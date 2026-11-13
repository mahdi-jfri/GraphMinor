module

public import GraphMinor.Compute.GM02CopyLabelBits

/-!
# Adding a whole component to the selected side

Copy the old side bits into a spare array, then write the union of those
bits with the vertices marked by search label one. The temporary copy
allows the output array to be allocated afresh without losing the old
side. This is the small-component branch of the grouping in II (3.1).
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths Classical

/-- A union bit: at least one of the old side bit and the reached-label bit is one. -/
def gm02UnionLabelExpr (src : Arr) : Expr := .op .le (.const 1)
  (.op .add (.read 71 (.reg 180)) (.op .eq (.read src (.reg 180)) (.const 1)))

/-- Copy the old side from array 70 to 71, then overwrite 70 by the union. -/
def gm02UnionLabelBitsProg (src : Arr) : Cmd :=
  .seq (gm02CopyLabelBitsProg 70 71)
    (gm13TabulateProg 180 (.reg 40) (gm02UnionLabelExpr src) 70)

/-- Adding all reached vertices writes exactly the union side bits, in
linear time, and changes only its two side arrays and loop counter. -/
theorem gm02UnionLabelBitsProg_exec {n w : ℕ} (Y C : Finset (Fin n))
    (mask : Fin n → ℕ) (hm : ∀ v, mask v ≤ 2) (hC : ∀ v, mask v = 1 ↔ v ∈ C)
    (src : Arr) (hs70 : src ≠ 70) (hs71 : src ≠ 71) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hrn : s.regs 40 = n)
    (hY : s.arrs 70 = gm02VertexBits Y) (hsrc : s.arrs src = List.ofFn mask) :
    ∃ s' t, Exec w (gm02UnionLabelBitsProg src) s s' t ∧ t ≤ 12 + n * 37 ∧
      Keeps [180] [70, 71] s s' ∧ s'.arrs 70 = gm02VertexBits (Y ∪ C) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hY₁⟩ := gm02CopyVertexBitsProg_exec Y 70 71 (by decide)
    s hw hn hrn hY
  have hsrc₁ : s₁.arrs src = List.ofFn mask :=
    (hk₁.2 _ (by simpa only [List.mem_singleton] using hs71)).trans hsrc
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout⟩ := gm13TabulateProg_exec (w := w)
    180 (.reg 40) (gm02UnionLabelExpr src) 70 (gm02VertexBits (Y ∪ C)) s₁ (by omega)
    (by simpa only [gm02VertexBits, List.length_ofFn] using hn)
    (fun st hk => by
      simp only [gm02VertexBits, List.length_ofFn]
      exact eval_reg ((hk.1 _ (by decide)).trans ((hk₁.1 _ (by decide)).trans hrn)) hn)
    (fun st i hi hk hri => by
      have hin : i < n := by simpa only [gm02VertexBits, List.length_ofFn] using hi
      let v : Fin n := ⟨i, hin⟩
      have hyarr : st.arrs 71 = gm02VertexBits Y := (hk.2 _ (by decide)).trans hY₁
      have hmarr : st.arrs src = List.ofFn mask :=
        (hk.2 _ (by simpa only [List.mem_singleton] using hs70)).trans hsrc₁
      have hei := eval_reg hri (hin.trans hn)
      have hey : (.read 71 (.reg 180) : Expr).eval w st = some (if v ∈ Y then 1 else 0) := by
        have he := eval_read (a := 71) hei (by simpa only [hyarr, gm02VertexBits, List.length_ofFn] using hin)
          (by simp only [hyarr, gm02VertexBits, List.getElem_ofFn]; split_ifs <;> omega)
        simpa only [hyarr, gm02VertexBits, List.getElem_ofFn, v] using he
      have hem : (.read src (.reg 180) : Expr).eval w st = some (mask v) := by
        have he := eval_read (a := src) hei (by simpa only [hmarr, List.length_ofFn] using hin)
          (by simpa only [hmarr, List.getElem_ofFn] using (hm v).trans_lt hw)
        simpa only [hmarr, List.getElem_ofFn, v] using he
      have hec := eval_eq hem (eval_const (show 1 < 2 ^ w by omega)) (by omega)
      have hec' : (.op .eq (.read src (.reg 180)) (.const 1) : Expr).eval w st =
          some (if v ∈ C then 1 else 0) := by simpa only [hC v] using hec
      have hsum : (if v ∈ Y then 1 else 0) + (if v ∈ C then 1 else 0) < 2 ^ w := by
        split_ifs <;> omega
      have headd := eval_add hey hec' hsum
      have hword : (gm02VertexBits (Y ∪ C))[i] = if v ∈ Y ∨ v ∈ C then 1 else 0 := by
        simp only [gm02VertexBits, List.getElem_ofFn, Finset.mem_union, v]
      rw [hword]
      change (match (Expr.const 1).eval w st,
          (.op .add (.read 71 (.reg 180)) (.op .eq (.read src (.reg 180)) (.const 1)) : Expr).eval w st with
        | some x, some y => BinOp.le.eval w x y
        | _, _ => none) = _
      rw [eval_const (show 1 < 2 ^ w by omega), headd]
      by_cases hy : v ∈ Y <;> by_cases hc : v ∈ C <;>
        simp [BinOp.eval, BinOp.raw, checkWord, hy, hc, show 1 < 2 ^ w by omega])
  have hk₁' : Keeps [180] [70, 71] s s₁ :=
    hk₁.mono (fun _ h => h) (by intro a ha; obtain rfl := List.mem_singleton.1 ha; simp)
  have hk₂' : Keeps [180] [70, 71] s₁ s₂ :=
    hk₂.mono (fun _ h => h) (by intro a ha; obtain rfl := List.mem_singleton.1 ha; simp)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, hk₁'.trans hk₂' (fun _ h => h) (fun _ h => h), hout⟩
  simp only [Expr.cost, gm02UnionLabelExpr, gm02VertexBits, List.length_ofFn] at ht₂
  have heq : n * 37 = n * 16 + n * 21 := by ring
  rw [heq]
  omega

end GraphMinor.Compute
