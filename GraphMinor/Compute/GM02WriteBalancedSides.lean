module

public import GraphMinor.Compute.GM02GroupingLoop

/-!
# Writing both balanced-separation sides

The first side consists of the separator and the selected component
union. The second side is the complement of the selected union, so the
separator occurs in both. Write their membership bits into the two
output arrays and set the successful-output flag. These are the vertex
sets of the separation constructed in II (2.6) for II (3.1).
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths GraphMinor.Compute.Crossing Classical

/-- First-side bit: separator membership plus selected-side membership. -/
def gm02LeftSideExpr (k : ℕ) : Expr := .op .add
  (.op .sub (.const 1) (gm02TupleFreeExpr 200 (.reg 180) k)) (.read 70 (.reg 180))

/-- Second-side bit: the vertex is absent from the selected component union. -/
def gm02RightSideExpr : Expr := .op .sub (.const 1) (.read 70 (.reg 180))

/-- Write the two vertex-set arrays and mark the output successful. -/
def gm02WriteBalancedSidesProg (k : ℕ) : Cmd :=
  .seq (gm13TabulateProg 180 (.reg 40) (gm02LeftSideExpr k) outArr)
    (.seq (gm13TabulateProg 180 (.reg 40) gm02RightSideExpr 2) (.assign outReg (.const 1)))

/-- Writing side arrays computes the exact vertex sets of the constructed
separation, with a linear vertex-count time bound for fixed slot count. -/
theorem gm02WriteBalancedSidesProg_exec {n k w : ℕ} (X Y : Finset (Fin n))
    (hdis : Disjoint X Y) (f : Fin k → ℕ) (hf : ∀ i, f i ≤ n) (hX : X = gm02SlotVertices f)
    (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hrn : s.regs 40 = n)
    (hY : s.arrs 70 = gm02VertexBits Y) (hslots : ∀ i, s.regs (200 + i.val) = f i) :
    ∃ s' t, Exec w (gm02WriteBalancedSidesProg k) s s' t ∧
      t ≤ 14 + n * (34 + 6 * k) ∧ Keeps [180, outReg] [outArr, 2] s s' ∧
      s'.regs outReg = 1 ∧ s'.arrs outArr = gm02VertexBits (X ∪ Y) ∧
      s'.arrs 2 = gm02VertexBits (Finset.univ \ Y) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hout₁⟩ := gm13TabulateProg_exec (w := w)
    180 (.reg 40) (gm02LeftSideExpr k) outArr (gm02VertexBits (X ∪ Y)) s (by omega)
    (by simpa only [gm02VertexBits, List.length_ofFn] using hn)
    (fun st hk => by
      simp only [gm02VertexBits, List.length_ofFn]
      exact eval_reg ((hk.1 _ (by decide)).trans hrn) hn)
    (fun st i hi hk hri => by
      have hin : i < n := by simpa only [gm02VertexBits, List.length_ofFn] using hi
      let v : Fin n := ⟨i, hin⟩
      have hslt : ∀ j, st.regs (200 + j.val) = f j := by
        intro j
        apply (hk.1 _ ?_).trans (hslots j)
        dsimp only [Reg]
        simp only [List.mem_singleton]
        omega
      have hefree := gm02TupleFreeExpr_eval_slots 200 180 f v st (by omega) hri hn hf hslt
      have hefree' : (gm02TupleFreeExpr 200 (.reg 180) k).eval w st =
          some (if v ∉ X then 1 else 0) := by simpa only [← hX] using hefree
      have hexbit := eval_sub (eval_const (show 1 < 2 ^ w by omega)) hefree'
      have heybit := gm02ReadVertexBits_eval Y v 70 180 st (by omega) hn hri
        ((hk.2 _ (by decide)).trans hY)
      have hsum : (1 - (if v ∉ X then 1 else 0)) + (if v ∈ Y then 1 else 0) < 2 ^ w := by
        split_ifs <;> omega
      have headd := eval_add hexbit heybit hsum
      have hword : (gm02VertexBits (X ∪ Y))[i] = if v ∈ X ∨ v ∈ Y then 1 else 0 := by
        simp only [gm02VertexBits, List.getElem_ofFn, Finset.mem_union, v]
      rw [hword]
      by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y
      · exact (Finset.disjoint_left.1 hdis hx hy).elim
      · simpa [gm02LeftSideExpr, hx, hy] using headd
      · simpa [gm02LeftSideExpr, hx, hy] using headd
      · simpa [gm02LeftSideExpr, hx, hy] using headd)
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout₂⟩ := gm13TabulateProg_exec (w := w)
    180 (.reg 40) gm02RightSideExpr 2 (gm02VertexBits (Finset.univ \ Y)) s₁ (by omega)
    (by simpa only [gm02VertexBits, List.length_ofFn] using hn)
    (fun st hk => by
      simp only [gm02VertexBits, List.length_ofFn]
      exact eval_reg ((hk.1 _ (by decide)).trans ((hk₁.1 _ (by decide)).trans hrn)) hn)
    (fun st i hi hk hri => by
      have hin : i < n := by simpa only [gm02VertexBits, List.length_ofFn] using hi
      let v : Fin n := ⟨i, hin⟩
      have heybit := gm02ReadVertexBits_eval Y v 70 180 st (by omega) hn hri
        ((hk.2 _ (by decide)).trans ((hk₁.2 _ (by decide)).trans hY))
      have he := eval_sub (eval_const (show 1 < 2 ^ w by omega)) heybit
      have hword : (gm02VertexBits (Finset.univ \ Y))[i] = if v ∉ Y then 1 else 0 := by
        simp only [gm02VertexBits, List.getElem_ofFn, Finset.mem_sdiff, Finset.mem_univ, true_and, v]
      rw [hword]
      by_cases hy : v ∈ Y <;> simpa [gm02RightSideExpr, hy] using he)
  let s₃ := s₂.setReg outReg 1
  have he₃ : Exec w (.assign outReg (.const 1)) s₂ s₃ 2 := .assign (eval_const (by omega))
  have hk₁' : Keeps [180, outReg] [outArr, 2] s s₁ :=
    hk₁.mono (by intro r hr; obtain rfl := List.mem_singleton.1 hr; simp)
      (by intro a ha; obtain rfl := List.mem_singleton.1 ha; simp)
  have hk₂' : Keeps [180, outReg] [outArr, 2] s₁ s₂ :=
    hk₂.mono (by intro r hr; obtain rfl := List.mem_singleton.1 hr; simp)
      (by intro a ha; obtain rfl := List.mem_singleton.1 ha; simp)
  refine ⟨s₃, t₁ + (t₂ + 2), .seq he₁ (.seq he₂ he₃), ?_,
    (hk₁'.trans hk₂' (fun _ h => h) (fun _ h => h)).setReg (by simp) _, by simp [s₃], ?_, hout₂⟩
  · have hc : (gm02LeftSideExpr k).cost = 6 + 6 * k := by
      simp only [gm02LeftSideExpr, Expr.cost, gm02TupleFreeExpr_cost]
      omega
    rw [hc] at ht₁
    simp only [Expr.cost, gm02RightSideExpr, gm02VertexBits, List.length_ofFn] at ht₁ ht₂
    have heq : n * (34 + 6 * k) = n * (1 + (6 + 6 * k) + 11) + n * 16 := by ring
    rw [heq]
    omega
  · exact (hk₂.2 _ (by decide)).trans hout₁

end GraphMinor.Compute
