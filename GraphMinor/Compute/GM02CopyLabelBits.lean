module

public import GraphMinor.Compute.GM02BalancedSeparationInput
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Writing component membership bits

The grouping step for II (3.1) sometimes selects one whole component.
The search labels already identify that component by label one. Test the
labels and write their membership bits into a fresh side array. This
also copies an existing zero/one side array when its one entries are the
selected set.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths Classical

/-- Write a fresh membership array for the vertices carrying label one. -/
def gm02CopyLabelBitsProg (src dst : Arr) : Cmd :=
  gm13TabulateProg 180 (.reg 40) (.op .eq (.read src (.reg 180)) (.const 1)) dst

/-- Copying the selected labels writes exactly their vertex-set bits in
linear time, without changing the source or other arrays. -/
theorem gm02CopyLabelBitsProg_exec {n w : ℕ} (S : Finset (Fin n))
    (mask : Fin n → ℕ) (hm : ∀ v, mask v ≤ 2) (hS : ∀ v, mask v = 1 ↔ v ∈ S)
    (src dst : Arr) (hne : src ≠ dst) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hrn : s.regs 40 = n)
    (hsrc : s.arrs src = List.ofFn mask) :
    ∃ s' t, Exec w (gm02CopyLabelBitsProg src dst) s s' t ∧
      t ≤ 6 + n * 16 ∧ Keeps [180] [dst] s s' ∧ s'.arrs dst = gm02VertexBits S := by
  obtain ⟨s', t, hex, ht, hk, hout⟩ := gm13TabulateProg_exec (w := w)
    180 (.reg 40) (.op .eq (.read src (.reg 180)) (.const 1)) dst (gm02VertexBits S) s
    (by omega) (by simpa only [gm02VertexBits, List.length_ofFn] using hn)
    (fun st hk => by
      simp only [gm02VertexBits, List.length_ofFn]
      exact eval_reg ((hk.1 _ (by decide)).trans hrn) hn)
    (fun st i hi hk hri => by
      have hin : i < n := by simpa only [gm02VertexBits, List.length_ofFn] using hi
      let v : Fin n := ⟨i, hin⟩
      have harr : st.arrs src = List.ofFn mask :=
        (hk.2 _ (by simpa only [List.mem_singleton] using hne)).trans hsrc
      have heread := eval_read (a := src) (eval_reg hri (hin.trans hn))
        (by simpa only [harr, List.length_ofFn] using hin)
        (by simpa only [harr, List.getElem_ofFn] using (hm v).trans_lt hw)
      have he : (.read src (.reg 180) : Expr).eval w st = some (mask v) := by
        simpa only [harr, List.getElem_ofFn, v] using heread
      have heq := eval_eq he (eval_const (show 1 < 2 ^ w by omega)) (by omega)
      simpa only [gm02VertexBits, List.getElem_ofFn, hS v, v] using heq)
  refine ⟨s', t, hex, ?_, hk, hout⟩
  simpa only [Expr.cost, gm02VertexBits, List.length_ofFn] using ht

/-- Membership-bit arrays can be copied by the same selected-label program. -/
theorem gm02CopyVertexBitsProg_exec {n w : ℕ} (S : Finset (Fin n))
    (src dst : Arr) (hne : src ≠ dst) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hrn : s.regs 40 = n)
    (hsrc : s.arrs src = gm02VertexBits S) :
    ∃ s' t, Exec w (gm02CopyLabelBitsProg src dst) s s' t ∧
      t ≤ 6 + n * 16 ∧ Keeps [180] [dst] s s' ∧ s'.arrs dst = gm02VertexBits S := by
  apply gm02CopyLabelBitsProg_exec S (fun v => if v ∈ S then 1 else 0)
    (fun v => by split_ifs <;> omega) (fun v => by by_cases hv : v ∈ S <;> simp [hv])
    src dst hne s hw hn hrn hsrc

/-- Reading a vertex membership array yields its exact zero/one indicator. -/
theorem gm02ReadVertexBits_eval {n w : ℕ} (S : Finset (Fin n)) (v : Fin n)
    (arr : Arr) (idx : Reg) (s : State) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hidx : s.regs idx = v.val) (harr : s.arrs arr = gm02VertexBits S) :
    (.read arr (.reg idx) : Expr).eval w s = some (if v ∈ S then 1 else 0) := by
  have he := eval_read (a := arr) (eval_reg hidx (v.isLt.trans hn))
    (by simpa only [harr, gm02VertexBits, List.length_ofFn] using v.isLt)
    (by simp only [harr, gm02VertexBits, List.getElem_ofFn]; split_ifs <;> omega)
  simpa only [harr, gm02VertexBits, List.getElem_ofFn, Fin.eta] using he

end GraphMinor.Compute
