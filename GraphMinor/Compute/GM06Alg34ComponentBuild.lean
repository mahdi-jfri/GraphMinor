module

public import GraphMinor.Compute.GM06Alg34ComponentMask
public import GraphMinor.Compute.GM06Alg34PayloadBuild
import Mathlib.Tactic.Ring

/-!
# Building a selected component branch input

Search from the selected label, copy its visited component marks into
the retained vertex mask, and run the complete induced input builder.
The supplied array becomes exactly the selected component payload for
the branch reduction in VI (3.3)(iv).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Install the component selected in register 114 as the branch input. -/
def gm06ComponentBuildProg : Cmd :=
  .seq (.assign 187 (.reg 114)) (.seq gm06VertexBfsProg
    (.seq gm06ComponentMaskProg gm06PayloadBuildProg))

private theorem update_budget (n : ℕ) :
    2 + (26 * (n * n) + 23 * n + 26) + (16 * n + 9) +
      1000 * (n + 2) ^ 3 ≤ 1100 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- The component update installs the exact finite induced payload in
cubic time, reading only the supplied array, computed CSR, and selected label. -/
theorem gm06ComponentBuildProg_exec (x : GM06DrawingData) (a : Fin x.n)
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = x.words)
    (hselected : s.regs 114 = a.val) (hsize : s.regs 4 = x.n)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n) :
    ∃ s' t, Exec (wordSize c x.size) gm06ComponentBuildProg s s' t ∧
      t ≤ 1100 * (x.size + 2) ^ 3 ∧ s'.arrs 0 = (x.componentData a).words := by
  have hc1 : 1 ≤ c := by omega
  have hc2 : 2 ≤ c := by omega
  have hsizew : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _)
  have hn := x.counts_le_size.1.trans_lt hsizew
  have hw : 1 < 2 ^ wordSize c x.size := by
    have h := x.five_le_words_length
    have hh := x.words_length_le_size
    omega
  have hsquare := (Nat.mul_le_mul (x.counts_le_size.1.trans (by omega))
    (x.counts_le_size.1.trans (by omega))).trans_lt (sq_lt_two_pow_wordSize (n := x.size) hc2)
  let s₁ := s.setReg 187 a.val
  have hex₁ : Exec (wordSize c x.size) (.assign 187 (.reg 114)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hselected, a.isLt.trans hn])
  obtain ⟨s₂, t₂, hex₂, ht₂, hmarks₂, ha₂, hg₂⟩ :=
    gm06VertexBfsProg_exec x a hw hn hsquare (s := s₁)
      (by simpa [s₁] using hsize) (by simp [s₁]) hlists hlen
  obtain ⟨s₃, t₃, hex₃, ht₃, hmask₃, ha₃, _⟩ :=
    gm06ComponentMaskProg_exec x a hw hn hmarks₂
      ((hg₂ 4 (by decide)).trans hsize)
  obtain ⟨s₄, t₄, hex₄, ht₄, hnewInput⟩ :=
    gm06PayloadBuildProg_exec x (x.componentVertices a) hc
      ((ha₃ 0 (by decide)).trans ((ha₂ 0 (by decide) (by decide)).trans hinput)) hmask₃
  have hnsize := x.counts_le_size.1
  have hsq := Nat.mul_le_mul hnsize hnsize
  refine ⟨s₄, 2 + (t₂ + (t₃ + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, hnewInput⟩
  exact (show 2 + (t₂ + (t₃ + t₄)) ≤
      2 + (26 * (x.size * x.size) + 23 * x.size + 26) + (16 * x.size + 9) +
        1000 * (x.size + 2) ^ 3 by omega).trans (update_budget x.size)

end GraphMinor.Compute
