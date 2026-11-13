module

public import GraphMinor.Compute.GM06Alg34PayloadBuild
public import GraphMinor.Compute.GM06Alg34MaskInit
public import GraphMinor.Compute.GM06Alg34SingletonData
import Mathlib.Tactic.Ring

/-!
# The complete singleton deletion update on RAM input

Read the vertex count from the input, initialize the retained mask,
and erase the selected singleton vertex. The verified payload builder
then replaces array 0 by the full new drawing data. The selected label
is the only value needed from the preceding singleton search.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Delete the selected label in register 114 and install the complete new input. -/
def gm06SingletonUpdateProg : Cmd :=
  .seq (.assign 100 (.read 0 (.const 0))) (.seq gm06InitVertexMaskProg
    (.seq gm06DeleteVertexProg gm06PayloadBuildProg))

private theorem update_budget (n : ℕ) :
    3 + (13 * n + 6) + (3 + 1000 * (n + 2) ^ 3) ≤ 1100 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- The singleton update computes the exact finite payload of (3.3)(i),
including all new regions, in cubic time with logarithmic words. -/
theorem gm06SingletonUpdateProg_exec (x : GM06DrawingData) (v : Fin x.n)
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = x.words)
    (hselected : s.regs 114 = v.val) :
    ∃ s' t, Exec (wordSize c x.size) gm06SingletonUpdateProg s s' t ∧
      t ≤ 1100 * (x.size + 2) ^ 3 ∧ s'.arrs 0 = (x.singletonData v).words := by
  have hsize : x.size < 2 ^ wordSize c x.size :=
    lt_two_pow_wordSize_of_le (by omega) (Nat.le_succ _)
  have hn := x.counts_le_size.1.trans_lt hsize
  have hw : 1 < 2 ^ wordSize c x.size := by
    have h := x.five_le_words_length
    have hh := x.words_length_le_size
    omega
  let s₁ := s.setReg 100 x.n
  have hex₁ : Exec (wordSize c x.size) (.assign 100 (.read 0 (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hinput, x.words_layout,
      Nat.zero_lt_of_lt hw, hn])
  obtain ⟨s₂, t₂, hex₂, ht₂, hmask₂, ha₂, hg₂⟩ :=
    gm06InitVertexMaskProg_exec hw hn (s := s₁) (by simp [s₁])
  obtain ⟨s₃, hex₃, hmask₃, ha₃, _⟩ :=
    gm06DeleteVertexProg_exec (List.finRange x.n) v hn hmask₂
      (by rw [hg₂ 114 (by decide)]; simpa [s₁, State.setReg] using hselected)
  obtain ⟨s₄, t₄, hex₄, ht₄, hinput₄⟩ :=
    gm06PayloadBuildProg_exec x (x.singletonSurvivors v) hc
      ((ha₃ 0 (by decide)).trans ((ha₂ 0 (by decide)).trans hinput)) hmask₃
  refine ⟨s₄, 3 + (t₂ + (3 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, hinput₄⟩
  exact (show 3 + (t₂ + (3 + t₄)) ≤
      3 + (13 * x.size + 6) + (3 + 1000 * (x.size + 2) ^ 3) by
    have hh := x.counts_le_size.1
    omega).trans (update_budget x.size)

end GraphMinor.Compute
