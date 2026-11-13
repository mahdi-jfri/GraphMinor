module

public import GraphMinor.Compute.GM06Alg34BranchFrames
public import GraphMinor.Compute.GM06Alg34ParentCopy
public import GraphMinor.Compute.GM06Alg34VertexAdjList
import Mathlib.Tactic.Ring

/-!
# Building a branch from the saved parent input

Restore the parent words, rebuild the endpoint adjacency lists, and
construct the component selected by the outer source counter. The
parent array, root mask, queue, and outer counters survive this complete
operation. Its time is cubic in the parent input size.
-/

public section
namespace GraphMinor.Compute

private theorem adjacency_arrays : gm06VertexAdjListProg.writtenArrs ⊆ Finset.range 40 := by decide
set_option maxRecDepth 2048 in
private theorem adjacency_registers : gm06VertexAdjListProg.writtenRegs ⊆ Finset.range 300 := by decide

private theorem adjacency_array_frame {w t : ℕ} {s s' : State}
    (hex : Exec w gm06VertexAdjListProg s s' t) {A : ℕ} (hA : 40 ≤ A) :
    s'.arrs A = s.arrs A := by
  apply hex.arrs_eq_of_not_mem_writtenArrs
  intro hm
  have hh := Finset.mem_range.mp (adjacency_arrays hm)
  omega

private theorem adjacency_register_frame {w t : ℕ} {s s' : State}
    (hex : Exec w gm06VertexAdjListProg s s' t) {q : ℕ} (hq : 5000 ≤ q) :
    s'.regs q = s.regs q := by
  apply hex.regs_eq_of_not_mem_writtenRegs
  intro hm
  have hh := Finset.mem_range.mp (adjacency_registers hm)
  omega

/-- Build the component at outer source counter 5001 from the saved parent. -/
@[expose] def gm06BranchRebuildProg : Cmd :=
  .seq gm06RestoreParentProg (.seq gm06VertexAdjListProg
    (.seq (.assign 114 (.reg 5001)) gm06ComponentBuildProg))

private theorem rebuild_budget (n : ℕ) :
    16 * n + 9 + (27 * (n * n) + 62 * n + 54) + 2 +
      1100 * (n + 2) ^ 3 ≤ 1200 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- The saved-parent branch builder installs exactly the selected
component input, with cubic time and preservation of the queue state. -/
theorem gm06BranchRebuildProg_exec (x : GM06DrawingData) (a : Fin x.n)
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hsaved : s.arrs 41 = x.words)
    (hlen : s.regs 5003 = x.words.length) (hsource : s.regs 5001 = a.val) :
    ∃ s' t, Exec (wordSize c x.size) gm06BranchRebuildProg s s' t ∧
      t ≤ 1200 * (x.size + 2) ^ 3 ∧ s'.arrs 0 = (x.componentData a).words ∧
      (∀ A : ℕ, 40 ≤ A → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, 5000 ≤ q → q < 5100 → s'.regs q = s.regs q) := by
  have hc1 : 1 ≤ c := by omega
  have hsize : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _)
  have hw : 1 < 2 ^ wordSize c x.size := by have hh := x.five_le_words_length; have hh' := x.words_length_le_size; omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hin₁, ha₁, hg₁⟩ := gm06RestoreParentProg_exec x hw hsize hsaved hlen
  obtain ⟨s₂, t₂, hex₂, ht₂, hadj₂, hlen₂, hsize₂, _, _, _, ha₂⟩ :=
    gm06VertexAdjListProg_exec x (by omega : 2 ≤ c) hin₁
  have hs₂ : s₂.regs 5001 = a.val :=
    (adjacency_register_frame hex₂ (by decide)).trans ((hg₁ 5001 (by decide)).trans hsource)
  let s₃ := s₂.setReg 114 a.val
  have hex₃ : Exec (wordSize c x.size) (.assign 114 (.reg 5001)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hs₂, a.isLt.trans (x.counts_le_size.1.trans_lt hsize)])
  obtain ⟨s₄, t₄, hex₄, ht₄, hin₄⟩ :=
    gm06ComponentBuildProg_exec x a hc (s := s₃)
      ((ha₂ 0 (by decide)).trans hin₁) (by simp [s₃])
      (by simpa [s₃] using hsize₂) (hadj₂.of_arrs_eq rfl rfl rfl) hlen₂
  have hn := x.counts_le_size.1
  have hm := x.counts_le_size.2.1
  have hsq := Nat.mul_le_mul hn hn
  refine ⟨s₄, t₁ + (t₂ + (2 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    (show t₁ + (t₂ + (2 + t₄)) ≤ 16 * x.size + 9 +
      (27 * (x.size * x.size) + 62 * x.size + 54) + 2 + 1100 * (x.size + 2) ^ 3 by
      have hh := x.words_length_le_size; omega).trans (rebuild_budget x.size), hin₄, ?_, ?_⟩
  · intro A hA
    exact (gm06ComponentBuildProg_array_frame hex₄ hA).trans
      ((adjacency_array_frame hex₂ hA).trans (ha₁ A (by omega)))
  · intro q hq hq'
    exact (gm06ComponentBuildProg_register_frame hex₄ hq).trans
      ((State.setReg_regs_ne _ _ (by omega : q ≠ 114)).trans
        ((adjacency_register_frame hex₂ hq).trans (hg₁ q hq')))

end GraphMinor.Compute
