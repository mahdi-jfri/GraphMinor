module

public import GraphMinor.Compute.GM06Alg34BranchAlloc
public import GraphMinor.Compute.GM06Alg34ParentCopy
public import GraphMinor.Compute.GM06Alg34VertexRootRanks

/-!
# Initializing the parent state for component branching

Save the supplied vertex count and computed component count, copy the
original input into the parent array, and allocate the branch queue.
Initialize the source and remaining-source counters. All retained data
are computed from the original array and the canonical root scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Save the parent input and counts, allocate its queue, and start the source scan. -/
def gm06BranchInitProg : Cmd :=
  .seq (.assign 5000 (.reg 4)) (.seq (.assign 5005 (.reg 203))
    (.seq gm06SaveParentProg (.seq gm06BranchAllocProg
      (.seq (.assign 5001 (.const 0)) (.assign 5006 (.reg 5000))))))

/-- The parent initialization prepares exactly the saved words, root
mask, empty queue, and counters needed by the verified branch loop. -/
theorem gm06BranchInitProg_exec (x : GM06DrawingData) {c : ℕ} (hc : 5 ≤ c)
    {s : State} (hinput : s.arrs 0 = x.words) (hn : s.regs 4 = x.n)
    (hheader : s.regs 100 = x.n) (hcount : s.regs 203 = x.componentRoots.length)
    (hmask : s.arrs 40 = gm06VertexRootMask x) :
    ∃ s' t, Exec (wordSize c x.size) gm06BranchInitProg s s' t ∧
      t ≤ gm06BranchCapacity x + 16 * x.size + 44 ∧
      s'.arrs 0 = x.words ∧ s'.arrs 41 = x.words ∧ s'.arrs 40 = gm06VertexRootMask x ∧
      IsPrefixBuffer 42 [] (gm06BranchCapacity x) s' ∧
      s'.regs 5000 = x.n ∧ s'.regs 5001 = 0 ∧ s'.regs 5002 = 0 ∧
      s'.regs 5003 = x.words.length ∧ s'.regs 5005 = x.componentRoots.length ∧ s'.regs 5006 = x.n := by
  have hc1 : 1 ≤ c := by omega
  have hsize := lt_two_pow_wordSize_of_le hc1 (n := x.size) (Nat.le_succ _)
  have hnw := x.counts_le_size.1.trans_lt hsize
  have hw : 1 < 2 ^ wordSize c x.size := by have hh := x.five_le_words_length; have hh' := x.words_length_le_size; omega
  have hroots := gm06VertexRootMask_sum_le x
  rw [gm06VertexRootMask_sum] at hroots
  have hrootw := hroots.trans_lt hnw
  let s₁ := s.setReg 5000 x.n
  let s₂ := s₁.setReg 5005 x.componentRoots.length
  have hex₁ : Exec (wordSize c x.size) (.assign 5000 (.reg 4)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hn, hnw])
  have hex₂ : Exec (wordSize c x.size) (.assign 5005 (.reg 203)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hcount, hrootw])
  obtain ⟨s₃, t₃, hex₃, ht₃, hparent₃, hlen₃, ha₃, hg₃⟩ :=
    gm06SaveParentProg_exec x hw hsize (s := s₂) hinput
  have hn₃ : s₃.regs 5000 = x.n := by
    rw [hg₃ 5000 (by decide) (by decide)]
    simp [s₂, s₁]
  have hhead₃ : s₃.regs 100 = x.n := by
    rw [hg₃ 100 (by decide) (by decide)]
    simpa [s₂, s₁] using hheader
  obtain ⟨s₄, t₄, hex₄, ht₄, hb₄, hp₄, ha₄, hg₄⟩ :=
    gm06BranchAllocProg_exec x hc ((ha₃ 0 (by decide)).trans hinput) hhead₃ hn₃
  let s₅ := s₄.setReg 5001 0
  let s₆ := s₅.setReg 5006 x.n
  have hex₅ : Exec (wordSize c x.size) (.assign 5001 (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hn₅ : s₅.regs 5000 = x.n := by
    simpa [s₅] using (hg₄ 5000 (by decide)).trans hn₃
  have hex₆ : Exec (wordSize c x.size) (.assign 5006 (.reg 5000)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hn₅, hnw])
  refine ⟨s₆, 2 + (2 + (t₃ + (t₄ + (2 + 2)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by have hh := x.words_length_le_size; omega,
    (ha₄ 0 (by decide)).trans ((ha₃ 0 (by decide)).trans hinput),
    (ha₄ 41 (by decide)).trans hparent₃,
    (ha₄ 40 (by decide)).trans ((ha₃ 40 (by decide)).trans hmask),
    hb₄, ?_, by simp [s₆, s₅], ?_, ?_, ?_, by simp [s₆]⟩
  · simpa [s₆, s₅] using (hg₄ 5000 (by decide)).trans hn₃
  · simpa [s₆, s₅] using hp₄
  · simpa [s₆, s₅] using (hg₄ 5003 (by decide)).trans hlen₃
  · have hh : s₃.regs 5005 = x.componentRoots.length := by
      rw [hg₃ 5005 (by decide) (by decide)]
      simp [s₂]
    simpa [s₆, s₅] using (hg₄ 5005 (by decide)).trans hh

end GraphMinor.Compute
