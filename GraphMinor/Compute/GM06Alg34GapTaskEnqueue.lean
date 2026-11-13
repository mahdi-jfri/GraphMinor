module

public import GraphMinor.Compute.GM06Alg34GapTaskEnqueueLoop

/-!
# Appending the complete component work list

Initialize the source scan at zero and scan every vertex label. The
canonical-root mask selects exactly one task for each component. The
result identifies the full pending queue, including any earlier words,
and preserves the parent drawing and its supplied gap labels.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append one parent/root record for each canonical component. -/
def gm06GapTaskEnqueueProg : Cmd :=
  .seq (.assign 5001 (.const 0))
    (.seq (.assign 5006 (.len 40)) gm06GapTaskEnqueueLoopProg)

/-- The complete scan appends exactly the canonical task list, retaining
all earlier queue words and the pending read cursor. -/
theorem gm06GapTaskEnqueueProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (R : List (Fin x.regions.length))
    (hw : 1 < 2 ^ w) (hsize : x.size + R.length + 3 < 2 ^ w)
    {pfx : List ℕ} {s : State} (hinput : s.arrs 0 = x.words)
    (hgap : s.arrs 47 = R.map Fin.val) (hmask : s.arrs 40 = gm06VertexRootMask x)
    (hend : pfx.length + ((gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words).length < 2 ^ w)
    (hbuf : IsPrefixBuffer 42 pfx
      (((gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words).length + cap) s)
    (hpos : s.regs 7001 = pfx.length) :
    ∃ s' t, Exec w gm06GapTaskEnqueueProg s s' t ∧
      t ≤ (20 * (x.size + R.length + 4) + 11) * x.n + 5 ∧
      IsPrefixBuffer 42
        (pfx ++ (gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words) cap s' ∧
      s'.regs 7001 =
        (pfx ++ (gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words).length ∧
      s'.regs 5001 = x.n ∧ s'.regs 5006 = 0 ∧
      (∀ A : ℕ, A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q < 7500, q ≠ 5001 → q ≠ 5006 → q ≠ 7001 → q ≠ 7400 → s'.regs q = s.regs q) := by
  have hn : x.n < 2 ^ w := x.counts_le_size.1.trans_lt (by omega : x.size < 2 ^ w)
  let s₁ := s.setReg 5001 0
  have he₁ : Exec w (.assign 5001 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  let s₂ := s₁.setReg 5006 x.n
  have he₂ : Exec w (.assign 5006 (.len 40)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₁, State.setReg, hmask, gm06VertexRootMask, hn])
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hp₃, hi₃, hz₃, ha₃, hg₃⟩ :=
    gm06GapTaskEnqueueLoopProg_exec x R (List.finRange x.n) hw hsize
      (i := 0) (s := s₂) (by simp) (by simp [List.range_eq_range'])
      hinput hgap hmask (by simp [s₂, s₁]) (by simp [s₂])
      (by simpa only [gm06GapTaskQueueWords_eq_tasks] using hend)
      (by simpa only [gm06GapTaskQueueWords_eq_tasks] using (hbuf.of_arr_eq (show s₂.arrs 42 = s.arrs 42 from rfl)))
      (by simpa [s₂, s₁] using hpos)
  refine ⟨s₃, 2 + (2 + t₃), .seq he₁ (.seq he₂ he₃), ?_, ?_, ?_, ?_, hz₃, ?_, ?_⟩
  · simp only [List.length_finRange] at ht₃
    omega
  · simpa only [gm06GapTaskQueueWords_eq_tasks] using hb₃
  · simpa only [gm06GapTaskQueueWords_eq_tasks] using hp₃
  · simpa only [List.length_finRange, Nat.zero_add] using hi₃
  · exact ha₃
  · intro q hq h5001 h5006 h7001 h7400
    exact (hg₃ q hq h5001 h5006 h7001 h7400).trans
      (by simp [s₂, s₁, State.setReg, h5001, h5006])

end GraphMinor.Compute
