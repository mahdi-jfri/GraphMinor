module

public import GraphMinor.Compute.GM06Alg34GapTaskEnqueue
public import GraphMinor.Compute.GM06Alg34GapBranchFrames

/-!
# Branching into augmented component tasks

Prepare the canonical component roots from the current drawing and
append a parent/root record for each root to the existing work queue.
The supplied gap list is copied into each record. Components are
materialized when the records are read, so the parent stays available
throughout this scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Find all components and append their augmented work records. -/
def gm06GapBranchProg : Cmd := .seq gm06BranchRootsProg gm06GapTaskEnqueueProg

/-- Branching appends exactly one task for each canonical component,
retains the parent input, and preserves the pending read cursor. -/
theorem gm06GapBranchProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (R : List (Fin x.regions.length))
    (hwidth : wordSize 2 x.size ≤ w) (hw : 1 < 2 ^ w)
    (hsize : x.size + R.length + 3 < 2 ^ w)
    {pfx : List ℕ} {s : State} (hinput : s.arrs 0 = x.words)
    (hgap : s.arrs 47 = R.map Fin.val)
    (hend : pfx.length + ((gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words).length < 2 ^ w)
    (hbuf : IsPrefixBuffer 42 pfx
      (((gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words).length + cap) s)
    (hpos : s.regs 7001 = pfx.length) :
    ∃ s' t, Exec w gm06GapBranchProg s s' t ∧
      t ≤ 300 * (x.size + 1) ^ 3 + (20 * (x.size + R.length + 4) + 11) * x.n + 5 ∧
      IsPrefixBuffer 42
        (pfx ++ (gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words) cap s' ∧
      s'.regs 7001 =
        (pfx ++ (gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words).length ∧
      s'.regs 203 = x.componentRoots.length ∧
      s'.arrs 0 = x.words ∧ s'.arrs 47 = R.map Fin.val ∧
      (∀ A : ℕ, 41 ≤ A → A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q, 5103 ≤ q → q < 7500 → q ≠ 5001 → q ≠ 5006 →
        q ≠ 7001 → q ≠ 7400 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hin₁, hm₁, _, _, hc₁⟩ :=
    gm06BranchRootsProg_exec x (by decide : 2 ≤ 2) hinput
  have he₁w := he₁.mono_wordSize hwidth
  have hgap₁ : s₁.arrs 47 = R.map Fin.val :=
    (gm06GapBranchRoots_array_frame he₁ 47 (by decide)).trans hgap
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hp₂, _, _, ha₂, hg₂⟩ :=
    gm06GapTaskEnqueueProg_exec x R hw hsize hin₁ hgap₁ hm₁ hend
      (hbuf.of_arr_eq (gm06GapBranchRoots_array_frame he₁ 42 (by decide)))
      ((gm06GapBranchRoots_register_frame he₁ 7001 (by decide)).trans hpos)
  refine ⟨s₂, t₁ + t₂, .seq he₁w he₂, by omega, hb₂, hp₂,
    (hg₂ 203 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc₁,
    (ha₂ 0 (by decide)).trans hin₁, (ha₂ 47 (by decide)).trans hgap₁, ?_, ?_⟩
  · intro A hA h42
    exact (ha₂ A h42).trans (gm06GapBranchRoots_array_frame he₁ A hA)
  · intro q hq hq' h5001 h5006 h7001 h7400
    exact (hg₂ q hq' h5001 h5006 h7001 h7400).trans
      (gm06GapBranchRoots_register_frame he₁ q hq)

end GraphMinor.Compute
