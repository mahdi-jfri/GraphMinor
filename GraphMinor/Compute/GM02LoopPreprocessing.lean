module

public import GraphMinor.Compute.GM02EliminateBranchLoops
import GraphMinor.Compute.GM02TopologicalBasicWords

/-!
# Polynomial Word RAM contract for branch-loop preprocessing

A word constant of two covers the entire plain input and the counts
used by initialization and loop removal. Combining these word bounds
with the actual execution theorem gives a quadratic preprocessing
program. Its output still describes the original topological question
and is ready for the corrected split tests.
-/

public section
namespace GraphMinor.Compute
open Graph GraphMinor.GM02

/-- Branch-loop preprocessing computes its loop-free graph pair from plain input in quadratic time. -/
theorem gm02EliminateBranchLoops_computes :
    ComputesRelInTime gm02TopologicalSize (fun x s => s.arrs inArr = x.enc)
      (fun x s => s.arrs inArr = x.enc ∧ s.arrs 22 = bitSetList x.vertices ∧
        s.regs 10 = x.G.n ∧ s.regs 11 = x.G.edges.length ∧ s.regs 15 = x.edges.length ∧
        s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card ∧
        (s.arrs 20).length = x.G.edges.length ∧ (∀ b ∈ s.arrs 20, b ≤ 1) ∧
        (s.arrs 21).length = x.edges.length ∧ (∀ b ∈ s.arrs 21, b ≤ 1) ∧
        (TopologicallyContains x.G.graph x.H ↔
          TopologicallyContains (gm02ActiveGraph x.G.graph (s.arrs 20)) (gm02ActiveGraph x.H (s.arrs 21))) ∧
        (∀ e v, v ∈ V(x.H) → ¬(gm02ActiveGraph x.G.graph (s.arrs 20)).IsLoopAt e v))
      gm02EliminateBranchLoopsProg (fun n => (n + 1) ^ 2) := by
  refine ⟨120, 2, by decide, by decide, ?_⟩
  intro x s hin
  obtain ⟨hw, hsize, _, hlen⟩ := gm02Topological_basicWordBounds x 2 le_rfl
  obtain ⟨s', t, he, ht, hsrc, hmask, h10, h11, _, _, _, h15, h16, hG, hHlen, hbits, hTopo, hNoLoop, _⟩ :=
    gm02EliminateBranchLoopsProg_exec x s hin hw hsize hlen
  refine ⟨s', t, he, ht, hsrc, hmask, h10, h11, h15, h16, ?_, ?_, hHlen, hbits, hTopo, hNoLoop⟩
  · rw [hG]
    exact gm02HostLoopFlags_length x _
  · rw [hG]
    exact gm02HostLoopFlags_bits x _

end GraphMinor.Compute
