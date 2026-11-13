module

public import GraphMinor.Compute.GM02RecursiveSubset
public import GraphMinor.Compute.GM02BuildSeparatorInput
public import GraphMinor.GM02.RecursiveWidthReports
import GraphMinor.Compute.GM02BalancedSeparationOutput

/-!
# Interpreting a rejected separator search as a width report

In Step 1 of II's two recursive routines, rejection by (3.1) means that
no separation with the required balance exists. The contrapositive of
(2.6) therefore gives tree-width at least the internal threshold. This
lemma connects the executable separator postcondition to that report.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- A valid rejected (3.1) call gives exactly the width report used by
both A1 and A2, Graph Minors II pages 316–317. -/
theorem gm02RecursiveSeparator_reject_width (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (k : ℕ) (s : State) (hcorrect : (gm02RecursiveSeparatorInput allVertices x).correct (k : ℤ) s)
    (hzero : s.regs outReg = 0) : k ≤ x.width := by
  rcases hcorrect with ⟨hone, _⟩ | ⟨_, hno⟩
  · omega
  · apply recursive_width_of_no_separation (Graph.ofSimpleGraph x.G) Set.finite_univ (Set.toFinite _)
      (gm02RecursiveSubset allVertices x : Set (Fin x.n)) (Set.subset_univ _) k
    rintro ⟨H, H', hsep, hbound, hL, hR⟩
    apply hno
    apply ((gm02RecursiveSeparatorInput allVertices x).exists_validSides_iff (k : ℤ)).2
    refine ⟨H, H', hsep, ?_, hL, hR⟩
    exact_mod_cast hbound

end GraphMinor.Compute
