module

public import GraphMinor.Compute.GM02CompressBoundaryScheme
public import GraphMinor.GM02.CrossingFeasibility

/-!
# Testing parent feasibility through the numbered boundary catalogue

Every parent crossing scheme is the expansion of a numbered boundary
scheme. Apply this coverage to the separation feasibility theorem. Thus
the finite catalogue search tests exactly the side problems required by
the recursive algorithm in Graph Minors II, Section 3, pages 316–318.
-/

public section
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- The complete boundary catalogue suffices for the separation feasibility test. -/
theorem gm02Feasible_iff_boundary_scheme (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (H H' : Graph (Fin x.n) (Sym2 (Fin x.n)))
    (hHL : V(H) = (L : Set (Fin x.n))) (hHR : V(H') = (R : Set (Fin x.n)))
    (hsep : IsSeparation (Graph.ofSimpleGraph x.G) H H') :
    x.A.Feasible (Graph.ofSimpleGraph x.G) ↔
      ∃ C : (gm02CompressedBoundaryInput x L R).schemes,
        let D := gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C
        D.left.Feasible D.inducedLeft ∧ D.right.Feasible D.inducedRight := by
  constructor
  · intro h
    obtain ⟨D, hD⟩ := (GraphMinor.GM02.theorem_2_9_proof x.A hsep).mp h
    obtain ⟨C, rfl⟩ := gm02ExpandCompressedBoundaryScheme_surjective x L R H H' hHL hHR D
    exact ⟨C, hD⟩
  · rintro ⟨C, hC⟩
    exact (GraphMinor.GM02.theorem_2_9_proof x.A hsep).mpr
      ⟨gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C, hC⟩

end GraphMinor.Compute
