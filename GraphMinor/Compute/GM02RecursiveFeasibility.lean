module

public import GraphMinor.Compute.GM02RecursiveChosenChild
public import GraphMinor.Compute.GM02RecursiveSides
public import GraphMinor.Compute.GM02BoundaryFeasibility

/-!
# Feasibility of the exact pair of recursive child inputs

The complete numbered catalogue covers all parent crossing schemes.
Apply corrected (2.9), then replace both actual induced graphs by the
compact inputs constructed by the machine. Thus scanning that catalogue
and testing both children decides exactly the parent's feasibility.
-/

public section
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Parent feasibility is precisely feasibility of both compact children of some catalogue scheme. -/
theorem gm02RecursiveFeasible_iff_children (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n))
    (hvalid : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    x.A.Feasible (Graph.ofSimpleGraph x.G) ↔
      ∃ C : (gm02CompressedBoundaryInput x L R).schemes,
        (gm02RecursiveChosenInput false x L R C).A.Feasible
          (Graph.ofSimpleGraph (gm02RecursiveChosenInput false x L R C).G) ∧
        (gm02RecursiveChosenInput true x L R C).A.Feasible
          (Graph.ofSimpleGraph (gm02RecursiveChosenInput true x L R C).G) := by
  have hsep := gm02RecursiveSides_canonical allVertices x q L R hvalid
  have hf := gm02Feasible_iff_boundary_scheme x L R _ _ rfl rfl hsep
  constructor
  · intro h
    obtain ⟨C, hleft, hright⟩ := hf.mp h
    refine ⟨C, ?_, ?_⟩
    · exact (gm02CanonicalLeftInput_feasible_iff x.G L R x.A
        (gm02CanonicalBoundaryScheme x L R C)).mpr hleft
    · exact (gm02CanonicalRightInput_feasible_iff x.G L R x.A
        (gm02CanonicalBoundaryScheme x L R C)).mpr hright
  · rintro ⟨C, hleft, hright⟩
    apply hf.mpr
    refine ⟨C, ?_, ?_⟩
    · exact (gm02CanonicalLeftInput_feasible_iff x.G L R x.A
        (gm02CanonicalBoundaryScheme x L R C)).mp hleft
    · exact (gm02CanonicalRightInput_feasible_iff x.G L R x.A
        (gm02CanonicalBoundaryScheme x L R C)).mp hright

/-- Every feasibility witness occurs before the end of the fixed code scan. -/
theorem gm02RecursiveFeasible_iff_scanned_children (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (q : ℕ) (L R : Finset (Fin x.n))
    (hvalid : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R))
    (hbound : (gm02CompressedBoundaryInput x L R).n ≤ gm02RecursiveBoundaryBound q) :
    x.A.Feasible (Graph.ofSimpleGraph x.G) ↔
      ∃ C : (gm02CompressedBoundaryInput x L R).schemes,
        gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C < gm02RecursiveCodeBound q ∧
        (gm02RecursiveChosenInput false x L R C).A.Feasible
          (Graph.ofSimpleGraph (gm02RecursiveChosenInput false x L R C).G) ∧
        (gm02RecursiveChosenInput true x L R C).A.Feasible
          (Graph.ofSimpleGraph (gm02RecursiveChosenInput true x L R C).G) := by
  rw [gm02RecursiveFeasible_iff_children allVertices x q L R hvalid]
  constructor
  · rintro ⟨C, hleft, hright⟩
    exact ⟨C, gm02BoundarySchemeCode_lt_bound _ hbound C, hleft, hright⟩
  · rintro ⟨C, _, hleft, hright⟩
    exact ⟨C, hleft, hright⟩

end GraphMinor.Compute
