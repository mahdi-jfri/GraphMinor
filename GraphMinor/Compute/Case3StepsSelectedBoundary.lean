module

public import GraphMinor.Compute.Case3StepsCompactSelectedDivision

/-!
# The boundary key is the selected member's true boundary

The (8.6) core theorem identifies every merged member boundary with its
intersection with the core. The selected member construction has exactly
its key boundary at that intersection. Wall corners have neighbors, so the
isolated boundary-vertex raw type is absent in the compass society.
-/

public section

namespace GraphMinor.Compute

/-- The key computed for a selected compass member is exactly its simple
society boundary, under the hypotheses of the valid (8.6) output. -/
theorem case3CompactSelectedMember_boundary {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (d : Alg86DivisionOutput (case3CompactSocietyInput D W h2 he hW))
    (hd : IsValidAlg86DivisionOutput (case3CompactSocietyInput D W h2 he hW) d)
    (i : Case3SelectedGroup (case3CompactSocietyInput D W h2 he hW) d.core.Z) :
    alg86Boundary (case3CompactSocietyInput D W h2 he hW)
      (case3SelectedMember (case3CompactSocietyInput D W h2 he hW) d.core.Z i) =
        case3GroupBoundary (case3CompactSocietyInput D W h2 he hW) d.core.Z i.1 := by
  let x := case3CompactSocietyInput D W h2 he hW
  have hmem : case3SelectedMember x d.core.Z i ∈ case3SelectedMembers x d.core.Z := Set.mem_range_self i
  rw [case3CompactSelectedMembers_eq_div D W h2 he hW d hd,
    (case3Alg86Division_families hd).2] at hmem
  have hcore := hd.2.2.1
  exact (alg86Boundary_eq_inter_Z_of_mem_division hcore.2.2.1 hcore.2.2.2.2.2.1 hd.1 hmem).trans
    (case3SelectedMember_inter_core x d.core.Z i)

end GraphMinor.Compute
