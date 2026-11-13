module

public import GraphMinor.Compute.Case3StepsAttachmentRows

/-!
# Three attachments suffice

Claim (1) of XIII (8.6), page 96, bounds the intersection of each raw member
with the core by three vertices. Applying it to the member of an outside
component bounds its attachment row. Core seeds have empty rows.
-/

public section

namespace GraphMinor.Compute

open Classical

/-- Every component attachment row returned from a valid (8.6) core has at
most three vertices, by (8.6), Claim (1). -/
theorem case3AttachmentRowSet_card_le_three (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d) (u : Fin x.n) :
    (case3AttachmentRowSet x d.core.Z u).card ≤ 3 := by
  by_cases hu : u ∈ d.core.Z
  · rw [case3AttachmentRowSet_eq_empty x d.core.Z u hu, Finset.card_empty]
    omega
  · rw [case3AttachmentRowSet_eq_attachOf x d.core.Z u hu]
    let hK := isComponentOutsideCore_compOutside x d.core.Z hu
    let A := mkAlg86TypeII x d.core.Z (compOutside x d.core.Z u) hK
    have hraw : A ∈ alg86RawDivision x d.core.Z :=
      Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x d.core.Z _ hK))
    have hGM : A.toGMGraph ∈ GM13.coreRawDivision x.toSociety d.core.toCoreGraph :=
      (mem_alg86RawDivision_iff_toGMGraph_mem_coreRawDivision x d.core.Z d.core.C A).mp hraw
    have hcard := (GM13.lemma_8_6_claim_1 hd.2.2.1.2.1 hGM).1
    have hverts : A.verts ∩ d.core.Z = attachOf x d.core.Z u := by
      change (compOutside x d.core.Z u ∪ attachOf x d.core.Z u) ∩ d.core.Z = _
      rw [Finset.union_inter_distrib_right,
        Finset.disjoint_iff_inter_eq_empty.mp hK.disjoint_Z, Finset.empty_union,
        Finset.inter_eq_left.mpr (attachOf_subset_Z x d.core.Z u)]
    rw [Alg86Subgraph.vertexSet_toGMGraph, Alg83Output.toCoreGraph,
      vertexSet_toCoreGraph, ← Finset.coe_inter, hverts] at hcard
    simpa only [Set.ncard_coe_finset] using hcard

end GraphMinor.Compute
