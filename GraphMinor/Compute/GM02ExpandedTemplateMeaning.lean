module

public import GraphMinor.Compute.GM02TemplatePairMeaning
public import GraphMinor.Compute.GM02ExpandedSchemeData

/-!
# Meaning of the six arrays for an actual catalogue scheme

The fixed pair templates give the canonical parent matching words and
the exact supports of the expanded scheme. The reserved templates give
the two expanded reserved sets. These identities connect executable
array outputs to the semantic crossing scheme used by the recursion.
-/

public section
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

variable (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n))
  (H H' : Graph (Fin x.n) (Sym2 (Fin x.n)))
  (hHL : V(H) = (L : Set (Fin x.n))) (hHR : V(H') = (R : Set (Fin x.n)))
  (C : (gm02CompressedBoundaryInput x L R).schemes)

/-- Expanding the first endpoint template gives the first parent matching words. -/
theorem gm02ExpandedTemplate_left_words :
    (gm02TemplatePairIndices C.left.pairs).map
      (fun i => (compactEmb (gm02BoundaryDeletedSet x L R) i).val) =
      flatEdges (edgeListOf
        (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).left.pairGraph) := by
  exact (gm02TemplatePairIndices_map_names C.left
    (compactEmb (gm02BoundaryDeletedSet x L R))).trans
      (gm02ExpandCompressedBoundaryScheme_left_pairWords x L R H H' hHL hHR C).symm

/-- Expanding the second endpoint template gives the second parent matching words. -/
theorem gm02ExpandedTemplate_right_words :
    (gm02TemplatePairIndices C.right.pairs).map
      (fun i => (compactEmb (gm02BoundaryDeletedSet x L R) i).val) =
      flatEdges (edgeListOf
        (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).right.pairGraph) := by
  exact (gm02TemplatePairIndices_map_names C.right
    (compactEmb (gm02BoundaryDeletedSet x L R))).trans
      (gm02ExpandCompressedBoundaryScheme_right_pairWords x L R H H' hHL hHR C).symm

/-- The first marked endpoint image is exactly the first expanded support. -/
theorem gm02ExpandedTemplate_left_support :
    (gm02TemplatePairIndices C.left.pairs).toFinset.image
      (compactEmb (gm02BoundaryDeletedSet x L R)) =
      (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).left.support.toFinset := by
  apply Finset.coe_injective
  simp only [Finset.coe_image, Set.coe_toFinset]
  exact (congrArg (Set.image (compactEmb (gm02BoundaryDeletedSet x L R)))
    (gm02TemplatePairIndices_support C.left)).trans
      (gm02ExpandCompressedBoundaryScheme_left_support x L R H H' hHL hHR C).symm

/-- The second marked endpoint image is exactly the second expanded support. -/
theorem gm02ExpandedTemplate_right_support :
    (gm02TemplatePairIndices C.right.pairs).toFinset.image
      (compactEmb (gm02BoundaryDeletedSet x L R)) =
      (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).right.support.toFinset := by
  apply Finset.coe_injective
  simp only [Finset.coe_image, Set.coe_toFinset]
  exact (congrArg (Set.image (compactEmb (gm02BoundaryDeletedSet x L R)))
    (gm02TemplatePairIndices_support C.right)).trans
      (gm02ExpandCompressedBoundaryScheme_right_support x L R H H' hHL hHR C).symm

/-- The first reserved template image is exactly the first expanded reserved set. -/
theorem gm02ExpandedTemplate_reservedLeft :
    C.reservedLeft.toFinset.image (compactEmb (gm02BoundaryDeletedSet x L R)) =
      (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).reservedLeft.toFinset := by
  apply Finset.coe_injective
  simp only [Finset.coe_image, Set.coe_toFinset]
  have hcoe := Set.coe_toFinset C.reservedLeft
  exact (congrArg (Set.image (compactEmb (gm02BoundaryDeletedSet x L R))) hcoe).trans
    (gm02ExpandCompressedBoundaryScheme_reservedLeft x L R H H' hHL hHR C).symm

/-- The second reserved template image is exactly the second expanded reserved set. -/
theorem gm02ExpandedTemplate_reservedRight :
    C.reservedRight.toFinset.image (compactEmb (gm02BoundaryDeletedSet x L R)) =
      (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).reservedRight.toFinset := by
  apply Finset.coe_injective
  simp only [Finset.coe_image, Set.coe_toFinset]
  have hcoe := Set.coe_toFinset C.reservedRight
  exact (congrArg (Set.image (compactEmb (gm02BoundaryDeletedSet x L R))) hcoe).trans
    (gm02ExpandCompressedBoundaryScheme_reservedRight x L R H H' hHL hHR C).symm

end GraphMinor.Compute
