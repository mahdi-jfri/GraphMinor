module

public import GraphMinor.Compute.GM02ExpandCompressedScheme
public import GraphMinor.Compute.GM02ExpandedPairWords

/-!
# Matching graphs of expanded catalogue schemes

The pair-set recovery identities identify both parent matching graphs
with the increasing images of the catalogue matching graphs. Their
canonical endpoint words therefore agree with the arrays emitted from
the fixed boundary templates.
-/

public section
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

private theorem pairGraph_eq_of_pairs {α : Type*} {S T : Set α}
    (A : Termination S) (B : Termination T) (h : A.pairs = B.pairs) :
    A.pairGraph = B.pairGraph := by
  ext u v
  simp only [Termination.pairGraph_adj_iff, h]

variable (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n))
  (H H' : Graph (Fin x.n) (Sym2 (Fin x.n)))
  (hHL : V(H) = (L : Set (Fin x.n))) (hHR : V(H') = (R : Set (Fin x.n)))
  (C : (gm02CompressedBoundaryInput x L R).schemes)

private theorem support_eq_of_pairs {α : Type*} {S T : Set α}
    (A : Termination S) (B : Termination T) (h : A.pairs = B.pairs) :
    A.support = B.support := by
  unfold Termination.support
  rw [h]

/-- The first parent terminal support is the old-name image of its boundary support. -/
theorem gm02ExpandCompressedBoundaryScheme_left_support :
    (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).left.support =
      compactEmb (gm02BoundaryDeletedSet x L R) '' C.left.support := by
  have hp := gm02ExpandCompressedBoundaryScheme_left_pairs x L R H H' hHL hHR C
  have hs := support_eq_of_pairs _
    (C.left.mapEmbedding (compactEmb (gm02BoundaryDeletedSet x L R)).toEmbedding)
    (by
      convert hp using 1
      simp only [Termination.mapEmbedding]
      apply Finset.coe_injective
      simp only [Finset.coe_image]
      rfl)
  exact hs.trans (C.left.mapEmbedding_support _)

/-- The second parent terminal support is the old-name image of its boundary support. -/
theorem gm02ExpandCompressedBoundaryScheme_right_support :
    (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).right.support =
      compactEmb (gm02BoundaryDeletedSet x L R) '' C.right.support := by
  have hp := gm02ExpandCompressedBoundaryScheme_right_pairs x L R H H' hHL hHR C
  have hs := support_eq_of_pairs _
    (C.right.mapEmbedding (compactEmb (gm02BoundaryDeletedSet x L R)).toEmbedding)
    (by
      convert hp using 1
      simp only [Termination.mapEmbedding]
      apply Finset.coe_injective
      simp only [Finset.coe_image]
      rfl)
  exact hs.trans (C.right.mapEmbedding_support _)

/-- The first parent matching is the increasing image of its boundary matching. -/
theorem gm02ExpandCompressedBoundaryScheme_left_pairGraph :
    (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).left.pairGraph =
      C.left.pairGraph.map (compactEmb (gm02BoundaryDeletedSet x L R)).toEmbedding := by
  exact (pairGraph_eq_of_pairs _
    (C.left.mapEmbedding (compactEmb (gm02BoundaryDeletedSet x L R)).toEmbedding)
    (by
      have hp := gm02ExpandCompressedBoundaryScheme_left_pairs x L R H H' hHL hHR C
      convert hp using 1
      simp only [Termination.mapEmbedding]
      apply Finset.coe_injective
      simp only [Finset.coe_image]
      rfl)).trans
      (C.left.mapEmbedding_pairGraph _)

/-- The second parent matching is the increasing image of its boundary matching. -/
theorem gm02ExpandCompressedBoundaryScheme_right_pairGraph :
    (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).right.pairGraph =
      C.right.pairGraph.map (compactEmb (gm02BoundaryDeletedSet x L R)).toEmbedding := by
  exact (pairGraph_eq_of_pairs _
    (C.right.mapEmbedding (compactEmb (gm02BoundaryDeletedSet x L R)).toEmbedding)
    (by
      have hp := gm02ExpandCompressedBoundaryScheme_right_pairs x L R H H' hHL hHR C
      convert hp using 1
      simp only [Termination.mapEmbedding]
      apply Finset.coe_injective
      simp only [Finset.coe_image]
      rfl)).trans
      (C.right.mapEmbedding_pairGraph _)

/-- Expanding boundary names preserves the first matching's index. -/
theorem gm02ExpandCompressedBoundaryScheme_left_index :
    (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).left.index = C.left.index := by
  unfold Termination.index
  rw [gm02ExpandCompressedBoundaryScheme_left_pairs]
  exact Finset.card_image_of_injective _ (Sym2.map.injective (compactEmb _).injective)

/-- Expanding boundary names preserves the second matching's index. -/
theorem gm02ExpandCompressedBoundaryScheme_right_index :
    (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).right.index = C.right.index := by
  unfold Termination.index
  rw [gm02ExpandCompressedBoundaryScheme_right_pairs]
  exact Finset.card_image_of_injective _ (Sym2.map.injective (compactEmb _).injective)

/-- The first parent endpoint words are obtained by fixed-template old-name lookup. -/
theorem gm02ExpandCompressedBoundaryScheme_left_pairWords :
    flatEdges (edgeListOf
      (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).left.pairGraph) =
      (edgeListOf C.left.pairGraph).flatMap (fun p =>
        [(compactEmb (gm02BoundaryDeletedSet x L R) p.1).val,
          (compactEmb (gm02BoundaryDeletedSet x L R) p.2).val]) := by
  simp only [gm02ExpandCompressedBoundaryScheme_left_pairGraph]
  rw [← gm02CompactMapped_edgeList, gm02FlatEdges_map]
  rfl

/-- The second parent endpoint words are obtained by fixed-template old-name lookup. -/
theorem gm02ExpandCompressedBoundaryScheme_right_pairWords :
    flatEdges (edgeListOf
      (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).right.pairGraph) =
      (edgeListOf C.right.pairGraph).flatMap (fun p =>
        [(compactEmb (gm02BoundaryDeletedSet x L R) p.1).val,
          (compactEmb (gm02BoundaryDeletedSet x L R) p.2).val]) := by
  simp only [gm02ExpandCompressedBoundaryScheme_right_pairGraph]
  rw [← gm02CompactMapped_edgeList, gm02FlatEdges_map]
  rfl

end GraphMinor.Compute
