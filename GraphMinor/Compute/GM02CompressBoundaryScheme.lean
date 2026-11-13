module

public import GraphMinor.Compute.GM02ExpandCompressedScheme
public import GraphMinor.GM02.CrossingSchemeBoundaryData
import GraphMinor.GM02.CrossingSchemeRenamingData

/-!
# Compressing parent crossing schemes into the finite catalogue

Restrict a parent scheme to the terminal and separator boundary, then
apply compact numbering. The resulting side sets and termination agree
with the encoded catalogue input, so every parent scheme has a catalogue
representative.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Restricting and numbering a parent scheme gives a valid catalogue scheme. -/
noncomputable def gm02CompressBoundaryScheme (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (H H' : Graph (Fin x.n) (Sym2 (Fin x.n)))
    (hHL : V(H) = (L : Set (Fin x.n))) (hHR : V(H') = (R : Set (Fin x.n)))
    (C : CrossingScheme (Graph.ofSimpleGraph x.G) H H' x.A) :
    (gm02CompressedBoundaryInput x L R).schemes := by
  let Z := gm02BoundaryDeletedSet x L R
  let S := {v : Fin x.n | v ∉ Z}
  let B := gm02CompressedBoundaryInput x L R
  let e := gm02CompactEquiv Z
  have hAS : x.A.support ⊆ S := gm02Boundary_support_survives x L R
  have hXS : V(H) ∩ V(H') ⊆ S := gm02Boundary_separator_survives x L R H H' hHL hHR
  let D := (C.induceBoundary hAS hXS).mapEquiv e
  have hVG : V(Graph.noEdge (e '' (Set.univ : Set S)) (Sym2 (Fin x.n))) =
      V(Graph.noEdge (Set.univ : Set (Fin B.n)) Unit) := by
    change e '' Set.univ = Set.univ
    exact Set.image_univ_of_surjective e.surjective
  have hVL : V(Graph.noEdge (e '' (Subtype.val ⁻¹' V(H) : Set S)) (Sym2 (Fin x.n))) =
      V(Graph.noEdge (B.left : Set (Fin B.n)) Unit) := by
    change e '' (Subtype.val ⁻¹' V(H)) = (B.left : Set (Fin B.n))
    rw [hHL]
    exact gm02CompactPullback_image Z L
  have hVR : V(Graph.noEdge (e '' (Subtype.val ⁻¹' V(H') : Set S)) (Sym2 (Fin x.n))) =
      V(Graph.noEdge (B.right : Set (Fin B.n)) Unit) := by
    change e '' (Subtype.val ⁻¹' V(H')) = (B.right : Set (Fin B.n))
    rw [hHR]
    exact gm02CompactPullback_image Z R
  have hApairs : B.A.pairs = (((x.A.rebase hAS).onVertices).mapEmbedding e.toEmbedding).pairs := rfl
  exact D.transferVertexSets (Graph.noEdge (Set.univ : Set (Fin B.n)) Unit)
    (Graph.noEdge (B.left : Set (Fin B.n)) Unit)
    (Graph.noEdge (B.right : Set (Fin B.n)) Unit) hVG hVL hVR B.A hApairs

section Data
set_option backward.isDefEq.respectTransparency.types false
variable (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n))
  (H H' : Graph (Fin x.n) (Sym2 (Fin x.n)))
  (hHL : V(H) = (L : Set (Fin x.n))) (hHR : V(H') = (R : Set (Fin x.n)))
  (C : CrossingScheme (Graph.ofSimpleGraph x.G) H H' x.A)

/-- Looking up original names after compression recovers the first pair set. -/
theorem gm02CompressBoundaryScheme_left_pairs :
    (gm02CompressBoundaryScheme x L R H H' hHL hHR C).left.pairs.image
      (Sym2.map (compactEmb (gm02BoundaryDeletedSet x L R))) = C.left.pairs := by
  unfold gm02CompressBoundaryScheme
  rw [CrossingScheme.transferVertexSets_left_pairs, CrossingScheme.mapEquiv_left_pairs]
  apply Finset.coe_injective
  simp only [Finset.coe_image]
  rw [gm02Compact_pair_images]
  have he := congrArg
    (fun P : Finset (Sym2 (Fin x.n)) => (P : Set (Sym2 (Fin x.n))))
    (C.induceBoundary_left_pairs_map
      (gm02Boundary_support_survives x L R)
      (gm02Boundary_separator_survives x L R H H' hHL hHR))
  simp only [Finset.coe_image] at he
  convert he using 1; rfl

/-- Looking up original names after compression recovers the second pair set. -/
theorem gm02CompressBoundaryScheme_right_pairs :
    (gm02CompressBoundaryScheme x L R H H' hHL hHR C).right.pairs.image
      (Sym2.map (compactEmb (gm02BoundaryDeletedSet x L R))) = C.right.pairs := by
  unfold gm02CompressBoundaryScheme
  rw [CrossingScheme.transferVertexSets_right_pairs, CrossingScheme.mapEquiv_right_pairs]
  apply Finset.coe_injective
  simp only [Finset.coe_image]
  rw [gm02Compact_pair_images]
  have he := congrArg
    (fun P : Finset (Sym2 (Fin x.n)) => (P : Set (Sym2 (Fin x.n))))
    (C.induceBoundary_right_pairs_map
      (gm02Boundary_support_survives x L R)
      (gm02Boundary_separator_survives x L R H H' hHL hHR))
  simp only [Finset.coe_image] at he
  convert he using 1; rfl

/-- Looking up original names after compression recovers the first reserved set. -/
theorem gm02CompressBoundaryScheme_reservedLeft :
    compactEmb (gm02BoundaryDeletedSet x L R) ''
      (gm02CompressBoundaryScheme x L R H H' hHL hHR C).reservedLeft = C.reservedLeft := by
  unfold gm02CompressBoundaryScheme
  rw [CrossingScheme.transferVertexSets_reservedLeft, CrossingScheme.mapEquiv_reservedLeft,
    gm02Compact_vertex_images]
  exact C.induceBoundary_reservedLeft_image _ _

/-- Looking up original names after compression recovers the second reserved set. -/
theorem gm02CompressBoundaryScheme_reservedRight :
    compactEmb (gm02BoundaryDeletedSet x L R) ''
      (gm02CompressBoundaryScheme x L R H H' hHL hHR C).reservedRight = C.reservedRight := by
  unfold gm02CompressBoundaryScheme
  rw [CrossingScheme.transferVertexSets_reservedRight, CrossingScheme.mapEquiv_reservedRight,
    gm02Compact_vertex_images]
  exact C.induceBoundary_reservedRight_image _ _
/-- Compressing and then expanding recovers the entire parent scheme. -/
theorem gm02ExpandCompressedBoundaryScheme_compress :
    gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR
      (gm02CompressBoundaryScheme x L R H H' hHL hHR C) = C := by
  apply CrossingScheme.ext_data
  · apply Termination.ext_pairs
    rw [gm02ExpandCompressedBoundaryScheme_left_pairs,
      gm02CompressBoundaryScheme_left_pairs]
  · apply Termination.ext_pairs
    rw [gm02ExpandCompressedBoundaryScheme_right_pairs,
      gm02CompressBoundaryScheme_right_pairs]
  · rw [gm02ExpandCompressedBoundaryScheme_reservedLeft,
      gm02CompressBoundaryScheme_reservedLeft]
  · rw [gm02ExpandCompressedBoundaryScheme_reservedRight,
      gm02CompressBoundaryScheme_reservedRight]

/-- Expansion of numbered boundary schemes covers all parent schemes. -/
theorem gm02ExpandCompressedBoundaryScheme_surjective :
    Function.Surjective (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR) := by
  intro D
  exact ⟨gm02CompressBoundaryScheme x L R H H' hHL hHR D,
    gm02ExpandCompressedBoundaryScheme_compress x L R H H' hHL hHR D⟩

end Data

end GraphMinor.Compute
