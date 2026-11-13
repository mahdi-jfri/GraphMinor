module

public import GraphMinor.Compute.GM02CompressedBoundary
public import GraphMinor.Compute.GM02CompactBoundarySides
public import GraphMinor.GM02.CrossingSchemeExpand
public import GraphMinor.GM02.CrossingSchemeTransfer
public import GraphMinor.GM02.CrossingSchemeRenaming
import GraphMinor.GM02.CrossingSchemeRenamingData

/-!
# Turning catalogue schemes into actual recursive parent schemes

Undo the compact numbering of a valid catalogue scheme. Its side flags
become exactly the original side memberships on the boundary, and its
original pairs become the original subtype termination. Transfer these
data to the boundary graphs used by the expansion theorem, then expand
through the subtype inclusion. This gives an actual parent crossing
scheme for every valid catalogue pattern.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Every valid scheme of the computed finite boundary gives an actual
scheme on parent sides with the encoded vertex sets. -/
noncomputable def gm02ExpandCompressedBoundaryScheme (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (H H' : Graph (Fin x.n) (Sym2 (Fin x.n)))
    (hHL : V(H) = (L : Set (Fin x.n))) (hHR : V(H') = (R : Set (Fin x.n)))
    (C : (gm02CompressedBoundaryInput x L R).schemes) :
    CrossingScheme (Graph.ofSimpleGraph x.G) H H' x.A := by
  let Z := gm02BoundaryDeletedSet x L R
  let S := {v : Fin x.n | v ∉ Z}
  let B := gm02CompressedBoundaryInput x L R
  let e := gm02CompactEquiv Z
  have hAS : x.A.support ⊆ S := gm02Boundary_support_survives x L R
  have hSG : S ⊆ V(Graph.ofSimpleGraph x.G) := fun _ _ => trivial
  have hXS : V(H) ∩ V(H') ⊆ S := gm02Boundary_separator_survives x L R H H' hHL hHR
  let A₀ := (x.A.rebase hAS).onVertices
  let D := C.mapEquiv e.symm
  have hVG : V(Graph.noEdge (e.symm '' (Set.univ : Set (Fin B.n))) Unit) =
      V(Graph.noEdge (Set.univ : Set S) Unit) := by
    change e.symm '' Set.univ = Set.univ
    exact Set.image_univ_of_surjective e.symm.surjective
  have hVL : V(Graph.noEdge (e.symm '' (B.left : Set (Fin B.n))) Unit) =
      V(Graph.noEdge (Subtype.val ⁻¹' V(H)) Unit) := by
    change e.symm '' (B.left : Set (Fin B.n)) = Subtype.val ⁻¹' V(H)
    rw [hHL]
    exact gm02CompactPullback_image_symm Z L
  have hVR : V(Graph.noEdge (e.symm '' (B.right : Set (Fin B.n))) Unit) =
      V(Graph.noEdge (Subtype.val ⁻¹' V(H')) Unit) := by
    change e.symm '' (B.right : Set (Fin B.n)) = Subtype.val ⁻¹' V(H')
    rw [hHR]
    exact gm02CompactPullback_image_symm Z R
  have hApairs : A₀.pairs = (B.A.mapEmbedding e.symm.toEmbedding).pairs :=
    (gm02CompactTermination_unmap_pairs Z (x.A.rebase hAS)).symm
  let E := D.transferVertexSets (Graph.noEdge (Set.univ : Set S) Unit)
    (Graph.noEdge (Subtype.val ⁻¹' V(H)) Unit) (Graph.noEdge (Subtype.val ⁻¹' V(H')) Unit)
    hVG hVL hVR A₀ hApairs
  exact CrossingScheme.expandBoundary (Graph.ofSimpleGraph x.G) H H' x.A hSG hAS hXS E

private theorem compact_inverse_function {n : ℕ} (Z : Finset (Fin n)) :
    (Subtype.val ∘ (gm02CompactEquiv Z).symm) = compactEmb Z := by
  funext i
  exact gm02CompactEquiv_symm_val Z i

section Data
set_option backward.isDefEq.respectTransparency.types false
variable (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n))
  (H H' : Graph (Fin x.n) (Sym2 (Fin x.n)))
  (hHL : V(H) = (L : Set (Fin x.n))) (hHR : V(H') = (R : Set (Fin x.n)))
  (C : (gm02CompressedBoundaryInput x L R).schemes)

/-- Expanding a numbered scheme maps its first pair set by the stored old names. -/
theorem gm02ExpandCompressedBoundaryScheme_left_pairs :
    (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).left.pairs =
      C.left.pairs.image (Sym2.map (compactEmb (gm02BoundaryDeletedSet x L R))) := by
  unfold gm02ExpandCompressedBoundaryScheme
  rw [CrossingScheme.expandBoundary_left_pairs, CrossingScheme.transferVertexSets_left_pairs,
    CrossingScheme.mapEquiv_left_pairs]
  apply Finset.coe_injective
  simp only [Finset.coe_image, Set.image_image, Sym2.map_map]
  exact congrArg (fun f => Sym2.map f '' (C.left.pairs : Set (Sym2 (Fin (gm02CompressedBoundaryInput x L R).n))))
    (compact_inverse_function (gm02BoundaryDeletedSet x L R))

/-- Expanding a numbered scheme maps its second pair set by the stored old names. -/
theorem gm02ExpandCompressedBoundaryScheme_right_pairs :
    (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).right.pairs =
      C.right.pairs.image (Sym2.map (compactEmb (gm02BoundaryDeletedSet x L R))) := by
  unfold gm02ExpandCompressedBoundaryScheme
  rw [CrossingScheme.expandBoundary_right_pairs, CrossingScheme.transferVertexSets_right_pairs,
    CrossingScheme.mapEquiv_right_pairs]
  apply Finset.coe_injective
  simp only [Finset.coe_image, Set.image_image, Sym2.map_map]
  exact congrArg (fun f => Sym2.map f '' (C.right.pairs : Set (Sym2 (Fin (gm02CompressedBoundaryInput x L R).n))))
    (compact_inverse_function (gm02BoundaryDeletedSet x L R))

/-- Expanding a numbered scheme maps its first reserved set by the stored old names. -/
theorem gm02ExpandCompressedBoundaryScheme_reservedLeft :
    (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).reservedLeft =
      compactEmb (gm02BoundaryDeletedSet x L R) '' C.reservedLeft := by
  unfold gm02ExpandCompressedBoundaryScheme
  rw [CrossingScheme.expandBoundary_reservedLeft, CrossingScheme.transferVertexSets_reservedLeft,
    CrossingScheme.mapEquiv_reservedLeft]
  simp only [Set.image_image]
  exact congrArg (fun f => f '' C.reservedLeft)
    (compact_inverse_function (gm02BoundaryDeletedSet x L R))

/-- Expanding a numbered scheme maps its second reserved set by the stored old names. -/
theorem gm02ExpandCompressedBoundaryScheme_reservedRight :
    (gm02ExpandCompressedBoundaryScheme x L R H H' hHL hHR C).reservedRight =
      compactEmb (gm02BoundaryDeletedSet x L R) '' C.reservedRight := by
  unfold gm02ExpandCompressedBoundaryScheme
  rw [CrossingScheme.expandBoundary_reservedRight, CrossingScheme.transferVertexSets_reservedRight,
    CrossingScheme.mapEquiv_reservedRight]
  simp only [Set.image_image]
  exact congrArg (fun f => f '' C.reservedRight)
    (compact_inverse_function (gm02BoundaryDeletedSet x L R))
end Data

end GraphMinor.Compute
