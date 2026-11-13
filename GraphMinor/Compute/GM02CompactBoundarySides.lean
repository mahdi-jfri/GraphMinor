module

public import GraphMinor.Compute.GM02CompactTermination
public import GraphMinor.Compute.GM02PullbackBits
import Mathlib.Logic.Equiv.Set

/-!
# Returning numbered boundary memberships to the vertex subtype

The inverse compact numbering sends numbered side flags back to exactly
the original side's intersection with the retained vertex subtype.
Applying the inverse numbering to the compact termination also recovers
its subtype endpoint pairs. These identities align the finite catalogue
objects with the hypotheses of boundary-scheme expansion.
-/

public section
namespace GraphMinor.Compute
open Set Classical GraphMinor.GM02

/-- A compact vertex and its inverse name have the same original vertex. -/
theorem gm02CompactEmb_equiv_apply {n : ℕ} (Z : Finset (Fin n))
    (a : {v : Fin n // v ∉ Z}) : compactEmb Z (gm02CompactEquiv Z a) = a.val := by
  calc
    compactEmb Z (gm02CompactEquiv Z a) = ((gm02CompactEquiv Z).symm (gm02CompactEquiv Z a)).val :=
      (gm02CompactEquiv_symm_val Z _).symm
    _ = a.val := congrArg Subtype.val ((gm02CompactEquiv Z).symm_apply_apply a)

/-- Pullback side flags return to exactly the side membership on the
surviving-vertex subtype. -/
theorem gm02CompactPullback_image_symm {n : ℕ} (Z : Finset (Fin n)) (L : Finset (Fin n)) :
    (gm02CompactEquiv Z).symm ''
        (gm02PullbackVertexSet (compactEmb Z) L : Set (Fin Zᶜ.card)) =
      Subtype.val ⁻¹' (L : Set (Fin n)) := by
  rw [Equiv.image_eq_preimage_symm]
  ext a
  simp only [Equiv.symm_symm, Set.mem_preimage, Finset.mem_coe, gm02PullbackVertexSet,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [gm02CompactEmb_equiv_apply]

/-- Inverse compact numbering recovers the original subtype pair set. -/
theorem gm02CompactTermination_unmap_pairs {n : ℕ} (Z : Finset (Fin n))
    (A : Termination {v : Fin n | v ∉ Z}) :
    ((gm02CompactTermination Z A).mapEmbedding (gm02CompactEquiv Z).symm.toEmbedding).pairs =
      A.onVertices.pairs := by
  change ((A.onVertices.mapEmbedding (gm02CompactEquiv Z).toEmbedding).mapEmbedding
    (gm02CompactEquiv Z).symm.toEmbedding).pairs = A.onVertices.pairs
  exact A.onVertices.mapEquiv_symm_pairs (gm02CompactEquiv Z)

/-- Compact numbering followed by old-name lookup is the subtype inclusion. -/
theorem gm02Compact_forward_function {n : ℕ} (Z : Finset (Fin n)) :
    (compactEmb Z ∘ gm02CompactEquiv Z) = Subtype.val := by
  funext a
  exact gm02CompactEmb_equiv_apply Z a

/-- Mapping pair sets through compact numbering and old names recovers
their image under subtype inclusion. -/
theorem gm02Compact_pair_images {n : ℕ} (Z : Finset (Fin n))
    (P : Set (Sym2 {v : Fin n // v ∉ Z})) :
    Sym2.map (compactEmb Z) '' (Sym2.map (gm02CompactEquiv Z) '' P) =
      Sym2.map Subtype.val '' P := by
  rw [Set.image_image]
  simp only [Sym2.map_map]
  exact congrArg (fun f => Sym2.map f '' P) (gm02Compact_forward_function Z)

/-- Mapping vertex sets through compact numbering and old names recovers
their image under subtype inclusion. -/
theorem gm02Compact_vertex_images {n : ℕ} (Z : Finset (Fin n)) (P : Set {v : Fin n // v ∉ Z}) :
    compactEmb Z '' (gm02CompactEquiv Z '' P) = Subtype.val '' P := by
  rw [Set.image_image]
  exact congrArg (fun f => f '' P) (gm02Compact_forward_function Z)

/-- Forward compact numbering carries the original side membership on the
surviving subtype to the numbered side flags. -/
theorem gm02CompactPullback_image {n : ℕ} (Z : Finset (Fin n)) (L : Finset (Fin n)) :
    gm02CompactEquiv Z '' (Subtype.val ⁻¹' (L : Set (Fin n))) =
      (gm02PullbackVertexSet (compactEmb Z) L : Set (Fin Zᶜ.card)) := by
  calc
    _ = gm02CompactEquiv Z '' ((gm02CompactEquiv Z).symm ''
        (gm02PullbackVertexSet (compactEmb Z) L : Set (Fin Zᶜ.card))) :=
      congrArg (Set.image (gm02CompactEquiv Z)) (gm02CompactPullback_image_symm Z L).symm
    _ = _ := by simp only [Set.image_image, Equiv.apply_symm_apply, Set.image_id']

end GraphMinor.Compute
