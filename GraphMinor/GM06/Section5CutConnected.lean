module

public import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5BoundaryConnected
import GraphMinor.GM06.DiscRegions
import Mathlib.Topology.Maps.Basic

/-!
# Connectivity after the one-path cut

The augmented cut graph contains the connected disc boundary. Every
identification made by the cut projection is on that boundary. If its
point set could be separated into two closed pieces, their images would
separate the connected original graph with its cuffs adjoined. An image
intersection either lifts uniquely or joins the two pieces on the
connected boundary. This proves the cut graph is connected, as needed
for the region-boundary walk in VI (5.1).
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

universe u v

private theorem preconnected_of_closed_image_and_connected_identifications
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsClosedMap f) {F B : Set X}
    (hF : IsClosed F) (hB : IsPreconnected B) (hBF : B ⊆ F)
    (himage : IsPreconnected (f '' F))
    (hinj : ∀ a ∈ F \ B, ∀ b ∈ F, f a = f b → a = b) : IsPreconnected F := by
  apply isPreconnected_closed_iff.mpr
  intro U V hUc hVc hcover hUn hVn
  have hcov : f '' F ⊆ f '' (F ∩ U) ∪ f '' (F ∩ V) := by
    rintro _ ⟨x, hx, rfl⟩
    rcases hcover hx with hU | hV
    · exact Or.inl ⟨x, ⟨hx, hU⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨hx, hV⟩, rfl⟩
  have hnU : (f '' F ∩ f '' (F ∩ U)).Nonempty := by
    obtain ⟨x, hxF, hxU⟩ := hUn
    exact ⟨f x, ⟨x, hxF, rfl⟩, ⟨x, ⟨hxF, hxU⟩, rfl⟩⟩
  have hnV : (f '' F ∩ f '' (F ∩ V)).Nonempty := by
    obtain ⟨x, hxF, hxV⟩ := hVn
    exact ⟨f x, ⟨x, hxF, rfl⟩, ⟨x, ⟨hxF, hxV⟩, rfl⟩⟩
  obtain ⟨z, _, ⟨a, ha, haz⟩, ⟨b, hb, hbz⟩⟩ := isPreconnected_closed_iff.mp himage
    (f '' (F ∩ U)) (f '' (F ∩ V)) (hf _ (hF.inter hUc)) (hf _ (hF.inter hVc)) hcov hnU hnV
  have heq : f a = f b := haz.trans hbz.symm
  by_cases haB : a ∈ B
  · by_cases hbB : b ∈ B
    · obtain ⟨x, hxB, hxU, hxV⟩ := isPreconnected_closed_iff.mp hB U V hUc hVc
        (hBF.trans hcover) ⟨a, haB, ha.2⟩ ⟨b, hbB, hb.2⟩
      exact ⟨x, hBF hxB, hxU, hxV⟩
    · have hba := hinj b ⟨hb.1, hbB⟩ a ha.1 heq.symm
      exact ⟨a, ha.1, ha.2, hba ▸ hb.2⟩
  · have hab := hinj a ⟨ha.1, haB⟩ b hb.1 heq
    exact ⟨a, ha.1, ha.2, hab.symm ▸ hb.2⟩

/-- With no reduction available, the actual augmented cut drawing
has a connected point set. Its connected boundary contains every
pair identified by projection, and its image is G with both cuffs. -/
theorem isConnected_augmented_single_strip_of_no_reduction
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {F : Drawing D}
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D) :
    IsConnected F.U := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let f : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hf : Continuous f := continuous_radialCylinderProjection.comp continuous_subtype_val
  have hcut := isCutAlongSet_single_strip_projection L hG hθ hD hBd hstrip
  have hbimage : f '' bd D = bd ClosedCylinder ∪ (L.pathDrawing 0).U := by
    rw [← hcut.preimage_bd, image_preimage_eq _ hcut.quotientMap.surjective]
  have himage : f '' F.U = G.U ∪ bd ClosedCylinder := by
    rw [hFU, image_union, image_preimage_eq _ hcut.quotientMap.surjective, hbimage, ← union_assoc]
    exact union_eq_left.mpr ((L.isSubdrawing 0).2.trans subset_union_left)
  have hDisc : IsClosedDiscSpace D := hD
  have hB : IsConnected (bd D) := by
    obtain ⟨e⟩ := hDisc.isOArc_bd
    exact isConnected_iff_connectedSpace.mpr (e.surjective.connectedSpace e.continuous)
  have hBF : bd D ⊆ F.U := by
    rw [hFU]
    exact subset_union_right
  refine ⟨hB.nonempty.mono hBF, ?_⟩
  apply preconnected_of_closed_image_and_connected_identifications hf.isClosedMap F.isClosed_U
    hB.isPreconnected hBF
  · rw [himage]
    exact (isConnected_union_boundary_of_no_section5_reduction L hG hno).isPreconnected
  · intro a ha b _ heq
    exact hcut.interior_inj a ha.2 b heq

end GraphMinor.GM06
