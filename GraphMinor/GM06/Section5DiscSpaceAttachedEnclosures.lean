module

public import GraphMinor.Surface.DiscGrow
public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5FiniteDiscardedEnclosures
import GraphMinor.GM06.Section5DiscSphereEmbedding
import GraphMinor.GM06.Section5EmbeddedInteriorContainment
import GraphMinor.GM06.Section5ContractionNeighbourPolar
import GraphMinor.GM07.Section9MoveOff
import GraphMinor.Surface.SurfacePull
import GraphMinor.GM11.Regions

/-!
# Attached-side enclosures inside the cut disc

For the one-path Reduction 2 argument of VI (5.5), page 130,
embed the cut disc in the sphere. Its retained punctured barrier
contains the boundary, so each region meeting the other drawing
stays inside the open disc image. The finite sphere enclosures
therefore pull back to discs in the cut space. Each meets the cut
boundary only possibly at the attachment, which will make projection
back to the cylinder injective on the whole enclosing disc.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- A punctured barrier containing a disc-space boundary gives
finite discarded-side enclosures meeting that boundary only at
the attachment. -/
theorem exists_disc_space_discs_enclosing_attached_side
    {S : Type} [TopologicalSpace S] [T2Space S] (hDisc : IsClosedDiscSpace S)
    {Γ T H : Drawing S} (hT : T.IsSubdrawing Γ) (hH : H.IsSubdrawing Γ)
    {s w : S} (hsV : s ∈ Γ.V) (hwV : w ∈ Γ.V)
    (hsb : s ∈ bd S) (hwb : w ∈ bd S) (hsw : s ≠ w)
    (hsT : s ∈ T.U) (hTp : IsConnected (T.U \ {s}))
    (hscl : s ∈ closure (T.U \ {s})) (hbdT : bd S ⊆ T.U)
    (hover : H.U ∩ T.U ⊆ {s}) (hcover : Γ.U ⊆ T.U ∪ H.U) :
    ∃ F : Set (Set S), F.Finite ∧
      (∀ D ∈ F, IsClosedDisc D ∧ discBd D ∩ Γ.U ⊆ {s} ∧ D ∩ bd S ⊆ {s}) ∧
      H.U \ {s} ⊆ ⋃ D ∈ F, discInt D := by
  let : Nonempty S := ⟨s⟩
  let : CompactSpace S := compactSpace_of_isClosedDiscSpace hDisc
  obtain ⟨j, hj, hopen, _⟩ := exists_closedDisc_sphere_embedding hDisc
  let Γ' := GM07.embedDrawing hj Γ
  let T' := GM07.embedDrawing hj T
  let H' := GM07.embedDrawing hj H
  have hΓU : Γ'.U = j '' Γ.U := GM07.embedDrawing_U hj Γ
  have hTU : T'.U = j '' T.U := GM07.embedDrawing_U hj T
  have hHU : H'.U = j '' H.U := GM07.embedDrawing_U hj H
  have hTΓ : T'.IsSubdrawing Γ' := by
    constructor
    · rw [GM07.embedDrawing_V, GM07.embedDrawing_V]; exact image_mono hT.1
    · rw [GM07.embedDrawing_E, GM07.embedDrawing_E]; exact image_mono hT.2
  have hHΓ : H'.IsSubdrawing Γ' := by
    constructor
    · rw [GM07.embedDrawing_V, GM07.embedDrawing_V]; exact image_mono hH.1
    · rw [GM07.embedDrawing_E, GM07.embedDrawing_E]; exact image_mono hH.2
  have hsc : j s ∈ T'.U := hTU.symm ▸ mem_image_of_mem _ hsT
  have hpun : T'.U \ {j s} = j '' (T.U \ {s}) := by
    rw [hTU, image_sdiff hj.injective, image_singleton]
  have hconn : IsConnected (T'.U \ {j s}) := by
    rw [hpun]; exact hTp.image j hj.continuous.continuousOn
  have hsacc : j s ∈ closure (T'.U \ {j s}) := by
    rw [hpun]; exact mem_closure_image hj.continuous.continuousAt hscl
  have hmeet : H'.U ∩ T'.U ⊆ {j s} := by
    rw [hHU, hTU]
    rintro y ⟨⟨x, hxH, rfl⟩, z, hzT, he⟩
    have hzx : z = x := hj.injective he
    exact congrArg j (hover ⟨hxH, hzx ▸ hzT⟩)
  have hcov : Γ'.U ⊆ T'.U ∪ H'.U := by
    rw [hΓU, hTU, hHU, ← image_union]
    exact image_mono hcover
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
  have hB : IsOArc (j '' bd S) := by
    obtain ⟨b⟩ := hDisc.isOArc_bd
    exact ⟨b.trans (hj.isEmbedding.homeomorphImage (bd S))⟩
  have hBΓ : j '' bd S ⊆ Γ'.U := by
    rw [hΓU]; exact image_mono (hbdT.trans hT.U_subset)
  have hvs : j s ∈ Γ'.V := by rw [GM07.embedDrawing_V]; exact mem_image_of_mem _ hsV
  have hvw : j w ∈ Γ'.V := by rw [GM07.embedDrawing_V]; exact mem_image_of_mem _ hwV
  obtain ⟨Φ, hp⟩ := exists_polar_at_vertex_on_oArc hS.1 Γ' hB hBΓ hvs hvw
    (mem_image_of_mem _ hsb) (mem_image_of_mem _ hwb) (fun he => hsw (hj.injective he))
  obtain ⟨F, hF, hdisc, hFc⟩ := exists_finite_discarded_region_enclosures
    hS.1 hsph hTΓ hHΓ hp hsc hconn.isPreconnected hsacc hmeet hcov
  have hsub (D) (hD : D ∈ F) : D ⊆ range j := by
    obtain ⟨_, _, _, r, hr, hHr, hDr⟩ := hdisc D hD
    have hmiss : Disjoint r (j '' bd S) := by
      apply disjoint_left.mpr
      rintro y hyr ⟨x, hx, rfl⟩
      exact region_subset hr hyr (hTU.symm ▸ mem_image_of_mem _ (hbdT hx))
    obtain ⟨y, hyH, hyr⟩ := hHr
    have hyrange : y ∈ range j := image_subset_range _ _ (hHU ▸ hyH)
    have hrsub := subset_embedded_interior_of_preconnected hj hopen
      (region_isPreconnected hr) hmiss ⟨y, hyr, hyrange⟩
    intro y hy
    rcases hDr hy with hyr | hys
    · exact image_subset_range _ _ (hrsub hyr)
    · exact mem_singleton_iff.mp hys ▸ mem_range_self s
  have hpull (D) (hD : D ∈ F) := isClosedDisc_preimage hj (hdisc D hD).1 (hsub D hD)
  refine ⟨(fun D => j ⁻¹' D) '' F, hF.image _, ?_, ?_⟩
  · rintro _ ⟨D, hD, rfl⟩
    refine ⟨(hpull D hD).1, ?_, ?_⟩
    · rw [(hpull D hD).2]
      rintro x ⟨hxb, hxΓ⟩
      exact hj.injective ((hdisc D hD).2.1 ⟨hxb, hΓU.symm ▸ mem_image_of_mem _ hxΓ⟩)
    · rintro x ⟨hxD, hxbd⟩
      exact hj.injective ((hdisc D hD).2.2.1 ⟨hxD, hTU.symm ▸ mem_image_of_mem _ (hbdT hxbd)⟩)
  · rintro x ⟨hxH, hxs⟩
    have hxcap : j x ∈ H'.U \ {j s} :=
      ⟨hHU.symm ▸ mem_image_of_mem _ hxH, fun he => hxs (hj.injective he)⟩
    obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp (hFc hxcap)
    refine mem_iUnion₂.mpr ⟨j ⁻¹' D, mem_image_of_mem _ hD, hxD.1, ?_⟩
    rw [(hpull D hD).2]
    exact hxD.2

end GraphMinor.GM06
