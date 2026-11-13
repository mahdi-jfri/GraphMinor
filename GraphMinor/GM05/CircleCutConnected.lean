module

public import GraphMinor.GM05.SurfaceDescent
import GraphMinor.GM05.CutComplement
import GraphMinor.GM05.CutConnected
import GraphMinor.GM05.CutOrientation
import GraphMinor.GM05.TwoSidedCut
import GraphMinor.GM05.TwoSidedSimpler
import GraphMinor.GM05.CuffPair
import GraphMinor.GM05.CappingPair
import GraphMinor.GM05.CappingGenus
import GraphMinor.GM19.CapOrient
import GraphMinor.GM19.CapExists
import GraphMinor.GM19.Perimeter
import GraphMinor.Surface.CutComp

/-!
# The connected-complement case of the circle cut

In Graph Minors V, (8.10), a circle with connected complement does not
bound a disc. Cut it into two boundary lifts, cap those two cuffs, and
pull the original orientation to the cut surface before extending it
over the caps. The normal-word comparison gives a strict genus drop.
This file carries out that case for a surface represented by its handle
model, keeping the homeomorphism of complementary open surfaces.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM19

/-- The connected-complement case of Graph Minors V, (8.10), page 112,
for a connected orientable surface represented by its handle model.
The complement homeomorphism is the inverse capping embedding followed
by the cutting surjection. -/
theorem lemma_8_10_connected_complement {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsClosedSurface S) (hO : IsOrientableSurface S)
    {g : ℕ} (eS : S ≃ₜ SurfaceModel g 0 0) {C : Set S}
    (hC : IsOArc C) (hc : IsConnected Cᶜ) :
    ∃ (T : Type) (_ : TopologicalSpace T) (hT : IsClosedSurface T),
      IsOrientableSurface T ∧ SurfaceGenusLT hT hS ∧
      ∃ D D' : Set T, IsClosedDisc D ∧ IsClosedDisc D' ∧ Disjoint D D' ∧
        Nonempty (↥((D ∪ D')ᶜ) ≃ₜ ↥(Cᶜ)) := by
  let : T2Space S := hS.2.1
  obtain ⟨Y,τY,ψ,hY,hψ,X,X',hd,hunion,hX,hX',hb,hb'⟩ :=
    exists_two_sided_handle_cut hS eS hC
  let : CompactSpace Y := hY.1
  let : T2Space Y := hY.2.1
  let : ConnectedSpace Y := connected_cut_of_complement hY hS hψ hC.isCompact.isClosed hc
  have hsimpler := simpler_two_sided_cut hY hψ hd hunion hX hX' hb hb'
  have hYorient := orientable_of_cutting hY hψ hO
  obtain ⟨T,τT,⟨cap⟩⟩ := exists_cappedSurface _ Y hY inferInstance rfl
  let : T2Space T := cap.isSurface.2.1
  obtain ⟨oY⟩ := hYorient
  obtain ⟨oT,-⟩ := exists_cap_orientation hY cap oY
  have hgenus := surfaceGenusLT_capping_of_simpler cap hS hsimpler eS
  have hbd : bd Y=X ∪ X' := (cutting_boundary_eq hψ hC.isCompact.isClosed hS).trans hunion.symm
  have hcuffs := cuffs_eq_pair_of_boundary hY hX hX' hbd
  have hne : X ≠ X' := by
    intro he
    obtain ⟨e⟩ := hX
    have hx : (e 1).1 ∈ X := (e 1).2
    exact Set.disjoint_left.mp hd hx (he ▸ hx)
  obtain ⟨D,D',hD,hD',hdis,⟨f⟩⟩ := capped_pair_complement hY cap hcuffs hne
  obtain ⟨e⟩ := cutting_complement_homeomorph hψ
  have he : (bd Y)ᶜ=ψ ⁻¹' Cᶜ := by
    rw [cutting_boundary_eq hψ hC.isCompact.isClosed hS,preimage_compl]
  exact ⟨T,τT,cap.isClosedSurface,⟨oT⟩,hgenus,D,D',hD,hD',hdis,
    ⟨f.symm.trans ((Homeomorph.setCongr he).trans e)⟩⟩

end GraphMinor.GM05
