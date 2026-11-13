module

public import GraphMinor.GM05.SurfaceDescent
import GraphMinor.GM05.TwoSidedCut
import GraphMinor.GM05.TwoSidedSimpler
import GraphMinor.GM05.CutConnected
import GraphMinor.GM05.CutComplement
import GraphMinor.GM05.CuffPair
import GraphMinor.GM05.CappingPair
import GraphMinor.GM05.CappingGenus
import GraphMinor.GM19.CapModel
import GraphMinor.GM19.Perimeter

/-!
# Retaining the handle model after a nonseparating cut

For the surface choice in GM V, (8.14), keep the explicit handle-model
representation through the circle-cut construction of (8.10). The
normal-word calculation and capping give a lower handle model directly.
The complement identification is the same cutting and capping map.
-/

public section
namespace GraphMinor.GM05
open Set Topology Surface GM19

/-- The connected-complement cut of GM V, (8.10), retaining its
explicit handle model for use in the proof of (8.14). -/
theorem exists_lower_handle_cut_connected {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {g : ℕ}
    (eS : S ≃ₜ SurfaceModel g 0 0) {C : Set S} (hC : IsOArc C) (hc : IsConnected Cᶜ) :
    ∃ (T : Type) (_ : TopologicalSpace T) (hT : IsClosedSurface T),
      (∃ a : ℕ,a<g ∧ Nonempty (T ≃ₜ SurfaceModel a 0 0)) ∧ SurfaceGenusLT hT hS ∧
      ∃ D D' : Set T,IsClosedDisc D ∧ IsClosedDisc D' ∧ Disjoint D D' ∧
        Nonempty (↥((D ∪ D')ᶜ) ≃ₜ ↥(Cᶜ)) := by
  let : T2Space S := hS.2.1
  obtain ⟨Y,τY,ψ,hY,hψ,X,X',hd,hunion,hX,hX',hb,hb'⟩ :=
    exists_two_sided_handle_cut hS eS hC
  let : CompactSpace Y := hY.1
  let : T2Space Y := hY.2.1
  let : ConnectedSpace Y := connected_cut_of_complement hY hS hψ hC.isCompact.isClosed hc
  have hsimpler := simpler_two_sided_cut hY hψ hd hunion hX hX' hb hb'
  obtain ⟨T,τT,⟨cap⟩⟩ := exists_cappedSurface _ Y hY inferInstance rfl
  let : T2Space T := cap.isSurface.2.1
  have hmodels := exists_handle_model_capping_of_simpler cap hsimpler eS
  have hgenus := surfaceGenusLT_capping_of_simpler cap hS hsimpler eS
  have hbd : bd Y=X ∪ X' := (cutting_boundary_eq hψ hC.isCompact.isClosed hS).trans hunion.symm
  have hcuffs := cuffs_eq_pair_of_boundary hY hX hX' hbd
  have hne : X≠X' := by
    intro he
    obtain ⟨e⟩ := hX
    exact disjoint_left.mp hd (e 1).prop (he ▸ (e 1).prop)
  obtain ⟨D,D',hD,hD',hdis,⟨f⟩⟩ := capped_pair_complement hY cap hcuffs hne
  obtain ⟨e⟩ := cutting_complement_homeomorph hψ
  have he : (bd Y)ᶜ=ψ ⁻¹' Cᶜ := by
    rw [cutting_boundary_eq hψ hC.isCompact.isClosed hS,preimage_compl]
  exact ⟨T,τT,cap.isClosedSurface,hmodels,hgenus,D,D',hD,hD',hdis,
    ⟨f.symm.trans ((Homeomorph.setCongr he).trans e)⟩⟩

end GraphMinor.GM05
