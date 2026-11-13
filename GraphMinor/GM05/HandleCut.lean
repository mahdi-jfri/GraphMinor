module

public import GraphMinor.GM05.SurfaceDescent
import GraphMinor.GM05.HandleCutConnected
import GraphMinor.GM05.HandleCutSeparating
import GraphMinor.GM05.TwoSidedCut
import GraphMinor.GM05.CutComplement
import GraphMinor.GM05.ComponentHandleModels
import GraphMinor.Surface.ModelCriterion
import GraphMinor.GM19.CutFragment
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.DiscMerge

/-!
# A connected handle surface cut with its models retained

For the minimal surface in GM V, (8.14), combine the two circle-cut
cases from (8.10), retaining the explicit handle models of the
replacement components. This uses the same connectedness and cutting
argument, with model data in place of an orientation of the replacement.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM19

/-- The connected handle-model form of GM V, (8.10), retaining the
representations needed for the surface choice in (8.14). -/
theorem exists_lower_handle_cut {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsClosedSurface S)
    {g : ℕ} (eS : S ≃ₜ SurfaceModel g 0 0) {C : Set S} (hC : IsOArc C) :
    (∃ D : Set S,IsClosedDisc D ∧ C=discBd D) ∨
    ∃ (T : Type) (_ : TopologicalSpace T) (hT : IsClosedSurface T),
      (∀ x : T,∃ a : ℕ,Nonempty ((connectedComponent x) ≃ₜ SurfaceModel a 0 0)) ∧
      SurfaceGenusLT hT hS ∧
      ∃ D D' : Set T,IsClosedDisc D ∧ IsClosedDisc D' ∧ Disjoint D D' ∧
        Nonempty (↥((D ∪ D')ᶜ) ≃ₜ ↥(Cᶜ)) := by
  classical
  let : T2Space S := hS.2.1
  by_cases hc : IsConnected Cᶜ
  · obtain ⟨T,τ,hT,⟨a,-,⟨eT⟩⟩,hlt,hrest⟩ := exists_lower_handle_cut_connected hS eS hC hc
    let : ConnectedSpace T := eT.connectedSpace_iff.mpr (modelCriterion.1 a 0 0).2
    exact .inr ⟨T,τ,hT,component_handle_models_of_connected eT,hlt,hrest⟩
  obtain ⟨Y,τY,ψ,hY,hψ,X,X',hd,hunion,hX,hX',hb,hb'⟩ :=
    exists_two_sided_handle_cut hS eS hC
  let : CompactSpace Y := hY.1
  let : T2Space Y := hY.2.1
  have hneX : X.Nonempty := by obtain ⟨e⟩ := hX; exact ⟨_,(e 1).2⟩
  have hneX' : X'.Nonempty := by obtain ⟨e⟩ := hX'; exact ⟨_,(e 1).2⟩
  obtain ⟨x,hx⟩ := hneX
  obtain ⟨y,hy⟩ := hneX'
  rcases cut_comps hψ hY hX.isPreconnected hX'.isPreconnected hunion hx hy with hconn|htwo
  · let : ConnectedSpace Y := hconn
    obtain ⟨e⟩ := cutting_complement_homeomorph hψ
    have he : (bd Y)ᶜ=ψ ⁻¹' Cᶜ := by
      rw [cutting_boundary_eq hψ hC.isCompact.isClosed hS,preimage_compl]
    let f : ↥((bd Y)ᶜ) ≃ₜ ↥(Cᶜ) := (Homeomorph.setCongr he).trans e
    let : ConnectedSpace ↥((bd Y)ᶜ) := isConnected_iff_connectedSpace.mp (isConnected_interior hY)
    have hconnC : ConnectedSpace ↥(Cᶜ) := f.connectedSpace_iff.mp inferInstance
    exact (hc (isConnected_iff_connectedSpace.mpr hconnC)).elim
  · obtain ⟨W₁,W₂,-,-,hsX,hsX',hW₁,hW₂,huW,hdW,hconn₁,hconn₂⟩ := htwo
    let : ConnectedSpace W₁ := hconn₁
    let : ConnectedSpace W₂ := hconn₂
    exact exists_lower_handle_cut_separating hS hY hψ hC eS hunion hb hb' hX hX'
      hW₁ hW₂ hdW huW hsX hsX'

end GraphMinor.GM05
