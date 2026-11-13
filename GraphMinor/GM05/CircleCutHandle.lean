module

public import GraphMinor.GM05.SurfaceDescent
import GraphMinor.GM05.CircleCutConnected
import GraphMinor.GM05.CircleCutSeparating
import GraphMinor.GM05.TwoSidedCut
import GraphMinor.GM05.CutComplement
import GraphMinor.GM05.OrientableHandleModel
import GraphMinor.GM19.CutFragment
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.DiscMerge

/-!
# Cutting a circle in a connected handle surface

This combines the connected-complement and separating-cut cases of
Graph Minors V, (8.10). The library cut has one or two connected
components. A connected cut has connected interior, so its circle
complement is connected. Otherwise use the two-component calculation.
The surface is given by its homeomorphism to a handle model.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM19

/-- Graph Minors V, (8.10), page 112, for a connected orientable
surface with a specified homeomorphism to its handle model.
The two complementary open surfaces are related by the restrictions
of the cutting and capping maps. -/
theorem lemma_8_10_handle_surface {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsClosedSurface S) (hO : IsOrientableSurface S)
    {g : ℕ} (eS : S ≃ₜ SurfaceModel g 0 0) {C : Set S} (hC : IsOArc C) :
    (∃ D : Set S,IsClosedDisc D ∧ C=discBd D) ∨
    ∃ (T : Type) (_ : TopologicalSpace T) (hT : IsClosedSurface T),
      IsOrientableSurface T ∧ SurfaceGenusLT hT hS ∧
      ∃ D D' : Set T,IsClosedDisc D ∧ IsClosedDisc D' ∧ Disjoint D D' ∧
        Nonempty (↥((D ∪ D')ᶜ) ≃ₜ ↥(Cᶜ)) := by
  classical
  let : T2Space S := hS.2.1
  by_cases hc : IsConnected Cᶜ
  · exact .inr (lemma_8_10_connected_complement hS hO eS hC hc)
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
    exact lemma_8_10_separating_cut hS hO hY hψ hC eS hunion hb hb' hX hX'
      hW₁ hW₂ hdW huW hsX hsX'

/-- The connected-surface case of Graph Minors V, (8.10), page 112.
Orientability and classification now supply the handle model, so the
only extra condition relative to the printed statement is connectedness. -/
theorem lemma_8_10_connected_surface {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsClosedSurface S) (hO : IsOrientableSurface S)
    {C : Set S} (hC : IsOArc C) :
    (∃ D : Set S,IsClosedDisc D ∧ C=discBd D) ∨
    ∃ (T : Type) (_ : TopologicalSpace T) (hT : IsClosedSurface T),
      IsOrientableSurface T ∧ SurfaceGenusLT hT hS ∧
      ∃ D D' : Set T,IsClosedDisc D ∧ IsClosedDisc D' ∧ Disjoint D D' ∧
        Nonempty (↥((D ∪ D')ᶜ) ≃ₜ ↥(Cᶜ)) := by
  obtain ⟨g,⟨eS⟩⟩ := orientable_closedSurface_handle_model hS hO
  exact lemma_8_10_handle_surface hS hO eS hC

end GraphMinor.GM05
