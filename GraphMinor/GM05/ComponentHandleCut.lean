module

public import GraphMinor.GM05.SurfaceDescent
import GraphMinor.GM05.HandleCut
import GraphMinor.GM05.ComponentHandleModels
import GraphMinor.GM05.SurfaceComponents
import GraphMinor.GM05.SurfaceSumDecrease
import GraphMinor.GM05.GenusHomeomorph
import GraphMinor.GM05.ClopenComplement
import GraphMinor.GM05.OpenSumComplement
import GraphMinor.GM19.CapModel
import GraphMinor.Surface.DiscMerge
import GraphMinor.Surface.CutComp

/-!
# Circle cuts preserving explicit component handle models

For GM V, (8.14), work in the component containing the circle and
apply the handle-model cut of (8.10). Include a bounding disc directly,
or replace the component by its lower handle models and keep the other
components. The same sum maps identify the complements and the genus
list strictly decreases.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM19

/-- The component-model form of the cut in GM V, (8.10), used to
retain the representations in the minimal-surface proof of (8.14). -/
theorem exists_lower_component_handle_cut {S : Type} [TopologicalSpace S] (hS : IsClosedSurface S)
    (hmodels : ∀ x : S,∃ g : ℕ,Nonempty ((connectedComponent x) ≃ₜ SurfaceModel g 0 0))
    {C : Set S} (hC : IsOArc C) :
    (∃ D : Set S,IsClosedDisc D ∧ C=discBd D) ∨
    ∃ (T : Type) (_ : TopologicalSpace T) (hT : IsClosedSurface T),
      (∀ x : T,∃ g : ℕ,Nonempty ((connectedComponent x) ≃ₜ SurfaceModel g 0 0)) ∧
      SurfaceGenusLT hT hS ∧
      ∃ D D' : Set T,IsClosedDisc D ∧ IsClosedDisc D' ∧ Disjoint D D' ∧
        Nonempty (↥((D ∪ D')ᶜ) ≃ₜ ↥(Cᶜ)) := by
  classical
  let : T2Space S := hS.2.1
  have hs : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  let : LocallyConnectedSpace S := hs.locallyConnected
  have hCne : C.Nonempty := by obtain ⟨φ⟩ := hC; exact ⟨_,(φ 1).2⟩
  obtain ⟨x,hx⟩ := hCne
  let U : Set S := connectedComponent x
  have hU : IsClopen U := ⟨isClosed_connectedComponent,isOpen_connectedComponent⟩
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hCU : C ⊆ U := hC.isPreconnected.subset_connectedComponent hx
  have hUclosed := isClosedSurface_clopen hS hU
  obtain ⟨g,⟨eU⟩⟩ := hmodels x
  have hrange : C ⊆ range (Subtype.val : U → S) := fun y hy ↦ ⟨⟨y,hCU hy⟩,rfl⟩
  let eC : (Subtype.val ⁻¹' C : Set U) ≃ₜ C := IsEmbedding.subtypeVal.homeomorphOfSubsetRange hrange
  have hcircle : IsOArc (Subtype.val ⁻¹' C : Set U) := by
    obtain ⟨φ⟩ := hC
    exact ⟨φ.trans eC.symm⟩
  rcases exists_lower_handle_cut hUclosed eU hcircle with hdisc|hcut
  · obtain ⟨D,hD,hbd⟩ := hdisc
    have hd := GM19.isClosedDisc_image hD (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : U → S))
    refine .inl ⟨Subtype.val '' D,hd.1,?_⟩
    rw [hd.2,← hbd]
    exact (image_preimage_eq_of_subset hrange).symm
  · obtain ⟨T,τT,hT,hTmodels,hgenus,D,D',hD,hD',hdis,⟨f⟩⟩ := hcut
    let : T2Space T := hT.2.1
    let R : Type := ↥(Uᶜ)
    have hRclosed : IsClosedSurface R := isClosedSurface_clopen hS hU.compl
    have hRmodels := component_handle_models_clopen hmodels hU.compl
    have hnew := isClosedSurface_sum hT hRclosed
    have hnewModels := component_handle_models_sum hTmodels hRmodels
    obtain ⟨eOld⟩ := clopen_sum_homeomorph hU
    have hnewGenus : SurfaceGenusLT hnew hS := by
      have h := surfaceGenusLT_sum_of_connected hUclosed hT hRclosed hgenus
      change GenusListLT (surfaceGenusList (T ⊕ R) hnew) (surfaceGenusList (U ⊕ R) _) at h
      change GenusListLT (surfaceGenusList (T ⊕ R) hnew) (surfaceGenusList S hS)
      rwa [surfaceGenusList_homeo eOld (isClosedSurface_sum hUclosed hRclosed) hS] at h
    have hd₁ : IsClosedDisc (Sum.inl '' D : Set (T ⊕ R)) := (GM19.isClosedDisc_image hD IsEmbedding.inl).1
    have hd₂ : IsClosedDisc (Sum.inl '' D' : Set (T ⊕ R)) := (GM19.isClosedDisc_image hD' IsEmbedding.inl).1
    have hdis' : Disjoint (Sum.inl '' D : Set (T ⊕ R)) (Sum.inl '' D') :=
      (disjoint_image_iff (fun y z he ↦ Sum.inl.inj he)).mpr hdis
    obtain ⟨eNew⟩ := sum_complement_empty_right (T := R) (hD.isCompact.union hD'.isCompact).isClosed
    rw [image_union] at eNew
    obtain ⟨eOldC⟩ := clopen_complement_homeomorph hU hC.isCompact.isClosed hCU
    refine .inr ⟨T ⊕ R,inferInstance,hnew,hnewModels,hnewGenus,Sum.inl '' D,Sum.inl '' D',hd₁,hd₂,hdis',?_⟩
    exact ⟨eNew.symm.trans ((Homeomorph.sumCongr f (Homeomorph.refl R)).trans eOldC)⟩

end GraphMinor.GM05
