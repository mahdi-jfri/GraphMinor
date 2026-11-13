module

public import GraphMinor.GM05.SurfaceDescent
import GraphMinor.GM05.CutComplement
import GraphMinor.GM05.CutOrientation
import GraphMinor.GM05.CuffComponent
import GraphMinor.GM05.CappingPair
import GraphMinor.GM05.SeparatingModels
import GraphMinor.GM05.DiscCutComponent
import GraphMinor.GM05.GenusSum
import GraphMinor.GM05.GenusReplacement
import GraphMinor.GM05.SumOrientation
import GraphMinor.GM05.OpenSumComplement
import GraphMinor.GM19.CapOrient
import GraphMinor.GM19.CapModel
import GraphMinor.GM19.Section4c
import GraphMinor.GM19.Perimeter
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.ModelCriterion

/-!
# The separating-cut case

For Graph Minors V, (8.10), cut a circle in a connected handle surface
into two components. A genus-zero component gives a closed disc bounded
by the circle. Otherwise both genera are positive and smaller than the
original genus. Cap the single cuff of each component and take their
topological sum. Orientations extend across the caps, and the inclusion
maps identify the complement with the original circle complement.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM19

/-- The separating-cut case of Graph Minors V, (8.10), page 112,
for a surface represented by its handle model. The hypotheses describe
the two components and boundary lifts of the library cut. -/
theorem lemma_8_10_separating_cut {Y S : Type} [TopologicalSpace Y]
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    (hO : IsOrientableSurface S) (hY : IsSurface Y)
    {ψ : Y → S} {C : Set S} (hψ : IsCutting ψ C) (hC : IsOArc C)
    {g : ℕ} (eS : S ≃ₜ SurfaceModel g 0 0)
    {X X' W₁ W₂ : Set Y} (hun : X ∪ X'=ψ ⁻¹' C)
    (hb : BijOn ψ X C) (hb' : BijOn ψ X' C) (hX : IsOArc X) (hX' : IsOArc X')
    (hW₁ : IsClopen W₁) (hW₂ : IsClopen W₂) (hdW : Disjoint W₁ W₂)
    (huW : W₁ ∪ W₂=univ) (hsX : X ⊆ W₁) (hsX' : X' ⊆ W₂)
    [ConnectedSpace W₁] [ConnectedSpace W₂] :
    (∃ D : Set S,IsClosedDisc D ∧ C=discBd D) ∨
    ∃ (T : Type) (_ : TopologicalSpace T) (hT : IsClosedSurface T),
      IsOrientableSurface T ∧ SurfaceGenusLT hT hS ∧
      ∃ D D' : Set T,IsClosedDisc D ∧ IsClosedDisc D' ∧ Disjoint D D' ∧
        Nonempty (↥((D ∪ D')ᶜ) ≃ₜ ↥(Cᶜ)) := by
  let : T2Space S := hS.2.1
  let : CompactSpace Y := hY.1
  let : T2Space Y := hY.2.1
  have hbd : bd Y=X ∪ X' := (cutting_boundary_eq hψ hC.isCompact.isClosed hS).trans hun.symm
  have hd₁ : Disjoint W₁ X' := hdW.mono_right hsX'
  have hd₂ : Disjoint W₂ X := hdW.symm.mono_right hsX
  obtain ⟨a₁,a₂,ha,⟨e₁⟩,⟨e₂⟩⟩ :=
    separating_cut_models hY hψ eS hun hb hb' hX hX' hW₁ hW₂ hdW huW hsX hsX'
  by_cases hzero₁ : a₁=0
  · subst a₁
    exact .inl (bounds_disc_of_cut_disc_component hY hψ hun hb hbd hW₁ hsX hd₁ e₁)
  by_cases hzero₂ : a₂=0
  · subst a₂
    exact .inl (bounds_disc_of_cut_disc_component hY hψ (union_comm X' X ▸ hun) hb'
      (hbd.trans (union_comm X X')) hW₂ hsX' hd₂ e₂)
  right
  obtain ⟨cap₁₀⟩ := nonempty_capped_model a₁ 0 1
  obtain ⟨cap₂₀⟩ := nonempty_capped_model a₂ 0 1
  let cap₁ : IsCappedSurface W₁ (SurfaceModel a₁ 0 0) := cap₁₀.ofHomeo e₁
  let cap₂ : IsCappedSurface W₂ (SurfaceModel a₂ 0 0) := cap₂₀.ofHomeo e₂
  let : T2Space (SurfaceModel a₁ 0 0) := cap₁.isSurface.2.1
  let : T2Space (SurfaceModel a₂ 0 0) := cap₂.isSurface.2.1
  let : ConnectedSpace (SurfaceModel a₁ 0 0) := cap₁.connected
  let : ConnectedSpace (SurfaceModel a₂ 0 0) := cap₂.connected
  have hY₁ := isSurface_sub hY hW₁
  have hY₂ := isSurface_sub hY hW₂
  obtain ⟨ω₁⟩ := orientable_cut_component hY hψ hO hW₁
  obtain ⟨ω₂⟩ := orientable_cut_component hY hψ hO hW₂
  obtain ⟨o₁,-⟩ := exists_cap_orientation hY₁ cap₁ ω₁
  obtain ⟨o₂,-⟩ := exists_cap_orientation hY₂ cap₂ ω₂
  have hT := isClosedSurface_sum cap₁.isClosedSurface cap₂.isClosedSurface
  have hgenus : SurfaceGenusLT hT hS := by
    change GenusListLT (surfaceGenusList _ hT) (surfaceGenusList S hS)
    rw [surfaceGenusList_sum_connected,surfaceGenusList_of_connected,connectedGenus_eq_of_model eS,
      connectedGenus_model,connectedGenus_model]
    have hn : ∃ n,n ∈ ({a₁,a₂} : Multiset ℕ) := ⟨a₁,by simp⟩
    have hsmall : ∀ n ∈ ({a₁,a₂} : Multiset ℕ),n<g := by
      intro n hn
      have hm : n=a₁ ∨ n=a₂ := by simpa using hn
      rcases hm with rfl|rfl <;> omega
    simpa only [zero_add,Multiset.sort_singleton] using genusListLT_replace 0 {a₁,a₂} g hn hsmall
  have hcuff₁ := (cut_component_single_cuff hY hX hbd hW₁ hsX hd₁).2.2
  have hcuff₂ := (cut_component_single_cuff hY hX' (hbd.trans (union_comm X X')) hW₂ hsX' hd₂).2.2
  obtain ⟨D₁,hD₁,⟨f₁⟩⟩ := capped_single_complement hY₁ cap₁ hcuff₁
  obtain ⟨D₂,hD₂,⟨f₂⟩⟩ := capped_single_complement hY₂ cap₂ hcuff₂
  have hD₁' : IsClosedDisc (Sum.inl '' D₁ : Set (SurfaceModel a₁ 0 0 ⊕ SurfaceModel a₂ 0 0)) :=
    (GM19.isClosedDisc_image hD₁ IsEmbedding.inl).1
  have hD₂' : IsClosedDisc (Sum.inr '' D₂ : Set (SurfaceModel a₁ 0 0 ⊕ SurfaceModel a₂ 0 0)) :=
    (GM19.isClosedDisc_image hD₂ IsEmbedding.inr).1
  have hdis : Disjoint (Sum.inl '' D₁) (Sum.inr '' D₂) :=
    Set.disjoint_left.mpr (by rintro _ ⟨x,_,rfl⟩ ⟨y,_,hy⟩; cases hy)
  obtain ⟨f⟩ := sum_complement_homeomorph hD₁.isCompact.isClosed hD₂.isCompact.isClosed
  obtain ⟨eI⟩ := component_interiors_homeomorph hY hW₁ hW₂ hdW huW
  obtain ⟨eC⟩ := cutting_complement_homeomorph hψ
  have he : (bd Y)ᶜ=ψ ⁻¹' Cᶜ := by
    rw [cutting_boundary_eq hψ hC.isCompact.isClosed hS,preimage_compl]
  refine ⟨_,_,hT,orientable_sum ⟨o₁⟩ ⟨o₂⟩,hgenus,Sum.inl '' D₁,Sum.inr '' D₂,hD₁',hD₂',hdis,?_⟩
  exact ⟨f.symm.trans ((Homeomorph.sumCongr f₁ f₂).symm.trans
    (eI.trans ((Homeomorph.setCongr he).trans eC)))⟩

end GraphMinor.GM05
