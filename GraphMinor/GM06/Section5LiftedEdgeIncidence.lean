module

public import GraphMinor.GM11.Regions
public import Mathlib.Topology.IsLocalHomeomorph
import GraphMinor.GM11.EdgeSides

/-!
# Propagating edge incidence through local cover charts

The sheet-sensitive contraction argument in VI (5.5), page 130,
needs incidence along a lifted edge. Two-side neighbourhoods of the
base edge lift through a local cover chart. Incidence is therefore
both open and closed along any connected lifted edge, even when
the cover itself is not compact.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
universe u v

private theorem subset_component_of_mem
    {X : Type u} [TopologicalSpace X] {B r A : Set X}
    (hr : r ∈ componentsIn B) (hA : IsPreconnected A) (hAB : A ⊆ B)
    {x : X} (hxA : x ∈ A) (hxr : x ∈ r) : A ⊆ r := by
  obtain ⟨y, _, rfl⟩ := hr
  rw [connectedComponentIn_eq hxr]
  exact hA.subset_connectedComponentIn hxA hAB

/-- The closure of a complementary component in a locally connected
space adds only points of the removed closed set. -/
theorem closure_component_complement_subset
    {X : Type u} [TopologicalSpace X] [LocallyConnectedSpace X]
    {B r : Set X} (hB : IsClosed B) (hr : r ∈ componentsIn Bᶜ) :
    closure r ⊆ r ∪ B := by
  obtain ⟨a, _, rfl⟩ := hr
  intro x hx
  by_cases hxB : x ∈ B
  · exact Or.inr hxB
  · have hxD : x ∈ connectedComponentIn Bᶜ x := mem_connectedComponentIn hxB
    have hDo : IsOpen (connectedComponentIn Bᶜ x) := hB.isOpen_compl.connectedComponentIn
    obtain ⟨z, hzD, hzr⟩ := mem_closure_iff.mp hx _ hDo hxD
    have heq : connectedComponentIn Bᶜ a = connectedComponentIn Bᶜ x :=
      (connectedComponentIn_eq hzr).trans (connectedComponentIn_eq hzD).symm
    exact Or.inl (heq.symm ▸ hxD)

/-- Incidence with a complementary component propagates along a
connected lifted edge under local homeomorphisms. -/
theorem lifted_edge_subset_closure_component
    {X : Type u} {S : Type v} [TopologicalSpace X] [TopologicalSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) (f : X → S)
    {e : Set S} (he : e ∈ Γ.E) {A r : Set X}
    (hA : IsPreconnected A) (hAe : A ⊆ f ⁻¹' e)
    (hlocal : IsLocalHomeomorphOn f A)
    (hr : r ∈ componentsIn (f ⁻¹' Γ.Uᶜ))
    (hinc : (A ∩ closure r).Nonempty) : A ⊆ closure r := by
  let : T2Space S := hS.2.1
  have hroff : ∀ x ∈ r, f x ∉ Γ.U := by
    obtain ⟨y, _, rfl⟩ := hr
    exact fun x hx => connectedComponentIn_subset _ _ hx
  have hstep : ∀ x ∈ A ∩ closure r,
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ A ∩ U ⊆ closure r := by
    rintro x ⟨hxA, hxr⟩
    obtain ⟨η, hxη, hη⟩ := hlocal x hxA
    have hηapp (y) : η y = f y := congrFun hη.symm y
    have hxT : f x ∈ η.target := hηapp x ▸ η.map_source hxη
    obtain ⟨W, B₁, B₂, _, _, hWo, hxW, _, hcover, hB₁, hB₂,
      hd₁, hd₂, hc₁, hc₂, _, _, _, _, _, _, hz₁, hz₂⟩ :=
      GraphMinor.GM11.exists_edge_sides_off hS Γ he (hAe hxA)
        η.open_target.isClosed_compl (not_not.mpr hxT)
    have hBT₁ : B₁ ⊆ η.target := fun y hy => by
      by_contra h
      exact disjoint_left.mp hz₁ hy h
    have hBT₂ : B₂ ⊆ η.target := fun y hy => by
      by_contra h
      exact disjoint_left.mp hz₂ hy h
    have hside : ∀ B : Set S, IsPreconnected B → Disjoint B Γ.U → B ⊆ η.target →
        IsPreconnected (η.symm '' B) ∧ η.symm '' B ⊆ f ⁻¹' Γ.Uᶜ := by
      intro B hB hd hBT
      refine ⟨hB.image η.symm (η.symm.continuousOn.mono hBT), ?_⟩
      rintro y ⟨z, hz, rfl⟩
      change f (η.symm z) ∉ Γ.U
      rw [← hηapp, η.right_inv (hBT hz)]
      exact disjoint_left.mp hd hz
    have hUo : IsOpen (η.source ∩ η ⁻¹' W) := η.isOpen_inter_preimage hWo
    have hxU : x ∈ η.source ∩ η ⁻¹' W := ⟨hxη, by
      change η x ∈ W
      rw [hηapp]
      exact hxW⟩
    obtain ⟨y, hyU, hyr⟩ := mem_closure_iff.mp hxr _ hUo hxU
    have hyW : f y ∈ W := hηapp y ▸ hyU.2
    have hyBs : f y ∈ B₁ ∪ B₂ := hcover ⟨hyW, hroff y hyr⟩
    have hfinish : ∀ B : Set S, IsPreconnected B → Disjoint B Γ.U → B ⊆ η.target →
        f y ∈ B → e ∩ W ⊆ closure B → A ∩ (η.source ∩ η ⁻¹' W) ⊆ closure r := by
      intro B hB hd hBT hyB hc
      obtain ⟨hpre, hsub⟩ := hside B hB hd hBT
      have hyim : y ∈ η.symm '' B :=
        ⟨f y, hyB, by rw [← hηapp, η.left_inv hyU.1]⟩
      have himr := subset_component_of_mem hr hpre hsub hyim hyr
      rintro z ⟨hzA, hzU⟩
      have hzT : f z ∈ η.target := hηapp z ▸ η.map_source hzU.1
      have hzcl : f z ∈ closure B := hc ⟨hAe hzA, hηapp z ▸ hzU.2⟩
      have hzin : η.symm (f z) ∈ closure (η.symm '' B) :=
        mem_closure_image (η.symm.continuousAt hzT) hzcl
      have hzback : η.symm (f z) = z := by rw [← hηapp, η.left_inv hzU.1]
      exact closure_mono himr (hzback ▸ hzin)
    refine ⟨_, hUo, hxU, ?_⟩
    rcases hyBs with hy | hy
    · exact hfinish B₁ hB₁ hd₁ hBT₁ hy hc₁
    · exact hfinish B₂ hB₂ hd₂ hBT₂ hy hc₂
  choose! U hUo hxU hUs using hstep
  let O : Set X := ⋃ x ∈ A ∩ closure r, U x
  have hOo : IsOpen O := isOpen_biUnion fun x hx => hUo x hx
  by_contra hnot
  obtain ⟨z, hzA, hzr⟩ := not_subset.mp hnot
  have hcov : A ⊆ O ∪ (closure r)ᶜ := by
    intro y hy
    by_cases hyr : y ∈ closure r
    · exact Or.inl (mem_iUnion₂.mpr ⟨y, ⟨hy, hyr⟩, hxU y ⟨hy, hyr⟩⟩)
    · exact Or.inr hyr
  obtain ⟨x, hxA, hxr⟩ := hinc
  obtain ⟨y, hyA, hyO, hyr⟩ := hA O (closure r)ᶜ hOo isClosed_closure.isOpen_compl hcov
    ⟨x, hxA, mem_iUnion₂.mpr ⟨x, ⟨hxA, hxr⟩, hxU x ⟨hxA, hxr⟩⟩⟩ ⟨z, hzA, hzr⟩
  obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hyO
  exact hyr (hUs w hw ⟨hyA, hyw⟩)

end GraphMinor.GM06
