module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.CutComp
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Complements in the circle-cutting argument

In Graph Minors V, (8.10), the surface obtained after cutting and capping
has the same complement of its caps as the original surface has of the
circle. The cutting surjection restricts to a homeomorphism off the
circle. A capping embedding restricts to a homeomorphism off the caps.
These lemmas give the maps that identify those complements.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u v

/-- Off the cut set, the cutting surjection is a homeomorphism. The map
is the restriction of the associated surjection of the library cut. -/
theorem cutting_complement_homeomorph {Y : Type u} [TopologicalSpace Y]
    {S : Type u} [TopologicalSpace S] [CompactSpace Y] [T2Space S]
    {ψ : Y → S} {C : Set S} (hψ : IsCutting ψ C) :
    Nonempty (↥(ψ ⁻¹' Cᶜ) ≃ₜ ↥(Cᶜ)) := by
  have hbij : Function.Bijective (Cᶜ.restrictPreimage ψ) := by
    constructor
    · intro a b he
      exact Subtype.ext (hψ.2.2.1 a.2 b.2 (congrArg Subtype.val he))
    · rintro ⟨x,hx⟩
      obtain ⟨y,hy⟩ := hψ.2.1 x
      have hyC : y ∈ ψ ⁻¹' Cᶜ := by
        change ψ y ∉ C
        rw [hy]
        exact hx
      exact ⟨⟨y,hyC⟩,Subtype.ext hy⟩
  have hhomeo : IsHomeomorph (Cᶜ.restrictPreimage ψ) :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨hψ.1.restrictPreimage,hψ.1.isClosedMap.restrictPreimage _,hbij⟩
  exact ⟨hhomeo.homeomorph⟩

/-- Cutting a surface without boundary introduces precisely the preimage
of the cut set as its boundary. -/
theorem cutting_boundary_eq {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]
    [T2Space Y] [CompactSpace Y] [T2Space S] {ψ : Y → S} {C : Set S}
    (hψ : IsCutting ψ C) (hC : IsClosed C) (hS : IsClosedSurface S) :
    bd Y=ψ ⁻¹' C := by
  apply Subset.antisymm
  · intro y hy
    by_contra hn
    exact (bd_of_bd hψ hC hy hn) (hS.2.2 (ψ y))
  · exact hψ.2.2.2.2

/-- An embedding used to cap a surface identifies its interior with the
complement of the caps. The map is the restriction of the embedding. -/
theorem capping_complement_homeomorph {Y : Type u} [TopologicalSpace Y]
    {S : Type v} [TopologicalSpace S] {j : Y → S} {K : Set S}
    (hj : IsEmbedding j) (hcover : range j ∪ K=univ)
    (hmeet : range j ∩ K=j '' bd Y) :
    Nonempty (↥((bd Y)ᶜ) ≃ₜ ↥(Kᶜ)) := by
  have hpre : j ⁻¹' K=bd Y := by
    ext y
    constructor
    · intro hy
      have hm : j y ∈ range j ∩ K := ⟨mem_range_self y,hy⟩
      rw [hmeet] at hm
      obtain ⟨z,hz,he⟩ := hm
      exact hj.injective he ▸ hz
    · intro hy
      have hm : j y ∈ j '' bd Y := mem_image_of_mem j hy
      rw [← hmeet] at hm
      exact hm.2
  have hsub : Kᶜ ⊆ range j := by
    intro x hx
    rcases (hcover ▸ mem_univ x : x ∈ range j ∪ K) with hr|hk
    · exact hr
    · exact (hx hk).elim
  have he : (bd Y)ᶜ=j ⁻¹' Kᶜ := by rw [preimage_compl,hpre]
  exact ⟨(Homeomorph.setCongr he).trans (hj.homeomorphOfSubsetRange hsub)⟩

/-- Cutting and capping preserve the complementary open surface. This is
 the complement identification used in Graph Minors V, (8.10). -/
theorem cut_cap_complement_homeomorph {Y S T : Type u}
    [TopologicalSpace Y] [TopologicalSpace S] [TopologicalSpace T]
    [T2Space Y] [CompactSpace Y] [T2Space S]
    {ψ : Y → S} {C : Set S} (hψ : IsCutting ψ C) (hC : IsClosed C)
    (hS : IsClosedSurface S) {j : Y → T} {K : Set T}
    (hj : IsEmbedding j) (hcover : range j ∪ K=univ)
    (hmeet : range j ∩ K=j '' bd Y) : Nonempty (↥(Kᶜ) ≃ₜ ↥(Cᶜ)) := by
  obtain ⟨e⟩ := cutting_complement_homeomorph hψ
  obtain ⟨f⟩ := capping_complement_homeomorph hj hcover hmeet
  have he : (bd Y)ᶜ=ψ ⁻¹' Cᶜ := by
    rw [cutting_boundary_eq hψ hC hS,preimage_compl]
  exact ⟨f.symm.trans ((Homeomorph.setCongr he).trans e)⟩

end GraphMinor.GM05
