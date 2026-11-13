module

public import GraphMinor.GM05.SurfaceGenus
public import Mathlib.Topology.Constructions.SumProd
import GraphMinor.GM05.SurfaceComponents
import GraphMinor.GM05.GenusClopen
import Mathlib.Topology.Clopen
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Multiset.Sum

/-!
# Genus lists of arbitrary disjoint unions

For the disconnected-surface extension of GM V, (8.10), the unchanged
components may themselves be disconnected. The components of a
topological sum are the images of the components of its two summands.
They form a finite disjoint clopen connected cover. Computing genera
from this cover gives the sorted multiset sum of the two genus lists.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u v

/-- A disjoint union contributes all the component genera of both
summands, with multiplicities, and then sorts them. -/
theorem surfaceGenusList_sum {S : Type u} [TopologicalSpace S]
    {T : Type v} [TopologicalSpace T] (hS : IsClosedSurface S) (hT : IsClosedSurface T)
    (hST : IsClosedSurface (S ⊕ T)) :
    surfaceGenusList (S ⊕ T) hST=
      ((surfaceGenusList S hS : Multiset ℕ)+(surfaceGenusList T hT : Multiset ℕ)).sort (· ≥ ·) := by
  classical
  let : Finite (ConnectedComponents S) := finite_surface_components hS
  let : Finite (ConnectedComponents T) := finite_surface_components hT
  let : Fintype (ConnectedComponents S) := Fintype.ofFinite _
  let : Fintype (ConnectedComponents T) := Fintype.ofFinite _
  let W : ConnectedComponents S ⊕ ConnectedComponents T → Set (S ⊕ T) := Sum.elim
    (fun c ↦ Sum.inl '' (ConnectedComponents.mk ⁻¹' {c} : Set S))
    (fun c ↦ Sum.inr '' (ConnectedComponents.mk ⁻¹' {c} : Set T))
  have hcl : ∀ i,IsClopen (W i) := by
    rintro (c|c)
    · exact ⟨IsClosedEmbedding.inl.isClosedMap _ (surface_component_isClopen hS c).1,
        isOpenMap_inl _ (surface_component_isClopen hS c).2⟩
    · exact ⟨IsClosedEmbedding.inr.isClosedMap _ (surface_component_isClopen hT c).1,
        isOpenMap_inr _ (surface_component_isClopen hT c).2⟩
  have hd : Pairwise (Function.onFun Disjoint W) := by
    rintro (c|c) (d|d) hcd
    · exact (disjoint_image_iff (fun x y h ↦ Sum.inl.inj h)).mpr
        (surface_components_disjoint S (fun h ↦ hcd (congrArg Sum.inl h)))
    · exact Set.disjoint_left.mpr (by rintro _ ⟨x,_,rfl⟩ ⟨y,_,he⟩; cases he)
    · exact Set.disjoint_left.mpr (by rintro _ ⟨x,_,rfl⟩ ⟨y,_,he⟩; cases he)
    · exact (disjoint_image_iff (fun x y h ↦ Sum.inr.inj h)).mpr
        (surface_components_disjoint T (fun h ↦ hcd (congrArg Sum.inr h)))
  have hu : ⋃ i,W i=univ := by
    apply Set.eq_univ_iff_forall.mpr
    rintro (x|y)
    · exact mem_iUnion.mpr ⟨Sum.inl (ConnectedComponents.mk x),x,rfl,rfl⟩
    · exact mem_iUnion.mpr ⟨Sum.inr (ConnectedComponents.mk y),y,rfl,rfl⟩
  have hc : ∀ i,IsConnected (W i) := by
    rintro (c|c)
    · exact (surface_component_isConnected c).image Sum.inl continuous_inl.continuousOn
    · exact (surface_component_isConnected c).image Sum.inr continuous_inr.continuousOn
  have hgS (c : ConnectedComponents S) :
      connectedGenus (W (.inl c))=connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set S) :=
    (connectedGenus_homeo (IsEmbedding.inl.homeomorphImage (ConnectedComponents.mk ⁻¹' {c} : Set S))).symm
  have hgT (c : ConnectedComponents T) :
      connectedGenus (W (.inr c))=connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set T) :=
    (connectedGenus_homeo (IsEmbedding.inr.homeomorphImage (ConnectedComponents.mk ⁻¹' {c} : Set T))).symm
  have heq : (Finset.univ : Finset (ConnectedComponents S ⊕ ConnectedComponents T)).val.map
      (fun i ↦ connectedGenus (W i))=
      (Finset.univ : Finset (ConnectedComponents S)).val.map
        (fun c ↦ connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set S))+
      (Finset.univ : Finset (ConnectedComponents T)).val.map
        (fun c ↦ connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set T)) := by
    rw [← Finset.univ_disjSum_univ,Finset.val_disjSum,Multiset.map_disjSum]
    apply congrArg₂ (·+·)
    · exact Multiset.map_congr rfl (fun c _ ↦ hgS c)
    · exact Multiset.map_congr rfl (fun c _ ↦ hgT c)
  rw [surfaceGenusList_of_clopen_decomposition hST W hcl hd hu hc,
    surfaceGenusList_eq_sort S hS,surfaceGenusList_eq_sort T hT,Multiset.sort_eq,Multiset.sort_eq]
  exact congrArg (fun M : Multiset ℕ ↦ M.sort (· ≥ ·)) heq

end GraphMinor.GM05
