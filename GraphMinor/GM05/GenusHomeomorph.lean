module

public import GraphMinor.GM05.SurfaceGenus
import GraphMinor.Surface.CutComp
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Genus lists and homeomorphisms

The genus comparisons in Graph Minors V, (8.10), do not depend on the
chosen representatives of the surfaces. A homeomorphism gives a
bijection of connected components and a homeomorphism on each component.
Thus it preserves the multiset of genera and its nonincreasing sort.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u v

/-- The component bijection induced by a homeomorphism. It sends the
component of `x` to the component of its image. -/
def connectedComponentEquiv {S : Type u} [TopologicalSpace S]
    {T : Type v} [TopologicalSpace T] (e : S ≃ₜ T) :
    ConnectedComponents S ≃ ConnectedComponents T :=
  Quotient.congr e.toEquiv fun x y ↦ by
    change connectedComponent x=connectedComponent y ↔
      connectedComponent (e x)=connectedComponent (e y)
    rw [connectedComponent_eq_iff_mem,connectedComponent_eq_iff_mem]
    constructor
    · intro h
      exact e.continuous.mapsTo_connectedComponent y h
    · intro h
      simpa only [Homeomorph.symm_apply_apply] using
        e.symm.continuous.mapsTo_connectedComponent (e y) h

/-- The induced bijection takes the component of a point to that of
its image. -/
theorem connectedComponentEquiv_mk {S : Type u} [TopologicalSpace S]
    {T : Type v} [TopologicalSpace T] (e : S ≃ₜ T) (x : S) :
    connectedComponentEquiv e (ConnectedComponents.mk x)=ConnectedComponents.mk (e x) := by rfl

/-- The homeomorphism restricts to a homeomorphism of corresponding
component fibers, so their genera agree. -/
theorem connectedGenus_component_homeo {S : Type u} [TopologicalSpace S]
    {T : Type v} [TopologicalSpace T] (e : S ≃ₜ T) (c : ConnectedComponents S) :
    connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set S)=
      connectedGenus (ConnectedComponents.mk ⁻¹' {connectedComponentEquiv e c} : Set T) := by
  have he : e '' (ConnectedComponents.mk ⁻¹' {c})=
      ConnectedComponents.mk ⁻¹' {connectedComponentEquiv e c} := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      change ConnectedComponents.mk (e x)=connectedComponentEquiv e c
      rw [← connectedComponentEquiv_mk]
      exact congrArg (connectedComponentEquiv e) hx
    · intro hz
      refine ⟨e.symm z,?_,e.apply_symm_apply z⟩
      apply (connectedComponentEquiv e).injective
      rw [connectedComponentEquiv_mk,e.apply_symm_apply]
      exact hz
  exact connectedGenus_homeo ((e.isEmbedding.homeomorphImage _).trans (Homeomorph.setCongr he))

/-- Homeomorphic closed surfaces have equal sorted component-genus lists. -/
theorem surfaceGenusList_homeo {S : Type u} [TopologicalSpace S]
    {T : Type v} [TopologicalSpace T] (e : S ≃ₜ T)
    (hS : IsClosedSurface S) (hT : IsClosedSurface T) :
    surfaceGenusList S hS=surfaceGenusList T hT := by
  classical
  let : CompactSpace S := hS.1
  let : CompactSpace T := hT.1
  have hs : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  have ht : IsSurface T := ⟨hT.1,hT.2.1,fun x ↦ (hT.2.2 x).isManifoldPoint⟩
  let : LocallyConnectedSpace S := hs.locallyConnected
  let : LocallyConnectedSpace T := ht.locallyConnected
  let : Fintype (ConnectedComponents S) := Fintype.ofFinite _
  let : Fintype (ConnectedComponents T) := Fintype.ofFinite _
  rw [surfaceGenusList_eq_sort,surfaceGenusList_eq_sort]
  have hu : (Finset.univ : Finset (ConnectedComponents S)).val.map (connectedComponentEquiv e)=
      (Finset.univ : Finset (ConnectedComponents T)).val := by
    change (Finset.univ.map (connectedComponentEquiv e).toEmbedding).val=Finset.univ.val
    rw [Finset.map_univ_equiv]
  have hm : (Finset.univ : Finset (ConnectedComponents S)).val.map
      (fun c ↦ connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set S))=
      (Finset.univ : Finset (ConnectedComponents T)).val.map
      (fun c ↦ connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set T)) := by
    calc
      _ = (Finset.univ : Finset (ConnectedComponents S)).val.map
          (fun c ↦ connectedGenus (ConnectedComponents.mk ⁻¹' {connectedComponentEquiv e c} : Set T)) := by
        apply Multiset.map_congr rfl
        intro c _
        exact connectedGenus_component_homeo e c
      _ = _ := by rw [← hu,Multiset.map_map]; rfl
  exact congrArg (fun M : Multiset ℕ ↦ M.sort (· ≥ ·)) hm

end GraphMinor.GM05
