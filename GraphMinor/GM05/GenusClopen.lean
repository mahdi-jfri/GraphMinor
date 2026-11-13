module

public import GraphMinor.GM05.SurfaceGenus
public import Mathlib.Data.Multiset.Sort
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Computing genus lists from the components

For Graph Minors V, (8.10), separating cuts give two components and
leave the other surface components unchanged. A finite disjoint clopen
cover by connected sets is exactly the connected-component partition.
Thus its genera, sorted in nonincreasing order, compute the genus list.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u v

/-- A finite disjoint clopen decomposition into connected sets computes
the list of genera of the surface components. -/
theorem surfaceGenusList_of_clopen_decomposition {S : Type u} [TopologicalSpace S]
    (hS : IsClosedSurface S) {ι : Type v} [Fintype ι] (U : ι → Set S)
    (hcl : ∀ i, IsClopen (U i)) (hd : Pairwise (Function.onFun Disjoint U))
    (hu : ⋃ i,U i=univ) (hc : ∀ i, IsConnected (U i)) :
    surfaceGenusList S hS=(Finset.univ.val.map (fun i ↦ connectedGenus (U i))).sort (· ≥ ·) := by
  classical
  let e : ConnectedComponents S ≃ ι :=
    ConnectedComponents.equivOfIsClopenOfIsConnected hcl hd hu hc
  let : Fintype (ConnectedComponents S) := Fintype.ofEquiv ι e.symm
  have hf (c : ConnectedComponents S) : (ConnectedComponents.mk ⁻¹' {c} : Set S)=U (e c) := by
    ext x
    constructor
    · intro hx
      change ConnectedComponents.mk x=c at hx
      obtain ⟨i,hi⟩ := Set.iUnion_eq_univ_iff.mp hu x
      have he : e (ConnectedComponents.mk x)=i :=
        ConnectedComponents.equivOfIsClopenOfIsConnected_mk hcl hd hu hc x hi
      rw [← hx,he]
      exact hi
    · intro hx
      change ConnectedComponents.mk x=c
      apply e.injective
      exact ConnectedComponents.equivOfIsClopenOfIsConnected_mk hcl hd hu hc x hx
  have hg (c : ConnectedComponents S) :
      connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set S)=connectedGenus (U (e c)) :=
    connectedGenus_homeo (Homeomorph.setCongr (hf c))
  have hm : (Finset.univ : Finset (ConnectedComponents S)).val.map e=
      (Finset.univ : Finset ι).val := by
    change (Finset.univ.map e.toEmbedding).val=Finset.univ.val
    rw [Finset.map_univ_equiv]
  rw [surfaceGenusList_eq_sort]
  have heq : (Finset.univ : Finset (ConnectedComponents S)).val.map
      (fun c ↦ connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set S))=
      (Finset.univ : Finset ι).val.map (fun i ↦ connectedGenus (U i)) := by
    calc
      _ = (Finset.univ : Finset (ConnectedComponents S)).val.map
          (fun c ↦ connectedGenus (U (e c))) := Multiset.map_congr rfl (fun c _ ↦ hg c)
      _ = _ := by rw [← hm,Multiset.map_map]; rfl
  exact congrArg (fun M : Multiset ℕ ↦ M.sort (· ≥ ·)) heq

end GraphMinor.GM05
