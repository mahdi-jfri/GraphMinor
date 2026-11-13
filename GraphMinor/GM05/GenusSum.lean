module

public import GraphMinor.GM05.SurfaceGenus
public import Mathlib.Topology.Constructions.SumProd
import GraphMinor.GM05.GenusClopen
import GraphMinor.Surface.Gluing
import Mathlib.Topology.Clopen
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Fintype.Basic

/-!
# The genus list of two connected surfaces

A separating circle cut in Graph Minors V, (8.10), gives two capped
connected surfaces. Their disjoint union uses the ordinary topological
sum. Its component genera are the two genera, sorted in nonincreasing
order. This also retains a spherical component as a zero entry.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u v

/-- The topological sum of two closed surfaces is a closed surface. -/
theorem isClosedSurface_sum {S : Type u} [TopologicalSpace S]
    {T : Type v} [TopologicalSpace T] (hS : IsClosedSurface S) (hT : IsClosedSurface T) :
    IsClosedSurface (S ⊕ T) := by
  let : CompactSpace S := hS.1
  let : CompactSpace T := hT.1
  let : T2Space S := hS.2.1
  let : T2Space T := hT.2.1
  refine ⟨inferInstance,inferInstance,?_⟩
  intro x
  cases x with
  | inl x => exact isInteriorPoint_of_isOpenEmbedding IsOpenEmbedding.inl (hS.2.2 x)
  | inr x => exact isInteriorPoint_of_isOpenEmbedding IsOpenEmbedding.inr (hT.2.2 x)

/-- The two connected summands contribute their two genera, including
zero genera, to the sorted list of the disjoint union. -/
theorem surfaceGenusList_sum_connected {S : Type u} [TopologicalSpace S] [ConnectedSpace S]
    {T : Type v} [TopologicalSpace T] [ConnectedSpace T]
    (hST : IsClosedSurface (S ⊕ T)) :
    surfaceGenusList (S ⊕ T) hST=
      ({connectedGenus S,connectedGenus T} : Multiset ℕ).sort (· ≥ ·) := by
  classical
  let U : Bool → Set (S ⊕ T) := fun b ↦ if b then range Sum.inl else range Sum.inr
  have hcl : ∀ b,IsClopen (U b) := by
    intro b
    cases b
    · exact isClopen_range_inr
    · exact isClopen_range_inl
  have hd : Pairwise (Function.onFun Disjoint U) := by
    intro a b hab
    cases a <;> cases b
    · exact (hab rfl).elim
    · exact Set.disjoint_left.mpr (by rintro _ ⟨x,rfl⟩ ⟨y,hy⟩; cases hy)
    · exact Set.disjoint_left.mpr (by rintro _ ⟨x,rfl⟩ ⟨y,hy⟩; cases hy)
    · exact (hab rfl).elim
  have hu : ⋃ b,U b=univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    cases x with
    | inl x => exact mem_iUnion.mpr ⟨true,x,rfl⟩
    | inr x => exact mem_iUnion.mpr ⟨false,x,rfl⟩
  have hc : ∀ b,IsConnected (U b) := by
    intro b
    cases b
    · exact isConnected_range continuous_inr
    · exact isConnected_range continuous_inl
  have hleft : connectedGenus (U true)=connectedGenus S :=
    (connectedGenus_homeo (IsEmbedding.inl.toHomeomorph : S ≃ₜ range (Sum.inl : S → S ⊕ T))).symm
  have hright : connectedGenus (U false)=connectedGenus T :=
    (connectedGenus_homeo (IsEmbedding.inr.toHomeomorph : T ≃ₜ range (Sum.inr : T → S ⊕ T))).symm
  rw [surfaceGenusList_of_clopen_decomposition hST U hcl hd hu hc,Fintype.univ_bool]
  simp [Finset.insert_val,Finset.singleton_val,Multiset.ndinsert_of_notMem,hleft,hright]

end GraphMinor.GM05
