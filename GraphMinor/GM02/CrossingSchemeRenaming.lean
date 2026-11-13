module

public import GraphMinor.GM02.CrossingScheme
public import GraphMinor.GM02.TerminationGraphMaps
public import GraphMinor.GM02.PairPathUnionMaps
import Mathlib.Logic.Equiv.Set

/-!
# Numbering the vertices of boundary crossing schemes

A bijection renames all terminal pairs, side vertex sets, and reserved
sets together. The support equations and parity condition pull back by
the inverse bijection. Mapping the complete path union proves the last
scheme condition. Thus finite-boundary schemes can be numbered on `Fin n`
without changing their meaning.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set SimpleGraph Classical
universe u u' v

/-- Rename every datum of a boundary scheme by a vertex bijection. The
edgeless graphs retain the side vertex sets used by the printed definition. -/
noncomputable def CrossingScheme.mapEquiv {α : Type u} {α' : Type u'} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A) (e : α ≃ α') :
    CrossingScheme (Graph.noEdge (e '' V(G)) β) (Graph.noEdge (e '' V(H)) β)
      (Graph.noEdge (e '' V(H')) β) (A.mapEmbedding e.toEmbedding) := by
  letI : DecidableEq α' := Classical.decEq α'
  let A' := A.mapEmbedding e.toEmbedding
  let L := C.left.mapEmbedding e.toEmbedding
  let R := C.right.mapEmbedding e.toEmbedding
  have hA : A'.support = e.symm ⁻¹' A.support := by
    exact (A.mapEmbedding_support e.toEmbedding).trans (e.image_eq_preimage_symm _)
  have hL : L.support = e.symm ⁻¹' C.left.support := by
    exact (C.left.mapEmbedding_support e.toEmbedding).trans (e.image_eq_preimage_symm _)
  have hR : R.support = e.symm ⁻¹' C.right.support := by
    exact (C.right.mapEmbedding_support e.toEmbedding).trans (e.image_eq_preimage_symm _)
  refine
    { left := L
      right := R
      reservedLeft := e '' C.reservedLeft
      reservedRight := e '' C.reservedRight
      reservedLeft_subset := ?_
      reservedRight_subset := ?_
      left_support := ?_
      right_support := ?_
      even_support := ?_
      reserved_disjoint := ?_
      reserved_union := ?_
      path_union := ?_ }
  · change e '' C.reservedLeft ⊆ (e '' V(H)) ∩ (e '' V(H'))
    simp only [e.image_eq_preimage_symm]
    exact fun _ ha => C.reservedLeft_subset ha
  · change e '' C.reservedRight ⊆ (e '' V(H)) ∩ (e '' V(H'))
    simp only [e.image_eq_preimage_symm]
    exact fun _ ha => C.reservedRight_subset ha
  · change L.support \ ((e '' V(H)) ∩ (e '' V(H'))) = A'.support ∩ ((e '' V(H)) \ (e '' V(H')))
    rw [hL, hA]
    simp only [e.image_eq_preimage_symm]
    exact congrArg (Set.preimage e.symm) C.left_support
  · change R.support \ ((e '' V(H)) ∩ (e '' V(H'))) = A'.support ∩ ((e '' V(H')) \ (e '' V(H)))
    rw [hR, hA]
    simp only [e.image_eq_preimage_symm]
    exact congrArg (Set.preimage e.symm) C.right_support
  · intro a ha
    change a ∈ (e '' V(H)) ∩ (e '' V(H')) at ha
    have ha' : e.symm a ∈ V(H) ∩ V(H') := by
      simpa only [e.image_eq_preimage_symm, Set.mem_inter_iff, Set.mem_preimage] using ha
    change Even ((if a ∈ A'.support then 1 else 0) +
      (if a ∈ L.support then 1 else 0) + (if a ∈ R.support then 1 else 0) : ℕ)
    rw [hA, hL, hR]
    exact C.even_support (e.symm a) ha'
  · simp only [e.image_eq_preimage_symm]
    apply Set.disjoint_left.2
    intro a ha hb
    exact Set.disjoint_left.1 C.reserved_disjoint ha hb
  · change (e '' C.reservedLeft) ∪ (e '' C.reservedRight) =
      ((e '' V(H)) ∩ (e '' V(H'))) \ (A'.support ∪ L.support ∪ R.support)
    rw [hA, hL, hR]
    simp only [e.image_eq_preimage_symm]
    exact congrArg (Set.preimage e.symm) C.reserved_union
  · have hp := C.path_union.mapEmbedding e.toEmbedding
    have hF : SimpleGraph.fromEdgeSet (L.pairs ∪ R.pairs : Finset (Sym2 α')) =
        (SimpleGraph.fromEdgeSet (C.left.pairs ∪ C.right.pairs : Finset (Sym2 α))).map e := by
      simp only [Finset.coe_union, SimpleGraph.fromEdgeSet_union]
      change L.pairGraph ⊔ R.pairGraph = (C.left.pairGraph ⊔ C.right.pairGraph).map e
      rw [Termination.mapEquiv_pairGraph, Termination.mapEquiv_pairGraph]
      calc
        _ = (C.left.pairGraph ⊔ C.right.pairGraph).comap e.symm := by ext a b; rfl
        _ = _ := SimpleGraph.comap_symm _ e
    have htarget : IsPairPathUnion A'
        (SimpleGraph.fromEdgeSet (L.pairs ∪ R.pairs : Finset (Sym2 α'))) (L.support ∪ R.support) := by
      rw [hF, Termination.mapEmbedding_support, Termination.mapEmbedding_support, ← Set.image_union]
      exact hp
    exact htarget

end GraphMinor.GM02
