module

public import GraphMinor.GM02.CrossingSchemeFinite
public import GraphMinor.GM02.TerminationSupportMaps
public import GraphMinor.GM02.PairPathUnionInduce

/-!
# Restricting a crossing scheme to its boundary

Only the original terminal support and separator are needed to describe
a crossing scheme. Regard all endpoint pairs as terminations of a set
containing this boundary, then restrict them and the side memberships to
the vertex subtype. The four printed crossing-scheme conditions pull
back to the subtype. The full path-union condition follows by restricting
its paths, including their vertex and edge coverage.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set SimpleGraph Classical
universe u v

/-- Compress a crossing scheme to any set containing its original support
and separator. The new edgeless graphs record only side vertex sets,
which are the only graph data used in the crossing-scheme definition. -/
noncomputable def CrossingScheme.induceBoundary {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    {S : Set α} (hAS : A.support ⊆ S) (hXS : V(H) ∩ V(H') ⊆ S) :
    CrossingScheme (Graph.noEdge (Set.univ : Set S) β)
      (Graph.noEdge (Subtype.val ⁻¹' V(H)) β) (Graph.noEdge (Subtype.val ⁻¹' V(H')) β)
      (A.rebase hAS).onVertices := by
  letI : DecidableEq S := Classical.decEq S
  have hLS : C.left.support ⊆ S := C.supports_subset.1.trans (Set.union_subset hAS hXS)
  have hRS : C.right.support ⊆ S := C.supports_subset.2.trans (Set.union_subset hAS hXS)
  let A' := (A.rebase hAS).onVertices
  let L := (C.left.rebase hLS).onVertices
  let R := (C.right.rebase hRS).onVertices
  have hA : A'.support = Subtype.val ⁻¹' A.support := by
    rw [Termination.onVertices_support, Termination.rebase_support]
  have hL : L.support = Subtype.val ⁻¹' C.left.support := by
    rw [Termination.onVertices_support, Termination.rebase_support]
  have hR : R.support = Subtype.val ⁻¹' C.right.support := by
    rw [Termination.onVertices_support, Termination.rebase_support]
  refine
    { left := L
      right := R
      reservedLeft := Subtype.val ⁻¹' C.reservedLeft
      reservedRight := Subtype.val ⁻¹' C.reservedRight
      reservedLeft_subset := fun _ ha => C.reservedLeft_subset ha
      reservedRight_subset := fun _ ha => C.reservedRight_subset ha
      left_support := ?_
      right_support := ?_
      even_support := ?_
      reserved_disjoint := ?_
      reserved_union := ?_
      path_union := ?_ }
  · change L.support \ ((Subtype.val ⁻¹' V(H)) ∩ (Subtype.val ⁻¹' V(H'))) =
      A'.support ∩ ((Subtype.val ⁻¹' V(H)) \ (Subtype.val ⁻¹' V(H')))
    rw [hL, hA]
    exact congrArg (Set.preimage (Subtype.val : S → α)) C.left_support
  · change R.support \ ((Subtype.val ⁻¹' V(H)) ∩ (Subtype.val ⁻¹' V(H'))) =
      A'.support ∩ ((Subtype.val ⁻¹' V(H')) \ (Subtype.val ⁻¹' V(H)))
    rw [hR, hA]
    exact congrArg (Set.preimage (Subtype.val : S → α)) C.right_support
  · intro a ha
    change Even ((if a ∈ A'.support then 1 else 0) +
      (if a ∈ L.support then 1 else 0) + (if a ∈ R.support then 1 else 0) : ℕ)
    rw [hA, hL, hR]
    exact C.even_support a.val ha
  · apply Set.disjoint_left.2
    intro a ha hb
    exact Set.disjoint_left.1 C.reserved_disjoint ha hb
  · change (Subtype.val ⁻¹' C.reservedLeft) ∪ (Subtype.val ⁻¹' C.reservedRight) =
      ((Subtype.val ⁻¹' V(H)) ∩ (Subtype.val ⁻¹' V(H'))) \ (A'.support ∪ L.support ∪ R.support)
    rw [hA, hL, hR]
    exact congrArg (Set.preimage (Subtype.val : S → α)) C.reserved_union
  · have hpath : IsPairPathUnion (A.rebase hAS)
        (SimpleGraph.fromEdgeSet (C.left.pairs ∪ C.right.pairs : Finset (Sym2 α)))
        (C.left.support ∪ C.right.support) := C.path_union
    have hp := hpath.induce (Set.union_subset hLS hRS)
    have hF : SimpleGraph.fromEdgeSet (L.pairs ∪ R.pairs : Finset (Sym2 S)) =
        (SimpleGraph.fromEdgeSet (C.left.pairs ∪ C.right.pairs : Finset (Sym2 α))).induce S := by
      simp only [Finset.coe_union, SimpleGraph.fromEdgeSet_union]
      change L.pairGraph ⊔ R.pairGraph = (C.left.pairGraph ⊔ C.right.pairGraph).induce S
      rw [Termination.onVertices_pairGraph, Termination.onVertices_pairGraph,
        Termination.rebase_pairGraph, Termination.rebase_pairGraph]
      ext a b
      rfl
    have htarget : IsPairPathUnion A'
        (SimpleGraph.fromEdgeSet (L.pairs ∪ R.pairs : Finset (Sym2 S))) (L.support ∪ R.support) := by
      rw [hF, hL, hR]
      exact hp
    exact htarget

end GraphMinor.GM02
