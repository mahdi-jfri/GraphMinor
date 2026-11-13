module

public import GraphMinor.GM02.SideReservations
public import GraphMinor.GM02.InducedTerminatedGraphs

/-!
# Extracting a crossing scheme from a feasible linkage

Split each original path into its maximal side pieces. Their endpoint
pairs give the two terminations. Reserve unused separator vertices as in
`SideReservations`. The endpoint, parity, and contracted-path lemmas
verify all four conditions of II's crossing-scheme definition.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v
variable {α : Type u} {β : Type v} (G H H' : Graph α β) (A : Termination V(G))
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)

/-- The crossing scheme obtained by cutting a feasible linkage along a
separation, as in the forward proof of Graph Minors II (2.9), page 315. -/
noncomputable def extractedCrossingScheme (hsep : IsSeparation G H H') : CrossingScheme G H H' A where
  left := sideTermination A G H P hP true
  right := sideTermination A G H P hP false
  reservedLeft := sideReservedLeft A G H H' P hP
  reservedRight := sideReservedRight A G H H' P hP
  reservedLeft_subset := fun _ h => h.1.1
  reservedRight_subset := fun _ h => h.1.1
  left_support := sideTermination_left_support A G H P hP hsep
  right_support := sideTermination_right_support A G H P hP hsep
  even_support := fun a _ => sideTermination_even_support A G H P hP a
  reserved_disjoint := sideReservations_disjoint A G H H' P hP
  reserved_union := sideReservations_union A G H H' P hP
  path_union := sidePairGraph_isPairPathUnion A G H P hP

/-- First-side pieces avoid both the reservation and the protected original terminals. -/
theorem RunPieceIndex.avoids_extractedLeft (hsep : IsSeparation G H H')
    (i : RunPieceIndex A G H P) (hc : i.color A G H P = true) :
    Disjoint (i.path A G H P).vertices
      ((extractedCrossingScheme G H H' A P hP hsep).reservedLeft ∪
        ((A.support ∩ (V(H) ∩ V(H'))) \
          (extractedCrossingScheme G H H' A P hP hsep).left.support)) := by
  apply Set.disjoint_left.2
  intro a hai hz
  rcases hz with hz | hz
  · exact Set.disjoint_left.1 (i.avoids_reservedLeft A G H H' P hP hc) hai hz
  · have ha := i.original_mem_side_support A G H P hP hz.1.1 hai
    rw [hc] at ha
    exact hz.2 ha

/-- Second-side pieces avoid both the reservation and the protected original terminals. -/
theorem RunPieceIndex.avoids_extractedRight (hsep : IsSeparation G H H')
    (i : RunPieceIndex A G H P) (hc : i.color A G H P = false) :
    Disjoint (i.path A G H P).vertices
      ((extractedCrossingScheme G H H' A P hP hsep).reservedRight ∪
        ((A.support ∩ (V(H) ∩ V(H'))) \
          (extractedCrossingScheme G H H' A P hP hsep).right.support)) := by
  apply Set.disjoint_left.2
  intro a hai hz
  rcases hz with hz | hz
  · exact Set.disjoint_left.1 (i.avoids_reservedRight A G H H' P hP hc) hai hz
  · have ha := i.original_mem_side_support A G H P hP hz.1.1 hai
    rw [hc] at ha
    exact hz.2 ha

end GraphMinor.GM02
