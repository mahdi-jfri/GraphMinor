module

public import GraphMinor.GM02.CrossingScheme
public import GraphMinor.GM02.TerminationMaps

/-!
# Crossing schemes depend only on side vertex sets and original pairs

The printed crossing-scheme conditions do not inspect the edges of the
three containing graphs. Replace those graphs by graphs with the same
vertex sets, and retain the same original terminal pairs. Rebase the two
new terminations to the new containing set. Every scheme condition and
all four scheme data fields are preserved. This connects numbered
edgeless boundary descriptions to their concrete graph representations.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v v'

/-- Transfer a scheme across equal vertex-set and original-pair data. -/
noncomputable def CrossingScheme.transferVertexSets {α : Type u} {β : Type v} {β' : Type v'}
    {G H H' : Graph α β} {A : Termination V(G)} (C : CrossingScheme G H H' A)
    (G₁ H₁ H₁' : Graph α β') (hG : V(G) = V(G₁)) (hH : V(H) = V(H₁)) (hH' : V(H') = V(H₁'))
    (A₁ : Termination V(G₁)) (hA : A₁.pairs = A.pairs) : CrossingScheme G₁ H₁ H₁' A₁ := by
  letI : DecidableEq α := Classical.decEq α
  have hLS : C.left.support ⊆ V(G₁) := fun _ ha => hG ▸ C.left.support_subset ha
  have hRS : C.right.support ⊆ V(G₁) := fun _ ha => hG ▸ C.right.support_subset ha
  let L := C.left.rebase hLS
  let R := C.right.rebase hRS
  have hAS : A₁.support = A.support := by
    unfold Termination.support
    rw [hA]
  refine
    { left := L
      right := R
      reservedLeft := C.reservedLeft
      reservedRight := C.reservedRight
      reservedLeft_subset := ?_
      reservedRight_subset := ?_
      left_support := ?_
      right_support := ?_
      even_support := ?_
      reserved_disjoint := C.reserved_disjoint
      reserved_union := ?_
      path_union := ?_ }
  · rw [← hH, ← hH']
    exact C.reservedLeft_subset
  · rw [← hH, ← hH']
    exact C.reservedRight_subset
  · change C.left.support \ (V(H₁) ∩ V(H₁')) = A₁.support ∩ (V(H₁) \ V(H₁'))
    rw [← hH, ← hH', hAS]
    exact C.left_support
  · change C.right.support \ (V(H₁) ∩ V(H₁')) = A₁.support ∩ (V(H₁') \ V(H₁))
    rw [← hH, ← hH', hAS]
    exact C.right_support
  · intro a ha
    rw [← hH, ← hH'] at ha
    change Even ((if a ∈ A₁.support then 1 else 0) +
      (if a ∈ C.left.support then 1 else 0) + (if a ∈ C.right.support then 1 else 0) : ℕ)
    rw [hAS]
    exact C.even_support a ha
  · change C.reservedLeft ∪ C.reservedRight =
      (V(H₁) ∩ V(H₁')) \ (A₁.support ∪ C.left.support ∪ C.right.support)
    rw [← hH, ← hH', hAS]
    exact C.reserved_union
  · have hp : IsPairPathUnion A₁
        (SimpleGraph.fromEdgeSet (C.left.pairs ∪ C.right.pairs : Finset (Sym2 α)))
        (C.left.support ∪ C.right.support) := by
      unfold IsPairPathUnion
      rw [hA]
      exact C.path_union
    exact hp

section Data
variable {α : Type u} {β : Type v} {β' : Type v'} {G H H' : Graph α β} {A : Termination V(G)}
  (C : CrossingScheme G H H' A) (G₁ H₁ H₁' : Graph α β')
  (hG : V(G) = V(G₁)) (hH : V(H) = V(H₁)) (hH' : V(H') = V(H₁'))
  (A₁ : Termination V(G₁)) (hA : A₁.pairs = A.pairs)

/-- Transferring graph representations retains the first scheme pair set. -/
theorem CrossingScheme.transferVertexSets_left_pairs :
    (C.transferVertexSets G₁ H₁ H₁' hG hH hH' A₁ hA).left.pairs = C.left.pairs := by
  unfold CrossingScheme.transferVertexSets
  rfl

/-- Transferring graph representations retains the second scheme pair set. -/
theorem CrossingScheme.transferVertexSets_right_pairs :
    (C.transferVertexSets G₁ H₁ H₁' hG hH hH' A₁ hA).right.pairs = C.right.pairs := by
  unfold CrossingScheme.transferVertexSets
  rfl

/-- Transferring graph representations retains the first reserved set. -/
theorem CrossingScheme.transferVertexSets_reservedLeft :
    (C.transferVertexSets G₁ H₁ H₁' hG hH hH' A₁ hA).reservedLeft = C.reservedLeft := by
  unfold CrossingScheme.transferVertexSets
  rfl

/-- Transferring graph representations retains the second reserved set. -/
theorem CrossingScheme.transferVertexSets_reservedRight :
    (C.transferVertexSets G₁ H₁ H₁' hG hH hH' A₁ hA).reservedRight = C.reservedRight := by
  unfold CrossingScheme.transferVertexSets
  rfl
end Data

end GraphMinor.GM02
