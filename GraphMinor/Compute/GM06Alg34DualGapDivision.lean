module

public import GraphMinor.Compute.GM06Alg34DualGapRelation
public import GraphMinor.Compute.GM06Alg34FiniteClasses

/-!
# Computing the dual division as finite gap lists

Enumerate the equivalence classes of the finite no-crossing relation
by their least gap labels. The resulting lists are exactly the dual
classes of VI Section 2, page 117. They form a division and cover every
gap, including the empty boundary-list case.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

open Set GM06

/-- The computed dual division on the supplied boundary-gap labels. -/
def dualGapDivision (x : GM06DrawingData) (L : List (Fin x.n)) : List (List (Fin L.length)) :=
  gm06ClassBlocks (x.dualGapRelated L)

/-- The set of blocks denoted by the computed gap lists. -/
def dualGapDivisionSet (x : GM06DrawingData) (L : List (Fin x.n)) : Set (Set (Fin L.length)) :=
  block '' {B | B ∈ x.dualGapDivision L}

/-- The computed gap blocks form a valid finite division. -/
theorem dualGapDivision_isDivision (x : GM06DrawingData) (L : List (Fin x.n)) :
    IsDivision (x.dualGapDivisionSet L) :=
  gm06ClassDivision_isDivision (x.dualGapRelated L) (x.dualGapRelated_equivalence L)

/-- Every supplied gap belongs to the computed dual division. -/
theorem dualGapDivision_union (x : GM06DrawingData) (L : List (Fin x.n)) :
    divisionUnion (x.dualGapDivisionSet L) = Set.univ :=
  gm06ClassDivision_union (x.dualGapRelated L) (x.dualGapRelated_equivalence L)

/-- The computed finite division is exactly the set of equivalence
classes of the paper's finite no-crossing test. -/
theorem dualGapDivision_eq_classes (x : GM06DrawingData) (L : List (Fin x.n)) :
    x.dualGapDivisionSet L =
      (fun i : Fin L.length => {j | x.dualGapRelated L i j = true}) '' Set.univ :=
  gm06ClassDivision_eq_classes (x.dualGapRelated L) (x.dualGapRelated_equivalence L)

end GraphMinor.Compute.GM06DrawingData
