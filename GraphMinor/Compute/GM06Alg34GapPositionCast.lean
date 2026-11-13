module

public import GraphMinor.Compute.GM06Alg34DualGapRelation

/-!
# Transporting gap positions across equal list lengths

The same finite list can be presented through equal cuff lengths.
Transport of its positions changes neither its crossing tests nor the
list obtained by reading a function at all positions.
-/

public section
namespace GraphMinor.Compute

/-- Transporting the domain length leaves a finite function's list unchanged. -/
theorem gm06OfFn_cast {α : Type*} {k n : ℕ} (e : k = n) (f : Fin n → α) :
    List.ofFn (fun i : Fin k => f (Fin.cast e i)) = List.ofFn f := by
  subst n
  rfl

/-- Equal cuff lists have equal primal-versus-gap tests after position transport. -/
theorem gm06PairCrossesGaps_cast {n : ℕ} {L M : List (Fin n)} (e : L = M)
    (a b : Fin n) (i j : Fin L.length) :
    GM06DrawingData.pairCrossesGaps L a b i j =
      GM06DrawingData.pairCrossesGaps M a b
        (Fin.cast (congrArg List.length e) i) (Fin.cast (congrArg List.length e) j) := by
  subst M
  rfl

/-- Equal finite position counts have equal cyclic gap crossing tests. -/
theorem gm06CrossesFinRange_cast {k n : ℕ} (e : k = n) (a b i j : Fin k) :
    GM06DrawingData.crossesOnList (List.finRange k) a b i j =
      GM06DrawingData.crossesOnList (List.finRange n)
        (Fin.cast e a) (Fin.cast e b) (Fin.cast e i) (Fin.cast e j) := by
  subst n
  rfl

end GraphMinor.Compute
