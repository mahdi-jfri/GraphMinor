module

public import GraphMinor.Compute.GM06Alg34InducedData
public import GraphMinor.Compute.GM06Alg34Singleton

/-!
# The finite payload for one singleton reduction

Delete the selected label from the complete original vertex list, then
compute the induced drawing data. Both the surviving labels and every
field of the result are finite computations on the supplied data.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

/-- The surviving vertex labels after deleting one specified vertex. -/
def singletonSurvivors (x : GM06DrawingData) (v : Fin x.n) : List (Fin x.n) :=
  gm06EraseVertex (List.finRange x.n) v

/-- The complete finite drawing payload for the singleton deletion (3.3)(i). -/
def singletonData (x : GM06DrawingData) (v : Fin x.n) : GM06DrawingData :=
  x.inducedData (x.singletonSurvivors v)

/-- Precisely the labels different from the selected singleton vertex survive. -/
theorem mem_singletonSurvivors_iff (x : GM06DrawingData) (v w : Fin x.n) :
    w ∈ x.singletonSurvivors v ↔ w ≠ v := by
  simp [singletonSurvivors, gm06EraseVertex]

end GraphMinor.Compute.GM06DrawingData
