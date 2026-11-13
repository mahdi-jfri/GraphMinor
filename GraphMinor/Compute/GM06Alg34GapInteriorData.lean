module

public import GraphMinor.Compute.GM06Alg34GapInducedData
public import GraphMinor.Compute.GM06Alg34DeletionSpace

/-!
# Finite interior-component deletion with gap incidence

Delete the reachable component selected by the base finite input and
carry the supplied cuff gaps through the same induced update. The base
payload is the existing component-deletion payload, so its strict vertex
decrease and uniform space bounds also apply to this augmented update.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06GapInput

/-- Delete a selected component and update every supplied gap region.
This is the finite augmented input update for VI (3.3)(ii), page 120. -/
def interiorGapData (X : GM06GapInput) (a : Fin X.drawing.n) : GM06GapInput :=
  X.inducedGapInput (X.drawing.interiorComponentSurvivors a)

/-- The augmented component deletion has the existing exact base payload. -/
theorem interiorGapData_drawing (X : GM06GapInput) (a : Fin X.drawing.n) :
    (X.interiorGapData a).drawing = X.drawing.interiorComponentData a := rfl

/-- Every augmented component deletion removes its selected source vertex. -/
theorem interiorGapData_n_lt (X : GM06GapInput) (a : Fin X.drawing.n) :
    (X.interiorGapData a).drawing.n < X.drawing.n := gm06InteriorComponentData_n_lt X.drawing a

end GraphMinor.Compute.GM06GapInput
