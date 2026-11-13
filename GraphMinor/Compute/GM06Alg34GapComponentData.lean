module

public import GraphMinor.Compute.GM06Alg34GapInducedData
public import GraphMinor.Compute.GM06Alg34ComponentInputs
public import GraphMinor.Compute.GM06Alg34GapDiscLayout

/-!
# Augmented finite inputs for component branches

Restrict the drawing to the component selected by a supplied vertex
label and retain its exact cuff gap incidence. Canonical component
roots enumerate all such branch inputs in the same order as the base
component list used in VI (3.3)(iv).
-/

@[expose] public section
namespace GraphMinor.Compute.GM06GapInput

/-- The complete augmented input on the component of a supplied label. -/
def componentGapData (X : GM06GapInput) (a : Fin X.drawing.n) : GM06GapInput :=
  X.inducedGapInput (X.drawing.componentVertices a)

/-- The component's base drawing is the existing exact finite component payload. -/
theorem componentGapData_drawing (X : GM06GapInput) (a : Fin X.drawing.n) :
    (X.componentGapData a).drawing = X.drawing.componentData a := rfl

/-- Augmented component inputs in canonical root order. -/
def componentGapInputs (X : GM06GapInput) : List GM06GapInput :=
  X.drawing.componentRoots.map X.componentGapData

/-- Reading the component inputs' base drawings recovers the existing component list. -/
theorem componentGapInputs_drawings (X : GM06GapInput) :
    X.componentGapInputs.map GM06GapInput.drawing = X.drawing.componentInputs := by
  simp only [componentGapInputs, GM06DrawingData.componentInputs, List.map_map,
    Function.comp_def, componentGapData_drawing]

/-- Every augmented component branch preserves the matching single-cuff layout. -/
theorem componentGapData_disc_layout (X : GM06GapInput) (a : Fin X.drawing.n)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length) :
    ∃ L R, (X.componentGapData a).drawing.cuffs = [L] ∧
      (X.componentGapData a).gapRegions = [R] ∧ R.length = L.length :=
  X.inducedGapInput_disc_layout (X.drawing.componentVertices a) hshape

end GraphMinor.Compute.GM06GapInput
