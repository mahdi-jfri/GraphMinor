module

public import GraphMinor.Compute.GM06Alg34GapInteriorData
public import GraphMinor.Compute.GM06Alg34GapDiscLayout

/-!
# One finite interior-component search and deletion

Search the supplied drawing for a component away from every cuff.
Delete the first such component when it exists, carrying its gap
incidence through the exact induced update. Otherwise leave the input
unchanged. This is the finite result used by one driver iteration.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06GapInput

/-- Perform one available instance of VI (3.3)(ii) on the finite augmented input. -/
def interiorStepData (X : GM06GapInput) : GM06GapInput :=
  match X.drawing.findInteriorComponent with
  | none => X
  | some a => X.interiorGapData a

/-- The search/deletion step never increases the supplied vertex count. -/
theorem interiorStepData_n_le (X : GM06GapInput) :
    X.interiorStepData.drawing.n ≤ X.drawing.n := by
  cases hf : X.drawing.findInteriorComponent with
  | none => rw [interiorStepData, hf]
  | some a => rw [interiorStepData, hf]; exact (X.interiorGapData_n_lt a).le

/-- A successful component search makes the step strictly decrease the vertex count. -/
theorem interiorStepData_n_lt (X : GM06GapInput) (a : Fin X.drawing.n)
    (ha : X.drawing.findInteriorComponent = some a) :
    X.interiorStepData.drawing.n < X.drawing.n := by
  rw [interiorStepData, ha]
  exact X.interiorGapData_n_lt a

/-- The matching single-cuff layout remains valid after the step. -/
theorem interiorStepData_disc_layout (X : GM06GapInput)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length) :
    ∃ L R, X.interiorStepData.drawing.cuffs = [L] ∧
      X.interiorStepData.gapRegions = [R] ∧ R.length = L.length := by
  cases hf : X.drawing.findInteriorComponent with
  | none => rw [interiorStepData, hf]; exact hshape
  | some a =>
    rw [interiorStepData, hf]
    exact X.inducedGapInput_disc_layout (X.drawing.interiorComponentSurvivors a) hshape

end GraphMinor.Compute.GM06GapInput
