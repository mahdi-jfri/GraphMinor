module

public import GraphMinor.Compute.GM06Alg34GapInducedData
public import GraphMinor.Compute.GM06Alg34SingletonReduce

/-!
# Finite singleton reductions with cuff gap incidence

Use the same surviving vertex list as the base singleton reduction and
carry the supplied gap groups through the proved finite induced update.
Repeated deletion terminates by the original strict vertex-count bound.
The base drawing of the augmented result is exactly the existing finite
singleton exhaustion, so its size and termination bounds remain valid.
-/

@[expose] public section
namespace GraphMinor.Compute

namespace GM06GapInput

/-- Delete one singleton vertex while retaining exact finite gap incidence data.
This is the input update for VI (3.3)(i), page 120. -/
def singletonGapData (X : GM06GapInput) (v : Fin X.drawing.n) : GM06GapInput :=
  X.inducedGapInput (X.drawing.singletonSurvivors v)

/-- The augmented singleton update has exactly the existing base drawing payload. -/
theorem singletonGapData_drawing (X : GM06GapInput) (v : Fin X.drawing.n) :
    (X.singletonGapData v).drawing = X.drawing.singletonData v := rfl

/-- Every augmented singleton update strictly reduces its vertex count. -/
theorem singletonGapData_n_lt (X : GM06GapInput) (v : Fin X.drawing.n) :
    (X.singletonGapData v).drawing.n < X.drawing.n :=
  gm06SingletonData_n_lt X.drawing v

end GM06GapInput

/-- Exhaust VI (3.3)(i) on the supplied finite drawing and gap incidence. -/
def gm06GapReduceSingletons (X : GM06GapInput) : GM06GapInput :=
  match gm06FindSingleton X.drawing.division with
  | none => X
  | some v => gm06GapReduceSingletons (X.singletonGapData v)
termination_by X.drawing.n
decreasing_by exact X.singletonGapData_n_lt v

/-- The augmented finite exhaustion has the same base drawing as the
already proved singleton exhaustion. -/
theorem gm06GapReduceSingletons_drawing (X : GM06GapInput) :
    (gm06GapReduceSingletons X).drawing = gm06ReduceSingletons X.drawing := by
  induction X using gm06GapReduceSingletons.induct with
  | case1 X h => rw [gm06GapReduceSingletons, h, gm06ReduceSingletons, h]
  | case2 X v h ih =>
    rw [gm06GapReduceSingletons, h, ih]
    conv_rhs => rw [gm06ReduceSingletons, h]
    rfl

/-- No singleton block remains after the augmented finite exhaustion. -/
theorem gm06GapReduceSingletons_find_none (X : GM06GapInput) :
    gm06FindSingleton (gm06GapReduceSingletons X).drawing.division = none := by
  rw [gm06GapReduceSingletons_drawing]
  exact gm06ReduceSingletons_find_none X.drawing

end GraphMinor.Compute
