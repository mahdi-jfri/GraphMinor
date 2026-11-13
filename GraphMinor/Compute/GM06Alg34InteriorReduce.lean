module

public import GraphMinor.Compute.GM06Alg34DeletionSpace

/-!
# The finite sequence of interior-component deletions

Find a component with no cuff vertex, replace the input by its computed
induced payload, and repeat. Every such deletion removes its source
vertex, so the recursion terminates. The output has no remaining
component to which VI (3.3)(ii) applies.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A source returned by the finite component search passes its cuff test. -/
theorem gm06FindInteriorComponent_sound (x : GM06DrawingData) (a : Fin x.n)
    (ha : x.findInteriorComponent = some a) : x.isInteriorComponent a = true :=
  List.find?_some ha

/-- Exhaust the component deletion case VI (3.3)(ii) on finite input data. -/
def gm06ReduceInteriorComponents (x : GM06DrawingData) : GM06DrawingData :=
  match x.findInteriorComponent with
  | none => x
  | some a => gm06ReduceInteriorComponents (x.interiorComponentData a)
termination_by x.n
decreasing_by exact gm06InteriorComponentData_n_lt x a

/-- Exhaustion leaves no component with all its vertices away from the cuffs. -/
theorem gm06ReduceInteriorComponents_find_none (x : GM06DrawingData) :
    (gm06ReduceInteriorComponents x).findInteriorComponent = none := by
  induction x using gm06ReduceInteriorComponents.induct with
  | case1 x h => rw [gm06ReduceInteriorComponents, h]; exact h
  | case2 x a h ih => rw [gm06ReduceInteriorComponents, h]; exact ih

/-- Exhausting interior components cannot increase the supplied vertex count. -/
theorem gm06ReduceInteriorComponents_n_le (x : GM06DrawingData) :
    (gm06ReduceInteriorComponents x).n ≤ x.n := by
  induction x using gm06ReduceInteriorComponents.induct with
  | case1 x h => rw [gm06ReduceInteriorComponents, h]
  | case2 x a h ih =>
    rw [gm06ReduceInteriorComponents, h]
    exact ih.trans (gm06InteriorComponentData_n_lt x a).le

/-- Exhausting interior components cannot increase the uniform space reservation. -/
theorem gm06ReduceInteriorComponents_space_le (x : GM06DrawingData) :
    gm06SingletonSpace (gm06ReduceInteriorComponents x) ≤ gm06SingletonSpace x := by
  induction x using gm06ReduceInteriorComponents.induct with
  | case1 x h => rw [gm06ReduceInteriorComponents, h]
  | case2 x a h ih =>
    rw [gm06ReduceInteriorComponents, h]
    exact ih.trans (gm06Induced_space_le x (x.interiorComponentSurvivors a)
      (gm06InteriorComponentData_n_lt x a))

end GraphMinor.Compute
