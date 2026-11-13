module

public import GraphMinor.Compute.GM06Alg34SingletonBounds
public import GraphMinor.Compute.GM06Alg34SingletonFind

/-!
# The finite sequence of singleton reductions

Repeatedly apply the supplied division's first-singleton test and the
computed singleton payload update. The vertex count strictly decreases,
so this finite-data computation ends at an input with no singleton block.
This function specifies the result of the RAM singleton loop.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Exhaust the singleton case of VI (3.3)(i), using only finite input data. -/
def gm06ReduceSingletons (x : GM06DrawingData) : GM06DrawingData :=
  match gm06FindSingleton x.division with
  | none => x
  | some v => gm06ReduceSingletons (x.singletonData v)
termination_by x.n
decreasing_by exact gm06SingletonData_n_lt x v

/-- Exhaustion leaves no singleton block in the output division. -/
theorem gm06ReduceSingletons_find_none (x : GM06DrawingData) :
    gm06FindSingleton (gm06ReduceSingletons x).division = none := by
  induction x using gm06ReduceSingletons.induct with
  | case1 x h => rw [gm06ReduceSingletons, h]; exact h
  | case2 x v h ih => rw [gm06ReduceSingletons, h]; exact ih

/-- Singleton exhaustion cannot increase the number of vertices. -/
theorem gm06ReduceSingletons_n_le (x : GM06DrawingData) :
    (gm06ReduceSingletons x).n ≤ x.n := by
  induction x using gm06ReduceSingletons.induct with
  | case1 x h => rw [gm06ReduceSingletons, h]
  | case2 x v h ih =>
    rw [gm06ReduceSingletons, h]
    exact ih.trans (gm06SingletonData_n_lt x v).le

/-- Singleton exhaustion cannot increase the region-count charge. -/
theorem gm06ReduceSingletons_charge_le (x : GM06DrawingData) :
    gm06SingletonRegionCharge (gm06ReduceSingletons x) ≤ gm06SingletonRegionCharge x := by
  induction x using gm06ReduceSingletons.induct with
  | case1 x h => rw [gm06ReduceSingletons, h]
  | case2 x v h ih =>
    rw [gm06ReduceSingletons, h]
    exact ih.trans (gm06SingletonRegionCharge_le x v)

end GraphMinor.Compute
