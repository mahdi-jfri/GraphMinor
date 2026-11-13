module

public import GraphMinor.Compute.GM06Alg34ComplementBfs

/-!
# Testing region roots with component marks

The complement graph has no edges incident with active cells. Thus
all cells reachable from an inactive source remain inactive. The least
inactive label of a component can therefore be found by checking that
its BFS has no mark at any smaller label, without a second active-mask
lookup for each smaller label.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

/-- A component of an inactive cell contains only inactive cells. -/
theorem complementGraph_reachable_inactive (x : GM06DrawingData) (vs : List (Fin x.n))
    {a b : Fin x.cellCount} (ha : x.activeCell vs (x.cellNumbering.symm a) = false)
    (hab : (x.complementGraph vs).Reachable a b) :
    x.activeCell vs (x.cellNumbering.symm b) = false := by
  have hp := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hab
  induction hp with
  | refl => exact ha
  | tail _ hstep _ => exact hstep.2.2.1

/-- A canonical region root is an inactive label whose BFS marks no
smaller label. Smaller reached cells would already be inactive. -/
theorem isRegionRoot_iff_no_smaller_reachable (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) :
    x.isRegionRoot vs a = true ↔
      x.activeCell vs (x.cellNumbering.symm a) = false ∧
        ∀ b : Fin x.cellCount, b < a → ¬ (x.complementGraph vs).Reachable a b := by
  simp only [isRegionRoot, decide_eq_true_eq]
  constructor
  · rintro ⟨ha, hmin⟩
    refine ⟨ha, fun b hba hab => ?_⟩
    exact hmin b hba (x.complementGraph_reachable_inactive vs ha hab) hab
  · rintro ⟨ha, hmin⟩
    exact ⟨ha, fun b hba _ => hmin b hba⟩

end GraphMinor.Compute.GM06DrawingData
