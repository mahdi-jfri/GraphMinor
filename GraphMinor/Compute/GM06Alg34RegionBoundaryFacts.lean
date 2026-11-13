module

public import GraphMinor.Compute.GM06Alg34RegionBoundary

/-!
# Inactive closure cells belong to the same region

If an inactive cell occurs in the closure of a cell already in a
complement component, the incidence graph joins it to that component.
Thus an inactive closure hit is exactly reachability. Boundary lists
can therefore discard all inactive closure cells and retain precisely
the active vertex and edge cells.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

/-- Among inactive cells, a closure hit is exactly membership in the
corresponding finite complement component. -/
theorem regionClosureHit_inactive_iff (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.cellCount) (b : GM06CellIndex x) (hb : x.activeCell vs b = false) :
    x.regionClosureHit vs r b = true ↔ (x.complementGraph vs).Reachable r (x.cellNumbering b) := by
  simp only [regionClosureHit, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, hrc, hbc⟩
    by_cases hcb : c = b
    · exact hcb ▸ hrc
    · apply hrc.trans
      apply SimpleGraph.Adj.reachable
      change x.cellNumbering c ≠ x.cellNumbering b ∧ _
      simp only [Equiv.symm_apply_apply]
      refine ⟨fun h => hcb (x.cellNumbering.injective h), hc, hb, ?_⟩
      exact of_decide_eq_true (show decide (c ∈ x.cellClosure b ∨ b ∈ x.cellClosure c) = true from
        decide_eq_true (Or.inr hbc))
  · intro hrb
    refine ⟨b, hb, hrb, ?_⟩
    rcases b with v | e | r
    · simp [cellClosure]
    · simp [cellClosure]
    · simp [cellClosure]

end GraphMinor.Compute.GM06DrawingData
