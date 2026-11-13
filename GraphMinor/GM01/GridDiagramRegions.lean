module

public import GraphMinor.GM01.GridDiagramCoordinates
import Lean.Elab.Tactic.Omega

/-!
# The free centre column in the grid diagram

The recursive construction in Graph Minors I, (3.2), Figure 3,
pages 51–52, uses the centre column of each smaller square only at
its root. The rest of that column carries the vertical path from
the next larger square. These sets describe the space available for
the recursive copies, without assuming that a tree model exists.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set

/-- Vertices available to a recursive copy in Figure 3: remove the
centre column except for the central root. -/
def gridDiagramRegion (a : ℕ) : Set (Fin (2 * a + 1) × Fin (2 * a + 1)) :=
  {v | v.2.val ≠ a ∨ v.1.val = a}

/-- The root of a diagram remains in its available region. -/
theorem gridDiagramRegion_root (a : ℕ) :
    ((⟨a, by omega⟩ : Fin (2 * a + 1)),
     (⟨a, by omega⟩ : Fin (2 * a + 1))) ∈ gridDiagramRegion a :=
  Or.inr rfl

/-- On the centre column, only the root is available to the copy. -/
theorem gridDiagramRegion_centre_column {a : ℕ}
    (v : Fin (2 * a + 1) × Fin (2 * a + 1)) (hc : v.2.val = a) :
    v ∈ gridDiagramRegion a ↔ v.1.val = a := by
  change (v.2.val ≠ a ∨ v.1.val = a) ↔ _
  simp only [hc, ne_eq, not_true_eq_false, false_or]

/-- The vertical corridor above or below the root avoids the region
occupied by a smaller copy of the diagram. -/
theorem gridDiagramRegion_disjoint_centre_corridor (a : ℕ) :
    Disjoint (gridDiagramRegion a)
      {v : Fin (2 * a + 1) × Fin (2 * a + 1) | v.2.val = a ∧ v.1.val ≠ a} := by
  apply Set.disjoint_left.mpr
  intro v hv hc
  exact hc.2 ((gridDiagramRegion_centre_column v hc.1).mp hv)

/-- Every vertex in either half-square lies away from the larger
square's centre column. The two copies leave that column free. -/
theorem gridDiagramRegion_half_square {a : ℕ} (side : Bool)
    (x : Fin (2 * a + 1) × Fin (2 * a + 1))
    (row : Fin (2 * (2 * a + 1) + 1)) :
    (row, (⟨(if side then 2 * a + 2 else 0) + x.2.val,
      by cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩ :
        Fin (2 * (2 * a + 1) + 1))) ∈ gridDiagramRegion (2 * a + 1) := by
  change ((if side then 2 * a + 2 else 0) + x.2.val ≠ 2 * a + 1) ∨ _
  left
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

end GraphMinor.GM01
