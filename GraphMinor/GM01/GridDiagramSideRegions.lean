module

public import GraphMinor.GM01.GridDiagramRegions
public import GraphMinor.GM01.GridCrosses
import Lean.Elab.Tactic.Omega

/-!
# The two side crosses of Figure 3

In the two-level induction for Graph Minors I, (3.2), pages 51–52,
the central root has a left child and a right child. Each child
occupies a cross between two smaller copies. The horizontal part
stops next to the central root, and the vertical part stops next to
the roots of the two copies. All these vertices avoid the central
column of the larger diagram.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph

/-- The column through the two smaller roots on a chosen side. -/
def gridDiagramSideColumn (a : ℕ) (side : Bool) : ℕ :=
  if side then 3 * a + 2 else a

/-- The cross representing one child of the central root in Figure 3. -/
def gridDiagramSideRegion (a : ℕ) (side : Bool) :
    Set (Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1)) :=
  {v | (v.1.val = 2 * a + 1 ∧
      (if side then 2 * a + 2 ≤ v.2.val ∧ v.2.val ≤ 3 * a + 2
       else a ≤ v.2.val ∧ v.2.val ≤ 2 * a)) ∨
    (v.2.val = gridDiagramSideColumn a side ∧
      a + 1 ≤ v.1.val ∧ v.1.val ≤ 3 * a + 1)}

/-- The two actual side crosses in Figure 3 are connected. -/
theorem gridDiagramSideRegion_connected (a : ℕ) (side : Bool) :
    GraphConnected ((gridGraph (2 * (2 * a + 1) + 1)).induce (gridDiagramSideRegion a side)) := by
  let row : Fin (2 * (2 * a + 1) + 1) := ⟨2 * a + 1, by omega⟩
  let col : Fin (2 * (2 * a + 1) + 1) := ⟨gridDiagramSideColumn a side,
    by cases side <;> simp only [gridDiagramSideColumn, Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  let rlo : Fin (2 * (2 * a + 1) + 1) := ⟨a + 1, by omega⟩
  let rhi : Fin (2 * (2 * a + 1) + 1) := ⟨3 * a + 1, by omega⟩
  let clo : Fin (2 * (2 * a + 1) + 1) := ⟨if side then 2 * a + 2 else a,
    by cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  let chi : Fin (2 * (2 * a + 1) + 1) := ⟨if side then 3 * a + 2 else 2 * a,
    by cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  have hr : rlo ≤ row ∧ row ≤ rhi := by
    change a + 1 ≤ 2 * a + 1 ∧ 2 * a + 1 ≤ 3 * a + 1
    constructor <;> omega
  have hc : clo ≤ col ∧ col ≤ chi := by
    change (if side then 2 * a + 2 else a) ≤ gridDiagramSideColumn a side ∧
      gridDiagramSideColumn a side ≤ (if side then 3 * a + 2 else 2 * a)
    cases side <;> simp only [gridDiagramSideColumn, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> omega
  have heq : gridDiagramSideRegion a side =
      ((fun c : Fin (2 * (2 * a + 1) + 1) ↦ (row, c)) '' Icc clo chi) ∪
      ((fun r : Fin (2 * (2 * a + 1) + 1) ↦ (r, col)) '' Icc rlo rhi) := by
    ext v
    constructor
    · intro hv
      rcases hv with ⟨hrow, hcols⟩ | ⟨hcol, hrows⟩
      · left
        refine ⟨v.2, ?_, ?_⟩
        · cases side <;> exact hcols
        · apply Prod.ext
          · exact Fin.ext hrow.symm
          · rfl
      · right
        exact ⟨v.1, hrows, Prod.ext rfl (Fin.ext hcol.symm)⟩
    · rintro (⟨c, hc', rfl⟩ | ⟨r, hr', rfl⟩)
      · left
        refine ⟨rfl, ?_⟩
        cases side <;> exact hc'
      · right
        exact ⟨rfl, hr'⟩
  rw [heq]
  exact gridGraph_cross_connected row col rlo rhi clo chi hr hc

/-- The side crosses leave the larger centre column unused. -/
theorem gridDiagramSideRegion_avoids_centre {a : ℕ} {side : Bool}
    {v : Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1)}
    (hv : v ∈ gridDiagramSideRegion a side) : v.2.val ≠ 2 * a + 1 := by
  rcases hv with ⟨_, hc⟩ | ⟨hc, _⟩
  · cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc <;> omega
  · cases side <;> simp only [gridDiagramSideColumn, Bool.false_eq_true, ↓reduceIte] at hc <;> omega

/-- The left and right child crosses have disjoint vertex sets. -/
theorem gridDiagramSideRegion_disjoint (a : ℕ) :
    Disjoint (gridDiagramSideRegion a false) (gridDiagramSideRegion a true) := by
  apply Set.disjoint_left.mpr
  intro v hl hr
  rcases hl with ⟨_, hl⟩ | ⟨hl, _⟩ <;>
    rcases hr with ⟨_, hr⟩ | ⟨hr, _⟩ <;>
    simp only [gridDiagramSideColumn, Bool.false_eq_true, ↓reduceIte] at hl hr <;> omega

end GraphMinor.GM01
