module

public import GraphMinor.GM01.GridDiagramQuadrants
import Lean.Elab.Tactic.Omega

/-!
# Supports of the left and right recursive arms

For the induction in Graph Minors I, (3.2), Figure 3 on page 52,
each arm consists of its cross and its two corner copies. The left
arm stays left of the centre column, and the right arm stays right
of it. This separates both arms from one another and from the root.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set

/-- The cross and two corner copies forming one arm of Figure 3. -/
def gridDiagramSideSupport (a : ℕ) (right : Bool) :
    Set (Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1)) :=
  gridDiagramSideRegion a right ∪
    (gridDiagramQuadrantRegion a false right ∪ gridDiagramQuadrantRegion a true right)

/-- Every vertex of an arm stays on its chosen side of the centre. -/
theorem gridDiagramSideSupport_side {a : ℕ} {right : Bool}
    {v : Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1)}
    (hv : v ∈ gridDiagramSideSupport a right) :
    if right then 2 * a + 2 ≤ v.2.val else v.2.val ≤ 2 * a := by
  rcases hv with hv | hv | hv
  · rcases hv with ⟨_, hc⟩ | ⟨hc, _⟩
    · cases right
      · exact hc.2
      · exact hc.1
    · cases right <;> simp only [gridDiagramSideColumn, Bool.false_eq_true, ↓reduceIte] at hc ⊢ <;> omega
  · exact gridDiagramQuadrantRegion_side hv
  · exact gridDiagramQuadrantRegion_side hv

/-- The left and right recursive arms are disjoint. -/
theorem gridDiagramSideSupport_disjoint (a : ℕ) :
    Disjoint (gridDiagramSideSupport a false) (gridDiagramSideSupport a true) := by
  apply Set.disjoint_left.mpr
  intro v hl hr
  have hl' := gridDiagramSideSupport_side hl
  have hr' := gridDiagramSideSupport_side hr
  simp only [Bool.false_eq_true, ↓reduceIte] at hl' hr'
  omega

/-- Both arms lie in the available region of the larger diagram. -/
theorem gridDiagramSideSupport_subset (a : ℕ) (right : Bool) :
    gridDiagramSideSupport a right ⊆ gridDiagramRegion (2 * a + 1) := by
  intro v hv
  left
  have hs := gridDiagramSideSupport_side hv
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at hs <;> omega

/-- The central root belongs to neither arm. -/
theorem gridDiagramSideSupport_not_centre (a : ℕ) (right : Bool) :
    ((⟨2 * a + 1, by omega⟩ : Fin (2 * (2 * a + 1) + 1)),
     (⟨2 * a + 1, by omega⟩ : Fin (2 * (2 * a + 1) + 1))) ∉
      gridDiagramSideSupport a right := by
  intro h
  have hs := gridDiagramSideSupport_side h
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at hs <;> omega

end GraphMinor.GM01
