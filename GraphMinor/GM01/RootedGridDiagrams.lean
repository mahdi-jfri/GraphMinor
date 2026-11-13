module

public import GraphMinor.GM01.GridDiagramSideSupports
public import GraphMinor.GM01.RootedGraphs
import Lean.Elab.Tactic.Omega

/-!
# Roots of the recursive grid diagrams

The root of the diagram in Graph Minors I, Figure 3, page 52, is its
centre. The two side crosses are rooted at the adjacent vertices in
the central row. These are data for the diagram, with no tree-model
condition included in their definitions.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph

/-- The centre vertex of a square of odd side length. -/
def gridDiagramRoot (a : ℕ) : Fin (2 * a + 1) × Fin (2 * a + 1) :=
  (⟨a, by omega⟩, ⟨a, by omega⟩)

/-- The square with its free centre column and distinguished central root. -/
def rootedGridDiagram (a : ℕ) : RootedGraph
    (Fin (2 * a + 1) × Fin (2 * a + 1))
    (Sym2 (Fin (2 * a + 1) × Fin (2 * a + 1))) :=
  ⟨(gridGraph (2 * a + 1)).induce (gridDiagramRegion a),
    ⟨gridDiagramRoot a, gridDiagramRegion_root a⟩⟩

/-- The vertex of a side cross next to the central root. -/
def gridDiagramSideRoot (a : ℕ) (right : Bool) :
    Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1) :=
  (⟨2 * a + 1, by omega⟩,
   ⟨if right then 2 * a + 2 else 2 * a,
     by cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩)

/-- The side root belongs to its horizontal cross interval. -/
theorem gridDiagramSideRoot_mem (a : ℕ) (right : Bool) :
    gridDiagramSideRoot a right ∈ gridDiagramSideRegion a right := by
  left
  refine ⟨rfl, ?_⟩
  cases right
  · change a ≤ 2 * a ∧ 2 * a ≤ 2 * a
    exact ⟨by omega, le_rfl⟩
  · change 2 * a + 2 ≤ 2 * a + 2 ∧ 2 * a + 2 ≤ 3 * a + 2
    exact ⟨le_rfl, by omega⟩

/-- One arm with its root adjacent to the central root. -/
def rootedGridDiagramSide (a : ℕ) (right : Bool) : RootedGraph
    (Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1))
    (Sym2 (Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1))) :=
  ⟨(gridGraph (2 * (2 * a + 1) + 1)).induce (gridDiagramSideSupport a right),
    ⟨gridDiagramSideRoot a right, Or.inl (gridDiagramSideRoot_mem a right)⟩⟩

/-- The central root has an actual grid edge to each side root. -/
theorem gridDiagramRoot_adj_side (a : ℕ) (right : Bool) :
    (gridGraph (2 * (2 * a + 1) + 1)).Adj
      (gridDiagramRoot (2 * a + 1)) (gridDiagramSideRoot a right) := by
  apply (gridGraph_adj_iff _ _).mpr
  right
  refine ⟨?_, rfl⟩
  change (2 * a + 1 + 1 = (if right then 2 * a + 2 else 2 * a)) ∨
    ((if right then 2 * a + 2 else 2 * a) + 1 = 2 * a + 1)
  cases right
  · exact Or.inr rfl
  · exact Or.inl rfl

end GraphMinor.GM01
