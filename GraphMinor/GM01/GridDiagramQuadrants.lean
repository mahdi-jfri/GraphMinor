module

public import GraphMinor.GM01.GridDiagramSideRegions
import Lean.Elab.Tactic.Omega

/-!
# Four smaller copies in the grid diagram

Figure 3 in Graph Minors I, page 52, places a smaller diagram in each
corner square. Each square omits its own centre column except at its
root. Thus its occupied vertices avoid both joining crosses, including
the parts of the vertical corridors lying inside that square.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set

/-- Translate one smaller square to a corner of the larger square. -/
def gridDiagramQuadrantMap (a : ℕ) (bottom right : Bool)
    (x : Fin (2 * a + 1) × Fin (2 * a + 1)) :
    Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1) :=
  (⟨(if bottom then 2 * a + 2 else 0) + x.1.val,
      by cases bottom <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩,
   ⟨(if right then 2 * a + 2 else 0) + x.2.val,
      by cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩)

/-- The vertices reserved for a recursive copy in one corner. -/
def gridDiagramQuadrantRegion (a : ℕ) (bottom right : Bool) :
    Set (Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1)) :=
  gridDiagramQuadrantMap a bottom right '' gridDiagramRegion a

/-- The corner translation is injective. -/
theorem gridDiagramQuadrantMap_injective (a : ℕ) (bottom right : Bool) :
    Function.Injective (gridDiagramQuadrantMap a bottom right) := by
  exact grid_translation_injective (if bottom then 2 * a + 2 else 0)
    (if right then 2 * a + 2 else 0)
    (by cases bottom <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)
    (by cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)

/-- Corner translations preserve every grid edge. -/
theorem gridDiagramQuadrantMap_adj {a : ℕ} (bottom right : Bool)
    {x y : Fin (2 * a + 1) × Fin (2 * a + 1)}
    (h : (gridGraph (2 * a + 1)).Adj x y) :
    (gridGraph (2 * (2 * a + 1) + 1)).Adj
      (gridDiagramQuadrantMap a bottom right x) (gridDiagramQuadrantMap a bottom right y) := by
  exact gridGraph_adj_translate (if bottom then 2 * a + 2 else 0)
    (if right then 2 * a + 2 else 0)
    (by cases bottom <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)
    (by cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega) x y h

/-- The omitted centre column of each smaller copy leaves both crosses
free, including the vertical corridor inside the smaller square. -/
theorem gridDiagramSideRegion_disjoint_quadrant (a : ℕ) (side bottom right : Bool) :
    Disjoint (gridDiagramSideRegion a side) (gridDiagramQuadrantRegion a bottom right) := by
  apply Set.disjoint_left.mpr
  rintro v hv ⟨x, hx, rfl⟩
  change x.2.val ≠ a ∨ x.1.val = a at hx
  change
    (((if bottom then 2 * a + 2 else 0) + x.1.val = 2 * a + 1 ∧ _) ∨
      ((if right then 2 * a + 2 else 0) + x.2.val = gridDiagramSideColumn a side ∧ _)) at hv
  rcases hv with ⟨hr, _⟩ | ⟨hc, hr⟩
  · cases bottom <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr <;> omega
  · change a + 1 ≤ (if bottom then 2 * a + 2 else 0) + x.1.val ∧
        (if bottom then 2 * a + 2 else 0) + x.1.val ≤ 3 * a + 1 at hr
    cases side <;> cases bottom <;> cases right <;>
      simp only [gridDiagramSideColumn, Bool.false_eq_true, ↓reduceIte] at hc hr <;> omega

/-- Distinct corner squares are disjoint, hence so are the regions
occupied by their smaller diagrams. -/
theorem gridDiagramQuadrantRegion_disjoint {a : ℕ} {b r b' r' : Bool}
    (hne : (b, r) ≠ (b', r')) :
    Disjoint (gridDiagramQuadrantRegion a b r) (gridDiagramQuadrantRegion a b' r') := by
  apply Set.disjoint_left.mpr
  rintro v ⟨x, _, rfl⟩ ⟨y, _, he⟩
  have hr := congrArg (fun z : Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1) ↦ z.1.val) he
  have hc := congrArg (fun z : Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1) ↦ z.2.val) he
  dsimp only [gridDiagramQuadrantMap] at hr hc
  cases b <;> cases r <;> cases b' <;> cases r' <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hr hc <;>
    first | exact False.elim (hne rfl) | omega

/-- A corner copy stays strictly to its chosen side of the larger
centre column. -/
theorem gridDiagramQuadrantRegion_side {a : ℕ} {b r : Bool}
    {v : Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1)}
    (hv : v ∈ gridDiagramQuadrantRegion a b r) :
    if r then 2 * a + 2 ≤ v.2.val else v.2.val ≤ 2 * a := by
  obtain ⟨x, _, rfl⟩ := hv
  cases r <;> simp only [gridDiagramQuadrantMap, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The corner roots are joined to their side cross by actual single
vertical grid edges. -/
theorem gridDiagramQuadrantRoot_adj_side (a : ℕ) (bottom right : Bool) :
    ∃ x ∈ gridDiagramSideRegion a right,
      (gridGraph (2 * (2 * a + 1) + 1)).Adj x
        (gridDiagramQuadrantMap a bottom right
          (⟨a, by omega⟩, ⟨a, by omega⟩)) := by
  let x : Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1) :=
    (⟨if bottom then 3 * a + 1 else a + 1,
      by cases bottom <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩,
     ⟨gridDiagramSideColumn a right,
      by cases right <;> simp only [gridDiagramSideColumn, Bool.false_eq_true, ↓reduceIte] <;> omega⟩)
  refine ⟨x, Or.inr ⟨rfl, ?_⟩, ?_⟩
  · change a + 1 ≤ (if bottom then 3 * a + 1 else a + 1) ∧
      (if bottom then 3 * a + 1 else a + 1) ≤ 3 * a + 1
    cases bottom <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> omega
  · apply (gridGraph_adj_iff _ _).mpr
    left
    constructor
    · change
        ((if bottom then 3 * a + 1 else a + 1) + 1 =
          (if bottom then 2 * a + 2 else 0) + a) ∨
        ((if bottom then 2 * a + 2 else 0) + a + 1 =
          (if bottom then 3 * a + 1 else a + 1))
      cases bottom <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    · apply Fin.ext
      change gridDiagramSideColumn a right = (if right then 2 * a + 2 else 0) + a
      cases right <;> simp only [gridDiagramSideColumn, Bool.false_eq_true, ↓reduceIte] <;> omega

end GraphMinor.GM01
