module

public import GraphMinor.GM01.Defs
public import GraphMinor.GM01.PathIndexIntervals
import Lean.Elab.Tactic.Omega

/-!
# Coordinates for the recursive grid diagram

In the diagram proving Graph Minors I, (3.2), pages 51–52, copies of
smaller diagrams sit in four squares. Translating both coordinates
preserves their edges. Horizontal and vertical intervals provide the
paths joining their roots to the centre of the larger diagram.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The grid adjacency rule in zero-based coordinates. -/
theorem gridGraph_adj_iff {n : ℕ} (x y : Fin n × Fin n) :
    (gridGraph n).Adj x y ↔
      ((x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val) ∧ x.2 = y.2) ∨
      ((x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val) ∧ x.1 = y.1) := by
  simp only [gridGraph, Graph.ofSimpleGraph_adj_iff, boxProd_adj, pathGraph_adj]

/-- Translating a smaller square into a larger one preserves grid edges,
as used for the four copies in Figure 3 on page 52. -/
theorem gridGraph_adj_translate {m n : ℕ} (r c : ℕ)
    (hr : r + m ≤ n) (hc : c + m ≤ n) (x y : Fin m × Fin m)
    (hxy : (gridGraph m).Adj x y) :
    (gridGraph n).Adj
      (⟨r + x.1.val, by omega⟩, ⟨c + x.2.val, by omega⟩)
      (⟨r + y.1.val, by omega⟩, ⟨c + y.2.val, by omega⟩) := by
  apply (gridGraph_adj_iff _ _).mpr
  dsimp only
  rcases (gridGraph_adj_iff x y).mp hxy with ⟨h, he⟩ | ⟨h, he⟩
  · left
    refine ⟨?_, ?_⟩
    · rcases h with h | h
      · left; omega
      · right; omega
    · apply Fin.ext
      exact congrArg (fun a : Fin m ↦ c + a.val) he
  · right
    refine ⟨?_, ?_⟩
    · rcases h with h | h
      · left; omega
      · right; omega
    · apply Fin.ext
      exact congrArg (fun a : Fin m ↦ r + a.val) he

/-- The coordinate translation used for a smaller square is injective. -/
theorem grid_translation_injective {m n : ℕ} (r c : ℕ)
    (hr : r + m ≤ n) (hc : c + m ≤ n) :
    Function.Injective (fun x : Fin m × Fin m ↦
      ((⟨r + x.1.val, by omega⟩ : Fin n),
       (⟨c + x.2.val, by omega⟩ : Fin n))) := by
  intro x y h
  have hrow := congrArg (fun z : Fin n × Fin n ↦ z.1.val) h
  have hcol := congrArg (fun z : Fin n × Fin n ↦ z.2.val) h
  apply Prod.ext <;> apply Fin.ext <;> dsimp only at hrow hcol ⊢ <;> omega

/-- Squares on opposite sides of the middle row have disjoint vertices.
The gap of one row is reserved for the joining paths in Figure 3. -/
theorem grid_quadrants_disjoint_rows {m : ℕ} (c d : ℕ)
    (hc : c + m ≤ 2 * m + 1) (hd : d + m ≤ 2 * m + 1) :
    Disjoint
      (Set.range (fun x : Fin m × Fin m ↦
        ((⟨x.1.val, by omega⟩ : Fin (2 * m + 1)),
         (⟨c + x.2.val, by omega⟩ : Fin (2 * m + 1)))))
      (Set.range (fun x : Fin m × Fin m ↦
        ((⟨m + 1 + x.1.val, by omega⟩ : Fin (2 * m + 1)),
         (⟨d + x.2.val, by omega⟩ : Fin (2 * m + 1))))) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, he⟩
  have h := congrArg (fun z : Fin (2 * m + 1) × Fin (2 * m + 1) ↦ z.1.val) he
  dsimp only at h
  omega

/-- Squares on opposite sides of the middle column have disjoint vertices. -/
theorem grid_quadrants_disjoint_columns {m : ℕ} (r s : ℕ)
    (hr : r + m ≤ 2 * m + 1) (hs : s + m ≤ 2 * m + 1) :
    Disjoint
      (Set.range (fun x : Fin m × Fin m ↦
        ((⟨r + x.1.val, by omega⟩ : Fin (2 * m + 1)),
         (⟨x.2.val, by omega⟩ : Fin (2 * m + 1)))))
      (Set.range (fun x : Fin m × Fin m ↦
        ((⟨s + x.1.val, by omega⟩ : Fin (2 * m + 1)),
         (⟨m + 1 + x.2.val, by omega⟩ : Fin (2 * m + 1))))) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, he⟩
  have h := congrArg (fun z : Fin (2 * m + 1) × Fin (2 * m + 1) ↦ z.2.val) he
  dsimp only at h
  omega

/-- Every nonempty horizontal interval of the grid is connected. -/
theorem gridGraph_horizontal_interval_connected {n : ℕ}
    (row lo hi : Fin n) (h : lo ≤ hi) :
    GraphConnected ((gridGraph n).induce
      ((fun col : Fin n ↦ (row, col)) '' Icc lo hi)) := by
  apply graphConnected_induce_index_interval _ _ lo hi h
  intro i j hij
  exact (gridGraph_adj_iff _ _).mpr (Or.inr ⟨Or.inl (by dsimp only; omega), rfl⟩)

/-- Every nonempty vertical interval of the grid is connected. -/
theorem gridGraph_vertical_interval_connected {n : ℕ}
    (col lo hi : Fin n) (h : lo ≤ hi) :
    GraphConnected ((gridGraph n).induce
      ((fun row : Fin n ↦ (row, col)) '' Icc lo hi)) := by
  apply graphConnected_induce_index_interval _ _ lo hi h
  intro i j hij
  exact (gridGraph_adj_iff _ _).mpr (Or.inl ⟨Or.inl (by dsimp only; omega), rfl⟩)

end GraphMinor.GM01
