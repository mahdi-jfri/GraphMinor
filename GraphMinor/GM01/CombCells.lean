module

public import GraphMinor.GM01.CombSpineCuts
public import GraphMinor.Minor.Model
import GraphMinor.GM01.Basic

/-!
# Connected cells on the comb spine

For the arbitrary-root tail argument in Graph Minors I, (4.1), page 55,
the spine vertex assigned to the root is joined to it inside one cell.
A cell consists of one spine vertex and its attached binary copy. Follow
binary parent edges toward the empty word, then the attachment edge.
These paths remain in the cell and prove that its induced graph is
connected.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- One spine vertex together with its binary copy in the page-55 comb. -/
def combCell (γ δ : ℕ) (i : Fin δ) : Set (PathCombVertex δ) :=
  {x | x ∈ (pathComb γ δ).verts ∧ pathCombSpineIndex x = i}

/-- The spine vertex belongs to its own cell. -/
theorem combCell_spine_mem (γ δ : ℕ) (i : Fin δ) : Sum.inl i ∈ combCell γ δ i :=
  ⟨pathComb_spine_mem γ δ i, rfl⟩

/-- A binary vertex reaches its spine vertex using only its assigned cell. -/
theorem combCell_binary_reachable_spine {γ δ : ℕ} (i : Fin δ)
    (word : List Bool) (hw : word.length < γ) :
    Relation.ReflTransGen ((toGraph (pathComb γ δ)).induce (combCell γ δ i)).Adj
      (Sum.inr (i, word)) (Sum.inl i) := by
  induction word with
  | nil =>
    apply Relation.ReflTransGen.single
    refine ⟨s(Sum.inr (i, []), Sum.inl i), ?_⟩
    exact ⟨⟨rfl, ⟨rfl, rfl, hw⟩⟩, ⟨hw, rfl⟩, combCell_spine_mem γ δ i⟩
  | cons bit word ih =>
    have hw' : word.length < γ := by simp only [List.length_cons] at hw; omega
    have hedge : ((toGraph (pathComb γ δ)).induce (combCell γ δ i)).Adj
        (Sum.inr (i, bit :: word)) (Sum.inr (i, word)) := by
      refine ⟨s(Sum.inr (i, bit :: word), Sum.inr (i, word)), ?_⟩
      exact ⟨⟨rfl, ⟨rfl, hw, hw', Or.inr ⟨bit, rfl⟩⟩⟩, ⟨hw, rfl⟩, ⟨hw', rfl⟩⟩
    exact (Relation.ReflTransGen.single hedge).trans (ih hw')

/-- Every cell induces a connected graph, including when no binary copy
is attached at height zero. -/
theorem combCell_connected (γ δ : ℕ) (i : Fin δ) :
    GraphConnected ((toGraph (pathComb γ δ)).induce (combCell γ δ i)) := by
  have htoSpine : ∀ x ∈ combCell γ δ i,
      Relation.ReflTransGen ((toGraph (pathComb γ δ)).induce (combCell γ δ i)).Adj x (Sum.inl i) := by
    intro x hx
    rcases hx with ⟨hx, hindex⟩
    cases x with
    | inl j =>
      change j = i at hindex
      subst j
      exact .refl
    | inr p =>
      rcases p with ⟨j, word⟩
      change j = i at hindex
      subst j
      exact combCell_binary_reachable_spine i word hx
  exact ⟨⟨Sum.inl i, combCell_spine_mem γ δ i⟩, fun x hx y hy ↦
    (htoSpine x hx).trans (Std.Symm.symm _ _ (htoSpine y hy))⟩

end GraphMinor.GM01
