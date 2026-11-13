module

public import GraphMinor.GM16.Defs
import GraphMinor.GM09.Basic

/-!
# Combining the vertex extensions in XVI (1.3)

The last step on page 52 combines the deletion of the exceptional
vertices with the vertex extension supplied by (2.3). Deleting two
sets in succession deletes their union, whose size is at most the sum
of their sizes.
-/

public section
namespace GraphMinor.GM16
open Set Graph GM09
universe u v

/-- Deleting two vertex sets in succession deletes their union. -/
theorem deleteVertices_deleteVertices_eq {α : Type u} {β : Type v}
    (G : Graph α β) (X Y : Set α) :
    deleteVertices (deleteVertices G X) Y = deleteVertices G (X ∪ Y) := by
  have hX : deleteVertices G X ≤ G := G.induce_le sdiff_subset
  have hXY : deleteVertices (deleteVertices G X) Y ≤ G :=
    ((deleteVertices G X).induce_le sdiff_subset).trans hX
  have hUnion : deleteVertices G (X ∪ Y) ≤ G := G.induce_le sdiff_subset
  refine (Compatible.of_le_le hXY hUnion).ext ?_ ?_
  · ext x
    change (x ∈ (V(G) \ X) \ Y) ↔ x ∈ V(G) \ (X ∪ Y)
    simp only [mem_sdiff, mem_union, not_or]
    tauto
  · ext e
    change (∃ x y, (deleteVertices G X).IsLink e x y ∧
      x ∈ V(deleteVertices G X) \ Y ∧ y ∈ V(deleteVertices G X) \ Y) ↔
      ∃ x y, G.IsLink e x y ∧ x ∈ V(G) \ (X ∪ Y) ∧ y ∈ V(G) \ (X ∪ Y)
    constructor
    · rintro ⟨x, y, hxy, hx, hy⟩
      exact ⟨x, y, hxy.1, ⟨hx.1.1, fun h => h.elim hx.1.2 hx.2⟩,
        ⟨hy.1.1, fun h => h.elim hy.1.2 hy.2⟩⟩
    · rintro ⟨x, y, hxy, hx, hy⟩
      have hxX : x ∈ V(G) \ X := ⟨hx.1, fun h => hx.2 (Or.inl h)⟩
      have hyX : y ∈ V(G) \ X := ⟨hy.1, fun h => hy.2 (Or.inl h)⟩
      exact ⟨x, y, ⟨hxy, hxX, hyX⟩, ⟨hxX, fun h => hx.2 (Or.inr h)⟩,
        ⟨hyX, fun h => hy.2 (Or.inr h)⟩⟩

/-- If `deleteVertices G Z = H` with `Z ⊆ V(G)` and `Z.ncard ≤ n`, then `G` is a `(≤ n)`-vertex
extension of `H`. -/
theorem isVertexExtension_of_deleteVertices_eq {α : Type u} {β : Type v}
    {n : ℕ} {G H : Graph α β} {Z : Set α}
    (hZ : Z ⊆ V(G)) (hcard : Z.ncard ≤ n) (heq : deleteVertices G Z = H) :
    IsVertexExtension n G H :=
  ⟨Z, hZ, hcard, heq⟩

/-- Vertex-extension bounds add. -/
theorem IsVertexExtension.trans {α : Type u} {β : Type v}
    {G H J : Graph α β} {n m : ℕ}
    (hGH : IsVertexExtension n G H) (hHJ : IsVertexExtension m H J) :
    IsVertexExtension (n + m) G J := by
  obtain ⟨X, hX, hXn, rfl⟩ := hGH
  obtain ⟨Y, hY, hYm, rfl⟩ := hHJ
  have hle₁ : deleteVertices G X ≤ G := G.induce_le sdiff_subset
  refine ⟨X ∪ Y, union_subset hX (hY.trans hle₁.vertexSet_mono), ?_, ?_⟩
  · exact (ncard_union_le X Y).trans (Nat.add_le_add hXn hYm)
  · exact (deleteVertices_deleteVertices_eq G X Y).symm

/-- Increasing the allowed number of deleted vertices preserves a vertex extension. -/
theorem IsVertexExtension.mono {α : Type u} {β : Type v}
    {G H : Graph α β} {n m : ℕ} (h : IsVertexExtension n G H) (hnm : n ≤ m) :
    IsVertexExtension m G H := by
  obtain ⟨X, hX, hcard, hdel⟩ := h
  exact ⟨X, hX, hcard.trans hnm, hdel⟩

/-- Loose vertex-extension bounds add. This combines the two extensions
in the proof of XVI (1.3), page 52. -/
theorem IsLooseVertexExtension.trans {α : Type u} {β : Type v}
    {G H J : Graph α β} {n m : ℕ}
    (hGH : IsLooseVertexExtension n G H) (hHJ : IsLooseVertexExtension m H J) :
    IsLooseVertexExtension (n + m) G J := by
  obtain ⟨X, hX, hXn, hle₁, hdel₁⟩ := hGH
  obtain ⟨Y, hY, hYm, hle₂, hdel₂⟩ := hHJ
  refine ⟨X ∪ Y, union_subset hX (hY.trans hle₁.vertexSet_mono), ?_, hle₂.trans hle₁, ?_⟩
  · exact (ncard_union_le X Y).trans (Nat.add_le_add hXn hYm)
  · calc deleteVertices G (X ∪ Y)
      _ = deleteVertices (deleteVertices G X) Y := (deleteVertices_deleteVertices_eq G X Y).symm
      _ = deleteVertices (deleteVertices H X) Y := by rw [hdel₁]
      _ = deleteVertices H (X ∪ Y) := deleteVertices_deleteVertices_eq H X Y
      _ = deleteVertices H (Y ∪ X) := by rw [union_comm]
      _ = deleteVertices (deleteVertices H Y) X := (deleteVertices_deleteVertices_eq H Y X).symm
      _ = deleteVertices (deleteVertices J Y) X := by rw [hdel₂]
      _ = deleteVertices J (Y ∪ X) := deleteVertices_deleteVertices_eq J Y X
      _ = deleteVertices J (X ∪ Y) := by rw [union_comm]

/-- Increasing the allowed number of deleted vertices preserves a loose vertex extension. -/
theorem IsLooseVertexExtension.mono {α : Type u} {β : Type v}
    {G H : Graph α β} {n m : ℕ} (h : IsLooseVertexExtension n G H) (hnm : n ≤ m) :
    IsLooseVertexExtension m G H := by
  obtain ⟨X, hX, hcard, hle, hdel⟩ := h
  exact ⟨X, hX, hcard.trans hnm, hle, hdel⟩

end GraphMinor.GM16
