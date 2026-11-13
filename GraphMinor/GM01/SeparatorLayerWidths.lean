module

public import GraphMinor.GM01.SeparatorLayerDecomposition
public import GraphMinor.GM01.PathWidthGluing
import GraphMinor.GM01.PathWidthMaps

/-!
# Gluing the width bounds of ordered separator layers

On page 57, Graph Minors I applies (1.6) to the decomposition from
(1.7). Consecutive bags meet only in the intervening separator.
Deleting all other bags leaves a subgraph of the chosen layer.
Thus a common width bound for the layers increases by at most twice
the separator bound when the layers are glued.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Consecutive layer bags meet only in their intervening separator,
as used on page 57 of GM01. -/
theorem separatorLayerBag_inter_subset {α β : Type*} {T : ℕ} {G : Graph α β} {root : α}
    (Y : Fin T → Set α) (hYG : ∀ i, Y i ⊆ V(G))
    (horder : ∀ i j, ∀ y ∈ Y j, GraphSeparates G (Y i) {y} {root} ↔ i ≤ j)
    (i j : Fin (T + 1)) (hji : j.val = i.val + 1) :
    separatorLayerBag G root Y i ∩ separatorLayerBag G root Y j ⊆
      Y ⟨i.val, by have := j.isLt; omega⟩ := by
  have hpart := (separatorLayer_partition Y horder).1
  intro x hx
  rcases hx.1 with hxW | hxY
  · rcases hx.2 with hxW' | hxY'
    · have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
      exact False.elim (Set.disjoint_left.mp (hpart hne) hxW hxW')
    · obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hxY'
      have hxNext := separator_subset_layer Y hYG horder a hxa
      have hne : i ≠ (⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩ : Fin (T + 1)) := by
        intro h
        have hv := congrArg Fin.val h
        change i.val = a.val + 1 at hv
        omega
      exact False.elim (Set.disjoint_left.mp (hpart hne) hxW hxNext)
  · obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hxY
    have heq : a = ⟨i.val, by have := j.isLt; omega⟩ := Fin.ext ha
    exact heq ▸ hxa

/-- The exclusive graph in (1.6) is a subgraph of its separator
layer in the application on page 57 of GM01. -/
theorem separatorLayer_exclusive_subgraph {α β : Type*} {T : ℕ} {G : Graph α β} {root : α}
    (Y : Fin T → Set α) (hYG : ∀ i, Y i ⊆ V(G))
    (horder : ∀ i j, ∀ y ∈ Y j, GraphSeparates G (Y i) {y} {root} ↔ i ≤ j)
    (i : Fin (T + 1)) :
    G.deleteVerts ((separatorLayerDecomposition Y hYG horder).otherBags i) ≤
      G.induce (separatorLayer G root Y i) := by
  let D := separatorLayerDecomposition Y hYG horder
  have hVertices : V(G.deleteVerts (D.otherBags i)) ⊆ separatorLayer G root Y i := by
    intro x hx
    rw [G.vertexSet_deleteVerts] at hx
    obtain ⟨a, hxa, _⟩ := exists_unique_separatorLayer Y horder hx.1
    by_cases hai : a = i
    · exact hai ▸ hxa
    · have hxOther : x ∈ D.otherBags i := Set.mem_iUnion₂.mpr ⟨a, hai, Or.inl hxa⟩
      exact False.elim (hx.2 hxOther)
  refine ⟨hVertices, ?_⟩
  intro e x y he
  exact ⟨((G.deleteVerts_isLink (D.otherBags i)).1 he).1,
    hVertices he.left_mem, hVertices he.right_mem⟩

/-- The width gluing step on page 57 of GM01, from proved (1.6)
and the actual layer decomposition (1.7). -/
theorem hasPathWidthLE_of_separator_layers {α β : Type*} {T : ℕ} {G : Graph α β}
    (hfin : V(G).Finite) {root : α} (Y : Fin T → Set α) (hYG : ∀ i, Y i ⊆ V(G))
    (horder : ∀ i j, ∀ y ∈ Y j, GraphSeparates G (Y i) {y} {root} ↔ i ≤ j)
    {k p : ℕ} (hcard : ∀ i, (Y i).ncard ≤ k)
    (hwidth : ∀ i : Fin (T + 1), HasPathWidthLE (G.induce (separatorLayer G root Y i)) p) :
    HasPathWidthLE G (p + 2 * k) := by
  apply theorem_1_6_proof hfin (separatorLayerDecomposition Y hYG horder)
  · intro i j hji
    let a : Fin T := ⟨i.val, by have hjT : j.val < T + 1 := j.isLt; omega⟩
    exact (Set.ncard_le_ncard (separatorLayerBag_inter_subset Y hYG horder i j hji)
      (hfin.subset (hYG a))).trans (hcard a)
  · intro i
    exact (hwidth i).of_le (separatorLayer_exclusive_subgraph Y hYG horder i)

end GraphMinor.GM01
