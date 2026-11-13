module

public import GraphMinor.GM01.NestedSeparators
import GraphMinor.GM01.FiniteTransitions

/-!
# Layers between ordered separators

Graph Minors I, (1.7), pages 41–42, assigns each vertex to the layer
where the ordered separators stop cutting it off from the root. The
first and last layers have just one test. Nesting of separation and the
unique finite transition prove that these layers partition the graph.
The order hypothesis also places each separator in its own layer.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph

/-- The sets `W_0,...,W_T` in GM01 (1.7), page 41. At layer `k`, the
preceding separator cuts off the vertex and the next separator does
not. At the two boundary layers the missing test is vacuous. -/
def separatorLayer {α β : Type*} {T : ℕ} (G : Graph α β) (root : α)
    (Y : Fin T → Set α) (k : Fin (T + 1)) : Set α :=
  {x | x ∈ V(G) ∧
    (∀ i : Fin T, i.val + 1 = k.val → GraphSeparates G (Y i) {x} {root}) ∧
    (∀ i : Fin T, i.val = k.val → ¬ GraphSeparates G (Y i) {x} {root})}

/-- The local layer tests are equivalent to separation by exactly the
earlier separators. This makes explicit the nesting argument in the
proof of GM01 (1.7), pages 41–42. -/
theorem mem_separatorLayer_iff {α β : Type*} {T : ℕ} {G : Graph α β} {root : α}
    (Y : Fin T → Set α)
    (horder : ∀ i j, ∀ y ∈ Y j,
      GraphSeparates G (Y i) {y} {root} ↔ i ≤ j)
    (k : Fin (T + 1)) (x : α) :
    x ∈ separatorLayer G root Y k ↔ x ∈ V(G) ∧
      ∀ i, GraphSeparates G (Y i) {x} {root} ↔ i.val < k.val := by
  exact and_congr_right fun _ ↦ fin_transition_iff _
    (fun i j hij h ↦ ordered_separator_separation_mono Y horder hij h) k

/-- Each vertex belongs to exactly one layer, as proved in GM01 (1.7),
pages 41–42, by the unique transition in its separation predicates. -/
theorem exists_unique_separatorLayer {α β : Type*} {T : ℕ} {G : Graph α β} {root : α}
    (Y : Fin T → Set α)
    (horder : ∀ i j, ∀ y ∈ Y j,
      GraphSeparates G (Y i) {y} {root} ↔ i ≤ j)
    {x : α} (hx : x ∈ V(G)) : ∃! k, x ∈ separatorLayer G root Y k := by
  obtain ⟨k, hk, huniq⟩ := exists_unique_fin_transition
    (fun i ↦ GraphSeparates G (Y i) {x} {root})
    (fun i j hij h ↦ ordered_separator_separation_mono Y horder hij h)
  exact ⟨k, ⟨hx, hk⟩, fun j hj ↦ huniq j hj.2⟩

/-- The partition assertion of GM01 (1.7), pages 41–42. -/
theorem separatorLayer_partition {α β : Type*} {T : ℕ} {G : Graph α β} {root : α}
    (Y : Fin T → Set α)
    (horder : ∀ i j, ∀ y ∈ Y j,
      GraphSeparates G (Y i) {y} {root} ↔ i ≤ j) :
    Pairwise (fun i j ↦ Disjoint (separatorLayer G root Y i) (separatorLayer G root Y j)) ∧
      (⋃ k, separatorLayer G root Y k) = V(G) := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨k, hk, huniq⟩ := exists_unique_separatorLayer Y horder hxi.1
    exact hij ((huniq i hxi).trans (huniq j hxj).symm)
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      exact hk.1
    · intro x hx
      obtain ⟨k, hk, _⟩ := exists_unique_separatorLayer Y horder hx
      exact Set.mem_iUnion.mpr ⟨k, hk⟩

/-- The containment `Y_i ⊆ W_i` in GM01 (1.7), page 41. Separator
indices start at zero, so the corresponding layer index is its successor. -/
theorem separator_subset_layer {α β : Type*} {T : ℕ} {G : Graph α β} {root : α}
    (Y : Fin T → Set α) (hYG : ∀ i, Y i ⊆ V(G))
    (horder : ∀ i j, ∀ y ∈ Y j,
      GraphSeparates G (Y i) {y} {root} ↔ i ≤ j) (i : Fin T) :
    Y i ⊆ separatorLayer G root Y ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
  intro x hx
  apply (mem_separatorLayer_iff Y horder _ x).mpr
  refine ⟨hYG i hx, ?_⟩
  intro j
  exact (horder j i x hx).trans (by change j.val ≤ i.val ↔ j.val < i.val + 1; omega)

end GraphMinor.GM01
