module

public import GraphMinor.GM01.SeparatorLayerEdges
public import GraphMinor.GM01.PathWidth

/-!
# The path decomposition given by ordered separators

Graph Minors I, (1.7), pages 41–42, adds the next separator to each
layer. Every edge either stays in one layer or has its later end in
that next separator. A vertex occurs only at its own layer and possibly
the preceding index, so the bags satisfy the interval condition.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph

/-- The sequence `W_0 ∪ Y_1,...,W_{T-1} ∪ Y_T,W_T` in GM01 (1.7),
page 41. Separator indices start at zero. -/
def separatorLayerBag {α β : Type*} {T : ℕ} (G : Graph α β) (root : α)
    (Y : Fin T → Set α) (k : Fin (T + 1)) : Set α :=
  separatorLayer G root Y k ∪ ⋃ i : Fin T, ⋃ (_ : i.val = k.val), Y i

/-- The actual path decomposition asserted by GM01 (1.7), pages 41–42.
The partition and the placement of separators have already been proved. -/
noncomputable def separatorLayerDecomposition {α β : Type*} {T : ℕ} {G : Graph α β}
    {root : α} (Y : Fin T → Set α) (hYG : ∀ i, Y i ⊆ V(G))
    (horder : ∀ i j, ∀ y ∈ Y j,
      GraphSeparates G (Y i) {y} {root} ↔ i ≤ j) : PathDecomposition G := by
  classical
  have huniq : ∀ {x}, x ∈ V(G) → ∃! k, x ∈ separatorLayer G root Y k :=
    fun hx ↦ exists_unique_separatorLayer Y horder hx
  have hindex : ∀ {x} {a b : Fin (T + 1)}, x ∈ separatorLayer G root Y a →
      x ∈ separatorLayerBag G root Y b → a.val = b.val ∨ a.val = b.val + 1 := by
    intro x a b hxa hxb
    obtain ⟨k, hk, hkuniq⟩ := huniq hxa.1
    rcases hxb with hxb | hxb
    · have hab : a = b := (hkuniq a hxa).trans (hkuniq b hxb).symm
      exact Or.inl (congrArg Fin.val hab)
    · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxb
      have hxnext := separator_subset_layer Y hYG horder i hxi
      have hanext := (hkuniq a hxa).trans (hkuniq _ hxnext).symm
      have hv : a.val = i.val + 1 := congrArg Fin.val hanext
      exact Or.inr (hv.trans (congrArg (fun z : ℕ ↦ z + 1) hi))
  have hedge : ∀ {u v} (e : β), G.IsLink e u v →
      ∀ i j : Fin (T + 1), i ≤ j → u ∈ separatorLayer G root Y i →
      v ∈ separatorLayer G root Y j →
      u ∈ separatorLayerBag G root Y i ∧ v ∈ separatorLayerBag G root Y i := by
    intro u v e he i j hij hui hvj
    refine ⟨Or.inl hui, ?_⟩
    by_cases hij' : i = j
    · exact Or.inl (hij'.symm ▸ hvj)
    have hiltj : i.val < j.val := by have hne := Fin.val_injective.ne hij'; omega
    let a : Fin T := ⟨i.val, by have hjT := j.isLt; omega⟩
    have huNot : ¬ GraphSeparates G (Y a) {u} {root} := by
      intro h
      have hi := ((mem_separatorLayer_iff Y horder i u).mp hui).2 a |>.mp h
      change i.val < i.val at hi
      exact Nat.lt_irrefl _ hi
    have hvSep : GraphSeparates G (Y a) {v} {root} :=
      (((mem_separatorLayer_iff Y horder j v).mp hvj).2 a).mpr hiltj
    have hvY : v ∈ Y a := mem_separator_of_adj ⟨e, he⟩ hvSep huNot
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨a, rfl, hvY⟩)
  refine ⟨T + 1, separatorLayerBag G root Y, ?_, ?_, ?_⟩
  · intro i x hx
    rcases hx with hx | hx
    · exact hx.1
    · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      exact hYG j hxj
  · intro e u v he
    obtain ⟨i, hui, _⟩ := huniq he.left_mem
    obtain ⟨j, hvj, _⟩ := huniq he.right_mem
    rcases le_total i j with hij | hji
    · exact ⟨i, hedge e he i j hij hui hvj⟩
    · have h := hedge e he.symm j i hji hvj hui
      exact ⟨j, h.2, h.1⟩
  · intro i j k hij hjk x hx
    have hxG : x ∈ V(G) := by
      rcases hx.1 with h | h
      · exact h.1
      · obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp h
        exact hYG a hxa
    obtain ⟨a, hxa, _⟩ := huniq hxG
    have hi := hindex hxa hx.1
    have hk := hindex hxa hx.2
    have hji : j = i ∨ j = k := by
      have hijv : i.val ≤ j.val := hij
      have hjkv : j.val ≤ k.val := hjk
      have hv : j.val = i.val ∨ j.val = k.val := by omega
      exact hv.imp Fin.ext Fin.ext
    rcases hji with rfl | rfl
    · exact hx.1
    · exact hx.2

/-- Graph Minors I, (1.7), pages 41–42.
"Let $\rho$ be a vertex of a graph $G$, and let $Y_1, Y_2, ..., Y_T$ be disjoint subsets of $V(G)$, where $T \ge 1$. Suppose that for $1 < i, i' \le T$, and for all $y \in Y_{i'}$, $Y_i$ separates $y$ and $\rho$ if and only if $i \le i'$. For $1 \le i < T$, let $W_i$ be the set of all vertices of $G$ separated from $\rho$ by $Y_i$, and not separated from $\rho$ by $Y_{i+1}$. Let $W_0$ be the set of vertices not separated from $\rho$ by $Y_1$, and let $W_T$ be the set of all vertices separated from $\rho$ by $Y_T$. Then the sets $W_0, W_1, ..., W_T$ are disjoint and partition $V(G)$, and $Y_i \subseteq W_i$ ($1 \le i \le T$), and the sequence"

The print has "$1 < i, i' \le T$", a misprint for $1 \le i, i' \le T$: as printed, nothing is
assumed about $Y_1$ and the result is false. The Lean assumes the condition for all
$1 \le i, i' \le T$. See the correction to (1.7) in `corrections/GM01.md`.

The final existential specifies both the length and the exact bag
sequence. Heterogeneous equality allows the sequence indices to be
identified by the stated equality of lengths. -/
theorem theorem_1_7_proof {α β : Type*} {T : ℕ} {G : Graph α β} {root : α}
    (_hroot : root ∈ V(G)) (_hT : 1 ≤ T)
    (Y : Fin T → Set α) (hYG : ∀ i, Y i ⊆ V(G))
    (_hdis : Pairwise (fun i j ↦ Disjoint (Y i) (Y j)))
    (horder : ∀ i j, ∀ y ∈ Y j,
      GraphSeparates G (Y i) {y} {root} ↔ i ≤ j) :
    Pairwise (fun i j ↦ Disjoint (separatorLayer G root Y i) (separatorLayer G root Y j)) ∧
      (⋃ k, separatorLayer G root Y k) = V(G) ∧
      (∀ i : Fin T, Y i ⊆ separatorLayer G root Y ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) ∧
      ∃ D : PathDecomposition G, D.length = T + 1 ∧
        HEq D.bag (separatorLayerBag G root Y) := by
  have hpart := separatorLayer_partition Y horder
  exact ⟨hpart.1, hpart.2, separator_subset_layer Y hYG horder,
    separatorLayerDecomposition Y hYG horder, rfl, HEq.rfl⟩

end GraphMinor.GM01
