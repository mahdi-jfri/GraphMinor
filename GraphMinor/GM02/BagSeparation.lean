module

public import GraphMinor.GM02.TreeDecomposition
public import GraphMinor.GM10.SubmodularBasic
import GraphMinor.GM10.TreeWidthBasic

/-!
# Adjacent bags give a separation in Graph Minors II

For II (2.4), a vertex in bags on opposite sides of a tree edge belongs
to both endpoint bags, by (W3). If two vertices outside that intersection
are equal or adjacent, (W1) or (W2) gives a common bag, contradicting this
fact on one of the two sides. A walk avoiding the intersection therefore
cannot pass from one side to the other.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set SimpleGraph
universe u v w

/-- Graph Minors II, Section 2, page 311: `X` separates `Y` and `Y'` when
no vertices of the two sets outside `X` can be joined after deleting `X`. -/
def Separates {α : Type u} {β : Type v} (G : Graph α β) (X Y Y' : Set α) : Prop :=
  ∀ a ∈ Y, ∀ b ∈ Y', a ∈ V(G) \ X → b ∈ V(G) \ X →
    ¬ Relation.ReflTransGen (G.induce (V(G) \ X)).Adj a b

private theorem separates_of_cover_of_no_cross {α : Type u} {β : Type v}
    {G : Graph α β} {X Y Y' : Set α}
    (hcover : ∀ a ∈ V(G) \ X, a ∈ Y ∨ a ∈ Y')
    (hcross : ∀ a ∈ Y, ∀ b ∈ Y', a ∈ V(G) \ X → b ∈ V(G) \ X →
      ¬ (a = b ∨ G.Adj a b)) : Separates G X Y Y' := by
  have hstay : ∀ {a b}, Relation.ReflTransGen (G.induce (V(G) \ X)).Adj a b →
      a ∈ Y → b ∈ Y := by
    intro a b h
    induction h with
    | refl => exact fun ha => ha
    | @tail b c _ hbc ih =>
      intro ha
      obtain ⟨e, he⟩ := hbc
      have hb : b ∈ V(G) \ X := he.left_mem
      have hc : c ∈ V(G) \ X := he.right_mem
      rcases hcover c hc with hcY | hcY'
      · exact hcY
      · exact (hcross b (ih ha) c hcY' hb hc (Or.inr ⟨e, he.1⟩)).elim
  intro a ha b hb _ hbX hpath
  exact hcross b (hstay hpath ha) b hb hbX hbX (Or.inl rfl)

/-- A vertex in bags on opposite sides of a tree edge lies in both endpoint bags. -/
theorem mem_bag_inter_of_opposite_bags
    {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) {j j' a b : ι} (hjj' : T.Adj j j')
    (ha : a ∈ GM10.treeComponent T j s(j, j'))
    (hb : b ∈ GM10.treeComponent T j' s(j', j))
    {v : α} (hv : v ∈ X a ∩ X b) : v ∈ X j ∩ X j' := by
  have hpj := GM10.onTreePath_of_mem_treeComponent hD.isTree hjj' ha hb
  have hpj' := GM10.onTreePath_of_mem_treeComponent hD.isTree hjj'.symm hb ha
  exact ⟨hD.inter_subset hpj hv,
    hD.inter_subset (GM10.onTreePath_comm.2 hpj') hv⟩

/-- Graph Minors II, (2.4), page 312:
"Let $e$ be an edge of $T$ with ends $j, j'$ say, and $N, N'$ be the vertex
sets of the two components of $T \setminus e$. Then $X_j \cap X_{j'}$
separates $\bigcup(X_i : i \in N)$ and $\bigcup(X_i : i \in N')$."

Here the two components are identified by the ends they contain. By (W1)
and (W2), an equal or adjacent pair across them has a common bag. The tree
paths to this bag force one member of the pair into the intersection by
(W3), as in the paper's proof. -/
theorem theorem_2_4_proof {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) {j j' : ι} (hjj' : T.Adj j j') :
    Separates G (X j ∩ X j')
      (⋃ i ∈ GM10.treeComponent T j s(j, j'), X i)
      (⋃ i ∈ GM10.treeComponent T j' s(j', j), X i) := by
  classical
  apply separates_of_cover_of_no_cross
  · intro v hv
    have hcover : v ∈ ⋃ i, X i := hD.iUnion_eq ▸ hv.1
    obtain ⟨i, hvi⟩ := Set.mem_iUnion.1 hcover
    by_cases hi : i ∈ GM10.treeComponent T j s(j, j')
    · exact Or.inl (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hvi⟩⟩)
    · have hi' := (GM10.notMem_treeComponent_iff hD.isTree hjj').1 hi
      exact Or.inr (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi', hvi⟩⟩)
  · intro v hv v' hv' hvX hvX' hpair
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hv
    obtain ⟨hi, hvi⟩ := Set.mem_iUnion.1 hi
    obtain ⟨i', hi'⟩ := Set.mem_iUnion.1 hv'
    obtain ⟨hi', hvi'⟩ := Set.mem_iUnion.1 hi'
    have hcommon : ∃ k, v ∈ X k ∧ v' ∈ X k := by
      rcases hpair with h | ⟨e, he⟩
      · exact ⟨i, hvi, h ▸ hvi⟩
      · exact hD.edge_mem he
    obtain ⟨k, hvk, hvk'⟩ := hcommon
    by_cases hk : k ∈ GM10.treeComponent T j s(j, j')
    · have hcut := mem_bag_inter_of_opposite_bags hD hjj'.symm hi' hk ⟨hvi', hvk'⟩
      exact hvX'.2 ⟨hcut.2, hcut.1⟩
    · have hk' := (GM10.notMem_treeComponent_iff hD.isTree hjj').1 hk
      exact hvX.2 (mem_bag_inter_of_opposite_bags hD hjj' hi hk' ⟨hvi, hvk⟩)

end GraphMinor.GM02
