module

public import GraphMinor.GM02.TreeDecomposition
public import GraphMinor.GM02.Feasibility
public import Mathlib.Combinatorics.Graph.Simple

/-!
# The terminated graph of Graph Minors II, page 319, and (4.4)

To decide whether `G` topologically contains `H`, page 319 of Graph Minors II
turns the question into a question about disjoint paths. It enumerates the
edges of `H` as `e₁, …, e_k`, and gives `eᵢ` ends `uᵢ, vᵢ`. Then it replaces
each vertex of `H` by new vertices: one vertex `sᵢ` for each edge `eᵢ` at its
end `uᵢ`, and one vertex `tᵢ` at its end `vᵢ`. The other vertices of `G` stay.
The map `g` sends each new vertex back to the vertex of `G` it stands for.
Two vertices are adjacent in the new simple graph `G'` when their images under
`g` are adjacent in `G`. The pairs to join are the pairs `(sᵢ, tᵢ)`.

We use the vertex type `α ⊕ (Fin k × Bool)`. The vertex `Sum.inl y` is the old
vertex `y`, while `Sum.inr (i, false)` is `sᵢ` and `Sum.inr (i, true)` is `tᵢ`.

The paper proves (4.4) in one sentence: deleting the `2k` new vertices of `G'`
leaves a subgraph of `G`. We follow this. Take a tree-decomposition of `G`,
remove the vertices of `H` from every bag, and add all `2k` new vertices to
every bag. Each bag grows by at most `2k`.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Classical

universe u v

variable {α : Type u} {β : Type v}

/-- The ends `uᵢ, vᵢ` of the edge `eᵢ` of `H`, Graph Minors II, page 318. The
paper does not say which end is `uᵢ`, so we choose one. -/
noncomputable def splitEnds (H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) (i : Fin k) :
    α × α :=
  ((H.exists_isLink_of_mem_edgeSet (edge i).2).choose,
    (H.exists_isLink_of_mem_edgeSet (edge i).2).choose_spec.choose)

theorem splitEnds_isLink (H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) (i : Fin k) :
    H.IsLink (edge i) (splitEnds H edge i).1 (splitEnds H edge i).2 :=
  (H.exists_isLink_of_mem_edgeSet (edge i).2).choose_spec.choose_spec

/-- The vertex `sᵢ` of Graph Minors II, page 319. -/
def splitS {k : ℕ} (i : Fin k) : α ⊕ (Fin k × Bool) := Sum.inr (i, false)

/-- The vertex `tᵢ` of Graph Minors II, page 319. -/
def splitT {k : ℕ} (i : Fin k) : α ⊕ (Fin k × Bool) := Sum.inr (i, true)

/-- The map `g` of Graph Minors II, page 319. It is the identity on `Y`, and it
sends `sᵢ` to `uᵢ` and `tᵢ` to `vᵢ`. -/
noncomputable def splitMap (H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) :
    α ⊕ (Fin k × Bool) → α
  | Sum.inl y => y
  | Sum.inr (i, false) => (splitEnds H edge i).1
  | Sum.inr (i, true) => (splitEnds H edge i).2

/-- The vertex set `X ∪ Y` of `G'`, where `Y = V(G) - V(H)` and `X` is the set of
the `2k` new vertices. -/
def splitVertexSet (G H : Graph α β) (k : ℕ) : Set (α ⊕ (Fin k × Bool)) :=
  Sum.inl '' (V(G) \ V(H)) ∪ range Sum.inr

/-- The adjacency of `G'`, Graph Minors II, page 319: "distinct
$a, b \in X \cup Y$ are adjacent if and only if $g(a), g(b)$ are adjacent in $G$". -/
def splitSimpleGraph (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) :
    SimpleGraph (α ⊕ (Fin k × Bool)) where
  Adj a b := a ≠ b ∧ G.Adj (splitMap H edge a) (splitMap H edge b)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The simple graph `G'` of Graph Minors II, page 319: "Define a simple graph
$G'$ with a vertex set $X \cup Y$, in which distinct $a, b \in X \cup Y$ are adjacent
if and only if $g(a), g(b)$ are adjacent in $G$." -/
noncomputable def splitGraph (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) :
    Graph (α ⊕ (Fin k × Bool)) (Sym2 (α ⊕ (Fin k × Bool))) :=
  (Graph.ofSimpleGraph (splitSimpleGraph G H edge)).induce (splitVertexSet G H k)

theorem splitGraph_vertexSet (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) :
    V(splitGraph G H edge) = splitVertexSet G H k := rfl

theorem splitGraph_adj_iff (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H))
    (a b : α ⊕ (Fin k × Bool)) :
    (splitGraph G H edge).Adj a b ↔ a ∈ splitVertexSet G H k ∧ b ∈ splitVertexSet G H k ∧
      a ≠ b ∧ G.Adj (splitMap H edge a) (splitMap H edge b) := by
  constructor
  · rintro ⟨e, he, ha, hb⟩
    exact ⟨ha, hb, (Graph.ofSimpleGraph_adj_iff a b).1 ⟨e, he⟩⟩
  · rintro ⟨ha, hb, hab⟩
    obtain ⟨e, he⟩ := (Graph.ofSimpleGraph_adj_iff (G := splitSimpleGraph G H edge) a b).2 hab
    exact ⟨e, he, ha, hb⟩

theorem splitVertexSet_finite (G H : Graph α β) (k : ℕ) (hV : V(G).Finite) :
    (splitVertexSet G H k).Finite :=
  ((hV.sdiff).image _).union (Set.finite_range _)

theorem splitGraph_vertexSet_finite (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H))
    (hV : V(G).Finite) : V(splitGraph G H edge).Finite :=
  splitVertexSet_finite G H k hV

theorem splitGraph_edgeSet_finite (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H))
    (hV : V(G).Finite) : E(splitGraph G H edge).Finite := by
  have hX := splitVertexSet_finite G H k hV
  apply (hX.image2 Sym2.mk hX).subset
  intro e he
  obtain ⟨a, b, hab⟩ := (splitGraph G H edge).exists_isLink_of_mem_edgeSet he
  exact ⟨a, hab.2.1, b, hab.2.2, hab.1.1.symm⟩

/-- The termination `𝒜 = {(sᵢ, tᵢ) : 1 ≤ i ≤ k}` of Graph Minors II, page 319. -/
noncomputable def splitTermination (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) :
    Termination V(splitGraph G H edge) where
  pairs := Finset.univ.image fun i => s(splitS i, splitT i)
  not_diag := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    simp [splitS, splitT]
  vertex_mem := by
    intro p hp w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    rcases Sym2.mem_iff.1 hw with rfl | rfl
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  disjoint := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
    have hij : i ≠ j := fun h => hpq (h ▸ rfl)
    rw [Set.disjoint_left]
    intro w hw hw'
    simp only [Set.mem_ofPred_eq, Sym2.mem_iff, splitS, splitT] at hw hw'
    rcases hw with rfl | rfl <;> rcases hw' with h | h <;> simp_all

/-! ### (4.4) -/

private theorem inl_mem_bag {k : ℕ} {S : Set α} {y : α} :
    (Sum.inl y : α ⊕ (Fin k × Bool)) ∈ Sum.inl '' S ∪ range Sum.inr ↔ y ∈ S := by
  constructor
  · rintro (⟨z, hz, h⟩ | ⟨_, h⟩)
    · rwa [← Sum.inl_injective h]
    · exact (Sum.inr_ne_inl h).elim
  · intro hy
    exact Or.inl ⟨y, hy, rfl⟩

private theorem ncard_bag_le {k : ℕ} (S : Set α) :
    (Sum.inl '' S ∪ range (Sum.inr : Fin k × Bool → α ⊕ (Fin k × Bool))).ncard ≤
      S.ncard + 2 * k := by
  refine (Set.ncard_union_le _ _).trans ?_
  rw [Set.ncard_image_of_injective _ Sum.inl_injective]
  have hr : (range (Sum.inr : Fin k × Bool → α ⊕ (Fin k × Bool))).ncard = 2 * k := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      Nat.mul_comm]
  rw [hr]

/-- Graph Minors II, (4.4), page 319:
"*$G'$ has tree-width at most $2k$ more than the tree-width of $G$.*"

The paper's reason: "we may obtain a subgraph of $G$ by deleting $2k$ vertices of
$G'$". From a tree-decomposition of `G` we remove the vertices of `H` from
each bag and add the `2k` new vertices to each bag. The hypotheses before (4.4)
on loops and on `V(H) ⊆ V(G)` are not needed. -/
theorem theorem_4_4_proof (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) (hV : V(G).Finite)
    (hE : E(G).Finite) :
    treeWidth (splitGraph G H edge) (splitGraph_vertexSet_finite G H edge hV)
      (splitGraph_edgeSet_finite G H edge hV) ≤ treeWidth G hV hE + 2 * k := by
  rw [treeWidth_le_iff]
  obtain ⟨ι, hι, T, X, hD, hw⟩ := (treeWidth_le_iff G hV hE _).1 le_rfl
  have hne : Nonempty ι := hD.isTree.connected.nonempty
  have hXV : ∀ i, X i ⊆ V(G) := fun i => hD.iUnion_eq ▸ Set.subset_iUnion X i
  let X' : ι → Set (α ⊕ (Fin k × Bool)) := fun i => Sum.inl '' (X i \ V(H)) ∪ range Sum.inr
  have hinr : ∀ i p, (Sum.inr p : α ⊕ (Fin k × Bool)) ∈ X' i := fun _ p => Or.inr ⟨p, rfl⟩
  have hcover : ∀ a ∈ splitVertexSet G H k, ∃ i, a ∈ X' i := by
    rintro a (⟨y, ⟨hyG, hyH⟩, rfl⟩ | ⟨p, rfl⟩)
    · rw [← hD.iUnion_eq] at hyG
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyG
      exact ⟨i, inl_mem_bag.2 ⟨hi, hyH⟩⟩
    · exact ⟨Classical.arbitrary ι, hinr _ p⟩
  refine ⟨ι, hι, T, X', ⟨hD.isTree, ?_, ?_, ?_⟩, ?_⟩
  · apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun i => ?_
      rintro a (⟨y, ⟨hy, hyH⟩, rfl⟩ | ⟨p, rfl⟩)
      · exact Or.inl ⟨y, ⟨hXV i hy, hyH⟩, rfl⟩
      · exact Or.inr ⟨p, rfl⟩
    · intro a ha
      obtain ⟨i, hi⟩ := hcover a ha
      exact Set.mem_iUnion.2 ⟨i, hi⟩
  · intro e a b hab
    have hadj : (splitGraph G H edge).Adj a b := ⟨e, hab⟩
    obtain ⟨ha, hb, -, hG⟩ := (splitGraph_adj_iff G H edge a b).1 hadj
    rcases a with y | p
    · rcases b with z | q
      · obtain ⟨c, hc⟩ := hG
        obtain ⟨i, hyi, hzi⟩ := hD.edge_mem hc
        have hyH : y ∉ V(H) := by
          rcases ha with ⟨y', hy', h⟩ | ⟨_, h⟩
          · rw [← Sum.inl_injective h]
            exact hy'.2
          · exact (Sum.inr_ne_inl h).elim
        have hzH : z ∉ V(H) := by
          rcases hb with ⟨z', hz', h⟩ | ⟨_, h⟩
          · rw [← Sum.inl_injective h]
            exact hz'.2
          · exact (Sum.inr_ne_inl h).elim
        exact ⟨i, inl_mem_bag.2 ⟨hyi, hyH⟩, inl_mem_bag.2 ⟨hzi, hzH⟩⟩
      · obtain ⟨i, hi⟩ := hcover _ ha
        exact ⟨i, hi, hinr i q⟩
    · obtain ⟨i, hi⟩ := hcover _ hb
      exact ⟨i, hinr i p, hi⟩
  · intro i j l hp a ⟨hai, hal⟩
    rcases a with y | p
    · rw [inl_mem_bag] at hai hal ⊢
      exact ⟨hD.inter_subset hp ⟨hai.1, hal.1⟩, hai.2⟩
    · exact hinr j p
  · intro i
    refine (ncard_bag_le (X i \ V(H))).trans ?_
    have h1 : (X i \ V(H)).ncard ≤ (X i).ncard :=
      Set.ncard_le_ncard Set.sdiff_subset (hV.subset (hXV i))
    have h2 := hw i
    omega

end GraphMinor.GM02
