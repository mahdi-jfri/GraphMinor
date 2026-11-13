module

public import GraphMinor.GM05.ShadowMinor

/-!
# Vertex bags for graphs with loops and parallel edges

The edge condition is stated for each actual edge. A loop is covered by any
bag containing its vertex. Every other edge gives an adjacency of the simple
shadow. Thus exactly the same bags decompose the graph and its shadow.
The same argument removes loops from the condition for a vertex separation.
-/

@[expose] public section
namespace GraphMinor.GM05.Full
open Graph Set
variable {α β ι : Type*}

/-- The vertex-bag definition of Graph Minors V, Section 1, pages 92–93,
for arbitrary graphs. Each edge, including a loop, has its ends in one bag. -/
structure IsTreeDecomposition [Fintype ι] (G : Graph α β)
    (T : SimpleGraph ι) (χ : ι → Set α) : Prop where
  isTree : T.IsTree
  iUnion_eq : (⋃ t, χ t) = V(G)
  edge_mem : ∀ ⦃e x y⦄, G.IsLink e x y → ∃ t, x ∈ χ t ∧ y ∈ χ t
  inter_subset : ∀ ⦃t t' t''⦄, GM10.OnTreePath T t t'' t' → χ t ∩ χ t'' ⊆ χ t'

/-- The same vertex bags decompose a graph and its simple shadow. -/
theorem isTreeDecomposition_iff [Fintype ι] {G : Graph α β}
    {T : SimpleGraph ι} {χ : ι → Set α} :
    IsTreeDecomposition G T χ ↔ GM05.IsTreeDecomposition (simpleShadow G) T χ := by
  constructor
  · intro h
    refine ⟨h.isTree, h.iUnion_eq, ?_, h.inter_subset⟩
    rintro x y ⟨_, e, he⟩
    exact h.edge_mem he
  · intro h
    refine ⟨h.isTree, h.iUnion_eq, ?_, h.inter_subset⟩
    intro e x y he
    by_cases hxy : x = y
    · subst y
      have hx : x ∈ ⋃ t, χ t := h.iUnion_eq.symm ▸ he.left_mem
      obtain ⟨t, ht⟩ := mem_iUnion.mp hx
      exact ⟨t, ht, ht⟩
    · exact h.adj_mem ⟨hxy, e, he⟩

/-- Graph Minors V, Section 1, page 93: a tree-decomposition of width at
most `w`, with natural-number width as in V. -/
def TreeWidthLE (G : Graph α β) (w : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (χ : ι → Set α),
    IsTreeDecomposition G T χ ∧ GM05.WidthLE χ w

/-- Graph Minors V, Section 1, page 93: the minimum nonnegative width. -/
noncomputable def treeWidth (G : Graph α β) : ℕ :=
  sInf {w | TreeWidthLE G w}

/-- Loops and parallel edges do not change the possible widths. -/
theorem treeWidthLE_iff {G : Graph α β} {w : ℕ} :
    TreeWidthLE G w ↔ GM05.TreeWidthLE (simpleShadow G) w := by
  unfold TreeWidthLE GM05.TreeWidthLE
  simp only [isTreeDecomposition_iff]

/-- A graph and its simple shadow have the same tree-width. -/
theorem treeWidth_eq (G : Graph α β) :
    treeWidth G = GM05.treeWidth (simpleShadow G) := by
  unfold treeWidth GM05.treeWidth
  congr 1
  ext w
  exact treeWidthLE_iff

/-- Graph Minors V, Section 1, page 94: a vertex separation, using
adjacency in the original graph, including loops. -/
structure IsSeparation (G : Graph α β) (A B : Set α) : Prop where
  subset_left : A ⊆ V(G)
  subset_right : B ⊆ V(G)
  union_eq : A ∪ B = V(G)
  not_adj : ∀ ⦃x y⦄, x ∈ A \ B → y ∈ B \ A → ¬ G.Adj x y

/-- A loop cannot cross the two sides of a vertex separation. -/
theorem isSeparation_iff {G : Graph α β} {A B : Set α} :
    IsSeparation G A B ↔ GM05.IsSeparation (simpleShadow G) A B := by
  constructor
  · intro h
    exact ⟨h.subset_left, h.subset_right, h.union_eq,
      fun _ _ hx hy hadj => h.not_adj hx hy hadj.2⟩
  · intro h
    refine ⟨h.subset_left, h.subset_right, h.union_eq, ?_⟩
    intro x y hx hy hadj
    exact h.not_adj hx hy ⟨fun heq => hx.2 (heq ▸ hy.1), hadj⟩

end GraphMinor.GM05.Full
