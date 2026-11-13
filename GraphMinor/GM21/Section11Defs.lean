module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM10.Defs2
public import GraphMinor.Thomas.Basic

/-!
# Graph Minors XXI, Sections 11 and 12: definitions

The definitions of Sections 1, 11 and 12 of N. Robertson and P. D. Seymour, *Graph Minors. XXI.
Graphs with unique linkages*, J. Combin. Theory Ser. B 99 (2009), 583–616, that the results of
Sections 11 and 12 use.

* `IsTreeDecomp21`: a tree-decomposition as defined on page 1 of the preprint. Unlike Graph Minors X
  (`GM10.IsTreeDecomposition`), two bags may share edges.
* `TreeWidthLE21`: tree-width at most `w`, as on page 1 of the preprint.
* `treeEdgeSet T W u v`: the set `W(e)` of page 43 for the edge `e = uv` of `T`.
* `IsLinkedTreeDecomp`: a linked tree-decomposition (page 43).
* `IsIntertwining` and `graphRank`: intertwinings and the rank of a graph (page 43).
* `IsPathTree`, `PathWidthLE21`: path-decompositions and path-width (page 47).
* `IsPathSystem`: a set of `k` mutually vertex-disjoint paths between two vertex sets, written as
  the linkage formed by their union, as in (2.6).
* `IsChain`: a `p`-chain (page 52).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Hypergraph GraphMinor.GM10

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}

/-! ## Tree-decompositions (page 1 of the preprint) -/

/-- Graph Minors XXI, Section 1 (page 1 of the preprint):
"A *tree-decomposition* of a graph $G$ is a pair $(T, W)$, where $T$ is a tree and
$W = (W_t : t \in V(T))$ is a family of subgraphs of $G$, satisfying
1. $\bigcup(W_t : t \in V(T)) = G$, and
2. if $t, t', t'' \in V(T)$ and $t'$ lies on the path of $T$ between $t$ and $t''$, then
$W_t \cap W_{t''} \subseteq W_{t'}$." -/
structure IsTreeDecomp21 [Fintype ι] (G : Hypergraph α β) (T : SimpleGraph ι)
    (W : ι → Hypergraph α β) : Prop where
  /-- `T` is a tree. -/
  isTree : T.IsTree
  /-- Each `W t` is a subgraph of `G`. -/
  le : ∀ t, W t ≤ G
  /-- 1. `⋃ (W t : t ∈ V(T)) = G`. -/
  biUnion_eq : Hypergraph.biUnion Finset.univ W = G
  /-- 2. If `t'` lies on the path of `T` between `t` and `t''`, then `W t ∩ W t'' ⊆ W t'`. -/
  inter_le : ∀ ⦃t t' t'' : ι⦄, OnTreePath T t t'' t' → W t ∩ W t'' ≤ W t'

/-- Graph Minors XXI, Section 1 (page 1 of the preprint): "It has width $\le w$ if
$|V(W_t)| \le w + 1$ for every $t \in V(T)$, and $G$ has *tree-width* $\le w$ if some
tree-decomposition has width $\le w$." -/
def TreeWidthLE21 (G : Hypergraph α β) (w : ℕ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (T : SimpleGraph κ) (W : κ → Hypergraph α β),
    IsTreeDecomp21 G T W ∧ ∀ t, (W t).vertexSet.ncard ≤ w + 1

/-! ## Linked tree-decompositions (page 43) -/

/-- Graph Minors XXI, Section 11 (page 43 of the preprint): "If $e$ is an edge of $T$, and
$T_1, T_2$ are the two components of $T \setminus e$ and $t_i$ is the end of $e$ in $T_i$
($i = 1, 2$), then $(W(T_1), W(T_2))$ is a separation of $G$ and
$W(T_1) \cap W(T_2) = W(t_1) \cap W(t_2)$. We define $W(e) = V(W(T_1) \cap W(T_2))$."

For the edge `e = uv`, the components of `T \ e` are those of `u` and `v`, and `W(T_i)` is the union
of the bags over a component (`GM10.treeDecompSide`). -/
noncomputable def treeEdgeSet [Fintype ι] (T : SimpleGraph ι) (W : ι → Hypergraph α β)
    (u v : ι) : Set α :=
  (treeDecompSide T W s(u, v) u ∩ treeDecompSide T W s(u, v) v).vertexSet

/-- Graph Minors XXI, Section 11 (page 43 of the preprint): "We say that a tree-decomposition
$(T, W)$ of $G$ is *linked* if for all $e_1, e_2 \in E(T)$ such that $|W(e_1)| = |W(e_2)| = k$
say, and $|W(e)| \ge k$ for all edges $e$ of the path of $T$ between $e_1$ and $e_2$, there are
$k$ mutually vertex-disjoint paths of $G$ between $W(e_1)$ and $W(e_2)$."

The edges are `e₁ = a₁b₁` and `e₂ = a₂b₂`, named so that the path of `T` from `a₁` to `b₂` passes
through `b₁` and `a₂`. This path is the path of `T` between `e₁` and `e₂`: its first edge is `e₁`
and its last edge is `e₂`. Every two edges can be named in this way. -/
def IsLinkedTreeDecomp [Fintype ι] (G : Hypergraph α β) (T : SimpleGraph ι)
    (W : ι → Hypergraph α β) : Prop :=
  ∀ ⦃a₁ b₁ a₂ b₂ : ι⦄, T.Adj a₁ b₁ → T.Adj a₂ b₂ →
    OnTreePath T a₁ b₂ b₁ → OnTreePath T a₁ b₂ a₂ → ∀ k : ℕ,
    (treeEdgeSet T W a₁ b₁).ncard = k → (treeEdgeSet T W a₂ b₂).ncard = k →
    (∀ ⦃s s' : ι⦄, Thomas.OnTreePathEdge T a₁ b₂ s s' → k ≤ (treeEdgeSet T W s s').ncard) →
    HasDisjointPaths G.skeleton (treeEdgeSet T W a₁ b₁) (treeEdgeSet T W a₂ b₂) k

/-! ## Intertwinings and rank (page 43) -/

/-- Graph Minors XXI, Section 11 (page 43 of the preprint): "Let $L_1$ and $L_2$ be linkages in
a graph $G$. We say that $G$ is an *intertwining* of $L_1$ and $L_2$ if $L'_1 \cup L'_2 = G$ for all
linkages $L'_1, L'_2$ in $G$ such that $L'_i$ has the same pattern as $L_i$ ($i = 1, 2$)." -/
def IsIntertwining (G L₁ L₂ : Hypergraph α β) : Prop :=
  ∀ L₁' L₂' : Hypergraph α β, IsLinkage G L₁' → IsLinkage G L₂' →
    linkagePattern L₁' = linkagePattern L₁ → linkagePattern L₂' = linkagePattern L₂ →
    L₁' ∪ L₂' = G

/-- The number `κ(G)` of components of `G` (page 43). -/
noncomputable def numComponents (G : Hypergraph α β) : ℕ :=
  {C : Hypergraph α β | IsComponentOf G C}.ncard

/-- Graph Minors XXI, Section 11 (page 43 of the preprint): "Let us say a graph $G$ has
*rank* $|E(G)| - |V(G)| + \kappa(G)$, where $\kappa(G)$ denotes the number of components of
$G$." -/
noncomputable def graphRank (G : Hypergraph α β) : ℤ :=
  (G.edgeSet.ncard : ℤ) - G.vertexSet.ncard + numComponents G

/-! ## Path-decompositions (page 47) -/

/-- `T` is a path: a tree in which every vertex has degree at most `2`. -/
def IsPathTree (T : SimpleGraph ι) : Prop :=
  T.IsTree ∧ ∀ t, (T.neighborSet t).ncard ≤ 2

/-- Graph Minors XXI, Section 12 (page 47 of the preprint): "We recall that a
*path-decomposition* of $G$ is a tree-decomposition $(T, W)$ of $G$ such that $T$ is a path, and
the *path-width* of $G$ is the minimum width of all path-decompositions of $G$."
This says that the path-width of `G` is at most `w`. -/
def PathWidthLE21 (G : Hypergraph α β) (w : ℕ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (P : SimpleGraph κ) (W : κ → Hypergraph α β),
    IsTreeDecomp21 G P W ∧ IsPathTree P ∧ ∀ t, (W t).vertexSet.ncard ≤ w + 1

/-! ## Sets of disjoint paths and chains (pages 47 and 52) -/

/-- `M` is the union of a set of `k` mutually vertex-disjoint paths of `H` between `Y` and `Z`: a
linkage in `H` with `k` components, each with one end in `Y` and the other in `Z`, as in (2.6).
A component with one vertex is a path between `Y` and `Z` when its vertex is in `Y ∩ Z`. -/
def IsPathSystem (H : Hypergraph α β) (Y Z : Set α) (k : ℕ) (M : Hypergraph α β) : Prop :=
  IsLinkage H M ∧ (linkagePattern M).ncard = k ∧
    ∀ P ∈ linkagePattern M, ∃ y ∈ Y, ∃ z ∈ Z, P = {y, z}

/-- Graph Minors XXI, Section 12 (page 52 of the preprint): "Let us say that a graph $G$ is a
$p$-chain if there exist $Y, Z \subseteq V(G)$ with $|Y| = |Z| \le p$, such that there is a unique
set of $|X|$ mutually vertex-disjoint paths of $G$ between $Y$ and $Z$, and every vertex of $G$
belongs to one of these paths. (Note that $Y \cap Z$ may be nonempty.)"

The paper's `|X|` is a misprint for `|Y|` (see the correction to the definition of a $p$-chain in
`corrections/GM21.md`). -/
def IsChain (G : Hypergraph α β) (p : ℕ) : Prop :=
  ∃ Y Z : Set α, Y ⊆ G.vertexSet ∧ Z ⊆ G.vertexSet ∧ Y.ncard = Z.ncard ∧ Y.ncard ≤ p ∧
    ∃ M : Hypergraph α β, IsPathSystem G Y Z Y.ncard M ∧
      (∀ M' : Hypergraph α β, IsPathSystem G Y Z Y.ncard M' → M' = M) ∧
      M.vertexSet = G.vertexSet

end GM21
end GraphMinor
