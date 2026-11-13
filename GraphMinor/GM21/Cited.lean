module

public import GraphMinor.Hypergraph.Basic
public import GraphMinor.GM10.Defs

/-!
# Graph Minors XXI: Cited Results

This file states Theorem (6.1) of Graph Minors XIII (*The Disjoint Paths Problem*,
J. Combin. Theory Ser. B 63 (1995), 65–110), which is cited in Section 10 (page 42 of the preprint)
of Graph Minors XXI to prove (10.3).

To stay close to the paper, (6.1) of XIII is stated in XIII's own terminology
over directed graphs (`Digraph`), rooted digraphs, models, `δ`-folios, and irrelevant vertices
(Graph Minors XIII, Section 1, pages 68–69, and Section 6, pages 83–84).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Hypergraph

universe u v

/-- A finite directed graph (digraph) in the sense of Graph Minors XIII, Section 1 (page 68):
it has a finite vertex set `vertexSet`, a finite edge set `edgeSet`, and each edge `e ∈ edgeSet`
has a tail `tail e ∈ vertexSet` and a head `head e ∈ vertexSet` (loops and parallel edges are
allowed). -/
structure Digraph (α : Type u) (β : Type v) where
  vertexSet : Set α
  edgeSet : Set β
  vertexSet_finite : vertexSet.Finite
  edgeSet_finite : edgeSet.Finite
  tail : β → α
  head : β → α
  tail_mem : ∀ e ∈ edgeSet, tail e ∈ vertexSet
  head_mem : ∀ e ∈ edgeSet, head e ∈ vertexSet

/-- A digraph `G` is finite if both `V(G)` and `E(G)` are finite. -/
structure Digraph.IsFinite {α : Type u} {β : Type v} (G : Digraph α β) : Prop where
  finite_V : G.vertexSet.Finite
  finite_E : G.edgeSet.Finite

/-- The underlying hypergraph (graph) of a digraph `G`. -/
def Digraph.toHypergraph {α : Type u} {β : Type v} (G : Digraph α β) : Hypergraph α β where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet
  Inc e v := e ∈ G.edgeSet ∧ (v = G.tail e ∨ v = G.head e)
  vertex_mem_of_inc := by
    rintro e v ⟨he, rfl | rfl⟩
    · exact G.tail_mem e he
    · exact G.head_mem e he
  edge_mem_of_inc := fun _ _ h => h.1
  vertexSet_finite := G.vertexSet_finite
  edgeSet_finite := G.edgeSet_finite

/-- A subdigraph `H` of `G` is a non-null connected subdigraph of `G` if `H ≤ G.toHypergraph`,
`H.vertexSet.Nonempty`, and `H.skeleton` is connected on `H.vertexSet`. -/
structure Digraph.IsConnectedSubgraph {α : Type u} {β : Type v}
    (G : Digraph α β) (H : Hypergraph α β) : Prop where
  le_toHypergraph : H ≤ G.toHypergraph
  nonempty : H.vertexSet.Nonempty
  connected : ∀ x ∈ H.vertexSet, ∀ y ∈ H.vertexSet, H.skeleton.Reachable x y

/-- Graph Minors XIII, Section 1 (page 68):
"Let $G, H$ be both graphs or both digraphs. A *model* $\phi$ of $H$ in $G$ assigns to each edge
$e$ of $H$ an edge $\phi(e)$ of $G$, and to each vertex $v$ of $H$ a non-null connected subgraph
$\phi(v)$ of $G$, such that
(i) the graphs $\phi(v)$ ($v \in V(H)$) are mutually vertex-disjoint, the edges $\phi(e)$ ($e \in E(H)$) are all distinct, and for $v \in V(H)$ and $e \in E(H)$, $\phi(e) \notin E(\phi(v))$
(ii) for $e \in E(H)$, if $e$ has head $u$ and tail $v$ (or, in the undirected case, has ends $u, v$) then $\phi(e)$ has a head in $V(\phi(u))$ and a tail in $V(\phi(v))$ (respectively, $\phi(e)$ has one end in $V(\phi(u))$ and the other in $V(\phi(v))$)." -/
structure IsDigraphModel {α₁ : Type u} {β₁ : Type v} {α₂ : Type u} {β₂ : Type v}
    (G : Digraph α₁ β₁) (H : Digraph α₂ β₂)
    (φV : α₂ → Hypergraph α₁ β₁) (φE : β₂ → β₁) : Prop where
  vert_conn : ∀ v ∈ H.vertexSet, G.IsConnectedSubgraph (φV v)
  vert_disjoint : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
    Disjoint (φV u).vertexSet (φV v).vertexSet
  edge_mem : ∀ e ∈ H.edgeSet, φE e ∈ G.edgeSet
  edge_inj : ∀ e₁ ∈ H.edgeSet, ∀ e₂ ∈ H.edgeSet, φE e₁ = φE e₂ → e₁ = e₂
  edge_not_in_vert : ∀ e ∈ H.edgeSet, ∀ v ∈ H.vertexSet, φE e ∉ (φV v).edgeSet
  tail_mem : ∀ e ∈ H.edgeSet, G.tail (φE e) ∈ (φV (H.tail e)).vertexSet
  head_mem : ∀ e ∈ H.edgeSet, G.head (φE e) ∈ (φV (H.head e)).vertexSet

/-- Graph Minors XIII, Section 1 (page 68):
"Thus, let us say that $(G, v_1, \dots, v_k)$ is a *rooted digraph* if $G$ is a digraph and
$v_1, \dots, v_k \in V(G)$ (not necessarily distinct)." -/
structure RootedDigraph (α : Type u) (β : Type v) (k : ℕ) where
  G : Digraph α β
  roots : Fin k → α
  roots_mem : ∀ i : Fin k, roots i ∈ G.vertexSet

/-- Graph Minors XIII, Section 1 (page 68):
"Let $(G, v_1, \dots, v_k)$, $(H, u_1, \dots, u_k)$ be rooted digraphs. A *model* of the second
in the first is a model $\phi$ of $H$ in $G$ such that $v_i \in V(\phi(u_i))$ ($1 \le i \le k$),
and if there is such a model, we say that $(H, u_1, \dots, u_k)$ is a minor of
$(G, v_1, \dots, v_k)$." -/
structure IsRootedDigraphMinor {α₁ : Type u} {β₁ : Type v} {α₂ : Type u} {β₂ : Type v} {k : ℕ}
    (RG : RootedDigraph α₁ β₁ k) (RH : RootedDigraph α₂ β₂ k) : Prop where
  exists_model :
    ∃ (φV : α₂ → Hypergraph α₁ β₁) (φE : β₂ → β₁),
      IsDigraphModel RG.G RH.G φV φE ∧
      ∀ i : Fin k, RG.roots i ∈ (φV (RH.roots i)).vertexSet

/-- Graph Minors XIII, Section 1 (page 68):
"If $\delta \ge 0$ is an integer, we say that $(H, u_1, \dots, u_k)$ has *detail* $\le \delta$ if
$|E(H)| \le \delta$ and $|V(H) - \{u_1, \dots, u_k\}| \le \delta$. The $\delta$-*folio* of
$(G, v_1, \dots, v_k)$ is the set of all minors of $(G, v_1, \dots, v_k)$ with detail $\le \delta$." -/
structure HasDetailLe {α : Type u} {β : Type v} {k : ℕ}
    (RH : RootedDigraph α β k) (δ : ℕ) : Prop where
  edge_le : RH.G.edgeSet.ncard ≤ δ
  nonroot_vert_le : (RH.G.vertexSet \ range RH.roots).ncard ≤ δ

/-- The `G \ v` operation on a digraph `G` removes `v` and all edges incident with `v`. -/
def Digraph.deleteVertex {α : Type u} {β : Type v} (G : Digraph α β) (v : α) : Digraph α β where
  vertexSet := G.vertexSet \ {v}
  edgeSet := {e ∈ G.edgeSet | G.tail e ≠ v ∧ G.head e ≠ v}
  vertexSet_finite := G.vertexSet_finite.sdiff
  edgeSet_finite := G.edgeSet_finite.subset (fun _ he => he.1)
  tail := G.tail
  head := G.head
  tail_mem e he := ⟨G.tail_mem e he.1, he.2.1⟩
  head_mem e he := ⟨G.head_mem e he.1, he.2.2⟩

/-- Graph Minors XIII, Section 1 (page 69):
"Thus, if $Z \subseteq V(G)$, by the $\delta$-folio of $G$ relative to $Z$ we mean the
$\delta$-folio of $(G, v_1, \dots, v_k)$ for any choice of $v_1, \dots, v_k$ with $k = |Z|$ and
$Z = \{v_1, \dots, v_k\}$."
"For $Z \subseteq V(G)$, a vertex $v$ of $G$ is *irrelevant (to the $\delta$-folio of $G$
relative to $Z$)* if $v \notin Z$ and the $\delta$-folios of $G$ and $G \setminus v$ relative to
$Z$ are equal." -/
structure IsIrrelevantToDigraphFolio {α : Type u} {β : Type v}
    (G : Digraph α β) (Z : Set α) (δ : ℕ) (v : α) : Prop where
  Z_sub : Z ⊆ G.vertexSet
  v_mem : v ∈ G.vertexSet
  v_not_mem_Z : v ∉ Z
  folio_eq :
    ∀ (k : ℕ) (roots : Fin k → α)
      (hG_roots : ∀ i : Fin k, roots i ∈ G.vertexSet)
      (hGv_roots : ∀ i : Fin k, roots i ∈ (G.deleteVertex v).vertexSet),
      k = Z.ncard → range roots = Z →
      ∀ (RH : RootedDigraph α β k),
        HasDetailLe RH δ →
        (IsRootedDigraphMinor ⟨G, roots, hG_roots⟩ RH ↔
         IsRootedDigraphMinor ⟨G.deleteVertex v, roots, hGv_roots⟩ RH)

/-- Graph Minors XIII, Section 6, Theorem (6.1) (pages 83–84):
"(6.1) *Let $G$ be a digraph and let $Z \subseteq V(G)$ with $|Z| \le \xi$. Let
$k = \lfloor \frac{5}{2}\xi \rfloor + 3\delta + 1$ and let $G_1, \dots, G_k$ be mutually
vertex-disjoint connected subgraphs of $G$ such that for $1 \le i < j \le k$ there is an edge of
$G$ between $G_i$ and $G_j$. Let $(A, B)$ be a separation of $G$ such that*
*(i) $A \cap G_i$ is null for some $i$ ($1 \le i \le k$)*
*(ii) $Z \subseteq V(A)$* ...
*(iii) subject to (i) and (ii), $(A, B)$ has minimum order*
*(iv) subject to (i), (ii), and (iii), $A$ is maximal.*
*Let $v \in V(B) - V(A)$. Then $v$ is irrelevant to the $\delta$-folio of $G$ relative to $Z$.*" -/
def GM13Theorem61Statement : Prop :=
  ∀ {α : Type u} {β : Type v} [Nonempty β] (G : Digraph α β) (Z : Set α) (ξ δ : ℕ),
    G.IsFinite →
    Z ⊆ G.vertexSet → Z.ncard ≤ ξ →
    let k : ℕ := (5 * ξ) / 2 + 3 * δ + 1
    ∀ (SubG : Fin k → Hypergraph α β),
      (∀ i : Fin k, G.IsConnectedSubgraph (SubG i)) →
      (∀ i j : Fin k, i ≠ j → Disjoint (SubG i).vertexSet (SubG j).vertexSet) →
      (∀ i j : Fin k, i < j →
        ∃ e ∈ G.edgeSet,
          ((G.tail e ∈ (SubG i).vertexSet ∧ G.head e ∈ (SubG j).vertexSet) ∨
           (G.tail e ∈ (SubG j).vertexSet ∧ G.head e ∈ (SubG i).vertexSet))) →
      ∀ (A B : Hypergraph α β),
        G.toHypergraph.IsSeparation A B →
        -- (i) A ∩ G_i is null for some i (1 ≤ i ≤ k)
        (∃ i : Fin k, Disjoint A.vertexSet (SubG i).vertexSet) →
        -- (ii) Z ⊆ V(A)
        Z ⊆ A.vertexSet →
        -- (iii) subject to (i) and (ii), (A, B) has minimum order
        (∀ A' B' : Hypergraph α β,
          G.toHypergraph.IsSeparation A' B' →
          (∃ i : Fin k, Disjoint A'.vertexSet (SubG i).vertexSet) →
          Z ⊆ A'.vertexSet →
          separationOrder A B ≤ separationOrder A' B') →
        -- (iv) subject to (i), (ii), and (iii), A is maximal
        (∀ A' B' : Hypergraph α β,
          G.toHypergraph.IsSeparation A' B' →
          (∃ i : Fin k, Disjoint A'.vertexSet (SubG i).vertexSet) →
          Z ⊆ A'.vertexSet →
          separationOrder A' B' ≤ separationOrder A B →
          A ≤ A' →
          A' = A) →
        ∀ v ∈ B.vertexSet \ A.vertexSet,
          IsIrrelevantToDigraphFolio G Z δ v

end GM21
end GraphMinor
