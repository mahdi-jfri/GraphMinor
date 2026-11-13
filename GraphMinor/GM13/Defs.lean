module

public import GraphMinor.GM05.Defs
public import GraphMinor.GM09.Defs
public import GraphMinor.GM10.Defs
public import GraphMinor.GM14.Defs
public import GraphMinor.Minor.Model

/-!
# Definitions for Graph Minors XIII (The Disjoint Paths Problem)

This file formalizes the definitions of N. Robertson and P. D. Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110:

- **Section 2 (pages 67–70):** Digraphs (`Digraph`), underlying undirected graphs (`Digraph.toGraph`),
  subdigraphs (`Digraph.IsSubdigraph`), induced subdigraphs `G|X` and vertex deletions `G \ X`
  (`Digraph.induce`, `Digraph.deleteVertices`, `Digraph.deleteVertex`), rooted digraphs
  (`RootedDigraph`), isomorphisms of digraphs and rooted digraphs (`Digraph.Iso`,
  `RootedDigraph.Iso`), models of graphs, digraphs, and rooted digraphs (`IsGraphModel`,
  `IsDigraphModel`, `IsRootedDigraphModel`), detail of a rooted digraph (`RootedDigraph.detail`),
  folios and `δ`-folios (`RootedDigraph.InFolio`, `RootedDigraph.InDeltaFolio`,
  `RootedDigraph.deltaFolio`, `HasSameDeltaFolio`, `HasSameDeltaFolioRel`), modellings
  (`IsDeltaFolioModelling`), separations of digraphs (`Digraph.IsSeparation`,
  `Digraph.separationOrder`), and irrelevant vertices (`IsIrrelevantVertex`).
- **Section 3 (pages 70–75):** Branch-decompositions of graphs (`IsGraphBranchDecomposition`),
  order of a tree edge (`graphBranchEdgeOrder`), width (`graphBranchDecompWidth`), and branch-width
  (`graphBranchWidth`, `GraphBranchWidthLE`), reusing `GM10.IsTernaryTree` and `GM10.leafSet`.
- **Section 5 (pages 78–83):** Generic `δ`-folios (`RootedDigraph.IsGenericDeltaFolio`,
  `IsGenericDeltaFolioRel`), edges between disjoint subgraphs (`Digraph.HasEdgeBetween`), and
  `p`-linked graphs (`IsPLinked`).
- **Section 6 (pages 83–87):** External vertex neighbourhood `N(X)` (`graphNeighborSet`).
- **Section 7 (pages 88–93):** Elementary walls of height `h` (`elementaryWallVerts`,
  `elementaryWall`), corners (`elementaryWallCorner`, `elementaryWallCorners`), perimeter
  (`elementaryWallPerimeter`), middle vertices (`elementaryWallMiddle₁`,
  `elementaryWallMiddle₂`), walls as subdivisions of elementary walls (`Wall`, `IsWallOfHeight`,
  `IsWallIn`), plane distance functions of walls (`planeWallDist`, `DistGeSub`), `H`-paths
  (reusing `GM14.IsHPathWithEnds`, `GM14.IsHPath`), and `(l, m)`-stars and external `(l, m)`-stars
  over a wall (`IsLMStarOver`, `IsExternalLMStarOver`).
- **Section 8 (pages 93–97):** Societies and crosses (reusing `GM09.Society`,
  `GM09.Society.IsCross`), trisecting subsets (`IsTrisecting`), cores (`IsCoreOf`), 4-linked
  vertices and 4-linked cores (`IsFourLinkedVertexIn`, `IsFourLinkedCore`), rural societies
  (reusing `GM09.Society.IsRuralSociety`), boundary `∂A` (`divBoundary`), divisions of a society
  (`IsSocietyDivision`), and rural divisions (`IsRuralDivision`).
- **Section 9 (pages 97–106):** Subwalls (`Wall.subwall`, `Wall.IsSubwallOf`), distance between
  subgraphs of a wall (`wallSubgraphDist`), crosses over a wall (`IsCrossOverWall`), dividing and
  non-dividing subwalls (`IsDividingSubwall`, `IsNonDividingSubwall`), compass of a wall
  (`wallCompass`), flat walls (`IsFlatWallIn`), society of a wall (`wallSociety`), and interior
  members of a division (`IsInteriorMember`).
- **Section 10 (pages 106–109):** `HypothesisC`, attachment sequences (`IsAttachmentSequence`),
  visions (`Vision`), `h`-homogeneous subwalls (`IsHomogeneousSubwall`), and the statement of
  (10.2) (`GM13Theorem102Statement`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM05 GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14

export GM14 (IsSubdivisionOf IsHPathWithEnds IsHPath SpanEmbedding)

universe u v w

/-! ## Section 2: Folios, Models, Separations, and Irrelevant Vertices (pages 67–70) -/

/-- A digraph `G` with vertex type `α` and edge type `β` (Graph Minors XIII, Section 2, page 68):
"For maximum generality we work with directed graphs, although that is not necessary for the
applications. Thus each edge has a head and a tail (the same, for a loop)." -/
structure Digraph (α : Type u) (β : Type v) where
  /-- The vertex set `V(G)`. -/
  vertexSet : Set α
  /-- The edge set `E(G)`. -/
  edgeSet : Set β
  /-- The head of an edge in `E(G)`. -/
  head : β → α
  /-- The tail of an edge in `E(G)`. -/
  tail : β → α
  /-- Every edge in `E(G)` has its head in `V(G)`. -/
  head_mem : ∀ ⦃e : β⦄, e ∈ edgeSet → head e ∈ vertexSet
  /-- Every edge in `E(G)` has its tail in `V(G)`. -/
  tail_mem : ∀ ⦃e : β⦄, e ∈ edgeSet → tail e ∈ vertexSet

namespace Digraph

variable {α : Type u} {β : Type v} {α' : Type*} {β' : Type*}

/-- A digraph `G` is finite if both `V(G)` and `E(G)` are finite. -/
structure IsFinite (G : Digraph α β) : Prop where
  /-- `V(G)` is finite. -/
  finite_V : G.vertexSet.Finite
  /-- `E(G)` is finite. -/
  finite_E : G.edgeSet.Finite

/-- A digraph `G` is null if `V(G) = ∅` and `E(G) = ∅`. -/
def IsNull (G : Digraph α β) : Prop :=
  G.vertexSet = ∅ ∧ G.edgeSet = ∅

/-- A digraph `G` is non-null if `V(G) ≠ ∅` (since every edge has ends in `V(G)`). -/
def IsNonNull (G : Digraph α β) : Prop :=
  G.vertexSet.Nonempty

/-- The underlying undirected graph of a digraph `G`, obtained by ignoring edge directions
(Graph Minors XIII, Section 2, page 68):
"The underlying graph of a digraph is obtained by forgetting the directions of its edges." -/
def toGraph (G : Digraph α β) : Graph α β where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet
  IsLink e x y := e ∈ G.edgeSet ∧ ((G.head e = x ∧ G.tail e = y) ∨ (G.head e = y ∧ G.tail e = x))
  isLink_symm e _ := ⟨fun x y h => ⟨h.1, h.2.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink e x y z w h1 h2 := by
    rcases h1.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl h3
    · exact Or.inr h3
    · exact Or.inr h4
    · exact Or.inl h4
  edge_mem_iff_exists_isLink e :=
    ⟨fun he => ⟨G.head e, G.tail e, he, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, he, _⟩ => he⟩
  left_mem_of_isLink e x y h := by
    rcases h.2 with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact G.head_mem h.1
    · exact G.tail_mem h.1

/-- `v` is an end of `e` in `G` (Graph Minors XIII, Section 2, page 68:
"Thus each edge has a head and a tail (the same, for a loop)."). -/
def Inc (G : Digraph α β) (e : β) (v : α) : Prop :=
  e ∈ G.edgeSet ∧ (G.head e = v ∨ G.tail e = v)

/-- `H` is a subdigraph of `G` (`H ⊆ G`). -/
structure IsSubdigraph (H G : Digraph α β) : Prop where
  /-- `V(H) ⊆ V(G)`. -/
  vertexSet_subset : H.vertexSet ⊆ G.vertexSet
  /-- `E(H) ⊆ E(G)`. -/
  edgeSet_subset : H.edgeSet ⊆ G.edgeSet
  /-- `H` and `G` agree on the head of every edge in `E(H)`. -/
  head_eq : ∀ ⦃e : β⦄, e ∈ H.edgeSet → H.head e = G.head e
  /-- `H` and `G` agree on the tail of every edge in `E(H)`. -/
  tail_eq : ∀ ⦃e : β⦄, e ∈ H.edgeSet → H.tail e = G.tail e

/-- The restriction of a digraph `G` to `X ⊆ V(G)` (Graph Minors XIII, Section 2, page 68). -/
def induce (G : Digraph α β) (X : Set α) : Digraph α β where
  vertexSet := G.vertexSet ∩ X
  edgeSet := {e ∈ G.edgeSet | G.head e ∈ X ∧ G.tail e ∈ X}
  head := G.head
  tail := G.tail
  head_mem _ he := ⟨G.head_mem he.1, he.2.1⟩
  tail_mem _ he := ⟨G.tail_mem he.1, he.2.2⟩

/-- Vertex deletion `G \ X` (Graph Minors XIII, Section 2, page 69). -/
def deleteVertices (G : Digraph α β) (X : Set α) : Digraph α β :=
  G.induce (G.vertexSet \ X)

/-- Single-vertex deletion `G \ v` (Graph Minors XIII, Section 2, page 69). -/
def deleteVertex (G : Digraph α β) (v : α) : Digraph α β :=
  G.deleteVertices {v}

/-- Subdigraph of `G` with vertex set `V' ⊆ V(G)` and edge set `E' ⊆ E(G)` (retaining edges of `E'`
whose ends lie in `V'`). -/
def subdigraphOf (G : Digraph α β) (V' : Set α) (E' : Set β) : Digraph α β where
  vertexSet := G.vertexSet ∩ V'
  edgeSet := {e ∈ G.edgeSet ∩ E' | G.head e ∈ V' ∧ G.tail e ∈ V'}
  head := G.head
  tail := G.tail
  head_mem _ he := ⟨G.head_mem he.1.1, he.2.1⟩
  tail_mem _ he := ⟨G.tail_mem he.1.1, he.2.2⟩

/-- The union `A ∪ B` of two subdigraphs `A, B` of `G`. -/
def unionSub (G A B : Digraph α β) : Digraph α β :=
  G.subdigraphOf (A.vertexSet ∪ B.vertexSet) (A.edgeSet ∪ B.edgeSet)

/-- The intersection `A ∩ B` of two subdigraphs `A, B` of `G`. -/
def interSub (G A B : Digraph α β) : Digraph α β :=
  G.subdigraphOf (A.vertexSet ∩ B.vertexSet) (A.edgeSet ∩ B.edgeSet)

/-- A digraph `H` is connected if the underlying graph is connected
(Graph Minors XIII, Section 2, page 68:
"In particular, a digraph is *connected* if the underlying graph is connected."). -/
def IsConnected (H : Digraph α β) : Prop :=
  H.vertexSet.Nonempty ∧ ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, Nonempty (GraphWalk H.toGraph u v)

/-- An isomorphism between two digraphs `G` and `G'`. -/
structure Iso (G : Digraph α β) (G' : Digraph α' β') where
  /-- The vertex map `V(G) → V(G')`. -/
  vMap : α → α'
  /-- The edge map `E(G) → E(G')`. -/
  eMap : β → β'
  /-- `vMap` is a bijection from `V(G)` to `V(G')`. -/
  bijOn_v : BijOn vMap G.vertexSet G'.vertexSet
  /-- `eMap` is a bijection from `E(G)` to `E(G')`. -/
  bijOn_e : BijOn eMap G.edgeSet G'.edgeSet
  /-- `head` is preserved by `(vMap, eMap)` on `E(G)`. -/
  head_eq : ∀ ⦃e : β⦄, e ∈ G.edgeSet → G'.head (eMap e) = vMap (G.head e)
  /-- `tail` is preserved by `(vMap, eMap)` on `E(G)`. -/
  tail_eq : ∀ ⦃e : β⦄, e ∈ G.edgeSet → G'.tail (eMap e) = vMap (G.tail e)

/-- Two digraphs `G` and `G'` are isomorphic. -/
def IsIso (G : Digraph α β) (G' : Digraph α' β') : Prop :=
  Nonempty (Iso G G')

/-- A separation `(A, B)` of a digraph `G` (Graph Minors XIII, Section 2, page 69):
"A separation of a graph or digraph $G$ is a pair $(A, B)$ of subgraphs such that $A \cup B = G$ and
$E(A \cap B) = \emptyset$, where for subgraphs $G_1 = (V_1, E_1)$, $G_2 = (V_2, E_2)$ of $G$,
$G_1 \cup G_2$ and $G_1 \cap G_2$ are the subgraphs $(V_1 \cup V_2, E_1 \cup E_2)$ and
$(V_1 \cap V_2, E_1 \cap E_2)$, respectively. The order of the separation $(A, B)$ is
$|V(A \cap B)|$." -/
structure IsSeparation (G A B : Digraph α β) : Prop where
  /-- `A` is a subdigraph of `G`. -/
  sub_left : A.IsSubdigraph G
  /-- `B` is a subdigraph of `G`. -/
  sub_right : B.IsSubdigraph G
  /-- `V(A) ∪ V(B) = V(G)`. -/
  vertexSet_union : A.vertexSet ∪ B.vertexSet = G.vertexSet
  /-- `E(A) ∪ E(B) = E(G)`. -/
  edgeSet_union : A.edgeSet ∪ B.edgeSet = G.edgeSet
  /-- `E(A ∩ B) = ∅`. -/
  edgeSet_disjoint : Disjoint A.edgeSet B.edgeSet

/-- The order `|V(A ∩ B)|` of a separation `(A, B)` of a digraph `G`
(Graph Minors XIII, Section 2, page 69). -/
noncomputable def separationOrder (A B : Digraph α β) : ℕ :=
  (A.vertexSet ∩ B.vertexSet).ncard

/-- There is an edge of `G` between two vertex sets `A, B ⊆ V(G)`
(Graph Minors XIII, Section 5, page 78):
"If $G$ is a digraph and $X, Y \subseteq V(G)$ or $X, Y$ are subgraphs of $G$, an edge of $G$ is
said to be *between* $X$ and $Y$ if it has one end in $X$ and the other in $Y$." -/
def HasEdgeBetween (G : Digraph α β) (A B : Set α) : Prop :=
  ∃ e ∈ G.edgeSet, (G.head e ∈ A ∧ G.tail e ∈ B) ∨ (G.head e ∈ B ∧ G.tail e ∈ A)

end Digraph

/-- A rooted digraph `(G, v₁, …, v_k)` (Graph Minors XIII, Section 2, page 68):
"Thus, let us say that $(G, v_1, \dots, v_k)$ is a *rooted digraph* if $G$ is a digraph and
$v_1, \dots, v_k \in V(G)$ (not necessarily distinct). For $1 \le i \le k$, $v_i$ is the $i$ th
root." -/
structure RootedDigraph (α : Type u) (β : Type v) (k : ℕ) where
  /-- The underlying digraph `G`. -/
  digraph : Digraph α β
  /-- The sequence of `k` roots `v₁, …, v_k`. -/
  roots : Fin k → α
  /-- Each root `v_i` belongs to `V(G)`. -/
  roots_mem : ∀ i : Fin k, roots i ∈ digraph.vertexSet

namespace RootedDigraph

variable {α : Type u} {β : Type v} {α' : Type*} {β' : Type*} {k : ℕ}

/-- An isomorphism between two rooted digraphs `(G, v₁, …, v_k)` and `(G', v'₁, …, v'_k)`
(Graph Minors XIII, Section 2, page 68):
"Isomorphism of rooted digraphs is defined in the natural way; thus, isomorphic rooted digraphs have
the same number of roots, and the isomorphism maps the $i$ th root of one to the $i$ th root of the
other, for all $i$." -/
structure Iso (R : RootedDigraph α β k) (R' : RootedDigraph α' β' k)
    extends Digraph.Iso R.digraph R'.digraph where
  /-- The isomorphism maps `v_i` to `v'_i` for `1 ≤ i ≤ k`. -/
  map_roots : ∀ i : Fin k, vMap (R.roots i) = R'.roots i

/-- Two rooted digraphs are isomorphic (Graph Minors XIII, Section 2, page 68). -/
def IsIso (R : RootedDigraph α β k) (R' : RootedDigraph α' β' k) : Prop :=
  Nonempty (Iso R R')

/-- The detail `max(|E(H)|, |V(H) - {u₁, …, u_k}|)` of a rooted digraph `(H, u₁, …, u_k)`
(Graph Minors XIII, Section 2, page 68):
"If $\delta \ge 0$ is an integer, we say that $(H, u_1, \dots, u_k)$ has *detail* $\le \delta$ if
$|E(H)| \le \delta$ and $|V(H) - \{u_1, \dots, u_k\}| \le \delta$." -/
noncomputable def detail (R : RootedDigraph α β k) : ℕ :=
  max R.digraph.edgeSet.ncard (R.digraph.vertexSet \ Set.range R.roots).ncard

end RootedDigraph

/-- A model `ϕ` of an undirected graph `H` in an undirected graph `G`
(Graph Minors XIII, Section 2, page 68):
"Let $G, H$ be both graphs or both digraphs. A *model* $\phi$ of $H$ in $G$ assigns to each edge $e$
of $H$ an edge $\phi(e)$ of $G$, and to each vertex $v$ of $H$ a non-null connected subgraph
$\phi(v)$ of $G$, such that
(i) the graphs $\phi(v)$ ($v \in V(H)$) are mutually vertex-disjoint, the edges $\phi(e)$
($e \in E(H)$) are all distinct, and for $v \in V(H)$ and $e \in E(H)$, $\phi(e) \notin E(\phi(v))$
(ii) for $e \in E(H)$, if $e$ has head $u$ and tail $v$ (or, in the undirected case, has ends
$u, v$) then $\phi(e)$ has a head in $V(\phi(u))$ and a tail in $V(\phi(v))$ (respectively,
$\phi(e)$ has one end in $V(\phi(u))$ and the other in $V(\phi(v))$)." -/
structure IsGraphModel {α : Type u} {β : Type v} {α' : Type*} {β' : Type*}
    (H : Graph α' β') (G : Graph α β) (vMap : α' → Graph α β) (eMap : β' → β) : Prop where
  /-- For each `v ∈ V(H)`, `ϕ(v)` is a subgraph of `G`. -/
  sub_of_mem : ∀ ⦃v : α'⦄, v ∈ V(H) → vMap v ≤ G
  /-- For each `v ∈ V(H)`, `ϕ(v)` is non-null. -/
  nonempty_of_mem : ∀ ⦃v : α'⦄, v ∈ V(H) → V(vMap v).Nonempty
  /-- For each `v ∈ V(H)`, `ϕ(v)` is connected. -/
  connected_of_mem : ∀ ⦃v : α'⦄, v ∈ V(H) →
    ∀ x ∈ V(vMap v), ∀ y ∈ V(vMap v), Nonempty (GraphWalk (vMap v) x y)
  /-- (i) If `u, v ∈ V(H)` are distinct then `ϕ(u)` and `ϕ(v)` are vertex-disjoint. -/
  disjoint_of_ne : ∀ ⦃u v : α'⦄, u ∈ V(H) → v ∈ V(H) → u ≠ v → Disjoint V(vMap u) V(vMap v)
  /-- For each `e ∈ E(H)`, `ϕ(e) ∈ E(G)`. -/
  edge_mem : ∀ ⦃e : β'⦄, e ∈ E(H) → eMap e ∈ E(G)
  /-- (ii) Non-loop link preservation: if `e` has distinct ends `u ≠ v` in `H`, then `ϕ(e)` has one
  end in `V(ϕ(u))` and the other in `V(ϕ(v))`. -/
  link_ends_of_ne : ∀ ⦃e : β'⦄ ⦃u v : α'⦄, H.IsLink e u v → u ≠ v →
    ∃ x ∈ V(vMap u), ∃ y ∈ V(vMap v), G.IsLink (eMap e) x y
  /-- (ii) Loop preservation: if `e` is a loop at `u` in `H`, then `ϕ(e) ∈ E(G) \ E(ϕ(u))` and both
  ends of `ϕ(e)` belong to `V(ϕ(u))`. -/
  loop_ends : ∀ ⦃e : β'⦄ ⦃u : α'⦄, H.IsLink e u u →
    eMap e ∉ E(vMap u) ∧ ∃ x ∈ V(vMap u), ∃ y ∈ V(vMap u), G.IsLink (eMap e) x y
  /-- (i) The edges `ϕ(e)` (`e ∈ E(H)`) are all distinct. -/
  eMap_injOn : InjOn eMap E(H)

/-- The model conditions of XIII, Section 2, page 68, with the edge map defined
only on edges of `H`. -/
structure IsEdgeGraphModel {α : Type u} {β : Type v} {α' : Type*} {β' : Type*}
    (H : Graph α' β') (G : Graph α β) (vMap : α' → Graph α β) (eMap : E(H) → β) : Prop where
  /-- For each `v ∈ V(H)`, `ϕ(v)` is a subgraph of `G`. -/
  sub_of_mem : ∀ ⦃v : α'⦄, v ∈ V(H) → vMap v ≤ G
  /-- For each `v ∈ V(H)`, `ϕ(v)` is non-null. -/
  nonempty_of_mem : ∀ ⦃v : α'⦄, v ∈ V(H) → V(vMap v).Nonempty
  /-- For each `v ∈ V(H)`, `ϕ(v)` is connected. -/
  connected_of_mem : ∀ ⦃v : α'⦄, v ∈ V(H) →
    ∀ x ∈ V(vMap v), ∀ y ∈ V(vMap v), Nonempty (GraphWalk (vMap v) x y)
  /-- (i) If `u, v ∈ V(H)` are distinct then `ϕ(u)` and `ϕ(v)` are vertex-disjoint. -/
  disjoint_of_ne : ∀ ⦃u v : α'⦄, u ∈ V(H) → v ∈ V(H) → u ≠ v → Disjoint V(vMap u) V(vMap v)
  /-- For each `e ∈ E(H)`, `ϕ(e) ∈ E(G)`. -/
  edge_mem : ∀ ⦃e : β'⦄ (he : e ∈ E(H)), eMap ⟨e, he⟩ ∈ E(G)
  /-- (ii) Non-loop link preservation: if `e` has distinct ends `u ≠ v` in `H`, then `ϕ(e)` has one
  end in `V(ϕ(u))` and the other in `V(ϕ(v))`. -/
  link_ends_of_ne : ∀ ⦃e : β'⦄ ⦃u v : α'⦄ (h : H.IsLink e u v), u ≠ v →
    ∃ x ∈ V(vMap u), ∃ y ∈ V(vMap v), G.IsLink (eMap ⟨e, h.edge_mem⟩) x y
  /-- (ii) Loop preservation: if `e` is a loop at `u` in `H`, then `ϕ(e) ∈ E(G) \ E(ϕ(u))` and both
  ends of `ϕ(e)` belong to `V(ϕ(u))`. -/
  loop_ends : ∀ ⦃e : β'⦄ ⦃u : α'⦄ (h : H.IsLink e u u),
    eMap ⟨e, h.edge_mem⟩ ∉ E(vMap u) ∧ ∃ x ∈ V(vMap u), ∃ y ∈ V(vMap u), G.IsLink (eMap ⟨e, h.edge_mem⟩) x y
  /-- (i) The edges `ϕ(e)` (`e ∈ E(H)`) are all distinct. -/
  eMap_injOn : Function.Injective eMap

/-- There exists a model of `H` in `G` (Graph Minors XIII, Section 2, page 68). -/
def HasGraphModel {α : Type u} {β : Type v} {α' : Type*} {β' : Type*}
    (H : Graph α' β') (G : Graph α β) : Prop :=
  ∃ (vMap : α' → Graph α β) (eMap : E(H) → β), IsEdgeGraphModel H G vMap eMap

/-- Restricting a total edge map gives a model on the actual edges. -/
theorem hasGraphModel_of_isGraphModel {α : Type u} {β : Type v} {α' β' : Type*}
    {H : Graph α' β'} {G : Graph α β} {vMap : α' → Graph α β} {eMap : β' → β}
    (h : IsGraphModel H G vMap eMap) : HasGraphModel H G := by
  exact ⟨vMap, fun e => eMap e, ⟨h.sub_of_mem, h.nonempty_of_mem,
    h.connected_of_mem, h.disjoint_of_ne, h.edge_mem, h.link_ends_of_ne,
    h.loop_ends, fun e f hef => Subtype.ext (h.eMap_injOn e.property f.property hef)⟩⟩

/-- A model given by total maps restricts to the edge set. -/
theorem hasGraphModel_of_exists_isGraphModel {α : Type u} {β : Type v} {α' β' : Type*}
    {H : Graph α' β'} {G : Graph α β}
    (h : ∃ (vMap : α' → Graph α β) (eMap : β' → β), IsGraphModel H G vMap eMap) :
    HasGraphModel H G := by
  obtain ⟨vMap, eMap, hm⟩ := h
  exact hasGraphModel_of_isGraphModel hm

/-- A model extends to all ambient edge names when the target edge type is nonempty. -/
theorem HasGraphModel.exists_isGraphModel {α : Type u} {β : Type v} {α' β' : Type*}
    [Nonempty β] {H : Graph α' β'} {G : Graph α β} (h : HasGraphModel H G) :
    ∃ (vMap : α' → Graph α β) (eMap : β' → β), IsGraphModel H G vMap eMap := by
  classical
  obtain ⟨vMap, eMap, hm⟩ := h
  let f : β' → β := fun e => if he : e ∈ E(H) then eMap ⟨e, he⟩ else Classical.arbitrary β
  have hf (e : β') (he : e ∈ E(H)) : f e = eMap ⟨e, he⟩ := by simp only [f, he, ↓reduceDIte]
  refine ⟨vMap, f, ⟨hm.sub_of_mem, hm.nonempty_of_mem, hm.connected_of_mem,
    hm.disjoint_of_ne, ?_, ?_, ?_, ?_⟩⟩
  · intro e he
    rw [hf e he]
    exact hm.edge_mem he
  · intro e u v hl hne
    rw [hf e hl.edge_mem]
    exact hm.link_ends_of_ne hl hne
  · intro e u hl
    rw [hf e hl.edge_mem]
    exact hm.loop_ends hl
  · intro e he f' hf' hef
    rw [hf e he, hf f' hf'] at hef
    exact congrArg Subtype.val (hm.eMap_injOn hef)

/-- A model `ϕ` of a digraph `H` in a digraph `G` (Graph Minors XIII, Section 2, page 68). -/
structure IsDigraphModel {α : Type u} {β : Type v} {α' : Type*} {β' : Type*}
    (H : Digraph α' β') (G : Digraph α β) (vMap : α' → Digraph α β) (eMap : β' → β) : Prop where
  /-- For each `v ∈ V(H)`, `ϕ(v)` is a subdigraph of `G`. -/
  sub_of_mem : ∀ ⦃v : α'⦄, v ∈ H.vertexSet → (vMap v).IsSubdigraph G
  /-- For each `v ∈ V(H)`, `ϕ(v)` is non-null and connected as a graph. -/
  connected_of_mem : ∀ ⦃v : α'⦄, v ∈ H.vertexSet → (vMap v).IsConnected
  /-- (i) If `u, v ∈ V(H)` are distinct then `ϕ(u)` and `ϕ(v)` are disjoint. -/
  disjoint_of_ne : ∀ ⦃u v : α'⦄, u ∈ H.vertexSet → v ∈ H.vertexSet → u ≠ v →
    Disjoint (vMap u).vertexSet (vMap v).vertexSet
  /-- For each `e ∈ E(H)`, `ϕ(e) ∈ E(G)`. -/
  edge_mem : ∀ ⦃e : β'⦄, e ∈ H.edgeSet → eMap e ∈ G.edgeSet
  /-- (ii) For each `e ∈ E(H)`, `ϕ(e)` has head in `V(ϕ(head(e)))` and tail in `V(ϕ(tail(e)))`. -/
  head_tail_mem : ∀ ⦃e : β'⦄, e ∈ H.edgeSet →
    G.head (eMap e) ∈ (vMap (H.head e)).vertexSet ∧
    G.tail (eMap e) ∈ (vMap (H.tail e)).vertexSet
  /-- (i) If `e ∈ E(H)` is a loop (`head(e) = tail(e) = u`), then `ϕ(e) ∉ E(ϕ(u))`. -/
  loop_not_mem : ∀ ⦃e : β'⦄, e ∈ H.edgeSet → H.head e = H.tail e →
    eMap e ∉ (vMap (H.head e)).edgeSet
  /-- (i) For `e, e' ∈ E(H)`, if `e ≠ e'` then `ϕ(e) ≠ ϕ(e')`. -/
  eMap_injOn : InjOn eMap H.edgeSet

/-- A model `ϕ` of a rooted digraph `(H, u₁, …, u_k)` in `(G, v₁, …, v_k)`
(Graph Minors XIII, Section 2, page 68):
"Let $(G, v_1, \dots, v_k)$, $(H, u_1, \dots, u_k)$ be rooted digraphs. A *model* of the second in
the first is a model $\phi$ of $H$ in $G$ such that $v_i \in V(\phi(u_i))$ ($1 \le i \le k$), and if
there is such a model, we say that $(H, u_1, \dots, u_k)$ is a minor of $(G, v_1, \dots, v_k)$." -/
structure IsRootedDigraphModel {α : Type u} {β : Type v} {α' : Type*} {β' : Type*} {k : ℕ}
    (H : RootedDigraph α' β' k) (G : RootedDigraph α β k)
    (vMap : α' → Digraph α β) (eMap : β' → β) : Prop
    extends IsDigraphModel H.digraph G.digraph vMap eMap where
  /-- `v_i ∈ V(ϕ(u_i))` for `1 ≤ i ≤ k`. -/
  root_mem : ∀ i : Fin k, G.roots i ∈ (vMap (H.roots i)).vertexSet

/-- `(H, u₁, …, u_k)` is a minor of `(G, v₁, …, v_k)` (Graph Minors XIII, Section 2, page 68). -/
def IsRootedDigraphMinor {α : Type u} {β : Type v} {α' : Type*} {β' : Type*} {k : ℕ}
    (H : RootedDigraph α' β' k) (G : RootedDigraph α β k) : Prop :=
  ∃ (vMap : α' → Digraph α β) (eMap : β' → β), IsRootedDigraphModel H G vMap eMap

namespace RootedDigraph

variable {α : Type u} {β : Type v} {α' : Type*} {β' : Type*} {k : ℕ}

/-- `(H, u₁, …, u_k)` belongs to the folio of `(G, v₁, …, v_k)`
(Graph Minors XIII, Section 2, page 68):
"The set of all minors of $(G, v_1, \dots, v_k)$ is closed under isomorphism, and we call it the
*folio* of $(G, v_1, \dots, v_k)$. Clearly the folio is finite up to isomorphism. If $\delta \ge 0$
is an integer, we say that $(H, u_1, \dots, u_k)$ has *detail* $\le \delta$ if
$|E(H)| \le \delta$ and $|V(H) - \{u_1, \dots, u_k\}| \le \delta$. The $\delta$-*folio* of
$(G, v_1, \dots, v_k)$ is the set of all minors of $(G, v_1, \dots, v_k)$ with detail
$\le \delta$." -/
def InFolio (G : RootedDigraph α β k) (H : RootedDigraph α' β' k) : Prop :=
  H.digraph.IsFinite ∧ IsRootedDigraphMinor H G

/-- `(H, u₁, …, u_k)` belongs to the `δ`-folio of `(G, v₁, …, v_k)`
(Graph Minors XIII, Section 2, page 68). -/
def InDeltaFolio (G : RootedDigraph α β k) (δ : ℕ) (H : RootedDigraph α' β' k) : Prop :=
  G.InFolio H ∧ H.detail ≤ δ

/-- The `δ`-folio of `(G, v₁, …, v_k)` represented as a set of finite rooted digraphs on `ℕ`
(since every finite rooted digraph is isomorphic to one with vertex and edge sets in `ℕ`). -/
def deltaFolio (G : RootedDigraph α β k) (δ : ℕ) : Set (RootedDigraph ℕ ℕ k) :=
  {H : RootedDigraph ℕ ℕ k | G.InDeltaFolio δ H}

end RootedDigraph

/-- Two rooted digraphs `R₁` and `R₂` have the same `δ`-folio
(Graph Minors XIII, Section 2, page 68). -/
def HasSameDeltaFolio {α₁ : Type*} {β₁ : Type*} {α₂ : Type*} {β₂ : Type*} {k : ℕ}
    (R₁ : RootedDigraph α₁ β₁ k) (R₂ : RootedDigraph α₂ β₂ k) (δ : ℕ) : Prop :=
  R₁.deltaFolio δ = R₂.deltaFolio δ

/-- A modelling of the `δ`-folio of `(G, v₁, …, v_k)` (Graph Minors XIII, Section 4, page 75):
"If $G$ is a digraph, $Z \subseteq V(G)$, and $\delta \ge 0$, a modelling of the $\delta$-folio of
$G$ relative to $Z$ means some choice of model, for each member of the $\delta$-folio of $G$
relative to $Z$ (up to isomorphism)." -/
def IsDeltaFolioModelling {α : Type u} {β : Type v} {k : ℕ}
    (G : RootedDigraph α β k) (δ : ℕ)
    (vMod : RootedDigraph ℕ ℕ k → ℕ → Digraph α β)
    (eMod : RootedDigraph ℕ ℕ k → ℕ → β) : Prop :=
  ∀ H ∈ G.deltaFolio δ, IsRootedDigraphModel H G (vMod H) (eMod H)

/-- Given a digraph `G`, a list of vertices `L : List α`, and a proof `hL : ∀ x ∈ L, x ∈ V(G)`,
construct the rooted digraph `(G, L[0], …, L[k-1])`. -/
def rootedDigraphOfList {α : Type u} {β : Type v} (G : Digraph α β) (L : List α)
    (hL : ∀ x ∈ L, x ∈ G.vertexSet) : RootedDigraph α β L.length where
  digraph := G
  roots i := L[i.1]
  roots_mem i := hL L[i.1] (List.getElem_mem _)

/-- The `δ`-folio of `G` relative to `Z ⊆ V(G)` (Graph Minors XIII, Section 2, page 69):
"Thus, if $Z \subseteq V(G)$, by the $\delta$-folio of $G$ relative to $Z$ we mean the
$\delta$-folio of $(G, v_1, \dots, v_k)$ for any choice of $v_1, \dots, v_k$ with $k = |Z|$ and
$Z = \{v_1, \dots, v_k\}$." -/
def HasSameDeltaFolioRel {α : Type u} {β₁ : Type v} {β₂ : Type w}
    (G₁ : Digraph α β₁) (G₂ : Digraph α β₂) (δ : ℕ) (Z : Set α) : Prop :=
  Z ⊆ G₁.vertexSet ∧ Z ⊆ G₂.vertexSet ∧
    ∀ (k : ℕ) (v : Fin k → α) (hv₁ : ∀ i, v i ∈ G₁.vertexSet) (hv₂ : ∀ i, v i ∈ G₂.vertexSet),
      Function.Injective v → Set.range v ⊆ Z →
      HasSameDeltaFolio (RootedDigraph.mk G₁ v hv₁) (RootedDigraph.mk G₂ v hv₂) δ

/-- A vertex `v ∈ V(G)` is irrelevant to the `δ`-folio of `G` relative to `Z`
(Graph Minors XIII, Section 2, page 69):
"For $Z \subseteq V(G)$, a vertex $v$ of $G$ is *irrelevant (to the $\delta$-folio of $G$ relative
to $Z$)* if $v \notin Z$ and the $\delta$-folios of $G$ and $G \setminus v$ relative to $Z$ are
equal." -/
def IsIrrelevantVertex {α : Type u} {β : Type v}
    (G : Digraph α β) (δ : ℕ) (Z : Set α) (v : α) : Prop :=
  v ∈ G.vertexSet ∧ v ∉ Z ∧ HasSameDeltaFolioRel (G.deleteVertex v) G δ Z

/-! ## Section 3: Branch-Width of a Graph (pages 70–75) -/

/-- The separation order `|V(A ∩ B)|` of a separation `(A, B)` of an undirected graph `G`
(Graph Minors XIII, Section 2, page 69). -/
noncomputable def graphSeparationOrder {α : Type u} {β : Type v} (A B : Graph α β) : ℕ :=
  (V(A) ∩ V(B)).ncard

/-- A finite simple graph `T` on `ι` is either the empty tree (`IsEmpty ι`) or a ternary tree
(`GM10.IsTernaryTree T`) (Graph Minors XIII, Section 3, page 70). -/
def IsTernaryOrEmptyTree {ι : Type*} [Fintype ι] (T : SimpleGraph ι) : Prop :=
  IsEmpty ι ∨ GM10.IsTernaryTree T

/-- `(T, τ)` is a branch-decomposition of a graph `G` (Graph Minors XIII, Section 3, page 70):
"A *branch-decomposition* of a graph or digraph $G$ is a pair $(T, \tau)$, where
(i) $T$ is a tree and every vertex of $T$ has valency 1 or 3
(ii) $\tau$ is a bijection from $E(G)$ to the set of leaves of $T$." -/
structure IsGraphBranchDecomposition {α : Type u} {β : Type v} {ι : Type*} [Fintype ι]
    (G : Graph α β) (T : SimpleGraph ι) (τ : β → ι) : Prop where
  /-- `T` is a ternary tree (or the empty tree when `E(G) = ∅`). -/
  isTernaryOrEmpty : IsTernaryOrEmptyTree T
  /-- `τ` is a bijection from `E(G)` onto the set of leaves of `T`. -/
  bijOn : Set.BijOn τ E(G) (GM10.leafSet T)

/-- For an edge `e ∈ E(T)` of a branch-decomposition `(T, τ)` of `G`, the order of `e` is the
number of vertices `v ∈ V(G)` incident with an edge mapped to one component of `T \ e` and an edge
mapped to the other component of `T \ e` (Graph Minors XIII, Section 3, page 70):
"For each $f \in E(T)$ the edges $e$ of $G$ are divided into two sets, depending on which component
of $T \setminus f$ contains $\tau(e)$. The *order* of $f$ is the number of vertices of $G$ incident
with an edge in each set." -/
noncomputable def graphBranchEdgeOrder {α : Type u} {β : Type v} {ι : Type*} [Fintype ι]
    (G : Graph α β) (T : SimpleGraph ι) (τ : β → ι) (e : Sym2 ι) : ℕ :=
  {v ∈ V(G) | ∃ f₁ ∈ E(G), ∃ f₂ ∈ E(G),
    ¬ (T.deleteEdges {e}).Reachable (τ f₁) (τ f₂) ∧ G.Inc f₁ v ∧ G.Inc f₂ v}.ncard

/-- The width of a branch-decomposition `(T, τ)` of `G` (Graph Minors XIII, Section 3, page 70):
"The *width* of $(T, \tau)$ is the maximum order of edges of $T$, and the *branch-width* of $G$ is
the minimum width of all branch-decompositions of $G$." -/
noncomputable def graphBranchDecompWidth {α : Type u} {β : Type v} {ι : Type*} [Fintype ι]
    (G : Graph α β) (T : SimpleGraph ι) (τ : β → ι) : ℕ :=
  sSup (graphBranchEdgeOrder G T τ '' T.edgeSet)

/-- `G` has a branch-decomposition of width at most `ω` (Graph Minors XIII, Section 3, page 70). -/
def GraphBranchWidthLE {α : Type u} {β : Type v} (G : Graph α β) (ω : ℕ) : Prop :=
  E(G).ncard ≤ 1 ∨
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : β → ι),
      IsGraphBranchDecomposition G T τ ∧ graphBranchDecompWidth G T τ ≤ ω

/-- The branch-width of a graph `G` (Graph Minors XIII, Section 3, page 70):
"(If there are no branch-decompositions of $G$, then $|E(G)| \le 1$ and $G$ has branch-width 0 by
convention.)" -/
noncomputable def graphBranchWidth {α : Type u} {β : Type v} (G : Graph α β) : ℕ :=
  sInf {ω : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : β → ι),
    IsGraphBranchDecomposition G T τ ∧ graphBranchDecompWidth G T τ = ω}

/-! ## Section 5: Generic Folios and `p`-Linked Graphs (pages 78–83) -/

/-- The `δ`-folio of a rooted digraph `(G, v₁, …, v_k)` is generic
(Graph Minors XIII, Section 5, page 78):
"The $\delta$-folio of a digraph $G$ relative to $Z \subseteq V(G)$ is *generic* if the
$\delta$-folio of the rooted digraph $(G, v_1, \dots, v_{\xi})$ contains every rooted digraph with
$\xi$ roots and with detail $\le \delta$, where $|Z| = \xi$ and $Z = \{v_1, \dots, v_{\xi}\}$." -/
def RootedDigraph.IsGenericDeltaFolio {α : Type u} {β : Type v} {k : ℕ}
    (G : RootedDigraph α β k) (δ : ℕ) : Prop :=
  Function.Injective G.roots ∧
    ∀ (H : RootedDigraph ℕ ℕ k),
      H.digraph.IsFinite → H.detail ≤ δ → G.InDeltaFolio δ H

/-- The `δ`-folio of `G` relative to `Z ⊆ V(G)` is generic (Graph Minors XIII, Section 5, page 78). -/
def IsGenericDeltaFolioRel {α : Type u} {β : Type v}
    (G : Digraph α β) (δ : ℕ) (Z : Set α) : Prop :=
  Z ⊆ G.vertexSet ∧ Z.Finite ∧
    ∀ (k : ℕ) (v : Fin k → α) (hv : ∀ i, v i ∈ G.vertexSet),
      Function.Injective v → Set.range v = Z →
      (RootedDigraph.mk G v hv).IsGenericDeltaFolio δ

/-- A graph `G` is `p`-linked (Graph Minors XIII, Section 5, page 83):
"A graph $G$ is said to be *$p$-linked*, where $p \ge 0$ is an integer, if for all $s_1, \dots, s_p$,
$t_1, \dots, t_p \in V(G)$ with $s_i, t_i \ne s_j, t_j$ for $1 \le i < j \le p$, there are $p$
mutually vertex-disjoint paths of $G$ linking $s_i$ and $t_i$ for $1 \le i \le p$." -/
def IsPLinked {α : Type u} {β : Type v} (G : Graph α β) (p : ℕ) : Prop :=
  2 * p ≤ V(G).ncard ∧
    ∀ (s t : Fin p → α),
      (∀ i, s i ∈ V(G)) → (∀ i, t i ∈ V(G)) →
      Function.Injective s → Function.Injective t → Disjoint (Set.range s) (Set.range t) →
      ∃ P : Fin p → Graph α β,
        Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
        ∀ i : Fin p, IsGraphPathWithEnds G (P i) (s i) (t i)

/-- A graph `G` is `k`-connected if `|V(G)| > k` and `G \ X` is connected for every `X ⊆ V(G)` with
`|X| < k` (Graph Minors XIII, Section 5, (5.6), page 83). -/
def IsKConnectedGraph {α : Type u} {β : Type v} (G : Graph α β) (k : ℕ) : Prop :=
  k < V(G).ncard ∧
    ∀ X ⊆ V(G), X.ncard < k →
      ∀ u ∈ V(deleteVertices G X), ∀ v ∈ V(deleteVertices G X),
        Nonempty (GraphWalk (deleteVertices G X) u v)

/-! ## Section 6: External Neighbourhood `N(X)` (pages 83–87) -/

/-- `N(X)`, the set of vertices in `V(G) - X` with a neighbour in `X`
(Graph Minors XIII, Section 6, page 85):
"If $G$ is a graph and $X \subseteq V(G)$, we denote by $N(X)$ the set of vertices in $V(G) - X$
with a neighbour in $X$." -/
def graphNeighborSet {α : Type u} {β : Type v} (G : Graph α β) (X : Set α) : Set α :=
  {v ∈ V(G) \ X | ∃ u ∈ X, G.Adj u v}

/-! ## Section 7: Elementary Walls, Walls, Distance Function, and `(l, m)`-Stars (pages 88–93) -/

/-- The vertex set of the elementary wall `J` of height `h` in `(x, y)`-coordinates with origin at
the bottom-left (Graph Minors XIII, Section 7, page 88, and Section 9, page 97):
"First, let $J$ be an elementary wall of height $h$. Draw $J$ in the plane as in Fig. 1, and let
us name the vertices of $J$ by $x, y$-coordinates, taking the origin in the bottom left of the
figure. Thus, $J$ has vertex set

$$\{(x, y) : 0 \le x \le 2h+1, 0 \le y \le h\} - \{(0, 0), (2h+1, h)\}$$

and corners $(1, 0), (2h+1, 0), (0, h), (2h, h)$." -/
def elementaryWallVerts (h : ℕ) : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | p.1 ≤ 2 * h + 1 ∧ p.2 ≤ h ∧ p ≠ (0, 0) ∧ p ≠ (2 * h + 1, h)}

/-- Adjacency in the elementary wall of height `h` (`h ≥ 2` even): horizontal edges along each row
`0 ≤ y ≤ h`, and vertical edges between `(x, y)` and `(x, y + 1)` whenever `x + y` is odd
(Graph Minors XIII, Section 7, page 88, and Section 9, page 97). -/
def elementaryWallAdj (h : ℕ) (p q : ℕ × ℕ) : Prop :=
  p ∈ elementaryWallVerts h ∧ q ∈ elementaryWallVerts h ∧
    ((p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1)) ∨
      (p.1 = q.1 ∧ ((p.2 + 1 = q.2 ∧ Odd (p.1 + p.2)) ∨ (q.2 + 1 = p.2 ∧ Odd (q.1 + q.2)))))

/-- The elementary wall of height `h` as a `Graph (ℕ × ℕ) (Sym2 (ℕ × ℕ))`
(Graph Minors XIII, Section 7, page 88, and Section 9, page 97). -/
def elementaryWall (h : ℕ) : Graph (ℕ × ℕ) (Sym2 (ℕ × ℕ)) where
  vertexSet := elementaryWallVerts h
  edgeSet := {e : Sym2 (ℕ × ℕ) | ∃ p q : ℕ × ℕ, elementaryWallAdj h p q ∧ e = s(p, q)}
  IsLink e p q := elementaryWallAdj h p q ∧ e = s(p, q)
  isLink_symm e _ := ⟨fun p q ⟨⟨hp, hq, hadj⟩, he⟩ => by
    refine ⟨⟨hq, hp, ?_⟩, he.trans Sym2.eq_swap⟩
    rcases hadj with ⟨hy, hx⟩ | ⟨hx, hy⟩
    · exact Or.inl ⟨hy.symm, hx.symm⟩
    · exact Or.inr ⟨hx.symm, hy.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := by
    have heq : s(_, _) = s(_, _) := h1.2.symm.trans h2.2
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink _ := Iff.rfl
  left_mem_of_isLink _ _ _ h := h.1.1

/-- The four corners of the elementary wall of height `h`, in cyclic order around the perimeter:
`(1, 0)`, `(0, h)`, `(2h, h)`, `(2h + 1, 0)` (Graph Minors XIII, Section 7, page 88, and Section 9,
page 97). -/
def elementaryWallCorner (h : ℕ) : Fin 4 → ℕ × ℕ
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (0, h)
  | ⟨2, _⟩ => (2 * h, h)
  | ⟨3, _⟩ => (2 * h + 1, 0)

/-- The set of four corners of the elementary wall of height `h`
(Graph Minors XIII, Section 7, page 88, and Section 9, page 97). -/
def elementaryWallCorners (h : ℕ) : Set (ℕ × ℕ) :=
  Set.range (elementaryWallCorner h)

/-- The vertices on the perimeter of the elementary wall of height `h`
(Graph Minors XIII, Section 7, page 88: "The *perimeter* is the circuit which bounds the infinite
region when drawn as in Fig. 1."). -/
def elementaryWallPerimeterVerts (h : ℕ) : Set (ℕ × ℕ) :=
  {p ∈ elementaryWallVerts h | p.2 = 0 ∨ p.2 = h ∨ p.1 ≤ 1 ∨ 2 * h ≤ p.1}

/-- The perimeter circuit of the elementary wall of height `h`
(Graph Minors XIII, Section 7, page 88). -/
def elementaryWallPerimeter (h : ℕ) : Graph (ℕ × ℕ) (Sym2 (ℕ × ℕ)) :=
  (elementaryWall h).induce (elementaryWallPerimeterVerts h)

/-- The first middle vertex `(h, h / 2)` of the elementary wall of height `h`
(Graph Minors XIII, Section 10, page 107). -/
def elementaryWallMiddle₁ (h : ℕ) : ℕ × ℕ :=
  (h, h / 2)

/-- The second middle vertex `(h + 1, h / 2)` of the elementary wall of height `h`
(Graph Minors XIII, Section 10, page 107). -/
def elementaryWallMiddle₂ (h : ℕ) : ℕ × ℕ :=
  (h + 1, h / 2)

/-- A wall of height `h` (`h ≥ 2` even), equipped with its subdivision structure from the
elementary wall of height `h` (Graph Minors XIII, Section 7, pages 88–89):
"A *wall of height $h$* (where $h \ge 2$ is even) is a subdivision of an elementary wall of height
$h$. It too therefore has four distinguished vertices, called its *corners*. A wall is thus a
pair $(H, P)$, where $H$ is a graph and $P \subseteq V(H)$ is
…
the set of corners, but for convenience we speak of a wall as a graph and leave the corners
implicit. The *perimeter* of a wall is defined as before." -/
structure Wall (α : Type u) (β : Type v) where
  /-- The underlying graph `H` of the wall. -/
  graph : Graph α β
  /-- The height `h` of the wall. -/
  height : ℕ
  /-- `h ≥ 2`. -/
  two_le_height : 2 ≤ height
  /-- `h` is even. -/
  even_height : Even height
  /-- The base graph `H₀` of branch vertices and virtual edges inside `α, β`. -/
  baseGraph : Graph α β
  /-- The isomorphism between the canonical elementary wall of height `h` and `baseGraph`. -/
  baseIso : Iso (elementaryWall height) baseGraph
  /-- The subdivision path `P_e ≤ graph` for each edge `e ∈ E(baseGraph)`. -/
  subdivisionPaths : β → Graph α β
  /-- `V(baseGraph) ⊆ V(graph)`. -/
  base_verts_subset : V(baseGraph) ⊆ V(graph)
  /-- Each edge `e ∈ E(baseGraph)` with ends `u, v` is subdivided by a non-empty path `P_e` of
  `graph` between `u` and `v` meeting `V(baseGraph)` only at `{u, v}`. -/
  path_of_edge : ∀ e ∈ E(baseGraph), ∃ u v : α,
    baseGraph.IsLink e u v ∧ IsGraphPathWithEnds graph (subdivisionPaths e) u v ∧
    E(subdivisionPaths e).Nonempty ∧ V(subdivisionPaths e) ∩ V(baseGraph) = {u, v}
  /-- Subdivision paths of distinct edges of `baseGraph` are edge-disjoint and internally
  vertex-disjoint. -/
  paths_disjoint : ∀ e₁ ∈ E(baseGraph), ∀ e₂ ∈ E(baseGraph), e₁ ≠ e₂ →
    Disjoint E(subdivisionPaths e₁) E(subdivisionPaths e₂) ∧
    V(subdivisionPaths e₁) ∩ V(subdivisionPaths e₂) ⊆ V(baseGraph)
  /-- `V(graph)` is the union of `V(baseGraph)` and the vertices of all subdivision paths. -/
  vertexSet_eq : V(graph) = V(baseGraph) ∪ ⋃ e ∈ E(baseGraph), V(subdivisionPaths e)
  /-- `E(graph)` is the union of the edges of all subdivision paths. -/
  edgeSet_eq : E(graph) = ⋃ e ∈ E(baseGraph), E(subdivisionPaths e)

namespace Wall

variable {α : Type u} {β : Type v} (W : Wall α β)

/-- Every `W : Wall α β` satisfies `GM14.IsSubdivisionOf W.graph W.baseGraph`. -/
theorem isSubdivisionOf : IsSubdivisionOf W.graph W.baseGraph :=
  ⟨W.base_verts_subset, W.subdivisionPaths, W.path_of_edge, W.paths_disjoint,
    W.vertexSet_eq, W.edgeSet_eq⟩

/-- The branch vertex in `V(W.graph)` corresponding to a coordinate `p ∈ elementaryWallVerts h`. -/
def branchVertex (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height) : α :=
  (W.baseIso.vertexEquiv ⟨p, hp⟩).1

/-- The four corners of the wall `W` in cyclic order around the perimeter
(Graph Minors XIII, Section 7, pages 88–89). -/
def corner (k : Fin 4) : α :=
  have hp : elementaryWallCorner W.height k ∈ elementaryWallVerts W.height := by
    have h2 := W.two_le_height
    fin_cases k <;> simp [elementaryWallCorner, elementaryWallVerts] <;> omega
  W.branchVertex (elementaryWallCorner W.height k) hp

/-- The set of four corners of `W` (Graph Minors XIII, Section 7, pages 88–89). -/
def corners : Set α :=
  Set.range W.corner

/-- The perimeter subgraph `C` of the wall `W` (Graph Minors XIII, Section 7, page 89). -/
def perimeter : Graph α β :=
  subgraphSUnion W.graph
    {P : Graph α β | ∃ (e₀ : Sym2 (ℕ × ℕ)) (he₀ : e₀ ∈ E(elementaryWallPerimeter W.height)),
      have he₀' : e₀ ∈ E(elementaryWall W.height) :=
        let ⟨p, q, hpq⟩ := he₀; ⟨p, q, hpq.1.1, hpq.1.2⟩
      P = W.subdivisionPaths (W.baseIso.edgeEquiv ⟨e₀, he₀'⟩).1}

/-- The vertices strictly inside the perimeter of `W` (Graph Minors XIII, Section 9, page 98:
“It follows that if $H'$ is a subwall of $H$, then $H'$ consists of its perimeter $C$ together with
the portion of $H$ inside $C$.”). -/
def insideVerts : Set α :=
  V(W.graph) \ V(W.perimeter)

/-- The first middle vertex of the wall `W` (Graph Minors XIII, Section 10, page 107:
“(The middle vertices of a wall are the two vertices corresponding to the two middle vertices of the
elementary wall of which the wall is a subdivision.)”). -/
def middleVertex₁ : α :=
  have hp : elementaryWallMiddle₁ W.height ∈ elementaryWallVerts W.height := by
    have h2 := W.two_le_height
    dsimp [elementaryWallMiddle₁, elementaryWallVerts]
    refine ⟨by omega, Nat.div_le_self _ _, ?_, ?_⟩
    · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    · intro h; have := congrArg Prod.fst h; dsimp at this; omega
  W.branchVertex (elementaryWallMiddle₁ W.height) hp

/-- The second middle vertex of the wall `W` (Graph Minors XIII, Section 10, page 107). -/
def middleVertex₂ : α :=
  have hp : elementaryWallMiddle₂ W.height ∈ elementaryWallVerts W.height := by
    have h2 := W.two_le_height
    dsimp [elementaryWallMiddle₂, elementaryWallVerts]
    refine ⟨by omega, Nat.div_le_self _ _, ?_, ?_⟩
    · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    · intro h; have := congrArg Prod.fst h; dsimp at this; omega
  W.branchVertex (elementaryWallMiddle₂ W.height) hp

/-- The set of two middle vertices of `W` (Graph Minors XIII, Section 10, page 107). -/
def middleVertices : Set α :=
  {W.middleVertex₁, W.middleVertex₂}

end Wall

/-- `H` is a wall of height `h` if there is a `Wall α β` structure with `W.graph = H` and
`W.height = h` (Graph Minors XIII, Section 7, pages 88–89). -/
def IsWallOfHeight {α : Type u} {β : Type v} (H : Graph α β) (h : ℕ) : Prop :=
  ∃ W : Wall α β, W.graph = H ∧ W.height = h

/-- `W` is a wall in a graph `G` (Graph Minors XIII, Section 7, page 90):
"Let $G$ be a graph. A *wall in* $G$ is a subgraph of $G$ which is a wall." -/
def IsWallIn {α : Type u} {β : Type v} (G : Graph α β) (W : Wall α β) : Prop :=
  W.graph ≤ G

/-- The distance function `d(s, t)` on the plane `EuclideanPlane` determined by the point set
`U ⊆ EuclideanPlane` of a plane drawing of a wall `H` (Graph Minors XIII, Section 7, pages 89–90):
"If $H$ is a wall, drawn in the plane as in Fig. 1, its *distance function* $d$ is defined as
follows. For $s, t$ in the plane, $d(s, t) = 0$ if $s = t$, and otherwise
…
$d(s, t)$ is the minimum of the number of points of $F$ in the drawing, taken over all subsets
$F$ in the plane homeomorphic to $[0, 1]$ with ends $s$ and $t$." -/
noncomputable def planeWallDist (U : Set EuclideanPlane) (s t : EuclideanPlane) : ℕ :=
  if s = t then 0
  else sInf {k : ℕ | ∃ F : Set EuclideanPlane,
    IsLineWithEnds F s t ∧ (F ∩ U).Finite ∧ (F ∩ U).ncard = k}

/-- Comparison `d' ≥ d - k` of two wall distance functions on the plane
(Graph Minors XIII, Section 7, page 90):
"If $d'(s, t) \ge d(s, t) - k$ for all points $s, t$ of the plane, we write $d' \ge d - k$." -/
def DistGeSub (d' d : EuclideanPlane → EuclideanPlane → ℕ) (k : ℕ) : Prop :=
  ∀ s t : EuclideanPlane, d s t ≤ d' s t + k

/-- A wall `W` equipped with its plane drawing point set `U` and vertex embedding
`ν : α → EuclideanPlane`, inducing both the plane distance function `planeDist` and the vertex
distance function `d(u, v) = d(ν(u), ν(v))` (Graph Minors XIII, Section 7, pages 89–90). -/
structure DrawnWall (α : Type u) (β : Type v) extends Wall α β where
  /-- The point set `U(H)` of the plane drawing of `W.graph`. -/
  drawingU : Set EuclideanPlane
  /-- The point `ν(u) ∈ U(H)` representing each vertex `u ∈ V(W.graph)` in the plane drawing. -/
  vertexPoint : α → EuclideanPlane
  /-- Every vertex of `W.graph` maps into `drawingU`. -/
  vertexPoint_mem : ∀ ⦃u : α⦄, u ∈ V(graph) → vertexPoint u ∈ drawingU
  /-- `vertexPoint` is injective on `V(W.graph)`. -/
  vertexPoint_injOn : InjOn vertexPoint V(graph)

namespace DrawnWall

variable {α : Type u} {β : Type v} (W : DrawnWall α β)

/-- The plane distance function `d(s, t)` of `W` (Graph Minors XIII, Section 7, pages 89–90). -/
noncomputable def planeDist (s t : EuclideanPlane) : ℕ :=
  planeWallDist W.drawingU s t

/-- The vertex distance function `d(u, v) = d(s, t)` for `u, v ∈ V(H)`
(Graph Minors XIII, Section 7, page 90:
"If $u, v \in V(H)$, we define $d(u, v) = d(s, t)$, where $s, t$ are the points of the drawing
representing $u, v$."). -/
noncomputable def dist (u v : α) : ℕ :=
  W.planeDist (W.vertexPoint u) (W.vertexPoint v)

end DrawnWall

/-- An `(l, m)`-star `S = P₁ ∪ ⋯ ∪ P_l` over a wall `H` in `G` with center `v`
(Graph Minors XIII, Section 7, pages 90–91):
"Let $H$ be a wall in $G$. For $l \ge 3$, $m \ge 0$ an $(l, m)$-*star over* $H$ in $G$ is a
subgraph $P_1 \cup \dots \cup P_l$ of $G$ such that for some vertex $v$,
…
(i) $P_1, \dots, P_l$ are paths of $G$ and all have one end $v$, and are otherwise mutually
vertex-disjoint

(ii) for $1 \le i \le l$, let the ends of $P_i$ be $v, u_i$; then $u_i \ne v$, and $u_i \in
V(H)$, and no edge or internal vertex of $P_i$ is in $H$

(iii) for $1 \le i < j \le l$, $u_i$ and $u_j$ are at distance $\ge m$ in $H$.

We say that $v$ is the *center* of the star. (It is unique.) The star is *external* if $v \notin
V(H)$." -/
structure IsLMStarOver {α : Type u} {β : Type v}
    (G : Graph α β) (W : DrawnWall α β) (l m : ℕ) (S : Graph α β) (v : α) : Prop where
  /-- `l ≥ 3`. -/
  three_le_l : 3 ≤ l
  /-- `W` is a wall in `G`. -/
  wall_le : W.graph ≤ G
  /-- `v ∈ V(G)`. -/
  center_mem : v ∈ V(G)
  /-- There exist paths `P₁, …, P_l` and ends `u₁, …, u_l ∈ V(H)` whose union is `S`. -/
  exists_paths : ∃ (P : Fin l → Graph α β) (u : Fin l → α),
    S = subgraphSUnion G (Set.range P) ∧
    (∀ i : Fin l, IsGraphPathWithEnds G (P i) v (u i) ∧ u i ≠ v ∧ u i ∈ V(W.graph) ∧
      V(P i) ∩ V(W.graph) ⊆ {v, u i} ∧ Disjoint E(P i) E(W.graph)) ∧
    (∀ i j : Fin l, i ≠ j → V(P i) ∩ V(P j) = {v}) ∧
    (∀ i j : Fin l, i ≠ j → m ≤ W.dist (u i) (u j))

/-- An `(l, m)`-star over `H` in `G` with center `v` is external if `v ∉ V(H)`
(Graph Minors XIII, Section 7, page 91: "The star is *external* if $v \notin V(H)$."). -/
def IsExternalLMStarOver {α : Type u} {β : Type v}
    (G : Graph α β) (W : DrawnWall α β) (l m : ℕ) (S : Graph α β) (v : α) : Prop :=
  IsLMStarOver G W l m S v ∧ v ∉ V(W.graph)

/-! ## Section 8: The 2-Paths Problem, Cores, and Rural Divisions (pages 93–97) -/

/-- `C` is a cross subgraph `P ∪ Q` in a society `(G, Ω)` (Graph Minors XIII, Section 8, page 93):
“A *cross* in a society $(G, \Omega)$ is a subgraph $P \cup Q$ of $G$, where $P, Q$ are
vertex-disjoint paths of $G$ with ends $p_1, p_2$ and $q_1, q_2$, respectively, and
$p_1, q_1, p_2, q_2 \in \bar{\Omega}$ and occur in this order or its reverse under $\Omega$.” -/
def IsCrossSubgraph {α : Type u} {β : Type v} (S : Society α β) (C : Graph α β) : Prop :=
  ∃ P Q : Graph α β, S.IsCross P Q ∧ C = subgraphUnion S.G P Q

/-- A society `(G, Ω)` has a cross (Graph Minors XIII, Section 8, page 93). -/
def HasCross {α : Type u} {β : Type v} (S : Society α β) : Prop :=
  ∃ P Q : Graph α β, S.IsCross P Q

/-- A subset `Z ⊆ V(G)` is trisecting in a society `(G, Ω)`
(Graph Minors XIII, Section 8, page 93):
“Let $(G, \Omega)$ be a society. A subset $Z \subseteq V(G)$ is *trisecting* if
$\bar{\Omega} \subseteq Z$, and for every $v \in V(G) - Z$ there are $\le 3$ vertices $z \in Z$ such
that there is a path of $G$ between $v$ and $z$ with no other vertex in $Z$. Thus, $V(G)$ is always
trisecting.” -/
structure IsTrisecting {α : Type u} {β : Type v} (S : Society α β) (Z : Set α) : Prop where
  /-- `Z ⊆ V(G)`. -/
  subset_V : Z ⊆ V(S.G)
  /-- `Ω̄ ⊆ Z`. -/
  bar_subset : S.Ω.bar ⊆ Z
  /-- For every `v ∈ V(G) \ Z`, at most 3 vertices `z ∈ Z` are reachable from `v` by a path in `G`
  meeting `Z` only at `z`. -/
  attach_ncard_le_three : ∀ v ∈ V(S.G) \ Z,
    {z ∈ Z | ∃ P : Graph α β, IsGraphPathWithEnds S.G P v z ∧ V(P) ∩ Z = {z}}.ncard ≤ 3

/-- A simple graph `C` is a core in `(G, Ω)` (Graph Minors XIII, Section 8, pages 93–94):
"A *core* $C$ in $(G, \Omega)$ is a simple graph with vertex set a trisecting subset $Z \subseteq
V(G)$, in which distinct $u, v \in Z$ are adjacent if and only if there is a
…
path in $G$ between $u$ and $v$ with no internal vertex in $Z$. (Note that $E(C) \not\subseteq
E(G)$ in general.)" -/
structure IsCoreOf {α : Type u} {β : Type v} {β' : Type*}
    (S : Society α β) (C : Graph α β') : Prop where
  /-- `C` is a simple graph. -/
  isSimple : IsSimpleGraph C
  /-- `E(C)` is finite. -/
  finite_E : E(C).Finite
  /-- `V(C)` is a trisecting subset of `(G, Ω)`. -/
  isTrisecting : IsTrisecting S V(C)
  /-- Distinct `u, v ∈ V(C)` are adjacent in `C` if and only if there is a path in `G` between `u`
  and `v` with no internal vertex in `V(C)`. -/
  adj_iff : ∀ u ∈ V(C), ∀ v ∈ V(C), u ≠ v →
    (C.Adj u v ↔ ∃ P : Graph α β, IsGraphPathWithEnds S.G P u v ∧ V(P) ∩ V(C) = {u, v})

/-- A vertex `v ∈ V(C)` is 4-linked in `C` (with respect to `Ω̄`)
(Graph Minors XIII, Section 8, page 94):
“If $C$ is a core, we say $v \in V(C)$ is 4-linked in $C$ if there is no separation $(A, B)$ of $C$
of order $\le 3$ with $v \in V(A) - V(B)$ and $\tilde{\Omega} \subseteq V(B)$. A core $C$ is
4-linked if every $v \in V(C)$ is 4-linked in $C$.” -/
def IsFourLinkedVertexIn {α : Type u} {β : Type v} {β' : Type*}
    (S : Society α β) (C : Graph α β') (v : α) : Prop :=
  v ∈ V(C) ∧
    ∀ A B : Graph α β', IsGraphSeparation C A B →
      (V(A) ∩ V(B)).ncard ≤ 3 → S.Ω.bar ⊆ V(B) → v ∉ V(A) \ V(B)

/-- A core `C` of `(G, Ω)` is 4-linked (Graph Minors XIII, Section 8, page 94). -/
structure IsFourLinkedCore {α : Type u} {β : Type v} {β' : Type*}
    (S : Society α β) (C : Graph α β') : Prop where
  /-- `C` is a core of `(G, Ω)`. -/
  isCore : IsCoreOf S C
  /-- Every `v ∈ V(C)` is 4-linked in `C`. -/
  fourLinked : ∀ v ∈ V(C), IsFourLinkedVertexIn S C v

/-- Given a core `C` of a society `(G, Ω)`, the core society `(C, Ω)`. -/
def coreSociety {α : Type u} {β : Type v} {β' : Type*}
    (S : Society α β) (C : Graph α β') (hC : IsCoreOf S C) : Society α β' where
  G := C
  Ω := S.Ω
  finite_V := S.finite_V.subset hC.isTrisecting.subset_V
  finite_E := hC.finite_E
  bar_subset := hC.isTrisecting.bar_subset

/-- The boundary `∂A` of a subgraph `A` of `G` in a society `(G, Ω)`
(Graph Minors XIII, Section 8, page 95):
“Let $(G, \Omega)$ be a society. For a subgraph $A$ of $G$ we define $\partial A$ to be the set of
all $v \in V(A)$ such that either $v \in \tilde{\Omega}$ or $v$ is incident with an edge of $G$ not
in $A$.” -/
def divBoundary {α : Type u} {β : Type v} (S : Society α β) (A : Graph α β) : Set α :=
  {v ∈ V(A) | v ∈ S.Ω.bar ∨ ∃ e ∈ E(S.G) \ E(A), S.G.Inc e v}

/-- `∂𝒜 = ⋃ (∂A : A ∈ 𝒜)` (Graph Minors XIII, Section 8, page 96). -/
def divTotalBoundary {α : Type u} {β : Type v}
    (S : Society α β) (𝒜 : Set (Graph α β)) : Set α :=
  ⋃ A ∈ 𝒜, divBoundary S A

/-- A division `𝒜` of a society `(G, Ω)` (Graph Minors XIII, Section 8, pages 95–96):
"A division of $(G, \Omega)$ is a set $\mathcal{A}$ of subgraphs of $G$ such that

(i) $\bigcup(A : A \in \mathcal{A}) = G$

(ii) for all distinct $A, A' \in \mathcal{A}$, $E(A \cap A') = \emptyset$ and $V(A \cap A') =
\partial A \cap \partial A'$
…
(iii) for each $A \in \mathcal{A}$, $|\partial A| \le 3$ and there are $|\partial A|$ mutually
vertex-disjoint paths of $G$ between $\partial A$ and $\tilde{\Omega}$

(iv) for each $A \in \mathcal{A}$ and all $u, v \in \partial A$, there is a path of $A$ between
$u$ and $v$ with no internal vertex in $\partial A$

(v) if $A, A' \in \mathcal{A}$ are distinct then $\partial A \ne \partial A'$

(vi) for each $A \in \mathcal{A}$, some vertex or edge of $A$ belongs to no other member of
$\mathcal{A}$." -/
structure IsSocietyDivision {α : Type u} {β : Type v}
    (S : Society α β) (𝒜 : Set (Graph α β)) : Prop where
  /-- Every member of `𝒜` is a subgraph of `G`. -/
  sub_of_mem : ∀ ⦃A : Graph α β⦄, A ∈ 𝒜 → A ≤ S.G
  /-- (i) `⋃ (A : A ∈ 𝒜) = G`. -/
  sUnion_eq : subgraphSUnion S.G 𝒜 = S.G
  /-- (ii) For all distinct `A, A' ∈ 𝒜`, `E(A ∩ A') = ∅`. -/
  edge_disjoint : ∀ ⦃A A' : Graph α β⦄, A ∈ 𝒜 → A' ∈ 𝒜 → A ≠ A' → Disjoint E(A) E(A')
  /-- (ii) For all distinct `A, A' ∈ 𝒜`, `V(A ∩ A') = ∂A ∩ ∂A'`. -/
  vertex_inter_eq : ∀ ⦃A A' : Graph α β⦄, A ∈ 𝒜 → A' ∈ 𝒜 → A ≠ A' →
    V(A) ∩ V(A') = divBoundary S A ∩ divBoundary S A'
  /-- (iii) For each `A ∈ 𝒜`, `|∂A| ≤ 3`. -/
  boundary_ncard_le_three : ∀ ⦃A : Graph α β⦄, A ∈ 𝒜 → (divBoundary S A).ncard ≤ 3
  /-- (iii) For each `A ∈ 𝒜`, there are `|∂A|` mutually vertex-disjoint paths of `G` between `∂A`
  and `Ω̄`. -/
  disjoint_paths_to_bar : ∀ ⦃A : Graph α β⦄, A ∈ 𝒜 →
    ∃ P : Fin (divBoundary S A).ncard → Graph α β,
      Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      ∀ i : Fin (divBoundary S A).ncard,
        ∃ s ∈ divBoundary S A, ∃ t ∈ S.Ω.bar, IsGraphPathWithEnds S.G (P i) s t
  /-- (iv) For each `A ∈ 𝒜` and all `u, v ∈ ∂A`, there is a path of `A` between `u` and `v` with no
  internal vertex in `∂A`. -/
  internal_path : ∀ ⦃A : Graph α β⦄, A ∈ 𝒜 → ∀ u ∈ divBoundary S A, ∀ v ∈ divBoundary S A,
    ∃ P : Graph α β, IsGraphPathWithEnds A P u v ∧ V(P) ∩ divBoundary S A ⊆ {u, v}
  /-- (v) If `A, A' ∈ 𝒜` are distinct then `∂A ≠ ∂A'`. -/
  boundary_injOn : InjOn (divBoundary S) 𝒜
  /-- (vi) For each `A ∈ 𝒜`, some vertex or edge of `A` belongs to no other member of `𝒜`. -/
  has_private_element : ∀ ⦃A : Graph α β⦄, A ∈ 𝒜 →
    (∃ v ∈ V(A), ∀ A' ∈ 𝒜, A' ≠ A → v ∉ V(A')) ∨
    (∃ e ∈ E(A), ∀ A' ∈ 𝒜, A' ≠ A → e ∉ E(A'))

/-- The bipartite graph `G'` with vertex set `𝒜 ∪ ∂𝒜` in which `A ∈ 𝒜` is adjacent to `v ∈ ∂𝒜` if
`v ∈ ∂A` (Graph Minors XIII, Section 8, page 96). -/
def divisionBipartiteGraph {α : Type u} {β : Type v}
    (S : Society α β) (𝒜 : Set (Graph α β)) : Graph (Graph α β ⊕ α) (Graph α β × α) where
  vertexSet := (Sum.inl '' 𝒜) ∪ (Sum.inr '' (divTotalBoundary S 𝒜 ∪ S.Ω.bar))
  edgeSet := {p : Graph α β × α | p.1 ∈ 𝒜 ∧ p.2 ∈ divBoundary S p.1}
  IsLink p x y :=
    p.1 ∈ 𝒜 ∧ p.2 ∈ divBoundary S p.1 ∧
      ((x = Sum.inl p.1 ∧ y = Sum.inr p.2) ∨ (x = Sum.inr p.2 ∧ y = Sum.inl p.1))
  isLink_symm p _ := ⟨fun x y ⟨h1, h2, h3⟩ => by
    refine ⟨h1, h2, ?_⟩
    rcases h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩⟩
  eq_or_eq_of_isLink_of_isLink p x y z w h1 h2 := by
    rcases h1.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  edge_mem_iff_exists_isLink p :=
    ⟨fun ⟨h1, h2⟩ => ⟨Sum.inl p.1, Sum.inr p.2, h1, h2, Or.inl ⟨rfl, rfl⟩⟩,
      fun ⟨_, _, h1, h2, _⟩ => ⟨h1, h2⟩⟩
  left_mem_of_isLink p x y h := by
    rcases h.2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl ⟨p.1, h.1, rfl⟩
    · exact Or.inr ⟨p.2, Or.inl (Set.mem_biUnion h.1 h.2.1), rfl⟩

/-- The cyclic permutation `Ω` transported along `Sum.inr` to `Graph α β ⊕ α`. -/
noncomputable def liftCyclicPermInr {α : Type u} {γ : Type w} (Ω : CyclicPerm α) :
    CyclicPerm (γ ⊕ α) where
  bar := Sum.inr '' Ω.bar
  toFun x := match x with
    | Sum.inl g => Sum.inl g
    | Sum.inr a => Sum.inr (Ω a)
  finite_bar := Ω.finite_bar.image Sum.inr
  bijOn := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨Ω a, Ω.bijOn.mapsTo ha, rfl⟩
    · rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨a₂, ha₂, rfl⟩ h
      simp only [Sum.inr.injEq] at h ⊢
      exact Ω.bijOn.injOn ha₁ ha₂ h
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨a, ha, rfl⟩ := Ω.bijOn.surjOn hb
      exact ⟨Sum.inr a, ⟨a, ha, rfl⟩, rfl⟩
  single_orbit := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨k, hk⟩ := Ω.single_orbit a ha b hb
    refine ⟨k, ?_⟩
    have hiter : ∀ n : ℕ,
        ((fun x : γ ⊕ α => match x with | Sum.inl g => Sum.inl g | Sum.inr c => Sum.inr (Ω c))^[n])
          (Sum.inr a) = Sum.inr ((Ω.toFun^[n]) a) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    rw [hiter k, hk]

/-- A division `𝒜` of `(G, Ω)` is rural (Graph Minors XIII, Section 8, page 96):
“If $\mathcal{A}$ is a division, we write $\partial\mathcal{A} = \bigcup(\partial A : A \in \mathcal{A})$.
Thus, $\tilde{\Omega} \subseteq \partial\mathcal{A}$. We say a division $\mathcal{A}$ of $(G, \Omega)$
is *rural* if $(G', \Omega)$ is rural, where $G'$ is the bipartite graph with vertex set
$\mathcal{A} \cup \partial\mathcal{A}$ in which $A \in \mathcal{A}$ is adjacent to
$v \in \partial\mathcal{A}$ if $v \in \partial A$.” -/
structure IsRuralDivision {α : Type u} {β : Type v}
    (S : Society α β) (𝒜 : Set (Graph α β)) : Prop where
  /-- `𝒜` is a division of `(G, Ω)`. -/
  isDivision : IsSocietyDivision S 𝒜
  /-- `𝒜` is finite (since each `A ∈ 𝒜` has a private vertex or edge in the finite graph `S.G`). -/
  finite_𝒜 : 𝒜.Finite
  /-- The bipartite society `(G', Ω)` is rural. -/
  isRuralBipartite :
    ∃ (hV : V(divisionBipartiteGraph S 𝒜).Finite)
      (hE : E(divisionBipartiteGraph S 𝒜).Finite)
      (hbar : (liftCyclicPermInr S.Ω).bar ⊆ V(divisionBipartiteGraph S 𝒜)),
      (Society.mk (divisionBipartiteGraph S 𝒜) (liftCyclicPermInr S.Ω) hV hE hbar).IsRuralSociety

/-! ## Section 9: Subwalls, Dividing Subwalls, Compasses, and Flat Walls (pages 97–106) -/

/-- The coordinate shift `(x, y) ↦ (x + i, y + j)` used in the definition of a subwall
(Graph Minors XIII, Section 9, pages 97–98). -/
def wallShift (i j : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 + i, p.2 + j)

/-- A wall `W'` is a subwall of a wall `W` (Graph Minors XIII, Section 9, pages 97–98):
"Let $h'$ be even with $2 \le h' \le h$, choose $i, j$, even, with $0 \le i \le 2h - 2h'$ and $0
\le j \le h - h'$, and let $J'$ be the subgraph of $J$ induced on the vertex set

$$\{(x, y) : i \le x \le i + 2h' + 1, j \le y \le j + h'\} - \{(i, j), (i + 2h' + 1, j + h')\}$$
…
with corners $(i+1, j)$, $(i+2h'+1, j)$, $(i, j+h')$, $(i+2h, j+h')$. Then $J'$ is an elementary
wall of height $h'$. Now let $H$ be a subdivision of $J$, and let $H'$ be the corresponding
subdivision of $J'$; we say that the wall $H'$ is a *subwall* of $H$." -/
structure Wall.IsSubwallOf {α : Type u} {β : Type v} (W' W : Wall α β) : Prop where
  /-- `h' ≤ h`. -/
  height_le : W'.height ≤ W.height
  /-- There exist even offsets `i, j` with `i ≤ 2h - 2h'` and `j ≤ h - h'` such that `W'` is the
  subdivision of the shifted elementary wall `J'` inside `W`. -/
  exists_shift : ∃ i j : ℕ, Even i ∧ Even j ∧
    i ≤ 2 * W.height - 2 * W'.height ∧ j ≤ W.height - W'.height ∧
    (∀ (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts W'.height)
       (hp : wallShift i j p ∈ elementaryWallVerts W.height),
      W'.branchVertex p hp' = W.branchVertex (wallShift i j p) hp) ∧
    W'.subdivisionPaths = W.subdivisionPaths ∧
    W'.baseGraph = W.baseGraph.induce
      ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height |
          ∃ q ∈ elementaryWallVerts W'.height, p.1 = wallShift i j q})

/-- The distance `d(H₁, H₂)` between two subgraphs `H₁, H₂` of a wall `W`
(Graph Minors XIII, Section 9, page 98):
“If $H$ is a wall, and $H_1, H_2$ are non-null subgraphs of $H$, we define $d(H_1, H_2)$ to be the
minimum of $d(v_1, v_2)$ over all $v_1 \in V(H_1)$ and $v_2 \in V(H_2)$, where $d$ is the distance
function of $H$.” -/
noncomputable def wallSubgraphDist {α : Type u} {β : Type v}
    (W : DrawnWall α β) (H₁ H₂ : Graph α β) : ℕ :=
  sInf {k : ℕ | ∃ v₁ ∈ V(H₁), ∃ v₂ ∈ V(H₂), W.dist v₁ v₂ = k}

/-- A cross `P ∪ Q` over a wall `W` in `G` (Graph Minors XIII, Section 9, page 98):
“Let $H$ be a wall in a graph $G$, and let $p_1, p_2, p_3, p_4$ be the corners of $H$, in cyclic
order. A *cross over* $H$ in $G$ is a subgraph $P \cup Q$, where $P, Q$ are mutually vertex-disjoint
paths of $G$ with ends $p_1, p_3$ and $p_2, p_4$, respectively.” -/
def IsCrossOverWall {α : Type u} {β : Type v}
    (G : Graph α β) (W : Wall α β) (P Q : Graph α β) : Prop :=
  Disjoint V(P) V(Q) ∧
    IsGraphPathWithEnds G P (W.corner 0) (W.corner 2) ∧
    IsGraphPathWithEnds G Q (W.corner 1) (W.corner 3)

/-- A subwall `W'` of a wall `W` in `G` is dividing in `G` (Graph Minors XIII, Section 9, page 99):
“Let $H'$ be a subwall of a wall $H$ in a graph $G$. We say $H'$ is *dividing* if there is no
$H$-path in $G$ with one end inside $H'$ and the other end outside, and *non-dividing*
otherwise.” -/
def IsDividingSubwall {α : Type u} {β : Type v}
    (G : Graph α β) (W W' : Wall α β) : Prop :=
  W'.IsSubwallOf W ∧
    ∀ P a b, IsHPathWithEnds G W.graph P a b →
      ¬ (a ∈ W'.insideVerts ∧ b ∈ V(W.graph) \ V(W'.graph))

/-- A subwall `W'` of a wall `W` in `G` is non-dividing in `G`
(Graph Minors XIII, Section 9, page 99). -/
def IsNonDividingSubwall {α : Type u} {β : Type v}
    (G : Graph α β) (W W' : Wall α β) : Prop :=
  W'.IsSubwallOf W ∧
    ∃ P a b, IsHPathWithEnds G W.graph P a b ∧
      a ∈ W'.insideVerts ∧ b ∈ V(W.graph) \ V(W'.graph)

/-- The vertex set `W_compass` of the compass of a wall `H` in `G`: the union of `V(C)` (where `C`
is the perimeter of `H`) and the vertex set of the component of `G \ V(C)` containing `insideVerts`
(Graph Minors XIII, Section 9, page 102). -/
def wallCompassVerts {α : Type u} {β : Type v} (G : Graph α β) (W : Wall α β) : Set α :=
  V(W.perimeter) ∪
    {v ∈ V(G) \ V(W.perimeter) | ∃ u ∈ W.insideVerts,
      Nonempty (GraphWalk (deleteVertices G V(W.perimeter)) u v)}

/-- The compass of a wall `H` in `G` (Graph Minors XIII, Section 9, page 102):
“Let $H$ be a wall in a graph $G$, with perimeter $C$. Let $W \subseteq V(G)$ be the union of
$V(C)$ and the vertex set of the unique component of $G \setminus V(C)$ that contains a vertex of
$H$. We define the *compass* of $H$ in $G$ to be the restriction of $G$ to $W$. It follows that $H$
is a subgraph of its compass, and its compass is connected.” -/
def wallCompass {α : Type u} {β : Type v} (G : Graph α β) (W : Wall α β) : Graph α β :=
  G.induce (wallCompassVerts G W)

/-- A wall (or subwall) `W` in `G` is flat in `G` (Graph Minors XIII, Section 9, page 103):
“A subwall $H$ of $G$ is *flat* in $G$ if there is no cross $P \cup Q$ over $H$ such that
$P \cup Q$ is a subgraph of the compass of $H$ in $G$.” -/
def IsFlatWallIn {α : Type u} {β : Type v} (G : Graph α β) (W : Wall α β) : Prop :=
  W.graph ≤ G ∧ ¬ ∃ P Q : Graph α β, IsCrossOverWall (wallCompass G W) W P Q

/-- The four corners of a wall `W` are pairwise distinct. -/
theorem Wall.corner_injective {α : Type u} {β : Type v} (W : Wall α β) :
    Function.Injective W.corner := by
  intro i j h
  have h2 := W.two_le_height
  have hsub :
      W.baseIso.vertexEquiv ⟨elementaryWallCorner W.height i, _⟩ =
      W.baseIso.vertexEquiv ⟨elementaryWallCorner W.height j, _⟩ :=
    Subtype.ext h
  have heq := congrArg Subtype.val (W.baseIso.vertexEquiv.injective hsub)
  fin_cases i <;> fin_cases j <;> simp [elementaryWallCorner] at heq ⊢ <;> omega

/-- The cyclic permutation `Ω` of the four corners `W.corner 0, W.corner 1, W.corner 2, W.corner 3`
of a wall `W` corresponding to their cyclic order in the perimeter of `W`
(Graph Minors XIII, Section 9, pages 103–104). -/
noncomputable def wallCornerCyclicPerm {α : Type u} {β : Type v} (W : Wall α β) : CyclicPerm α where
  bar := W.corners
  toFun x :=
    if x = W.corner 0 then W.corner 1
    else if x = W.corner 1 then W.corner 2
    else if x = W.corner 2 then W.corner 3
    else if x = W.corner 3 then W.corner 0
    else x
  finite_bar := Set.finite_range W.corner
  bijOn := by
    have h01 : W.corner 0 ≠ W.corner 1 := W.corner_injective.ne (by decide)
    have h02 : W.corner 0 ≠ W.corner 2 := W.corner_injective.ne (by decide)
    have h03 : W.corner 0 ≠ W.corner 3 := W.corner_injective.ne (by decide)
    have h12 : W.corner 1 ≠ W.corner 2 := W.corner_injective.ne (by decide)
    have h13 : W.corner 1 ≠ W.corner 3 := W.corner_injective.ne (by decide)
    have h23 : W.corner 2 ≠ W.corner 3 := W.corner_injective.ne (by decide)
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [Wall.corners, Ne.symm h01, Ne.symm h02,
        Ne.symm h03, Ne.symm h12, Ne.symm h13, Ne.symm h23]
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
      fin_cases i <;> fin_cases j <;>
        simp [h01, h02, h03, h12, h13, h23, Ne.symm h01, Ne.symm h02, Ne.symm h03,
          Ne.symm h12, Ne.symm h13, Ne.symm h23] at hij ⊢
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · refine ⟨W.corner 3, ⟨3, rfl⟩, ?_⟩
        simp [Ne.symm h03, Ne.symm h13, Ne.symm h23]
      · refine ⟨W.corner 0, ⟨0, rfl⟩, ?_⟩
        simp
      · refine ⟨W.corner 1, ⟨1, rfl⟩, ?_⟩
        simp [Ne.symm h01]
      · refine ⟨W.corner 2, ⟨2, rfl⟩, ?_⟩
        simp [Ne.symm h02, Ne.symm h12]
  single_orbit := by
    have h01 : W.corner 0 ≠ W.corner 1 := W.corner_injective.ne (by decide)
    have h02 : W.corner 0 ≠ W.corner 2 := W.corner_injective.ne (by decide)
    have h03 : W.corner 0 ≠ W.corner 3 := W.corner_injective.ne (by decide)
    have h12 : W.corner 1 ≠ W.corner 2 := W.corner_injective.ne (by decide)
    have h13 : W.corner 1 ≠ W.corner 3 := W.corner_injective.ne (by decide)
    have h23 : W.corner 2 ≠ W.corner 3 := W.corner_injective.ne (by decide)
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    fin_cases i <;> fin_cases j
    · exact ⟨0, rfl⟩
    · refine ⟨1, ?_⟩; simp
    · refine ⟨2, ?_⟩; simp [Ne.symm h01]
    · refine ⟨3, ?_⟩; simp [Ne.symm h01, Ne.symm h02, Ne.symm h12]
    · refine ⟨3, ?_⟩; simp [Ne.symm h01, Ne.symm h02, Ne.symm h12, Ne.symm h03, Ne.symm h13, Ne.symm h23]
    · exact ⟨0, rfl⟩
    · refine ⟨1, ?_⟩; simp [Ne.symm h01]
    · refine ⟨2, ?_⟩; simp [Ne.symm h01, Ne.symm h02, Ne.symm h12]
    · refine ⟨2, ?_⟩; simp [Ne.symm h02, Ne.symm h12, Ne.symm h03, Ne.symm h13, Ne.symm h23]
    · refine ⟨3, ?_⟩; simp [Ne.symm h02, Ne.symm h12, Ne.symm h03, Ne.symm h13, Ne.symm h23]
    · exact ⟨0, rfl⟩
    · refine ⟨1, ?_⟩; simp [Ne.symm h02, Ne.symm h12]
    · refine ⟨1, ?_⟩; simp [Ne.symm h03, Ne.symm h13, Ne.symm h23]
    · refine ⟨2, ?_⟩; simp [Ne.symm h03, Ne.symm h13, Ne.symm h23]
    · refine ⟨3, ?_⟩; simp [Ne.symm h01, Ne.symm h03, Ne.symm h13, Ne.symm h23]
    · exact ⟨0, rfl⟩

/-- `S` is the society `(K, Ω)` of a wall `W` in `G` (Graph Minors XIII, Section 9, pages 103–104):
"Let $H$ be a wall in $G$. The *society* of $H$ in $G$ is the society $(K, \Omega)$, where $K$ is
the compass of $H$ in $G$ and $\Omega$ is the cyclic permutation of the corners
…
of $H$ corresponding to their order in the perimeter of $H$." -/
def IsWallSociety {α : Type u} {β : Type v}
    (G : Graph α β) (W : Wall α β) (S : Society α β) : Prop :=
  S.G = wallCompass G W ∧ S.Ω = wallCornerCyclicPerm W

/-- A member `A ∈ 𝒜` of a rural division `𝒜` of the society of `W` in `G` is interior if `A ∩ C` is
null, where `C` is the perimeter of `W` (Graph Minors XIII, Section 9, page 104):
“Let $\mathcal{A}$ be a rural division of the society of $H$ in $G$. We say that $A \in \mathcal{A}$
is *interior* if $A \cap C$ is null, where $C$ is the perimeter of $H$.” -/
def IsInteriorMember {α : Type u} {β : Type v}
    (W : Wall α β) (𝒜 : Set (Graph α β)) (A : Graph α β) : Prop :=
  A ∈ 𝒜 ∧ Disjoint V(A) V(W.perimeter)

/-! ## Section 10: Homogeneously Labelled Walls, Visions, and Statement (10.2) (pages 106–109) -/

/-- Hypothesis C (Graph Minors XIII, Section 10, page 106):
“Hypothesis C. *$G$ is a digraph, $X \subseteq V(G)$ with $|X| = q$, $H$ is a wall in
$G \setminus X$, and $\mathcal{A}$ is a rural division of the society of $H$ in $G \setminus X$.*” -/
structure HypothesisC {α : Type u} {β : Type v}
    (G : Digraph α β) (q : ℕ) (X : Set α) (H : Wall α β)
    (S_H : Society α β) (𝒜 : Set (Graph α β)) : Prop where
  /-- `G` is finite. -/
  isFinite : G.IsFinite
  /-- `X ⊆ V(G)`. -/
  X_subset : X ⊆ G.vertexSet
  /-- `|X| = q`. -/
  X_ncard : X.ncard = q
  /-- `H` is a wall in `G \ X`. -/
  wall_in : H.graph ≤ (G.deleteVertices X).toGraph
  /-- `S_H` is the society of `H` in `G \ X`. -/
  isWallSociety : IsWallSociety (G.deleteVertices X).toGraph H S_H
  /-- `𝒜` is a rural division of the society of `H` in `G \ X`. -/
  isRuralDivision : IsRuralDivision S_H 𝒜

/-- A list `sSeq = [s₁, …, s_k]` is a valid numbering of `∂A` for an interior member `A ∈ 𝒜` in a
society `S_H = (K, Ω)` (Graph Minors XIII, Section 10, page 106):
"Let $A \in \mathcal{A}$ be interior, and let $|\partial A| = k$; then $k \le 3$. Choose a
numbering $\{s_1, \dots, s_k\}$ of $\partial A$, where if $k = 3$ we number "clockwise;" that is,
we number $s_1, s_2, s_3$ so that there are three paths $P_1, P_2, P_3$ of $K$ from $\partial A$
to $\bar{\Omega}$, mutually vertex-disjoint, where $P_i$ has ends $s_i, t_i$ ($i = 1, 2, 3$), and
$t_1, t_2, t_3$ occur in this order under $\Omega$. Let $X = \{x_1, \dots, x_r\}$; the sequence
$(s_1, \dots, s_k, x_1, \dots, x_r)$ is called an *attachment sequence* of $A$, and we denote it
by $\pi(A)$." -/
def IsClockwiseBoundaryNumbering {α : Type u} {β : Type v}
    (S_H : Society α β) (A : Graph α β) (sSeq : List α) : Prop :=
  sSeq.Nodup ∧ {x : α | x ∈ sSeq} = divBoundary S_H A ∧
    ∀ (s₁ s₂ s₃ : α), sSeq = [s₁, s₂, s₃] →
      ∃ (P₁ P₂ P₃ : Graph α β) (t₁ t₂ t₃ : α),
        Disjoint V(P₁) V(P₂) ∧ Disjoint V(P₁) V(P₃) ∧ Disjoint V(P₂) V(P₃) ∧
        IsGraphPathWithEnds S_H.G P₁ s₁ t₁ ∧ V(P₁) ∩ divBoundary S_H A = {s₁} ∧
        V(P₁) ∩ S_H.Ω.bar = {t₁} ∧
        IsGraphPathWithEnds S_H.G P₂ s₂ t₂ ∧ V(P₂) ∩ divBoundary S_H A = {s₂} ∧
        V(P₂) ∩ S_H.Ω.bar = {t₂} ∧
        IsGraphPathWithEnds S_H.G P₃ s₃ t₃ ∧ V(P₃) ∩ divBoundary S_H A = {s₃} ∧
        V(P₃) ∩ S_H.Ω.bar = {t₃} ∧
        S_H.Ω.IsClockwise3 t₁ t₂ t₃

/-- `π = (s₁, …, s_k, x₁, …, x_r)` is an attachment sequence of `A` with respect to an ordering
`xSeq = [x₁, …, x_r]` of `X` (Graph Minors XIII, Section 10, page 106). -/
def IsAttachmentSequence {α : Type u} {β : Type v}
    (S_H : Society α β) (X : Set α) (xSeq : List α) (A : Graph α β) (π : List α) : Prop :=
  xSeq.Nodup ∧ {x : α | x ∈ xSeq} = X ∧
    ∃ sSeq : List α, IsClockwiseBoundaryNumbering S_H A sSeq ∧ π = sSeq ++ xSeq

/-- A vision under Hypothesis C (Graph Minors XIII, Section 10, page 106):
“For each $A \in \mathcal{A}$, choose a subgraph $\tilde{A}$ of $G$ with $X \subseteq V(\tilde{A})$
and with $\tilde{A} \setminus X = A$, such that every edge of $G$ with both ends in
$X \cup V(K)$ is in $E(\tilde{A})$ for exactly one $A \in \mathcal{A}$. Let $T_A$ be the
$\delta$-folio of $(\tilde{A}, \pi(A))$. Now for each interior $A \in \mathcal{A}$, let
$v(A) \in V(H)$ such that there is a path of $K$ from $\partial A$ to $v(A)$ with no vertex in
$V(H)$ except $v(A)$. (Such a path always exists since $K$ is connected and $A$ is non-null.) This
information (that is, for each interior $A \in \mathcal{A}$, a choice of $\tilde{A}$, an attachment
sequence $\pi(A)$ of $A$, the $\delta$-folio of $(\tilde{A}, \pi(A))$, and a vertex $v(A)$) is
called a *vision*.” -/
structure Vision {α : Type u} {β : Type v}
    (G : Digraph α β) (X : Set α) (H : Wall α β)
    (S_H : Society α β) (𝒜 : Set (Graph α β)) where
  /-- The fixed ordering `[x₁, …, x_q]` of `X`. -/
  xSeq : List α
  /-- `xSeq` has no duplicates. -/
  xSeq_nodup : xSeq.Nodup
  /-- The elements of `xSeq` are `X`. -/
  xSeq_set : {x : α | x ∈ xSeq} = X
  /-- For each `A ∈ 𝒜`, the subdigraph `Ã` of `G`. -/
  tildeA : Graph α β → Digraph α β
  /-- For each `A ∈ 𝒜`, `Ã` is a subdigraph of `G` with `X ⊆ V(Ã)` and `(Ã \ X).toGraph = A`. -/
  tildeA_valid : ∀ ⦃A : Graph α β⦄, A ∈ 𝒜 →
    (tildeA A).IsSubdigraph G ∧
    X ⊆ (tildeA A).vertexSet ∧
    ((tildeA A).deleteVertices X).toGraph = A
  /-- Every edge of `G` with both ends in `X ∪ V(K)` is in `E(Ã)` for a unique `A ∈ 𝒜`. -/
  edge_partition : ∀ ⦃e : β⦄, e ∈ G.edgeSet →
    G.head e ∈ X ∪ V(S_H.G) → G.tail e ∈ X ∪ V(S_H.G) →
    ∃! A : Graph α β, A ∈ 𝒜 ∧ e ∈ (tildeA A).edgeSet
  /-- For each interior `A ∈ 𝒜`, the clockwise numbering `sSeq(A)` of `∂A`. -/
  sSeq : Graph α β → List α
  /-- For each interior `A ∈ 𝒜`, `sSeq A` is a clockwise numbering of `∂A`. -/
  sSeq_valid : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A →
    IsClockwiseBoundaryNumbering S_H A (sSeq A)
  /-- For each interior `A ∈ 𝒜`, the vertex `v(A) ∈ V(H)`. -/
  vOf : Graph α β → α
  /-- For each interior `A ∈ 𝒜`, `v(A) ∈ V(H)` and there is a path of `K` between `∂A` (or `V(A)` when
  `∂A = ∅`) and `v(A)` with no vertex in `V(H)` except `v(A)`. -/
  vOf_valid : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A →
    vOf A ∈ V(H.graph) ∧
    ∃ P : Graph α β, ∃ s : α,
      (s ∈ divBoundary S_H A ∨ (divBoundary S_H A = ∅ ∧ s ∈ V(A))) ∧
      IsGraphPathWithEnds S_H.G P s (vOf A) ∧
      V(P) ∩ V(H.graph) = {vOf A}

namespace Vision

variable {α : Type u} {β : Type v} {G : Digraph α β} {X : Set α} {H : Wall α β}
  {S_H : Society α β} {𝒜 : Set (Graph α β)} (vis : Vision G X H S_H 𝒜)

/-- The attachment sequence `π(A) = (s₁, …, s_k, x₁, …, x_r)` of an interior member `A ∈ 𝒜`
(Graph Minors XIII, Section 10, page 106). -/
def pi (A : Graph α β) : List α :=
  vis.sSeq A ++ vis.xSeq

/-- Two interior members `A, A' ∈ 𝒜` have the same `δ`-folio under the vision `vis` if
`|(π(A))| = |(π(A'))|` and `(Ã', π(A'))` has the same `δ`-folio as `(Ã, π(A))`
(Graph Minors XIII, Section 10, page 107). -/
def HasSameMemberDeltaFolio (δ : ℕ) (A A' : Graph α β) : Prop :=
  ∃ (hA : ∀ x ∈ vis.pi A, x ∈ (vis.tildeA A).vertexSet)
    (hA' : ∀ x ∈ vis.pi A', x ∈ (vis.tildeA A').vertexSet)
    (hlen : (vis.pi A).length = (vis.pi A').length),
    HasSameDeltaFolio
      (rootedDigraphOfList (vis.tildeA A) (vis.pi A) hA)
      (hlen ▸ rootedDigraphOfList (vis.tildeA A') (vis.pi A') hA') δ

end Vision

/-- Under Hypothesis C and given a vision `vis`, a subwall `H'` of `H` is `h`-homogeneous
(Graph Minors XIII, Section 10, page 107):
“Under Hypothesis C and given some vision, a subwall $H'$ of $H$ is said to be *$h$-homogeneous* if
for every internal $A \in \mathcal{A}$ with $v(A)$ inside $H'$ and for every subwall $H''$ of $H'$
of height $h$, there exists some internal $A' \in \mathcal{A}$ with $v(A')$ inside $H''$ such that
$(A', \pi(A'))$ has the same $\delta$-folio as $(A, \pi(A))$.” -/
def IsHomogeneousSubwall {α : Type u} {β : Type v}
    {G : Digraph α β} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (vis : Vision G X H S_H 𝒜) (δ h : ℕ) (H' : Wall α β) : Prop :=
  H'.IsSubwallOf H ∧
    ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → vis.vOf A ∈ H'.insideVerts →
      ∀ ⦃H'' : Wall α β⦄, H''.IsSubwallOf H' → H''.height = h →
        ∃ A' : Graph α β, IsInteriorMember H 𝒜 A' ∧ vis.vOf A' ∈ H''.insideVerts ∧
          vis.HasSameMemberDeltaFolio δ A A'

/-- Graph Minors XIII, (10.2) (Section 10, page 107):
“(10.2) *For any $q$, $\delta \ge 0$ and $h \ge 2$, even, there exists $f(h) \ge h$, even, such
that under Hypothesis C, if $H' \subseteq H$ is an $h$-homogeneous subwall of height $f(h)$ then
both middle vertices of $H'$ are irrelevant to the $\delta$-folio of $G$ relative to $X$.*” -/
def GM13Theorem102Statement : Prop :=
  ∀ (q δ h : ℕ), 2 ≤ h → Even h →
    ∃ f_h : ℕ, h ≤ f_h ∧ Even f_h ∧
      ∀ {α : Type u} {β : Type v}
        (G : Digraph α β) (X : Set α) (H H' : Wall α β)
        (S_H : Society α β) (𝒜 : Set (Graph α β))
        (vis : Vision G X H S_H 𝒜),
        HypothesisC G q X H S_H 𝒜 →
        IsHomogeneousSubwall vis δ h H' →
        H'.height = f_h →
        IsIrrelevantVertex G δ X H'.middleVertex₁ ∧
        IsIrrelevantVertex G δ X H'.middleVertex₂

end GraphMinor.GM13
