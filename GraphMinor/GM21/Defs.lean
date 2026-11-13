module

public import GraphMinor.Hypergraph.Basic
public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.GM07.Defs
public import GraphMinor.GM10.Defs
public import GraphMinor.GM10.Defs2
public import GraphMinor.GM10.TreeWidth
public import GraphMinor.GM11.Defs
public import GraphMinor.GM12.Defs
public import GraphMinor.GM12.Bridge
public import GraphMinor.GM14.Defs
public import GraphMinor.GM17.Defs
public import GraphMinor.GM19.Defs
public import GraphMinor.GM19.Defs2

/-!
# Graph Minors XXI: Definitions

Definitions from N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616.

Sections 1–10:
- Section 1: Linkages, terminals, pattern, `p`-linkages, vital linkages
- Section 2: Separations, vertex splitting
- Section 3: Tangles, `𝒯 \ W`, `θ`-truncation
- Section 4: Respectful tangles in drawings
- Section 5: Cuff regions and the metric of a respectful tangle
- Section 6: Spaces, supports, ends, presentations, exhaustive linkages, `Σ`-jumps
- Section 7: Small subgraphs with respect to a tangle, surrounding a tangle, `Γ^+`
- Section 8: Circular order on a cuff, units, pseudo-presentations, disjointed pseudo-presentations
- Section 9: Paintings (with 2 or 3 vertices on each cell boundary), portraits, surrounding a tangle
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM10

universe u v w

/-! ## Section 1: Linkages, patterns, and vital linkages -/

/-- The set of edges of a hypergraph `H` incident with a vertex `x`. -/
def incidentEdges {α : Type u} {β : Type v} (H : Hypergraph α β) (x : α) : Set β :=
  {e ∈ H.edgeSet | H.Inc e x}

/-- The degree of a vertex `x` in a hypergraph (graph) `H`, counting loops twice and non-loops once. -/
noncomputable def vertexDegree {α : Type u} {β : Type v} (H : Hypergraph α β) (x : α) : ℕ :=
  (incidentEdges H x).ncard +
    {e ∈ incidentEdges H x | (H.ends e).Subsingleton}.ncard

/-- `C` is a connected component of `H` if `C ≤ H`, `C` is non-null, `C.skeleton` is connected on
`C.vertexSet`, and `C` is maximal with these properties. -/
def IsComponentOf {α : Type u} {β : Type v} (H C : Hypergraph α β) : Prop :=
  C ≤ H ∧
  C.vertexSet.Nonempty ∧
  (∀ x ∈ C.vertexSet, ∀ y ∈ C.vertexSet, C.skeleton.Reachable x y) ∧
  ∀ C' : Hypergraph α β, C' ≤ H → C'.vertexSet.Nonempty →
    (∀ x ∈ C'.vertexSet, ∀ y ∈ C'.vertexSet, C'.skeleton.Reachable x y) →
    C ≤ C' → C' = C

/-- A subhypergraph `P` of `G` is a *path* if it is a non-null connected graph with no loops,
no parallel edges, every vertex has degree at most `2` in `P`, and if `P` has edges then it has
at least one vertex of degree `1` in `P` (which excludes cycles).

Graph Minors XXI, Section 1 (page 1 of the preprint):
“All graphs in this paper are finite and undirected, and may have loops or parallel edges. *Paths*
have at least one vertex, and have no "repeated" vertices or edges.” -/
def IsPathGraph {α : Type u} {β : Type v} (P : Hypergraph α β) : Prop :=
  P.IsGraph ∧
  P.vertexSet.Nonempty ∧
  (∀ x ∈ P.vertexSet, ∀ y ∈ P.vertexSet, P.skeleton.Reachable x y) ∧
  (∀ e ∈ P.edgeSet, (P.ends e).ncard = 2) ∧
  (∀ e₁ ∈ P.edgeSet, ∀ e₂ ∈ P.edgeSet, P.ends e₁ = P.ends e₂ → e₁ = e₂) ∧
  (∀ x ∈ P.vertexSet, (incidentEdges P x).ncard ≤ 2) ∧
  (∀ H : Hypergraph α β, H ≤ P → H.edgeSet.Nonempty →
    ∃ x ∈ H.vertexSet, (incidentEdges H x).ncard = 1)

/-- Graph Minors XXI, Section 1 (page 1 of the preprint):
"A *linkage* in a graph $G$ is a subgraph every component of which is a path." -/
def IsLinkage {α : Type u} {β : Type v} (G L : Hypergraph α β) : Prop :=
  L ≤ G ∧ L.IsGraph ∧ ∀ C : Hypergraph α β, IsComponentOf L C → IsPathGraph C

/-- Graph Minors XXI, Section 1 (page 1 of the preprint):
"A vertex of $G$ is a *terminal* of a linkage $L$ in $G$ if $v \in V(L)$ and $v$ has degree
$\le 1$ in $L$." -/
def IsTerminal {α : Type u} {β : Type v} (L : Hypergraph α β) (v : α) : Prop :=
  v ∈ L.vertexSet ∧ vertexDegree L v ≤ 1

/-- The set of all terminals of `L`. -/
def terminals {α : Type u} {β : Type v} (L : Hypergraph α β) : Set α :=
  {v : α | IsTerminal L v}

/-- Graph Minors XXI, Section 1 (page 1 of the preprint):
"The *pattern* of a linkage $L$ is the partition of its terminals in which two terminals are
in the same block if and only if they belong to the same component of $L$." -/
def linkagePattern {α : Type u} {β : Type v} (L : Hypergraph α β) : Set (Set α) :=
  {B : Set α | ∃ C : Hypergraph α β, IsComponentOf L C ∧ B = terminals L ∩ C.vertexSet}

/-- Graph Minors XXI, Section 1 (page 1 of the preprint):
"A linkage is a *$p$-linkage* if it has $\le p$ terminals, where $p \ge 0$ is an integer." -/
def IsPLinkage {α : Type u} {β : Type v} (G L : Hypergraph α β) (p : ℕ) : Prop :=
  IsLinkage G L ∧ (terminals L).ncard ≤ p

/-- Graph Minors XXI, Section 1 (page 1 of the preprint):
"A linkage $L$ in $G$ is *vital* if $V(L) = V(G)$, and no linkage in $G$ different from $L$
has the same pattern as $L$." -/
def IsVitalLinkage {α : Type u} {β : Type v} (G L : Hypergraph α β) : Prop :=
  IsLinkage G L ∧
  L.vertexSet = G.vertexSet ∧
  ∀ L' : Hypergraph α β, IsLinkage G L' → linkagePattern L' = linkagePattern L → L' = L

/-- `L` is a vital `p`-linkage in `G` if it is both a vital linkage in `G` and a `p`-linkage in `G`. -/
def IsVitalPLinkage {α : Type u} {β : Type v} (G L : Hypergraph α β) (p : ℕ) : Prop :=
  IsVitalLinkage G L ∧ IsPLinkage G L p

/-- A graph `G` has a vital `p`-linkage if some subgraph `L` of `G` is a vital `p`-linkage in `G`. -/
def HasVitalPLinkage {α : Type u} {β : Type v} (G : Hypergraph α β) (p : ℕ) : Prop :=
  ∃ L : Hypergraph α β, IsVitalPLinkage G L p

/-! ## Section 2: Separations and vertex splitting -/

/-- Graph Minors XXI, Section 2 (page 2 of the preprint):
"A *separation* of $G$ is a pair $(A, B)$ of subgraphs of $G$ with union $G$ and with
$E(A \cap B) = \emptyset$; its *order* is $|V(A \cap B)|$."
This is `Hypergraph.IsSeparation` and `Hypergraph.separationOrder`. -/
abbrev IsSeparation {α : Type u} {β : Type v} (G A B : Hypergraph α β) : Prop :=
  G.IsSeparation A B

/-- Graph Minors XXI, Section 2 (pages 2–3 of the preprint):
"Let $v$ be a vertex of a graph $G$, and let $\delta_1, \delta_2 \subseteq E(G)$ with
$\delta_1 \cap \delta_2 = \emptyset$, so ... that $\delta_1 \cup \delta_2$ is the set of all edges
of $G$ incident with $v$. Take two new elements $v_1, v_2$, and let $G'$ be the graph with
vertex set $(V(G) \setminus \{v\}) \cup \{v_1, v_2\}$ and edge set $E(G)$, in which an edge $e$
is incident with a vertex $u \in V(G')$ if either $u \ne v_1, v_2$ and $e$ is incident with $u$
in $G$, or $u = v_i$ and $e \in \delta_i$ for $i = 1$ or $2$. We say that $G'$ is obtained from
$G$ by *splitting* $v$ *(according to $\delta_1, \delta_2$)*." -/
structure IsVertexSplit {α : Type u} {β : Type v}
    (G G' : Hypergraph α β) (v v₁ v₂ : α) (δ₁ δ₂ : Set β) : Prop where
  v_mem : v ∈ G.vertexSet
  v₁_not_mem : v₁ ∉ G.vertexSet
  v₂_not_mem : v₂ ∉ G.vertexSet
  v₁_ne_v₂ : v₁ ≠ v₂
  δ_disjoint : Disjoint δ₁ δ₂
  δ_union : δ₁ ∪ δ₂ = incidentEdges G v
  vertexSet_eq : G'.vertexSet = (G.vertexSet \ {v}) ∪ {v₁, v₂}
  edgeSet_eq : G'.edgeSet = G.edgeSet
  inc_iff : ∀ e ∈ G'.edgeSet, ∀ u ∈ G'.vertexSet,
    G'.Inc e u ↔
      ((u ≠ v₁ ∧ u ≠ v₂ ∧ G.Inc e u) ∨
       (u = v₁ ∧ e ∈ δ₁) ∨
       (u = v₂ ∧ e ∈ δ₂))

/-- `G'` is obtained from `G` by splitting a vertex if there exist `v, v₁, v₂, δ₁, δ₂` satisfying
`IsVertexSplit G G' v v₁ v₂ δ₁ δ₂`. -/
def ObtainedBySplittingVertex {α : Type u} {β : Type v} (G G' : Hypergraph α β) : Prop :=
  ∃ (v v₁ v₂ : α) (δ₁ δ₂ : Set β), IsVertexSplit G G' v v₁ v₂ δ₁ δ₂

/-- `G'` can be obtained from `G` by splitting at most `k` vertices. -/
inductive ObtainedBySplittingLe {α : Type u} {β : Type v} : ℕ → Hypergraph α β → Hypergraph α β → Prop
  | refl (k : ℕ) (G : Hypergraph α β) : ObtainedBySplittingLe k G G
  | step {k : ℕ} {G G₁ G' : Hypergraph α β} :
      ObtainedBySplittingVertex G G₁ →
      ObtainedBySplittingLe k G₁ G' →
      ObtainedBySplittingLe (k + 1) G G'

/-! ## Section 6: Spaces, supports, ends, presentations, exhaustive linkages, and `Σ`-jumps -/

/-- Graph Minors XXI, Section 6 (page 21 of the preprint):
"If $\Gamma$ is a drawing in a surface $\Sigma$ such that $|V(\Gamma) \cap C| \ge 2$ for every
cuff $C$, we call the connected components of $bd(\Sigma) \setminus V(\Gamma)$ the *spaces* of
$\Gamma$ in $\Sigma$. For every space $s$ there are two vertices $u, v$ such that
$s \cup \{u, v\}$ is a line; we call $u, v$ the *ends* of $s$." -/
def drawingSpaces {S : Type w} [TopologicalSpace S] (Γ : Drawing S) : Set (Set S) :=
  componentsIn (bd S \ Γ.V)

/-- `s` is a space of `Γ` in `S`. -/
def IsSpaceOfDrawing {S : Type w} [TopologicalSpace S] (Γ : Drawing S) (s : Set S) : Prop :=
  s ∈ drawingSpaces Γ

/-- `u` and `v` are the ends of a space `s` of `Γ` in `S`: `u, v ∈ V(Γ) ∩ bd(S)` and
`s ∪ {u, v}` is a line with ends `u` and `v`. -/
def SpaceHasEnds {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) (s : Set S) (u v : S) : Prop :=
  s ∈ drawingSpaces Γ ∧
  u ∈ Γ.V ∩ bd S ∧
  v ∈ Γ.V ∩ bd S ∧
  u ≠ v ∧
  IsLineWithEnds (s ∪ {u, v}) u v ∧
  closure s = s ∪ {u, v}

/-- Graph Minors XXI, Section 6 (page 21 of the preprint):
"A *support* of $\Gamma$ in $\Sigma$ is either a set $\{v\}$ where
$v \in V(\Gamma) \cap bd(\Sigma)$, or a line $F \subseteq bd(\Sigma)$ with both ends in
$V(\Gamma)$ (where possibly some internal points of $F$ belong to $V(\Gamma)$). The *ends* of a
support $F$ are $a$ and $b$, where $a = b = v$ if $F = \{v\}$, and $a$ and $b$ are the ends of
the line $F$ if $F$ is a line." -/
def SupportHasEnds {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) (F : Set S) (a b : S) : Prop :=
  (∃ v ∈ Γ.V ∩ bd S, F = {v} ∧ a = v ∧ b = v) ∨
  (F ⊆ bd S ∧ a ≠ b ∧ a ∈ Γ.V ∩ bd S ∧ b ∈ Γ.V ∩ bd S ∧ IsLineWithEnds F a b)

/-- `F` is a support of `Γ` in `S`. -/
def IsSupportOfDrawing {S : Type w} [TopologicalSpace S] (Γ : Drawing S) (F : Set S) : Prop :=
  ∃ a b : S, SupportHasEnds Γ F a b

/-- The domain of the map `μ` in a presentation or pseudo-presentation of `G` in `S`:
a boundary vertex `u ∈ V(Γ) ∩ bd(S)` or a space `s ∈ drawingSpaces Γ` (called a *unit* in
Section 8, page 32 of the preprint: "A *unit* is either a vertex in $V(\Gamma) \cap bd(\Sigma)$ or a
space in $F_1^* \cup \dots \cup F_r^*$"). -/
inductive BoundaryUnit (S : Type w) : Type w
  | vertex (u : S) : BoundaryUnit S
  | space (s : Set S) : BoundaryUnit S

/-- For a support `F` of `Γ` in `S`, `supportGraph Γ μ F` is `μ(F)`:
"For a support $F$ of $\Gamma$ in $\Sigma$, $\mu(F)$ denotes the union of $\mu(s)$ over all spaces
$s \subseteq F$ and $\mu(u)$ over all $u \in F \cap V(\Gamma)$."
(Graph Minors XXI, Section 6, page 22 of the preprint). -/
def supportGraph {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (G : Hypergraph α β) (Γ : Drawing S) (μ : BoundaryUnit S → Hypergraph α β) (F : Set S) :
    Hypergraph α β where
  vertexSet := G.vertexSet ∩
    ((⋃ s ∈ {s ∈ drawingSpaces Γ | s ⊆ F}, (μ (.space s)).vertexSet) ∪
     (⋃ u ∈ Γ.V ∩ F, (μ (.vertex u)).vertexSet))
  edgeSet := G.edgeSet ∩
    ((⋃ s ∈ {s ∈ drawingSpaces Γ | s ⊆ F}, (μ (.space s)).edgeSet) ∪
     (⋃ u ∈ Γ.V ∩ F, (μ (.vertex u)).edgeSet))
  Inc e v := G.Inc e v ∧
    ((∃ s ∈ drawingSpaces Γ, s ⊆ F ∧ (μ (.space s)).Inc e v) ∨
     (∃ u ∈ Γ.V ∩ F, (μ (.vertex u)).Inc e v))
  vertex_mem_of_inc := by
    rintro e v ⟨hG, ⟨s, hs, hsF, hinc⟩ | ⟨u, hu, hinc⟩⟩
    · exact ⟨G.vertex_mem_of_inc hG, Or.inl (mem_biUnion ⟨hs, hsF⟩ ((μ (.space s)).vertex_mem_of_inc hinc))⟩
    · exact ⟨G.vertex_mem_of_inc hG, Or.inr (mem_biUnion hu ((μ (.vertex u)).vertex_mem_of_inc hinc))⟩
  edge_mem_of_inc := by
    rintro e v ⟨hG, ⟨s, hs, hsF, hinc⟩ | ⟨u, hu, hinc⟩⟩
    · exact ⟨G.edge_mem_of_inc hG, Or.inl (mem_biUnion ⟨hs, hsF⟩ ((μ (.space s)).edge_mem_of_inc hinc))⟩
    · exact ⟨G.edge_mem_of_inc hG, Or.inr (mem_biUnion hu ((μ (.vertex u)).edge_mem_of_inc hinc))⟩
  vertexSet_finite := G.vertexSet_finite.subset inter_subset_left
  edgeSet_finite := G.edgeSet_finite.subset inter_subset_left

/-- A vertex `u ∈ F ∩ V(Γ)` lies between spaces `s₁, s₂ ⊆ F` in a support `F` if there are
supports `I₁, I₂ ⊆ F` with `I₁ ∪ I₂ = F`, `I₁ ∩ I₂ = {u}`, `s₁ ⊆ I₁`, and `s₂ ⊆ I₂`. -/
def LiesBetweenInSupport {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) (F s₁ s₂ : Set S) (u : S) : Prop :=
  u ∈ F ∩ Γ.V ∧ s₁ ∈ drawingSpaces Γ ∧ s₂ ∈ drawingSpaces Γ ∧ s₁ ⊆ F ∧ s₂ ⊆ F ∧
  ∃ I₁ I₂ : Set S, IsSupportOfDrawing Γ I₁ ∧ IsSupportOfDrawing Γ I₂ ∧
    I₁ ∪ I₂ = F ∧ I₁ ∩ I₂ = {u} ∧ s₁ ⊆ I₁ ∧ s₂ ⊆ I₂

/-- `(ιV, ιE)` maps the hypergraph `Γ.toHypergraph` of a drawing `Γ` in `S` isomorphically onto
the subgraph `Γ_sub`: `ιV` is injective on `Γ.V` with image `Γ_sub.vertexSet`, `ιE` is injective
on `Γ.E` with image `Γ_sub.edgeSet`, and for `e ∈ Γ.E` and `u ∈ Γ.V`,
`Γ_sub.Inc (ιE e) (ιV u) ↔ u ∈ closure e`.

Graph Minors XXI, Section 6 (page 21 of the preprint):
"Let $\Gamma$, as above, be a subgraph of some graph $G$, which is not required to be a drawing."
Graph Minors XXI, Section 8 (page 32 of the preprint):
"Let $\Gamma \subseteq G$ be a drawing in $\Sigma$" -/
structure IsDrawingIso {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α) (ιE : Set S → β) : Prop where
  ιV_injOn : InjOn ιV Γ.V
  ιV_image : ιV '' Γ.V = Γ_sub.vertexSet
  ιE_injOn : InjOn ιE Γ.E
  ιE_image : ιE '' Γ.E = Γ_sub.edgeSet
  inc_iff : ∀ e ∈ Γ.E, ∀ u ∈ Γ.V, Γ_sub.Inc (ιE e) (ιV u) ↔ u ∈ closure e

/-- Graph Minors XXI, Section 6 (pages 21–22 of the preprint):
"Let $\Gamma$, as above, be a subgraph of some graph $G$, which is not required to be a drawing.
Let $F_1^*, \dots, F_r^*$ be mutually disjoint supports of $\Gamma$ in $\Sigma$ with
$V(\Gamma) \cap bd(\Sigma) \subseteq F_1^* \cup \dots \cup F_r^*$. For $1 \le j \le r$, let
$H_j \subseteq G$, so that
(V1) $H_1 \cup \dots \cup H_r \cup \Gamma = G$; $H_1, \dots, H_r$ *are mutually vertex-disjoint;
and for* $1 \le j \le r, V(H_j \cap \Gamma) = V(\Gamma) \cap F_j^*$, *and*
$E(H_j \cap \Gamma) = \emptyset$. ...
For $1 \le j \le r$, let $q_j \ge 1$ be an integer; for each $u \in V(\Gamma) \cap F_j^*$ let
$\mu(u)$ be an edge-less subgraph of $H_j$ with $q_j$ vertices and with
$V(\mu(u) \cap \Gamma) = \{u\}$; and for each space $s$ with $s \subseteq F_j^*$, let $\mu(s)$ be a
subgraph of $H_j$, satisfying the following. (For a support $F$ of $\Gamma$ in $\Sigma$, $\mu(F)$
denotes the union of $\mu(s)$ over all spaces $s \subseteq F$ and $\mu(u)$ over all
$u \in F \cap V(\Gamma)$.)
(V2) *For* $1 \le j \le r, H_j = \mu(F_j^*)$.
(V3) *For* $1 \le j \le r$, *if* $s \subseteq F_j^*$ *is a space with ends* $u_1, u_2$, *then*
$V(\mu(s) \cap \Gamma) = \{u_1, u_2\}$, *and* $\mu(u_1), \mu(u_2) \subseteq \mu(s)$ *and there are*
$q_j$ *mutually vertex-disjoint paths of* $\mu(s)$ *between* $V(\mu(u_1))$ *and* $V(\mu(u_2))$.
(V4) *For* $1 \le j \le r$, *if* $s_1, s_2 \subseteq F_j^*$ *are spaces, and*
$u \in F_j^* \cap V(\Gamma)$ *lies between them in* $F_j^*$, *then*
$\mu(s_1) \cap \mu(s_2) \subseteq \mu(u)$ *(and consequently* $E(\mu(s_1) \cap \mu(s_2)) = \emptyset$).
In these circumstances, we call $\Gamma, F_1^*, \dots, F_r^*, H_1, \dots, H_r, \mu$ a
*presentation* of $G$ in $\Sigma$, with *defect* $r$. Its *depth* is
$\max(q_j : 1 \le j \le r)$, or $0$ if $r = 0$ (which implies $bd(\Sigma) = \emptyset$)."

Here `Γ_sub ≤ G` is the subgraph of `G` corresponding to the drawing `Γ` via `(ιV, ιE)`. -/
structure IsPresentation {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
    (ιV : S → α) (ιE : Set S → β)
    (r : ℕ) (F_star : Fin r → Set S) (H : Fin r → Hypergraph α β)
    (μ : BoundaryUnit S → Hypergraph α β) (q : Fin r → ℕ) : Prop where
  is_surface : IsSurface S
  is_connected_surface : ConnectedSpace S
  is_proper_drawing : Γ.IsProper
  cuff_vertices_ge_two : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard
  drawing_subgraph : Γ_sub ≤ G
  drawing_iso : IsDrawingIso Γ Γ_sub ιV ιE
  supports_isSupport : ∀ j : Fin r, IsSupportOfDrawing Γ (F_star j)
  supports_disjoint : Pairwise (fun i j : Fin r => Disjoint (F_star i) (F_star j))
  bd_vertices_covered : Γ.V ∩ bd S ⊆ ⋃ j : Fin r, F_star j
  -- (V1)
  v1_sub : ∀ j : Fin r, H j ≤ G
  v1_union_V : G.vertexSet = (⋃ j : Fin r, (H j).vertexSet) ∪ Γ_sub.vertexSet
  v1_union_E : G.edgeSet = (⋃ j : Fin r, (H j).edgeSet) ∪ Γ_sub.edgeSet
  v1_disjoint : Pairwise (fun i j : Fin r => Disjoint (H i).vertexSet (H j).vertexSet)
  v1_inter_V : ∀ j : Fin r, (H j).vertexSet ∩ Γ_sub.vertexSet = ιV '' (Γ.V ∩ F_star j)
  v1_inter_E : ∀ j : Fin r, Disjoint (H j).edgeSet Γ_sub.edgeSet
  -- Depth parameters q_j >= 1 and μ(u), μ(s):
  q_pos : ∀ j : Fin r, 1 ≤ q j
  μ_vertex_sub : ∀ j : Fin r, ∀ u ∈ Γ.V ∩ F_star j,
    μ (.vertex u) ≤ H j ∧
    (μ (.vertex u)).edgeSet = ∅ ∧
    (μ (.vertex u)).vertexSet.ncard = q j ∧
    (μ (.vertex u)).vertexSet ∩ Γ_sub.vertexSet = {ιV u}
  μ_space_sub : ∀ j : Fin r, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j → μ (.space s) ≤ H j
  -- (V2)
  v2_eq : ∀ j : Fin r, H j = supportGraph G Γ μ (F_star j)
  -- (V3)
  v3_space : ∀ j : Fin r, ∀ s ∈ drawingSpaces Γ, ∀ u₁ u₂ : S,
    s ⊆ F_star j → SpaceHasEnds Γ s u₁ u₂ →
    (μ (.space s)).vertexSet ∩ Γ_sub.vertexSet = {ιV u₁, ιV u₂} ∧
    μ (.vertex u₁) ≤ μ (.space s) ∧
    μ (.vertex u₂) ≤ μ (.space s) ∧
    HasDisjointPaths (μ (.space s)).skeleton (μ (.vertex u₁)).vertexSet (μ (.vertex u₂)).vertexSet (q j)
  -- (V4)
  v4_between : ∀ j : Fin r, ∀ s₁ s₂ : Set S, ∀ u : S,
    LiesBetweenInSupport Γ (F_star j) s₁ s₂ u →
    μ (.space s₁) ∩ μ (.space s₂) ≤ μ (.vertex u)

namespace IsPresentation

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
  {H : Fin r → Hypergraph α β} {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

theorem ιV_injOn (h : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) : InjOn ιV Γ.V :=
  h.drawing_iso.ιV_injOn

theorem ιV_image (h : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) :
    ιV '' Γ.V = Γ_sub.vertexSet :=
  h.drawing_iso.ιV_image

theorem ιE_injOn (h : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) : InjOn ιE Γ.E :=
  h.drawing_iso.ιE_injOn

theorem ιE_image (h : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) :
    ιE '' Γ.E = Γ_sub.edgeSet :=
  h.drawing_iso.ιE_image

theorem inc_iff (h : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) :
    ∀ e ∈ Γ.E, ∀ u ∈ Γ.V, Γ_sub.Inc (ιE e) (ιV u) ↔ u ∈ closure e :=
  h.drawing_iso.inc_iff

end IsPresentation

/-- A presentation has depth `≤ d` if `q j ≤ d` for all `j : Fin r` (and `bd S = ∅` when `r = 0`). -/
def PresentationHasDepthLe {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
    (ιV : S → α) (ιE : Set S → β)
    (r : ℕ) (F_star : Fin r → Set S) (H : Fin r → Hypergraph α β)
    (μ : BoundaryUnit S → Hypergraph α β) (d : ℕ) : Prop :=
  ∃ q : Fin r → ℕ,
    IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q ∧
    (∀ j : Fin r, q j ≤ d) ∧
    (r = 0 → bd S = ∅)

/-- Graph Minors XXI, Section 6 (page 24 of the preprint):
"Let $\Gamma, F_1^*, \ldots, F_r^*, H_1, \ldots, H_r, \mu$ be a presentation of $G$ in $\Sigma$,
and let $L$ be a vital linkage in $G$. If $\Gamma \subseteq L$ and every terminal of $L$ is in
one of $H_1, \ldots, H_r$, we say that $L$ is *exhaustive* (for the presentation)." -/
def IsExhaustiveLinkage {α : Type u} {β : Type v}
    (G Γ_sub : Hypergraph α β) (r : ℕ) (H : Fin r → Hypergraph α β) (L : Hypergraph α β) : Prop :=
  IsVitalLinkage G L ∧
  Γ_sub ≤ L ∧
  terminals L ⊆ ⋃ j : Fin r, (H j).vertexSet

/-- Graph Minors XXI, Section 6 (page 24 of the preprint):
"Let us say a $\Sigma$-*jump* is a path in $\Gamma$ with distinct ends both in $bd(\Sigma)$ and
with no internal vertex in $bd(\Sigma)$."

In a presentation the graph $\Gamma$ is the subgraph `Γ_sub` of `G`, and `ιV` maps the vertices of
the drawing `Γ` onto `V(Γ_sub)`. So a `Σ`-jump is a path `J ≤ Γ_sub` whose ends (its terminals)
are `ιV u` and `ιV v` for distinct `u, v ∈ V(Γ) ∩ bd(Σ)`, and such that no other vertex
`ιV x` with `x ∈ V(Γ) ∩ bd(Σ)` lies on `J`. -/
def IsSigmaJump {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α) (J : Hypergraph α β) : Prop :=
  J ≤ Γ_sub ∧ IsPathGraph J ∧
  ∃ u ∈ Γ.V ∩ bd S, ∃ v ∈ Γ.V ∩ bd S, u ≠ v ∧
    terminals J = {ιV u, ιV v} ∧
    ∀ x ∈ Γ.V ∩ bd S, ιV x ∈ J.vertexSet → x = u ∨ x = v

/-- The set of all `Σ`-jumps of a drawing `Γ` in `S`, drawn as the subgraph `Γ_sub`. -/
def sigmaJumps {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α) : Set (Hypergraph α β) :=
  {J | IsSigmaJump Γ Γ_sub ιV J}

/-! ## Section 7: Tangles, small subgraphs, surrounding a tangle, and `Γ^+` -/

/-- Graph Minors XXI, Section 7 (page 29 of the preprint):
"If $\mathcal{T}$ is a tangle in a graph $G$, a subgraph $A$ of $G$ is *small* (with respect to
$\mathcal{T}$) if there exists $B \subseteq G$ such that $(A, B) \in \mathcal{T}$." -/
def IsSmallSubgraph {α : Type u} {β : Type v}
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (A : Hypergraph α β) : Prop :=
  ∃ B : Hypergraph α β, (A, B) ∈ 𝒯

/-- Graph Minors XXI, Section 7 (page 30 of the preprint):
"If $\Gamma, F_1^*, \dots, F_r^*, H_1, \dots, H_r, \mu$ is a presentation of $G$ in $\Sigma$,
and $\mathcal{T}$ is a tangle in $G$, we say that the presentation *surrounds* $\mathcal{T}$ if
$\mu(s)$ is small for every space $s \subseteq F_1^* \cup \dots \cup F_r^*$." -/
def PresentationSurroundsTangle {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) (r : ℕ) (F_star : Fin r → Set S)
    (μ : BoundaryUnit S → Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∀ s ∈ drawingSpaces Γ, (∃ j : Fin r, s ⊆ F_star j) → IsSmallSubgraph 𝒯 (μ (.space s))

/-- Graph Minors XXI, Section 7 (page 30 of the preprint):
"If $\Gamma$ is a drawing in a surface $\Sigma$ such that $|V(\Gamma) \cap C| \ge 2$ for every
cuff $C$, we define $\Gamma^+$ to be the drawing in $\hat{\Sigma}$ with
$U(\Gamma^+) = U(\Gamma) \cup bd(\Sigma)$ and $V(\Gamma^+) = V(\Gamma)$."
Viewed as an abstract hypergraph (graph), `Γ^+` has vertex set `Γ.V` and edge set
`Γ.E ∪ drawingSpaces Γ`. -/
def drawingPlusHypergraph {S : Type w} [TopologicalSpace S] (Γ : Drawing S)
    (h_spaces_fin : (drawingSpaces Γ).Finite) : Hypergraph S (Set S) where
  vertexSet := Γ.V
  edgeSet := Γ.E ∪ drawingSpaces Γ
  Inc e v := (e ∈ Γ.E ∪ drawingSpaces Γ) ∧ v ∈ Γ.V ∧ v ∈ closure e
  vertex_mem_of_inc := fun _ _ h => h.2.1
  edge_mem_of_inc := fun _ _ h => h.1
  vertexSet_finite := Γ.finite_V
  edgeSet_finite := Γ.finite_edges.union h_spaces_fin

/-! ## Section 8: Pseudo-presentations and disjointed pseudo-presentations -/

/-- A unit `x : BoundaryUnit S` belongs to a subset `F ⊆ S` if `u ∈ F` (for a vertex `u`) or
`s ⊆ F` (for a space `s`). -/
def BoundaryUnit.InSet {S : Type w} (x : BoundaryUnit S) (F : Set S) : Prop :=
  match x with
  | .vertex u => u ∈ F
  | .space s => s ⊆ F

/-- The underlying subset of `S` of a `BoundaryUnit S`. -/
def BoundaryUnit.toSet {S : Type w} (x : BoundaryUnit S) : Set S :=
  match x with
  | .vertex u => {u}
  | .space s => s

/-- Four subsets/points `(X₁, u₁, X₂, u₂)` on a cuff `C` occur in circular order around `C` if
for every `x₁ ∈ closure X₁ ∩ C` and `x₂ ∈ closure X₂ ∩ C`, `(x₁, u₁, x₂, u₂)` occur in order on `C`
(`GM19.InOrderOn C x₁ u₁ x₂ u₂`), witnessed by a parametrization `f : Circle ≃ₜ C`. -/
def InCuffOrder {S : Type w} [TopologicalSpace S]
    (C X₁ : Set S) (u₁ : S) (X₂ : Set S) (u₂ : S) : Prop :=
  ∃ (f : Circle ≃ₜ C) (a₁ b₁ t₁ a₂ b₂ t₂ : ℝ),
    a₁ ≤ b₁ ∧ b₁ ≤ t₁ ∧ t₁ ≤ a₂ ∧ a₂ ≤ b₂ ∧ b₂ ≤ t₂ ∧ t₂ ≤ a₁ + 2 * Real.pi ∧
    GM19.cuffPoint f t₁ = u₁ ∧
    GM19.cuffPoint f t₂ = u₂ ∧
    (closure X₁ ∩ C).Nonempty ∧ closure X₁ ∩ C ⊆ GM19.cuffPoint f '' Icc a₁ b₁ ∧
    (closure X₂ ∩ C).Nonempty ∧ closure X₂ ∩ C ⊆ GM19.cuffPoint f '' Icc a₂ b₂

/-- Graph Minors XXI, Section 8 (page 32 of the preprint):
"More precisely, a *pseudo-presentation* of a graph $G$ in a surface $\Sigma$ is defined as
follows. Let $\Gamma \subseteq G$ be a drawing in $\Sigma$ such that $|V(\Gamma) \cap C| \ge 2$
for each cuff $C$. Let $F_1^*, \dots, F_r^*$ be mutually disjoint supports of $\Gamma$ in $\Sigma$
with $V(\Gamma) \cap bd(\Sigma) \subseteq F_1^* \cup \dots \cup F_r^*$. For $1 \le j \le r$ let
$q_j \ge 1$ be an integer; for each $u \in V(\Gamma) \cap F_j^*$ let $\mu(u)$ be an edge-less
subgraph of $G$ with $q_j$ vertices and with $V(\mu(u) \cap \Gamma) = \{u\}$; and for each space
$s$ with $s \subseteq F_j^*$ let $\mu(s) \subseteq G$, satisfying (P1)–(P4) below. A *unit* is
either a vertex in $V(\Gamma) \cap bd(\Sigma)$ or a space in $F_1^* \cup \dots \cup F_r^*$.
(P1) $G = \Gamma \cup \bigcup(\mu(F_j^*) : 1 \le j \le r)$; $\Gamma$ *and all the graphs*
$\mu(s)$ *for* $s \in S(\Gamma)$ *and* $s \subseteq F_1^* \cup \dots \cup F_r^*$ *are mutually
edge-disjoint; and if* $x_1, x_2$ *are units in different cuffs then* $\mu(x_1)$ *and* $\mu(x_2)$
*are mutually vertex-disjoint.*
(P2) *For* $1 \le j \le r$, *if* $s \subseteq F_j^*$ *is a space with ends* $u_1, u_2$ *then*
$V(\mu(s) \cap \Gamma) = \{u_1, u_2\}$ *and* $\mu(u_1), \mu(u_2) \subseteq \mu(s)$, *and there are*
$q_j$ *mutually vertex-disjoint paths of* $\mu(s)$ *between* $V(\mu(u_1))$ *and* $V(\mu(u_2))$.
(P3) *For each cuff* $C$, *if* $x_1$ *and* $x_2$ *are units in* $C$ *and*
$u_1, u_2 \in C \cap V(\Gamma)$ *are such that* $x_1, u_1, x_2, u_2$ *occur in order in* $C$,
*then* $\mu(x_1) \cap \mu(x_2) \subseteq \mu(u_1) \cup \mu(u_2)$.
(P4) *For each cuff* $C, \bigcap(\mu(u) : u \in V(\Gamma) \cap C)$ *is null.*
Then we say that $\Gamma, F_1^*, \dots, F_4^*, \mu$ is a *pseudo-presentation* of $G$ in $\Sigma$.
Its depth is $\max(q_j : 1 \le j \le r)$, or $0$ if $r = 0$, and its defect is $r$. We say that
the pseudo-presentation is *disjointed* if for each space $s$ with ends $u_1, u_2$ such that
$s \nsubseteq F_1^* \cup \dots \cup F_r^*$, the graphs $\mu(u_1)$ and $\mu(u_2)$ are
vertex-disjoint." -/
structure IsPseudoPresentation {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
    (ιV : S → α) (ιE : Set S → β)
    (r : ℕ) (F_star : Fin r → Set S)
    (μ : BoundaryUnit S → Hypergraph α β) (q : Fin r → ℕ) : Prop where
  is_surface : IsSurface S
  is_connected_surface : ConnectedSpace S
  is_proper_drawing : Γ.IsProper
  cuff_vertices_ge_two : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard
  drawing_subgraph : Γ_sub ≤ G
  drawing_iso : IsDrawingIso Γ Γ_sub ιV ιE
  supports_isSupport : ∀ j : Fin r, IsSupportOfDrawing Γ (F_star j)
  supports_disjoint : Pairwise (fun i j : Fin r => Disjoint (F_star i) (F_star j))
  bd_vertices_covered : Γ.V ∩ bd S ⊆ ⋃ j : Fin r, F_star j
  q_pos : ∀ j : Fin r, 1 ≤ q j
  μ_vertex : ∀ j : Fin r, ∀ u ∈ Γ.V ∩ F_star j,
    μ (.vertex u) ≤ G ∧
    (μ (.vertex u)).edgeSet = ∅ ∧
    (μ (.vertex u)).vertexSet.ncard = q j ∧
    (μ (.vertex u)).vertexSet ∩ Γ_sub.vertexSet = {ιV u}
  μ_space : ∀ j : Fin r, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j → μ (.space s) ≤ G
  -- (P1)
  p1_union_V : G.vertexSet = Γ_sub.vertexSet ∪
    ⋃ j : Fin r, (supportGraph G Γ μ (F_star j)).vertexSet
  p1_union_E : G.edgeSet = Γ_sub.edgeSet ∪
    ⋃ j : Fin r, (supportGraph G Γ μ (F_star j)).edgeSet
  p1_edge_disjoint_drawing : ∀ j : Fin r, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j →
    Disjoint Γ_sub.edgeSet (μ (.space s)).edgeSet
  p1_edge_disjoint_spaces : ∀ s₁ ∈ drawingSpaces Γ, ∀ s₂ ∈ drawingSpaces Γ,
    (∃ j₁ : Fin r, s₁ ⊆ F_star j₁) → (∃ j₂ : Fin r, s₂ ⊆ F_star j₂) → s₁ ≠ s₂ →
    Disjoint (μ (.space s₁)).edgeSet (μ (.space s₂)).edgeSet
  p1_diff_cuff_disjoint : ∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S, C₁ ≠ C₂ →
    ∀ x₁ x₂ : BoundaryUnit S,
      x₁.InSet C₁ → x₂.InSet C₂ →
      Disjoint (μ x₁).vertexSet (μ x₂).vertexSet
  -- (P2)
  p2_space : ∀ j : Fin r, ∀ s ∈ drawingSpaces Γ, ∀ u₁ u₂ : S,
    s ⊆ F_star j → SpaceHasEnds Γ s u₁ u₂ →
    (μ (.space s)).vertexSet ∩ Γ_sub.vertexSet = {ιV u₁, ιV u₂} ∧
    μ (.vertex u₁) ≤ μ (.space s) ∧
    μ (.vertex u₂) ≤ μ (.space s) ∧
    HasDisjointPaths (μ (.space s)).skeleton (μ (.vertex u₁)).vertexSet (μ (.vertex u₂)).vertexSet (q j)
  -- (P3)
  p3_order : ∀ C ∈ cuffs S, ∀ x₁ x₂ : BoundaryUnit S, ∀ u₁ ∈ C ∩ Γ.V, ∀ u₂ ∈ C ∩ Γ.V,
    x₁.InSet C → x₂.InSet C →
    InCuffOrder C x₁.toSet u₁ x₂.toSet u₂ →
    μ x₁ ∩ μ x₂ ≤ μ (.vertex u₁) ∪ μ (.vertex u₂)
  -- (P4)
  p4_inter_null : ∀ C ∈ cuffs S, (⋂ u ∈ Γ.V ∩ C, (μ (.vertex u)).vertexSet) = ∅

namespace IsPseudoPresentation

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

theorem ιV_injOn (h : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) : InjOn ιV Γ.V :=
  h.drawing_iso.ιV_injOn

theorem ιV_image (h : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) :
    ιV '' Γ.V = Γ_sub.vertexSet :=
  h.drawing_iso.ιV_image

theorem ιE_injOn (h : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) : InjOn ιE Γ.E :=
  h.drawing_iso.ιE_injOn

theorem ιE_image (h : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) :
    ιE '' Γ.E = Γ_sub.edgeSet :=
  h.drawing_iso.ιE_image

theorem inc_iff (h : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) :
    ∀ e ∈ Γ.E, ∀ u ∈ Γ.V, Γ_sub.Inc (ιE e) (ιV u) ↔ u ∈ closure e :=
  h.drawing_iso.inc_iff

end IsPseudoPresentation

/-- A pseudo-presentation has depth `≤ d` if `q j ≤ d` for all `j : Fin r` (and `bd S = ∅` when `r = 0`). -/
def PseudoPresentationHasDepthLe {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
    (ιV : S → α) (ιE : Set S → β)
    (r : ℕ) (F_star : Fin r → Set S)
    (μ : BoundaryUnit S → Hypergraph α β) (d : ℕ) : Prop :=
  ∃ q : Fin r → ℕ,
    IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q ∧
    (∀ j : Fin r, q j ≤ d) ∧
    (r = 0 → bd S = ∅)

/-- Graph Minors XXI, Section 8 (page 32 of the preprint):
"We say that the pseudo-presentation is *disjointed* if for each space $s$ with ends $u_1, u_2$
such that $s \nsubseteq F_1^* \cup \dots \cup F_r^*$, the graphs $\mu(u_1)$ and $\mu(u_2)$ are
vertex-disjoint." -/
def IsDisjointedPseudoPresentation {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
    (ιV : S → α) (ιE : Set S → β)
    (r : ℕ) (F_star : Fin r → Set S)
    (μ : BoundaryUnit S → Hypergraph α β) (q : Fin r → ℕ) : Prop :=
  IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q ∧
  ∀ s ∈ drawingSpaces Γ, ∀ u₁ u₂ : S,
    SpaceHasEnds Γ s u₁ u₂ →
    (∀ j : Fin r, ¬ s ⊆ F_star j) →
    Disjoint (μ (.vertex u₁)).vertexSet (μ (.vertex u₂)).vertexSet

/-- Graph Minors XXI, Section 8 (page 36 of the preprint):
"Now let $\Gamma, F_1^*, \dots, F_r^*, \mu$ be a pseudo-presentation of $G$, and let
$\mathcal{T}$ be a tangle in $G$. We say the pseudo-presentation *surrounds* $\mathcal{T}$ if
$\mu(s)$ is small for every space $s \in F_1^* \cup \dots \cup F_r^*$." -/
def PseudoPresentationSurroundsTangle {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) (r : ℕ) (F_star : Fin r → Set S)
    (μ : BoundaryUnit S → Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∀ s ∈ drawingSpaces Γ, (∃ j : Fin r, s ⊆ F_star j) → IsSmallSubgraph 𝒯 (μ (.space s))

/-! ## Section 9: Paintings and portraits -/

/-- Graph Minors XXI, Section 9 (page 37 of the preprint):
> A *painting* $\Gamma$ in a surface $\Sigma$ is a pair $(U, V)$, where $U \subseteq \Sigma$ is
> closed and $V \subseteq U$ is finite, satisfying
> (i) $U \setminus V$ has only finitely many connected components, called *cells*
> (ii) for each cell $c$, its closure $\bar{c}$ is a closed disc, and $\tilde{c} \subseteq bd(\bar{c})$
> (where $\tilde{c}$ denotes $\bar{c} \setminus c$) and $|\tilde{c}| = 2$ or $3$
> (iii) $bd(\Sigma) \subseteq U$
> (iv) for each cell $c$, if $c \cap bd(\Sigma) \ne \emptyset$ (that is, $c$ is a border cell) then
> $|\tilde{c}| = 2$ and $\bar{c} \cap bd(\Sigma)$ is a line with ends the two members of $\tilde{c}$.
> (This differs very slightly from the definition in [10]. In that paper it was convenient to allow
> cells $c$ with $|\tilde{c}| = 0$ or $1$, but we no longer need such cells.)

Thus a painting in the sense of XXI is a `GM17.Painting S` (whose node set `Γ.N` is XXI's `V(Γ)`)
satisfying the additional condition `2 ≤ (tilde c).ncard` for every cell `c ∈ Γ.C`. -/
def IsPainting21 {S : Type} [TopologicalSpace S] (Γ : GM17.Painting S) : Prop :=
  ∀ c ∈ Γ.C, (tilde c).ncard = 2 ∨ (tilde c).ncard = 3

/-- A cell `c ∈ Γ.C` is a *border cell* if `c ∩ bd S ≠ ∅`, and an *internal cell* otherwise
(Graph Minors XXI, Section 9, page 37 of the preprint):
> for each cell $c$, if $c \cap bd(\Sigma) \ne \emptyset$ (that is, $c$ is a border cell) then
> $|\tilde{c}| = 2$ and $\bar{c} \cap bd(\Sigma)$ is a line with ends the two members of $\tilde{c}$.
> A cell which is not a border cell is called an *internal cell*. -/
def IsBorderCell {S : Type} [TopologicalSpace S] (Γ : GM17.Painting S) (c : Set S) : Prop :=
  c ∈ Γ.C ∧ (c ∩ bd S).Nonempty

/-- A cell `c ∈ Γ.C` is an *internal cell* if it is not a border cell. -/
def IsInternalCell {S : Type} [TopologicalSpace S] (Γ : GM17.Painting S) (c : Set S) : Prop :=
  c ∈ Γ.C ∧ Disjoint c (bd S)

/-- A subgraph `H` of `G` can be drawn in a closed disc with the members of `X ⊆ H.vertexSet`
drawn in the boundary of the disc (Graph Minors XXI, Section 9, (R9) and (9.1), page 38 of the
preprint). -/
def CanBeDrawnInDiscWithBoundary {α : Type u} {β : Type v}
    (H : Hypergraph α β) (X : Set α) : Prop :=
  ∃ (D : Drawing ClosedUnitDisc) (ι : ClosedUnitDisc → α),
    BijOn ι D.V H.vertexSet ∧
    X ⊆ ι '' (D.V ∩ bd ClosedUnitDisc) ∧
    ∀ u ∈ D.V, ∀ v ∈ D.V, u ≠ v →
      (H.skeleton.Adj (ι u) (ι v) ↔ D.toHypergraph.skeleton.Adj u v)

/-- Graph Minors XXI, Section 9 (pages 37–38 of the preprint):
> Let $G$ be a graph. We say that a pair $\Gamma, \alpha$ is a *portrait* of $G$ in $\Sigma$ (this
> is closely connected with the 'portrayal' of [10]) if
> (R1) *$\Gamma$ is a painting in $\Sigma$ and $V(\Gamma) \subseteq V(G)$, and $\alpha$ is a function
> with domain $(V(\Gamma) \cap bd(\Sigma)) \cup C(\Gamma)$.*
> (R2) *For each $c$ of $\Gamma$, $\alpha(c) \subseteq G$ and
> $V(\alpha(c)) \cap V(\Gamma) = \tilde{c}$.*
> (R3) *$G = \bigcup(\alpha(c) : c \in C(\Gamma))$, and
> $E(\alpha(c_1) \cap \alpha(c_2)) = \emptyset$ for all distinct cells $c_1, c_2$.*
> (R4) *For each $v \in V(\Gamma) \cap bd(\Sigma)$, $\alpha(v)$ is an edge-less subgraph of $G$ and
> $V(\alpha(v)) \cap V(\Gamma) = \{v\}$.*
> (R5) *For each cuff $C$ there is an integer $q(C) \ge 1$ such that $|V(\alpha(v))| = q(C)$ for all
> $v \in V(\Gamma) \cap C$.*
> (R6) *For each border cell $c$ with $\tilde{c} = \{u, v\}$, $\alpha(u)$ and $\alpha(v)$ are
> subgraphs of $\alpha(c)$, and either*
> (i) *there are $|V(\alpha(u))|$ mutually vertex-disjoint paths of $\alpha(c)$ between
> $V(\alpha(u))$ and $V(\alpha(v))$, that is, $c$ is 'linked', or*
> (ii) *there is a cell $c'$ with $|\tilde{c}'| = 3$ and $u, v \in \tilde{c}'$.*
> (R7) *If $c_1, c_2 \in C(\Gamma)$ are distinct, then
> $V(\alpha(c_1) \cap \alpha(c')) = \tilde{c}_1 \cap \tilde{c}_2$ unless $c_1$ and $c_2$ border the
> same cuff (that is, unless $c_1 \cap C \ne \emptyset \ne c_2 \cap C$ for some cuff $C$).*
> (R8) *If $c_1, c_2 \in C(\Gamma)$ border a cuff $C$, and $u_1, u_2 \in V(\Gamma) \cap C$ and
> $c_1, u_1, c_2, u_2$ are in order around $C$, then
> $\alpha(c_1) \cap \alpha(c_2) \subseteq \alpha(u_1) \cup \alpha(u_2)$.*
> (R9) *If $c \in C(\Gamma)$ and $|\tilde{c}| = 3$, then $\alpha(c)$ cannot be drawn in a disc so
> that the three members of $\tilde{c}$ are drawn in the boundary of the disc.*
> (R10) *For each cuff $C, \bigcap(\alpha(u) : u \in V(\Gamma) \cap C)$ is null.*
> Its depth is the maximum of $q(C)$, taken over all cuffs $C$ (or $0$ if $bd(\Sigma) = \emptyset$).

Here `ιN : S → α` is the injective embedding identifying the nodes `Γ.N` (written `V(Γ)` in XXI)
with vertices of `G`. -/
structure IsPortrait {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    (G : Hypergraph α β) (Γ : GM17.Painting S) (ιN : S → α)
    (α_cell : Set S → Hypergraph α β) (α_vert : S → Hypergraph α β)
    (q_cuff : Set S → ℕ) : Prop where
  is_surface : IsSurface S
  is_connected_surface : ConnectedSpace S
  -- (R1)
  r1_painting : IsPainting21 Γ
  r1_injOn : InjOn ιN Γ.N
  r1_subset : ιN '' Γ.N ⊆ G.vertexSet
  -- (R2)
  r2_cell_le : ∀ c ∈ Γ.C, α_cell c ≤ G
  r2_cell_inter : ∀ c ∈ Γ.C, (α_cell c).vertexSet ∩ (ιN '' Γ.N) = ιN '' (tilde c)
  -- (R3)
  r3_union_V : G.vertexSet = ⋃ c ∈ Γ.C, (α_cell c).vertexSet
  r3_union_E : G.edgeSet = ⋃ c ∈ Γ.C, (α_cell c).edgeSet
  r3_edge_disjoint : ∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C, c₁ ≠ c₂ →
    Disjoint (α_cell c₁).edgeSet (α_cell c₂).edgeSet
  -- (R4)
  r4_vert : ∀ v ∈ Γ.N ∩ bd S,
    α_vert v ≤ G ∧
    (α_vert v).edgeSet = ∅ ∧
    (α_vert v).vertexSet ∩ (ιN '' Γ.N) = {ιN v}
  -- (R5)
  r5_cuff_pos : ∀ C ∈ cuffs S, 1 ≤ q_cuff C
  r5_cuff_card : ∀ C ∈ cuffs S, ∀ v ∈ Γ.N ∩ C, (α_vert v).vertexSet.ncard = q_cuff C
  -- (R6)
  r6_border : ∀ c ∈ Γ.C, (c ∩ bd S).Nonempty →
    ∀ u v : S, u ≠ v → tilde c = {u, v} →
      α_vert u ≤ α_cell c ∧
      α_vert v ≤ α_cell c ∧
      (HasDisjointPaths (α_cell c).skeleton (α_vert u).vertexSet (α_vert v).vertexSet
          (α_vert u).vertexSet.ncard ∨
       ∃ c' ∈ Γ.C, (tilde c').ncard = 3 ∧ u ∈ tilde c' ∧ v ∈ tilde c')
  -- (R7)
  r7_inter : ∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C, c₁ ≠ c₂ →
    (∀ C ∈ cuffs S, ¬ ((c₁ ∩ C).Nonempty ∧ (c₂ ∩ C).Nonempty)) →
    (α_cell c₁ ∩ α_cell c₂).vertexSet = ιN '' (tilde c₁ ∩ tilde c₂)
  -- (R8)
  r8_order : ∀ C ∈ cuffs S, ∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C,
    (c₁ ∩ C).Nonempty → (c₂ ∩ C).Nonempty →
    ∀ u₁ ∈ Γ.N ∩ C, ∀ u₂ ∈ Γ.N ∩ C,
      InCuffOrder C c₁ u₁ c₂ u₂ →
      α_cell c₁ ∩ α_cell c₂ ≤ α_vert u₁ ∪ α_vert u₂
  -- (R9)
  r9_three : ∀ c ∈ Γ.C, (tilde c).ncard = 3 →
    ¬ CanBeDrawnInDiscWithBoundary (α_cell c) (ιN '' (tilde c))
  -- (R10)
  r10_null : ∀ C ∈ cuffs S, (⋂ u ∈ Γ.N ∩ C, (α_vert u).vertexSet) = ∅

/-- A portrait has depth `≤ q` if `q_cuff C ≤ q` for every cuff `C ∈ cuffs S`. -/
def PortraitHasDepthLe {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    (G : Hypergraph α β) (Γ : GM17.Painting S) (ιN : S → α)
    (α_cell : Set S → Hypergraph α β) (α_vert : S → Hypergraph α β) (q : ℕ) : Prop :=
  ∃ q_cuff : Set S → ℕ,
    IsPortrait G Γ ιN α_cell α_vert q_cuff ∧
    ∀ C ∈ cuffs S, q_cuff C ≤ q

/-- Graph Minors XXI, Section 9 (page 38 of the preprint):
"If $\mathcal{T}$ is a tangle in $G$, a portrait $\Gamma, \alpha$ of $G$ in $\Sigma$ *surrounds*
$\mathcal{T}$ if $\alpha(c)$ is small for each $c \in C(\Gamma)$." -/
def PortraitSurroundsTangle {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    (Γ : GM17.Painting S) (α_cell : Set S → Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∀ c ∈ Γ.C, IsSmallSubgraph 𝒯 (α_cell c)

end GM21
end GraphMinor
