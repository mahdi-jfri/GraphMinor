module

public import GraphMinor.GM20.Assembled
public import GraphMinor.GM16.Section1Statements
public import GraphMinor.Compute.DPStatement
public import GraphMinor.GM06.Defs
public import GraphMinor.GM16.Defs
public import GraphMinor.Minor.Basic
public import GraphMinor.Surface.TopologyStatements
public import Mathlib.Data.List.Forall2
public import Mathlib.Order.WellFoundedSet

/-!
# Definitions for Graph Minors VIII (A Kuratowski Theorem for General Surfaces)

This file formalizes the definitions of N. Robertson and P. D. Seymour,
*Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288:

- **Section 1 (pages 255–257):**
  - Finite graphs (`IsFiniteGraph`), antichains of graphs (`IsGraphAntichain`), genus of a surface
    and of a graph (`surfaceGenus`, `graphGenus`, `HasGraphGenusLE`), and topological containment
    (`contractEdgeInto`, `SuppressDivalentStep`, `ObtainedBySuppressingDivalent`,
    `IsTopologicallyContained`), as well as `T_surface` ($T(\Sigma)$).
- **Section 2 (pages 257–259):**
  - Graph properties and hereditary properties (`IsGraphProperty`, `IsHereditaryProperty`),
    proper minors (`IsProperMinor`), $S(P)$ and $T(P)$ (`minorMinimalOut`, `topMinimalOut`),
     finite up to isomorphism (`IsFiniteUpToIso`), vertex valency (`vertexValency`), splitting a
    vertex and splitting vertices (`ObtainedBySplittingVertex`, `ObtainedBySplittingVertices`),
    $Z(H)$ (`splitClass`), and the invariant $N(G) = 2|E(G)| - 3|V'|$ (`splitInvariantN`).
- **Section 3 (pages 259–260):**
  - Quasi-orders (`IsQuasiOrder`), well-quasi-orders (`IsWellQuasiOrder`), product quasi-order
    (`prodLE`), and finite sequence quasi-order $\mathbf{Q}^{<\omega}$ (`seqLE`).
- **Section 4 (pages 260–262):**
  - Simulations of graphs (`IsGraphSimulation`, equivalent to `IsMinorModel`), grafts (`Graft`),
    simulations of grafts (`IsGraftSimulation`, `IsGraftSimulatedIn`), well-rooted classes of
    grafts (`IsWellRootedGraftClass`), index of a graft and of a class of grafts (`Graft.index`,
    `HasBoundedGraftIndex`, `graftClassIndex`), rooted graphs (`RootedGraph`), simulations of
    rooted graphs (`IsRootedGraphSimulation`, `IsRootedGraphSimulatedIn`), underlying graft of a
    rooted graph (`RootedGraph.toGraft`), and well-rooted classes of rooted graphs
    (`IsWellRootedRootedGraphClass`, `HasBoundedRootedGraphIndex`).
- **Section 5 (pages 262–263):**
  - Surface embedding of a graft (`EmbedsGraft`, using `Surface.GraftDrawing`) and of a class of
    grafts (`EmbedsGraftClass`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Relation Topology Graph GraphMinor.Surface

universe u v u' v' w

/-! ## Section 1: Graphs, Antichains, Topological Containment, and Genus (pages 255–257) -/

/-- A graph $G : \operatorname{Graph} \alpha \beta$ is finite if both its vertex set $V(G)$ and its
edge set $E(G)$ are finite.
Graph Minors VIII, Section 1 (page 255): "Graphs are finite, and may have loops or multiple
edges." -/
def IsFiniteGraph {α : Type u} {β : Type v} (G : Graph α β) : Prop :=
  V(G).Finite ∧ E(G).Finite

/-- A set $A$ of finite graphs is an *antichain* if no member of $A$ is isomorphic to a minor of
another distinct member of $A$.
Graph Minors VIII, Section 1 (page 256): "it is an antichain, that is, no member of $A$ is
isomorphic to a minor of another." -/
def IsGraphAntichain {α : Type u} {β : Type v} (A : Set (Graph α β)) : Prop :=
  (∀ G ∈ A, IsFiniteGraph G) ∧ ∀ G ∈ A, ∀ H ∈ A, G ≠ H → ¬ IsIsoMinor G H

/-- The *valency* of a vertex $v$ in a graph $G$ is the number of edges incident with it, counting
loops twice.
Graph Minors VIII, Section 2 (page 258): "(The *valency* of a vertex is the number of edges
incident with it, counting loops twice.)" -/
noncomputable abbrev vertexValency {α : Type u} {β : Type v} (G : Graph α β) (v : α) : ℕ :=
  GM06.vertexValency G v

/-- The graph on the same types $\alpha, \beta$ obtained from $G$ by contracting an edge $e$ with
ends $u, v$ into the vertex $u$ (collapsing $v$ to $u$ and deleting $e$).
Graph Minors VIII, Section 1 (page 256) and Section 2 (page 258). -/
noncomputable def contractEdgeInto {α : Type u} {β : Type v} (G : Graph α β) (e : β) (u v : α) :
    Graph α β := by
  classical
  exact (G.map (fun x => if x = v then u else x)).deleteEdges {e}

/-- $G'$ is obtained from $G$ by *suppressing a divalent vertex* $v$ if $v \in V(G)$ has valency 2
and is incident with two distinct edges $e, f \in E(G)$, where $e$ links $u$ and $v$, and $G'$ is
obtained by contracting $e$ into $u$.
Graph Minors VIII, Section 1 (page 255): "A graph $G$ topologically contains $H$ if we may obtain a
graph isomorphic to $H$ from some subgraph of $G$ by suppressing some divalent vertices." -/
def SuppressDivalentStep {α : Type u} {β : Type v} (G G' : Graph α β) : Prop :=
  ∃ e f : β, ∃ u v : α,
    e ≠ f ∧ G.IsLink e u v ∧ G.Inc f v ∧ vertexValency G v = 2 ∧
    G' = contractEdgeInto G e u v

/-- $G'$ is obtained from $G_0$ by *suppressing some divalent vertices* if $G'$ is reachable from
$G_0$ by a finite sequence of divalent-vertex suppression steps.
Graph Minors VIII, Section 1 (page 255). -/
def ObtainedBySuppressingDivalent {α : Type u} {β : Type v} (G₀ G' : Graph α β) : Prop :=
  ReflTransGen SuppressDivalentStep G₀ G'

/-- A graph $H$ is *topologically contained* in a graph $G$ (or $G$ *topologically contains* $H$) if
a graph isomorphic to $H$ can be obtained from some subgraph $G_0 \le G$ by suppressing some
divalent vertices.
Graph Minors VIII, Section 1 (page 255): "A graph $G$ topologically contains $H$ if we may obtain a
graph isomorphic to $H$ from some subgraph of $G$ by suppressing some divalent vertices." -/
def IsTopologicallyContained {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (H : Graph α' β') (G : Graph α β) : Prop :=
  ∃ G₀ ≤ G, ∃ G' : Graph α β, ObtainedBySuppressingDivalent G₀ G' ∧ Nonempty (Iso H G')

/-- The genus (orientable or non-orientable) of a surface $\Sigma$, defined for connected surfaces
homeomorphic to $\Sigma(a, b, c)$ as the minimum of $a + b$ (so $a$ when $b = 0$ and $b$ when
$a = 0$), and 0 if not homeomorphic to any model.
Graph Minors VIII, Section 1 (page 256). -/
noncomputable def surfaceGenus (S : Type w) [TopologicalSpace S] : ℕ :=
  sInf {g : ℕ | ∃ a b c : ℕ, Nonempty (S ≃ₜ SurfaceModel a b c) ∧ a + b ≤ g}

/-- The *genus* of a graph $G$ is the minimum genus (orientable or non-orientable) of the surfaces
in which it can be drawn.
Graph Minors VIII, Section 1 (page 256): "The genus of a graph is the minimum genus (orientable or
non-orientable) of the surfaces in which it can be drawn." -/
noncomputable def graphGenus {α : Type u} {β : Type v} (G : Graph α β) : ℕ :=
  sInf {g : ℕ | ∃ a b c : ℕ, a + b ≤ g ∧ GM16.CanBeDrawnIn (SurfaceModel a b c) G}

/-- A graph $G$ has genus at most $g$ if there is a model surface $\Sigma(a, b, c)$ of genus
$a + b \le g$ in which $G$ can be drawn.
Graph Minors VIII, Section 1 (page 256). -/
def HasGraphGenusLE {α : Type u} {β : Type v} (G : Graph α β) (g : ℕ) : Prop :=
  ∃ a b c : ℕ, a + b ≤ g ∧ GM16.CanBeDrawnIn (SurfaceModel a b c) G

/-! ## Section 2: Hereditary Properties, Splitting Vertices, $S(P)$, $T(P)$, and $Z(H)$ (pages 257–259) -/

/-- A class $C$ of finite graphs is *finite up to isomorphism* if there is a finite subset
$F \subseteq C$ such that every graph in $C$ is isomorphic to some graph in $F$.
Graph Minors VIII, Section 1 (page 256) and Section 2 (page 257). -/
def IsFiniteUpToIso {α : Type u} {β : Type v} (C : Set (Graph α β)) : Prop :=
  ∃ F : Set (Graph α β), F.Finite ∧ F ⊆ C ∧ ∀ G ∈ C, ∃ G₀ ∈ F, Nonempty (Iso G G₀)

/-- A *property* of finite graphs is a class $P$ of finite graphs closed under isomorphism.
Graph Minors VIII, Section 2 (page 257). -/
def IsGraphProperty {α : Type u} {β : Type v} (P : Set (Graph α β)) : Prop :=
  (∀ G ∈ P, IsFiniteGraph G) ∧
  ∀ G H : Graph α β, IsFiniteGraph G → IsFiniteGraph H → Nonempty (Iso G H) → (G ∈ P ↔ H ∈ P)

/-- A property $P$ of graphs is *hereditary* if whenever $G$ has $P$ and $H$ is a finite graph
isomorphic to a minor of $G$, $H$ also has $P$.
Graph Minors VIII, Section 2 (page 257): "Let $P$ be a property of graphs such that if $G$ has $P$
and $H$ is isomorphic to a minor of $G$ then $H$ has $P$---we call such a property $P$ a
*hereditary property*." -/
def IsHereditaryProperty {α : Type u} {β : Type v} (P : Set (Graph α β)) : Prop :=
  IsGraphProperty P ∧
  ∀ G ∈ P, ∀ H : Graph α β, IsFiniteGraph H → IsIsoMinor H G → H ∈ P

/-- $H$ is a *proper minor* of $G$ if $H$ is isomorphic to a minor of $G$ and not isomorphic to $G$.
Graph Minors VIII, Section 2 (page 257). -/
def IsProperMinor {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (H : Graph α' β') (G : Graph α β) : Prop :=
  IsIsoMinor H G ∧ ¬ Nonempty (Iso H G)

/-- $S(P)$: the class of all finite graphs, minimal under minor containment, without property $P$.
Graph Minors VIII, Section 2 (page 257): "let $S(P)$ denote the class of all graphs, minimal under
minor containment, without property $P$." -/
def minorMinimalOut {α : Type u} {β : Type v} (P : Set (Graph α β)) : Set (Graph α β) :=
  {G : Graph α β | IsFiniteGraph G ∧ G ∉ P ∧
    ∀ H : Graph α β, IsFiniteGraph H → IsProperMinor H G → H ∈ P}

/-- $T(P)$: the class of all finite graphs, minimal under topological containment, without property
$P$.
Graph Minors VIII, Section 2 (page 257): "Let $T(P)$ denote the class of all graphs, minimal under
topological containment, without property $P$". -/
def topMinimalOut {α : Type u} {β : Type v} (P : Set (Graph α β)) : Set (Graph α β) :=
  {G : Graph α β | IsFiniteGraph G ∧ G ∉ P ∧
    ∀ H : Graph α β, IsFiniteGraph H → IsTopologicallyContained H G → ¬ Nonempty (Iso H G) → H ∈ P}

/-- For a surface $\Sigma$, the property of finite graphs that can be drawn in $\Sigma$.
Graph Minors VIII, Section 2 (page 257): "For example, if $\Sigma$ is a surface, the property
“$G$ can be drawn in $\Sigma$” is hereditary." -/
def drawableProperty {α : Type u} {β : Type v} (S : Type w) [TopologicalSpace S] :
    Set (Graph α β) :=
  {G : Graph α β | IsFiniteGraph G ∧ GM16.CanBeDrawnIn S G}

/-- $T(\Sigma)$: the class of all finite graphs which cannot be drawn in $\Sigma$ and which are
minimal with this property under topological containment.
Graph Minors VIII, Section 1 (page 255): "If $\Sigma$ is a surface, let $T(\Sigma)$ denote the class
of all graphs which cannot be drawn in $\Sigma$ and which are minimal with this property under
topological containment." -/
def T_surface {α : Type u} {β : Type v} (S : Type w) [TopologicalSpace S] :
    Set (Graph α β) :=
  topMinimalOut (drawableProperty S)

/-- A graph $G_1$ is obtained from a graph $G_2$ by *splitting a vertex* if there is an edge
$e \in E(G_1)$ with distinct ends $u \ne v$, both with valency at least three in $G_1$, such that
$G_2$ is isomorphic to the graph obtained from $G_1$ by contracting $e$.
Graph Minors VIII, Section 2 (page 258): "Let $e$ be an edge of a graph $G_1$ with distinct ends,
both with valency at least three. (The *valency* of a vertex is the number of edges incident with
it, counting loops twice.) Let $G_2$ be the graph obtained from $G_1$ by contracting $e$. Then we
say that $G_1$ is obtained from $G_2$ by *splitting a vertex*." -/
def ObtainedBySplittingVertex {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (G₁ : Graph α β) (G₂ : Graph α' β') : Prop :=
  ∃ e : β, ∃ u v : α,
    u ≠ v ∧ G₁.IsLink e u v ∧ 3 ≤ vertexValency G₁ u ∧ 3 ≤ vertexValency G₁ v ∧
    Nonempty (Iso G₂ (contractEdgeInto G₁ e u v))

/-- A graph $G_1$ is obtained from a graph $G_2$ by *splitting vertices* if there is a sequence
$G_2 \cong H_0, H_1, \dots, H_k = G_1$ of graphs where for $1 \le i \le k$, $H_i$ is obtained from
$H_{i-1}$ by splitting a vertex.
Graph Minors VIII, Section 2 (page 258): "We say that $G_1$ is obtained from $G_2$ by *splitting
vertices* if there is a sequence $$G_2 = H_0, H_1, H_2, \dots, H_k = G_1$$ of graphs where for
$1 \le i \le k$, $H_i$ is obtained from $H_{i-1}$ by splitting a vertex." -/
def ObtainedBySplittingVertices {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (G₁ : Graph α β) (G₂ : Graph α' β') : Prop :=
  ∃ (k : ℕ) (H_seq : Fin (k + 1) → Graph α β),
    Nonempty (Iso G₂ (H_seq 0)) ∧ H_seq (Fin.last k) = G₁ ∧
    ∀ i : Fin k, ObtainedBySplittingVertex (H_seq i.succ) (H_seq i.castSucc)

/-- $Z(H)$: the class of all finite graphs which can be obtained from $H$ by splitting vertices.
Graph Minors VIII, Section 2 (page 259): "For any graph $H$, let $Z(H)$ denote the class of all
graphs which can be obtained from $H$ by splitting vertices." -/
def splitClass {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (H : Graph α' β') : Set (Graph α β) :=
  {G : Graph α β | IsFiniteGraph G ∧ ObtainedBySplittingVertices G H}

/-- The set $V'$ of vertices of $G$ with valency $\ge 3$.
Graph Minors VIII, Section 2, proof of (2.3) (page 259): "where $V'$ is the set of vertices of $G$
with valency $\ge 3$." -/
def highValencyVerts {α : Type u} {β : Type v} (G : Graph α β) : Set α :=
  {v ∈ V(G) | 3 ≤ vertexValency G v}

/-- The invariant $N(G) = 2|E(G)| - 3|V'|$ from the proof of (2.3), where $V'$ is the set of
vertices of $G$ with valency $\ge 3$.
Graph Minors VIII, Section 2, proof of (2.3) (page 259): "For any graph $G$, define $N(G)$ to be
$2 |E(G)| - 3 |V'|$ where $V'$ is the set of vertices of $G$ with valency $\ge 3$." -/
noncomputable def splitInvariantN {α : Type u} {β : Type v} (G : Graph α β) : ℕ :=
  2 * E(G).ncard - 3 * (highValencyVerts G).ncard

/-! ## Section 3: Well-Quasi-Orders (pages 259–260) -/

/-- A relation $\le$ on $Q$ is a *quasi-order* if it is reflexive and transitive.
Graph Minors VIII, Section 3 (page 259): "A quasi-order $\mathbf{Q} = (Q, \le)$ is a class $Q$
together with a transitive, reflexive relation $\le$." -/
def IsQuasiOrder {Q : Type u} (le : Q → Q → Prop) : Prop :=
  (∀ x, le x x) ∧ (∀ x y z, le x y → le y z → le x z)

/-- A quasi-order $(Q, \le)$ is a *well-quasi-order* if for every countable sequence
$q_1, q_2, \dots$ of members of $Q$ there exist $j > i$ such that $q_i \le q_j$.
Graph Minors VIII, Section 3 (page 259): "A quasi-order $(Q, \le)$ is a well-quasi-order if for
every countable sequence $q_1, q_2, \dots$ of members of $Q$ there exist $j > i \ge 1$ such that
$q_i \le q_j$." -/
def IsWellQuasiOrder {Q : Type u} (le : Q → Q → Prop) : Prop :=
  IsQuasiOrder le ∧ ∀ q : ℕ → Q, ∃ i j : ℕ, i < j ∧ le (q i) (q j)

/-- The product order on $Q_1 \times Q_2$: $(p_1, p_2) \le (q_1, q_2)$ if and only if
$p_1 \le_1 q_1$ and $p_2 \le_2 q_2$.
Graph Minors VIII, Section 3 (page 259): "If $\mathbf{Q}_1 = (Q_1, \le_1)$ and
$\mathbf{Q}_2 = (Q_2, \le_2)$ are quasi-orders, we define
$\mathbf{Q}_1 \times \mathbf{Q}_2 = (Q_1 \times Q_2, \le)$, where $(p_1, p_2) \le (q_1, q_2)$ if
$p_1 \le_1 q_1$ and $p_2 \le_2 q_2$." -/
def prodLE {Q₁ : Type u} {Q₂ : Type v} (le₁ : Q₁ → Q₁ → Prop) (le₂ : Q₂ → Q₂ → Prop)
    (p q : Q₁ × Q₂) : Prop :=
  le₁ p.1 q.1 ∧ le₂ p.2 q.2

/-- The order on finite sequences $Q^{<\omega} = \operatorname{List} Q$:
$(p_1, \dots, p_r) \le (q_1, \dots, q_s)$ if and only if there exist strictly increasing indices
$i_1 < \dots < i_r$ with $p_j \le q_{i_j}$, which is `List.SublistForall₂ le`.
Graph Minors VIII, Section 3 (page 260): "If $(p_1, \dots, p_r)$,
$(q_1, \dots, q_s) \in Q^{<\omega}$, we say that $(p_1, \dots, p_r) \le (q_1, \dots, q_s)$ if there
exist integers $$1 \le i_1 < i_2 < \dots < i_r \le s$$ such that $p_j \le q_{i_j}$
($1 \le j \le r$)." -/
abbrev seqLE {Q : Type u} (le : Q → Q → Prop) : List Q → List Q → Prop :=
  List.SublistForall₂ le

/-! ## Section 4: Simulations, Grafts, and Rooted Graphs (pages 260–262) -/

/-- A *simulation* $\sigma = (\eta_v, \eta_e)$ of a graph $H$ in a graph $G$, satisfying (S1)–(S5).
This is `IsMinorModel H G ηv ηe` from `GraphMinor/Minor/Model.lean`.
Graph Minors VIII, Section 4 (page 260): "We call such a function $\sigma$ a simulation of $H$ in
$G$." -/
abbrev IsGraphSimulation {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (H : Graph α' β') (G : Graph α β) (ηv : α' → Set α) (ηe : β' → β) : Prop :=
  IsMinorModel H G ηv ηe

/-- A *graft* is a pair $(G, T)$ where $G$ is a finite graph and $T \subseteq V(G)$.
Graph Minors VIII, Section 4 (page 260): "A graft is a pair $(G, T)$ where $G$ is a graph and
$T \subseteq V(G)$." -/
structure Graft (α : Type u) (β : Type v) where
  /-- The underlying graph $G$. -/
  G : Graph α β
  /-- The root subset $T \subseteq V(G)$. -/
  T : Set α
  /-- $T$ is a subset of $V(G)$. -/
  T_subset : T ⊆ V(G)
  /-- $G$ is a finite graph. -/
  finite_G : IsFiniteGraph G

/-- The *index* $|T|$ of a graft $(G, T)$.
Graph Minors VIII, Section 4 (page 260): "We call $|T|$ the index of the graft." -/
noncomputable def Graft.index {α : Type u} {β : Type v} (X : Graft α β) : ℕ :=
  X.T.ncard

/-- A *simulation* of a graft $(H, U)$ in a graft $(G, T)$ is a simulation $(\eta_v, \eta_e)$ of $H$
in $G$ satisfying (S6): $|T| = |U|$, and for each $u \in U$, some vertex of $\sigma(u)$ is in $T$.
Graph Minors VIII, Section 4 (page 260): "(S6) $|T| = |U|$, and for each $u \in U$, some vertex of
$\sigma(u)$ is in $T$. (This vertex is necessarily unique.)" -/
def IsGraftSimulation {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (Y : Graft α' β') (X : Graft α β) (ηv : α' → Set α) (ηe : β' → β) : Prop :=
  IsGraphSimulation Y.G X.G ηv ηe ∧
  X.T.ncard = Y.T.ncard ∧
  ∀ u ∈ Y.T, (ηv u ∩ X.T).Nonempty

/-- A graft $Y = (H, U)$ is *simulated in* a graft $X = (G, T)$ if there is a simulation of $Y$ in
$X$.
Graph Minors VIII, Section 4 (page 260): "'$X$ is simulated in $Y$' will always mean 'there is a
simulation of $X$ in $Y$.'" -/
def IsGraftSimulatedIn {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (Y : Graft α' β') (X : Graft α β) : Prop :=
  ∃ (ηv : α' → Set α) (ηe : β' → β), IsGraftSimulation Y X ηv ηe

/-- A class $\mathscr{A}$ of grafts is *well-rooted* if the relation `IsGraftSimulatedIn` is a
well-quasi-order on $\mathscr{A}$.
Graph Minors VIII, Section 4 (page 260): "Let $\mathscr{A}$ be a class of grafts. The relation 'is
simulated in' is a quasi-order of $\mathscr{A}$. If it is a well-quasi-order we say that
$\mathscr{A}$ is well-rooted." -/
def IsWellRootedGraftClass {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) : Prop :=
  ∀ X : ℕ → Graft α β, (∀ n, X n ∈ 𝒜) → ∃ i j : ℕ, i < j ∧ IsGraftSimulatedIn (X i) (X j)

/-- A class $\mathscr{A}$ of grafts *has an index* (or *has bounded index*) if there is a bound
$k \in \mathbb{N}$ such that every member $(G, T) \in \mathscr{A}$ has $|T| \le k$.
Graph Minors VIII, Section 4 (page 260): "If there is a maximum index of the members of
$\mathscr{A}$, we call this the index of $\mathscr{A}$. (Conventionally, the empty set has index
zero.)" -/
def HasGraftClassIndex {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) : Prop :=
  ∃ k : ℕ, ∀ X ∈ 𝒜, X.index ≤ k

/-- The *index* of a class of grafts $\mathscr{A}$ (0 if $\mathscr{A} = \emptyset$, or the supremum
of $|T|$ for $(G, T) \in \mathscr{A}$).
Graph Minors VIII, Section 4 (page 260). -/
noncomputable def graftClassIndex {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) : ℕ :=
  sSup (Graft.index '' 𝒜)

/-- A *rooted graph* is a pair $(G, \tau)$, where $G$ is a finite graph and $\tau$ is a finite
sequence of vertices of $G$.
Graph Minors VIII, Section 4 (page 261): "A rooted graph then is a pair $(G, \tau)$, where $G$ is a
graph and $\tau$ is a finite sequence of vertices of $G$." -/
structure RootedGraph (α : Type u) (β : Type v) where
  /-- The underlying graph $G$. -/
  G : Graph α β
  /-- The finite sequence of root vertices $\tau$. -/
  τ : List α
  /-- Every entry of $\tau$ is a vertex of $G$. -/
  τ_subset : ∀ v ∈ τ, v ∈ V(G)
  /-- $G$ is a finite graph. -/
  finite_G : IsFiniteGraph G

/-- The *index* of a rooted graph $(G, \tau)$ is the length of $\tau$.
Graph Minors VIII, Section 4 (page 261): "The index of a rooted graph is the length of $\tau$." -/
def RootedGraph.index {α : Type u} {β : Type v} (X : RootedGraph α β) : ℕ :=
  X.τ.length

/-- The *underlying graft* $(G, T)$ of a rooted graph $(G, \tau)$, where $T = \{v : v \in \tau\}$.
Graph Minors VIII, Section 4 (page 261): "If $(G, \tau)$ is a rooted graph of index $k$, its
underlying graft is $(G, T)$, where $T = \{\tau(1), \dots, \tau(k)\}$." -/
def RootedGraph.toGraft {α : Type u} {β : Type v} (X : RootedGraph α β) : Graft α β where
  G := X.G
  T := {v | v ∈ X.τ}
  T_subset _ hv := X.τ_subset _ hv
  finite_G := X.finite_G

/-- A *simulation* of a rooted graph $(H, \upsilon)$ in a rooted graph $(G, \tau)$ is a simulation
$(\eta_v, \eta_e)$ of $H$ in $G$ satisfying (S7): $\tau$ and $\upsilon$ have the same length $k$,
for $i < k$, $\tau(i) \in \eta_v(\upsilon(i))$, and for $i < j < k$, $\tau(i) = \tau(j) \iff
\upsilon(i) = \upsilon(j)$.
Graph Minors VIII, Section 4 (page 261): "(S7) $(G, \tau)$ and $(H, v)$ have the same index $k$ say,
and for $1 \le i \le k$, $\tau(i)$ is a vertex of $\sigma(v(i))$; and for $1 \le i < j \le k$,
$\tau(i) = \tau(j)$ if and only if $v(i) = v(j)$." -/
def IsRootedGraphSimulation {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (Y : RootedGraph α' β') (X : RootedGraph α β) (ηv : α' → Set α) (ηe : β' → β) : Prop :=
  IsGraphSimulation Y.G X.G ηv ηe ∧
  ∃ hlen : X.τ.length = Y.τ.length,
    (∀ i : Fin X.τ.length, X.τ[i] ∈ ηv (Y.τ[i.cast hlen])) ∧
    (∀ i j : Fin X.τ.length, X.τ[i] = X.τ[j] ↔ Y.τ[i.cast hlen] = Y.τ[j.cast hlen])

/-- A rooted graph $Y = (H, \upsilon)$ is *simulated in* a rooted graph $X = (G, \tau)$ if there is
a simulation of $Y$ in $X$.
Graph Minors VIII, Section 4 (page 261). -/
def IsRootedGraphSimulatedIn {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (Y : RootedGraph α' β') (X : RootedGraph α β) : Prop :=
  ∃ (ηv : α' → Set α) (ηe : β' → β), IsRootedGraphSimulation Y X ηv ηe

/-- A class $\mathscr{B}$ of rooted graphs is *well-rooted* if the relation
`IsRootedGraphSimulatedIn` is a well-quasi-order on $\mathscr{B}$.
Graph Minors VIII, Section 4 (page 261): "Again, the relation 'is simulated in' is a quasi-order on
any class of rooted graphs; and again if it is a well-quasi-order we say the class of rooted graphs
is well-rooted." -/
def IsWellRootedRootedGraphClass {α : Type u} {β : Type v} (ℬ : Set (RootedGraph α β)) : Prop :=
  ∀ X : ℕ → RootedGraph α β, (∀ n, X n ∈ ℬ) →
    ∃ i j : ℕ, i < j ∧ IsRootedGraphSimulatedIn (X i) (X j)

/-- A class $\mathscr{B}$ of rooted graphs has *bounded index* if there is a bound $k \in \mathbb{N}$
such that every member $(G, \tau) \in \mathscr{B}$ has $|\tau| \le k$.
Graph Minors VIII, Section 4 (page 261). -/
def HasBoundedRootedGraphIndex {α : Type u} {β : Type v} (ℬ : Set (RootedGraph α β)) : Prop :=
  ∃ k : ℕ, ∀ X ∈ ℬ, X.index ≤ k

/-! ## Section 5: Drawings of Grafts (pages 262–263) -/

/-- A surface $\Sigma$ *embeds* a graft $(G, T)$ if $(G, T)$ has a drawing (`GraftDrawing`) in
$\Sigma$.
Graph Minors VIII, Section 5 (page 263): "If $(G, T)$ has a drawing in $\Sigma$, we say that
$\Sigma$ *embeds* $(G, T)$." -/
def EmbedsGraft {α : Type u} {β : Type v} (S : Type w) [TopologicalSpace S]
    (X : Graft α β) : Prop :=
  Nonempty (GraftDrawing X.G X.T S)

/-- A surface $\Sigma$ *embeds* a class of grafts $\mathscr{A}$ if $\Sigma$ embeds every member of
$\mathscr{A}$.
Graph Minors VIII, Section 5 (page 263): "If $\mathcal{A}$ is a set of grafts (respectively, rooted
graphs), we say that $\Sigma$ *embeds* $\mathcal{A}$ if $\Sigma$ embeds (the underlying graft of)
each member of $\mathcal{A}$." -/
def EmbedsGraftClass {α : Type u} {β : Type v} (S : Type w) [TopologicalSpace S]
    (𝒜 : Set (Graft α β)) : Prop :=
  ∀ X ∈ 𝒜, EmbedsGraft S X

/-! ## Section 13: Direct Sums and Vertex Identification (pages 274–275) -/

/-- A graft $(G, T)$ is the *direct sum* $(G_1, T_1) \oplus (G_2, T_2)$ of two grafts $(G_1, T_1)$
and $(G_2, T_2)$ if there is a subset $X \subseteq V(G)$ such that no edge of $G$ has one end in $X$
and the other in $V(G) \setminus X$, $G_1$ and $G_2$ are the restrictions of $G$ to $X$ and
$V(G) \setminus X$, and $T_1 = T \cap X$, $T_2 = T \setminus X$.
Graph Minors VIII, Section 13 (page 274): "Let $(G, T)$ be a graft, and let $X \subseteq V(G)$ be
such that no edge of $G$ has one end in $X$ and the other in $V(G) - X$. Let $G_1$, $G_2$ be the
restrictions of $G$ to $X$ and to $V(G) - X$, respectively, and let $T_1 = T \cap X$,
$T_2 = T - X$. Then $(G_1, T_1)$, $(G_2, T_2)$ are grafts, and we write
$$(G, T) = (G_1, T_1) \oplus (G_2, T_2).$$" -/
def IsGraftDirectSum {α : Type u} {β : Type v} (C A B : Graft α β) : Prop :=
  ∃ X ⊆ V(C.G),
    (∀ e x y, C.G.IsLink e x y → (x ∈ X ↔ y ∈ X)) ∧
    A.G = C.G.induce X ∧
    B.G = C.G.induce (V(C.G) \ X) ∧
    A.T = C.T ∩ X ∧
    B.T = C.T \ X

/-- For two classes of grafts $\mathscr{A}$ and $\mathscr{B}$, $\mathscr{A} \oplus \mathscr{B}$ is
the class of all grafts of the form $A \oplus B$ with $A \in \mathscr{A}$ and $B \in \mathscr{B}$.
Graph Minors VIII, Section 13 (page 274): "Let $\mathscr{A}$, $\mathscr{B}$ be classes of grafts. We
define $\mathscr{A} \oplus \mathscr{B}$ to be the class of all grafts of the form $A \oplus B$,
where $A \in \mathscr{A}$ and $B \in \mathscr{B}$." -/
def graftDirectSumClass {α : Type u} {β : Type v}
    (𝒜 ℬ : Set (Graft α β)) : Set (Graft α β) :=
  {C | ∃ A ∈ 𝒜, ∃ B ∈ ℬ, IsGraftDirectSum C A B}

/-- The vertex map identifying $t_1$ and $t_2$ into $t$ and fixing all other vertices. -/
noncomputable def identifyVerticesFun {α : Type u} (t₁ t₂ t : α) (v : α) : α :=
  open Classical in if v = t₁ ∨ v = t₂ then t else v

/-- A graft $(G', T')$ is *obtained by a vertex identification* from $(G, T)$ if there exist
distinct $t_1, t_2 \in T$ and a vertex $t \notin V(G) \setminus \{t_1, t_2\}$ such that $G'$ is
obtained from $G$ by identifying $t_1$ and $t_2$ into $t$, and $T'$ is either
$T \setminus \{t_1, t_2\}$ or $(T \setminus \{t_1, t_2\}) \cup \{t\}$.
Graph Minors VIII, Section 13 (page 274): "Let $(G, T)$ be a graft and let $t_1, t_2 \in T$ be
distinct. Let $G'$ be obtained from $G$ by identifying $t_1$ and $t_2$ forming a new vertex $t$
say; and let $T'$ be one of $$T - \{t_1, t_2\}, (T - \{t_1, t_2\}) \cup \{t\}.$$ Then $(G', T')$ is
a graft, and we say it is obtained from $(G, T)$ by a *vertex identification*." -/
def ObtainedByVertexIdentification {α : Type u} {β : Type v} (X Y : Graft α β) : Prop :=
  ∃ t₁ ∈ X.T, ∃ t₂ ∈ X.T, t₁ ≠ t₂ ∧
    ∃ t : α, t ∉ V(X.G) \ {t₁, t₂} ∧
      Y.G = X.G.map (identifyVerticesFun t₁ t₂ t) ∧
      (Y.T = X.T \ {t₁, t₂} ∨ Y.T = (X.T \ {t₁, t₂}) ∪ {t})

/-- $W^1(\mathscr{A})$ is the class of all grafts obtained from a member of $\mathscr{A}$ by a
vertex identification.
Graph Minors VIII, Section 13 (pages 274–275). -/
def W1GraftClass {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) : Set (Graft α β) :=
  {Y | ∃ X ∈ 𝒜, ObtainedByVertexIdentification X Y}

/-- $W^i(\mathscr{A})$: defined inductively by $W^0(\mathscr{A}) = \mathscr{A}$ and
$W^{i+1}(\mathscr{A}) = W^1(W^i(\mathscr{A}))$.
Graph Minors VIII, Section 13 (page 275): "If $\mathcal{A}$ is a class of grafts, let
$W^0(\mathcal{A}) = \mathcal{A}$; and inductively, for $i = 1, 2, \dots$ let $W^i(\mathcal{A})$ be
the class of all grafts which can be obtained from a member of $W^{i-1}(\mathcal{A})$ by a vertex
identification." -/
def WiGraftClass {α : Type u} {β : Type v} : ℕ → Set (Graft α β) → Set (Graft α β)
  | 0, 𝒜 => 𝒜
  | i + 1, 𝒜 => W1GraftClass (WiGraftClass i 𝒜)

/-- $W(\mathscr{A}) = \bigcup_{i \ge 0} W^i(\mathscr{A})$.
Graph Minors VIII, Section 13 (page 275): "If $\mathcal{A}$ is a class of grafts, let
$W^0(\mathcal{A}) = \mathcal{A}$; and inductively, for $i = 1, 2, \dots$ let $W^i(\mathcal{A})$ be
the class of all grafts which can be obtained from a member of $W^{i-1}(\mathcal{A})$ by a vertex
identification. Let $$W(\mathcal{A}) = W^0(\mathcal{A}) \cup W^1(\mathcal{A}) \cup \dots.$$" -/
def WGraftClass {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) : Set (Graft α β) :=
  ⋃ i : ℕ, WiGraftClass i 𝒜

/-! ## Section 14: Chains, Trains, and Concatenations (pages 275–279) -/

/-- A subgraph $P$ of $G$ is a *path* of $G$ from $u$ to $v$ parameterized by its duplicate-free
vertex list `verts` ($v_0, \dots, v_m$ with $v_0 = u$, $v_m = v$) and edge list `edges`
($e_0, \dots, e_{m-1}$). -/
structure GraphPathIn {α : Type u} {β : Type v} (G : Graph α β) (P : Graph α β)
    (u v : α) where
  /-- The ordered list of vertices along the path. -/
  verts : List α
  /-- The ordered list of edges along the path. -/
  edges : List β
  /-- `P` is a subgraph of `G`. -/
  le_G : P ≤ G
  /-- The vertex list is nonempty and has length `edges.length + 1`. -/
  length_verts : verts.length = edges.length + 1
  /-- The vertices along the path are distinct. -/
  nodup_verts : verts.Nodup
  /-- The first vertex is `u`. -/
  head_eq : verts[0]'(by omega) = u
  /-- The last vertex is `v`. -/
  last_eq : verts[edges.length]'(by omega) = v
  /-- The vertex set of `P` is the set of vertices in `verts`. -/
  vertexSet_eq : V(P) = {x | x ∈ verts}
  /-- The edge set of `P` is the set of edges in `edges`. -/
  edgeSet_eq : E(P) = {e | e ∈ edges}
  /-- Each edge `edges[s]` links `verts[s]` and `verts[s + 1]` in `P`. -/
  isLink_step : ∀ (s : ℕ) (hs : s < edges.length),
    P.IsLink (edges[s]'hs) (verts[s]'(by omega)) (verts[s + 1]'(by omega))

/-- $P$ is a path of $G$ from a vertex set $A$ to a vertex set $B$ if there exist $u \in A$ and
$v \in B$ such that $P$ is a path of $G$ from $u$ to $v$. -/
def IsGraphPathFromTo {α : Type u} {β : Type v} (G P : Graph α β) (A B : Set α) : Prop :=
  ∃ u ∈ A, ∃ v ∈ B, Nonempty (GraphPathIn G P u v)

/-- $P$ is a path of $G$ (between some pair of vertices). -/
def IsGraphPath {α : Type u} {β : Type v} (G P : Graph α β) : Prop :=
  ∃ u v : α, Nonempty (GraphPathIn G P u v)

/-- The path $P$ is obtained by concatenating the paths $P_1, \dots, P_r$ in order: there is a path
witness `wp : GraphPathIn G P u v` and non-decreasing cut indices
$0 = c_0 \le c_1 \le \dots \le c_r = \text{edges.length}$ such that for each $i < r$, $P_i$ is the
subpath of $P$ from `verts[c_i]` to `verts[c_{i+1}]`. -/
def IsConcatenatedPath {α : Type u} {β : Type v} {r : ℕ}
    (G P : Graph α β) (Ps : Fin r → Graph α β) : Prop :=
  ∃ (u v : α) (wp : GraphPathIn G P u v) (c : Fin (r + 1) → ℕ),
    c ⟨0, Nat.zero_lt_succ r⟩ = 0 ∧
    c (Fin.last r) = wp.edges.length ∧
    Monotone c ∧
    ∀ i : Fin r,
      V(Ps i) = {x | ∃ s : ℕ, c i.castSucc ≤ s ∧ s ≤ c i.succ ∧
        ∃ hs : s < wp.verts.length, wp.verts[s]'hs = x} ∧
      E(Ps i) = {e | ∃ s : ℕ, c i.castSucc ≤ s ∧ s < c i.succ ∧
        ∃ hs : s < wp.edges.length, wp.edges[s]'hs = e} ∧
      Ps i ≤ P

/-- A *path-decomposition* of a graft $(G, T)$ over a class of grafts $\mathscr{A}$: a sequence
$(G_i, Y_{i-1}, Y_i)$ ($1 \le i \le r$) for some $r \ge 1$ satisfying (i)–(v) of Section 14.
Graph Minors VIII, Section 14 (page 275): "A *path-decomposition* of $(G, T)$ over $\mathcal{A}$ is
a sequence $(G_i, Y_{i-1}, Y_i)$ ($1 \le i \le r$) for some $r \ge 1$, such that
(i) $(G_i, Y_{i-1} \cup Y_i) \in \mathcal{A}$ for $1 \le i \le r$
(ii) $G_i$ is a subgraph of $G$ for $1 \le i \le r$, $G_1 \cup \dots \cup G_r = G$, and
$G_1, \dots, G_r$ are mutually edge-disjoint
(iii) for $1 \le h \le i \le j \le r$, $V(G_h) \cap V(G_j) \subseteq V(G_i)$
(iv) for $1 \le i < r$, $V(G_i) \cap V(G_{i+1}) = Y_i$
(v) $T = Y_0 \cup Y_r$." -/
structure GraftPathDecomposition {α : Type u} {β : Type v}
    (𝒜 : Set (Graft α β)) (X : Graft α β) where
  /-- The number of parts $r \ge 1$. -/
  r : ℕ
  /-- $r \ge 1$. -/
  hr : 1 ≤ r
  /-- The subgraphs $G_1, \dots, G_r$ (indexed by `Fin r`). -/
  G : Fin r → Graph α β
  /-- The boundary vertex sets $Y_0, \dots, Y_r$ (indexed by `Fin (r + 1)`). -/
  Y : Fin (r + 1) → Set α
  /-- For each $i$, $Y_{i-1} \cup Y_i \subseteq V(G_i)$. -/
  Y_subset : ∀ i : Fin r, Y i.castSucc ∪ Y i.succ ⊆ V(G i)
  /-- (ii) Each $G_i$ is a subgraph of $G$. -/
  le_G : ∀ i : Fin r, G i ≤ X.G
  /-- (i) Each $(G_i, Y_{i-1} \cup Y_i) \in \mathscr{A}$. -/
  mem_𝒜 : ∀ i : Fin r,
    Graft.mk (G i) (Y i.castSucc ∪ Y i.succ) (Y_subset i)
      ⟨X.finite_G.1.subset (le_G i).vertexSet_mono,
       X.finite_G.2.subset (le_G i).edgeSet_mono⟩ ∈ 𝒜
  /-- (ii) $V(G_1) \cup \dots \cup V(G_r) = V(G)$. -/
  vertexSet_iUnion : (⋃ i : Fin r, V(G i)) = V(X.G)
  /-- (ii) $E(G_1) \cup \dots \cup E(G_r) = E(G)$. -/
  edgeSet_iUnion : (⋃ i : Fin r, E(G i)) = E(X.G)
  /-- (ii) $G_1, \dots, G_r$ are mutually edge-disjoint. -/
  edge_disjoint : ∀ i j : Fin r, i ≠ j → Disjoint E(G i) E(G j)
  /-- (iii) For $1 \le h \le i \le j \le r$, $V(G_h) \cap V(G_j) \subseteq V(G_i)$. -/
  vertex_inter_subset : ∀ h i j : Fin r, h ≤ i → i ≤ j → V(G h) ∩ V(G j) ⊆ V(G i)
  /-- (iv) For $1 \le i < r$, $V(G_i) \cap V(G_{i+1}) = Y_i$. -/
  adj_vertex_inter : ∀ (i : Fin r) (hi : i.1 + 1 < r),
    V(G i) ∩ V(G ⟨i.1 + 1, hi⟩) = Y i.succ
  /-- (v) $T = Y_0 \cup Y_r$. -/
  T_eq : X.T = Y ⟨0, Nat.zero_lt_succ r⟩ ∪ Y (Fin.last r)

/-- The $i$-th graft $(G_i, Y_{i-1} \cup Y_i)$ of a path-decomposition. -/
def GraftPathDecomposition.partGraft {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (i : Fin D.r) :
    Graft α β where
  G := D.G i
  T := D.Y i.castSucc ∪ D.Y i.succ
  T_subset := D.Y_subset i
  finite_G := ⟨X.finite_G.1.subset (D.le_G i).vertexSet_mono,
    X.finite_G.2.subset (D.le_G i).edgeSet_mono⟩

/-- There exist $k$ mutually vertex-disjoint paths of $G$ from $A$ to $B$. -/
def HasDisjointGraphPathsFromTo {α : Type u} {β : Type v}
    (G : Graph α β) (A B : Set α) (k : ℕ) : Prop :=
  ∃ P : Fin k → Graph α β,
    (∀ p : Fin k, IsGraphPathFromTo G (P p) A B) ∧
    (∀ p q : Fin k, p ≠ q → Disjoint V(P p) V(P q))

/-- A graft $(G, T)$ is a *$k$-chain* over $\mathscr{A}$ if it has a path-decomposition
$(G_i, Y_{i-1}, Y_i)$ ($1 \le i \le r$) over $\mathscr{A}$ such that $|Y_i| = k$ ($0 \le i \le r$)
and there are $k$ mutually vertex-disjoint paths of $G$ between $Y_0$ and $Y_r$.
Graph Minors VIII, Section 14 (page 275): "If $k \ge 0$ is an integer, we say that $(G, T)$ is a
*$k$-chain* over $\mathcal{A}$ if it has a path-decomposition $(G_i, Y_{i-1}, Y_i)$ ($1 \le i \le r$)
such that $|Y_i| = k$ ($0 \le i \le r$), and there are $k$ mutually vertex-disjoint paths of $G$
between $Y_0$ and $Y_r$." -/
def IsKChain {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) (k : ℕ) (X : Graft α β) : Prop :=
  ∃ D : GraftPathDecomposition 𝒜 X,
    (∀ i : Fin (D.r + 1), (D.Y i).ncard = k) ∧
    HasDisjointGraphPathsFromTo X.G (D.Y ⟨0, Nat.zero_lt_succ D.r⟩) (D.Y (Fin.last D.r)) k

/-- The class of all $k$-chains over $\mathscr{A}$.
Graph Minors VIII, Section 14 (page 276). -/
def kChainClass {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) (k : ℕ) : Set (Graft α β) :=
  {X | IsKChain 𝒜 k X}

/-- Two grafts $(H, U)$ and $(G, T)$ are *isomorphic* if there is a graph isomorphism
$\phi : H \simeq G$ mapping $U$ onto $T$.
Graph Minors VIII, Section 14 (page 279). -/
def IsGraftIso {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (Y : Graft α' β') (X : Graft α β) : Prop :=
  ∃ φ : Iso Y.G X.G,
    ∀ u : V(Y.G), u.1 ∈ Y.T ↔ (φ.vertexEquiv u).1 ∈ X.T

/-- For a class of grafts $\mathscr{A}$, $\mathscr{A}^*$ is the class of all grafts isomorphic to a
member of $\mathscr{A}$.
Graph Minors VIII, Section 14 (page 279): "If $\mathcal{A}$ is a class of grafts, we denote by
$\mathcal{A}^*$ the class of all grafts isomorphic (in the natural sense) to a member of
$\mathcal{A}$." -/
def isoGraftClass {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) : Set (Graft α β) :=
  {X | ∃ Y ∈ 𝒜, IsGraftIso Y X}

/-- A graft $(G, T)$ is a *$k$-train* over $\mathscr{A}$ if it has a path-decomposition
$(G_i, Y_{i-1}, Y_i)$ ($1 \le i \le r$) over $\mathscr{A}$ such that (i) for $1 \le i < r$,
$|Y_i| = k$, and (ii) if $r \ge 3$ there are $k$ mutually vertex-disjoint paths of $G$ between
$Y_1$ and $Y_{r-1}$.
Graph Minors VIII, Section 14 (page 279): "We say that $(G, T)$ is a *$k$-train* over $\mathcal{A}$
if it has a path-decomposition $(G_i, Y_{i-1}, Y_i)$ ($1 \le i \le r$) over $\mathcal{A}$ such that
(i) for $1 \le i < r$, $|Y_i| = k$
(ii) if $r \ge 3$ there are $k$ mutually vertex-disjoint paths of $G$ between $Y_1$ and $Y_{r-1}$." -/
def IsKTrain {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) (k : ℕ) (X : Graft α β) : Prop :=
  ∃ D : GraftPathDecomposition 𝒜 X,
    (∀ (i : ℕ) (hi : i < D.r + 1), 1 ≤ i → i < D.r → (D.Y ⟨i, hi⟩).ncard = k) ∧
    (∀ hr3 : 3 ≤ D.r,
      HasDisjointGraphPathsFromTo X.G
        (D.Y ⟨1, by omega⟩) (D.Y ⟨D.r - 1, by omega⟩) k)

/-- $L^k(\mathscr{A})$ is the class of all $k$-trains over $\mathscr{A}$.
Graph Minors VIII, Section 14 (page 279): "If $\mathcal{A}$ is a class of grafts, $L^k(\mathcal{A})$
denotes the class of $k$-trains over $\mathcal{A}$". -/
def LKGraftClass {α : Type u} {β : Type v} (k : ℕ) (𝒜 : Set (Graft α β)) : Set (Graft α β) :=
  {X | IsKTrain 𝒜 k X}

/-- $C^k(\mathscr{A}) = L^0(L^1(L^2(\dots(L^k(\mathscr{A}))\dots)))$.
Graph Minors VIII, Section 14 (page 279): "and $C^k(\mathcal{A})$ denotes
$L^0(L^1(L^2(...(L^k(\mathcal{A}))...)))$." -/
def CKGraftClass {α : Type u} {β : Type v} : ℕ → Set (Graft α β) → Set (Graft α β)
  | 0, 𝒜 => LKGraftClass 0 𝒜
  | k + 1, 𝒜 => CKGraftClass k (LKGraftClass (k + 1) 𝒜)

/-- A graft $(G, T)$ is a *concatenation over $\mathscr{A}$* if $(G, T) \in C^k(\mathscr{A})$ for
some $k \ge 0$.
Graph Minors VIII, Section 14 (page 279): "We say that a graft $(G, T)$ is a *concatenation over
$\mathcal{A}$* if $(G, T) \in C^k(\mathcal{A})$ for some $k \ge 0$." -/
def IsConcatenationOver {α : Type u} {β : Type v}
    (𝒜 : Set (Graft α β)) (X : Graft α β) : Prop :=
  ∃ k : ℕ, X ∈ CKGraftClass k 𝒜

/-- The class of all concatenations over $\mathscr{A}$.
Graph Minors VIII, Section 14 (page 279). -/
def concatenationClass {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) : Set (Graft α β) :=
  {X | IsConcatenationOver 𝒜 X}

end GraphMinor.GM08
