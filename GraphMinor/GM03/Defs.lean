module

public import GraphMinor.Statement
public import GraphMinor.Minor.Basic
public import GraphMinor.Planar.Defs
public import GraphMinor.GM07.RegionNest
public import GraphMinor.GM09.Defs
public import GraphMinor.GM16.Defs
public import GraphMinor.GM21.Final
public import GraphMinor.GM22.Defs
public import GraphMinor.Thomas.Basic

/-!
# Definitions for Graph Minors III: Planar Tree-Width

This file formalizes the definitions of N. Robertson and P. D. Seymour,
*Graph Minors. III. Planar Tree-Width*, J. Combin. Theory Ser. B **36** (1984), 49–64:

- **Section 1 (pages 49–51):**
  - Tree-decompositions `(T, X)` (`IsTreeDecomposition`) and tree-width (`TreeWidthLE`,
    `graphTreeWidth`, re-exported from `GraphMinor.GM22`).
  - Minors (`IsIsoMinor`), proper minors (`IsIsoProperMinor`), and minors with specified vertex
    contraction maps $v_i \to u_i$ (`IsProperMinorWithMap`).
  - Paths between vertex sets (`IsPathBetween`) and vertex separation (`Separates`).
- **Section 2 (pages 51–56):**
  - Plane drawings $M$ of a planar graph $G$ (`PlanarDrawing`), region chains (`IsRegionChain`),
    region distance $d(R)$ (`regionDist`), drawing radius $\rho(M)$ (`HasDrawingRadiusLE`,
    `drawingRadius`), and graph radius (`HasRadiusLE`, `graphRadius`).
  - Inside/outside of a circuit $C$ in a drawing $M$ (`IsInsideDisc`, `IsVertexInside`,
    `IsEdgeInside`, `IsCircuitInside`), nested sequences of circuits (`IsNestedCircuitSeq`), and
    $d$-shells (`IsDShell`).
  - The $r \times s$ cylinder (`cylinderGraph`), its circles (`cylinderCircle`) and central circle
    (`cylinderCentralCircle`), its radial lines (`cylinderRadialLine`), the tree $Y_\lambda$
    (`treeY`), and the graph $N(d, \lambda)$ (`graphN`).
- **Section 3 (pages 56–59):**
  - Branches of a tree $T$ at $t$ (`IsBranchAt`) and the unique branch $T_t(v)$ containing all
    bags of $v \notin X_t$ (`treeBranchAt`).
  - Cylinder identification (`IsCylinderIdentification`) and sleeve unions (`IsSleeveUnion`,
    `IsPlanarSleeveUnion`).
- **Section 4 (pages 59–62):**
  - Drawings majoring the $r \times s$ cylinder (`MajorsCylinder`), the radius bound $k(r, s)$ of
    (4.4) (`cylinderRadiusBound`), and the tree-width bound of (4.5) (`cylinderTreeWidthBound`).
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Topology Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM16
open GraphMinor.GM22 GraphMinor.Thomas

export GraphMinor.GM22 (TreeWidthLE graphTreeWidth graphTreeWidthPlusOne IsGraphTreeDecomposition)

universe u v u₁ v₁ u₂ v₂ w

/-! ## Section 1: Introduction (pages 49–51) -/

/-- A *tree-decomposition* of a graph $G$ is a pair $(T, \mathcal{X})$, where $T$ is a tree and
$\mathcal{X} = (X_t : t \in V(T))$ is a family of subsets of $V(G)$ satisfying (W1), (W2), (W3).
Graph Minors III, Section 1 (page 49):
"A *tree-decomposition* of a graph $G$ is a pair $(T, \mathcal{X})$, where $T$ is a tree and
$\mathcal{X} = (X_t : t \in V(T))$ is a family of subsets of $V(G)$, with the following properties:
(W1) $\bigcup_t (X_t : t \in V(T)) = V(G)$.
(W2) For every edge $e$ of $G$ there exists $t \in V(T)$ such that $e$ has both ends in $X_t$.
(W3) For $t, t', t'' \in V(T)$, if $t'$ is on the path of $T$ between $t$ and $t''$ then
$$X_t \cap X_{t''} \subseteq X_{t'}.$$" -/
structure IsTreeDecomposition {α : Type u} {β : Type v} {ι : Type w}
    (G : Graph α β) (T : SimpleGraph ι) (X : ι → Set α) : Prop where
  /-- $T$ is a tree. -/
  isTree : T.IsTree
  /-- Each bag $X_t$ is a subset of $V(G)$. -/
  bag_subset : ∀ t : ι, X t ⊆ V(G)
  /-- (W1) $\bigcup_t (X_t : t \in V(T)) = V(G)$. -/
  iUnion_bags : (⋃ t : ι, X t) = V(G)
  /-- (W2) For every edge $e$ of $G$ there exists $t \in V(T)$ such that $e$ has both ends in
  $X_t$. -/
  edge_in_bag : ∀ ⦃e : β⦄ ⦃u v : α⦄, G.IsLink e u v → ∃ t : ι, u ∈ X t ∧ v ∈ X t
  /-- (W3) For $t, t', t'' \in V(T)$, if $t'$ is on the path of $T$ between $t$ and $t''$ then
  $X_t \cap X_{t''} \subseteq X_{t'}$. -/
  inter_subset_on_path : ∀ ⦃t t' t'' : ι⦄, OnTreePath T t t'' t' → X t ∩ X t'' ⊆ X t'

/-- A tree-decomposition $(T, \mathcal{X})$ has width $\le w$ if $|X_t| - 1 \le w$ (that is,
$|X_t| \le w + 1$) for all $t \in V(T)$.
Graph Minors III, Section 1 (page 49):
"The width of the tree-decomposition is
$$\max_{t \in V(T)} (|X_t| - 1).$$
The graph $G$ has *tree-width* $w$ if $w$ is minimum such that $G$ has a tree-decomposition of
width $w$." -/
def TreeDecompHasWidthLE {α : Type u} {ι : Type w} (X : ι → Set α) (w : ℕ) : Prop :=
  ∀ t : ι, (X t).ncard ≤ w + 1

/-- $H$ is isomorphic to a *proper minor* of $G$.
Graph Minors III, Section 1 (page 50):
"A graph $H$ is a *minor* of a graph $G$ if $H$ can be obtained from a subgraph of $G$ by
contraction. If $H \ne G$ it is a *proper minor*." -/
def IsIsoProperMinor {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    (H : Graph α₁ β₁) (G : Graph α₂ β₂) : Prop :=
  ∃ G' ≤ G, ∃ C ⊆ E(G'), ¬ (G' = G ∧ C = ∅) ∧ Nonempty (Iso H (contract G' C))

/-- $H$ is isomorphic to a proper minor of $G$ with specified vertex contraction map
$v_i \to u_i$ ($1 \le i \le r$).
Graph Minors III, Section 1 (page 50) and Section 3 (page 59):
"If $H$ is a minor of $G$ then each vertex $u$ of $H$ is formed by taking a nonempty subset
$Z_u \subseteq V(G)$ and identifying the vertices in $Z_u$ by contraction. If $v \in Z_u$ we write
$v \to u$." -/
def IsProperMinorWithMap {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {r : ℕ} (H : Graph α₁ β₁) (G : Graph α₂ β₂) (v : Fin r → α₂) (u : Fin r → α₁) : Prop :=
  ∃ (G' : Graph α₂ β₂) (_ : G' ≤ G) (C : Set β₂) (_ : C ⊆ E(G')),
    ¬ (G' = G ∧ C = ∅) ∧
    ∃ φ : Iso H (contract G' C),
      ∀ i : Fin r, ∃ hu : u i ∈ V(H), v i ∈ (φ.vertexEquiv ⟨u i, hu⟩).1

/-- $P$ is a path of $G$ between $X$ and $Y$.
Graph Minors III, Section 1 (page 51):
"When $u, v \in V(G)$, a path between $u$ and $v$ is a path with initial vertex $u$ and terminal
vertex $v$, and when $X, Y \subseteq V(G)$, a path between $X$ and $Y$ is a path with initial
vertex in $X$ and terminal vertex in $Y$." -/
def IsPathBetween {α : Type u} {β : Type v} (G P : Graph α β) (X Y : Set α) : Prop :=
  ∃ u ∈ X, ∃ v ∈ Y, IsGraphPathWithEnds G P u v

/-- A set $Z \subseteq V(G)$ *separates* $X$ and $Y$ in $G$ if no path of $G$ between $X$ and $Y$
avoids $Z$.
Graph Minors III, Section 1 (page 51):
"A path *avoids* $Z \subseteq V(G)$ if no vertex of it is in $Z$. When $Z \subseteq V(G)$, $Z$
*separates* $X$ and $Y$ if no path of $G$ between $X$ and $Y$ avoids $Z$." -/
def Separates {α : Type u} {β : Type v} (G : Graph α β) (Z X Y : Set α) : Prop :=
  ∀ P : Graph α β, IsPathBetween G P X Y → ¬ Disjoint V(P) Z

/-! ## Section 2: Radius (pages 51–56) -/

/-- A plane drawing $M$ of a planar graph $G$, represented via stereographic projection as a
drawing on a 2-sphere `S` together with a designated infinite region `infRegion ∈ drawing.R`.
Graph Minors III, Section 2 (pages 51–52):
"If $G$ is a planar graph, it can be drawn without crossings in the plane, and by a \"drawing\" we
shall always mean such a drawing." -/
structure PlanarDrawing {α : Type u} {β : Type v} (G : Graph α β) where
  /-- The ambient 2-sphere (one-point compactification of the plane). -/
  S : Type
  /-- Topological space structure on `S`. -/
  [topSpace : TopologicalSpace S]
  /-- `S` is a closed surface (`bd S = ∅`). -/
  isClosedSurface : IsClosedSurface S
  /-- `S` is a 2-sphere. -/
  isSphere : IsSphere S
  /-- The topological graph drawing of `G` in `S`. -/
  graphDrawing : GraphDrawing G S
  /-- The infinite region $R_0$ of the drawing $M$. -/
  infRegion : Set S
  /-- `infRegion` is a region of `graphDrawing.drawing`. -/
  infRegion_mem : infRegion ∈ graphDrawing.drawing.R

attribute [instance] PlanarDrawing.topSpace

namespace PlanarDrawing

variable {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)

/-- The underlying surface drawing `Drawing M.S`. -/
abbrev drawing : Drawing M.S := M.graphDrawing.drawing

/-- Every graph with a `PlanarDrawing` is planar (`IsPlanar G`). -/
theorem isPlanar (M : PlanarDrawing G) : IsPlanar G :=
  IsPlanar.of_graphDrawing M.isClosedSurface.isSurface M.isSphere M.graphDrawing

end PlanarDrawing

/-- There is a sequence $R_0, R_1, \dots, R_k$ of regions of $M$, where $R_0$ is the infinite
region, $R_k = R$, and for $1 \le j \le k$ there is a vertex $v$ incident with both $R_{j-1}$ and
$R_j$.
Graph Minors III, Section 2 (pages 51–52):
"For every region $R$ of a drawing $M$, we define $d(R)$ to be the minimum value of $k$ such that
there is a sequence $R_0, R_1, \dots, R_k$ of regions of $M$, where $R_0$ is the
infinite region, $R_k = R$, and for $1 \le j \le k$ there is a vertex $v$ incident with both
$R_{j-1}$ and $R_j$." -/
def IsRegionChain {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)
    (R : Set M.S) (k : ℕ) : Prop :=
  ∃ R_seq : Fin (k + 1) → Set M.S,
    (∀ j : Fin (k + 1), R_seq j ∈ M.drawing.R) ∧
    R_seq ⟨0, Nat.zero_lt_succ k⟩ = M.infRegion ∧
    R_seq ⟨k, Nat.lt_succ_self k⟩ = R ∧
    ∀ j : Fin k, ∃ v ∈ M.drawing.V,
      v ∈ closure (R_seq ⟨j.1, Nat.lt_succ_of_lt j.2⟩) ∧
      v ∈ closure (R_seq ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)

/-- The region distance $d(R)$ in a drawing $M$.
Graph Minors III, Section 2 (pages 51–52). -/
noncomputable def regionDist {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)
    (R : Set M.S) : ℕ :=
  sInf {k : ℕ | IsRegionChain M R k}

/-- A drawing $M$ of $G$ has radius $\rho(M) \le d$ if $d(R) \le d$ for all regions $R$ of $M$.
Graph Minors III, Section 2 (page 52):
"The *radius* $\rho(M)$ of $M$ is the minimum value of $d$ such that $d(R) \le d$ for all regions
$R$ of $M$." -/
def HasDrawingRadiusLE {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)
    (d : ℕ) : Prop :=
  ∀ R ∈ M.drawing.R, ∃ k ≤ d, IsRegionChain M R k

/-- The radius $\rho(M)$ of a drawing $M$.
Graph Minors III, Section 2 (page 52):
"The *radius* $\rho(M)$ of $M$ is the minimum value of $d$ such that $d(R) \le d$ for all regions
$R$ of $M$." -/
noncomputable def drawingRadius {α : Type u} {β : Type v} {G : Graph α β}
    (M : PlanarDrawing G) : ℕ :=
  sInf {d : ℕ | HasDrawingRadiusLE M d}

/-- A planar graph $G$ has radius $\le d$ if it has a plane drawing $M$ with $\rho(M) \le d$.
Graph Minors III, Section 2 (page 52):
"The *radius* of a planar graph is the minimum of the radii of its drawings." -/
def HasRadiusLE {α : Type u} {β : Type v} (G : Graph α β) (d : ℕ) : Prop :=
  ∃ M : PlanarDrawing G, HasDrawingRadiusLE M d

/-- The radius of a planar graph $G$.
Graph Minors III, Section 2 (page 52):
"The *radius* of a planar graph is the minimum of the radii of its drawings." -/
noncomputable def graphRadius {α : Type u} {β : Type v} (G : Graph α β) : ℕ :=
  sInf {d : ℕ | HasRadiusLE G d}

/-- $\Delta \subseteq M.S$ is the closed disc bounded by the circuit $C$ of $G$ on the inside of
$C$ (disjoint from the infinite region $R_0$ of $M$).
Graph Minors III, Section 2 (page 51):
"If $M$ is a drawing of $G$ and $C$ is a circuit of $G$, then every region of $M$ and every vertex
and edge of $G$ not in $C$ is either inside or outside $C$ in $M$, in the obvious sense." -/
def IsInsideDisc {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)
    (C : Graph α β) (Δ : Set M.S) : Prop :=
  IsClosedDisc Δ ∧ discBd Δ = graphDrawingSubgraphU M.graphDrawing C ∧ Disjoint Δ M.infRegion

/-- A vertex $v \in V(G) \setminus V(C)$ is *inside* the circuit $C$ in $M$.
Graph Minors III, Section 2 (page 51). -/
def IsVertexInside {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)
    (C : Graph α β) (v : α) : Prop :=
  v ∈ V(G) \ V(C) ∧ ∃ Δ : Set M.S, IsInsideDisc M C Δ ∧
    graphDrawingVertexSet M.graphDrawing v ⊆ Δ

/-- An edge $e \in E(G) \setminus E(C)$ is *inside* the circuit $C$ in $M$.
Graph Minors III, Section 2 (page 51). -/
def IsEdgeInside {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)
    (C : Graph α β) (e : β) : Prop :=
  e ∈ E(G) \ E(C) ∧ ∃ Δ : Set M.S, IsInsideDisc M C Δ ∧
    graphDrawingEdgeSet M.graphDrawing e ⊆ Δ

/-- A circuit $C'$ of $G$ (disjoint from $C$) is *inside* the circuit $C$ in $M$.
Graph Minors III, Section 2 (page 52). -/
def IsCircuitInside {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)
    (C' C : Graph α β) : Prop :=
  ∃ Δ' Δ : Set M.S, IsInsideDisc M C' Δ' ∧ IsInsideDisc M C Δ ∧ Δ' ⊆ Δ

/-- A *nested sequence of circuits* $C_1, \dots, C_d$ of a drawing $M$ of $G$.
Graph Minors III, Section 2 (page 52):
"Let $M$ be a drawing of a planar graph $G$. By a *nested sequence of circuits* of $M$ we mean a
sequence $C_1, \dots, C_d$ of circuits of $G$ such that for $1 \le j < j' \le d$, $C_j$ and
$C_{j'}$ have no common vertices and $C_{j'}$ is inside $C_j$ in $M$." -/
def IsNestedCircuitSeq {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)
    (d : ℕ) (C : Fin d → Graph α β) : Prop :=
  (∀ j : Fin d, IsGraphCircuit G (C j)) ∧
  ∀ ⦃j j' : Fin d⦄, j < j' → Disjoint V(C j) V(C j') ∧ IsCircuitInside M (C j') (C j)

/-- A *$d$-shell* $C_1, \dots, C_d$ of a drawing $M$ of $G$.
Graph Minors III, Section 2 (page 52):
"By a *$d$-shell* of $M$ (where $d \ge 0$ is an integer) we mean a nested sequence $C_1, \dots, C_d$
of circuits of $M$ such that
(S1) every vertex of $G$ is either in one of $V(C_1), \dots, V(C_d)$ or is inside $C_d$,
(S2) for $1 \le j \le d$, every edge of $G$ which joins two vertices in $V(C_j)$ is in $E(C_j)$." -/
structure IsDShell {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)
    (d : ℕ) (C : Fin d → Graph α β) : Prop where
  /-- $C_1, \dots, C_d$ is a nested sequence of circuits of $M$. -/
  isNested : IsNestedCircuitSeq M d C
  /-- (S1) Every vertex of $G$ is either in one of $V(C_1), \dots, V(C_d)$ or is inside $C_d$. -/
  vertex_in_or_inside : ∀ (hd : 0 < d), ∀ v ∈ V(G),
    (∃ j : Fin d, v ∈ V(C j)) ∨ IsVertexInside M (C ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩) v
  /-- (S2) For $1 \le j \le d$, every edge of $G$ which joins two vertices in $V(C_j)$ is in
  $E(C_j)$. -/
  edge_induced : ∀ (j : Fin d) ⦃e : β⦄ ⦃u v : α⦄,
    G.IsLink e u v → u ∈ V(C j) → v ∈ V(C j) → e ∈ E(C j)

/-- Next spoke index $(i + 1) \bmod r$ on a circle of length $r$. -/
def nextSpoke {r : ℕ} (i : Fin r) : Fin r :=
  ⟨(i.1 + 1) % r, Nat.mod_lt _ i.pos⟩

/-- The $r \times s$ *cylinder* graph, with $r$ radial lines and $s$ concentric circles.
Vertices are `(i, j) : Fin r × Fin s`, where `i : Fin r` indexes the radial lines and `j : Fin s`
indexes the circles from outermost (`j = 0`, representing $C_1$) to innermost (`j = s - 1`,
representing the central circle $C_s$).
Circular edges are `Sum.inl (i, j)` linking `(i, j)` and `(nextSpoke i, j)`.
Radial edges are `Sum.inr (i, j)` (for `j.1 + 1 < s`) linking `(i, j)` and `(i, j + 1)`.
Graph Minors III, Section 2 (page 54):
"When $r \ge 0$, $s > 0$ are integers, the $r \times s$ *cylinder* is the graph shown in Fig. 1,
with $r$ radial lines and $s$ circles.
The \"circular\" circuits are called the *circles* of the cylinder, and the innermost one is called
the *central circle*." -/
def cylinderGraph (r s : ℕ) : Graph (Fin r × Fin s) ((Fin r × Fin s) ⊕ (Fin r × Fin s)) where
  vertexSet := Set.univ
  edgeSet :=
    {e | match e with
      | Sum.inl _ => True
      | Sum.inr p => p.2.1 + 1 < s}
  IsLink e u v :=
    match e with
    | Sum.inl p =>
      (u = p ∧ v = (nextSpoke p.1, p.2)) ∨ (v = p ∧ u = (nextSpoke p.1, p.2))
    | Sum.inr p =>
      ∃ h : p.2.1 + 1 < s,
        (u = p ∧ v = (p.1, ⟨p.2.1 + 1, h⟩)) ∨ (v = p ∧ u = (p.1, ⟨p.2.1 + 1, h⟩))
  isLink_symm e _ := ⟨fun u v h => by
    cases e with
    | inl p => exact h.symm
    | inr p => rcases h with ⟨hs, h⟩; exact ⟨hs, h.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink e _ _ _ _ h1 h2 := by
    cases e with
    | inl p =>
      rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl h3.symm
      · exact Or.inr h3.symm
      · exact Or.inr h4.symm
      · exact Or.inl h4.symm
    | inr p =>
      rcases h1 with ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> rcases h2 with ⟨_, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩
      · exact Or.inl h3.symm
      · exact Or.inr h3.symm
      · exact Or.inr h4.symm
      · exact Or.inl h4.symm
  edge_mem_iff_exists_isLink e := by
    cases e with
    | inl p =>
      simp only [mem_ofPred_eq, true_iff]
      exact ⟨p, (nextSpoke p.1, p.2), Or.inl ⟨rfl, rfl⟩⟩
    | inr p =>
      simp only [mem_ofPred_eq]
      exact ⟨fun h => ⟨p, (p.1, ⟨p.2.1 + 1, h⟩), h, Or.inl ⟨rfl, rfl⟩⟩,
        fun ⟨_, _, h, _⟩ => h⟩
  left_mem_of_isLink _ _ _ _ := Set.mem_univ _

/-- The $j$-th circle $C_j$ of the $r \times s$ cylinder (`0 ≤ j < s`).
Graph Minors III, Section 2 (page 54):
"The \"circular\" circuits are called the *circles* of the cylinder, and the innermost one is called
the *central circle*." -/
def cylinderCircle (r s : ℕ) (j : Fin s) :
    Graph (Fin r × Fin s) ((Fin r × Fin s) ⊕ (Fin r × Fin s)) :=
  ((cylinderGraph r s).induce {p : Fin r × Fin s | p.2 = j}).restrict
    {e | ∃ i : Fin r, e = Sum.inl (i, j)}

/-- The central (innermost) circle $C_s$ (`j = s - 1`) of the $r \times s$ cylinder.
Graph Minors III, Section 2 (page 54). -/
def cylinderCentralCircle (r s : ℕ) (hs : 0 < s) :
    Graph (Fin r × Fin s) ((Fin r × Fin s) ⊕ (Fin r × Fin s)) :=
  cylinderCircle r s ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩

/-- The $i$-th radial line $L_i$ of the $r \times s$ cylinder (`0 ≤ i < r`).
Graph Minors III, Section 2 (page 54). -/
def cylinderRadialLine (r s : ℕ) (i : Fin r) :
    Graph (Fin r × Fin s) ((Fin r × Fin s) ⊕ (Fin r × Fin s)) :=
  ((cylinderGraph r s).induce {p : Fin r × Fin s | p.1 = i}).restrict
    {e | ∃ j : Fin s, e = Sum.inr (i, j)}

/-- Internal vertices of the tree $Y_\lambda$ ($\lambda \ge 1$): the central vertex `none`, together
with heap-indexed binary tree vertices `some (b, m)` in each of the 3 branches `b : Fin 3` for
`m : Fin (2 ^ (lam - 1) - 1)` (representing heap index `m.1 + 1 ∈ {1, …, 2 ^ (lam - 1) - 1}`). -/
abbrev TreeYInternal (lam : ℕ) : Type :=
  Option (Fin 3 × Fin (2 ^ (lam - 1) - 1))

/-- Parent of an internal vertex `t : TreeYInternal lam` towards the center `none` (with `none`
mapped to `none`, as in the proof of (2.5) on page 55). -/
def treeYInternalParent {lam : ℕ} : TreeYInternal lam → TreeYInternal lam
  | none => none
  | some (b, m) =>
    if h : m.1 = 0 then none
    else some (b, ⟨(m.1 + 1) / 2 - 1, by omega⟩)

/-- For each of the $3 \cdot 2^{\lambda - 1}$ end-vertices `i : Fin (3 * 2 ^ (lam - 1))` of
$Y_\lambda$, the internal vertex of $Y_\lambda$ to which leaf `i` is attached. -/
def treeYLeafParent (lam : ℕ) (i : Fin (3 * 2 ^ (lam - 1))) : TreeYInternal lam :=
  if h : lam ≤ 1 then none
  else
    have hpow : 2 ≤ 2 ^ (lam - 1) := by
      have : 1 ≤ lam - 1 := by omega
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (lam - 1) := Nat.pow_le_pow_right (by omega) this
    let b : Fin 3 := ⟨i.1 / 2 ^ (lam - 1), by
      have := i.2
      exact Nat.div_lt_of_lt_mul (by linarith)⟩
    let q : ℕ := i.1 % 2 ^ (lam - 1)
    have hq : q < 2 ^ (lam - 1) := Nat.mod_lt _ (by positivity)
    some (b, ⟨2 ^ (lam - 2) + q / 2 - 1, by
      have h2 : 2 ^ (lam - 1) = 2 * 2 ^ (lam - 2) := by
        rw [← pow_succ', show lam - 2 + 1 = lam - 1 by omega]
      omega⟩)

/-- Vertex type of $N(d, \lambda)$ (`graphN d lam`): internal vertices of $Y_\lambda$ together with
the vertices of the $3 \cdot 2^{\lambda - 1} \times \max(d, 1)$ cylinder (when $d = 0$, the single
circle `Fin 1` consists of the $3 \cdot 2^{\lambda - 1}$ end-vertices of $Y_\lambda$). -/
abbrev GraphNVertex (d lam : ℕ) : Type :=
  TreeYInternal lam ⊕ (Fin (3 * 2 ^ (lam - 1)) × Fin (max d 1))

/-- Edge type of $N(d, \lambda)$ (`graphN d lam`):
- `Sum.inl (Sum.inl t)` for `t : TreeYInternal lam` (`t ≠ none`): internal tree edge of $Y_\lambda$
  joining `t` and `treeYInternalParent t`,
- `Sum.inl (Sum.inr i)` for `i : Fin (3 * 2 ^ (lam - 1))`: leaf edge of $Y_\lambda$ joining
  `treeYLeafParent lam i` and the central circle vertex `(i, max d 1 - 1)`,
- `Sum.inr e`: cylinder edge `e` of the $3 \cdot 2^{\lambda - 1} \times d$ cylinder (when $d \ge 1$). -/
abbrev GraphNEdge (d lam : ℕ) : Type :=
  (TreeYInternal lam ⊕ Fin (3 * 2 ^ (lam - 1))) ⊕
    ((Fin (3 * 2 ^ (lam - 1)) × Fin (max d 1)) ⊕ (Fin (3 * 2 ^ (lam - 1)) × Fin (max d 1)))

/-- The graph $N(d, \lambda)$ for integers $d \ge 0$, $\lambda \ge 1$.
Graph Minors III, Section 2 (page 54):
"Thus $Y_\lambda$ has $3 \cdot 2^{\lambda-1}$ end-vertices. For $d, \lambda \ge 1$, take the
$3 \cdot 2^{\lambda-1} \times d$ cylinder, and let $C_1, \dots, C_d$ be its circles, in order, where
$C_d$ is the central circle. Identify the vertices of the central circle with the end-vertices of
$Y_\lambda$, in the cyclic order provided by the drawing of Fig. 2. The resulting graph we call
$N(d, \lambda)$. (See Fig. 3.) We also set $N(0, \lambda) = Y_\lambda$." -/
def graphN (d lam : ℕ) : Graph (GraphNVertex d lam) (GraphNEdge d lam) where
  vertexSet := Set.univ
  edgeSet :=
    {e | match e with
      | Sum.inl (Sum.inl t) => t ≠ none
      | Sum.inl (Sum.inr _) => True
      | Sum.inr (Sum.inl _) => 0 < d
      | Sum.inr (Sum.inr p) => 0 < d ∧ p.2.1 + 1 < max d 1}
  IsLink e u v :=
    match e with
    | Sum.inl (Sum.inl t) =>
      t ≠ none ∧
        ((u = Sum.inl t ∧ v = Sum.inl (treeYInternalParent t)) ∨
          (v = Sum.inl t ∧ u = Sum.inl (treeYInternalParent t)))
    | Sum.inl (Sum.inr i) =>
      let cIdx : Fin (max d 1) := ⟨max d 1 - 1, by omega⟩
      (u = Sum.inl (treeYLeafParent lam i) ∧ v = Sum.inr (i, cIdx)) ∨
        (v = Sum.inl (treeYLeafParent lam i) ∧ u = Sum.inr (i, cIdx))
    | Sum.inr (Sum.inl p) =>
      0 < d ∧
        ((u = Sum.inr p ∧ v = Sum.inr (nextSpoke p.1, p.2)) ∨
          (v = Sum.inr p ∧ u = Sum.inr (nextSpoke p.1, p.2)))
    | Sum.inr (Sum.inr p) =>
      0 < d ∧ ∃ h : p.2.1 + 1 < max d 1,
        (u = Sum.inr p ∧ v = Sum.inr (p.1, ⟨p.2.1 + 1, h⟩)) ∨
          (v = Sum.inr p ∧ u = Sum.inr (p.1, ⟨p.2.1 + 1, h⟩))
  isLink_symm e _ := ⟨fun u v h => by
    rcases e with (t | i) | (p | p)
    · exact ⟨h.1, h.2.symm⟩
    · exact h.symm
    · exact ⟨h.1, h.2.symm⟩
    · rcases h with ⟨hd, hs, h⟩; exact ⟨hd, hs, h.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink e _ _ _ _ h1 h2 := by
    rcases e with (t | i) | (p | p)
    · rcases h1.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl h3.symm
      · exact Or.inr h3.symm
      · exact Or.inr h4.symm
      · exact Or.inl h4.symm
    · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl h3.symm
      · exact Or.inr h3.symm
      · exact Or.inr h4.symm
      · exact Or.inl h4.symm
    · rcases h1.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl h3.symm
      · exact Or.inr h3.symm
      · exact Or.inr h4.symm
      · exact Or.inl h4.symm
    · rcases h1.2 with ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> rcases h2.2 with ⟨_, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩
      · exact Or.inl h3.symm
      · exact Or.inr h3.symm
      · exact Or.inr h4.symm
      · exact Or.inl h4.symm
  edge_mem_iff_exists_isLink e := by
    rcases e with (t | i) | (p | p)
    · simp only [mem_ofPred_eq]
      exact ⟨fun ht => ⟨Sum.inl t, Sum.inl (treeYInternalParent t), ht, Or.inl ⟨rfl, rfl⟩⟩,
        fun ⟨_, _, ht, _⟩ => ht⟩
    · simp only [mem_ofPred_eq, true_iff]
      exact ⟨Sum.inl (treeYLeafParent lam i), Sum.inr (i, ⟨max d 1 - 1, by omega⟩),
        Or.inl ⟨rfl, rfl⟩⟩
    · simp only [mem_ofPred_eq]
      exact ⟨fun hd => ⟨Sum.inr p, Sum.inr (nextSpoke p.1, p.2), hd, Or.inl ⟨rfl, rfl⟩⟩,
        fun ⟨_, _, hd, _⟩ => hd⟩
    · simp only [mem_ofPred_eq]
      exact ⟨fun ⟨hd, hs⟩ => ⟨Sum.inr p, Sum.inr (p.1, ⟨p.2.1 + 1, hs⟩), hd, hs, Or.inl ⟨rfl, rfl⟩⟩,
        fun ⟨_, _, hd, hs, _⟩ => ⟨hd, hs⟩⟩
  left_mem_of_isLink _ _ _ _ := Set.mem_univ _

/-- The tree $Y_\lambda = N(0, \lambda)$ ($\lambda \ge 1$) with $3 \cdot 2^{\lambda-1}$
end-vertices.
Graph Minors III, Section 2 (page 54):
"When $\lambda \ge 1$ is an integer, the graph $Y_\lambda$ is a tree as shown in Fig. 2.
Thus $Y_\lambda$ has $3 \cdot 2^{\lambda-1}$ end-vertices." -/
abbrev treeY (lam : ℕ) : Graph (GraphNVertex 0 lam) (GraphNEdge 0 lam) :=
  graphN 0 lam

/-! ## Section 3: Sleeve Unions (pages 56–59) -/

/-- A *branch* of a tree $T$ at $t \in V(T)$ is the vertex set $B$ of a connected component of
$T \setminus t$.
Graph Minors III, Section 3 (page 56):
"Let $(T, \mathcal{X})$ be a tree-decomposition of $G$, where $\mathcal{X} = (X_t : t \in V(T))$.
For each $t \in V(T)$, the connected components of $T \setminus t$ are called the *branches* of $T$
at $t$." -/
def IsBranchAt {ι : Type w} (T : SimpleGraph ι) (t : ι) (B : Set ι) : Prop :=
  ∃ s ≠ t, B = {s' : ι | s' ≠ t ∧ ∃ w : T.Walk s s', t ∉ w.support}

/-- For $v \notin X_t$, $T_t(v)$ is the unique branch of $T$ at $t$ which contains all
$t' \in V(T)$ with $v \in X_{t'}$.
Graph Minors III, Section 3 (page 56):
"(3.1) *For $t \in V(T)$ and $v \in V(G)$, either $v \in X_t$, or there is a branch of $T$ at $t$
which contains all $t' \in V(T)$ with $v \in X_{t'}$.*
This follows immediately from (W1), (W3). If $v \notin X_t$, let $T_t(v)$ denote this branch. (It is
unique.)" -/
def treeBranchAt {α : Type u} {ι : Type w} (T : SimpleGraph ι) (X : ι → Set α)
    (t : ι) (v : α) : Set ι :=
  {s' : ι | s' ≠ t ∧ ∃ s : ι, v ∈ X s ∧ ∃ w : T.Walk s s', t ∉ w.support}

/-- Given an edge $e = \{t, t'\}$ of a tree $T$, the vertex set $N$ of the component of $T \setminus e$
containing $t$ (all vertices $n$ of $T$ whose path to $t$ does not pass through $t'$).
Graph Minors III, Section 3 (page 57):
"(3.4) *Let $e$ be an edge of $T$ with ends $t, t'$ say, and let $N, N'$ be the vertex sets of the
two components of $T \setminus e$.*" -/
def treeEdgeSide {ι : Type w} (T : SimpleGraph ι) (t t' : ι) : Set ι :=
  {n : ι | ¬ OnTreePath T t n t'}

/-- $G$ is obtained from $H$ and the $r \times s$ cylinder $S$ (with central circle vertices
$u_1, \dots, u_r$) by identifying $u_i$ with $v_i$ ($1 \le i \le r$), where $v_1, \dots, v_r$ are
distinct vertices of $H$: up to isomorphism of $G$, $G$ has a separation $(H', S')$ with
$V(H') \cap V(S') = \{v'_1, \dots, v'_r\}$, an isomorphism $\phi_H : H \cong H'$ sending $v_i$ to
$v'_i$, and an isomorphism $\phi_S : \text{cylinderGraph } r\ s \cong S'$ sending the $i$-th central
circle vertex $(i, s - 1)$ to $v'_i$.
Graph Minors III, Section 3 (pages 58–59):
"With $S, C_1, \dots, C_s$ as before, let $V(C_s) = \{u_1, \dots, u_r\}$. Let $H$ be another graph,
vertex-disjoint from $S$, and let $v_1, \dots, v_r$ be distinct vertices of $H$. Construct $G$ by
making the identifications $u_1 = v_1, \dots, u_r = v_r$." -/
def IsCylinderIdentification {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {r : ℕ} (G : Graph α₁ β₁) (H : Graph α₂ β₂) (s : ℕ) (hs : 0 < s) (v : Fin r → α₂) : Prop :=
  Function.Injective v ∧ ∃ hv : ∀ i : Fin r, v i ∈ V(H),
  ∃ (H' S' : Graph α₁ β₁) (φH : Iso H H') (φS : Iso (cylinderGraph r s) S'),
    IsGraphSeparation G H' S' ∧
    V(H') ∩ V(S') = Set.range (fun i : Fin r => (φH.vertexEquiv ⟨v i, hv i⟩).1) ∧
    ∀ i : Fin r,
      (φS.vertexEquiv ⟨(i, ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩), Set.mem_univ _⟩).1 =
        (φH.vertexEquiv ⟨v i, hv i⟩).1

/-- $G$ is the *sleeve union* of $G_1, G_2$.
Graph Minors III, Section 3 (page 59):
"Let $(H_1, H_2)$ be a separation of $G$. Let
$$V(H_1) \cap V(H_2) = \{v_1, \dots, v_r\},$$
say. Let $s$ be the least integer such that $2s \ge r$. Let $S_1, S_2$ be graphs, both isomorphic to
the $r \times s$ cylinder, and let the vertex set of the central circles of $S_1, S_2$ be
$\{u_1^1, \dots, u_r^1\}$ and $\{u_1^2, \dots, u_r^2\}$, respectively, in order. Suppose that $S_1$
is a proper minor of $H_2$, where $v_1 \to u_1^1, \dots, v_r \to u_r^1$, and $S_2$ is a proper minor
of $H_1$ where $v_1 \to u_1^2, \dots, v_r \to u_r^2$.
Let $G_k$ be the graph obtained from $H_k, S_k$ by making the identifications $v_i = u_i^k$
$(1 \le i \le r)$ $(k = 1, 2)$. We say that $G$ is the *sleeve union* of $G_1, G_2$."
When $r = 0$, $s = 1$ (since cylinders have $s > 0$, page 54) and $2s \ge r$; for $r \ge 1$,
$s = (r + 1) / 2$ is the least positive integer with $2s \ge r$. -/
def IsSleeveUnion {α : Type u} {β : Type v} {α₁ : Type u₁} {β₁ : Type v₁}
    {α₂ : Type u₂} {β₂ : Type v₂}
    (G : Graph α β) (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) : Prop :=
  ∃ (H₁ H₂ : Graph α β) (r : ℕ) (v : Fin r → α),
    IsGraphSeparation G H₁ H₂ ∧
    Function.Injective v ∧
    V(H₁) ∩ V(H₂) = Set.range v ∧
    let s : ℕ := max 1 ((r + 1) / 2)
    have hs : 0 < s := Nat.le_max_left 1 ((r + 1) / 2)
    let u_cyl : Fin r → Fin r × Fin s := fun i => (i, ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)
    IsProperMinorWithMap (cylinderGraph r s) H₂ v u_cyl ∧
    IsProperMinorWithMap (cylinderGraph r s) H₁ v u_cyl ∧
    IsCylinderIdentification G₁ H₁ s hs v ∧
    IsCylinderIdentification G₂ H₂ s hs v

/-- $G$ is expressible as a sleeve union of two planar graphs $G_1, G_2$.
Graph Minors III, Section 4 (pages 61–62) and Section 5 (pages 62–63). -/
def IsExpressibleAsPlanarSleeveUnion {α : Type u} {β : Type v} (G : Graph α β) : Prop :=
  ∃ (G₁ G₂ : Graph α β), IsPlanar G₁ ∧ IsPlanar G₂ ∧ IsSleeveUnion G G₁ G₂

/-! ## Section 4: The Production of Cylinders (pages 59–62) -/

/-- A drawing $M$ of a planar graph $G$ *majors* the $r \times s$ cylinder ($r \ge 0$, $s \ge 1$).
Graph Minors III, Section 4 (page 59):
"Let $r \ge 0$, $s \ge 1$ be integers, and let $M$ be a drawing of a planar graph $G$. We say that
$M$ *majors* the $r \times s$ cylinder if there is a nested sequence $C_1, \dots, C_s$ of circuits
of $M$ and vertex-disjoint paths $P_1, \dots, P_r$ of $G$, each between $V(C_1)$ and $V(C_s)$, such
that for $1 \le i \le r$ and $1 \le j \le s$, $P_i \cap C_j$ is a path." -/
def MajorsCylinder {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)
    (r s : ℕ) : Prop :=
  ∃ (hs : 0 < s) (C : Fin s → Graph α β) (P : Fin r → Graph α β),
    IsNestedCircuitSeq M s C ∧
    Pairwise (fun i₁ i₂ : Fin r => Disjoint V(P i₁) V(P i₂)) ∧
    (∀ i : Fin r, IsPathBetween G (P i)
      V(C ⟨0, hs⟩) V(C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)) ∧
    ∀ (i : Fin r) (j : Fin s), IsGraphPath G (subgraphInter G (P i) (C j))

/-- The integer $k$ in (4.4) and (4.5):
$k = s + \frac{1}{2} r^2$ ($r$ even), $k = s + \frac{1}{2}(r^2 - 1)$ ($r$ odd), which equals
`s + r ^ 2 / 2` in natural number division for all $r \ge 0$.
Graph Minors III, Section 4 (page 62):
"Suppose that $G$ is not expressible as a sleeve union of two planar
graphs, and $M$ does not major the $r \times s$ cylinder. Then $G$ has radius $<k$, where" -/
def cylinderRadiusBound (r s : ℕ) : ℕ :=
  s + r ^ 2 / 2

/-- The tree-width upper bound in (4.5):
$3(s + \frac{1}{2} r^2) - 2$ ($r$ even), $3(s + \frac{1}{2}(r^2 - 1)) - 2$ ($r$ odd), that is,
`3 * cylinderRadiusBound r s - 2`.
Graph Minors III, Section 4 (page 62):
"If $G$ is a planar graph which is not expressible as the sleeve union of two planar graphs, then
either $G$ has a minor isomorphic to the $r \times s$ cylinder, or it has tree-width at most" -/
def cylinderTreeWidthBound (r s : ℕ) : ℕ :=
  3 * cylinderRadiusBound r s - 2

end GraphMinor.GM03
