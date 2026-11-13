module

public import Mathlib.Combinatorics.Graph.Lattice
public import GraphMinor.GM14.Defs
public import GraphMinor.GM19.Defs2

/-!
# Definitions of Graph Minors XXII (Irrelevant Vertices in Linkage Problems)

This file formalizes the definitions of N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563, Sections 1–8:

- **Section 1 (pages 530–531):**
  - Linkages (`IsLinkage`), terminals of a linkage (`IsTerminal`, `terminals`), $p$-linkages
    (`IsPLinkage`), the pattern of a linkage (`linkagePattern`), vital linkages (`IsVitalLinkage`,
    `IsVitalPLinkage`), tree-decompositions of a graph and their width
    (`IsGraphTreeDecomposition`, `graphTreeDecompWidthPlusOne`, `graphTreeDecompWidth`), and
    tree-width (`graphTreeWidthPlusOne`, `graphTreeWidth`, `TreeWidthLE`).
- **Section 2 (pages 531–534):**
  - The effect of a subgraph $L$ on a vertex set $Z$ (`effectOn`, `HasSameEffectOn`), subgraphs
    vital for $Z$ in $G$ (`IsVitalFor`), $Z$-divisions of a graph (`IsZDivision`,
    `IsIndexedZDivision`), and $L$-connected vertices (`AreConnectedIn`).
- **Section 3 (pages 534–537):**
  - Embeddings of drawings as subgraphs (`Drawing.toEmbeddedGraph`), union of compatible graphs
    (`graphUnion`), $h$-insulation of a point $x \in \Sigma$ from $Y \subseteq \Sigma$ by a drawing
    $\Gamma$ (`IsInsulated`, `insulatedSet`), and havens of order $h$ in a graph (`IsHaven`).
- **Section 4 (pages 537–539):**
  - $T$-variants of a drawing $\Gamma$ in a surface $\Sigma$ (`IsVariant`) and sleeves for a cuff
    $C$ of $\Sigma$ in $\Gamma$ (`IsSleeve`).
- **Section 5 (pages 539–542):**
  - The tangle metric distance $d(X, Y)$ between subsets $X, Y \subseteq \Sigma$
    (`subsetTangleDist`).
- **Section 6 (pages 542–545):**
  - Digraphs (`Digraph`), rooted digraphs (`RootedDigraph`), detail $\le \delta$
    (`RootedDigraph.HasDetailLE`), models of rooted digraphs (`IsRootedDigraphModel`,
    `HasRootedDigraphModel`), the $\delta$-folio (`HasSameDeltaFolio`), bases for a model
    (`IsModelBasis`), and orderings of a finite set (`IsOrderingOf`).
- **Section 7 (pages 545–556):**
  - The system of hypotheses `(J1)`–`(J6)` (`SystemJ1ToJ6`), adequate subsets $\mathcal{A}' \subseteq \mathcal{A}$
    for a model (`IsAdequateFor`), concatenation of finite sequences $\pi + \omega$ (`seqConcat`),
    sufficient subsets $\mathcal{A}' \subseteq \mathcal{A}$ for a model (`IsSufficientFor`),
    hypothesis `(J7)` (`ConditionJ7`), and good/bad members of $\mathcal{A}$ (`IsGoodMember`,
    `IsBadMember`).
- **Section 8 (pages 556–563):**
  - The bipartite incidence graph $G'$ on $Z \cup \mathcal{A}$ (`divisionIncidenceGraph`) and its
    disc drawing condition (`HasDiscDrawingWithBoundaryOrder`), and the hypotheses of Theorem 8.3
    (`Hypotheses83`).
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14

universe u v w u₁ v₁ u₂ v₂

/-! ## Section 1: Introduction (pages 530–531) -/

/-- A *linkage* in a graph $G$ is a subgraph of $G$, every component of which is a path.
Graph Minors XXII, Section 1 (page 530):
"A *linkage* in a graph $G$ is a subgraph of $G$, every component of which is a path. (Paths have
at least one vertex, and have no “repeated” vertices.)" -/
def IsLinkage {α : Type u} {β : Type v} (G L : Graph α β) : Prop :=
  L ≤ G ∧ ∀ P ∈ graphComponents L, IsGraphPath L P

/-- A vertex $v \in V(G)$ is a *terminal* of a linkage $L$ if $v \in V(L)$ and $v$ has degree at
most one in $L$.
Graph Minors XXII, Section 1 (page 530):
"If $L$ is a linkage in $G$, a vertex $v \in V(G)$ is a *terminal* of $L$ if $v \in V(L)$ and $v$
has degree at most one in $L$." -/
def IsTerminal {α : Type u} {β : Type v} (L : Graph α β) (v : α) : Prop :=
  v ∈ V(L) ∧ vertexValency L v ≤ 1

/-- The set of all terminals of a linkage $L$.
Graph Minors XXII, Section 1 (page 530):
"If $L$ is a linkage in $G$, a vertex $v \in V(G)$ is a *terminal* of $L$ if $v \in V(L)$ and $v$
has degree at most one in $L$." -/
def terminals {α : Type u} {β : Type v} (L : Graph α β) : Set α :=
  {v ∈ V(L) | vertexValency L v ≤ 1}

/-- A linkage $L$ in $G$ is a *$p$-linkage* if it has at most $p$ terminals.
Graph Minors XXII, Section 1 (page 530):
"We say a linkage $L$ is a $p$-linkage if it has at most $p$ terminals." -/
def IsPLinkage {α : Type u} {β : Type v} (G L : Graph α β) (p : ℕ) : Prop :=
  IsLinkage G L ∧ (terminals L).ncard ≤ p

/-- The *pattern* of a linkage $L$ is the partition of its set of terminals determined by the
components of $L$.
Graph Minors XXII, Section 1 (pages 530–531):
"The *pattern*" "of a linkage $L$ is the partition of its set of terminals determined by the
components of $L$; that is, two terminals belong to the same block of the pattern if and only if
they are the ends of some component of $L$." -/
def linkagePattern {α : Type u} {β : Type v} (L : Graph α β) : Set (Set α) :=
  {B : Set α | B.Nonempty ∧ ∃ P ∈ graphComponents L, B = V(P) ∩ terminals L}

/-- A linkage $L$ in $G$ is *vital* if $V(L) = V(G)$ and there is no linkage $L' \ne L$ in $G$ with
the same pattern as $L$.
Graph Minors XXII, Section 1 (page 531):
"We say a linkage $L$ in $G$ is *vital* if $V(L) = V(G)$ and there is no linkage $L' \ne L$ in $G$
with the same pattern as $L$." -/
def IsVitalLinkage {α : Type u} {β : Type v} (G L : Graph α β) : Prop :=
  IsLinkage G L ∧ V(L) = V(G) ∧
    ∀ L' : Graph α β, IsLinkage G L' → linkagePattern L' = linkagePattern L → L' = L

/-- A linkage $L$ in $G$ is a *vital $p$-linkage* if it is both a $p$-linkage and vital in $G$.
Graph Minors XXII, Section 1 (pages 530–531). -/
def IsVitalPLinkage {α : Type u} {β : Type v} (G L : Graph α β) (p : ℕ) : Prop :=
  IsPLinkage G L p ∧ IsVitalLinkage G L

/-- A *tree-decomposition* of a graph $G$ is a pair $(T, W)$, where $T$ is a tree and
$W = (W_t : t \in V(T))$ is a family of subgraphs of $G$ satisfying conditions 1 and 2.
Graph Minors XXII, Section 1 (page 531):
"A *tree-decomposition* of a graph $G$ is a pair $(T, W)$, where $T$ is a tree and
$W = (W_t : t \in V(T))$ is a family of subgraphs of $G$, such that
1. $\bigcup(W_t : t \in V(T)) = G$, and
2. if $t, t', t'' \in V(T)$ and $t'$ lies on the path of $T$ between $t$ and $t''$ then
   $W_t \cap W_{t''} \subseteq W_{t'}$." -/
structure IsGraphTreeDecomposition {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    (G : Graph α β) (T : SimpleGraph ι) (W : ι → Graph α β) : Prop where
  /-- $T$ is a tree. -/
  isTree : T.IsTree
  /-- Each $W_t$ is a subgraph of $G$. -/
  le : ∀ t : ι, W t ≤ G
  /-- 1. $\bigcup(W_t : t \in V(T)) = G$. -/
  sUnion_eq : subgraphSUnion G (Set.range W) = G
  /-- 2. If $t'$ lies on the path of $T$ between $t$ and $t''$ then
  $W_t \cap W_{t''} \subseteq W_{t'}$. -/
  inter_le : ∀ ⦃t t' t'' : ι⦄, OnTreePath T t t'' t' → subgraphInter G (W t) (W t'') ≤ W t'

/-- One plus the width of a graph tree-decomposition $(T, W)$: $\max_{t \in V(T)} |V(W_t)|$.
Graph Minors XXII, Section 1 (page 531):
"Its *width* is $\max (|V(W_t)| - 1 : t \in V(T))$". -/
noncomputable def graphTreeDecompWidthPlusOne {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    (W : ι → Graph α β) : ℕ :=
  sSup (Set.range fun t : ι ↦ V(W t).ncard)

/-- The *width* $\max (|V(W_t)| - 1 : t \in V(T))$ of a tree-decomposition $(T, W)$ of $G$.
Graph Minors XXII, Section 1 (page 531):
"Its *width* is $\max (|V(W_t)| - 1 : t \in V(T))$". -/
noncomputable def graphTreeDecompWidth {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    (W : ι → Graph α β) : ℤ :=
  (graphTreeDecompWidthPlusOne W : ℤ) - 1

/-- One plus the *tree-width* of a graph $G$, as a natural number.
Graph Minors XXII, Section 1 (page 531):
"and the *tree-width* of $G$ is the minimum width of a tree-decomposition of $G$." -/
noncomputable def graphTreeWidthPlusOne {α : Type u} {β : Type v} (G : Graph α β) : ℕ :=
  sInf {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (W : ι → Graph α β),
    IsGraphTreeDecomposition G T W ∧ graphTreeDecompWidthPlusOne W = w}

/-- The *tree-width* of a graph $G$, as an integer ($\ge -1$).
Graph Minors XXII, Section 1 (page 531):
"Its *width* is $\max (|V(W_t)| - 1 : t \in V(T))$, and the *tree-width* of $G$ is the minimum
width of a tree-decomposition of $G$." -/
noncomputable def graphTreeWidth {α : Type u} {β : Type v} (G : Graph α β) : ℤ :=
  (graphTreeWidthPlusOne G : ℤ) - 1

/-- A graph $G$ has *tree-width $\le w$* if it admits a tree-decomposition $(T, W)$ of width at
most $w$, that is, with $|V(W_t)| \le w + 1$ for every $t \in V(T)$.
Graph Minors XXII, Section 1 (page 531). -/
def TreeWidthLE {α : Type u} {β : Type v} (G : Graph α β) (w : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (W : ι → Graph α β),
    IsGraphTreeDecomposition G T W ∧ ∀ t : ι, V(W t).ncard ≤ w + 1

/-! ## Section 2: Vital Subgraphs (pages 531–534) -/

/-- The *effect of $L$ on $Z$* is the partition of $V(L) \cap Z$ in which two vertices belong to
the same block if and only if they belong to the same component of $L$.
Graph Minors XXII, Section 2 (page 531):
"If also $Z \subseteq V(G)$, we define the *effect of* $L$ *on* $Z$ to be the partition of
$V(L) \cap Z$ in which two vertices belong to the same block if and only if they belong to the same
component of $L$." -/
def effectOn {α : Type u} {β : Type v} (L : Graph α β) (Z : Set α) : Set (Set α) :=
  {B : Set α | B.Nonempty ∧ ∃ C ∈ graphComponents L, B = V(C) ∩ Z}

/-- Two subgraphs $L_1, L_2$ have the *same effect on $Z$* if `effectOn L₁ Z = effectOn L₂ Z`.
Graph Minors XXII, Section 2 (page 531):
"If two subgraphs $L_1, L_2$ have the same effect on $Z$ then necessarily
$V(L_1) \cap Z = V(L_2) \cap Z$." -/
def HasSameEffectOn {α : Type u} {β : Type v} (L₁ L₂ : Graph α β) (Z : Set α) : Prop :=
  effectOn L₁ Z = effectOn L₂ Z

/-- A subgraph $L$ is *vital for $Z$ in $G$* if $Z \subseteq V(L)$ and no subgraph $L' \ne L$ in
$G$ has the same effect on $Z$ as $L$.
Graph Minors XXII, Section 2 (page 531):
"We say that a subgraph $L$ is *vital for* $Z$ *in* $G$ if $Z \subseteq V(L)$ and no subgraph
$L' \ne L$ in $G$ has the same effect on $Z$ as $L$." -/
def IsVitalFor {α : Type u} {β : Type v} (G L : Graph α β) (Z : Set α) : Prop :=
  L ≤ G ∧ Z ⊆ V(L) ∧ ∀ L' : Graph α β, L' ≤ G → effectOn L' Z = effectOn L Z → L' = L

/-- A *$Z$-division* of $G$ is a finite set $\mathcal{A} = \{A_1, \ldots, A_k\}$ of subgraphs of
$G$ such that $A_1 \cup \cdots \cup A_k = G$, and $E(A_i \cap A_j) = \emptyset$ and
$V(A_i \cap A_j) \subseteq Z$ for distinct $A_i, A_j \in \mathcal{A}$.
Graph Minors XXII, Section 2 (page 532):
"If $G$ is a graph and $Z \subseteq V(G)$, a *$Z$-division* of $G$ is a set $\{A_1, \ldots, A_k\}$
of subgraphs of $G$, such that $A_1 \cup \cdots \cup A_k = G$, and $E(A_i \cap A_j) = \emptyset$
and $V(A_i \cap A_j) \subseteq Z$ for $1 \le i < j \le k$." -/
def IsZDivision {α : Type u} {β : Type v} (G : Graph α β) (Z : Set α)
    (𝒜 : Set (Graph α β)) : Prop :=
  𝒜.Finite ∧ (∀ A ∈ 𝒜, A ≤ G) ∧ subgraphSUnion G 𝒜 = G ∧
    ∀ A₁ ∈ 𝒜, ∀ A₂ ∈ 𝒜, A₁ ≠ A₂ → Disjoint E(A₁) E(A₂) ∧ V(A₁) ∩ V(A₂) ⊆ Z

/-- An indexed family $(A_i : i \in \iota)$ of subgraphs of $G$ is a *$Z$-division* of $G$ if
$\bigcup_i A_i = G$, and $E(A_i \cap A_j) = \emptyset$ and $V(A_i \cap A_j) \subseteq Z$ for
distinct $i, j \in \iota$.
Graph Minors XXII, Section 2 (page 532):
"If $G$ is a graph and $Z \subseteq V(G)$, a *$Z$-division* of $G$ is a set $\{A_1, \ldots, A_k\}$
of subgraphs of $G$, such that $A_1 \cup \cdots \cup A_k = G$, and $E(A_i \cap A_j) = \emptyset$
and $V(A_i \cap A_j) \subseteq Z$ for $1 \le i < j \le k$." -/
def IsIndexedZDivision {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    (G : Graph α β) (Z : Set α) (A : ι → Graph α β) : Prop :=
  (∀ i : ι, A i ≤ G) ∧ subgraphSUnion G (Set.range A) = G ∧
    ∀ i j : ι, i ≠ j → Disjoint E(A i) E(A j) ∧ V(A i) ∩ V(A j) ⊆ Z

/-- Two vertices $u, v \in V(G)$ are *$L$-connected* if $u, v \in V(L)$ and $u, v$ belong to the
same component of $L$.
Graph Minors XXII, Section 2 (page 532):
"If $L \subseteq G$, we say $u, v \in V(G)$ are *$L$-connected* if $u, v \in V(L)$ and $u, v$
belong to the same component of $L$." -/
def AreConnectedIn {α : Type u} {β : Type v} (L : Graph α β) (u v : α) : Prop :=
  ∃ C ∈ graphComponents L, u ∈ V(C) ∧ v ∈ V(C)

/-! ## Section 3: Drawings in a Disc (pages 534–537) -/

/-- A drawing $\Gamma$ in a surface $\Sigma$ embedded as a graph on vertex type $\alpha$ and edge
type $\beta$ via injections $\iota_V \colon \Sigma \hookrightarrow \alpha$ and
$\iota_E \colon \mathcal{P}(\Sigma) \hookrightarrow \beta$. When $\alpha = \Sigma$ and
$\beta = \mathcal{P}(\Sigma)$ with the identity embeddings, this is `Γ.toGraph`.
Graph Minors XXII, Section 3 (page 534):
"We use graph-theoretic terminology for drawings in the natural way." -/
def _root_.GraphMinor.Surface.Drawing.toEmbeddedGraph {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} (Γ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β) : Graph α β where
  vertexSet := ιV '' Γ.V
  edgeSet := ιE '' Γ.E
  IsLink e x y := ∃ e₀ x₀ y₀, Γ.toGraph.IsLink e₀ x₀ y₀ ∧ ιE e₀ = e ∧ ιV x₀ = x ∧ ιV y₀ = y
  isLink_symm _ _ := ⟨fun _ _ ⟨e₀, x₀, y₀, h, he, hx, hy⟩ => ⟨e₀, y₀, x₀, h.symm, he, hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w ⟨e₀, x₀, y₀, h₁, rfl, rfl, rfl⟩ ⟨e₁, v₀, w₀, h₂, he, rfl, rfl⟩
    obtain rfl : e₀ = e₁ := ιE.injective he.symm
    obtain rfl | rfl := h₁.left_eq_or_eq h₂ <;> simp
  edge_mem_iff_exists_isLink e := by
    constructor
    · rintro ⟨e₀, he₀, rfl⟩
      obtain ⟨x₀, y₀, hlink⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet he₀
      exact ⟨ιV x₀, ιV y₀, e₀, x₀, y₀, hlink, rfl, rfl, rfl⟩
    · rintro ⟨_, _, e₀, x₀, y₀, hlink, rfl, rfl, rfl⟩
      exact ⟨e₀, hlink.edge_mem, rfl⟩
  left_mem_of_isLink := by
    rintro _ _ _ ⟨e₀, x₀, y₀, hlink, rfl, rfl, rfl⟩
    exact ⟨x₀, hlink.left_mem, rfl⟩

/-- The union $G_1 \cup G_2$ of two graphs on the same vertex and edge types without requiring an
ambient supergraph. When $G_1$ and $G_2$ are compatible (`G₁.Compatible G₂`), its links are the
union of the links of $G_1$ and $G_2$. -/
noncomputable def graphUnion {α : Type u} {β : Type v} (G₁ G₂ : Graph α β) : Graph α β :=
  open Classical in
  { vertexSet := V(G₁) ∪ V(G₂)
    edgeSet := E(G₁) ∪ E(G₂)
    IsLink := fun e x y => G₁.IsLink e x y ∨ (e ∉ E(G₁) ∧ G₂.IsLink e x y)
    isLink_symm := fun _ _ => ⟨fun _ _ h =>
      h.elim (fun h₁ => Or.inl h₁.symm) (fun ⟨hne, h₂⟩ => Or.inr ⟨hne, h₂.symm⟩)⟩
    eq_or_eq_of_isLink_of_isLink := by
      rintro e x y v w (h₁ | ⟨hne₁, h₁⟩) (h₂ | ⟨hne₂, h₂⟩)
      · exact h₁.left_eq_or_eq h₂
      · exact (hne₂ h₁.edge_mem).elim
      · exact (hne₁ h₂.edge_mem).elim
      · exact h₁.left_eq_or_eq h₂
    edge_mem_iff_exists_isLink := fun e => by
      constructor
      · intro he
        by_cases he₁ : e ∈ E(G₁)
        · obtain ⟨x, y, h⟩ := G₁.exists_isLink_of_mem_edgeSet he₁
          exact ⟨x, y, Or.inl h⟩
        · rcases he with he₁' | he₂
          · exact (he₁ he₁').elim
          · obtain ⟨x, y, h⟩ := G₂.exists_isLink_of_mem_edgeSet he₂
            exact ⟨x, y, Or.inr ⟨he₁, h⟩⟩
      · rintro ⟨x, y, h | ⟨_, h⟩⟩
        · exact Or.inl h.edge_mem
        · exact Or.inr h.edge_mem
    left_mem_of_isLink := by
      rintro e x y (h | ⟨_, h⟩)
      · exact Or.inl h.left_mem
      · exact Or.inr h.left_mem }

/-- A point $x \in \Sigma$ is *$h$-insulated (in $\Sigma$) from $Y$ (by $\Gamma$)* if there are $h$
closed discs $\Delta_1, \ldots, \Delta_h \subseteq \Sigma$ such that
$x \in \Delta_h \setminus \operatorname{bd}(\Delta_h)$, $Y \cap \Delta_1 = \emptyset$,
$\Delta_{i+1} \subseteq \Delta_i \setminus \operatorname{bd}(\Delta_i)$ for $1 \le i < h$, and
$\operatorname{bd}(\Delta_i) \subseteq U(\Gamma)$ for $1 \le i \le h$.
Graph Minors XXII, Section 3 (page 534):
"We say $x \in \Sigma$ is *$h$-insulated (in $\Sigma$) from $Y$ (by $\Gamma$)* if there are $h$
disjoint circuits of $\Gamma$, all bounding discs in $\Sigma$ disjoint from $Y$ and containing $x$
in their interiors; or more precisely, there are $h$ closed discs
$\Delta_1, \ldots, \Delta_h \subseteq \Sigma$ such that
- $x \in \Delta_h \setminus bd(\Delta_h)$, and $Y \cap \Delta_1 = \emptyset$,
- for $1 \le i < h$, $\Delta_{i+1} \subseteq \Delta_i \setminus bd(\Delta_i)$,
- for $1 \le i \le h$, $bd(\Delta_i) \subseteq U(\Gamma)$." -/
def IsInsulated {S : Type w} [TopologicalSpace S] (Γ : Drawing S) (Y : Set S) (h : ℕ)
    (x : S) : Prop :=
  ∃ Δ : Fin h → Set S,
    (∀ i : Fin h, IsClosedDisc (Δ i) ∧ subBd (Δ i) = discBd (Δ i) ∧ subBd (Δ i) ⊆ Γ.U) ∧
    (∀ (i : Fin h) (hi : i.1 + 1 < h), Δ ⟨i.1 + 1, hi⟩ ⊆ Δ i \ subBd (Δ i)) ∧
    (∀ hpos : 0 < h,
      x ∈ Δ ⟨h - 1, Nat.sub_lt hpos zero_lt_one⟩ \
        subBd (Δ ⟨h - 1, Nat.sub_lt hpos zero_lt_one⟩) ∧
      Disjoint Y (Δ ⟨0, hpos⟩))

/-- The set of all points of $\Sigma$ that are $h$-insulated in $\Sigma$ from $Y$ by $\Gamma$.
Graph Minors XXII, Section 4 (page 537):
"let $T$ be the set of all points of $\Sigma$ that are $h$-insulated from $V(\Gamma \cap K)$ by
$\Gamma$." -/
def insulatedSet {S : Type w} [TopologicalSpace S] (Γ : Drawing S) (Y : Set S) (h : ℕ) : Set S :=
  {x : S | IsInsulated Γ Y h x}

/-- A *haven of order $h$* in a graph $G$ is a function $\beta$ assigning some component $\beta(X)$
of $G \setminus X$ to every subset $X \subseteq V(G)$ with $|X| < h$, such that
$\beta(X) \subseteq \beta(Y)$ whenever $Y \subseteq X \subseteq V(G)$ and $|X| < h$.
Graph Minors XXII, Section 3 (page 535):
"A *haven of order $h$* in $G$ means a function $\beta$ assigning some component $\beta(X)$ of
$G \setminus X$ to every subset $X \subseteq V(G)$ with $|X| < h$, in such a way that
$\beta(X) \subseteq \beta(Y)$ for all $X, Y$ with $Y \subseteq X \subseteq V(G)$ and $|X| < h$." -/
structure IsHaven {α : Type u} {β : Type v} (G : Graph α β) (h : ℕ)
    (β_haven : Set α → Graph α β) : Prop where
  /-- For every $X \subseteq V(G)$ with $|X| < h$, $\beta(X)$ is a component of $G \setminus X$. -/
  isComponent : ∀ X ⊆ V(G), X.ncard < h →
    IsGraphComponent (β_haven X) (G.deleteVerts X)
  /-- Monotonicity: $\beta(X) \subseteq \beta(Y)$ for $Y \subseteq X \subseteq V(G)$ with
  $|X| < h$. -/
  mono : ∀ X Y : Set α, Y ⊆ X → X ⊆ V(G) → X.ncard < h → β_haven X ≤ β_haven Y

/-- A line $F$ in a surface $\Sigma$ is *proper* if its ends are in $\operatorname{bd}(\Sigma)$ and
no other point of $F$ is in $\operatorname{bd}(\Sigma)$.
Graph Minors XXII, Section 3 (page 535):
"A line $F$ in a surface $\Sigma$ is *proper* if its ends are in $bd(\Sigma)$ and no other point of
$F$ is in $bd(\Sigma)$." -/
abbrev IsProperLine {S : Type w} [TopologicalSpace S] (F : Set S) : Prop :=
  IsProperIArc F

/-! ## Section 4: Changing the Drawing (pages 537–539) -/

/-- A drawing $\Gamma'$ is a *$T$-variant of $\Gamma$ in $\Sigma$* if
$V(\Gamma) \setminus T = V(\Gamma') \setminus T$ and every edge in
$(E(\Gamma) \setminus E(\Gamma')) \cup (E(\Gamma') \setminus E(\Gamma))$ has closure contained in
$T$.
Graph Minors XXII, Section 4 (page 537):
"Let $\Gamma$ and $\Gamma'$ be drawings in a surface $\Sigma$, and let $T \subseteq \Sigma$. We say
that $\Gamma'$ is a *$T$-variant of $\Gamma$ in $\Sigma$* if the drawings differ only within $T$;
or more precisely,
- $V(\Gamma) \setminus T = V(\Gamma') \setminus T$, and
- if $e \in E(\Gamma) \setminus E(\Gamma')$ or $e \in E(\Gamma') \setminus E(\Gamma)$, then
  $\bar{e} \subseteq T$." -/
structure IsVariant {S : Type w} [TopologicalSpace S] (Γ Γ' : Drawing S) (T : Set S) : Prop where
  /-- $V(\Gamma) \setminus T = V(\Gamma') \setminus T$. -/
  V_diff_eq : Γ.V \ T = Γ'.V \ T
  /-- If $e \in E(\Gamma) \setminus E(\Gamma')$ then $\bar{e} \subseteq T$. -/
  edge_subset_of_mem_diff_left : ∀ e ∈ Γ.E \ Γ'.E, closure e ⊆ T
  /-- If $e \in E(\Gamma') \setminus E(\Gamma)$ then $\bar{e} \subseteq T$. -/
  edge_subset_of_mem_diff_right : ∀ e ∈ Γ'.E \ Γ.E, closure e ⊆ T

/-- If $C$ is a cuff of $\Sigma$, a *sleeve for $C$ in $\Gamma$* is a closed disc
$\Delta \subseteq \hat{\Sigma}$ such that $\operatorname{bd}(\Delta) \subseteq U(\Gamma)$, $\Delta$
includes the open disc pasted onto $C$ in forming $\hat{\Sigma}$, and
$\Delta \cap \operatorname{bd}(\Sigma) = C$.
Graph Minors XXII, Section 4 (page 538):
"Let $\Sigma$ be a surface. We denote by $\hat{\Sigma}$ the surface obtained from $\Sigma$ by
pasting an open disc onto each cuff of $\Sigma$. Let $\Gamma$ be a drawing in $\Sigma$. If $C$ is a
cuff of $\Sigma$, a *sleeve for $C$ in $\Gamma$* is a closed disc $\Delta \subseteq \hat{\Sigma}$
such that
- $\text{bd}(\Delta) \subseteq U(\Gamma)$,
- $\Delta$ includes the open disc pasted onto $C$ in forming $\hat{\Sigma}$,
- $\Delta \cap \text{bd}(\Sigma) = C$." -/
structure IsSleeve {S : Type w} [TopologicalSpace S] {Shat : Type w} [TopologicalSpace Shat]
    (cap : GM19.IsCappedSurface S Shat) (Γ : Drawing S) (C : Set S) (Δ : Set Shat) : Prop where
  /-- $C$ is a cuff of $\Sigma$. -/
  isCuff : C ∈ cuffs S
  /-- $\Delta \subseteq \hat{\Sigma}$ is a closed disc. -/
  isClosedDisc : IsClosedDisc Δ
  /-- $\operatorname{bd}(\Delta) \subseteq U(\Gamma)$. -/
  bd_subset_U : subBd Δ ⊆ cap.emb '' Γ.U
  /-- $\Delta$ includes the open disc pasted onto $C$ in forming $\hat{\Sigma}$. -/
  cuffDisc_subset : cap.cuffDisc C ⊆ Δ
  /-- $\Delta \cap \operatorname{bd}(\Sigma) = C$. -/
  inter_bd_eq : Δ ∩ (cap.emb '' bd S) = cap.emb '' C

/-! ## Section 5: Tangles (pages 539–542) -/

/-- For a $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with $|F \cap V(\Gamma)| < \operatorname{ord}(\mathcal{T})$,
$\Delta = \operatorname{ins}(F)$ is the closed disc in $\Sigma$ bounded by $F$ such that
$(\Gamma \cap \Delta, \Gamma \cap \overline{\Sigma \setminus \Delta}) \in \mathcal{T}$.
Graph Minors XXII, Section 5 (page 539):
"If $\Gamma$ is a drawing in a surface $\Sigma$ with $\text{bd}(\Sigma) = \emptyset$, a tangle
$\mathcal{T}$ in $\Gamma$ is *respectful* if for every $\Gamma$-normal $O$-arc $F \subseteq \Sigma$
with $|F \cap V(\Gamma)| < \text{ord}(\mathcal{T})$ there is a closed disc $\Delta \subseteq \Sigma$
bounded by $F$ with
$$(\Gamma \cap \Delta, \Sigma \cap \overline{\Sigma \setminus \Delta}) \in \mathcal{T}.$$

In this case, we write $\Delta = \text{ins}(F)$."
The second term $\Sigma \cap \overline{\Sigma \setminus \Delta}$ is a misprint for
$\Gamma \cap \overline{\Sigma \setminus \Delta}$, since the members of $\mathcal{T}$ are separations of
$\Gamma$. The Lean uses the corrected form. See the correction on page 539 in `corrections/GM22.md`.
-/
def IsTangleIns {S : Type w} [TopologicalSpace S] (Γ : Drawing S)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (F Δ : Set S) : Prop :=
  IsClosedDisc Δ ∧ subBd Δ = F ∧
    ((PaintingOrDrawing.drawing Γ).inter Δ, (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T

/-- For $X, Y \subseteq \Sigma$, $d(X, Y)$ is the minimum of $d(a, b)$ over all atoms
$a, b \in A(\Gamma)$ with $a \cap X \ne \emptyset$ and $b \cap Y \ne \emptyset$, or
$\operatorname{ord}(\mathcal{T})$ if one of $X, Y$ is empty.
Graph Minors XXII, Section 5 (page 539):
"If $X, Y \subseteq \Sigma$, we define $d(X, Y)$ to be the minimum of $d(a, b)$, taken over all
atoms $a, b$ with $a \cap X \ne \emptyset$ and $b \cap Y \ne \emptyset$, or
$d(X, Y) = \text{ord}(\mathcal{T})$ if one of $X, Y$ is empty." -/
noncomputable def subsetTangleDist {S : Type w} [TopologicalSpace S] (Γ : Drawing S)
    (ord : ℕ) (d : Set S → Set S → ℕ) (X Y : Set S) : ℕ :=
  open Classical in
  if ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty then
    sInf {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = k}
  else ord

/-! ## Section 6: Rooted Digraphs (pages 542–545) -/

/-- A *digraph* (directed graph), consisting of an underlying undirected multigraph `toGraph`
together with `head` and `tail` functions assigning to each edge $e \in E(G)$ its head and tail
ends in `toGraph`.
Graph Minors XXII, Section 6 (page 542):
"A digraph is a directed graph. When without explanation we use graph-theoretic terms for digraphs,
such as “connected”, “path”, “separation”, “subgraph”, these should be taken to refer to the
undirected graph underlying the digraph." -/
structure Digraph (α : Type u) (β : Type v) where
  /-- The underlying undirected graph of the digraph. -/
  toGraph : Graph α β
  /-- The head of each edge. -/
  head : β → α
  /-- The tail of each edge. -/
  tail : β → α
  /-- For every edge $e \in E(G)$, $e$ links its tail and head in the underlying graph. -/
  isLink_of_mem : ∀ e ∈ E(toGraph), toGraph.IsLink e (tail e) (head e)

/-- The subdigraph of a digraph $G$ determined by a subgraph $H \le G.\text{toGraph}$, inheriting
edge directions from $G$. -/
def Digraph.ofSubgraph {α : Type u} {β : Type v} (G : Digraph α β) (H : Graph α β)
    (hH : H ≤ G.toGraph) : Digraph α β where
  toGraph := H
  head := G.head
  tail := G.tail
  isLink_of_mem e he := (hH.isLink_iff he).mpr (G.isLink_of_mem e (hH.edgeSet_mono he))

/-- A *rooted digraph* $(G, u_1, \ldots, u_q)$ consists of a digraph $G$ and a sequence
$u_1, \ldots, u_q$ of vertices of $G$, not necessarily distinct.
Graph Minors XXII, Section 6 (page 542):
"A rooted digraph $(G, u_1, \ldots, u_q)$ consists of a digraph $G$ and a sequence
$u_1, \ldots, u_q$ of vertices of $G$, not necessarily distinct." -/
structure RootedDigraph (α : Type u) (β : Type v) (q : ℕ) where
  /-- The underlying digraph $G$. -/
  G : Digraph α β
  /-- The sequence $u_1, \ldots, u_q$ of root vertices of $G$. -/
  roots : Fin q → α
  /-- Every root belongs to $V(G)$. -/
  roots_mem : ∀ i : Fin q, roots i ∈ V(G.toGraph)

/-- A rooted digraph $(G, u_1, \ldots, u_q)$ *has detail $\le \delta$* if $|E(G)| \le \delta$ and
$|V(G) \setminus \{u_1, \ldots, u_q\}| \le \delta$.
Graph Minors XXII, Section 6 (page 542):
"A rooted digraph $(G, u_1, \ldots, u_q)$ has detail $\le \delta$, where $\delta \ge 0$ is an
integer, if $|E(G)| \le \delta$ and $|V(G) \setminus \{u_1, \ldots, u_q\}| \le \delta$." -/
def RootedDigraph.HasDetailLE {α : Type u} {β : Type v} {q : ℕ}
    (R : RootedDigraph α β q) (δ : ℕ) : Prop :=
  V(R.G.toGraph).Finite ∧ E(R.G.toGraph).Finite ∧
    E(R.G.toGraph).ncard ≤ δ ∧ (V(R.G.toGraph) \ Set.range R.roots).ncard ≤ δ

/-- A *model* $\phi = (\phi_V, \phi_E)$ of a rooted digraph $(H, v_1, \ldots, v_q)$ in a rooted
digraph $(G, u_1, \ldots, u_q)$.
Graph Minors XXII, Section 6 (page 542):
"If $(G, u_1, \ldots, u_q)$ and $(H, v_1, \ldots, v_q)$ are rooted digraphs, both with $q$ roots,
a model of the second in the first is a function $\phi$ with domain $V(H) \cup E(H)$, such that
(i) for each $v \in V(H)$, $\phi(v)$ is a non-null connected subgraph of $G$; for all distinct
$v, v' \in V(H)$, $\phi(v) \cap \phi(v')$ is null; and for $1 \le i \le q$,
$u_i \in V(\phi(v_i))$;
(ii) for each $e \in E(H)$, $\phi(e)$ is an edge of $G$; for all distinct $e, e' \in E(H)$,
$\phi(e) \ne \phi(e')$; for all $e \in E(H)$ and $v \in V(H)$, $\phi(e) \notin E(\phi(v))$; and if
$e \in E(H)$ has head $v \in V(H)$ and tail $v' \in V(H)$ then $\phi(e)$ has head in $V(\phi(v))$
and tail in $V(\phi(v'))$." -/
structure IsRootedDigraphModel {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {q : ℕ} (R_G : RootedDigraph α₁ β₁ q) (R_H : RootedDigraph α₂ β₂ q)
    (φV : α₂ → Graph α₁ β₁) (φE : β₂ → β₁) : Prop where
  /-- (i) For each $v \in V(H)$, $\phi(v)$ is a subgraph of $G$. -/
  subgraph_of_mem : ∀ v ∈ V(R_H.G.toGraph), φV v ≤ R_G.G.toGraph
  /-- (i) For each $v \in V(H)$, $\phi(v)$ is non-null and connected. -/
  connected_of_mem : ∀ v ∈ V(R_H.G.toGraph), IsGraphConnected (φV v)
  /-- (i) For all distinct $v, v' \in V(H)$, $\phi(v) \cap \phi(v')$ is null. -/
  disjoint_V : ∀ v ∈ V(R_H.G.toGraph), ∀ v' ∈ V(R_H.G.toGraph), v ≠ v' →
    Disjoint V(φV v) V(φV v') ∧ Disjoint E(φV v) E(φV v')
  /-- (i) For $1 \le i \le q$, $u_i \in V(\phi(v_i))$. -/
  root_mem : ∀ i : Fin q, R_G.roots i ∈ V(φV (R_H.roots i))
  /-- (ii) For each $e \in E(H)$, $\phi(e)$ is an edge of $G$. -/
  edge_mem : ∀ e ∈ E(R_H.G.toGraph), φE e ∈ E(R_G.G.toGraph)
  /-- (ii) For all distinct $e, e' \in E(H)$, $\phi(e) \ne \phi(e')$. -/
  injOn_E : InjOn φE E(R_H.G.toGraph)
  /-- (ii) For all $e \in E(H)$ and $v \in V(H)$, $\phi(e) \notin E(\phi(v))$. -/
  edge_not_mem_φV : ∀ e ∈ E(R_H.G.toGraph), ∀ v ∈ V(R_H.G.toGraph), φE e ∉ E(φV v)
  /-- (ii) If $e \in E(H)$ has head $v \in V(H)$, then $\phi(e)$ has head in $V(\phi(v))$. -/
  head_mem : ∀ e ∈ E(R_H.G.toGraph), R_G.G.head (φE e) ∈ V(φV (R_H.G.head e))
  /-- (ii) If $e \in E(H)$ has tail $v' \in V(H)$, then $\phi(e)$ has tail in $V(\phi(v'))$. -/
  tail_mem : ∀ e ∈ E(R_H.G.toGraph), R_G.G.tail (φE e) ∈ V(φV (R_H.G.tail e))

/-- Whether there exists a model of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$.
Graph Minors XXII, Section 6 (page 542). -/
def HasRootedDigraphModel {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {q : ℕ} (R_G : RootedDigraph α₁ β₁ q) (R_H : RootedDigraph α₂ β₂ q) : Prop :=
  ∃ (φV : α₂ → Graph α₁ β₁) (φE : β₂ → β₁), IsRootedDigraphModel R_G R_H φV φE

/-- Two rooted digraphs have the *same $\delta$-folio* if the same rooted digraphs of detail
$\le \delta$ have models in both.
Graph Minors XXII, Section 6 (page 542):
"For $\delta \ge 0$, the $\delta$-folio of $(G, u_1, \ldots, u_q)$ is the class of all rooted
digraphs with detail $\le \delta$ of which there is a model in $(G, u_1, \ldots, u_q)$." -/
def HasSameDeltaFolio {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {q : ℕ} (R₁ : RootedDigraph α₁ β₁ q) (R₂ : RootedDigraph α₂ β₂ q) (δ : ℕ) : Prop :=
  ∀ {αH βH : Type} (R_H : RootedDigraph αH βH q),
    R_H.HasDetailLE δ → (HasRootedDigraphModel R₁ R_H ↔ HasRootedDigraphModel R₂ R_H)

/-- A *basis* for a model $\phi$ of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$ is a subset
$Z \subseteq V(G)$ such that $u_1, \ldots, u_q \in Z$, both ends of $\phi(e)$ belong to $Z$ for
every $e \in E(H)$, and $Z \cap V(\phi(v)) \ne \emptyset$ for every $v \in V(H)$.
Graph Minors XXII, Section 6 (page 542):
"Let $\phi$ be a model of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$. A basis for $\phi$ is
a subset $Z \subseteq V(G)$ such that $u_1, \ldots, u_q \in Z$, both ends of $\phi(e)$ belong to
$Z$ for every $e \in E(H)$, and $Z \cap V(\phi(v)) \ne \emptyset$ for every $v \in V(H)$." -/
structure IsModelBasis {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {q : ℕ} (R_G : RootedDigraph α₁ β₁ q) (R_H : RootedDigraph α₂ β₂ q)
    (φV : α₂ → Graph α₁ β₁) (φE : β₂ → β₁) (Z : Set α₁) : Prop where
  /-- $Z \subseteq V(G)$. -/
  subset_V : Z ⊆ V(R_G.G.toGraph)
  /-- $u_1, \ldots, u_q \in Z$. -/
  roots_mem : ∀ i : Fin q, R_G.roots i ∈ Z
  /-- The head of $\phi(e)$ belongs to $Z$ for every $e \in E(H)$. -/
  head_mem : ∀ e ∈ E(R_H.G.toGraph), R_G.G.head (φE e) ∈ Z
  /-- The tail of $\phi(e)$ belongs to $Z$ for every $e \in E(H)$. -/
  tail_mem : ∀ e ∈ E(R_H.G.toGraph), R_G.G.tail (φE e) ∈ Z
  /-- $Z \cap V(\phi(v)) \ne \emptyset$ for every $v \in V(H)$. -/
  inter_φV_nonempty : ∀ v ∈ V(R_H.G.toGraph), (Z ∩ V(φV v)).Nonempty

/-- An *ordering* of a finite set $X$ is a sequence $x_1, \ldots, x_n$ such that $x_1, \ldots, x_n$
are all distinct and $X = \{x_1, \ldots, x_n\}$.
Graph Minors XXII, Section 6 (page 542):
"If $X$ is a finite set, an ordering of $X$ is a sequence $x_1, \ldots, x_n$ such that
$x_1, \ldots, x_n$ are all distinct and $X = \{x_1, \ldots, x_n\}$." -/
def IsOrderingOf {α : Type u} {n : ℕ} (X : Set α) (π : Fin n → α) : Prop :=
  Function.Injective π ∧ Set.range π = X

/-! ## Section 7: A Generalization (pages 545–556) -/

/-- Concatenation $\pi + \omega$ of two finite sequences $v_1, \ldots, v_p$ and
$w_1, \ldots, w_q$.
Graph Minors XXII, Section 7 (page 547): If $\pi$ and $\omega$ are the finite sequences
$v_1, \dots, v_p$ and $w_1, \dots, w_q$,
"we denote their concatenation $v_1, \dots, v_p, w_1, \dots, w_q$ by $\pi + \omega$." -/
def seqConcat {α : Type u} {p q : ℕ} (π : Fin p → α) (ω : Fin q → α) : Fin (p + q) → α :=
  Fin.append π ω

theorem seqConcat_mem {α : Type u} {p q : ℕ} {s : Set α} {π : Fin p → α} {ω : Fin q → α}
    (hπ : ∀ i : Fin p, π i ∈ s) (hω : ∀ j : Fin q, ω j ∈ s) (k : Fin (p + q)) :
    seqConcat π ω k ∈ s := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa [seqConcat] using hπ i
  · simpa [seqConcat] using hω j

/-- Given a digraph $G$, a subgraph $A \le G.\text{toGraph}$, and a sequence of roots $\pi$ in
$V(A)$, the rooted digraph $(A, \pi)$. -/
def subRootedDigraph {α : Type u} {β : Type v} {r : ℕ} (G : Digraph α β) (A : Graph α β)
    (hA : A ≤ G.toGraph) (π : Fin r → α) (hπ : ∀ i : Fin r, π i ∈ V(A)) :
    RootedDigraph α β r where
  G := G.ofSubgraph A hA
  roots := π
  roots_mem := hπ

/-- A sequence $s_1, s_2, s_3$ of three distinct points on $\operatorname{bd}(D)$ enumerates
$\{s_1, s_2, s_3\}$ in clockwise order around $D$ with respect to the surface orientation `orient`.
Graph Minors XXII, Section 7, (J4) (page 546):
"and if $|\bar{\pi}(A)| = 3$ then $\pi(A)$ enumerates $\bar{\pi}(A)$ in clockwise order around
$D(A)$". -/
def EnumeratesClockwise {S : Type w} [TopologicalSpace S] (orient : GM19.SurfaceOrientation S)
    (D : Set S) {r : ℕ} (π : Fin r → S) : Prop :=
  ∀ h : r = 3,
    orient.pos D (π ⟨0, by omega⟩) (π ⟨1, by omega⟩) (π ⟨2, by omega⟩)

/-- The system of hypotheses `(J1)`–`(J6)` of Graph Minors XXII, Section 7 (page 546):
"(J1) $(G, \omega)$ is a rooted digraph where $\omega$ is the sequence $w_1, \dots, w_q$;
$w_1, \dots, w_q$ are all distinct and $W = \{w_1, \dots, w_q\}$; and $N_W$ is the graph with
vertex set $W$ and no edges.
(J2) $\mathcal{A}$ is a set of subdigraphs of $G$; for all distinct $A, A' \in \mathcal{A}$,
$E(A \cap A') = \emptyset$; for all $A \in \mathcal{A}$, $W \subseteq V(A)$ and $\pi(A)$ is a
sequence of distinct vertices of $A$ not in $W$, with one, two or three terms, and $\bar{\pi}(A)$
is the set of terms of $\pi(A)$; and for all distinct $A, A' \in \mathcal{A}$,
$$V(A \cap A') = (\bar{\pi}(A) \cap \bar{\pi}(A')) \cup W.$$
(J3) $\Gamma \subseteq G \setminus W$ is a directed 2-cell drawing in a sphere $\Sigma$; an
orientation of $\Sigma$ is specified, called “clockwise”; $\mathcal{T}$ is a tangle in $\Gamma$ of
order $\ge \theta \ge 4$, $ins$ is defined by $\mathcal{T}$, and $d$ is the metric of $\mathcal{T}$.
(J4) For each $A \in \mathcal{A}$, $D(A) \subseteq \Sigma$ is a closed disc such that $bd(D(A))$ is
$\Gamma$-normal, $D(A) = ins(bd(D(A)))$, $\Gamma \cap D(A) = \Gamma \cap A$,
$\bar{\pi}(A) = bd(D(A)) \cap V(G)$, and if $|\bar{\pi}(A)| = 3$ then $\pi(A)$ enumerates
$\bar{\pi}(A)$ in clockwise order around $D(A)$; and for all distinct $A, A' \in \mathcal{A}$,
$D(A) \cap D(A') = \bar{\pi}(A) \cap \bar{\pi}(A')$.
(J5) $N = \Gamma \cup N_W \cup \bigcup(A : A \in \mathcal{A})$; $(N, K)$ is a separation of $G$ and
$W \subseteq V(N \cap K)$; $\Delta \subseteq \Sigma$ is a closed disc with
$bd(\Delta) \subseteq U(\Gamma)$; $d(v, \Sigma \setminus \Delta) \ge \theta$ for all
$v \in V(\Gamma \cap K)$; $d(D(A), \Sigma \setminus \Delta) \ge \theta$ for all $A \in \mathcal{A}$
with $A \cap K \ne N_W$; and $v^* \in V(\Gamma)$ with $v^* \notin \Delta$.
(J6) $\delta \ge 0$ is an integer; $(H, \chi)$ is a rooted digraph with detail $\le \delta$; $\phi$
is a model of $(H, \chi)$ in $(G, \omega)$; for each $v \in V(H)$,
$\phi(v) \cap (K \cup \bigcup(A : A \in \mathcal{A}))$ is non-null; and for each $e \in E(H)$,
$\phi(e) \in E(K \cup \bigcup(A : A \in \mathcal{A}))$." -/
structure SystemJ1ToJ6 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    {αH : Type u₁} {βH : Type v₁} {q : ℕ}
    (ιV : S ↪ α) (ιE : Set S ↪ β)
    (R_G : RootedDigraph α β q) (W : Set α)
    (𝒜 : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
    (Γ : Drawing S) (orient : GM19.SurfaceOrientation S)
    (θ ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (ins : Set S → Set S) (d : Set S → Set S → ℕ)
    (D : Graph α β → Set S)
    (N K : Graph α β) (Δ : Set S) (v_star : S)
    (δ : ℕ) (R_H : RootedDigraph αH βH q)
    (φV : αH → Graph α β) (φE : βH → β) : Prop where
  /-- $V(G)$ is finite. -/
  finite_V : V(R_G.G.toGraph).Finite
  /-- $E(G)$ is finite. -/
  finite_E : E(R_G.G.toGraph).Finite
  /-- (J1) $w_1, \ldots, w_q$ are all distinct. -/
  inj_roots : Function.Injective R_G.roots
  /-- (J1) $W = \{w_1, \ldots, w_q\}$. -/
  W_eq : W = Set.range R_G.roots
  /-- (J2) $\mathcal{A}$ is a finite set of subgraphs of $G$. -/
  finite_𝒜 : 𝒜.Finite
  /-- (J2) Every $A \in \mathcal{A}$ is a subgraph of $G$. -/
  le_of_mem_𝒜 : ∀ A ∈ 𝒜, A ≤ R_G.G.toGraph
  /-- (J2) For all distinct $A, A' \in \mathcal{A}$, $E(A \cap A') = \emptyset$. -/
  edge_disjoint_𝒜 : ∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ≠ A' → Disjoint E(A) E(A')
  /-- (J2) For all $A \in \mathcal{A}$, $W \subseteq V(A)$. -/
  W_subset_V : ∀ A ∈ 𝒜, W ⊆ V(A)
  /-- (J2) For all $A \in \mathcal{A}$, $\pi(A)$ has one, two or three terms, all distinct and in
  $V(A) \setminus W$. -/
  π_valid : ∀ A ∈ 𝒜, 1 ≤ πLen A ∧ πLen A ≤ 3 ∧ Function.Injective (πS A) ∧
    ∀ i : Fin (πLen A), ιV (πS A i) ∈ V(A) \ W
  /-- (J2) For all distinct $A, A' \in \mathcal{A}$,
  $V(A \cap A') = (\bar{\pi}(A) \cap \bar{\pi}(A')) \cup W$. -/
  vertex_inter_𝒜 : ∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ≠ A' →
    V(A) ∩ V(A') = ((ιV '' Set.range (πS A)) ∩ (ιV '' Set.range (πS A'))) ∪ W
  /-- (J3) $\Sigma$ is a sphere. -/
  isSphere : IsSphere S
  /-- (J3) $\Gamma \subseteq G \setminus W$. -/
  Γ_le : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph.deleteVerts W
  /-- (J3) $\Gamma$ is a 2-cell drawing in $\Sigma$. -/
  isTwoCell : Γ.IsTwoCell
  /-- (J3) $\theta \ge 4$ and $\operatorname{ord}(\mathcal{T}) \ge \theta$. -/
  four_le_θ : 4 ≤ θ
  /-- (J3) $\theta \le \operatorname{ord}(\mathcal{T})$. -/
  θ_le_ord : θ ≤ ord
  /-- (J3) $\mathcal{T}$ is a respectful tangle in $\Gamma$ of order `ord` with metric $d$. -/
  hasMetric : HasTangleMetric Γ ord T d
  /-- (J3) $\operatorname{ins}$ is defined by $\mathcal{T}$ on $\Gamma$-normal $O$-arcs of order
  $< \operatorname{ord}(\mathcal{T})$. -/
  ins_spec : ∀ F : Set S, IsOArc F → Γ.IsNormal F → (F ∩ Γ.V).ncard < ord →
    IsTangleIns Γ T F (ins F)
  /-- (J4) For each $A \in \mathcal{A}$, $D(A) \subseteq \Sigma$ is a closed disc with
  $\operatorname{bd}(D(A))$ $\Gamma$-normal and $D(A) = \operatorname{ins}(\operatorname{bd}(D(A)))$. -/
  disc_D : ∀ A ∈ 𝒜, IsClosedDisc (D A) ∧ Γ.IsNormal (subBd (D A)) ∧ D A = ins (subBd (D A))
  /-- (J4) For each $A \in \mathcal{A}$, $\Gamma \cap D(A) = \Gamma \cap A$. -/
  Γ_inter_D : ∀ A ∈ 𝒜,
    (Γ.interSet (D A)).toEmbeddedGraph ιV ιE = (Γ.toEmbeddedGraph ιV ιE) ⊓ A
  /-- (J4) For each $A \in \mathcal{A}$, $\bar{\pi}(A) = \operatorname{bd}(D(A)) \cap V(G)$. -/
  π_bar_eq_bd_inter : ∀ A ∈ 𝒜,
    Set.range (πS A) = subBd (D A) ∩ (ιV ⁻¹' V(R_G.G.toGraph))
  /-- (J4) If $|\bar{\pi}(A)| = 3$ then $\pi(A)$ enumerates $\bar{\pi}(A)$ in clockwise order
  around $D(A)$. -/
  π_clockwise : ∀ A ∈ 𝒜, EnumeratesClockwise orient (D A) (πS A)
  /-- (J4) For all distinct $A, A' \in \mathcal{A}$,
  $D(A) \cap D(A') = \bar{\pi}(A) \cap \bar{\pi}(A')$. -/
  D_inter_eq : ∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ≠ A' →
    D A ∩ D A' = Set.range (πS A) ∩ Set.range (πS A')
  /-- (J5) $N = \Gamma \cup N_W \cup \bigcup(A : A \in \mathcal{A})$. -/
  N_eq : N = graphUnion (graphUnion (Γ.toEmbeddedGraph ιV ιE) (Graph.noEdge W β))
    (subgraphSUnion R_G.G.toGraph 𝒜)
  /-- (J5) $(N, K)$ is a separation of $G$ and $W \subseteq V(N \cap K)$. -/
  sep_NK : IsGraphSeparation R_G.G.toGraph N K ∧ W ⊆ V(N) ∩ V(K)
  /-- (J5) $\Delta \subseteq \Sigma$ is a closed disc with
  $\operatorname{bd}(\Delta) \subseteq U(\Gamma)$. -/
  disc_Δ : IsClosedDisc Δ ∧ subBd Δ ⊆ Γ.U
  /-- (J5) $d(v, \Sigma \setminus \Delta) \ge \theta$ for all $v \in V(\Gamma \cap K)$. -/
  dist_Γ_inter_K : ∀ v ∈ Γ.V, ιV v ∈ V(K) → θ ≤ subsetTangleDist Γ ord d {v} (Set.univ \ Δ)
  /-- (J5) $d(D(A), \Sigma \setminus \Delta) \ge \theta$ for all $A \in \mathcal{A}$ with
  $A \cap K \ne N_W$. -/
  dist_D_of_inter_K : ∀ A ∈ 𝒜, A ⊓ K ≠ Graph.noEdge W β →
    θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)
  /-- (J5) $v^* \in V(\Gamma)$ with $v^* \notin \Delta$. -/
  v_star_mem : v_star ∈ Γ.V ∧ v_star ∉ Δ
  /-- (J6) $(H, \chi)$ has detail $\le \delta$. -/
  detail_H : R_H.HasDetailLE δ
  /-- (J6) $\phi$ is a model of $(H, \chi)$ in $(G, \omega)$. -/
  isModel : IsRootedDigraphModel R_G R_H φV φE
  /-- (J6) For each $v \in V(H)$, $\phi(v) \cap (K \cup \bigcup(A : A \in \mathcal{A}))$ is
  non-null. -/
  φV_meets : ∀ v ∈ V(R_H.G.toGraph),
    (V(φV v) ∩ (V(K) ∪ ⋃ A ∈ 𝒜, V(A))).Nonempty
  /-- (J6) For each $e \in E(H)$, $\phi(e) \in E(K \cup \bigcup(A : A \in \mathcal{A}))$. -/
  φE_mem : ∀ e ∈ E(R_H.G.toGraph),
    φE e ∈ E(K) ∪ ⋃ A ∈ 𝒜, E(A)

/-- Under `(J1)`–`(J6)`, a subset $\mathcal{A}' \subseteq \mathcal{A}$ is *adequate* for a model
$\phi'$ of $(H, \chi)$ in $(G, \omega)$ if conditions (i)–(iv) hold.
Graph Minors XXII, Section 7 (page 547):
"Let (J1)–(J6) hold, and let $\phi'$ be a model of $(H, \chi)$ in $(G, \omega)$. We say that
$\mathcal{A}' \subseteq \mathcal{A}$ is *adequate* for $\phi'$ if
(i) for each $v \in V(H)$ and $A \in \mathcal{A}$, if $A \cap \phi'(v) \not\subseteq \Gamma \cup N_W$
then $A \in \mathcal{A}'$,
(ii) for each $v \in V(H)$, $\phi'(v) \cap (K \cup \bigcup(A : A \in \mathcal{A}'))$ is non-null,
(iii) for each $e \in E(H)$, $\phi'(e) \in E(K \cup \bigcup(A : A \in \mathcal{A}'))$, and
(iv) for each $A \in \mathcal{A}$, if $A \cap K \ne N_W$ then $A \in \mathcal{A}'$." -/
structure IsAdequateFor {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {αH : Type u₁} {βH : Type v₁} {q : ℕ}
    (ιV : S ↪ α) (ιE : Set S ↪ β)
    (W : Set α) (𝒜 𝒜' : Set (Graph α β)) (Γ : Drawing S) (K : Graph α β)
    (R_H : RootedDigraph αH βH q) (φV' : αH → Graph α β) (φE' : βH → β) : Prop where
  /-- $\mathcal{A}' \subseteq \mathcal{A}$. -/
  subset : 𝒜' ⊆ 𝒜
  /-- (i) For each $v \in V(H)$ and $A \in \mathcal{A}$, if
  $A \cap \phi'(v) \not\subseteq \Gamma \cup N_W$ then $A \in \mathcal{A}'$. -/
  mem_of_not_le_Γ_union_NW : ∀ v ∈ V(R_H.G.toGraph), ∀ A ∈ 𝒜,
    ¬ (A ⊓ φV' v ≤ graphUnion (Γ.toEmbeddedGraph ιV ιE) (Graph.noEdge W β)) → A ∈ 𝒜'
  /-- (ii) For each $v \in V(H)$, $\phi'(v) \cap (K \cup \bigcup(A : A \in \mathcal{A}'))$ is
  non-null. -/
  φV_meets : ∀ v ∈ V(R_H.G.toGraph),
    (V(φV' v) ∩ (V(K) ∪ ⋃ A ∈ 𝒜', V(A))).Nonempty
  /-- (iii) For each $e \in E(H)$, $\phi'(e) \in E(K \cup \bigcup(A : A \in \mathcal{A}'))$. -/
  φE_mem : ∀ e ∈ E(R_H.G.toGraph),
    φE' e ∈ E(K) ∪ ⋃ A ∈ 𝒜', E(A)
  /-- (iv) For each $A \in \mathcal{A}$, if $A \cap K \ne N_W$ then $A \in \mathcal{A}'$. -/
  mem_of_inter_K_ne_NW : ∀ A ∈ 𝒜, A ⊓ K ≠ Graph.noEdge W β → A ∈ 𝒜'

/-- Under `(J1)`–`(J6)`, a subset $\mathcal{A}' \subseteq \mathcal{A}$ is *sufficient* for a model
$\phi'$ of $(H, \chi)$ in $(G, \omega)$ if for each $v \in V(H)$ and each $A \in \mathcal{A}$,
whenever some edge of $A \cap \phi'(v)$ is incident with a vertex in $W$ we have $A \in \mathcal{A}'$,
and the remaining three adequacy conditions hold.
Graph Minors XXII, Section 7 (page 552):
"If (J1)–(J6) hold and $\mathcal{A}' \subseteq \mathcal{A}$, and $\phi'$ is a model of $(H, \chi)$
in $(G, \omega)$, we say that $\mathcal{A}'$ is *sufficient* for $\phi'$ if
- for each $v \in V(H)$ and each $A \in \mathcal{A}$, if some edge of $A \cap \phi'(v)$ is incident
  with a vertex in $W$ then $A \in \mathcal{A}'$,
- for each $v \in V(H)$, $\phi'(v) \cap (K \cup \bigcup(A \colon A \in \mathcal{A}'))$ is non-null,
- for each $e \in E(H)$, $\phi'(e) \subseteq E(K \cup \bigcup(A \colon A \in \mathcal{A}'))$, and
- for each $A \in \mathcal{A}$, if $A \cap K \ne N_W$ then $A \in \mathcal{A}'$." -/
structure IsSufficientFor {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁} {q : ℕ}
    (W : Set α) (𝒜 𝒜' : Set (Graph α β)) (K : Graph α β)
    (R_H : RootedDigraph αH βH q) (φV' : αH → Graph α β) (φE' : βH → β) : Prop where
  /-- $\mathcal{A}' \subseteq \mathcal{A}$. -/
  subset : 𝒜' ⊆ 𝒜
  /-- For each $v \in V(H)$ and each $A \in \mathcal{A}$, if some edge of $A \cap \phi'(v)$ is
  incident with a vertex in $W$ then $A \in \mathcal{A}'$. -/
  mem_of_edge_inc_W : ∀ v ∈ V(R_H.G.toGraph), ∀ A ∈ 𝒜,
    (∃ e ∈ E(A ⊓ φV' v), ∃ w ∈ W, (A ⊓ φV' v).Inc e w) → A ∈ 𝒜'
  /-- For each $v \in V(H)$, $\phi'(v) \cap (K \cup \bigcup(A : A \in \mathcal{A}'))$ is
  non-null. -/
  φV_meets : ∀ v ∈ V(R_H.G.toGraph),
    (V(φV' v) ∩ (V(K) ∪ ⋃ A ∈ 𝒜', V(A))).Nonempty
  /-- For each $e \in E(H)$, $\phi'(e) \in E(K \cup \bigcup(A : A \in \mathcal{A}'))$. -/
  φE_mem : ∀ e ∈ E(R_H.G.toGraph),
    φE' e ∈ E(K) ∪ ⋃ A ∈ 𝒜', E(A)
  /-- For each $A \in \mathcal{A}$, if $A \cap K \ne N_W$ then $A \in \mathcal{A}'$. -/
  mem_of_inter_K_ne_NW : ∀ A ∈ 𝒜, A ⊓ K ≠ Graph.noEdge W β → A ∈ 𝒜'

/-- A member $A \in \mathcal{A}$ is *good* if $\bar{\pi}(A) \subseteq V(\Gamma)$ and for all
$u, v \in \bar{\pi}(A)$ there is a path of $\Gamma \cap A$ with ends $u, v$ and with no internal
vertex in $\bar{\pi}(A)$.
Graph Minors XXII, Section 7, proof of 7.4 (page 553):
"Let us say $A \in \mathcal{A}$ is *good* if $\bar{\pi}(A) \subseteq V(\Gamma)$ and for all
$u, v \in \bar{\pi}(A)$ there is a path of $\Gamma \cap A$ with ends $u, v$ and with no internal
vertex in $\bar{\pi}(A)$. We say $A \in \mathcal{A}$ is *bad* if it is not good." -/
def IsGoodMember {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    (ιV : S ↪ α) (ιE : Set S ↪ β) (Γ : Drawing S)
    (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
    (A : Graph α β) : Prop :=
  Set.range (πS A) ⊆ Γ.V ∧
    ∀ u ∈ ιV '' Set.range (πS A), ∀ v ∈ ιV '' Set.range (πS A),
      ∃ P : Graph α β, IsGraphPathWithEnds ((Γ.toEmbeddedGraph ιV ιE) ⊓ A) P u v ∧
        Disjoint (pathInternalVerts ((Γ.toEmbeddedGraph ιV ιE) ⊓ A) P)
          (ιV '' Set.range (πS A))

/-- A member $A \in \mathcal{A}$ is *bad* if it is not good.
Graph Minors XXII, Section 7, proof of 7.4 (page 553):
"Let us say $A \in \mathcal{A}$ is *good* if $\bar{\pi}(A) \subseteq V(\Gamma)$ and for all
$u, v \in \bar{\pi}(A)$ there is a path of $\Gamma \cap A$ with ends $u, v$ and with no internal
vertex in $\bar{\pi}(A)$. We say $A \in \mathcal{A}$ is *bad* if it is not good." -/
def IsBadMember {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    (ιV : S ↪ α) (ιE : Set S ↪ β) (Γ : Drawing S)
    (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
    (A : Graph α β) : Prop :=
  ¬ IsGoodMember ιV ιE Γ πLen πS A

/-- Condition `(J7)` of Graph Minors XXII, Section 7 (page 552):
"(J7) For each $A \in \mathcal{A}$, if $u, v \in \bar{\pi}(A)$ there is a path of $A$ with ends
$u, v$ and with no internal vertex in $\bar{\pi}(A) \cup W$; for each $A \in \mathcal{A}$, there is
no separation $(C, D)$ of $G \setminus W$ with order $< |\bar{\pi}(A)|$ such that
$A \setminus W \subseteq C$ and $(C \cap \Gamma, D \cap \Gamma) \in \mathcal{T}$; and for each
$A \in \mathcal{A}$, either
- $V(\Gamma \cap A) \subseteq \bar{\pi}(A)$ and $E(\Gamma \cap A) = \emptyset$, or
- $\Gamma \cap A$ is a path with both ends in $\bar{\pi}(A)$, or
- $|\bar{\pi}(A)| = 3$, $\bar{\pi}(A) \subseteq V(\Gamma)$, some $v \in \bar{\pi}(A)$ has degree 0
  in $\Gamma \cap A$, and $(\Gamma \cap A) \setminus \{v\}$ is a path with both ends in
  $\bar{\pi}(A)$, or
- $|\bar{\pi}(A)| = 3$, $\bar{\pi}(A) \subseteq V(\Gamma)$, and for all $u, v \in \bar{\pi}(A)$
  there is a path of $\Gamma \cap A$ with ends $u, v$ and with no internal vertex in
  $\bar{\pi}(A)$." -/
structure ConditionJ7 {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    (ιV : S ↪ α) (ιE : Set S ↪ β)
    (G : Graph α β) (W : Set α) (𝒜 : Set (Graph α β))
    (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
    (Γ : Drawing S) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) : Prop where
  /-- For each $A \in \mathcal{A}$ and $u, v \in \bar{\pi}(A)$, there is a path of $A$ with ends
  $u, v$ and with no internal vertex in $\bar{\pi}(A) \cup W$. -/
  path_in_A : ∀ A ∈ 𝒜, ∀ u ∈ ιV '' Set.range (πS A), ∀ v ∈ ιV '' Set.range (πS A),
    ∃ P : Graph α β, IsGraphPathWithEnds (A.deleteVerts W) P u v ∧
      Disjoint (pathInternalVerts (A.deleteVerts W) P) (ιV '' Set.range (πS A))
  /-- For each $A \in \mathcal{A}$, there is no separation $(C, D)$ of $G \setminus W$ with order
  $< |\bar{\pi}(A)|$ such that $A \setminus W \subseteq C$ and
  $(C \cap \Gamma, D \cap \Gamma) \in \mathcal{T}$. -/
  no_small_sep : ∀ A ∈ 𝒜, ¬ ∃ (C D : Graph α β) (C_Γ D_Γ : Hypergraph S (Set S)),
    IsGraphSeparation (G.deleteVerts W) C D ∧
    (V(C) ∩ V(D)).ncard < πLen A ∧
    A.deleteVerts W ≤ C ∧
    C_Γ.vertexSet = ιV ⁻¹' V(C) ∩ Γ.V ∧ C_Γ.edgeSet = ιE ⁻¹' E(C) ∩ Γ.E ∧
    D_Γ.vertexSet = ιV ⁻¹' V(D) ∩ Γ.V ∧ D_Γ.edgeSet = ιE ⁻¹' E(D) ∩ Γ.E ∧
    (C_Γ, D_Γ) ∈ T
  /-- For each $A \in \mathcal{A}$, one of the four structural alternatives for $\Gamma \cap A$
  holds. -/
  structure_Γ_inter_A : ∀ A ∈ 𝒜,
    let GA := (Γ.toEmbeddedGraph ιV ιE) ⊓ A
    let πBar := ιV '' Set.range (πS A)
    (V(GA) ⊆ πBar ∧ E(GA) = ∅) ∨
    (∃ u ∈ πBar, ∃ v ∈ πBar, IsGraphPathWithEnds GA GA u v) ∨
    (πLen A = 3 ∧ Set.range (πS A) ⊆ Γ.V ∧
      ∃ v ∈ πBar, vertexValency GA v = 0 ∧
        ∃ u₁ ∈ πBar \ {v}, ∃ u₂ ∈ πBar \ {v},
          IsGraphPathWithEnds (GA.deleteVerts {v}) (GA.deleteVerts {v}) u₁ u₂) ∨
    (πLen A = 3 ∧ IsGoodMember ιV ιE Γ πLen πS A)

/-! ## Section 8: Homogeneity (pages 556–563) -/

/-- The bipartite incidence graph $G'$ with vertex set $Z \cup \mathcal{A}$ in which $z \in Z$ and
$A \in \mathcal{A}$ are adjacent if $z \in V(A)$ (Theorem 8.3(x), page 559). -/
def divisionIncidenceGraph {α : Type u} {β : Type v} (Z : Set α) (𝒜 : Set (Graph α β)) :
    Graph (α ⊕ Graph α β) (α × Graph α β) where
  vertexSet := (Sum.inl '' Z) ∪ (Sum.inr '' 𝒜)
  edgeSet := {p : α × Graph α β | p.1 ∈ Z ∧ p.2 ∈ 𝒜 ∧ p.1 ∈ V(p.2)}
  IsLink p x y := p.1 ∈ Z ∧ p.2 ∈ 𝒜 ∧ p.1 ∈ V(p.2) ∧
    ((x = Sum.inl p.1 ∧ y = Sum.inr p.2) ∨ (x = Sum.inr p.2 ∧ y = Sum.inl p.1))
  isLink_symm _ _ := ⟨fun _ _ ⟨h₁, h₂, h₃, h₄⟩ =>
    ⟨h₁, h₂, h₃, h₄.elim (fun ⟨hx, hy⟩ => Or.inr ⟨hy, hx⟩) (fun ⟨hx, hy⟩ => Or.inl ⟨hy, hx⟩)⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro p x y v w ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink p := by
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      exact ⟨Sum.inl p.1, Sum.inr p.2, h₁, h₂, h₃, Or.inl ⟨rfl, rfl⟩⟩
    · rintro ⟨_, _, h₁, h₂, h₃, _⟩
      exact ⟨h₁, h₂, h₃⟩
  left_mem_of_isLink := by
    rintro p x y ⟨h₁, h₂, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨p.1, h₁, rfl⟩
    · exact Or.inr ⟨p.2, h₂, rfl⟩

/-- Condition (x) of Theorem 8.3 (Graph Minors XXII, Section 8, page 559):
Let $G'$ be the bipartite graph with vertex set $Z \cup \mathcal{A}$, in which $z \in Z$ and
$A \in \mathcal{A}$ are adjacent if $z \in V(A)$; then $G'$ is planar, and can be drawn in a closed
disc with the vertices of $\Pi$ in the boundary of the disc, in the same order in which they occur
in $U(C_0)$. -/
def HasDiscDrawingWithBoundaryOrder {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    (ιV : S ↪ α) (C₀ : Drawing S) (PiSet : Set S) (Z : Set α) (𝒜 : Set (Graph α β)) : Prop :=
  ∃ (D_disc : Set EuclideanPlane) (gd : GraphDrawing (divisionIncidenceGraph Z 𝒜) EuclideanPlane)
    (φ_C : Circle ≃ₜ C₀.U) (φ_D : Circle ≃ₜ subBd D_disc),
    IsClosedDisc D_disc ∧ gd.drawing.U ⊆ D_disc ∧
    (∀ p : S, p ∈ PiSet →
      ∃ hp : Sum.inl (ιV p) ∈ V(divisionIncidenceGraph Z 𝒜),
        (gd.iso.vertexEquiv ⟨Sum.inl (ιV p), hp⟩).1 ∈ subBd D_disc) ∧
    (∀ v : V(divisionIncidenceGraph Z 𝒜),
      (gd.iso.vertexEquiv v).1 ∈ subBd D_disc ↔ ∃ p ∈ PiSet, v.1 = Sum.inl (ιV p)) ∧
    ∀ (t₁ t₂ t₃ t₄ : ℝ) (p₁ p₂ p₃ p₄ : S),
      0 ≤ t₁ → t₁ < t₂ → t₂ < t₃ → t₃ < t₄ → t₄ < 2 * Real.pi →
      PiSet = {p₁, p₂, p₃, p₄} →
      (φ_C (Circle.exp t₁)).1 = p₁ → (φ_C (Circle.exp t₂)).1 = p₂ →
      (φ_C (Circle.exp t₃)).1 = p₃ → (φ_C (Circle.exp t₄)).1 = p₄ →
      ∃ (s₁ s₂ s₃ s₄ : ℝ) (hp₁ : Sum.inl (ιV p₁) ∈ V(divisionIncidenceGraph Z 𝒜))
        (hp₂ : Sum.inl (ιV p₂) ∈ V(divisionIncidenceGraph Z 𝒜))
        (hp₃ : Sum.inl (ιV p₃) ∈ V(divisionIncidenceGraph Z 𝒜))
        (hp₄ : Sum.inl (ιV p₄) ∈ V(divisionIncidenceGraph Z 𝒜)),
        0 ≤ s₁ ∧ s₁ < s₂ ∧ s₂ < s₃ ∧ s₃ < s₄ ∧ s₄ < 2 * Real.pi ∧
        (φ_D (Circle.exp s₁)).1 = (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₁), hp₁⟩).1 ∧
        (φ_D (Circle.exp s₂)).1 = (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₂), hp₂⟩).1 ∧
        (φ_D (Circle.exp s₃)).1 = (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₃), hp₃⟩).1 ∧
        (φ_D (Circle.exp s₄)).1 = (gd.iso.vertexEquiv ⟨Sum.inl (ιV p₄), hp₄⟩).1

/-- The hypotheses (i)–(xiv) of Theorem 8.3 of Graph Minors XXII, Section 8 (pages 559–560):
"(iv) $\mathcal{T}$ is a tangle in $\Gamma$ of order $\ge \theta$, and there is no
$(A, B) \in \mathcal{T}$ with order $\le 3$ such that $\Pi \subseteq V(A)$; $d$ is the metric of
$\mathcal{T}$."
"(ix) For each $A \in \mathcal{A}$, if $u, v \in \bar{\pi}(A)$ there is a path of $A \setminus W$
between $u$ and $v$ with no internal vertex in $\bar{\pi}(A)$."
"(xiii) If $A \in \mathcal{A}$ and $v(A) \in \Sigma \setminus D$ then for every
$v \in V(\Gamma) \setminus D$, either $d(v, D) \le h$ or there exists $A' \in \mathcal{A}$ such
that $d(v, v(A')) \le h$ and $(A', \pi(A') + \omega)$ has the same $\delta$-folio as
$(A, \pi(A) + \omega)$." -/
structure Hypotheses83 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (q δ h θ : ℕ)
    (ιV : S ↪ α) (ιE : Set S ↪ β)
    (R_G : RootedDigraph α β q) (W : Set α)
    (Γ C₀ : Drawing S) (r₀ : Set S) (orient : GM19.SurfaceOrientation S)
    (PiSet : Set S)
    (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (J : Graph α β) (Z : Set α) (𝒜 : Set (Graph α β))
    (πLen : Graph α β → ℕ) (πA : ∀ A : Graph α β, Fin (πLen A) → α)
    (vA : Graph α β → S) (D_disc : Set S) (v_star : S) : Prop where
  /-- $V(G)$ is finite. -/
  finite_V : V(R_G.G.toGraph).Finite
  /-- $E(G)$ is finite. -/
  finite_E : E(R_G.G.toGraph).Finite
  /-- $W \subseteq V(G)$ and $\omega$ is an ordering of $W$. -/
  ordering_W : W ⊆ V(R_G.G.toGraph) ∧ IsOrderingOf W R_G.roots
  /-- $\Gamma \subseteq G \setminus W$. -/
  Γ_le : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph.deleteVerts W
  /-- (i) $\Sigma$ is a sphere and $\Gamma$ is a subdivision of a simple 3-connected graph. -/
  hyp_i : IsSphere S ∧ IsSubdivisionOfSimpleThreeConnected Γ.toGraph
  /-- (ii) $C_0$ is a circuit of $\Gamma$, and $U(C_0)$ bounds a region $r_0$ of $\Gamma$. -/
  hyp_ii : C₀.IsSubdrawing Γ ∧ C₀.IsCircuit ∧ r₀ ∈ Γ.R ∧ subBd r₀ = C₀.U
  /-- (iii) $\Pi \subseteq V(C_0)$ with $|\Pi| = 4$. -/
  hyp_iii : PiSet ⊆ C₀.V ∧ PiSet.ncard = 4
  /-- (iv) $\mathcal{T}$ is a respectful tangle in $\Gamma$ of order `ord ≥ θ` with metric $d$, and
  there is no $(A, B) \in \mathcal{T}$ with order $\le 3$ such that $\Pi \subseteq V(A)$. -/
  hyp_iv : θ ≤ ord ∧ HasTangleMetric Γ ord T d ∧
    ∀ A B : Hypergraph S (Set S), (A, B) ∈ T → separationOrder A B ≤ 3 → ¬ (PiSet ⊆ A.vertexSet)
  /-- (v) $J \subseteq G$ has vertex set the union of $W$, $V(\Gamma)$, and the vertex sets of all
  components of $G \setminus (V(C_0) \cup W)$ which meet $V(\Gamma)$, and edge set all edges of $G$
  with both ends in $V(J)$. -/
  hyp_v : J ≤ R_G.G.toGraph ∧
    J = R_G.G.toGraph.induce
      (W ∪ (ιV '' Γ.V) ∪
        ⋃ C ∈ {C ∈ graphComponents (R_G.G.toGraph.deleteVerts ((ιV '' C₀.V) ∪ W)) |
          (V(C) ∩ (ιV '' Γ.V)).Nonempty}, V(C))
  /-- (vi) $Z \subseteq V(J) \setminus W$ with $\Pi \subseteq Z$, and $\mathcal{A}$ is a
  $(Z \cup W)$-division of $J$, such that $W \subseteq V(A)$ for all $A \in \mathcal{A}$. -/
  hyp_vi : Z ⊆ V(J) \ W ∧ ιV '' PiSet ⊆ Z ∧ IsZDivision J (Z ∪ W) 𝒜 ∧ ∀ A ∈ 𝒜, W ⊆ V(A)
  /-- (vii) For each $A \in \mathcal{A}$, $Z \cap V(A) = \bar{\pi}(A)$, $|\bar{\pi}(A)| \le 3$, and
  $\pi(A)$ is a linear order of $\bar{\pi}(A)$. -/
  hyp_vii : ∀ A ∈ 𝒜, πLen A ≤ 3 ∧ IsOrderingOf (Z ∩ V(A)) (πA A)
  /-- (viii) For each $A \in \mathcal{A}$, there are $|\bar{\pi}(A)|$ mutually vertex-disjoint
  paths of $J \setminus W$ between $\bar{\pi}(A)$ and $\Pi$, preserving clockwise order when
  $|\bar{\pi}(A)| = 3$. -/
  hyp_viii : ∀ A ∈ 𝒜,
    ∃ (P : Fin (πLen A) → Graph α β) (t : Fin (πLen A) → S),
      (∀ i : Fin (πLen A), t i ∈ PiSet ∧
        IsGraphPathWithEnds (J.deleteVerts W) (P i) (πA A i) (ιV (t i))) ∧
      Pairwise (fun i j : Fin (πLen A) => Disjoint V(P i) V(P j)) ∧
      (∀ h3 : πLen A = 3,
        orient.pos (Set.univ \ r₀) (t ⟨0, by omega⟩) (t ⟨1, by omega⟩) (t ⟨2, by omega⟩))
  /-- (ix) For each $A \in \mathcal{A}$, if $u, v \in \bar{\pi}(A)$ there is a path of
  $A \setminus W$ between $u$ and $v$ with no internal vertex in $\bar{\pi}(A)$. -/
  hyp_ix : ∀ A ∈ 𝒜, ∀ u ∈ Z ∩ V(A), ∀ v ∈ Z ∩ V(A),
    ∃ P : Graph α β, IsGraphPathWithEnds (A.deleteVerts W) P u v ∧
      Disjoint (pathInternalVerts (A.deleteVerts W) P) (Z ∩ V(A))
  /-- (x) The bipartite incidence graph $G'$ on $Z \cup \mathcal{A}$ can be drawn in a closed disc
  with $\Pi$ in the boundary in the order of $U(C_0)$. -/
  hyp_x : HasDiscDrawingWithBoundaryOrder ιV C₀ PiSet Z 𝒜
  /-- (xi) For each $A \in \mathcal{A}$, $v(A) \in V(\Gamma)$ and there is a path of $G \setminus W$
  between $v(A)$ and a vertex of $\bar{\pi}(A)$ with no vertex in $V(\Gamma)$ except $v(A)$. -/
  hyp_xi : ∀ A ∈ 𝒜, vA A ∈ Γ.V ∧
    ∃ u ∈ Z ∩ V(A), ∃ P : Graph α β,
      IsGraphPathWithEnds (R_G.G.toGraph.deleteVerts W) P (ιV (vA A)) u ∧
      V(P) ∩ (ιV '' Γ.V) = {ιV (vA A)}
  /-- (xii) $D \subseteq \Sigma$ is a closed disc with $\operatorname{bd}(D) \subseteq U(\Gamma)$
  including the region $r_0$ of $\Gamma$ bounded by $U(C_0)$. -/
  hyp_xii : IsClosedDisc D_disc ∧ subBd D_disc ⊆ Γ.U ∧ r₀ ⊆ D_disc
  /-- (xiii) Homogeneity condition outside $D$. -/
  hyp_xiii : ∀ (A : Graph α β) (hA : A ∈ 𝒜), vA A ∈ Set.univ \ D_disc → ∀ v ∈ Γ.V \ D_disc,
    subsetTangleDist Γ ord d {v} D_disc ≤ h ∨
      ∃ (A' : Graph α β) (hA' : A' ∈ 𝒜), subsetTangleDist Γ ord d {v} {vA A'} ≤ h ∧
        ∃ hlen : πLen A' = πLen A,
          HasSameDeltaFolio
            (subRootedDigraph R_G.G A' ((hyp_vi.2.2.1.2.1 A' hA').trans hyp_v.1)
              (seqConcat (πA A' ∘ Fin.cast hlen.symm) R_G.roots)
              (seqConcat_mem
                (fun j => ((hyp_vii A' hA').2.2.subset ⟨Fin.cast hlen.symm j, rfl⟩).2)
                (fun j => hyp_vi.2.2.2 A' hA' (ordering_W.2.2.subset ⟨j, rfl⟩))))
            (subRootedDigraph R_G.G A ((hyp_vi.2.2.1.2.1 A hA).trans hyp_v.1)
              (seqConcat (πA A) R_G.roots)
              (seqConcat_mem
                (fun j => ((hyp_vii A hA).2.2.subset ⟨j, rfl⟩).2)
                (fun j => hyp_vi.2.2.2 A hA (ordering_W.2.2.subset ⟨j, rfl⟩))))
            δ
  /-- (xiv) $v^* \in V(\Gamma) \setminus D$ and $d(v^*, D) \ge \theta$. -/
  hyp_xiv : v_star ∈ Γ.V \ D_disc ∧ θ ≤ subsetTangleDist Γ ord d {v_star} D_disc

end GraphMinor.GM22
