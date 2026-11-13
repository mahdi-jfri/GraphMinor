module

public import GraphMinor.GM01.BinaryTrees
public import GraphMinor.GM01.BlockBypass
public import GraphMinor.GM01.CombBypassFork
public import GraphMinor.GM01.CombEndAttachmentPaths
public import GraphMinor.GM01.CombFirstBoundaryPaths
public import GraphMinor.GM01.CombFirstBoundaryRootPaths
public import GraphMinor.GM01.CombLateBoundaryVertices
public import GraphMinor.GM01.CombPrefixModels
public import GraphMinor.GM01.Defs
public import GraphMinor.GM01.ForestGraphs
public import GraphMinor.GM01.ForestTrees
public import GraphMinor.GM01.FullDisconnectedSeparators
public import GraphMinor.GM01.FullPathFamilies
public import GraphMinor.GM01.FullPaths
public import GraphMinor.GM01.FullStars
public import GraphMinor.GM01.GraphComponents
public import GraphMinor.GM01.GraphSeparators
public import GraphMinor.GM01.LayerAttachmentPaths
public import GraphMinor.GM01.LayerBlockSets
public import GraphMinor.GM01.ManyGraphSeparators
public import GraphMinor.GM01.OrderedBlockWindows
public import GraphMinor.GM01.OrderedSeparatorLocalization
public import GraphMinor.GM01.PathBagBoundaries
public import GraphMinor.GM01.PathWidth
public import GraphMinor.GM01.PathWidthComponents
public import GraphMinor.GM01.QuantitativeBounds
public import GraphMinor.GM01.QuantitativeParity
public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM01.RootedForks
public import GraphMinor.GM01.RootedWidth
public import GraphMinor.GM01.Section4CombAttachment
public import GraphMinor.GM01.Section4DisjointPaths
public import GraphMinor.GM01.Section4FirstEnd
public import GraphMinor.GM01.Section4LayerDisjointness
public import GraphMinor.GM01.Section4Localization
public import GraphMinor.GM01.Section4NotLastLayer
public import GraphMinor.GM01.Section4RootSeparation
public import GraphMinor.GM01.Section4SecondBoundaryPath
public import GraphMinor.GM01.Section4SecondEnd
public import GraphMinor.GM01.Section4Separators
public import GraphMinor.GM01.SeparatorLayerDecomposition
public import GraphMinor.GM01.SeparatorLayerEdges
public import GraphMinor.GM01.Statements
public import GraphMinor.GM01.SubdivisionInteriorFork
public import GraphMinor.GM09.Defs
public import GraphMinor.Minor.Model
public import GraphMinor.Statement
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Set.Card
import GraphMinor.GM01.BoundedWidthCharacterization
import GraphMinor.GM01.ForestBinaryMinor
import GraphMinor.GM01.ForestFirstSequence
import GraphMinor.GM01.ForestGridExclusion
import GraphMinor.GM01.ForestTreeWidth
import GraphMinor.GM01.FullConnectedSubgraphs
import GraphMinor.GM01.FullGridPaths
import GraphMinor.GM01.FullMengerSeparators
import GraphMinor.GM01.FullSeparators
import GraphMinor.GM01.FullUniquePaths
import GraphMinor.GM01.GridBinaryMinor
import GraphMinor.GM01.GridForestMinor
import GraphMinor.GM01.MainReduction
import GraphMinor.GM01.MeshBoundGraphs
import GraphMinor.GM01.PathWidthGluing
import GraphMinor.GM01.Section3Bounds
import GraphMinor.GM01.Section4Conclusion
import GraphMinor.GM01.Section4FirstBoundaryPath
import GraphMinor.GM01.Section4SampledOrder
import GraphMinor.GM01.Section4SmallSeparators
import GraphMinor.GM01.Section5Claims

/-!
# Graph Minors I. Excluding a forest

N. Robertson and P. D. Seymour, J. Combin. Theory Ser. B 35 (1983) 39–61.

This file lists every numbered result of the paper in order. The proofs are in the other
files of this folder and, for algorithms, in `GraphMinor/Compute/`. Where a printed statement
or proof has an error, the docstring says so and refers to `corrections/GM01.md`.
-/

public section

namespace GraphMinor.GM01

/-! ## Section 1. Introduction -/

section

open Graph

universe u v u' v'

/-- Graph Minors I, (1.1), page 39, from the paper's later result (3.1):
"For every forest $H$ there is an integer $w$ such that every graph with no minor isomorphic to $H$ has path-width $\le w$."

The proof on page 51 reduces forest exclusion to exclusion of an odd-depth
branching tree. The elementary forest-minor observation in that proof is
proved here rather than assumed. Apply the proved numbered bound (3.1). -/
theorem theorem_1_1 {α : Type u'} {β : Type v'} (H : Graph α β) (hfin : V(H).Finite)
    (hforest : IsForest H) :
    ∃ w : ℕ, ∀ {γ : Type u} {δ : Type v} (G : Graph γ δ),
      V(G).Finite → E(G).Finite → ¬ IsIsoMinor H G → HasPathWidthLE G w := by exact GraphMinor.GM01.theorem_1_1_proof H hfin hforest

end

section

open Set Graph

universe u v

/-- Graph Minors I, (1.2), page 40: "Let $\mathcal{F}$ be a set of
graphs. Then the following are equivalent:"
"for some integer $w$, every $G \in \mathcal{F}$ has path-width $\le w$;"
"there is a forest $H$ such that no $G \in \mathcal{F}$ has a minor
isomorphic to $H$."
All graphs are finite by the paper's convention. The excluded forest
may have its own vertex and edge types, distinct from those of the family. -/
theorem theorem_1_2 {α : Type u} {β : Type v} (F : Set (Graph α β))
    (hFinite : ∀ G ∈ F, V(G).Finite ∧ E(G).Finite) :
    (∃ w : ℕ, ∀ G ∈ F, HasPathWidthLE G w) ↔
    ∃ (ν ε : Type) (H : Graph ν ε), V(H).Finite ∧ E(H).Finite ∧ IsForest H ∧
      ∀ G ∈ F, ¬ IsIsoMinor H G := by exact GraphMinor.GM01.theorem_1_2_proof F hFinite

end

section

open Graph

/-- Graph Minors I, (1.3), page 40: "Let $G_1, G_2, ..., $ be a
countable sequence of graphs, such that $G_1$ is a forest. Then there
exist $j > i \ge 1$ such that $G_i$ is isomorphic to a minor of $G_j$."
The proof is the paper's: (1.1) bounds the path-width of the later graphs that
exclude the forest, and Graph Minors IV, (1.5) applies to them. The sequence is
indexed from zero, so its first graph is `G 0`. -/
theorem theorem_1_3 {α β : Type*} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite)
    (hForest : IsForest (G 0)) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by exact GraphMinor.GM01.theorem_1_3_proof G hV hE hForest

end

section

open Graph

/-- **Graph Minors I, (1.4)** (page 40):
"If every connected component of $G$ has path-width $\le k$, then $G$ has path-width $\le k$."

Graph Minors I, (1.4), page 40: if every connected component has
path-width at most `k`, concatenate their decompositions to obtain that bound
for the whole graph. -/
theorem theorem_1_4 {α β : Type*}
    {G : Graph α β} (hfin : V(G).Finite) {k : ℕ}
    (h : ∀ v : V(G), HasPathWidthLE (G.induce (componentVertices G v)) k) :
    HasPathWidthLE G k := by exact GraphMinor.GM01.theorem_1_4_proof hfin h

end

section

open Graph

/-- **Graph Minors I, (1.5)** (page 40):
"If $X \subseteq V(G)$ and $G \setminus X$ has path-width $\le k$, then $G$ has path-width $\le k + |X|$."

Graph Minors I, (1.5), page 40.

> If $X \subseteq V(G)$ and $G \setminus X$ has path-width $\le k$, then $G$ has path-width $\le k + |X|$.

First cover the remaining isolated vertices by singleton bags. Then add `X`
to every bag and append a bag `X` to allow an empty remaining graph. -/
theorem theorem_1_5 {α β : Type*}
    {G : Graph α β} (hfin : V(G).Finite)
    {X : Set α} (hX : X ⊆ V(G)) {k : ℕ}
    (h : HasPathWidthLE (G.deleteVerts X) k) :
    HasPathWidthLE G (k + X.ncard) := by exact GraphMinor.GM01.theorem_1_5_proof hfin hX h

end

section

open Set Graph

/-- **Graph Minors I, (1.6)** (page 40):
"If $X_1, ..., X_r \subseteq V(G)$ is a path-decomposition of $G$, and for $1 \le i \le r - 1$, $|X_i \cap X_{i+1}| \le k$, and for $1 \le i \le r$,"

Graph Minors I, (1.6), page 40. If consecutive bag intersections
have size at most `k`, and deleting all other bags leaves width at
most `k'` for each chosen bag, the whole graph has width at most
`k' + 2k`. The proof refines each bag and concatenates the refinements. -/
theorem theorem_1_6 {α β : Type*} {G : Graph α β} (hfin : V(G).Finite)
    (D : PathDecomposition G) {k k' : ℕ}
    (hOverlap : ∀ i j : Fin D.length, j.val = i.val + 1 → (D.bag i ∩ D.bag j).ncard ≤ k)
    (hLocal : ∀ i : Fin D.length, HasPathWidthLE (G.deleteVerts (D.otherBags i)) k') :
    HasPathWidthLE G (k' + 2 * k) := by exact GraphMinor.GM01.theorem_1_6_proof hfin D hOverlap hLocal

end

section

open Set Graph

/-- Graph Minors I, (1.7), pages 41–42.
"Let $\rho$ be a vertex of a graph $G$, and let $Y_1, Y_2, ..., Y_T$ be disjoint subsets of $V(G)$, where $T \ge 1$. Suppose that for $1 < i, i' \le T$, and for all $y \in Y_{i'}$, $Y_i$ separates $y$ and $\rho$ if and only if $i \le i'$. For $1 \le i < T$, let $W_i$ be the set of all vertices of $G$ separated from $\rho$ by $Y_i$, and not separated from $\rho$ by $Y_{i+1}$. Let $W_0$ be the set of vertices not separated from $\rho$ by $Y_1$, and let $W_T$ be the set of all vertices separated from $\rho$ by $Y_T$. Then the sets $W_0, W_1, ..., W_T$ are disjoint and partition $V(G)$, and $Y_i \subseteq W_i$ ($1 \le i \le T$), and the sequence"

The print has "$1 < i, i' \le T$", a misprint for $1 \le i, i' \le T$: as printed, nothing is
assumed about $Y_1$ and the result is false. The Lean assumes the condition for all
$1 \le i, i' \le T$. See the correction to (1.7) in `corrections/GM01.md`. The proof prints "$\rho$
has both ends" for "$e$ has both ends" (see the correction to the proof of (1.7) in
`corrections/GM01.md`).

The final existential specifies both the length and the exact bag
sequence. Heterogeneous equality allows the sequence indices to be
identified by the stated equality of lengths. -/
theorem theorem_1_7 {α β : Type*} {T : ℕ} {G : Graph α β} {root : α}
    (_hroot : root ∈ V(G)) (_hT : 1 ≤ T)
    (Y : Fin T → Set α) (hYG : ∀ i, Y i ⊆ V(G))
    (_hdis : Pairwise (fun i j ↦ Disjoint (Y i) (Y j)))
    (horder : ∀ i j, ∀ y ∈ Y j,
      GraphSeparates G (Y i) {y} {root} ↔ i ≤ j) :
    Pairwise (fun i j ↦ Disjoint (separatorLayer G root Y i) (separatorLayer G root Y j)) ∧
      (⋃ k, separatorLayer G root Y k) = V(G) ∧
      (∀ i : Fin T, Y i ⊆ separatorLayer G root Y ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) ∧
      ∃ D : PathDecomposition G, D.length = T + 1 ∧
        HEq D.bag (separatorLayerBag G root Y) := by exact GraphMinor.GM01.theorem_1_7_proof _hroot _hT Y hYG _hdis horder

end

/-! ## Section 2. Grids -/

section

open Graph Set SimpleGraph GM05

universe u v

/-- Graph Minors I, (2.1), page 42, for graphs with loops and multiple edges:
"If $P_1, ..., P_m$ are disjoint paths of a graph $G \in \mathcal{F}_\theta$, and $B_1, ..., B_n$
are also disjoint paths, and each $P_i$ has exactly one vertex in common with each $B_j$, and each
$P_i$ meets $B_1, ..., B_n$ in that order, then either $m < \theta$ or
$n < \frac{1}{2}\theta \cdot \theta!$."
The simple special case is `GM01.theorem_2_1_simple`.

The statement retains loops and parallel edges, using the simple shadow in the proof. -/
theorem theorem_2_1 {α : Type u} {β : Type v}
    {θ m n : ℕ} (hθ : 2 ≤ θ) {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) (hG : ¬ IsIsoMinor (gridGraph θ) G)
    (P : Fin m → Full.Path α β) (B : Fin n → Full.Path α β)
    (hP : ∀ i, (P i).IsIn G)
    (hPD : Pairwise fun i j ↦ Disjoint (P i).verts (P j).verts)
    (hB : ∀ j, (B j).IsIn G)
    (hBD : Pairwise fun i j ↦ Disjoint (B i).verts (B j).verts)
    (hmeet : ∀ i j, ((P i).verts ∩ (B j).verts).ncard = 1)
    (hord : ∀ i, (P i).toPath.MeetsInOrder (fun j ↦ (B j).toPath.toSubgraph)) :
    m < θ ∨ n < θ * θ.factorial / 2 := by exact GraphMinor.GM01.Full.theorem_2_1_proof hθ hV hE hG P B hP hPD hB hBD hmeet hord

end

section

open Graph Set SimpleGraph GM05

universe u v

/-- Graph Minors I, (2.2), page 42, for graphs with loops and multiple edges:
"If $P_1, ..., P_m$ are disjoint paths of $G \in \mathcal{F}_\theta$, and $B_1, ..., B_n$ are
disjoint stars, and each $P_i$ has exactly one vertex in common with each $B_j$, and no $P_i$
contains the centre of any star $B_j$, and each $P_i$ meets $B_1, ..., B_n$ in that order, then
either $m < \theta$ or $n < \theta(\theta - 1)$."
The simple special case is `GM01.theorem_2_2_simple`.

The statement retains actual stars and their centres in multigraphs. -/
theorem theorem_2_2 {α : Type u} {β : Type v}
    {θ m n : ℕ} (hθ : 3 ≤ θ) {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) (hG : ¬ IsIsoMinor (gridGraph θ) G)
    (P : Fin m → Full.Path α β) (B : Fin n → Graph α β) (c : Fin n → α)
    (hP : ∀ i, (P i).IsIn G)
    (hPD : Pairwise fun i j ↦ Disjoint (P i).verts (P j).verts)
    (hB : ∀ j, B j ≤ G) (hstar : ∀ j, Full.IsStarWithCenter (B j) (c j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hmeet : ∀ i j, ((P i).verts ∩ V(B j)).ncard = 1)
    (hc : ∀ i j, c j ∉ (P i).verts)
    (hord : ∀ i, (P i).toPath.MeetsInOrder (fun j ↦ simpleShadow (B j))) :
    m < θ ∨ n < θ * (θ - 1) := by exact GraphMinor.GM01.Full.theorem_2_2_proof hθ hV hE hG P B c hP hPD hB hstar hBD hmeet hc hord

end

section

open Graph Set SimpleGraph GM05

universe u v

/-- Graph Minors I, (2.3), page 43, for graphs with loops and multiple edges:
"If $P_1, \dots, P_m$ are disjoint paths of $G \in \mathcal{F}_\theta$, and $B_1, \dots, B_n$ are
disjoint connected subgraphs of $G$, and each $P_i$ meets each $B_j$, and for $1 \le j < j' \le n$
all vertices of $B_j$ on $P_i$ occur before all vertices of $B_{j'}$, then either
$m < \frac{1}{2}\theta^2$ or $n < \theta^{2\theta - 2}$."
The simple special case is `GM01.theorem_2_3_simple`.

The statement applies to general finite graphs. -/
theorem theorem_2_3 {α : Type u} {β : Type v}
    {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    (P : Fin m → Full.Path α β) (B : Fin n → Graph α β)
    (hP : ∀ i, (P i).IsIn G)
    (hPD : Pairwise fun i j ↦ Disjoint (P i).verts (P j).verts)
    (hB : ∀ j, B j ≤ G) (hconn : ∀ j, GraphConnected (B j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hmeet : ∀ i j, ((P i).verts ∩ V(B j)).Nonempty)
    (hord : ∀ i, (P i).toPath.MeetsInOrder (fun j ↦ simpleShadow (B j))) :
    m < θ ^ 2 / 2 ∨ n < θ ^ (2 * θ - 2) := by exact GraphMinor.GM01.Full.theorem_2_3_proof hθ heven hV hE hG P B hP hPD hB hconn hBD hmeet hord

end

section

open Graph Set SimpleGraph GM05

universe u v

/-- **Graph Minors I, (2.4)** (page 44):
"If $P_1, \dots, P_m$ are disjoint paths of $G \in \mathcal{F}_\theta$, and $B_1, \dots, B_n$ are disjoint connected subgraphs of $G$, and each $B_j$ meets at least $\frac{1}{2}\theta^2$ of $P_1, \dots, P_m$, and for $1 \le i \le m$ and for $1 \le j < j' \le n$, all vertices of $B_j$ on $P_i$ occur before all vertices of $B_{j'}$, then $n < \theta^{2\theta - 2} \binom{m}{\frac{1}{2}\theta^2}$."

Graph Minors I, (2.4), page 44, for graphs with loops and multiple edges,
with the boundary correction `θ ^ 2 / 2 ≤ m`. The unrestricted printed
statement fails for the empty graph and `m = n = 0`: its conclusion is
`0 < 0`. This is the general-graph form of the corrected simple statement
`GM01.theorem_2_4_simple`, and is not an exact version of the printed bound.

The extra bound on the first family excludes the false empty-family case. The graph may have loops
and parallel edges. See the correction to (2.4) in `corrections/GM01.md`. -/
theorem theorem_2_4 {α : Type u} {β : Type v}
    {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    (hm : θ ^ 2 / 2 ≤ m)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    (P : Fin m → Full.Path α β) (B : Fin n → Graph α β)
    (hP : ∀ i, (P i).IsIn G)
    (hPD : Pairwise fun i j ↦ Disjoint (P i).verts (P j).verts)
    (hB : ∀ j, B j ≤ G) (hconn : ∀ j, GraphConnected (B j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hmeet : ∀ j, θ ^ 2 / 2 ≤ {i : Fin m | ((P i).verts ∩ V(B j)).Nonempty}.ncard)
    (hord : ∀ i, (P i).toPath.MeetsInOrder (fun j ↦ simpleShadow (B j))) :
    n < θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2) := by exact GraphMinor.GM01.Full.theorem_2_4_proof hθ heven hm hV hE hG P B hP hPD hB hconn hBD hmeet hord

end

section

open Graph Set SimpleGraph GM05

universe u v

/-- **Graph Minors I, (2.5)** (page 44):
"If $A_1, A_2 \subseteq V(G)$, and there is a unique set $\{P_1, \dots, P_m\}$ of $m$ disjoint paths
in $G$ from $A_1$ to $A_2$, and every vertex of $G$ is in one of these paths, then there is an
integer-valued function $\mu$ defined on $V(G)$, such that
(i) if $v'$ is after $v$ on $P_i$, then $\mu(v') > \mu(v)$ ($1 \le i \le m$);
(ii) for any integer $t$, $Z_t$ separates $\{v \colon \mu(v) < t\}$ from
$\{v \colon \mu(v) \ge t\}$, where
$Z_t = \{v \colon \text{for some } i, v \text{ is the first vertex on } P_i \text{ with } \mu(v) \ge t\}$."
This full form uses actual-edge uniqueness. The simple special case is
`GM01.theorem_2_5_simple`.

Uniqueness concerns actual paths, including their chosen edges. -/
theorem theorem_2_5 {α : Type u} {β : Type v}
    {G : Graph α β} (hV : V(G).Finite)
    {A₁ A₂ : Set α} (_hA₁ : A₁ ⊆ V(G)) (_hA₂ : A₂ ⊆ V(G))
    {m : ℕ} (P : Fin m → Full.Path α β)
    (hunique : Full.IsUniqueDisjointPathFamily G A₁ A₂ P)
    (hspan : V(G) ⊆ ⋃ i, (P i).verts) :
    ∃ μ : α → ℤ,
      (∀ i (x y : α), (P i).toPath.Precedes x y → μ x < μ y) ∧
      ∀ t : ℤ, Full.Separates G {x | ∃ i, (P i).toPath.IsFirstGe μ t x}
        {x | x ∈ V(G) ∧ μ x < t} {x | x ∈ V(G) ∧ t ≤ μ x} := by exact GraphMinor.GM01.Full.theorem_2_5_proof hV _hA₁ _hA₂ P hunique hspan

end

section

open Graph Set SimpleGraph GM05

universe u v

/-- **Graph Minors I, (2.6)** (page 46):
"Suppose that $G \in \mathcal{F}_\theta$, and $A_1, A_2 \subseteq V(G)$, and $m > 0$ is an integer, and the following conditions are satisfied:"

Graph Minors I, (2.6), page 46, for general graphs, with the boundary
correction `θ ^ 2 / 2 ≤ m`. Actual-edge uniqueness is transferred by lifting
competitors. The unrestricted printed version fails for one isolated vertex,
its unique one-vertex path, `θ = 6` and `n = 0`. This is the general form of
corrected `GM01.theorem_2_6_simple`, rather than the false unrestricted version.

The extra bound on the first family excludes the false empty-family case. See the correction to
(2.6) in `corrections/GM01.md`. -/
theorem theorem_2_6 {α : Type u} {β : Type v}
    {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    (hm : θ ^ 2 / 2 ≤ m)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    {A₁ A₂ : Set α} (_hA₁ : A₁ ⊆ V(G)) (_hA₂ : A₂ ⊆ V(G))
    (P : Fin m → Full.Path α β) (hunique : Full.IsUniqueDisjointPathFamily G A₁ A₂ P)
    (hspan : V(G) ⊆ ⋃ i, (P i).verts)
    (B : Fin n → Graph α β) (hB : ∀ j, B j ≤ G)
    (hconn : ∀ j, GraphConnected (B j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hmeet : ∀ j, θ ^ 2 / 2 ≤ {i : Fin m | ((P i).verts ∩ V(B j)).Nonempty}.ncard) :
    n < 2 * m * θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2) := by exact GraphMinor.GM01.Full.theorem_2_6_proof hθ heven hm hV hE hG _hA₁ _hA₂ P hunique hspan B hB hconn hBD hmeet

end

section

open Graph Set SimpleGraph GM05

universe u v

/-- **Graph Minors I, (2.7)** (page 47):
"Suppose that there are $m$ disjoint paths in $G \in \mathscr{F}_\theta$ from $A_1$ to $A_2$, where
$A_1, A_2 \subseteq V(G)$; and that $B_1, \dots, B_n$ are disjoint connected subgraphs of $G$, and
for $1 \le j \le n$, $V(B_j)$ separates $A_1$ and $A_2$. Then either $m < \frac{1}{2}\theta^2$ or
$n < \theta^{2\theta}$."
This is the general-graph form. The simple special case is `GM01.theorem_2_7_simple`.

The statement applies to general finite graphs. The proof prints "incident with $v_0$" for
"incident with $v$" (see the correction to the proof of (2.7) in `corrections/GM01.md`). -/
theorem theorem_2_7 {α : Type u} {β : Type v}
    {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    {A₁ A₂ : Set α} (hA₁ : A₁ ⊆ V(G)) (hA₂ : A₂ ⊆ V(G))
    (P : Fin m → Full.Path α β) (hP : Full.IsDisjointPathFamily G A₁ A₂ P)
    (B : Fin n → Graph α β) (hB : ∀ j, B j ≤ G)
    (hconn : ∀ j, GraphConnected (B j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hsep : ∀ j, Full.Separates G V(B j) A₁ A₂) :
    m < θ ^ 2 / 2 ∨ n < θ ^ (2 * θ) := by exact GraphMinor.GM01.Full.theorem_2_7_proof hθ heven hV hE hG hA₁ hA₂ P hP B hB hconn hBD hsep

end

section

open Graph Set SimpleGraph GM05

universe u v

/-- **Graph Minors I, (2.8)** (page 48):
"Let $A_1, A_2, X \subseteq V(G)$, where $G \in \mathscr{F}_\theta$, and let $B_1, \dots, B_n$ be disjoint subgraphs of $G$, each with at most $d$ components. Suppose that the following conditions are satisfied:"

Graph Minors I, (2.8), page 48, for general graphs, with the boundary
correction `0 < d + r`. The printed version fails for `d = r = m = 0`,
empty endpoint sets and `n = θ²` empty subgraphs. This transfers the corrected
simple statement `GM01.theorem_2_8_simple`, rather than the false unrestricted one.

The hypothesis that the sum of the two parameters is positive excludes a false boundary case. See
the correction to (2.8) in `corrections/GM01.md`. -/
theorem theorem_2_8 {α : Type u} {β : Type v}
    {θ d r m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    (hs : 0 < d + r)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    {A₁ A₂ X : Set α} (hA₁ : A₁ ⊆ V(G)) (hA₂ : A₂ ⊆ V(G)) (hX : X ⊆ V(G))
    (hXcard : X.ncard ≤ r * n)
    (P : Fin m → Full.Path α β) (hP : Full.IsDisjointPathFamily G A₁ A₂ P)
    (havoid : ∀ i, Disjoint (P i).verts X)
    (B : Fin n → Graph α β) (hB : ∀ j, B j ≤ G)
    (hcomp : ∀ j, Full.numComponents (B j) ≤ d)
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hsep : ∀ j, Full.Separates G (X ∪ V(B j)) A₁ A₂) :
    let s := d + r * (θ ^ 2 - 1)
    m < s * θ ^ 2 / 2 ∨ n < 2 ^ (s * θ ^ 2 / 2) * (θ ^ 2 + 2 * s * θ ^ (2 * θ)) := by exact GraphMinor.GM01.Full.theorem_2_8_proof hθ heven hs hV hE hG hA₁ hA₂ hX hXcard P hP havoid B hB hcomp hBD hsep

end

section

open Graph Set SimpleGraph GM05

universe u v

/-- **Graph Minors I, (2.9)** (pages 49–50):
"If $B_1, \dots, B_n$ are disjoint connected subgraphs of a graph $G \in \mathscr{F}_\theta$, and
$V' \subseteq V(G)$ and $r \ge 0$ is an integer, then one of the following is true:
(i) there exists $J \subseteq \{1, \dots, n\}$ with $|J| = r$ such that for each $j \in J$ there is
a path $P_j$ in $G$ from $B_j$ to $V'$, and the paths $P_j$ ($j \in J$) are disjoint, and each has
no internal vertex in $V' \cup \bigcup_{j \in J} V(B_j)$;"
"(ii) there exist $X \subseteq V(G)$ and $J \subseteq \{1, \dots, n\}$ with
$|X| + |J| \le 2^{r\theta^4}$, such that $X$ separates $V'$ from every $B_j$
($j \in \{1, \dots, n\} - J$)."
This is the general-graph form. The simple special case is `GM01.theorem_2_9_simple`.

The statement retains the actual edges of the resulting paths. -/
theorem theorem_2_9 {α : Type u} {β : Type v}
    {θ r n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    {V' : Set α} (hV' : V' ⊆ V(G))
    (B : Fin n → Graph α β) (hB : ∀ j, B j ≤ G)
    (hconn : ∀ j, GraphConnected (B j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j)) :
    (∃ (J : Set (Fin n)) (P : J → Full.Path α β),
      J.ncard = r ∧
      (∀ j : J, (P j).IsFromTo G V(B j.1) V') ∧
      Pairwise (fun i j : J ↦ Disjoint (P i).verts (P j).verts) ∧
      (∀ j : J, Disjoint (P j).toPath.internalVerts (V' ∪ ⋃ j' ∈ J, V(B j')))) ∨
    (∃ (X : Set α) (J : Set (Fin n)),
      X ⊆ V(G) ∧ X.ncard + J.ncard ≤ 2 ^ (r * θ ^ 4) ∧
      ∀ j ∉ J, Full.Separates G X V' V(B j)) := by exact GraphMinor.GM01.Full.theorem_2_9_proof hθ heven hV hE hG hV' B hB hconn hBD

end

section

open Set Graph SimpleGraph

universe u v

/-- Graph Minors I, (2.10), page 50: "There is an integer $\theta' > 0$
such that if $A_1, \dots, A_{\theta'}$ are disjoint connected subgraphs
of a graph $G \in \mathscr{F}_\theta$, and $B_1, \dots, B_{\theta'}$ are
also disjoint connected subgraphs of $G$, then some $A_i$ is disjoint
from some $B_j$."
Use the proved GM05 (5.3) through the simple form, then lift the
vertex-set conclusion to the general graph. The fixed even grid
parameter satisfies the standing Section 2 condition `θ ≥ 6`.

The proof uses the mesh bound from Graph Minors V, where the paper says this result is proved. -/
theorem theorem_2_10 {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) :
    ∃ n : ℕ, 0 < n ∧ ∀ {α : Type u} {β : Type v} (G : Graph α β),
      V(G).Finite → ¬ IsIsoMinor (gridGraph θ) G →
      ∀ (A B : Fin n → Graph α β),
        (∀ i, A i ≤ G) → (∀ j, B j ≤ G) →
        (∀ i, GraphConnected (A i)) → (∀ j, GraphConnected (B j)) →
        (Pairwise fun i j ↦ Disjoint V(A i) V(A j)) →
        (Pairwise fun i j ↦ Disjoint V(B i) V(B j)) →
        ∃ i j, Disjoint V(A i) V(B j) := by exact GraphMinor.GM01.theorem_2_10_proof hθ heven

end

/-! ## Section 3. The Main Theorem -/

section

open Set Graph
open Graph

universe u v

/-- Graph Minors I, (3.1), page 51: "For $\lambda \ge 1$, odd, there is
a number $w(\lambda)$ such that every graph with no minor isomorphic to
$\mathbf{Y}_\lambda$ has path-with $\le w(\lambda)$."
Follow its proof on page 54 using the now-proved (3.5) and (3.7)(i).
The bound is `p(lam,3)` and every component receives the same bound. -/
theorem theorem_3_1 :
  ∀ ℓ : ℕ, 0 < ℓ → Odd ℓ → ∃ w : ℕ,
    ∀ {α : Type u} {β : Type v} (G : Graph α β), V(G).Finite → E(G).Finite →
      ¬ IsIsoMinor (forestTreeGraph ℓ) G → HasPathWidthLE G w := by exact GraphMinor.GM01.theorem_3_1_proof

end

section

open Set Graph

/-- Graph Minors I, (3.2), page 51: "For any even $\lambda \ge 0$, the
$(2^{(\lambda+1)/2}-1)$-grid has a minor isomorphic to $\mathbf{H}_\lambda$."
The printed exponent is corrected to `λ / 2 + 1`. This is the smallest
correction consistent with the one-vertex base and Figure 3's height-six
subdivision in the fifteen-grid. The proof follows that diagram's
induction, adding two levels at each step.

The grid exponent is corrected to give an integer and the required height-zero case. See the
correction to (3.2) in `corrections/GM01.md`. -/
theorem theorem_3_2 (lam : ℕ) (heven : Even lam) :
    IsIsoMinor (toGraph (binaryTree lam)) (gridGraph (2 ^ (lam / 2 + 1) - 1)) := by exact GraphMinor.GM01.theorem_3_2_proof lam heven

end

section

open Set SimpleGraph

/-- Graph Minors I, (3.3), page 51: "For any $\lambda \ge 1$,
$\mathbf{Y}_\lambda$ is isomorphic to a minor of $\mathbf{H}_{\lambda+1}$."
Contract the first two binary levels to the centre and retain three
of the four grandchild subtrees. -/
theorem theorem_3_3 (lam : ℕ) (hlam : 1 ≤ lam) :
    IsIsoMinor (forestTreeGraph lam) (toGraph (binaryTree (lam + 1))) := by exact GraphMinor.GM01.theorem_3_3_proof lam hlam

end

section



/-- Graph Minors I, (3.4), page 52: "For any odd $\lambda \ge 1$, the
$(2^{(\lambda+3)/2}-1)$-grid has a minor isomorphic to $\mathbf{Y}_\lambda$."
Compose the corrected diagram (3.2) with the contraction (3.3), as in
the paper. -/
theorem theorem_3_4 (lam : ℕ) (hlam : 1 ≤ lam) (hodd : Odd lam) :
    IsIsoMinor (forestTreeGraph lam) (gridGraph (2 ^ ((lam + 3) / 2) - 1)) := by exact GraphMinor.GM01.theorem_3_4_proof lam hlam hodd

end

section



/-- Graph Minors I, (3.5), page 52: "For odd $\lambda \ge 1$, let
$\theta = \max(6, 2^{(\lambda+3)/2})$. For any graph $G$, if $G$ has no
minor isomorphic to $\mathbf{Y}_\lambda$, then $G \in \mathscr{F}_\theta$."
Use (3.4), include its grid in the larger square, and compose minors. -/
theorem theorem_3_5 {α β : Type*} (lam : ℕ) (hlam : 1 ≤ lam) (hodd : Odd lam)
    (G : Graph α β) (hNo : ¬ IsIsoMinor (forestTreeGraph lam) G) :
    ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G := by exact GraphMinor.GM01.theorem_3_5_proof lam hlam hodd G hNo

end

section



/-- **Graph Minors I, (3.6)** (page 53):
"With the above definitions, the following inequalities hold:"

Graph Minors I, (3.6)(i)–(iv), page 53, with the definitions of
`θ`, `α`, `β`, `f`, `p`, and `q` on that page. The proof supplies the
four estimates that the paper leaves to the reader. -/
theorem theorem_3_6 {lam : ℕ} (_hlam : 1 ≤ lam) (hodd : Odd lam) :
    (∀ δ : ℕ, 2 ≤ δ → δ - 2 ≤ pathWidthBound lam 0 δ) ∧
    (∀ γ δ : ℕ, 1 ≤ γ → 2 ≤ δ →
      (gm01Theta lam) ^ 2 +
        pathWidthBound lam (γ - 1) (2 + 4 * (gm01Theta lam) ^ (2 * gm01Theta lam) + 2 * δ) ≤
        forkWidthBound lam γ δ) ∧
    (∀ γ δ : ℕ, 1 ≤ γ → 2 ≤ δ → forkWidthBound lam γ 4 ≤ pathWidthBound lam γ δ) ∧
    (∀ γ δ : ℕ, 1 ≤ γ → γ ≤ lam → 3 ≤ δ →
      (gm01Alpha lam) ^ (δ * 2 ^ γ) +
        max (pathWidthBound lam γ (δ - 1))
          (forkWidthBound lam γ (3 * (gm01Alpha lam) ^ (δ * 2 ^ γ) + 6)) ≤
        pathWidthBound lam γ δ) := by exact GraphMinor.GM01.theorem_3_6_proof _hlam hodd

end

section

open Set Graph SimpleGraph

/-- Graph Minors I, (3.7), page 54:
"If $G \in \mathscr{F}_\theta$, and is rooted and connected, and has no rooted minor isomorphic to $P(\gamma, \delta)$, then $G$ has path-width at most $p(\gamma, \delta)$, for $0 \le \gamma \le \lambda$, $\delta \ge 2$."
"If $G \in \mathscr{F}_\theta$, and is rooted and connected, and has no rooted minor isomorphic to $Q(\gamma, \delta)$, then $G$ has path-width at most $q(\gamma, \delta)$, for $1 \le \gamma \le \lambda$, $\delta \ge 2$."

The height and length inductions follow Parts 1–3, pages 54–61. -/
theorem theorem_3_7 {α β : Type*} (lam : ℕ) (_hlam : 1 ≤ lam) (hodd : Odd lam)
    (G : RootedGraph α β) (hV : V(G.graph).Finite) (_hE : E(G.graph).Finite)
    (hConn : GraphConnected G.graph)
    (hGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph) :
    ((∀ γ : ℕ, γ ≤ lam → ∀ (δ : ℕ) (hδ : 2 ≤ δ),
      (¬ HasRootedMinor (rootedPathComb γ δ (by omega)) G) →
      HasPathWidthLE G.graph (pathWidthBound lam γ δ)) ∧
    (∀ (γ : ℕ) (hγ : 0 < γ), γ ≤ lam → ∀ (δ : ℕ) (hδ : 2 ≤ δ),
      (¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G) →
      HasPathWidthLE G.graph (forkWidthBound lam γ δ))) := by exact GraphMinor.GM01.theorem_3_7_proof lam _hlam hodd G hV _hE hConn hGrid

end

/-! ## Section 4. Part 2: The Reduction of $Q(\gamma, \delta)$ -/

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.1), page 55:
"For $1 \le j \le n$, $S_j$ separates $\bigcup_{1 \le j' \le j} S_{j'}$ from $\bigcup_{j \le j' \le n} S_{j'}$ in $G$."

As printed, both unions contain `S_j`. The indices here start at zero.
The proof trims a separator-failure path and performs the paper's
rooted-fork contraction using the preceding initial piece, skipped
binary arm and final comb arm. -/
theorem theorem_4_1 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    (j : Fin n) :
    GraphSeparates G.graph
      (combBlock hL (subgraphUnion G.graph N R) c j)
      (⋃ i : Fin n, ⋃ (_ : i ≤ j), combBlock hL (subgraphUnion G.graph N R) c i)
      (⋃ i : Fin n, ⋃ (_ : j ≤ i), combBlock hL (subgraphUnion G.graph N R) c i) := by exact GraphMinor.GM01.theorem_4_1_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR j

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- **Graph Minors I, (4.2)** (page 55):
"For $\nu \le j \le n$, there exists $X_j \subseteq V(G)$ with $|X_j| < \frac{1}{2}\theta^2$, separating $\bigcup_{1 \le j' \le j-\nu+1} S_{j'}$ and $\bigcup_{j \le j' \le n} S_{j'}$."

Graph Minors I, (4.2), pages 55–56. The zero-based condition
`θ^(2θ) ≤ j+1` corresponds to the paper's `v ≤ j`. The early union has
`j+2−θ^(2θ)` blocks, matching the paper's union through `S_{j−v+1}`, and
the late union begins at block `j`, as printed. -/
theorem theorem_4_2 {α : Type u} {β : Type v} {γ δ L n θ : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β) (hfin : V(G.graph).Finite)
    (hθ : 6 ≤ θ) (heven : Even θ) (hGrid : ¬ IsIsoMinor (gridGraph θ) G.graph)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    (j : Fin n) (hj : θ ^ (2 * θ) ≤ j.val + 1) :
    ∃ X ⊆ V(G.graph), X.ncard < θ ^ 2 / 2 ∧ GraphSeparates G.graph X
      (⋃ i : Fin n, ⋃ (_ : i.val < j.val + 2 - θ ^ (2 * θ)),
        combBlock hL (subgraphUnion G.graph N R) c i)
      (⋃ i : Fin n, ⋃ (_ : j ≤ i), combBlock hL (subgraphUnion G.graph N R) c i) := by exact GraphMinor.GM01.theorem_4_2_proof hγ hδ hL htail G hfin hθ heven hGrid hno hN hc hV hE hPaths hInter hR hmeetR j hj

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.3), page 56.
"For $\nu \le j \le n$, $X_j \subseteq S_{j-\nu+1} \cup Z_{j-\nu+2} \cup \dots \cup Z_{j-1} \cup S_j$."

A minimal window separator is contained in its boundary blocks and the attachment regions between.
The indices start at zero. The parameter `ν` is the window length
(called `v` in the paper). As in the minimal choice after (4.2), `X`
is an inclusion-minimal separator of the blocks up to `l` from the
blocks from `j` on. -/
theorem theorem_4_3 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    (ν : ℕ) (hν : 3 ≤ ν) (l j : Fin n) (hwindow : l.val + ν = j.val + 1)
    {X : Set α} (hX : IsMinimalGraphSeparator G.graph X
      (⋃ i : Fin n, ⋃ (_ : i ≤ l), combBlock hL (subgraphUnion G.graph N R) c i)
      (⋃ i : Fin n, ⋃ (_ : j ≤ i), combBlock hL (subgraphUnion G.graph N R) c i)) :
    X ⊆ combBlock hL (subgraphUnion G.graph N R) c l ∪
      (⋃ i : Fin n, ⋃ (_ : l < i ∧ i < j),
        blockAttachmentRegion G.graph (⋃ k : Fin n,
          combBlock hL (subgraphUnion G.graph N R) c k)
          (combBlock hL (subgraphUnion G.graph N R) c i)) ∪
      combBlock hL (subgraphUnion G.graph N R) c j := by exact GraphMinor.GM01.theorem_4_3_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR ν hν l j hwindow hX

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.4), page 56, parts (i) and (ii).
"For $\nu \le i \le n$, $1 \le j \le n$, if $s \in S_j$, then (i) $X_i$ separates $s$ and $\rho(G)$ if $j \ge 1$, and (ii) $X_i$ does not separate $s$ and $\rho(G)$ if $j \le i - \nu$."

Late blocks are separated from the root and blocks before the separator window
are not. Indices start at zero: the paper's `i` and `j` are `j + 1` and
`k + 1` here. Part (i) is stated for `j ≥ i`, not for `j ≥ 1` as
printed: with `j = 1` the printed (i) contradicts (ii). See the correction to (4.4) in
`corrections/GM01.md`. -/
theorem theorem_4_4 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    (ν : ℕ) (hν : 3 ≤ ν) (l j : Fin n) (hwindow : l.val + ν = j.val + 1)
    {X : Set α} (hX : IsMinimalGraphSeparator G.graph X
      (⋃ i : Fin n, ⋃ (_ : i ≤ l), combBlock hL (subgraphUnion G.graph N R) c i)
      (⋃ i : Fin n, ⋃ (_ : j ≤ i), combBlock hL (subgraphUnion G.graph N R) c i))
    (k : Fin n) {s : α} (hs : s ∈ combBlock hL (subgraphUnion G.graph N R) c k) :
    (j ≤ k → GraphSeparates G.graph X {s} {G.root.val}) ∧
    (k.val + ν ≤ j.val → ¬ GraphSeparates G.graph X {s} {G.root.val}) := by exact GraphMinor.GM01.theorem_4_4_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR ν hν l j hwindow hX k hs

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.5), pages 56–57:
"For $1 \le i, i' \le T$ and for every $y \in Y_{i'}$, $Y_i$ separates $y$ and $\rho(G)$ if and only if $i \le i'$."

Indices start at zero. The functions `left` and `right` record the
boundary indices of the sampled windows. The minimal separators are
those of (4.3) and (4.4). -/
theorem theorem_4_5 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (i i' : Fin T) {y : α} (hy : y ∈ Y i') :
    GraphSeparates G.graph (Y i) {y} {G.root.val} ↔ i ≤ i' := by exact GraphMinor.GM01.theorem_4_5_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR hν left right hleft hright Y hY i i' hy

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.6), page 57: "$A, B$ and $W_i$ are disjoint."
The proof uses (4.4) for each block and the defining two tests of the
layer. The local choices are the minimal separators of (4.3) and
(4.4). No separation conclusion is assumed. -/
theorem theorem_4_6 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (hn : n = ν * T + 1) (i : Fin (T + 1)) :
    let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
    Disjoint (layerLateBlocks S ν i.val) (layerEarlyBlocks S ν i.val) ∧
      Disjoint (layerLateBlocks S ν i.val) (separatorLayer G.graph G.root.val Y i) ∧
      Disjoint (layerEarlyBlocks S ν i.val) (separatorLayer G.graph G.root.val Y i) := by exact GraphMinor.GM01.theorem_4_6_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i

end

section

open Set Graph SimpleGraph Function Relation GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.7), page 58:
"There is a path in $G$ from $V(D)$ to $V(H)$ avoiding $A \cup B$."
Only nonemptiness and containment in the layer are needed from the
chosen subdivision `D`. The proof follows the paper's two layer cases,
using the minimal separators of (4.3). -/
theorem theorem_4_7 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (hn : n = ν * T + 1) (i : Fin (T + 1))
    (hGconn : GraphConnected G.graph) (hT : 1 ≤ T)
    (D : Graph α β) (hD : V(D).Nonempty)
    (hDW : V(D) ⊆ separatorLayer G.graph G.root.val Y i) :
    let H := subgraphUnion G.graph N R
    let S := fun k : Fin n ↦ combBlock hL H c k
    ∃ d ∈ V(D), ∃ s ∈ V(H), ∃ P₀ : Graph α β,
      IsGraphPathWithEnds G.graph P₀ d s ∧
      Disjoint V(P₀) (layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) := by exact GraphMinor.GM01.theorem_4_7_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i hGconn hT D hD hDW

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.8), page 58:
"There is a path $P_1$ in $G$ from $D$ to $w_1$, avoiding $A \cup B - \{w_1\}$."
The first path is obtained from proved (4.7) and the boundary extension
inside `H`. The bound ensuring the boundary vertex exists is derived
from the paper's tail inequality, not assumed. -/
theorem theorem_4_8 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (hn : n = ν * T + 1) (i : Fin (T + 1))
    (hGconn : GraphConnected G.graph) (hT : 1 ≤ T)
    (D : Graph α β) (hD : V(D).Nonempty)
    (hDW : V(D) ⊆ separatorLayer G.graph G.root.val Y i) :
    let H := subgraphUnion G.graph N R
    let S := fun k : Fin n ↦ combBlock hL H c k
    let hbound : 2 * (ν * (i.val - 1)) ≤ L := by
      have hm := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
      omega
    let w := firstLayerBoundary G c ν i.val (by omega) hbound
    ∃ d ∈ V(D), ∃ P₁ : Graph α β, IsGraphPathWithEnds G.graph P₁ d w ∧
      Disjoint V(P₁) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}) := by exact GraphMinor.GM01.theorem_4_8_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i hGconn hT D hD hDW

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.9), page 58: "$d_1$ is in one of the ends of $D$."
The first boundary path is the paper's chosen path meeting `D` only
at its initial end. The proof constructs the root path and the rooted
fork model, rather than assuming the contraction step. -/
theorem theorem_4_9 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (hn : n = ν * T + 1) (i : Fin (T + 1))
    {m : ℕ} (hm : m = 2 + 4 * ν + 2 * δ) (D : Graph α β) (hDG : D ≤ G.graph)
    (hDW : V(D) ⊆ separatorLayer G.graph G.root.val Y i)
    {cD : (pathComb (γ - 1) m).verts → α} (hcD : Injective cD)
    (PD : (pathComb (γ - 1) m).coe.edgeSet → Graph α β)
    (hVD : V(D) = range cD ∪ ⋃ e, V(PD e))
    (hDPaths : ∀ e : (pathComb (γ - 1) m).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (PD e) (cD a) (cD b) ∧ V(PD e) ∩ range cD = {cD a,cD b})
    (hDInter : ∀ e f : (pathComb (γ - 1) m).coe.edgeSet, e ≠ f → V(PD e) ∩ V(PD f) ⊆ range cD)
    (d₁ : V(D)) (P₁ : Graph α β)
    (hP₁ : IsGraphPathWithEnds G.graph P₁ d₁.val
      (firstLayerBoundary G c ν i.val (by omega) (by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega)))
    (hP₁D : V(P₁) ∩ V(D) = {d₁.val}) :
    d₁.val ∈ combFirstEndSupport (by omega) cD PD ∪ combSecondEndSupport (by omega) cD PD := by exact GraphMinor.GM01.theorem_4_9_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths hDInter d₁ P₁ hP₁ hP₁D

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.10), page 58: "$i \ne T$."
Apply proved (4.9), reflect the actual subdivision when needed, and
perform the longer-comb contraction in the resulting first-end
orientation. The orientation is a constructed choice, not a hypothesis. -/
theorem theorem_4_10 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (hn : n = ν * T + 1) (i : Fin (T + 1))
    {m : ℕ} (hm : m = 2 + 4 * ν + 2 * δ) (D : Graph α β) (hDG : D ≤ G.graph)
    (hDW : V(D) ⊆ separatorLayer G.graph G.root.val Y i)
    {cD : (pathComb (γ - 1) m).verts → α} (hcD : Injective cD)
    (PD : (pathComb (γ - 1) m).coe.edgeSet → Graph α β)
    (hVD : V(D) = range cD ∪ ⋃ e, V(PD e))
    (hDPaths : ∀ e : (pathComb (γ - 1) m).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (PD e) (cD a) (cD b) ∧ V(PD e) ∩ range cD = {cD a,cD b})
    (hDInter : ∀ e f : (pathComb (γ - 1) m).coe.edgeSet, e ≠ f →
      V(PD e) ∩ V(PD f) ⊆ range cD ∧ Disjoint E(PD e) E(PD f))
    (d₁ : V(D)) (P₁ : Graph α β)
    (hP₁ : IsGraphPathWithEnds G.graph P₁ d₁.val
      (firstLayerBoundary G c ν i.val (by omega) (by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega)))
    (hP₁D : V(P₁) ∩ V(D) = {d₁.val})
    (hAvoidP₁ :
      let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
      let hbound : 2 * (ν * (i.val - 1)) ≤ L := by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega
      let w := firstLayerBoundary G c ν i.val (by omega) hbound
      Disjoint V(P₁) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}))
    (hT : 2 ≤ T)
    (hmaxT : ∀ t : ℕ, 2 * ν * t ≤ L - 2 * δ → t ≤ T)
    (hmaxL : ∀ k (hk : 0 < k), HasRootedMinor (rootedPathComb (γ - 1) k hk) G → k ≤ L) :
    i.val ≠ T := by exact GraphMinor.GM01.theorem_4_10_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths hDInter d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.11), page 58:
"There is a path $P_2$ from $D$ to $w_2$ avoiding $A \cup B - \{w_2\}$."
The conclusion also constructs the late boundary vertex with its
printed block and adjacency conditions, and makes the following
minimal first-hit choice explicit. Result (4.10) is proved and used,
not assumed as an extra hypothesis. -/
theorem theorem_4_11 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (hn : n = ν * T + 1) (i : Fin (T + 1))
    {m : ℕ} (hm : m = 2 + 4 * ν + 2 * δ) (D : Graph α β) (hDG : D ≤ G.graph)
    (hDW : V(D) ⊆ separatorLayer G.graph G.root.val Y i)
    {cD : (pathComb (γ - 1) m).verts → α} (hcD : Injective cD)
    (PD : (pathComb (γ - 1) m).coe.edgeSet → Graph α β)
    (hVD : V(D) = range cD ∪ ⋃ e, V(PD e))
    (hDPaths : ∀ e : (pathComb (γ - 1) m).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (PD e) (cD a) (cD b) ∧ V(PD e) ∩ range cD = {cD a,cD b})
    (hDInter : ∀ e f : (pathComb (γ - 1) m).coe.edgeSet, e ≠ f →
      V(PD e) ∩ V(PD f) ⊆ range cD ∧ Disjoint E(PD e) E(PD f))
    (d₁ : V(D)) (P₁ : Graph α β)
    (hP₁ : IsGraphPathWithEnds G.graph P₁ d₁.val
      (firstLayerBoundary G c ν i.val (by omega) (by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega)))
    (hP₁D : V(P₁) ∩ V(D) = {d₁.val})
    (hAvoidP₁ :
      let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
      let hbound : 2 * (ν * (i.val - 1)) ≤ L := by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega
      let w := firstLayerBoundary G c ν i.val (by omega) hbound
      Disjoint V(P₁) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}))
    (hT : 2 ≤ T)
    (hmaxT : ∀ t : ℕ, 2 * ν * t ≤ L - 2 * δ → t ≤ T)
    (hmaxL : ∀ k (hk : 0 < k), HasRootedMinor (rootedPathComb (γ - 1) k hk) G → k ≤ L)
    (hGconn : GraphConnected G.graph) :
    let H := subgraphUnion G.graph N R
    let S := fun k : Fin n ↦ combBlock hL H c k
    let h2n : 2 * n ≤ L := by omega
    let cut := combBlockCutCentre hL h2n c
    ∃ k : Fin n, k.val + 1 = ν * (i.val + 1) ∧ ∃ w₂ ∈ S k,
      cut k ∈ S (⟨k.val - 1, by omega⟩ : Fin n) ∧ H.Adj (cut k) w₂ ∧
      ∃ d₂ ∈ V(D), ∃ P₂ : Graph α β, IsGraphPathWithEnds G.graph P₂ d₂ w₂ ∧
        Disjoint V(P₂) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w₂}) ∧
        V(P₂) ∩ V(D) = {d₂} := by exact GraphMinor.GM01.theorem_4_11_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths hDInter d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL hGconn

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09 GraphMinor.Surface

universe u v

/-- Graph Minors I, (4.12), page 59:
"$d_2$ *is in the second end of* $D$."
The first attachment is in the first end, in the orientation chosen
after (4.9). The maximality conditions are the actual choices from
page 55 and are used through proved (4.10). -/
theorem theorem_4_12 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (hn : n = ν * T + 1) (i : Fin (T + 1))
    {m : ℕ} (hm : m = 2 + 4 * ν + 2 * δ) (D : Graph α β) (hDG : D ≤ G.graph)
    (hDW : V(D) ⊆ separatorLayer G.graph G.root.val Y i)
    {cD : (pathComb (γ - 1) m).verts → α} (hcD : Injective cD)
    (PD : (pathComb (γ - 1) m).coe.edgeSet → Graph α β)
    (hVD : V(D) = range cD ∪ ⋃ e, V(PD e))
    (hDPaths : ∀ e : (pathComb (γ - 1) m).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (PD e) (cD a) (cD b) ∧ V(PD e) ∩ range cD = {cD a,cD b})
    (hDInter : ∀ e f : (pathComb (γ - 1) m).coe.edgeSet, e ≠ f →
      V(PD e) ∩ V(PD f) ⊆ range cD ∧ Disjoint E(PD e) E(PD f))
    (d₁ : V(D)) (P₁ : Graph α β)
    (hP₁ : IsGraphPathWithEnds G.graph P₁ d₁.val
      (firstLayerBoundary G c ν i.val (by omega) (by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega)))
    (hP₁D : V(P₁) ∩ V(D) = {d₁.val})
    (hAvoidP₁ :
      let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
      let hbound : 2 * (ν * (i.val - 1)) ≤ L := by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega
      let w := firstLayerBoundary G c ν i.val (by omega) hbound
      Disjoint V(P₁) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}))
    (hT : 2 ≤ T)
    (hmaxT : ∀ t : ℕ, 2 * ν * t ≤ L - 2 * δ → t ≤ T)
    (hmaxL : ∀ k (hk : 0 < k), HasRootedMinor (rootedPathComb (γ - 1) k hk) G → k ≤ L)
    (hfirst : d₁.val ∈ combFirstEndSupport (by omega) cD PD)
    (q : Fin n) (hq : q.val + 1 = ν * (i.val + 1))
    (w₂ : α) (hw₂ : w₂ ∈ combBlock hL (subgraphUnion G.graph N R) c q)
    (d₂ : V(D)) (P₂ : Graph α β) (hP₂ : IsGraphPathWithEnds G.graph P₂ d₂.val w₂)
    (hAvoidP₂ :
      let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
      Disjoint V(P₂) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w₂}))
    (hP₂D : V(P₂) ∩ V(D) = {d₂.val}) :
    d₂.val ∈ combSecondEndSupport (by omega) cD PD := by exact GraphMinor.GM01.theorem_4_12_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths hDInter d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL hfirst q hq w₂ hw₂ d₂ P₂ hP₂ hAvoidP₂ hP₂D

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.13), page 59:
"$P_1$ *and* $P_2$ *are disjoint.*"
Apply proved (4.12) to the rerouted clean path, as in the paper. -/
theorem theorem_4_13 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (hn : n = ν * T + 1) (i : Fin (T + 1))
    {m : ℕ} (hm : m = 2 + 4 * ν + 2 * δ) (D : Graph α β) (hDG : D ≤ G.graph)
    (hDW : V(D) ⊆ separatorLayer G.graph G.root.val Y i)
    {cD : (pathComb (γ - 1) m).verts → α} (hcD : Injective cD)
    (PD : (pathComb (γ - 1) m).coe.edgeSet → Graph α β)
    (hVD : V(D) = range cD ∪ ⋃ e, V(PD e))
    (hDPaths : ∀ e : (pathComb (γ - 1) m).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (PD e) (cD a) (cD b) ∧ V(PD e) ∩ range cD = {cD a,cD b})
    (hDInter : ∀ e f : (pathComb (γ - 1) m).coe.edgeSet, e ≠ f →
      V(PD e) ∩ V(PD f) ⊆ range cD ∧ Disjoint E(PD e) E(PD f))
    (d₁ : V(D)) (P₁ : Graph α β)
    (hP₁ : IsGraphPathWithEnds G.graph P₁ d₁.val
      (firstLayerBoundary G c ν i.val (by omega) (by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega)))
    (hP₁D : V(P₁) ∩ V(D) = {d₁.val})
    (hAvoidP₁ :
      let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
      let hbound : 2 * (ν * (i.val - 1)) ≤ L := by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega
      let w := firstLayerBoundary G c ν i.val (by omega) hbound
      Disjoint V(P₁) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}))
    (hT : 2 ≤ T)
    (hmaxT : ∀ t : ℕ, 2 * ν * t ≤ L - 2 * δ → t ≤ T)
    (hmaxL : ∀ k (hk : 0 < k), HasRootedMinor (rootedPathComb (γ - 1) k hk) G → k ≤ L)
    (hfirst : d₁.val ∈ combFirstEndSupport (by omega) cD PD)
    (q : Fin n) (hq : q.val + 1 = ν * (i.val + 1))
    (w₂ : α) (hw₂ : w₂ ∈ combBlock hL (subgraphUnion G.graph N R) c q)
    (d₂ : V(D)) (P₂ : Graph α β) (hP₂ : IsGraphPathWithEnds G.graph P₂ d₂.val w₂)
    (hAvoidP₂ :
      let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
      Disjoint V(P₂) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w₂}))
    (hP₂D : V(P₂) ∩ V(D) = {d₂.val}) :
    Disjoint V(P₁) V(P₂) := by exact GraphMinor.GM01.theorem_4_13_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths hDInter d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL hfirst q hq w₂ hw₂ d₂ P₂ hP₂ hAvoidP₂ hP₂D

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- **Graph Minors I, (4.14)** (page 59):
"Conclusion."

Graph Minors I, (4.14), page 59, the conclusion of Part 2.
The actual three retained pieces and their joining paths give the
longer rooted comb, contradicting the chosen maximal length.
Results (4.10), (4.12), and (4.13) are proved and invoked internally. The printed conclusion has
unbalanced brackets in $P(\gamma - 1, N + 2\delta - 2)$ (see the correction to (4.14) in
`corrections/GM01.md`). -/
theorem theorem_4_14 {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (hn : n = ν * T + 1) (i : Fin (T + 1))
    {m : ℕ} (hm : m = 2 + 4 * ν + 2 * δ) (D : Graph α β) (hDG : D ≤ G.graph)
    (hDW : V(D) ⊆ separatorLayer G.graph G.root.val Y i)
    {cD : (pathComb (γ - 1) m).verts → α} (hcD : Injective cD)
    (PD : (pathComb (γ - 1) m).coe.edgeSet → Graph α β)
    (hVD : V(D) = range cD ∪ ⋃ e, V(PD e))
    (hDPaths : ∀ e : (pathComb (γ - 1) m).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (PD e) (cD a) (cD b) ∧ V(PD e) ∩ range cD = {cD a,cD b})
    (hDInter : ∀ e f : (pathComb (γ - 1) m).coe.edgeSet, e ≠ f →
      V(PD e) ∩ V(PD f) ⊆ range cD ∧ Disjoint E(PD e) E(PD f))
    (d₁ : V(D)) (P₁ : Graph α β)
    (hP₁ : IsGraphPathWithEnds G.graph P₁ d₁.val
      (firstLayerBoundary G c ν i.val (by omega) (by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega)))
    (hP₁D : V(P₁) ∩ V(D) = {d₁.val})
    (hAvoidP₁ :
      let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
      let hbound : 2 * (ν * (i.val - 1)) ≤ L := by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega
      let w := firstLayerBoundary G c ν i.val (by omega) hbound
      Disjoint V(P₁) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}))
    (hT : 2 ≤ T)
    (hmaxT : ∀ t : ℕ, 2 * ν * t ≤ L - 2 * δ → t ≤ T)
    (hmaxL : ∀ k (hk : 0 < k), HasRootedMinor (rootedPathComb (γ - 1) k hk) G → k ≤ L)
    (hfirst : d₁.val ∈ combFirstEndSupport (by omega) cD PD)
    (q : Fin n) (hq : q.val + 1 = ν * (i.val + 1))
    (w₂ : α) (hw₂ : w₂ ∈ combBlock hL (subgraphUnion G.graph N R) c q)
    (d₂ : V(D)) (P₂ : Graph α β) (hP₂ : IsGraphPathWithEnds G.graph P₂ d₂.val w₂)
    (hAvoidP₂ :
      let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
      Disjoint V(P₂) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w₂}))
    (hP₂D : V(P₂) ∩ V(D) = {d₂.val}) :
    False := by exact GraphMinor.GM01.theorem_4_14_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths hDInter d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL hfirst q hq w₂ hw₂ d₂ P₂ hP₂ hAvoidP₂ hP₂D

end

/-! ## Section 5. PART 3: THE REDUCTION OF $P(\gamma, \delta)$ WHEN $\gamma \ge 1$ -/

section

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- Graph Minors I, (5.1), pages 60–61:
"If $X_0$ does not contain any vertex of $C$, then $C$ has path-width $\le p(\gamma, \delta - 1)$."

The root support is the actual binary subdivision and its separate root
path. The component root is chosen by the proved clean joining-path and
half-contraction argument, then the closed length bound is applied. -/
theorem theorem_5_1 {α β : Type*} {γ δ n : ℕ} (lam : ℕ) (hodd : Odd lam)
    (hγ : 0 < γ) (hγlam : γ ≤ lam) (hδ : 3 ≤ δ)
    (G : RootedGraph α β) (hVfin : V(G.graph).Finite) (hEfin : E(G.graph).Finite)
    (hConn : GraphConnected G.graph) (hGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph)
    (hNo : ¬ HasRootedMinor (rootedPathComb γ δ (by omega)) G)
    (F : RootedForestFamily G γ n) {N R : Graph α β} (hNG : N ≤ G.graph)
    (c : (binaryTree γ).verts → α) (P : (binaryTree γ).coe.edgeSet → Graph α β)
    (hV : V(N) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (binaryTree γ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (binaryTree γ).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b))
    (hR : IsGraphPathWithEnds G.graph R G.root.val (c (binaryRootedTree γ).root))
    (hRootSet : F.rootSet = V(N) ∪ V(R)) (X : Set α) (a : V(G.graph.deleteVerts X))
    (hDis : Disjoint F.rootSet (componentVertices (G.graph.deleteVerts X) a)) :
    HasPathWidthLE ((G.graph.deleteVerts X).induce (componentVertices (G.graph.deleteVerts X) a))
      (pathWidthBound lam γ (δ - 1)) := by exact GraphMinor.GM01.theorem_5_1_proof lam hodd hγ hγlam hδ G hVfin hEfin hConn hGrid hNo F hNG c P hV hPaths hR hRootSet X a hDis

end

section

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- Graph Minors I, (5.2), page 61:
"If $X_0$ contains a vertex of $C$, then $C$ has path-width at most $q(\gamma, 3\Omega + 6)$."

The actual cut and maximal family give the geometric fork exclusion by
packing and replacement. The closed current-height fork bound is then
applied at the constructed component root. -/
theorem theorem_5_2 {α β : Type*} {γ n Ω : ℕ} (lam : ℕ) (hodd : Odd lam)
    (hγ : 0 < γ) (hγlam : γ ≤ lam) (G : RootedGraph α β)
    (hVfin : V(G.graph).Finite) (hEfin : E(G.graph).Finite)
    (hGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph)
    (F : RootedForestFamily G γ n) (hMax : ∀ k, RootedForestFamily G γ k → k ≤ n)
    {N R : Graph α β} (hNG : N ≤ G.graph) (c : (binaryTree γ).verts → α)
    (P : (binaryTree γ).coe.edgeSet → Graph α β)
    (hV : V(N) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (binaryTree γ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (binaryTree γ).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b))
    (hR : IsGraphPathWithEnds G.graph R G.root.val (c (binaryRootedTree γ).root))
    (hRootSet : F.rootSet = V(N) ∪ V(R)) (X : Set α) (J : Set (Fin n))
    (hSize : X.ncard + J.ncard ≤ Ω)
    (hSep : ∀ j ∉ J, GraphSeparates G.graph X F.rootSet (F.otherSet j))
    (a : V(G.graph.deleteVerts X))
    (hMeet : (componentVertices (G.graph.deleteVerts X) a ∩ F.rootSet).Nonempty) :
    HasPathWidthLE ((G.graph.deleteVerts X).induce (componentVertices (G.graph.deleteVerts X) a))
      (forkWidthBound lam γ (3 * Ω + 6)) := by exact GraphMinor.GM01.theorem_5_2_proof lam hodd hγ hγlam G hVfin hEfin hGrid F hMax hNG c P hV hPaths hR hRootSet X J hSize hSep a hMeet

end

end GraphMinor.GM01
