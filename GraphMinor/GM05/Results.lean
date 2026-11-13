module

public import GraphMinor.GM05.OpenDiscCounterexample

public import GraphMinor.Compute.GM13ClassRecognition
public import GraphMinor.GM05.ChordalDefs
public import GraphMinor.GM05.CircuitPackingDefs
public import GraphMinor.GM05.ConnectedTransfer
public import GraphMinor.GM05.Defs
public import GraphMinor.GM05.EdgeTransfer
public import GraphMinor.GM05.ForestDecomposition
public import GraphMinor.GM05.FullSection5
public import GraphMinor.GM05.FullSection6
public import GraphMinor.GM05.FullTreeWidth
public import GraphMinor.GM05.FullWebDefs
public import GraphMinor.GM05.FullWebIteration
public import GraphMinor.GM05.FullWebSpider
public import GraphMinor.GM05.GenusListOrder
public import GraphMinor.GM05.GridLines
public import GraphMinor.GM05.PathTransfer
public import GraphMinor.GM05.Planar
public import GraphMinor.GM05.Quoted
public import GraphMinor.GM05.Section3
public import GraphMinor.GM05.Section4
public import GraphMinor.GM05.Section4Bipartite
public import GraphMinor.GM05.Section5
public import GraphMinor.GM05.Section6
public import GraphMinor.GM05.Section7
public import GraphMinor.GM05.SeriesParallelDefs
public import GraphMinor.GM05.Statements
public import GraphMinor.GM05.SurfaceDescent
public import GraphMinor.GM05.SurfaceGenus
public import GraphMinor.GM19.Defs2
public import GraphMinor.Minor.Basic
public import GraphMinor.Planar.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Compute.GM05MinorTest
import GraphMinor.GM05.Characterization
import GraphMinor.GM05.Chordal
import GraphMinor.GM05.CircleCut
import GraphMinor.GM05.CircuitPacking
import GraphMinor.GM05.ErdosPosaNonplanar
import GraphMinor.GM05.ErdosPosaPlanar
import GraphMinor.GM05.FullBipartite
import GraphMinor.GM05.FullLeafPath
import GraphMinor.GM05.FullPlanar
import GraphMinor.GM05.FullSection3
import GraphMinor.GM05.FullSection7
import GraphMinor.GM05.FullSeparatingPaths
import GraphMinor.GM05.FullWebExclusion
import GraphMinor.GM05.GridWidth
import GraphMinor.GM05.IndependentSelection
import GraphMinor.GM05.IntroductionMesh
import GraphMinor.GM05.MinimalSurfaceIntersection
import GraphMinor.GM05.MinimalSurfaceRegions
import GraphMinor.GM05.MinorWidth
import GraphMinor.GM05.OpenDiscContainment
import GraphMinor.GM05.Sequence
import GraphMinor.GM05.SeriesParallel
import GraphMinor.GM05.Simplicial
import GraphMinor.GM05.SubtreeSelection
import GraphMinor.GM05.SubtreeTransversal
import GraphMinor.GM05.WidthOne

/-!
# Graph Minors V. Excluding a planar graph

N. Robertson and P. D. Seymour, J. Combin. Theory Ser. B 41 (1986) 92–114.

This file lists every numbered result of the paper in order. The proofs are in the other
files of this folder and, for algorithms, in `GraphMinor/Compute/`. Where a printed statement
or proof has an error, the docstring says so and refers to `corrections/GM05.md`.
-/

public section

namespace GraphMinor.GM05

/-! ## Section 1. INTRODUCTION -/

section

open SimpleGraph Set

/-- Graph Minors V, (1.1), page 93:
"The simple graphs of tree-width $\le 1$ are precisely the forests."
The two directions respectively prune the decomposition tree and delete
vertices with at most one neighbour from the forest.

The statement concerns simple graphs, and width uses vertex bags. Loops and parallel edges do
not change the width. -/
theorem theorem_1_1 {V : Type*}
    {G : (⊤ : SimpleGraph V).Subgraph} (hfin : G.verts.Finite) :
    TreeWidthLE G 1 ↔ G.coe.IsAcyclic := by exact GraphMinor.GM05.theorem_1_1_proof hfin

end

section

open SimpleGraph Set

/-- Graph Minors V, (1.2), page 93:
"The graphs of tree-width $\le 2$ are precisely the series-parallel graphs."
Vertex bags see the same ends in the simple shadow as in the multigraph.
The proof suppresses vertices supplied by leaf bags and reverses those
reductions by attaching bags with at most three vertices.

The paper does not define series-parallel graphs. The Lean definition uses the reductions of
R. J. Duffin (J. Math. Anal. Appl. 10 (1965), Section 4) applied to the simple shadow. -/
theorem theorem_1_2 {α β : Type*} (G : Graph α β)
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
    TreeWidthLE (simpleShadow G) 2 ↔ IsSeriesParallel G := by exact GraphMinor.GM05.theorem_1_2_proof G hV hE

end

section

open SimpleGraph Set Graph Relation

/-- Graph Minors V, (1.3), page 93:
"If $H$ is a minor of $G$ then the tree-width of $H$ is no greater than the tree-width of $G$."
A minor model transfers bags without increasing their sizes.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_1_3 {α β α' β' : Type*}
    {H : Graph α' β'} {G : Graph α β}
    (hVH : V(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hminor : IsIsoMinor H G) :
    treeWidth (simpleShadow H) ≤ treeWidth (simpleShadow G) := by exact GraphMinor.GM05.theorem_1_3_proof hVH hVG hEG hminor

end

section

open SimpleGraph Set

/-- Graph Minors V, (1.4), page 93:
"For $n \ge 1$, the complete graph $K_n$ has tree-width $n - 1$, and for $\theta \ge 2$ the $\theta$-grid has tree-width $\theta$."
The lower bounds force a large bag, and explicit decompositions give the
matching upper bounds.

The width convention bounds bag sizes by `w + 1` in the natural numbers, which avoids
subtraction on empty bags. -/
theorem theorem_1_4 {n θ : ℕ} (hn : 1 ≤ n) (hθ : 2 ≤ θ) :
    treeWidth (SimpleGraph.toSubgraph (⊤ : SimpleGraph (Fin n)) le_top) = n - 1 ∧
      treeWidth (squareGrid θ) = θ := by exact GraphMinor.GM05.theorem_1_4_proof hn hθ

end

section

open Graph

/-- **Graph Minors V, (1.5)** (page 93):
"For every planar graph $H$, there is a number $w$ such that every planar graph with no minor isomorphic to $H$ has tree-width $\le w$."

Graph Minors V, (1.5), page 93, for arbitrary finite hosts.
For every planar graph `H`, excluding `H` bounds tree-width.
`GM05.theorem_1_5_simple` is the simple-host version. As in (2.1), the bound here
also applies to nonplanar hosts.

The bound applies to every finite host graph, as in the paper’s later uses. See the correction to
(1.5) in `corrections/GM05.md`. -/
theorem theorem_1_5 {α β α' β' : Type*}
    (H : Graph α' β') (hH : IsPlanar H) :
    ∃ w : ℕ, ∀ (G : Graph α β), V(G).Finite → E(G).Finite →
      ¬ IsIsoMinor H G → Full.TreeWidthLE G w := by exact GraphMinor.GM05.Full.theorem_1_5_proof H hH

end

section

open SimpleGraph Set GM01

universe u v

/-- Graph Minors V, (1.6), page 93:
"For any positive integer $\theta$ there exists an integer $\theta'$ such that if $G$ has subgraphs $H$ and $K$, each with $\ge \theta'$ components, and if each component of $H$ meets each component of $K$, then $G$ contains a $\theta$-grid minor."

Components are represented by their vertex sets in the simple shadow.
`graphConnected_iff_simpleShadow_connected` proves that these are the same
connected pieces. The simple shadow is a minor of the original multigraph,
so the mesh argument transfers without changing the requested grid. -/
theorem theorem_1_6 {θ : ℕ} (hθ : 0 < θ) :
    ∃ θ' : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β),
      G.vertexSet.Finite → G.edgeSet.Finite → ∀ {H K : Graph α β},
      H ≤ G → K ≤ G → θ' ≤ numComponents (simpleShadow H) →
      θ' ≤ numComponents (simpleShadow K) →
      (∀ C D, IsComponentOf C (simpleShadow H) → IsComponentOf D (simpleShadow K) →
        (C.verts ∩ D.verts).Nonempty) →
      IsIsoMinor (gridGraph θ) G := by exact GraphMinor.GM05.theorem_1_6_proof hθ

end

section

open Graph

/-- Graph Minors V, (1.7), page 93:
"If $G_1, G_2, \ldots$ is a countable sequence of graphs and $G_1$ is planar, then there exist $i, j$ with $j > i$ such that $G_i$ is isomorphic to a minor of $G_j$."

The sequence is indexed from zero. The proof is IV's: either a later graph
contains the first one as a minor, or IV (1.4) applies to the later graphs. -/
theorem theorem_1_7 {α β : Type*} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite)
    (hPlanar : IsPlanar (G 0)) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by exact GraphMinor.GM05.theorem_1_7_proof G hV hE hPlanar

end

section

open Graph Set Classical
open GraphMinor.Compute

/-- Graph Minors V, (1.8), page 94:
"If $H$ is any fixed planar graph, there is a polynomial time algorithm to test if an arbitrary graph has a minor isomorphic to $H$."

V cites this from II, and the proof is II (1.1). The input is the multigraph
encoding `x.G.enc`. Output zero means that `H` is a minor, and output one
means that it is not. The time is polynomial in `(x.n + 1)²`. -/
theorem algorithm_1_8 (H : Graph ℕ (ℕ × ℕ × ℕ))
    (hV : V(H).Finite) (hE : E(H).Finite) (hPlanar : IsPlanar H) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg =
          if IsIsoMinor H x.G.toGMDigraph.toGraph then 0 else 1)
        P (fun n => (n + 1) ^ c) := by exact GraphMinor.Compute.gm05_algorithm_1_8 H hV hE hPlanar

end

/-! ## Section 2. THE MAIN RESULT -/

section

open Graph

/-- Graph Minors V, (2.1), page 95, for arbitrary finite hosts:
"If $H$ is a planar graph, then every graph with no minor isomorphic to $H$ has tree-width at most $\theta_9(\theta(H))$."

`GM05.theorem_2_1_simple` is the simple-host version. This numbered version permits
loops and parallel edges in both the host and the excluded graph.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_2_1 {α β α' β' : Type*}
    {H : Graph α' β'} (hH : IsPlanar H) {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) (hno : ¬ IsIsoMinor H G) :
    Full.TreeWidthLE G (θ₉ (θOf H)) := by exact GraphMinor.GM05.Full.theorem_2_1_proof hH hV hE hno

end

/-! ## Section 3. GRIDS -/

section

open Graph GM01

/-- **Graph Minors V, (3.1)** (page 95):
"Let $B_1, \ldots, B_n$ be disjoint connected subgraphs of $G \in \mathscr{F}_\theta$, and let $V' \subseteq V(G)$. Let $r \ge 0$ be an integer. Then at least one of the following is true:"

Graph Minors V, (3.1), page 95, for hosts with loops and parallel edges.
Link selected disjoint connected subgraphs to a prescribed vertex set, or
separate almost all of them with a bounded vertex set.
`GM05.theorem_3_1_simple` is the simple-host version.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_3_1 {α β : Type*}
    {G : Graph α β} {θ n : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G)
    (B : Fin n → Graph α β) (hle : ∀ j, B j ≤ G)
    (hc : ∀ j, GraphConnected (B j))
    (hd : Pairwise fun i j => Disjoint V(B i) V(B j))
    (V' : Set α) (hV' : V' ⊆ V(G)) (r : ℕ) :
    (∃ (J : Finset (Fin n)) (P : J → GM01.Path α), J.card = r ∧
      (∀ j : J, Full.PathFromTo (P j) G V(B j.1) V') ∧
      Pairwise (fun i j : J => Disjoint (P i).verts (P j).verts) ∧
      ∀ j : J, Disjoint (P j).internalVerts (V' ∪ ⋃ j' ∈ J, V(B j'))) ∨
    (∃ (X : Set α) (J : Finset (Fin n)), X ⊆ V(G) ∧
      X.ncard + J.card ≤ 2 ^ (r * θ ^ 4) ∧
      ∀ j : Fin n, j ∉ J → Full.Separates G X V' V(B j)) := by exact GraphMinor.GM05.Full.theorem_3_1_proof hθ heven hV hE hno B hle hc hd V' hV' r

end

section

open Graph GM01

/-- **Graph Minors V, (3.2)** (page 96):
"Let $G \in \mathcal{F}_\theta$, and let $V_1, \dots, V_k \subseteq V(G)$, where $k \ge 2$. Let $n \ge 0$ be an integer. Then at least one of the following is true:"

Graph Minors V, (3.2), pages 95–96, for hosts with loops and parallel edges.
Either `n` disjoint connected subgraphs meet every prescribed set, or fewer
than `α θ k n` vertices meet every such connected subgraph.
`GM05.theorem_3_2_simple` is the simple-host version.
The multigraph form is transferred from the simple-graph version through the simple shadow. -/
theorem theorem_3_2 {α β : Type*}
    {G : Graph α β} {θ k n : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) (hk : 2 ≤ k)
    (S : Fin k → Set α) (hS : ∀ i, S i ⊆ V(G)) :
    (∃ B : Fin n → Graph α β,
      (∀ j, B j ≤ G) ∧ (∀ j, GraphConnected (B j)) ∧
      Pairwise (fun i j => Disjoint V(B i) V(B j)) ∧
      ∀ i j, (V(B j) ∩ S i).Nonempty) ∨
    (∃ X ⊆ V(G), X.ncard < GM05.α θ k n ∧
      ∀ B : Graph α β, B ≤ G → GraphConnected B →
        (∀ i, (V(B) ∩ S i).Nonempty) → (V(B) ∩ X).Nonempty) := by exact GraphMinor.GM05.Full.theorem_3_2_proof hθ heven hV hE hno hk S hS

end

/-! ## Section 4. GRIDS AND WEBS -/

section

open Graph GM01

/-- **Graph Minors V, (4.1)** (page 97):
"Let $G \in \mathcal{F}_\theta$. Let $A_1, \dots, A_m, B_1, \dots, B_n$ be disjoint connected subgraphs of $G$ such that for $1 \le i \le m$, $1 \le j \le n$ there is a vertex of $A_i$ and a vertex of $B_j$ which are adjacent in $G$. Then either $m < \theta^2/2$ or $n < \theta^2/2$."

Graph Minors V, (4.1), page 97, for hosts with loops and parallel edges.
A grid-excluding graph cannot contain the indicated large complete bipartite
configuration. `GM05.theorem_4_1_simple` is the simple-host version.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_4_1 {α β : Type*}
    {G : Graph α β} {θ m n : ℕ}
    (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G)
    (A : Fin m → Graph α β) (B : Fin n → Graph α β)
    (hA : ∀ i, A i ≤ G) (hB : ∀ j, B j ≤ G)
    (hcA : ∀ i, GraphConnected (A i)) (hcB : ∀ j, GraphConnected (B j))
    (hdA : Pairwise fun i j => Disjoint V(A i) V(A j))
    (hdB : Pairwise fun i j => Disjoint V(B i) V(B j))
    (hdAB : ∀ i j, Disjoint V(A i) V(B j))
    (hadj : ∀ i j, ∃ x ∈ V(A i), ∃ y ∈ V(B j), G.Adj x y) :
    m < θ ^ 2 / 2 ∨ n < θ ^ 2 / 2 := by exact GraphMinor.GM05.Full.theorem_4_1_proof heven hV hE hno A B hA hB hcA hcB hdA hdB hdAB hadj

end

section

open Graph GM01

/-- **Graph Minors V, (4.2)** (page 97):
"Let $A_1, \dots, A_{\theta^2/2}$ be disjoint connected subgraphs of $G \in \mathcal{F}_\theta$, and let $B_1, \dots, B_n$ be pairwise edge-disjoint connected subgraphs of $G$. Suppose that for $1 \le i \le \theta^2/2$, $1 \le j \le n$ there is a unique vertex $v_{ij}$ in $V(A_i) \cap V(B_j)$, and it has valency 1 in $B_j$. Suppose in addition that all vertices of $G$ have valency $\le 4$. Then $n < \theta_1$, where $\theta_1$ is as defined in Section 2."

Graph Minors V, (4.2), page 97, for hosts with loops and parallel edges.
The connected subgraphs `B j` use disjoint actual edge sets, their prescribed
intersection vertices have actual valency one, and the host has maximum
valency four. The conclusion is the printed bound `n < θ₁ θ`.
`GM05.theorem_4_2_simple` is the simple-host version. The proof uses the same
counting argument, with incident edges paying for shadow neighbor counts.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_4_2 {α β : Type*}
    {G : Graph α β} {θ n : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G)
    (A : Fin (θ ^ 2 / 2) → Graph α β) (B : Fin n → Graph α β)
    (hA : ∀ i, A i ≤ G) (hcA : ∀ i, GraphConnected (A i))
    (hdA : Pairwise fun i j => Disjoint V(A i) V(A j))
    (hB : ∀ j, B j ≤ G) (hcB : ∀ j, GraphConnected (B j))
    (hdB : Pairwise fun i j => Disjoint E(B i) E(B j))
    (hAB : ∀ i j, ∃ x, V(A i) ∩ V(B j) = {x} ∧ Full.IsLeafOf (B j) x)
    (hdeg : ∀ x ∈ V(G), Full.valency G x ≤ 4) : n < θ₁ θ := by exact GraphMinor.GM05.Full.theorem_4_2_proof hθ heven hV hE hno A B hA hcA hdA hB hcB hdB hAB hdeg

end

section

open Graph GM01

/-- **Graph Minors V, (4.3)** (page 98):
"Let $A_1, A_2 \subseteq V(G)$, where $G \in \mathcal{F}_\theta$, and let $D_1, \dots, D_m$ be disjoint subgraphs of $G$, each with at most $d$ components. Suppose that there are $n$ disjoint paths in $G$ from $A_1$ to $A_2$, and for $1 \le k \le m$, $D_k$ separates $A_1$ and $A_2$. Then either $n < d\theta^2/2$ or $m < 2^{d\theta^2/2}(\theta^2 + 2d\theta^{2\theta})$."

Graph Minors V, (4.3), page 98, for hosts with loops and parallel edges,
with the same correction `0 < d + n` as the simple-host version
`GM05.theorem_4_3_simple`. Bound a disjoint family of separators of disjoint paths.

The extra positivity hypothesis excludes the false empty case. See the correction to (4.3) in
`corrections/GM05.md`. -/
theorem theorem_4_3 {α β : Type*}
    {G : Graph α β} {θ m n d : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hpos : 0 < d + n)
    (hV : V(G).Finite) (hE : E(G).Finite) (hno : ¬ IsIsoMinor (gridGraph θ) G)
    (A B : Set α) (hA : A ⊆ V(G)) (hB : B ⊆ V(G))
    (D : Fin m → Graph α β) (hle : ∀ i, D i ≤ G)
    (hd : Pairwise fun i j => Disjoint V(D i) V(D j))
    (hcomp : ∀ i, numComponents (simpleShadow (D i)) ≤ d)
    (hpaths : ∃ P : Fin n → GM01.Path α,
      (∀ i, Full.PathFromTo (P i) G A B) ∧
      Pairwise (fun i j => Disjoint (P i).verts (P j).verts))
    (hsep : ∀ i, Full.Separates G V(D i) A B) :
    n < d * θ ^ 2 / 2 ∨ m < 2 ^ (d * θ ^ 2 / 2) * (θ ^ 2 + 2 * d * θ ^ (2 * θ)) := by exact GraphMinor.GM05.Full.theorem_4_3_proof hθ heven hpos hV hE hno A B hA hB D hle hd hcomp hpaths hsep

end

section

open Graph Set SimpleGraph GM01

/-- **Graph Minors V, (4.4)** (page 98):
"Let $G \in \mathcal{F}_\theta$, and let $p, q \ge 0$ be integers. Let $m = p 2^{p\theta^2}$, $n = p + q + m$. Suppose that $((A_1, \dots, A_m), (B_1, \dots, B_n))$ is an ($m, n$)-web in $G$. Then there exists $I \subseteq \{1, \dots, m\}$, $J \subseteq \{1, \dots, n\}$ such that $|I| = p$, $|J| = q$, and $((A_i \colon i \in I), (B_j \colon j \in J))$ is a ($p, q$)-web with a spider."

Graph Minors V, (4.4), pages 98–99, for paths with actual multigraph edges.
Select a `(p,q)`-subweb with a spider. The same correction `0 < p` as in
`GM05.theorem_4_4_simple` excludes the empty-host counterexample.

The first subweb parameter is positive, excluding the null graph counterexample. See the
correction to (4.4) in `corrections/GM05.md`. -/
theorem theorem_4_4 {α β : Type*}
    {G : Graph α β} {θ p q : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) (hp : 0 < p)
    {A : Fin (p * 2 ^ (p * θ ^ 2)) → Full.Path α β}
    {B : Fin (p + q + p * 2 ^ (p * θ ^ 2)) → Full.Path α β} (hw : Full.IsWeb G A B) :
    ∃ (embI : Fin p ↪ Fin (p * 2 ^ (p * θ ^ 2)))
      (embJ : Fin q ↪ Fin (p + q + p * 2 ^ (p * θ ^ 2))) (K : Graph α β),
      Full.IsSpider G (fun i => A (embI i)) (fun j => B (embJ j)) K := by exact GraphMinor.GM05.Full.theorem_4_4_proof hθ heven hV hE hno hp hw

end

section

open Graph Set SimpleGraph GM01

/-- **Graph Minors V, (4.5)** (page 99):
"For $0 \le k < \theta_2$, if $G \in \mathcal{F}_\theta$ has a ($\phi_k, \psi_k$)-web with $k$ edge-disjoint spiders, then it has a ($\phi_{k+1}, \psi_{k+1}$)-web with $k + 1$ edge-disjoint spiders."

Graph Minors V, (4.5), page 99, with actual edge-disjoint spiders.
The same correction of the printed index `k < θ₁ θ` as in `GM05.theorem_4_5_simple` is used.
Delete the old spider edges, apply full (4.4), and restore the old spiders.

The index bound uses the first web threshold, correcting the printed subscript. See the
correction to (4.5) in `corrections/GM05.md`. -/
theorem theorem_4_5 {α β : Type*}
    {G : Graph α β} {θ k : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) (hk : k < θ₁ θ)
    (h : Full.HasWebWithSpiders G (φ θ k) (ψ θ k) k) :
    Full.HasWebWithSpiders G (φ θ (k + 1)) (ψ θ (k + 1)) (k + 1) := by exact GraphMinor.GM05.Full.theorem_4_5_proof hθ heven hV hE hno hk h

end

section

open Graph Set SimpleGraph GM01

/-- **Graph Minors V, (4.6)** (page 100):
"If $G \in \mathcal{F}_\theta$ then $G$ has no $(\theta_2, \theta_2)$-web."

Graph Minors V, (4.6), page 100, for hosts with loops and parallel edges.
There is no `(θ₂ θ, θ₂ θ)`-web using actual disjoint edges in a graph
excluding the grid. `GM05.theorem_4_6_simple` is the simple-host version.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_4_6 {α β : Type*}
    {G : Graph α β} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) : ¬ Full.HasWeb G (θ₂ θ) (θ₂ θ) := by exact GraphMinor.GM05.Full.theorem_4_6_proof hθ heven hV hE hno

end

/-! ## Section 5. Webs and Meshes -/

section

open Graph Set GM01

/-- **Graph Minors V, (5.1)** (page 100):
"Let $v$ be a vertex of a connected graph $G$, and let $p, q \ge 0$ be integers. Let $V_1, ..., V_{p^q} \subseteq V(G)$ be disjoint and non-empty, with $v \in V_1 \cup \dots \cup V_{p^q}$. Then at least one of the following holds:"

Graph Minors V, (5.1), pages 100–101, for hosts with loops and parallel edges.
Find the rooted connected configuration with actual valency-one leaves, or
an actual path starting at the root and meeting exactly `q + 1` sets.
`GM05.theorem_5_1_simple` is the simple-host version. Its correction `2 ≤ p`
is retained.

The branching parameter is at least two, excluding the singleton counterexample. See the
correction to (5.1) in `corrections/GM05.md`. -/
theorem theorem_5_1 {α β : Type*}
    {G : Graph α β} (hV : V(G).Finite) (hc : GraphConnected G)
    {v : α} {p q : ℕ} (hp : 2 ≤ p) (S : Fin (p ^ q) → Set α)
    (hS : ∀ j, S j ⊆ V(G)) (hd : Pairwise fun i j => Disjoint (S i) (S j))
    (hne : ∀ j, (S j).Nonempty) (hv : ∃ j, v ∈ S j) :
    (∃ (C : Graph α β) (emb : Fin p ↪ Fin (p ^ q)) (leaf : Fin p → α),
      C ≤ G ∧ GraphConnected C ∧ v ∈ V(C) ∧
      ∀ i, leaf i ≠ v ∧ Full.IsLeafOf C (leaf i) ∧ S (emb i) ∩ V(C) = {leaf i}) ∨
    (∃ P : Full.Path α β, P.IsIn G ∧ P.seq.first = v ∧
      (metIndices S P.verts).card = q + 1) := by exact GraphMinor.GM05.Full.theorem_5_1_proof hV hc hp S hS hd hne hv

end

section

open Graph GM01

/-- **Graph Minors V, (5.2)** (page 101):
"Let $G \in \mathcal{F}_\theta$, and let $p, q \ge 2$ be integers. Let $n = (\theta^2/2)^{q-1}$, $m = p \binom{n}{q} + \frac{1}{2}\theta^2 \binom{n}{\theta^2/2}$. Suppose that $((A_1, ..., A_m), (B_1, ..., B_n))$ is an $(m, n)$-mesh in $G$. Then there exists $I \subseteq \{1, ..., m\}$ and $J \subseteq \{1, ..., n\}$ with $|I| = p$, $|J| = q$, and for each $i \in I$ a path $P_i$ of $A_i$, such that $((P_i : i \in I), (B_j : j \in J))$ is a $(p, q)$-mesh."

Graph Minors V, (5.2), page 101, for hosts with loops and parallel edges.
Select `p` branch paths and `q` members of the other family to obtain a
smaller mesh. The path conditions specify the mesh by its vertex sets.
`GM05.theorem_5_2_simple` is the simple-host version.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_5_2 {α β : Type*}
    {G : Graph α β} {θ p q : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) (hp : 2 ≤ p) (hq : 2 ≤ q)
    {A : Fin (p * ((θ ^ 2 / 2) ^ (q - 1)).choose q +
      (θ ^ 2 / 2) * ((θ ^ 2 / 2) ^ (q - 1)).choose (θ ^ 2 / 2)) → Graph α β}
    {B : Fin ((θ ^ 2 / 2) ^ (q - 1)) → Graph α β} (hm : Full.IsMesh G A B) :
    ∃ (embI : Fin p ↪ Fin (p * ((θ ^ 2 / 2) ^ (q - 1)).choose q +
        (θ ^ 2 / 2) * ((θ ^ 2 / 2) ^ (q - 1)).choose (θ ^ 2 / 2)))
      (embJ : Fin q ↪ Fin ((θ ^ 2 / 2) ^ (q - 1))) (P : Fin p → GM01.Path α),
      (∀ i, Full.PathIsIn (P i) (A (embI i))) ∧
      Pairwise (fun i j => Disjoint (P i).verts (P j).verts) ∧
      (∀ j, B (embJ j) ≤ G ∧ GraphConnected (B (embJ j))) ∧
      Pairwise (fun i j => Disjoint V(B (embJ i)) V(B (embJ j))) ∧
      ∀ i j, ((P i).verts ∩ V(B (embJ j))).Nonempty := by exact GraphMinor.GM05.Full.theorem_5_2_proof hθ heven hV hE hno hp hq hm

end

section

open Graph GM01

/-- **Graph Minors V, (5.3)** (page 102):
"If $G \in \mathcal{F}_\theta$ then $G$ has no $(\theta_5, \theta_6)$-mesh."

Graph Minors V, (5.3), page 102, for hosts with loops and parallel edges.
A grid-excluding graph has no mesh of the specified size.
`GM05.theorem_5_3_simple` is the simple-host version.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_5_3 {α β : Type*}
    {G : Graph α β} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) :
    ¬ ∃ (A : Fin (θ₅ θ) → Graph α β) (B : Fin (θ₆ θ) → Graph α β), Full.IsMesh G A B := by exact GraphMinor.GM05.Full.theorem_5_3_proof hθ heven hV hE hno

end

/-! ## Section 6. Large Subgraphs and Small Separations -/

section

open Graph

/-- **Graph Minors V, (6.1)** (page 103):
"If $G$ is a 2-connected graph with $n$ vertices, we may enumerate its vertices as $v_1, ..., v_n$ in such a way that for $0 \le i \le n$, $G|\{v_1, ..., v_i\}$, $G|\{v_{i+1}, ..., v_n\}$ are both connected."

Graph Minors V, (6.1), page 103, for hosts with loops and parallel edges.
Enumerate a 2-connected graph with connected prefixes and suffixes, allowing
the empty prefix or suffix. Two-connectivity uses the shadow, since it is
unchanged by loops and parallel edges. `GM05.theorem_6_1_simple` is the simple-host version.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_6_1 {α β : Type*}
    {G : Graph α β} (hV : V(G).Finite)
    (h2 : GM05.IsTwoConnected (simpleShadow G)) :
    ∃ v : Fin V(G).ncard → α, Function.Injective v ∧ Set.range v = V(G) ∧
      ∀ i : ℕ, i ≤ V(G).ncard →
        GraphPreconnected (G.induce {x | ∃ j : Fin V(G).ncard, j.1 < i ∧ v j = x}) ∧
        GraphPreconnected (G.induce {x | ∃ j : Fin V(G).ncard, i ≤ j.1 ∧ v j = x}) := by exact GraphMinor.GM05.Full.theorem_6_1_proof hV h2

end

section

open Graph

/-- **Graph Minors V, (6.2)** (page 103):
"Let $G$ be a connected graph, let $w \colon V(G) \to \mathbf{Z}^+$ be some function, and let $k > 0$ be an integer with $k \le (w(V(G)) + 2)/3$. Then exactly one of the following is true:"

Graph Minors V, (6.2), page 103, for hosts with loops and parallel edges.
Exactly one of a heavy connected split and a vertex hitting all heavy
components exists. Components use the shadow representation of (1.6).
`GM05.theorem_6_2_simple` is the simple-host version.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_6_2 {α β : Type*}
    {G : Graph α β} (hV : V(G).Finite)
    (hc : GraphConnected G) (w : α → ℕ) {k : ℕ} (hk : 0 < k)
    (hbound : k ≤ (weightSum w V(G) + 2) / 3) :
    (Full.Cond62_i G w k ∨ GM05.Cond62_ii (simpleShadow G) w k) ∧
      ¬ (Full.Cond62_i G w k ∧ GM05.Cond62_ii (simpleShadow G) w k) := by exact GraphMinor.GM05.Full.theorem_6_2_proof hV hc w hk hbound

end

section

open Graph

/-- **Graph Minors V, (6.3)** (page 104):
"Let $G$ be a connected graph, and let $k>0$ be an integer. Then at least one of the following is true:"

Graph Minors V, (6.3), page 104, for hosts with loops and parallel edges.
Pack `k` large connected subgraphs or delete fewer than `k` vertices to leave
only small components. Components use the shadow representation of (1.6).
`GM05.theorem_6_3_simple` is the simple-host version.
The multigraph form is transferred from the simple-graph version through the simple shadow. -/
theorem theorem_6_3 {α β : Type*}
    {G : Graph α β} (hV : V(G).Finite)
    (hc : GraphConnected G) {k : ℕ} (hk : 0 < k) :
    (∃ B : Fin k → Graph α β,
      (∀ i, B i ≤ G ∧ GraphConnected (B i) ∧
        2 * V(G).ncard ≤ (3 ^ k - 1) * V(B i).ncard) ∧
      Pairwise (fun i j => Disjoint V(B i) V(B j))) ∨
    GM05.Cond63_ii (simpleShadow G) k := by exact GraphMinor.GM05.Full.theorem_6_3_proof hV hc hk

end

section

open Graph

/-- **Graph Minors V, (6.4)** (page 106):
"Let $G$ be a graph and let $k>0$ be an integer. Then at least one of the following holds:"

Graph Minors V, (6.4), page 106, for hosts with loops and parallel edges.
Pack `k` large connected subgraphs or find a small balanced separation.
`GM05.theorem_6_4_simple` is the simple-host version.
The multigraph form is transferred from the simple-graph version through the simple shadow. -/
theorem theorem_6_4 {α β : Type*}
    {G : Graph α β} (hV : V(G).Finite) {k : ℕ} (hk : 0 < k) :
    (∃ B : Fin k → Graph α β,
      (∀ i, B i ≤ G ∧ GraphConnected (B i) ∧
        4 * V(G).ncard ≤ 3 * (3 ^ k - 1) * V(B i).ncard) ∧
      Pairwise (fun i j => Disjoint V(B i) V(B j))) ∨
    (∃ A B : Set α, Full.IsSeparation G A B ∧ (A ∩ B).ncard < k ∧
      3 * (A \ B).ncard ≤ 2 * V(G).ncard ∧
      3 * (B \ A).ncard ≤ 2 * V(G).ncard) := by exact GraphMinor.GM05.Full.theorem_6_4_proof hV hk

end

/-! ## Section 7. Meshes and Tree-Width -/

section

open Graph GM01

/-- **Graph Minors V, (7.1)** (page 106):
"If $G\in \mathcal{F}_\theta$ then $G$ has a separation $(V_1, V_2)$ such that $|V_1\cap V_2|\le \theta_7$ and $|V_1 - V_2|, |V_2 - V_1|\le (1 - \theta_8^{-1})|V(G)|$, where $\theta_7, \theta_8$ are as defined in Section 2."

Graph Minors V, (7.1), page 106, for hosts with loops and parallel edges.
A graph excluding the grid has a small balanced vertex separation.
`GM05.theorem_7_1_simple` is the simple-host version.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_7_1 {α β : Type*}
    {G : Graph α β} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) :
    ∃ A B : Set α, Full.IsSeparation G A B ∧ (A ∩ B).ncard ≤ θ₇ θ ∧
      θ₈ θ * (A \ B).ncard ≤ (θ₈ θ - 1) * V(G).ncard ∧
      θ₈ θ * (B \ A).ncard ≤ (θ₈ θ - 1) * V(G).ncard := by exact GraphMinor.GM05.Full.theorem_7_1_proof hθ heven hV hE hno

end

section

open Graph GM01

/-- **Graph Minors V, (7.2)** (page 107):
"If $G\in \mathcal{F}_\theta$ and $X\subseteq V(G)$ then $G$ has a separation $(V_1, V_2)$ such that $|V_1\cap V_2|\le \theta_7$ and $|(V_1 - V_2)\cap X|, |(V_2 - V_1)\cap X|\le (1 - \theta_8^{-1})|X|$."

Graph Minors V, (7.2), page 107, for hosts with loops and parallel edges.
The separator balances any prescribed vertex set `X`.
`GM05.theorem_7_2_simple` is the simple-host version.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_7_2 {α β : Type*}
    {G : Graph α β} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) {X : Set α} (hX : X ⊆ V(G)) :
    ∃ A B : Set α, Full.IsSeparation G A B ∧ (A ∩ B).ncard ≤ θ₇ θ ∧
      θ₈ θ * ((A \ B) ∩ X).ncard ≤ (θ₈ θ - 1) * X.ncard ∧
      θ₈ θ * ((B \ A) ∩ X).ncard ≤ (θ₈ θ - 1) * X.ncard := by exact GraphMinor.GM05.Full.theorem_7_2_proof hθ heven hV hE hno hX

end

section

open Graph GM01

/-- **Graph Minors V, (7.3)** (page 108):
"If $G \in \mathcal{F}_\theta$ then $G$ has tree-width at most $\theta_9$."

Graph Minors V, (7.3), page 108, for hosts with loops and parallel edges.
Excluding the grid bounds tree-width by `θ₉ θ`.
`GM05.theorem_7_3_simple` is the simple-host version.

The statement uses general finite graphs. The proof transfers the simple-graph version through
the simple shadow, which has the same vertex bags and vertex separations. -/
theorem theorem_7_3 {α β : Type*}
    {G : Graph α β} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) : Full.TreeWidthLE G (θ₉ θ) := by exact GraphMinor.GM05.Full.theorem_7_3_proof hθ heven hV hE hno

end

/-! ## Section 8. A Generalization of the Erdös-Pósa Theorem -/

section

open Graph Set GM01 GM09

universe u v

/-- Graph Minors V, (8.1), page 109: "For any integer $k \ge 0$ there is an
integer $k' \ge 0$ such that for every graph $G$, at least one of the following is true:"
The alternatives are `k` disjoint circuits, or deletion of at most `k'`
vertices leaving no circuits. This proof derives the result from the
proved grid bound (7.3) and the subtree packing lemma.

The paper cites (8.1) from Erdős and Pósa without proof. Here it is derived from the proved grid
bound. -/
theorem theorem_8_1 (k : ℕ) : ∃ k' : ℕ,
    ∀ {α : Type u} {β : Type v} (G : Graph α β),
      V(G).Finite → E(G).Finite →
      HasDisjointCircuits G k ∨ ∃ X ⊆ V(G), X.ncard ≤ k' ∧
        ¬ ∃ C, IsGraphCircuit (deleteVertices G X) C := by exact GraphMinor.GM05.theorem_8_1_proof k

end

section

open Graph

universe u v u' v'

/-- Graph Minors V, (8.2), page 110:
"A graph has the Erdös-Pósa property if and only if it is planar."
This uses the proved (8.8) and (8.14), as in
the last sentence of their proof on page 113. -/
theorem theorem_8_2 {α' : Type u'} {β' : Type v'} (H : Graph α' β')
    (hV : V(H).Finite) (hE : E(H).Finite) :
    HasErdosPosaProperty.{u,v,u',v'} H ↔ IsPlanar H := by exact GraphMinor.GM05.theorem_8_2_proof H hV hE

end

section

open SimpleGraph Set

universe u

/-- Graph Minors V, (8.3), page 110:
"$G$ is a subtree intersection graph if and only if $G$ is chordal."
The reverse direction uses the later numbered result (8.4) to delete a
simplicial vertex. The forward direction is proved by deleting tree leaves. -/
theorem theorem_8_3 {V : Type u} [Finite V]
    (G : SimpleGraph V) : IsSubtreeIntersectionGraph G ↔ IsChordal G := by exact GraphMinor.GM05.theorem_8_3_proof G

end

section

open SimpleGraph Set

universe u

/-- Graph Minors V, (8.4), page 110:
"If $G$ is chordal and non-null then $G$ has a vertex $v$ such that the vertices adjacent to $v$ are pairwise adjacent."
The result is quoted from Dirac [3]; the proof here uses minimal clique
separators and induction, with the empty clique as the set to avoid. -/
theorem theorem_8_4 {V : Type u} [Finite V] [Nonempty V] (G : SimpleGraph V)
    (hG : IsChordal G) : ∃ v, IsSimplicial G v := by exact GraphMinor.GM05.theorem_8_4_proof G hG

end

section

open SimpleGraph Set
open scoped BigOperators

universe u

/-- **Graph Minors V, (8.5)** (page 110):
"Let $G$ be chordal, and let $Z_1, \dots, Z_m$ be independent subsets of $V(G)$, pairwise disjoint, and each with cardinality $k$. Let $x_1, \dots, x_m \ge 0$ be integers with $x_1 + \dots + x_m = k$. Then there exists an independent subset $X \subseteq V(G)$ with $|X \cap Z_i| = x_i$ $(1 \le i \le m)$."

Graph Minors V, (8.5), pages 110–111: disjoint independent sets of
cardinality `k` in a chordal graph have an independent selection with
prescribed intersection sizes whose sum is `k`. The proof is the paper's
simplicial-vertex induction. -/
theorem theorem_8_5 {V : Type u} [Finite V] {m k : ℕ} {G : SimpleGraph V}
    (hG : IsChordal G) (Z : Fin m → Set V) (hZ : ∀ i,G.IsIndepSet (Z i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (Z i) (Z j)))
    (hcard : ∀ i,(Z i).ncard=k) (x : Fin m → ℕ) (hsum : ∑ i,x i=k) :
    ∃ X : Set V, G.IsIndepSet X ∧ ∀ i,(X∩Z i).ncard=x i := by exact GraphMinor.GM05.theorem_8_5_proof hG Z hZ hdisj hcard x hsum

end

section

open SimpleGraph Set
open scoped BigOperators

/-- **Graph Minors V, (8.6)** (page 111):
"Let $T$ be a tree, and let $\mathcal{A}_1, \dots, \mathcal{A}_m$ be families of subtrees of $T$. Let $x_1, \dots, x_m \ge 0$ be integers, and let $x_1 + \dots + x_m = k$. Suppose that for $1 \le i \le m$, there are $k$ members of $\mathcal{A}_i$ which are pairwise vertex-disjoint. Then for $1 \le i \le m$ there are $x_i$ members $T_1^i, \dots, T_{x_i}^i$ of $\mathcal{A}_i$, such that
$$
T_1^1, \dots, T_{x_1}^1, T_1^2, \dots, T_{x_2}^2, \dots, T_1^m, \dots, T_{x_m}^m
$$
are all pairwise vertex-disjoint."

Graph Minors V, (8.6), page 111: if each of `m` families of subtrees
contains `k` disjoint members, one can select `x i` members of each family,
all disjoint together, whenever the targets sum to `k`. Subtrees are
represented by their nonempty connected vertex sets. The proof applies
(8.5) to the intersection graph, as in the paper. -/
theorem theorem_8_6 {ι : Type*} [Fintype ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {m k : ℕ} (A : Fin m → Set (Set ι))
    (hA : ∀ i S, S∈A i → (T.induce S).Connected)
    (x : Fin m → ℕ) (hsum : ∑ i,x i=k)
    (hpack : ∀ i, ∃ S : Fin k → Set ι, (∀ a,S a∈A i) ∧
      Pairwise (fun a b ↦ Disjoint (S a) (S b))) :
    ∃ B : (i : Fin m) → Fin (x i) → Set ι,
      (∀ i a, B i a∈A i) ∧
      Pairwise (fun a b : (i : Fin m) × Fin (x i) ↦ Disjoint (B a.1 a.2) (B b.1 b.2)) := by exact GraphMinor.GM05.theorem_8_6_proof hT A hA x hsum hpack

end

section

open SimpleGraph Set

/-- **Graph Minors V, (8.7)** (page 111):
"Let $T$ be a tree, and let $\mathcal{F}$ be a family of subtrees of $T$. Then for any integer $k \ge 0$, either there are $k$ pairwise vertex-disjoint members of $\mathcal{F}$, or there is a subset $X \subseteq V(T)$ with $|X| < k$ which has non-empty intersection with every member of $\mathcal{F}$."

Graph Minors V, (8.7), page 111: for any family of subtrees and any
natural `k`, either `k` members are pairwise vertex-disjoint, or fewer
than `k` tree vertices meet every member. The proof is direct leaf induction,
through `subtrees_pack_or_hit`. -/
theorem theorem_8_7 {ι : Type*} [Fintype ι] {T : SimpleGraph ι} (hT : T.IsTree)
    (F : Set (Set ι)) (hF : ∀ A∈F,(T.induce A).Connected) (k : ℕ) :
    (∃ A : Fin k → Set ι, (∀ i,A i∈F) ∧ Pairwise (fun i j ↦ Disjoint (A i) (A j))) ∨
      ∃ X : Set ι, X.ncard<k ∧ ∀ A∈F,(X∩A).Nonempty := by exact GraphMinor.GM05.theorem_8_7_proof hT F hF k

end

section

open Graph Set GM06

universe u v u' v'

/-- Graph Minors V, (8.8), page 111:
"If $H$ is planar then $H$ has the Erdös-Pósa property."
The proof follows the paper's component-family argument using the proved
(8.6) and (8.7).

The proof applies (1.5) to the graph of $k$ disjoint copies of $H$, which is planar since it is a
minor of a grid. -/
theorem theorem_8_8 {α' : Type u'} {β' : Type v'} {H : Graph α' β'}
    (hH : IsPlanar H) : HasErdosPosaProperty.{u,v,u',v'} H := by exact GraphMinor.GM05.theorem_8_8_proof hH

end

section

open Surface GM19

universe u v

/-- Graph Minors V, (8.9), page 112:
"There is no infinite sequence $\Sigma_1, \Sigma_2, \dots$ of orientable surfaces with $g(\Sigma_{i+1}) < g(\Sigma_i)$ ($i = 1, 2, \dots$)."
The proof uses well-foundedness of the multiset order on component genera. -/
theorem theorem_8_9 (S : ℕ → Type u) (τ : ∀ n,TopologicalSpace (S n))
    (hS : ∀ n,@IsClosedSurface (S n) (τ n))
    (_hO : ∀ n,@IsOrientableSurface (S n) (τ n)) :
    ¬∀ n,@SurfaceGenusLT (S (n+1)) (τ (n+1)) (S n) (τ n) (hS (n+1)) (hS n) := by exact GraphMinor.GM05.theorem_8_9_proof S τ hS _hO

end

section

open Set Topology Surface GM19

/-- Graph Minors V, (8.10), page 112:
"Let $\Sigma$ be an orientable surface, and let $C \subseteq \Sigma$ be homeomorphic to a circle. Then one of the following holds:"
"there is a closed disc $\Delta \subseteq \Sigma$ with $C = \text{bd } \Delta$;"
"there is an orientable surface $\Sigma'$ with $g(\Sigma') < g(\Sigma)$, and disjoint closed discs $\Delta_1, \Delta_2 \subseteq \Sigma'$, such that $\Sigma' - (\Delta_1 \cup \Delta_2) = \Sigma - C$."
The displayed identification of complements is formalized by its
homeomorphism, built from the cutting and capping maps. -/
theorem theorem_8_10 {S : Type} [TopologicalSpace S] (hS : IsClosedSurface S)
    (hO : IsOrientableSurface S) {C : Set S} (hC : IsOArc C) :
    (∃ D : Set S,IsClosedDisc D ∧ C=discBd D) ∨
    ∃ (T : Type) (_ : TopologicalSpace T) (hT : IsClosedSurface T),
      IsOrientableSurface T ∧ SurfaceGenusLT hT hS ∧
      ∃ D D' : Set T,IsClosedDisc D ∧ IsClosedDisc D' ∧ Disjoint D D' ∧
        Nonempty (↥((D ∪ D')ᶜ) ≃ₜ ↥(Cᶜ)) := by exact GraphMinor.GM05.theorem_8_10_proof hS hO hC

end

section

open Set Topology Surface

/- A counterexample to Graph Minors V, (8.11), page 113:
"If $r$ is a connected open subset of a surface $\Sigma$, and every subset of $r$ homeomorphic to a circle bounds a closed disc in $\Sigma$, then there is an open disc $\Delta \subseteq \Sigma$ with $r \subseteq \Delta$."
The sphere itself satisfies the hypotheses and fails the conclusion.
A corrected statement must exclude a whole spherical component. -/
example :
    IsClosedSurface (SurfaceModel 0 0 0) ∧
    ∃ r : Set (SurfaceModel 0 0 0),IsConnected r ∧ IsOpen r ∧
      (∀ C : Set (SurfaceModel 0 0 0),C ⊆ r → IsOArc C →
        ∃ D : Set (SurfaceModel 0 0 0),IsClosedDisc D ∧ C=discBd D) ∧
      ¬∃ D : Set (SurfaceModel 0 0 0),IsOpenDisc D ∧ r ⊆ D := by exact GraphMinor.GM05.sphere_counterexample_to_8_11

end

section

open Set Surface Topology

/-- Graph Minors V, (8.11), page 113:
"If $r$ is a connected open subset of a surface $\Sigma$, and every subset of $r$ homeomorphic to a circle bounds a closed disc in $\Sigma$, then there is an open disc $\Delta \subseteq \Sigma$ with $r \subseteq \Delta$."
The printed statement fails when `r` is a whole spherical component.
The additional condition excludes exactly those cases. The connected
proof uses the already proved GM VII (11.2) and the maximal flat-set
construction of GM XI instead of the omitted argument in GM V.

The open set cannot be a whole spherical component. The containment proof uses proved surface
results. See the correction to (8.11) in `corrections/GM05.md`. -/
theorem theorem_8_11 {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) {r : Set S} (hr : IsConnected r) (hro : IsOpen r)
    (H : ∀ F : Set S, F ⊆ r → IsOArc F → ∃ D : Set S, IsClosedDisc D ∧ F = discBd D)
    (hex : ∀ x ∈ r, ¬(IsSphere (connectedComponent x) ∧ r = connectedComponent x)) :
    ∃ D : Set S, IsOpenDisc D ∧ r ⊆ D := by exact GraphMinor.GM05.theorem_8_11_proof hS hr hro H hex

end

section

open Set Topology Surface GM19

universe u v

/-- Graph Minors V, (8.12), page 113:
"For any drawing of $H$ in $\Sigma$ and any region $r$ of this drawing, there is an open disc $\Delta \subseteq \Sigma$ with $r \subseteq \Delta$."
The context chooses an orientable surface minimal in the component-genus
order. We also require this drawing to meet every spherical component:
an unused sphere is a counterexample to the printed statement.

The drawing meets every spherical component. Minimal surfaces are chosen with no unused component.
See the correction to (8.12) in `corrections/GM05.md`. -/
theorem theorem_8_12 {α : Type u} {β : Type v} {H : Graph α β}
    {S : Type} [TopologicalSpace S] (hS : IsClosedSurface S)
    (hO : IsOrientableSurface S)
    (hmin : ∀ (T : Type) [TopologicalSpace T] (hT : IsClosedSurface T),
      IsOrientableSurface T → Nonempty (GraphDrawing H T) → ¬SurfaceGenusLT hT hS)
    (Γ : GraphDrawing H S)
    (hused : ∀ x : S, IsSphere (connectedComponent x) →
      (Γ.drawing.U ∩ connectedComponent x).Nonempty)
    {r : Set S} (hr : r ∈ Γ.drawing.R) :
    ∃ D : Set S, IsOpenDisc D ∧ r ⊆ D := by exact GraphMinor.GM05.theorem_8_12_proof hS hO hmin Γ hused hr

end

section

open Set Surface GM19

universe u v

/-- Graph Minors V, (8.13), page 113:
"With $H, \Sigma$ as in (8.12), any two drawings of $H$ in $\Sigma$ meet."
The proof follows the paper. Since `H` is nonplanar, it has a nonplanar
component. If two drawings of `H` were disjoint, the drawing of that
component would lie in one region of the other drawing, which by (8.12)
lies in an open disc, so the component would be planar. We retain the
correction to (8.12) that the second drawing meets every spherical
component.

The step "a nonplanar graph has a nonplanar component" is proved in `ComponentPlanar.lean`, and the
unused-sphere correction is kept. -/
theorem theorem_8_13 {α : Type u} {β : Type v} {H : Graph α β}
    (hnp : ¬GraphMinor.IsPlanar H) {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (hO : IsOrientableSurface S)
    (hmin : ∀ (T : Type) [TopologicalSpace T] (hT : IsClosedSurface T),
      IsOrientableSurface T → Nonempty (GraphDrawing H T) → ¬SurfaceGenusLT hT hS)
    (Γ Δ : GraphDrawing H S)
    (hused : ∀ x : S, IsSphere (connectedComponent x) →
      (Δ.drawing.U ∩ connectedComponent x).Nonempty) :
    (Γ.drawing.U ∩ Δ.drawing.U).Nonempty := by exact GraphMinor.GM05.theorem_8_13_proof hnp hS hO hmin Γ Δ hused

end

section

open Set Surface Graph
open Graph

universe u v u' v'

/-- Graph Minors V, (8.14), page 113:
"$H$ does not have the Erdös–Pósa property."
The graph `H` is finite and nonplanar, as fixed before (8.12).

The construction retains component models, removes loops before making copies, and uses a minimal
surface without unused components. The paper does not say how to choose the $2k' + 1$ drawings of
$H$, so the Lean makes its own choice: parallel copies of each edge, joined by stars near each
vertex. -/
theorem theorem_8_14 :
  ∀ {α' : Type u'} {β' : Type v'} (H : Graph α' β'),
    V(H).Finite → E(H).Finite → ¬ IsPlanar H → ¬ HasErdosPosaProperty.{u,v,u',v'} H := by exact GraphMinor.GM05.theorem_8_14_proof

end

end GraphMinor.GM05
