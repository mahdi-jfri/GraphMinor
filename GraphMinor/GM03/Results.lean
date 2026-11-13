module

public import GraphMinor.GM03.Cited
public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section1
public import GraphMinor.GM03.Section2
public import GraphMinor.GM03.Section2a
public import GraphMinor.GM03.Section2f
public import GraphMinor.GM03.Section2g
public import GraphMinor.GM03.Section2n
public import GraphMinor.GM03.Section3
public import GraphMinor.GM03.Section3a
public import GraphMinor.GM03.Section4
public import GraphMinor.GM04.Main
public import GraphMinor.GM07.Bridge
public import GraphMinor.GM07.CuffSlide
public import GraphMinor.GM07.Section9
public import GraphMinor.GM09.Basic
public import GraphMinor.GM09.DiscDrawing
public import GraphMinor.GM09.PlanarNests
public import GraphMinor.GM13.Section4
public import GraphMinor.GM19.FragmentCut
public import GraphMinor.GM19.Section6a
public import GraphMinor.GM21.Section4Tangle
public import GraphMinor.Menger.Basic
public import GraphMinor.Planar.Grid
public import GraphMinor.Thomas.Separator
public import GraphMinor.Thomas.Translate
import GraphMinor.GM03.Section5
import GraphMinor.GM03.Section6

/-!
# Graph Minors III. Planar tree-width

N. Robertson and P. D. Seymour, J. Combin. Theory Ser. B 36 (1984) 49–64.

This file lists every numbered result of the paper in order. The proofs are in the other
files of this folder and, for algorithms, in `GraphMinor/Compute/`. Where a printed statement
or proof has an error, the docstring says so and refers to `corrections/GM03.md`.
-/

public section

namespace GraphMinor.GM03

/-! ## Section 1. INTRODUCTION -/

section

open Set Function Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM13 GraphMinor.GM21
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (1.1)** (Section 1, page 50):
"(1.1) [3]. *If $\mathcal{F}$ is an infinite set of graphs all with tree-width $\le w$, where $w$
is some integer, then there exist $G, G' \in \mathcal{F}$ such that $G$ is isomorphic to a minor
of $G'$.*" -/
theorem theorem_1_1 {α : Type u} {β : Type v} (w : ℕ) (ℱ : Set (Graph α β))
    (hℱ : ℱ.Infinite)
    (hV : ∀ G ∈ ℱ, V(G).Finite) (hE : ∀ G ∈ ℱ, E(G).Finite)
    (htw : ∀ G ∈ ℱ, TreeWidthLE G w) :
    ∃ G ∈ ℱ, ∃ G' ∈ ℱ, G ≠ G' ∧ IsIsoMinor G G' := by exact GraphMinor.GM03.theorem_1_1_proof w ℱ hℱ hV hE htw

end

-- (1.2) is not formalized: this cited result has no numbered declaration in this paper.

section

open Set Function Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM13 GraphMinor.GM21
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (1.3)** (Section 1, page 50):
"(1.3) *Any proper subset of the set of all planar graphs which is closed under isomorphism and
the taking of minors is a set of graphs with bounded tree-width.*"

It follows from (1.4), as in the paper. -/
theorem theorem_1_3 {α : Type u} {β : Type v} (ℱ : Set (Graph α β))
    (hV : ∀ G ∈ ℱ, V(G).Finite) (hE : ∀ G ∈ ℱ, E(G).Finite)
    (hPlanar : ∀ G ∈ ℱ, IsPlanar G)
    (hProper : ∃ H : Graph α β, V(H).Finite ∧ E(H).Finite ∧ IsPlanar H ∧ H ∉ ℱ)
    (hClosed : ∀ G ∈ ℱ, ∀ H : Graph α β, V(H).Finite → E(H).Finite → IsIsoMinor H G → H ∈ ℱ) :
    ∃ w : ℕ, ∀ G ∈ ℱ, TreeWidthLE G w := by exact GraphMinor.GM03.theorem_1_3_proof ℱ hV hE hPlanar hProper hClosed

end

section

open Set Function Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM13 GraphMinor.GM21
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (1.4)** (Section 1, page 50):
"(1.4) *For every planar graph $H$, there is a number $w$ such that every planar graph with no
minor isomorphic to $H$ has tree-width $\le w$.*"

The paper proves (1.4) in Section 5 as (5.3), and so does the Lean. -/
theorem theorem_1_4 {α₁ : Type u₁} {β₁ : Type v₁} (H : Graph α₁ β₁) (hPlanar : IsPlanar H) :
    ∃ w : ℕ, ∀ {α₂ : Type u₂} {β₂ : Type v₂} (G : Graph α₂ β₂),
      V(G).Finite → E(G).Finite → IsPlanar G → ¬ IsIsoMinor H G → TreeWidthLE G w := by exact GraphMinor.GM03.theorem_1_4_proof H hPlanar

end

section

open Set Function Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM13 GraphMinor.GM21
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (1.5)** (Section 1, page 50):
"(1.5) *If $\mathcal{F}$ is an infinite set of planar graphs, then there exist distinct
$G, G' \in \mathcal{F}$ such that $G$ is isomorphic to a minor of $G'$.*
*Proof.* Choose $H \in \mathcal{F}$, and choose a number $w$ as in (1.4). If there exists
$G \in \mathcal{F} - \{H\}$ such that $H$ is isomorphic to a minor of $G$ then (1.5) is true. If
not, then by our choice of $w$, each $G \in \mathcal{F} - \{H\}$ has tree-width $\le w$, and the
result follows from (1.1)." -/
theorem theorem_1_5 {α : Type u} {β : Type v} (ℱ : Set (Graph α β))
    (hℱ : ℱ.Infinite)
    (hV : ∀ G ∈ ℱ, V(G).Finite) (hE : ∀ G ∈ ℱ, E(G).Finite)
    (hPlanar : ∀ G ∈ ℱ, IsPlanar G) :
    ∃ G ∈ ℱ, ∃ G' ∈ ℱ, G ≠ G' ∧ IsIsoMinor G G' := by exact GraphMinor.GM03.theorem_1_5_proof ℱ hℱ hV hE hPlanar

end

/-! ## Section 2. RADIUS -/

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (2.1)** (page 52):
"(2.1) *Any planar graph of radius $\le d$ is isomorphic to a minor of a simple planar graph with
radius $\le d$.*"

*Proof.* Replace each edge of $G$ by three edges in series (obtained by splitting all edges of a
radius-$\le d$ drawing $M$ of $G$ twice via `GM11.exists_split`). The resulting graph $G'$ is
planar, has the same regions and hence drawing radius $\le d$, is simple
(`simple_of_double_splitData`), and has $G$ as a minor (`isIsoMinor_of_splitData`). -/
theorem theorem_2_1 {α : Type u} {β : Type v}
    {G : Graph α β} {d : ℕ}
    (_hPlanar : IsPlanar G) (hrad : HasRadiusLE G d) :
    ∃ (α' : Type) (β' : Type) (G' : Graph α' β'),
      G'.Simple ∧ IsPlanar G' ∧ HasRadiusLE G' d ∧ IsIsoMinor G G' := by exact GraphMinor.GM03.theorem_2_1_proof _hPlanar hrad

end

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (2.2)** (page 52):
"(2.2) *Let $G$ be a simple planar graph of radius $\le d$, where $d \ge 0$ is an integer. Then
there exist a simple planar graph $G'$ with a minor isomorphic to $G$ and a drawing $M'$ of $G'$
such that $\rho(M') \le d$ and $M'$ has a $d$-shell.*" -/
theorem theorem_2_2 {α : Type u} {β : Type v}
    {G : Graph α β} {d : ℕ}
    (hSimple : G.Simple) (_hPlanar : IsPlanar G) (hrad : HasRadiusLE G d) :
    ∃ (α' : Type) (β' : Type) (G' : Graph α' β') (M' : PlanarDrawing G')
      (C : Fin d → Graph α' β'),
      G'.Simple ∧ IsPlanar G' ∧ IsIsoMinor G G' ∧ HasDrawingRadiusLE M' d ∧
      IsDShell M' d C := by exact GraphMinor.GM03.theorem_2_2_proof hSimple _hPlanar hrad

end

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (2.3)** (page 55):
"(2.3) *Let $G$ be a simple planar graph, with a drawing $M$ such that $\rho(M) \le d$ and $M$ has
a $d$-shell $C_1, \dots, C_d$. Then $G$ is isomorphic to a minor of $N(d, \lambda)$ for some
sufficiently large $\lambda$.*" -/
theorem theorem_2_3 {α : Type u} {β : Type v}
    {G : Graph α β} {M : PlanarDrawing G} {d : ℕ} {C : Fin d → Graph α β}
    (hSimple : G.Simple) (hrad : HasDrawingRadiusLE M d) (hShell : IsDShell M d C) :
    ∃ lam : ℕ, 1 ≤ lam ∧ IsIsoMinor G (graphN d lam) := by exact GraphMinor.GM03.theorem_2_3_proof hSimple hrad hShell

end

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (2.4)** (page 55):
"(2.4) *If $G$ is a planar graph with radius $\le d$ then $G$ is isomorphic to a minor of
$N(d, \lambda)$ for some sufficiently large $\lambda$.*
This follows from (2.1), (2.2), and (2.3)." -/
theorem theorem_2_4 {α : Type u} {β : Type v}
    {G : Graph α β} {d : ℕ}
    (hPlanar : IsPlanar G) (hrad : HasRadiusLE G d) :
    ∃ lam : ℕ, 1 ≤ lam ∧ IsIsoMinor G (graphN d lam) := by exact GraphMinor.GM03.theorem_2_4_proof hPlanar hrad

end

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (2.5)** (page 55):
"(2.5) *For all $d \ge 0$, $\lambda \ge 1$, the graph $N(d, \lambda)$ has tree-width
$\le 3d + 1$.*" -/
theorem theorem_2_5 (d lam : ℕ) (_hlam : 1 ≤ lam) :
    TreeWidthLE (graphN d lam) (3 * d + 1) := by exact GraphMinor.GM03.theorem_2_5_proof d lam _hlam

end

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (2.6)** (page 56):
"(2.6) *If $G'$ is isomorphic to a minor of $G$ then the tree-width of $G'$ is not greater than
the tree-width of $G$.*" -/
theorem theorem_2_6 {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {G' : Graph α₁ β₁} {G : Graph α₂ β₂} {w : ℕ}
    (hVG : V(G).Finite) (hMinor : IsIsoMinor G' G) (hw : TreeWidthLE G w) :
    TreeWidthLE G' w := by exact GraphMinor.GM03.theorem_2_6_proof hVG hMinor hw

end

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (2.7)** (page 56):
"If $G$ is planar and has radius $\le d$ then its tree-width is at most $3d + 1$."

 -/
theorem theorem_2_7 {α : Type u} {β : Type v}
    {G : Graph α β} {d : ℕ}
    (hPlanar : IsPlanar G) (hrad : HasRadiusLE G d) :
    TreeWidthLE G (3 * d + 1) := by exact GraphMinor.GM03.theorem_2_7_proved hPlanar hrad

end

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (2.8)** (page 56):
"(2.8) *Let $G$ be a planar graph with radius $\ge d$, and let $M$ be a drawing of $G$. Then there
is a nested sequence $C_1, C_2, \dots, C_d$ of circuits of $M$.*" -/
theorem theorem_2_8 {α : Type u} {β : Type v}
    {G : Graph α β} (M : PlanarDrawing G) (d : ℕ)
    (hrad : ∀ _ : 0 < d, ¬ HasRadiusLE G (d - 1)) :
    ∃ C : Fin d → Graph α β, IsNestedCircuitSeq M d C := by exact GraphMinor.GM03.theorem_2_8_proof M d hrad

end

/-! ## Section 3. Sleeve Unions -/

section

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-- Graph Minors III, (3.1) (page 56):
"(3.1) *For $t \in V(T)$ and $v \in V(G)$, either $v \in X_t$, or there is a branch of $T$ at $t$
which contains all $t' \in V(T)$ with $v \in X_{t'}$.*" -/
theorem theorem_3_1 {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) (t : ι) {v : α} (hv : v ∈ V(G)) :
    v ∈ X t ∨
      (IsBranchAt T t (treeBranchAt T X t v) ∧
        ∀ t' : ι, v ∈ X t' → t' ∈ treeBranchAt T X t v) := by exact GraphMinor.GM03.theorem_3_1_proof hTD t hv

end

section

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-- Graph Minors III, (3.2) (page 56):
"(3.2) *If $v, v' \notin X_t$ and $v, v'$ are adjacent in $G$ then $T_t(v) = T_t(v')$.*" -/
theorem theorem_3_2 {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) (t : ι) {v v' : α}
    (hv : v ∉ X t) (hv' : v' ∉ X t) (hadj : G.Adj v v') :
    treeBranchAt T X t v = treeBranchAt T X t v' := by exact GraphMinor.GM03.theorem_3_2_proof hTD t hv hv' hadj

end

section

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-- Graph Minors III, (3.3) (page 56):
"(3.3) *If $v, v' \notin X_t$ and $v, v'$ are not separated in $G$ by $X_t$, then
$T_t(v) = T_t(v')$.*" -/
theorem theorem_3_3 {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) (t : ι) {v v' : α}
    (hv : v ∉ X t) (hv' : v' ∉ X t)
    (hnot_sep : ¬ Separates G (X t) {v} {v'}) :
    treeBranchAt T X t v = treeBranchAt T X t v' := by exact GraphMinor.GM03.theorem_3_3_proof hTD t hv hv' hnot_sep

end

section

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-- Graph Minors III, (3.4) (page 57):
"(3.4) *Let $e$ be an edge of $T$ with ends $t, t'$ say, and let $N, N'$ be the vertex sets of the
two components of $T \setminus e$. Then $X_t \cap X_{t'}$ separates $\bigcup(X_n : n \in N)$ and
$\bigcup(X_n : n \in N')$.*" -/
theorem theorem_3_4 {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) {t t' : ι} (hadj : T.Adj t t') :
    Separates G (X t ∩ X t')
      (⋃ n ∈ treeEdgeSide T t t', X n) (⋃ n ∈ treeEdgeSide T t' t, X n) := by exact GraphMinor.GM03.theorem_3_4_proof hTD hadj

end

section

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-- Graph Minors III, (3.5) (page 57):
"(3.5) *Let $|V(T)| \ge 2$, and for each $t \in V(T)$ let $G_t$ be a connected subgraph of $G$ with
$V(G_t) \cap X_t = \emptyset$. Then there exist $t, t' \in V(T)$, adjacent in $T$, such that
$X_t \cap X_{t'}$ separates $V(G_t)$ and $V(G_{t'})$ in $G$.*" -/
theorem theorem_3_5 {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) (_hT_card : 2 ≤ Fintype.card ι)
    (G_sub : ι → Graph α β)
    (hsub : ∀ t : ι, G_sub t ≤ G)
    (hconn : ∀ t : ι, IsGraphConnected (G_sub t))
    (hdisj : ∀ t : ι, Disjoint V(G_sub t) (X t)) :
    ∃ t t' : ι, T.Adj t t' ∧ Separates G (X t ∩ X t') V(G_sub t) V(G_sub t') := by exact GraphMinor.GM03.theorem_3_5_proof hTD _hT_card G_sub hsub hconn hdisj

end

section

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-- Graph Minors III, (3.6) (page 57):
"(3.6) *Suppose $X \subseteq V(S)$ and $|X \cap V(C_j)| \ge 2$ $(1 \le j \le s)$. Then there are $r$
vertex-disjoint paths of $S$, each between $X$ and $V(C_s)$.*" -/
theorem theorem_3_6 (r s : ℕ) (hs : 0 < s) (hr : r ≤ 2 * s)
    (X : Set (Fin r × Fin s))
    (hX : ∀ j : Fin s, 2 ≤ (X ∩ V(cylinderCircle r s j)).ncard) :
    ∃ P : Fin r → Graph (Fin r × Fin s) ((Fin r × Fin s) ⊕ (Fin r × Fin s)),
      Pairwise (fun i₁ i₂ : Fin r => Disjoint V(P i₁) V(P i₂)) ∧
      ∀ i : Fin r, IsPathBetween (cylinderGraph r s) (P i) X (V(cylinderCentralCircle r s hs)) := by exact GraphMinor.GM03.theorem_3_6_proof r s hs hr X hX

end

section

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-- Graph Minors III, (3.7) (page 58):
"(3.7) *Let $(T, \mathcal{X})$ be a tree-decomposition of $S$, where
$\mathcal{X} = (X_t : t \in V(T))$. Then there exist $t_0 \in V(T)$ and $r$ vertex-disjoint paths
of $S$, each between $X_{t_0}$ and $C_s$.*" -/
theorem theorem_3_7 {ι : Type w} [Fintype ι]
    (r s : ℕ) (hs : 0 < s) (hr : r ≤ 2 * s)
    {T : SimpleGraph ι} {X : ι → Set (Fin r × Fin s)}
    (hTD : IsTreeDecomposition (cylinderGraph r s) T X) :
    ∃ (t₀ : ι) (P : Fin r → Graph (Fin r × Fin s) ((Fin r × Fin s) ⊕ (Fin r × Fin s))),
      Pairwise (fun i₁ i₂ : Fin r => Disjoint V(P i₁) V(P i₂)) ∧
      ∀ i : Fin r, IsPathBetween (cylinderGraph r s) (P i) (X t₀)
        (V(cylinderCentralCircle r s hs)) := by exact GraphMinor.GM03.theorem_3_7_proof r s hs hr hTD

end

section

open Set Function Relation Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM16 GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-- Graph Minors III, (3.8) (page 58):
"(3.8) *With $S, C_1, \dots, C_s$ as before, let $V(C_s) = \{u_1, \dots, u_r\}$. Let $H$ be another
graph, vertex-disjoint from $S$, and let $v_1, \dots, v_r$ be distinct vertices of $H$. Construct
$G$ by making the identifications $u_1 = v_1, \dots, u_r = v_r$. If $G$ has tree-width $\le w$,
then $H$ has a tree-decomposition $(T, \mathcal{X})$ where $\mathcal{X} = (X_t : t \in V(T))$ say,
of width $\le w$, such that $\{v_1, \dots, v_r\} \subseteq X_{t_0}$ for some $t_0 \in V(T)$.*" -/
theorem theorem_3_8 {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {r : ℕ} {G : Graph α₁ β₁} {H : Graph α₂ β₂} (hVG : V(G).Finite)
    (s : ℕ) (hs : 0 < s) (hr : r ≤ 2 * s) (v : Fin r → α₂)
    (hId : IsCylinderIdentification G H s hs v) {w : ℕ} (htw : TreeWidthLE G w) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (X : ι → Set α₂) (t₀ : ι),
      IsTreeDecomposition H T X ∧ TreeDecompHasWidthLE X w ∧ Set.range v ⊆ X t₀ := by exact GraphMinor.GM03.theorem_3_8_proof hVG s hs hr v hId htw

end

section

open Set Function Relation Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM16 GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-- Graph Minors III, (3.9) (page 59):
"(3.9) *If $G$ is the sleeve union of $G_1, G_2$ then $G_1, G_2$ are both isomorphic to proper
minors of $G$.*"

The sleeve cylinder has positive length also at radius zero. See the correction to (3.9) in
`corrections/GM03.md`. -/
theorem theorem_3_9 {α : Type u} {β : Type v} {α₁ : Type u₁} {β₁ : Type v₁}
    {α₂ : Type u₂} {β₂ : Type v₂}
    {G : Graph α β} {G₁ : Graph α₁ β₁} {G₂ : Graph α₂ β₂}
    (hSU : IsSleeveUnion G G₁ G₂) :
    IsIsoProperMinor G₁ G ∧ IsIsoProperMinor G₂ G := by exact GraphMinor.GM03.theorem_3_9_proof hSU

end

section

open Set Function Relation Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM16 GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-- Graph Minors III, (3.10) (page 59):
"(3.10) *If $G$ is the sleeve union of $G_1, G_2$ then the tree-width of $G$ is the maximum of the
tree-widths of $G_1, G_2$.*" -/
theorem theorem_3_10 {α : Type u} {β : Type v} {α₁ : Type u₁} {β₁ : Type v₁}
    {α₂ : Type u₂} {β₂ : Type v₂}
    {G : Graph α β} {G₁ : Graph α₁ β₁} {G₂ : Graph α₂ β₂}
    (hVG : V(G).Finite) (hSU : IsSleeveUnion G G₁ G₂) (w : ℕ) :
    TreeWidthLE G w ↔ TreeWidthLE G₁ w ∧ TreeWidthLE G₂ w := by exact GraphMinor.GM03.theorem_3_10_proof hVG hSU w

end

/-! ## Section 4. The Production of Cylinders -/

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM09.PlanarNests
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22

universe u v

/-- **Graph Minors III, (4.1)** (page 60):
"(4.1) *Let $r \ge 0$, $s \ge 1$ be integers, and let $M$ be a drawing of the planar graph $G$.
Suppose that there is a nested sequence $C_1, \dots, C_s$ of circuits of $M$ such that there are $r$
vertex-disjoint paths of $G$, each between $V(C_1)$ and $V(C_s)$. Then $M$ majors the $r \times s$
cylinder.*"

The proof is III's own. It is written once, in `GM09/PlanarNests.lean`, because IX (10.1) and XIV
(9.5) use it too. -/
theorem theorem_4_1 {α : Type u} {β : Type v}
    {G : Graph α β} (M : PlanarDrawing G) (r s : ℕ) (hs : 0 < s)
    (C₀ : Fin s → Graph α β) (P₀ : Fin r → Graph α β)
    (hC₀ : IsNestedCircuitSeq M s C₀)
    (hP₀_disj : Pairwise (fun i₁ i₂ : Fin r => Disjoint V(P₀ i₁) V(P₀ i₂)))
    (hP₀_path : ∀ i : Fin r, IsPathBetween G (P₀ i)
      V(C₀ ⟨0, hs⟩) V(C₀ ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)) :
    MajorsCylinder M r s := by exact GraphMinor.GM03.theorem_4_1_proof M r s hs C₀ P₀ hC₀ hP₀_disj hP₀_path

end

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM09.PlanarNests
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22

universe u v

/-- **Graph Minors III, (4.2)** (page 61):
"(4.2) *Let $r \ge 0$, $s \ge 1$ be integers, and let $M$ be a drawing of the planar graph $G$. Let
$C_1, \dots, C_s$ be a nested sequence of circuits of $M$. Then one of the following holds:*

(i) *$M$ majors the $r \times s$ cylinder,*
(ii) *there exists $X \subseteq V(G)$ with $|X| < r$, such that $X$ separates $V(C_1)$ and
$V(C_s)$.*" -/
theorem theorem_4_2 {α : Type u} {β : Type v}
    {G : Graph α β} (M : PlanarDrawing G) (r s : ℕ) (hs : 0 < s)
    (C : Fin s → Graph α β) (hC : IsNestedCircuitSeq M s C) :
    MajorsCylinder M r s ∨
      ∃ X ⊆ V(G), X.ncard < r ∧
        Separates G X V(C ⟨0, hs⟩) V(C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩) := by exact GraphMinor.GM03.theorem_4_2_proof M r s hs C hC

end

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM09.PlanarNests
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22

universe u v

/-- **Graph Minors III, (4.3)** (page 61):
"(4.3) *Let $r \ge 0$ be an integer, and let $r' = r + 1$ if $r$ is odd, and $r' = r$ if $r$ is
even. Let $s > r'$ be an integer. Let $M$ be a drawing of the planar graph $G$, and suppose that $M$
majors the $r \times s$ cylinder. Then either $M$ majors the $(r + 1) \times (s - r')$ cylinder, or
$G$ is expressible as the sleeve union of two planar graphs.*" -/
theorem theorem_4_3 {α : Type u} {β : Type v}
    {G : Graph α β} (M : PlanarDrawing G) (r s : ℕ)
    (hs : 2 * ((r + 1) / 2) < s)
    (hMaj : MajorsCylinder M r s) :
    MajorsCylinder M (r + 1) (s - 2 * ((r + 1) / 2)) ∨
      IsExpressibleAsPlanarSleeveUnion G := by exact GraphMinor.GM03.theorem_4_3_proof M r s hs hMaj

end

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM09.PlanarNests
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22

universe u v

/-- **Graph Minors III, (4.4)** (page 61):
"Let $r \ge 0$, $s \ge 1$ be integers, and let $M$ be a drawing of the planar graph $G$. Suppose that $G$ is not expressible as a sleeve union of two planar"

 -/
theorem theorem_4_4 {α : Type u} {β : Type v}
    {G : Graph α β} (M : PlanarDrawing G) (r s : ℕ) (hs : 0 < s)
    (hNotSleeve : ¬ IsExpressibleAsPlanarSleeveUnion G)
    (hNotMaj : ¬ MajorsCylinder M r s) :
    HasRadiusLE G (cylinderRadiusBound r s - 1) := by exact GraphMinor.GM03.theorem_4_4_proof M r s hs hNotSleeve hNotMaj

end

section

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM09.PlanarNests
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22

universe u v

/-- **Graph Minors III, (4.5)** (page 62):
"(4.5) *Let $r \ge 0$, $s \ge 1$ be integers. If $G$ is a planar graph which is not expressible as
the sleeve union of two planar graphs, then either $G$ has a minor isomorphic to the $r \times s$
cylinder, or it has tree-width at most*
$$
\begin{aligned}
&3(s + \frac{1}{2}r^2) - 2 && (r\text{ even}) \\
&3(s + \frac{1}{2}(r^2 - 1)) - 2 && (r\text{ odd}).
\end{aligned}
$$" -/
theorem theorem_4_5 {α : Type u} {β : Type v}
    {G : Graph α β} (r s : ℕ) (hs : 0 < s)
    (hPlanar : IsPlanar G) (hNotSleeve : ¬ IsExpressibleAsPlanarSleeveUnion G) :
    IsIsoMinor (cylinderGraph r s) G ∨ TreeWidthLE G (cylinderTreeWidthBound r s) := by exact GraphMinor.GM03.theorem_4_5_proof r s hs hPlanar hNotSleeve

end

/-! ## Section 5. THE MAIN RESULT -/

section

open Set Function Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.GM01 GraphMinor.GM09 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (5.1)** (page 62):
"(5.1) *For every planar graph $H$ there is a number $r \ge 1$ such that the $r \times r$ cylinder
has a minor isomorphic to $H$.*"

The paper refers to [5], which is VII, for a proof. The Lean uses VII (9.6). -/
theorem theorem_5_1 {α : Type u} {β : Type v}
    {H : Graph α β} (hPlanar : IsPlanar H) :
    ∃ r : ℕ, 1 ≤ r ∧ IsIsoMinor H (cylinderGraph r r) := by exact GraphMinor.GM03.theorem_5_1_proof hPlanar

end

section

open Set Function Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.GM01 GraphMinor.GM09 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (5.2)** (pages 62–63):
"(5.2) *Let $r \ge 1$ be an integer. If $G$ is planar and has no minor isomorphic to the $r \times r$
cylinder then $G$ has tree-width $\le \frac{3}{2}(r^2 + 2r) - 2$.*" -/
theorem theorem_5_2 {α : Type u} {β : Type v}
    {G : Graph α β} (r : ℕ) (hr : 1 ≤ r)
    (hPlanar : IsPlanar G) (hNoCyl : ¬ IsIsoMinor (cylinderGraph r r) G) :
    TreeWidthLE G (3 * (r ^ 2 + 2 * r) / 2 - 2) := by exact GraphMinor.GM03.theorem_5_2_proof r hr hPlanar hNoCyl

end

section

open Set Function Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.GM01 GraphMinor.GM09 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

/-- **Graph Minors III, (5.3)** (page 63):
"(5.3) *For every planar graph $H$ there is a number $w$ such that every planar graph with no minor
isomorphic to $H$ has tree-width $\le w$.*" -/
theorem theorem_5_3 {α₁ : Type u₁} {β₁ : Type v₁} (H : Graph α₁ β₁) (hPlanar : IsPlanar H) :
    ∃ w : ℕ, ∀ {α₂ : Type u₂} {β₂ : Type v₂} (G : Graph α₂ β₂),
      IsPlanar G → ¬ IsIsoMinor H G → TreeWidthLE G w := by exact GraphMinor.GM03.theorem_5_3_proof H hPlanar

end

/-! ## Section 6. REMARKS -/

section

open Set Function Topology Classical
open Graph
open GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11
open GraphMinor.GM19 GraphMinor.GM21 GraphMinor.Planar

universe u₁ v₁ u₂ v₂

/-- **Graph Minors III, (6.1)** (page 64):
"Let $S$ be a surface of genus $g > 0$, and let $H$ be a graph which may be embedded in $S$. Then there is a number $k$ with the following property. For every graph $G$ which has no minor isomorphic to $H$ but which can be embedded in $S$, there exists $X \subseteq V(G)$ with $|X| \le k$ such that $G \setminus X$ can be embedded on a surface of genus $<g$."

Graph Minors III, (6.1) (page 64):
> (6.1) *Let $S$ be a surface of genus $g > 0$, and let $H$ be a graph which may be embedded in $S$.
> Then there is a number $k$ with the following property. For every graph $G$ which has no minor
> isomorphic to $H$ but which can be embedded in $S$, there exists $X \subseteq V(G)$ with $|X| \le k$
> such that $G \setminus X$ can be embedded on a surface of genus $<g$.*

Here `S` is a closed surface homeomorphic to `SurfaceModel a b 0` of Euler genus
`g = 2 * a + b > 0` (and orientable genus `a` when `b = 0`). Deleting the `≤ k` vertices of `G`
lying on a `Γ_G.drawing`-normal non-null-homotopic `O`-arc `F` and cutting `S` along `F` via
`GM19.exists_cut_simpler` embeds `GM09.deleteVertices G X` in a surface `S'` each of whose connected
components `C ∈ spaceComponents S'` is simpler than `S` and has genus `2 * a' + b' < g`
(and `a' < a` when `b = 0`). -/
theorem theorem_6_1 {α₁ : Type u₁} {β₁ : Type v₁}
    (S : Type) [TopologicalSpace S] (hS : IsSurface S)
    (a b g : ℕ) (hg : 2 * a + b = g) (hg_pos : 0 < g)
    (he : Nonempty (S ≃ₜ SurfaceModel a b 0))
    (H : Graph α₁ β₁) (hH : Nonempty (GraphDrawing H S)) :
    ∃ k : ℕ, ∀ {α₂ : Type u₂} {β₂ : Type v₂} (G : Graph α₂ β₂),
      ¬ IsIsoMinor H G → Nonempty (GraphDrawing G S) →
      ∃ X ⊆ V(G), X.ncard ≤ k ∧
        ∃ (S' : Type) (_ : TopologicalSpace S'),
          IsSurface S' ∧
          Nonempty (GraphDrawing (GM09.deleteVertices G X) S') ∧
          ∀ C ∈ spaceComponents S',
            IsSimplerThan C S ∧
            ∃ a' b' c' : ℕ,
              Nonempty (C ≃ₜ SurfaceModel a' b' c') ∧
              (b = 0 → b' = 0 ∧ a' < a) ∧ 2 * a' + b' < g := by exact GraphMinor.GM03.theorem_6_1_proof S hS a b g hg hg_pos he H hH

end

end GraphMinor.GM03
