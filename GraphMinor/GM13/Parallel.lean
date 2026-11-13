module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM13.Section7Figure1
public import GraphMinor.GM16.Defs

/-!
# Graph Minors XIII: parallel statements (Sections 7 and 9)

Statements from N. Robertson and P. D. Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110:

- `GM13Theorem73Statement`: **(7.3)** (Section 7, page 90), proved by `theorem_7_3`
  (`Section7ThreeAll.lean`) and used in Section 9.
- `GM13Theorem74Statement`: **(7.4)** (Section 7, page 90), proved by `theorem_7_4_statement`
  (`Section7Six.lean`). Section 9 uses `GM13.theorem_7_4_proof` directly.
- `GM13Theorem77Statement`: **(7.7)** (Section 7, page 93), proved by `theorem_7_7`
  (`Section7Six.lean`) and used in Section 9.
- `GM13Theorem91Statement`: **(9.1)** (Section 9, page 98), used in (9.2) and (9.6)–(9.9).
- `GM13Theorem92Statement`: **(9.2)** (Section 9, page 99), used in (9.3) and (9.6)–(9.9).
- `GM13Theorem98Statement`: **(9.8)** and **(9.9)** (Section 9, page 104), proved in Section 9
  and used in Section 10.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 GraphMinor.GM16

universe u v

/-! ## Parallel Statements from Section 7 (pages 90–93) -/

/-- **Graph Minors XIII, (7.3)** (Section 7, page 90):
"(7.3) *Let $H$ be a wall of height $h$ with distance function $d$ and let $v \in V(H)$. Let
$r \ge 0$ be an integer with $h \ge 2r + 4$. Then there is a subgraph $H'$ of $H$, which is a wall
of height $h - 2r - 2$, such that*
*(i) $d' \ge d - 4r - 4$, where $d'$ is the distance function in $H'$*
*(ii) there is no vertex $u$ of $H'$ with $d(u, v) \le r$.*" -/
def GM13Theorem73Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (H : DrawnWall α β) (v : α) (r : ℕ),
    H.IsFigure1 →
    v ∈ V(H.graph) →
    2 * r + 4 ≤ H.height →
    ∃ H' : DrawnWall α β,
      H'.IsFigure1 ∧
      H'.graph ≤ H.graph ∧
      H'.drawingU ⊆ H.drawingU ∧
      H'.vertexPoint = H.vertexPoint ∧
      H'.height = H.height - 2 * r - 2 ∧
      DistGeSub H'.planeDist H.planeDist (4 * r + 4) ∧
      ∀ u ∈ V(H'.graph), ¬ H.dist u v ≤ r

/-- **Graph Minors XIII, (7.4)** (Section 7, page 90):
"(7.4) *For any $p \ge 2$ there exists $r \ge 0$ such that the following holds. Let $H$ be a wall
in a graph $G$. Let $P_1, \dots, P_{\binom{p}{2}}$ be mutually vertex-disjoint $H$-paths in $G$,
with their $p(p - 1)$ ends mutually at distance $\ge r$. Then $G$ has a minor isomorphic to $K_p$.
Moreover, there is an algorithm, with running time $\le C\varepsilon(G)$, where $C$ depends only
on $p$, which, given $G$, $H$, and $P_1, \dots, P_{\binom{p}{2}}$ as above, finds a model of $K_p$
in $G$.*" -/
def GM13Theorem74Statement : Prop :=
  ∀ (p : ℕ), 2 ≤ p →
    ∃ r : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β),
      H.IsFigure1 →
      IsWallIn G H.toWall →
      ∀ (P : Fin (p.choose 2) → Graph α β) (s t : Fin (p.choose 2) → α),
        (∀ i, IsHPathWithEnds G H.graph (P i) (s i) (t i)) →
        Pairwise (fun i j => Disjoint V(P i) V(P j)) →
        (∀ i j, i ≠ j →
          r ≤ H.dist (s i) (s j) ∧
          r ≤ H.dist (s i) (t j) ∧
          r ≤ H.dist (t i) (s j) ∧
          r ≤ H.dist (t i) (t j)) →
        (∀ i, r ≤ H.dist (s i) (t i)) →
        HasGraphModel (GM16.completeGraph p) G

/-- **Graph Minors XIII, (7.7)** (Section 7, page 93):
"(7.7) *For any $p \ge 2$ there are integers $l \ge 3$, $m \ge 0$ with the following property.
Let $G$ be a graph and let $H$ be a wall in $G$, so that there are $\binom{p}{2}$ $(l, m)$-stars
over $H$, with distinct centers; then $G$ has a $K_p$-minor. Moreover, there is an algorithm, with
running time $\le C\varepsilon(G)$, where $C$ depends only on $p$, which, given $\binom{p}{2}$
$(l, m)$-stars with distinct centers over a wall $H$ in a graph $G$, finds a model of $K_p$ in
$G$.*" -/
def GM13Theorem77Statement : Prop :=
  ∀ (p : ℕ), 2 ≤ p →
    ∃ l m : ℕ, 3 ≤ l ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β),
        H.IsFigure1 →
        IsWallIn G H.toWall →
        ∀ (S : Fin (p.choose 2) → Graph α β) (v : Fin (p.choose 2) → α),
          (∀ a, IsLMStarOver G H l m (S a) (v a)) →
          Function.Injective v →
          HasGraphModel (GM16.completeGraph p) G

/-! ## Parallel Statements from Section 9 (pages 98–104) -/

/-- **Graph Minors XIII, (9.1)** (Section 9, page 98):
"(9.1) *For any integer $p \ge 0$ there exist $k, r \ge 0$ such that the following holds. Let $H$ be
a wall in $G$, and let $H_1, \dots, H_k$ be subwalls of $H$ with $d(H_i, H_j) \ge r$
$(1 \le i < j \le k)$, where $d$ is the distance function of $H$. For $1 \le i \le k$, let
$P_i \cup Q_i$ be a cross over $H_i$, such that*
*(i) $(P_i \cup Q_i) \cap H \subseteq H_i$, for $1 \le i \le k$*
*(ii) $(P_i \cup Q_i) \cap (P_j \cup Q_j)$ is null for $1 \le i < j \le k$.*
*Then $G$ has a $K_p$-minor. Moreover, a model of $K_p$ in $G$ can be found in time $\le C\varepsilon(G)$, where $C$ depends only on $p$ and the height of $H$.*" -/
def GM13Theorem91Statement : Prop :=
  ∀ (p : ℕ), ∃ k r : ℕ,
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β)
      (H_sub : Fin k → Wall α β) (P Q : Fin k → Graph α β),
      H.IsFigure1 →
      IsWallIn G H.toWall →
      (∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall) →
      (∀ i j : Fin k, i ≠ j → r ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
      (∀ i : Fin k, IsCrossOverWall G (H_sub i) (P i) (Q i)) →
      (∀ i : Fin k, (V(P i) ∪ V(Q i)) ∩ V(H.graph) ⊆ V((H_sub i).graph)) →
      Pairwise (fun i j : Fin k => Disjoint (V(P i) ∪ V(Q i)) (V(P j) ∪ V(Q j))) →
      HasGraphModel (GM16.completeGraph p) G

/-- **Graph Minors XIII, (9.2)** (Section 9, page 99):
"(9.2) *For any $l \ge 3$, and $m, p \ge 0$, there exist $k, r \ge 0$ such that the following
holds. Let $H$ be a wall with distance function $d$ in a graph $G$, and let $H_1, \dots, H_k$ be
non-dividing subwalls of $H$, with*
$$d(H_i, H_j) \ge r \quad (1 \le i < j \le k).$$
*Then either there is an $(l, m)$-star over $H$ or $G$ has a $K_p$-minor. Moreover, there is an algorithm with running time $\le C\varepsilon(G)$, where $C$ depends only on $l, m, p$ and the height of $H$, which given such subwalls $H_1, \dots, H_k$, finds either an $(l, m)$-star over $H$ or a model of $K_p$ in $G$.*" -/
def GM13Theorem92Statement : Prop :=
  ∀ (l m p : ℕ), 3 ≤ l →
    ∃ k r : ℕ,
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β)
        (H_sub : Fin k → Wall α β),
        H.IsFigure1 →
        IsWallIn G H.toWall →
        (∀ i : Fin k, IsNonDividingSubwall G H.toWall (H_sub i)) →
        (∀ i j : Fin k, i ≠ j → r ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
        (∃ (S : Graph α β) (v : α), IsLMStarOver G H l m S v) ∨
          HasGraphModel (GM16.completeGraph p) G

/-- **Graph Minors XIII, (9.8) and (9.9)** (Section 9, page 104):
"(9.8) *For all $p \ge 0$ and $h \ge 2$, even, there exists $\omega \ge 0$ such that there is an
algorithm as in (9.9), with running time $O(v\varepsilon)$ for fixed $p, h$.*
(9.9) Algorithm.
*Input:* A graph $G$.
*Output:* Either
(i) a branch-decomposition of $G$ of width $\le \omega$, or
(ii) a model of $K_p$ in $G$, or
(iii) a subset $X \subseteq V$ with $|X| < \binom{p}{2}$ and a flat wall $H$ in $G \setminus X$ of
height $h$, and a rural division $\mathcal{A}$ of the society of $H$ in $G \setminus X$, and a
branch-decomposition of width $\le \omega$ of each interior member of $\mathcal{A}$." -/
def GM13Theorem98Statement : Prop :=
  ∀ (p h : ℕ), 2 ≤ h → Even h →
    ∃ ω : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β),
      V(G).Finite → E(G).Finite →
      GraphBranchWidthLE G ω ∨
      HasGraphModel (GM16.completeGraph p) G ∨
      ∃ (X : Set α) (H : Wall α β) (S_H : Society α β) (𝒜 : Set (Graph α β)),
        X ⊆ V(G) ∧
        X.ncard < p.choose 2 ∧
        IsFlatWallIn (deleteVertices G X) H ∧
        H.height = h ∧
        IsWallSociety (deleteVertices G X) H S_H ∧
        IsRuralDivision S_H 𝒜 ∧
        ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω

end GraphMinor.GM13
