module

public import GraphMinor.Compute.Algorithm33
public import GraphMinor.Compute.Algorithm41Verified
public import GraphMinor.Compute.Algorithm44
public import GraphMinor.Compute.Algorithm62
public import GraphMinor.Compute.Algorithm63
public import GraphMinor.Compute.Algorithm64
public import GraphMinor.Compute.Algorithm65
public import GraphMinor.Compute.Algorithm72
public import GraphMinor.Compute.Algorithm74
public import GraphMinor.Compute.Algorithm77
public import GraphMinor.Compute.Algorithm83
public import GraphMinor.Compute.Algorithm91
public import GraphMinor.Compute.Algorithm92Final
public import GraphMinor.Compute.DPStatement
public import GraphMinor.Compute.DisjointPathsFinal
public import GraphMinor.Compute.GM13ClassRecognition
public import GraphMinor.Compute.GM13ProgramsClosed
public import GraphMinor.Compute.GM13VisionProgram
public import GraphMinor.Compute.GM13WallProgram
public import GraphMinor.Compute.Join104
public import GraphMinor.Compute.Specs13
public import GraphMinor.Compute.Specs9
public import GraphMinor.GM13.Defs
public import GraphMinor.GM13.Parallel
public import GraphMinor.GM13.Section102Proved
public import GraphMinor.GM13.Section10Free
public import GraphMinor.GM13.Section10a
public import GraphMinor.GM13.Section2
public import GraphMinor.GM13.Section3
public import GraphMinor.GM13.Section3a
public import GraphMinor.GM13.Section4
public import GraphMinor.GM13.Section5
public import GraphMinor.GM13.Section5a
public import GraphMinor.GM13.Section5d
public import GraphMinor.GM13.Section6
public import GraphMinor.GM13.Section6a
public import GraphMinor.GM13.Section7FourProof
public import GraphMinor.GM13.Section7Six
public import GraphMinor.GM13.Section7ThreeAll
public import GraphMinor.GM13.Section8
public import GraphMinor.GM13.Section8a
public import GraphMinor.GM13.Section9
public import GraphMinor.GM13.Section9a
public import GraphMinor.GM13.Section9b

/-!
# Graph Minors XIII: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XIII. The disjoint paths problem*, J. Combin. Theory
Ser. B **63** (1995), 65–110.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. The errors of the paper and their corrections are listed in
`corrections/GM13.md`.
-/

public section

namespace GraphMinor.GM13

open Set

universe u v w u_1 u_2

/-! ## Section 1. Introduction -/

open GraphMinor.Compute GraphMinor.LRPlanarity GraphMinor.Compute.Crossing SimpleGraph in
/-- **Graph Minors XIII**, the main result (Section 1, pages 65–66), which the paper does not
number: "The main result of this paper is that for any fixed $k$ there is a polynomial algorithm to
solve DP. It has running time $O(v^3)$, where $v = v(G)$ is defined to be $|V(G)| + 1$." Shiloach's
two-paths algorithm is replaced by the crossing extractor of `docs/crossing/crossing_extractor.tex`,
since Shiloach's paper gives only a sketch of its algorithm. The planarity test that the extractor
needs is proved from the note `docs/planarity/planarity_test.tex`. The paper names no model of
computation. The programs run on the word RAM of `GraphMinor/Compute/Basic.lean`. -/
theorem disjoint_paths (k : ℕ) :
    ∃ P : Cmd,
    ComputesRelInTime (dpSize (k := k)) (fun x s => s.arrs inArr =
      encDPIn x) IsValidDPOutput P (fun v => (v + 1) ^ 3) :=
  Compute.disjointPathsStatement_proved k

/-! ## Section 2. Folios -/

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM05 GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 in
/-- **Graph Minors XIII, (2.1)** (page 69):
"If $Z' \subseteq Z \subseteq V(G)$ and $\delta \ge 0$, the $\delta$-folio of $G$ relative to $Z'$
is determined by a knowledge of the $\delta$-folio of $G$ relative to $Z$." -/
theorem theorem_2_1 {α : Type u} {β₁ : Type v} {β₂ : Type w} {G₁ : Digraph α β₁} {G₂ : Digraph α β₂}
    {δ : ℕ} {Z Z' : Set α} (hZ'Z : Z' ⊆ Z) (h : HasSameDeltaFolioRel G₁ G₂ δ Z) :
    HasSameDeltaFolioRel G₁ G₂ δ Z' :=
  GM13.theorem_2_1_proof hZ'Z h

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM05 GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 in
/-- **Graph Minors XIII, (2.2)** (page 69):
"Let $(A, B)$ be a separation of a digraph $G$, and let $V(A \cap B) \subseteq Z \subseteq V(G)$.
For $\delta \ge 0$, the $\delta$-folio of $G$ relative to $Z$ is determined by a knowledge of the
$\delta$-folios of $A$ relative to $Z \cap V(A)$ and of $B$ relative to $Z \cap V(B)$." -/
theorem theorem_2_2 {α : Type u} {β₁ : Type v} {β₂ : Type w} {G₁ A₁ B₁ : Digraph α β₁}
    {G₂ A₂ B₂ : Digraph α β₂} {δ : ℕ} {Z : Set α} (hsep₁ : G₁.IsSeparation A₁ B₁)
    (hsep₂ : G₂.IsSeparation A₂ B₂) (hfin : (A₁.vertexSet ∩ B₁.vertexSet).Finite)
    (hAB₁ : A₁.vertexSet ∩ B₁.vertexSet ⊆ Z) (hAB₂ : A₂.vertexSet ∩ B₂.vertexSet ⊆ Z)
    (hZ₁ : Z ⊆ G₁.vertexSet) (hZ₂ : Z ⊆ G₂.vertexSet) (hZA : Z ∩ A₁.vertexSet = Z ∩ A₂.vertexSet)
    (hZB : Z ∩ B₁.vertexSet = Z ∩ B₂.vertexSet)
    (hA : HasSameDeltaFolioRel A₁ A₂ δ (Z ∩ A₁.vertexSet))
    (hB : HasSameDeltaFolioRel B₁ B₂ δ (Z ∩ B₁.vertexSet)) :
    HasSameDeltaFolioRel G₁ G₂ δ Z :=
  GM13.theorem_2_2_proof hsep₁ hsep₂ hfin hAB₁ hAB₂ hZ₁ hZ₂ hZA hZB hA hB

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM05 GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 in
/-- **Graph Minors XIII, (2.3)** (page 70):
"Let $(A, B)$ be a separation of a digraph $G$, and let $Z \subseteq V(A)$. If $v \in V(B)$ is
irrelevant to the $\delta$-folio of $B$ relative to $V(A \cap B)$ then it is irrelevant to the
$\delta$-folio of $G$ relative to $Z$." -/
theorem theorem_2_3 {α : Type u} {β : Type v} {G A B : Digraph α β} {δ : ℕ} {Z : Set α} {v : α}
    (hsep : G.IsSeparation A B) (hfin : (A.vertexSet ∩ B.vertexSet).Finite) (hZ : Z ⊆ A.vertexSet)
    (hirr : IsIrrelevantVertex B δ (A.vertexSet ∩ B.vertexSet) v) :
    IsIrrelevantVertex G δ Z v :=
  GM13.theorem_2_3_proof hsep hfin hZ hirr

/-! ## Section 3. Branch-Width -/

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM16 in
/-- **Graph Minors XIII, (3.1) Lemma** (page 71):
"*Let $G$ be a graph with branch-width $\le \omega$, where $\omega \ge 2$, and let $Z \subseteq
V(G)$. Then there is a separation $(A, B)$ of $G$ of order $\le \omega$ with*
$$|Z - V(A)|, |Z - V(B)| \le \frac{2}{3} |Z| - \frac{1}{2} |Z \cap V(A \cap B)|.$$" -/
theorem theorem_3_1 {α : Type u} {β : Type v} (G : Graph α β) (hVG : V(G).Finite)
    (hEG : E(G).Finite) (ω : ℕ) (hω : 2 ≤ ω) (hbw : GraphBranchWidthLE G ω) (Z : Set α)
    (hZ : Z ⊆ V(G)) :
    ∃ A B : Graph α β, IsGraphSeparation G A B ∧
    graphSeparationOrder A B ≤ ω ∧
    6 * (Z \ V(A)).ncard + 3 * (Z ∩ (V(A) ∩ V(B))).ncard ≤ 4 * Z.ncard ∧
    6 * (Z \ V(B)).ncard + 3 * (Z ∩ (V(A) ∩ V(B))).ncard ≤ 4 * Z.ncard :=
  GM13.theorem_3_1_proof G hVG hEG ω hω hbw Z hZ

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM16 in
/-- **Graph Minors XIII, (3.2) Lemma** (page 72):
"If $\omega \ge 2$ is an integer and $G$ is a simple graph with branch-width $\le \omega$, then
$|E(G)| \le (\frac{3}{2}\omega - 1) |V(G)|$." -/
theorem theorem_3_2 {α : Type u} {β : Type v} (G : Graph α β) (hVG : V(G).Finite)
    (hEG : E(G).Finite) (hSimp : IsSimpleGraph G) (ω : ℕ) (hω : 2 ≤ ω)
    (hbw : GraphBranchWidthLE G ω) :
    E(G).ncard ≤ (3 * ω / 2 - 1) * V(G).ncard ∧
    2 * E(G).ncard ≤ (3 * ω - 2) * V(G).ncard :=
  GM13.theorem_3_2_proof G hVG hEG hSimp ω hω hbw

open scoped BigOperators in
open GraphMinor.Compute SimpleGraph in
/-- **Graph Minors XIII, (3.3) Algorithm** (pages 72–75):
"(3.3) Algorithm.
*Input:* A graph $G$ with $|E(G)| \ge 2$.
*Output:* A subgraph $G'$ of $G$ and a branch-decomposition of $G'$ of width $\le 3\omega$, such
that either $G' = G$ or $G'$ has branch-width $\ge \omega$.
*Running time:* $O(v^2 + \varepsilon)$."

For every fixed integer `ω ≥ 2`, `alg33Prog ω` computes in `O(v²)` time on the Word RAM a valid
output `out` satisfying `IsValidAlg33Output ω x (decAlg33Out ω x out)`:
- `(decAlg33Out ω x out).G' ≤ x.H₁`;
- `IsBranchDecompOfWidthLe (3 * ω) (decAlg33Out ω x out).G' (decAlg33Out ω x out).T (decAlg33Out ω x
out).τ`;
- `(decAlg33Out ω x out).G' = x.H₁ ∨ ¬ GM13.GraphBranchWidthLE (decAlg33Out ω x out).G'.toGMGraph (ω
- 1)`. -/
theorem algorithm_3_3 (ω : ℕ) (hω : 2 ≤ ω) :
    ComputesArrRelInTime alg33Size encAlg33In
    (fun x out => IsValidAlg33Output ω x (decAlg33Out ω x out))
    (alg33Prog ω) (fun v => (v + 1) ^ 2) :=
  Compute.gm13_algorithm_3_3 ω hω

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM16 in
/-- **Graph Minors XIII, (3.3)** (page 72): "Algorithm. Input: A graph $G$ with $|E(G)| \ge 2$.
Output: A subgraph $G'$ of $G$ and a branch-decomposition of $G'$ of width $\le 3\omega$, such that
either $G' = G$ or $G'$ has branch-width $\ge \omega$. Running time: $O(v^2 + \varepsilon)$.
Description: We construct the simple graph $H_1$ underlying $G$, by deleting all loops and multiple
edges. We choose a maximal subgraph $H_2$ of $H_1$ with $|E(H_2)| \le (\frac{3}{2}\omega - 1)
|V(H_1)| + 1$. Thus, either $H_2 = H_1$ or $H_2$ has branch-width $\ge \omega$, by (3.2). We assume
that $|E(H_2)| \ge 2$, for otherwise the problem is trivial. We shall construct a subgraph $H_3$ of
$H_2$ and a branch-decomposition of $H_3$ of width $\le 3\omega$, such that either $H_3 = H_2$ or
$H_3$ has branch-width $\ge \omega$. Given such an $H_3$, the algorithm is completed as follows. If
$H_3 \ne H_2$, we set $G' = H_3$ and stop. If $H_3 = H_2$, we have a branch-decomposition of $H_2$
of width $\le 3\omega$. If $H_2 \ne H_1$ we set $G' = H_2$ and stop. If $H_2 = H_1$, we convert our
branch-decomposition to one for $G$, set $G' = G$, and stop."

, numbered alias for `algorithm_3_3_correct`. -/
theorem theorem_3_3 {α : Type u} {β : Type v} (G : Graph α β) (hVG : V(G).Finite)
    (hEG : E(G).Finite) (hE2 : 2 ≤ E(G).ncard) (ω : ℕ) (hω : 2 ≤ ω) :
    ∃ (G' : Graph α β) (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : β → ι),
    G' ≤ G ∧
    2 ≤ E(G').ncard ∧
    IsGraphBranchDecomposition G' T τ ∧
    graphBranchDecompWidth G' T τ ≤ 3 * ω ∧
    (G' = G ∨ ¬ GraphBranchWidthLE G' ω) ∧
    (G' = G ∨ ¬ GraphBranchWidthLE G' (ω - 1)) :=
  GM13.theorem_3_3_proof G hVG hEG hE2 ω hω

/-! ## Section 4. Folio Determination with Bounded Branch-Width -/

open GraphMinor.Compute in
/-- **Graph Minors XIII, (4.1)**, pages 75–76:
"(4.1) **Algorithm.**

*Input:* A digraph $G$, and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$, and a
branch-decomposition $(T, \tau)$ of $G$ of width $\le \omega$.

*Output:* The $\delta$-folio of $G$ relative to $Z$, and a modelling of it.

*Running time:* $O(\varepsilon)$."
The output reader reads the written codes, edge indices, and branch bit lists. -/
theorem algorithm_4_1 (δ ξ ω : ℕ) :
    ComputesArrRelInTime (alg41Size (ξ := ξ) (ω := ω)) encAlg41In
    (fun x out => IsValidAlg41ReadOutput δ x (decAlg41Out δ x out))
    (alg41Prog δ ξ ω) (fun n => n) :=
  Compute.gm13_algorithm_4_1 δ ξ ω

open scoped Classical in
open Function Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM16 in
/-- **Graph Minors XIII, (4.1)** (page 75): "Algorithm. Input: A digraph $G$, and a subset $Z
\subseteq V(G)$ with $|Z| \le \xi$, and a branch-decomposition $(T, \tau)$ of $G$ of width $\le
\omega$. Output: The $\delta$-folio of $G$ relative to $Z$, and a modelling of it. Running time:
$O(\varepsilon)$. Description: Since the effect of isolated vertices of $G$ on the folio is clear,
we may arrange (by deleting them) that $G$ has no isolated vertices. Let $z$ be a leaf of $T$, and
number the edges of $T$ as $f_1, \dots, f_m$, where $m = |E(T)|$, so that the numbers on every path
leaving $z$ are decreasing. (Our branch-decomposition in applications usually comes already equipped
with such a numbering; but if not, one can be found in time $O(\varepsilon)$.) For $1 \le i \le m$,
let $S_i, T_i$ be the components of $T \setminus f_i$, with $z \in V(S_i)$. Let $A_i$ be the
subgraph of $G$ formed by the edges $e$ with $\tau(e) \in V(S_i)$, and their ends; and define $B_i$
similarly. Since $G$ has no isolated vertices, $(A_i, B_i)$ is a separation of $G$ of order $\le
\omega$. Let $Z_i = (V(A_i) \cup Z) \cap V(B_i)$. We shall compute the $\delta$-folio of $B_i$
relative to $Z_i$ for each $i$, by a recursion as follows. At the start of the $i$ th iteration, the
$\delta$-folio of $B_j$ relative to $Z_j$, has been determined for $1 \le j < i$. (!) If $i \le m$
and $|V(T_i)| = 1$ then $|E(B_i)| = 1$ and $|V(B_i)| \le 2$. We determine the folio of $Z_i$ in
$B_i$ and return to (1) for the next iteration. (2) If $i \le m$ and $|V(T_i)| > 1$, let $f_j, f_k$
be the two edges of $T_i$ with a common end with $f_i$. Then $j, k < i$, and $(B_j, B_k)$ is a
separation of $B_i$, and the $\delta$-folios of $B_j$ relative to $Z_j$ and $B_k$ relative to $Z_k$
have already been determined. Since $V(B_j \cap B_k) \subseteq Z_j \cap Z_k$ we can calculate the
$\delta$-folio of $B_j \cup B_k$ relative to $Z_j \cup Z_k$ from this information, by (2.2). Since
$Z_i \subseteq Z_j \cup Z_k$ and $B_j \cup B_k = B_i$, the $\delta$-folio of $B_i$ relative to $Z_i$
can be calculated by (2.1). (Note that, since $\delta$-folios have size bounded by a constant, these
calculations take constant time.) We return to (1) for the next iteration. (3) If $i = m + 1$, the
folio of $B_m$ relative to $Z_m$ has been determined. We determine the $\delta$-folio of $A_m$
relative to $(Z \cup V(B_m)) \cap V(A_m)$ (this is easy, since $|V(A_m)| \le 2$), and we use (2.1)
and (2.2) to determine the $\delta$-folio of $Z$ in $A_m \cup B_m = G$. (4) For each member of the
$\delta$-folio of $Z$ in $G$ (up to isomorphism) we backtrack through this computation to compute a
corresponding model, in the natural way."

, numbered alias for `algorithm_4_1_correct`. -/
theorem theorem_4_1 {α : Type u} {β : Type v} [Nonempty α] [Nonempty β] {k : ℕ} (G : Digraph α β)
    (hVG : G.vertexSet.Finite) (Z : Set α) (hZ : Z ⊆ G.vertexSet) (r : Fin k → α)
    (hr : ∀ i, r i ∈ G.vertexSet) (δ : ℕ) :
    (∃ (vMod : RootedDigraph ℕ ℕ k → ℕ → Digraph α β)
       (eMod : RootedDigraph ℕ ℕ k → ℕ → β),
       IsDeltaFolioModelling (RootedDigraph.mk G r hr) δ vMod eMod) ∧
    (∀ {A_m B_m G' A_m' B_m' : Digraph α β},
      G.IsSeparation A_m B_m →
      G'.IsSeparation A_m' B_m' →
      Z ⊆ G'.vertexSet →
      (Z ∪ B_m.vertexSet) ∩ A_m.vertexSet = (Z ∪ B_m'.vertexSet) ∩ A_m'.vertexSet →
      (A_m.vertexSet ∪ Z) ∩ B_m.vertexSet = (A_m'.vertexSet ∪ Z) ∩ B_m'.vertexSet →
      HasSameDeltaFolioRel A_m A_m' δ ((Z ∪ B_m.vertexSet) ∩ A_m.vertexSet) →
      HasSameDeltaFolioRel B_m B_m' δ ((A_m.vertexSet ∪ Z) ∩ B_m.vertexSet) →
      HasSameDeltaFolioRel G G' δ Z) :=
  GM13.theorem_4_1_proof G hVG Z hZ r hr δ

open scoped Classical in
open Function Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM16 in
/-- **Graph Minors XIII, (4.2) Theorem** (page 76):
"For every planar graph $H$ there is a number $\omega$ such that every graph with branch-width
$\ge \omega$ has a minor isomorphic to $H$." -/
theorem theorem_4_2 {α : Type u} {β : Type v} {α' : Type u_1} {β' : Type u_2} (H : Graph α' β')
    (hPlanar : IsPlanar H) :
    ∃ ω : ℕ, 2 ≤ ω ∧ ∀ (G : Graph α β), V(G).Finite → E(G).Finite →
    ¬ GraphBranchWidthLE G (ω - 1) → IsIsoMinor H G :=
  GM13.theorem_4_2_proof H hPlanar

open GraphMinor.Compute GraphMinor GM13 Graph Classical in
/-- **Graph Minors XIII, (4.3)**, pages 76–77:
"Let $\mathcal{F}$ be a minor-closed class of graphs such that some planar graph is not in
$\mathcal{F}$. Then there is an algorithm to determine whether $G \in \mathcal{F}$ with running
time $O(v^2)$."

This reusable recognition result takes only minor closure and a finite excluded
planar graph. It derives the finite obstruction list, the width cutoff, and all
subroutine specifications. The input size is `(n + 1)²`, so a linear bound in
`alg44Size` is the asserted quadratic bound in the number of vertices.

Step (1) keeps at most `δ + 1` edges between two distinct vertices, not `δ` as printed, since the
printed cutoff can lose a minor. See the correction to (4.3) in `corrections/GM13.md`. -/
theorem algorithm_4_3 (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ)))
    (hclosed : ∀ ⦃G₁ G₂ : Graph ℕ (ℕ × ℕ × ℕ)⦄, V(G₁).Finite → E(G₁).Finite → V(G₂).Finite →
      E(G₂).Finite → IsIsoMinor G₁ G₂ → G₂ ∈ ℱ → G₁ ∈ ℱ) (H₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (hVH₀ : V(H₀).Finite) (hEH₀ : E(H₀).Finite) (hPlanar₀ : IsPlanar H₀) (hH₀_not : H₀ ∉ ℱ) :
    ∃ P : Cmd,
    ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
      (fun x s => s.regs outReg = if x.G.toGMDigraph.toGraph ∈ ℱ then 1 else 0)
      P (fun size => size) :=
  Compute.gm13_algorithm_4_3 ℱ hclosed H₀ hVH₀ hEH₀ hPlanar₀ hH₀_not

open scoped Classical in
open Function Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM16 in
/-- **Graph Minors XIII, (4.3)** (page 76):
"Let $\mathcal{F}$ be a minor-closed class of graphs such that some planar graph is not in
$\mathcal{F}$. Then there is an algorithm to determine whether $G \in \mathcal{F}$ with running
time $O(v^2)$."

This theorem gives the data fixed at the start of the proof: the finite excluded-minor list `B`
(from Graph Minors IV, (1.4), via `exists_finite_excluded_minors_of_planar`), the number `ω` of
(4.2), and `δ`, the largest number of vertices or edges of a graph in `B`. The four steps of the
algorithm are the program `Compute.alg43Prog`; Step (1) is proved in
`GraphMinor/Compute/GM13PairCapMinor.lean`. -/
theorem theorem_4_3 {α : Type u} {β : Type v} [Nonempty β] (ℱ : Set (Graph α β))
    (hclosed : ∀ ⦃G₁ G₂ : Graph α β⦄, V(G₁).Finite → E(G₁).Finite → V(G₂).Finite → E(G₂).Finite →
      IsIsoMinor G₁ G₂ → G₂ ∈ ℱ → G₁ ∈ ℱ) (H₀ : Graph α β) (hVH₀ : V(H₀).Finite)
    (hEH₀ : E(H₀).Finite) (hPlanar₀ : IsPlanar H₀) (hH₀_not : H₀ ∉ ℱ) :
    ∃ (B : Finset (Graph α β)) (ω δ : ℕ),
    H₀ ∈ B ∧
    2 ≤ ω ∧
    (∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ V(H).ncard ≤ δ ∧ E(H).ncard ≤ δ ∧ H ∉ ℱ) ∧
    (∀ G : Graph α β, V(G).Finite → E(G).Finite →
      (G ∈ ℱ ↔ ∀ H ∈ B, ¬ IsIsoMinor H G)) ∧
    (∀ G : Graph α β, V(G).Finite → E(G).Finite →
      ¬ GraphBranchWidthLE G (ω - 1) → G ∉ ℱ) :=
  GM13.theorem_4_3_proof ℱ hclosed H₀ hVH₀ hEH₀ hPlanar₀ hH₀_not

open scoped BigOperators in
open GraphMinor.Compute SimpleGraph in
/-- **GM XIII (4.4) Algorithm joined with `gm13_algorithm_3_3` (`Join433.lean`) and
`GM13.theorem_4_2_proof`
(`Join413.lean`) (page 77)**:
"Let $H$ be a planar graph. ...
(4.4) **Algorithm.**
*Input:* A graph $G$.
*Output:* Decides if there is a model of $H$ in $G$, and outputs such a model if one exists.
*Running time:* $O(v^2)$." -/
theorem algorithm_4_4 {p : ℕ} (edgesH : List (Fin p × Fin p))
    (hPlanar : IsPlanar (targetGMGraph p edgesH)) :
    ∃ (P44 : Cmd),
    ComputesArrRelInTime alg44Size encAlg44In (IsAlg44Output edgesH) P44 (fun m => m) :=
  Compute.gm13_algorithm_4_4 edgesH hPlanar

open scoped Classical in
open Function Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM16 in
/-- **Graph Minors XIII, (4.4)** (page 77): "Algorithm. Input: A graph $G$. Output: Decides if there
is a model of $H$ in $G$, and outputs such a model if one exists. Running time: $O(v^2)$.
Description: Let $\omega$ be as in (4.2), with $\omega \ge 2$. (1) We choose a maximal subgraph
$G_1$ of $G$ with at most $|E(H)|$ loops at every vertex and at most $|E(H)| + 1$ edges mutually
parallel. There is a model of $H$ in $G$ if and only if there is one in $G_1$. (2) We apply (3.3) to
$G_1$. We obtain a subgraph $G_2$ of $G_1$, and a branch-decomposition of $G_2$ of width $\le
3\omega$, such that either $G_2 = G_1$ or $G_2$ has branch-width $\ge \omega$. From the choice of
$\omega$, it follows that either $G_2 = G_1$ or there is a model of $H$ in $G_2$. Consequently there
is a model of $H$ in $G_1$ if and only if there is one in $G_2$. (3) We test if $G_2$ has an
$H$-minor, and if so find a model of it in $G_2$, by using (4.1) to compute the
$\varepsilon(H)$-folio of $G_2$ relative to $\emptyset$ and a modelling of it."

, numbered alias for `algorithm_4_4_correct`. -/
theorem theorem_4_4 {α : Type u} {β : Type v} {α' : Type u_1} {β' : Type u_2} [Nonempty β]
    (H : Graph α' β') (hVH : V(H).Finite) (hEH : E(H).Finite) (hPlanar : IsPlanar H) :
    ∃ ω : ℕ, 2 ≤ ω ∧
    (∀ G : Graph α β, V(G).Finite → E(G).Finite →
      ¬ GraphBranchWidthLE G (ω - 1) → IsIsoMinor H G) ∧
    (∀ D : Digraph α β, D.IsFinite →
      let δ := max V(H).ncard E(H).ncard
      ∃ D₁ : Digraph α β, D₁.IsSubdigraph D ∧ D₁.vertexSet = D.vertexSet ∧
        HasSameDeltaFolioRel D D₁ δ ∅ ∧
        D₁.HasBoundedMultiplicity δ ∧
        (IsIsoMinor H D.toGraph ↔ IsIsoMinor H D₁.toGraph) ∧
        (2 ≤ E(D₁.toGraph).ncard →
          ∃ (G₂ : Graph α β) (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : β → ι),
            G₂ ≤ D₁.toGraph ∧
            2 ≤ E(G₂).ncard ∧
            IsGraphBranchDecomposition G₂ T τ ∧
            graphBranchDecompWidth G₂ T τ ≤ 3 * ω ∧
            (G₂ = D₁.toGraph ∨ IsIsoMinor H G₂) ∧
            (IsIsoMinor H D₁.toGraph ↔ IsIsoMinor H G₂))) :=
  GM13.theorem_4_4_proof H hVH hEH hPlanar

/-! ## Section 5. Generic Folios -/

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface in
/-- **Graph Minors XIII, (5.1)** (page 78):
"Let $G$ be a digraph with $|V(G)| \ge 2\xi + 3\delta$, and let $Z \subseteq V(G)$ with
$|Z| = \xi$. Suppose that $u, v \in Z$, for all distinct $u, v \in V$ that are non-adjacent in $G$.
Then the $\delta$-folio of $G$ relative to $Z$ is generic." -/
theorem theorem_5_1 {α : Type u} {β : Type v} [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ δ : ℕ}
    (hfin : G.vertexSet.Finite) (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard = ξ)
    (hVcard : 2 * ξ + 3 * δ ≤ G.vertexSet.ncard)
    (hadj : ∀ ⦃u v : α⦄, u ∈ G.vertexSet → v ∈ G.vertexSet → u ≠ v → ¬ G.toGraph.Adj u v → u ∈ Z ∧
      v ∈ Z) :
    IsGenericDeltaFolioRel G δ Z :=
  theorem_5_1_proof hfin hZ hZcard hVcard hadj

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface in
/-- **Graph Minors XIII, (5.2)** (pages 78–79):
"*Let $G$ be a digraph, let $Z \subseteq V(G)$ with $|Z| = \xi$, and let $k = 2\xi + 3\delta$.
Suppose that there are $k$ non-null connected subgraphs $G_1, \dots, G_k$ of $G$, mutually
vertex-disjoint, such that*

(i) *$|Z \cap V(G_i)| = 1$ ($1 \le i \le \xi$), and (hence) $Z \cap V(G_i) = \emptyset$ ($\xi + 1
\le i \le k$)*
…
(ii) *for $1 \le i < j \le k$, if there is no edge of $G$ between $G_i$ and $G_j$ then $i, j \le
\xi$.*

*Then the $\delta$-folio of $G$ relative to $Z$ is generic.*" -/
theorem theorem_5_2 {α : Type u} {β : Type v} [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ δ k : ℕ}
    (hZ : Z ⊆ G.vertexSet) (hZfin : Z.Finite) (hZcard : Z.ncard = ξ) (hk : k = 2 * ξ + 3 * δ)
    {sub : Fin k → Digraph α β} (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hconn : ∀ i : Fin k, (sub i).IsConnected)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hZi : ∀ i : Fin k, i.1 < ξ → (Z ∩ (sub i).vertexSet).ncard = 1)
    (hZempty : ∀ i : Fin k, ξ ≤ i.1 → Z ∩ (sub i).vertexSet = ∅)
    (hadj : ∀ i j : Fin k, i < j → ¬ G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet → i.1 <
      ξ ∧ j.1 < ξ) :
    IsGenericDeltaFolioRel G δ Z :=
  theorem_5_2_proof hZ hZfin hZcard hk hsub hconn hdisj hZi hZempty hadj

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (5.3)** (pages 79–80):
"*Let $G$ be a graph and let $Z \subseteq V(G)$ with $|Z| = \xi$. Let $k \ge \lfloor
\frac{3}{2}\xi \rfloor$ and let $G_1, \dots, G_k$ be subgraphs of $G$, mutually vertex-disjoint,
such that*

(i) *for $1 \le i \le k$, either $G_i$ is connected or every component of $G_i$ has a vertex in
$Z$,*

(ii) *for $1 \le i < j \le k$, either $V(G_i)$ and $V(G_j)$ both meet $Z$ or there is an edge of
$G$ between $G_i$ and $G_j$, and*

(iii) *for $1 \le i \le k$, there is no separation $(A, B)$ of $G$ of order $< \xi$ with $Z
\subseteq V(A)$ and with $A \cap G_i$ null.*

*Then for some $\mu$ with $0 \le \mu \le \xi$ there are $\kappa = k - \lfloor \frac{1}{2}(\xi -
\mu) \rfloor$ non-null connected subgraphs $H_1, \dots, H_\kappa$ of $G$, mutually
vertex-disjoint, such that*

(a) *$|V(H_i) \cap Z| = 1$ ($1 \le i \le \xi$) and $V(H_i) \cap Z = \emptyset$ ($\xi + 1 \le i
\le \kappa$), and*

(b) *for $1 \le i < j \le \kappa$, if there is no edge of $G$ between $H_i$ and $H_j$ then $i, j
\le \mu$.*

*In particular, for any $\delta \ge 0$, if $k \ge \lfloor \frac{5}{2}\xi \rfloor + 3\delta$ and
$G$ is a digraph then the $\delta$-folio of $G$ relative to $Z$ is generic.*"

Here `G` is a digraph from the start, as the second assertion needs. The first assertion only
uses its underlying graph: connectivity, edges between subgraphs and separations ignore the
directions. -/
theorem theorem_5_3 {α : Type u} {β : Type v} [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ k : ℕ}
    (hfin : G.IsFinite) (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard = ξ) (hk : (3 * ξ) / 2 ≤ k)
    {sub : Fin k → Digraph α β} (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hi : ∀ i : Fin k, (sub i).IsConnected ∨
      ((sub i).vertexSet.Nonempty ∧ ∀ u ∈ (sub i).vertexSet, ∃ z ∈ Z ∩ (sub i).vertexSet,
        Nonempty (GraphWalk (sub i).toGraph u z)))
    (hii : ∀ i j : Fin k, i < j →
      (((sub i).vertexSet ∩ Z).Nonempty ∧ ((sub j).vertexSet ∩ Z).Nonempty) ∨
      G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hiii : ∀ (i : Fin k) (A B : Digraph α β), G.IsSeparation A B → Z ⊆ A.vertexSet →
      (G.interSub A (sub i)).IsNull → ξ ≤ Digraph.separationOrder A B) :
    (∃ (μ : ℕ) (_ : μ ≤ ξ) (H : Fin (k - (ξ - μ) / 2) → Digraph α β),
      (∀ i, (H i).IsSubdigraph G) ∧
      (∀ i, (H i).IsConnected) ∧
      Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) ∧
      (∀ i : Fin (k - (ξ - μ) / 2),
        (i.1 < ξ → ((H i).vertexSet ∩ Z).ncard = 1) ∧
        (ξ ≤ i.1 → (H i).vertexSet ∩ Z = ∅)) ∧
      (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
        ¬ G.HasEdgeBetween (H i).vertexSet (H j).vertexSet → i.1 < μ ∧ j.1 < μ)) ∧
    (∀ δ : ℕ, (5 * ξ) / 2 + 3 * δ ≤ k → IsGenericDeltaFolioRel G δ Z) :=
  GM13.theorem_5_3_proof hfin hZ hZcard hk hsub hdisj hi hii hiii

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (5.4)** (page 82):
"Let $G$ be a graph and let $Z \subseteq V(G)$ with $|Z| = \xi$. Let $k \ge \lfloor \frac{3}{2}\xi
\rfloor$ and let $G_1, \dots, G_k$ be connected subgraphs of $G$, mutually vertex-disjoint, such
that for $1 \le i < j \le k$ there is an edge of $G$ between $G_i$ and $G_j$. Suppose that there is
no separation $(A, B)$ of $G$ of order $< |Z|$ with $Z \subseteq V(A)$ and $A \cap G_i$ null for
some $i$ ($1 \le i \le k$). Then for every partition $(Z_1, \dots, Z_n)$ of $Z$ into non-empty
subsets, there are $n$ connected subgraphs $T_1, \dots, T_n$ of $G$, mutually disjoint and with
$V(T_t) \cap Z = Z_t$ ($1 \le t \le n$)." -/
theorem theorem_5_4 {α : Type u} {β : Type v} {G : Digraph α β} {Z : Set α} {ξ k n : ℕ}
    (hfin : G.IsFinite) (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard = ξ) (hk : (3 * ξ) / 2 ≤ k)
    {sub : Fin k → Digraph α β} (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hconn : ∀ i : Fin k, (sub i).IsConnected)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hadj : ∀ i j : Fin k, i < j → G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hno_sep : ∀ (i : Fin k) (A B : Digraph α β), G.IsSeparation A B → Z ⊆ A.vertexSet →
      (G.interSub A (sub i)).IsNull → ξ ≤ Digraph.separationOrder A B) (Z_part : Fin n → Set α)
    (hZ_nonempty : ∀ t : Fin n, (Z_part t).Nonempty)
    (hZ_disj : Pairwise (fun t₁ t₂ : Fin n => Disjoint (Z_part t₁) (Z_part t₂)))
    (hZ_union : (⋃ t : Fin n, Z_part t) = Z) :
    ∃ T : Fin n → Digraph α β,
    (∀ t : Fin n, (T t).IsSubdigraph G) ∧
    (∀ t : Fin n, (T t).IsConnected) ∧
    Pairwise (fun t₁ t₂ : Fin n => Disjoint (T t₁).vertexSet (T t₂).vertexSet) ∧
    (∀ t : Fin n, (T t).vertexSet ∩ Z = Z_part t) :=
  GM13.theorem_5_4_proof hfin hZ hZcard hk hsub hconn hdisj hadj hno_sep Z_part hZ_nonempty hZ_disj hZ_union

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (5.5)** (page 83):
"*Let $p \ge 1$ be an integer, and let $G$ be a non-null simple graph with*

$$
|E(G)| \ge 2.68 p(\log_2(p))^{1/2} |V(G)|.
$$

*Then $G$ has a $K_p$-minor.*"

Thomason's paper gives the constant 2.68 only asymptotically, so we prove the bound for every
$p \ge 1$: `GraphMinor.Thomason.thomason84` in `GraphMinor/Thomason/UniformTheorem.lean`. For
$p \ge 51$ the proof follows the note `docs/thomason/uniform_minor_bound.tex`. -/
theorem theorem_5_5 {α : Type u} {β : Type v} {G : Graph α β} {p : ℕ} (hp : 1 ≤ p)
    (hfinV : V(G).Finite) (hfinE : E(G).Finite) (hne : V(G).Nonempty) (hsimple : IsSimpleGraph G)
    (hedges : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) * (V(G).ncard : ℝ) ≤
      (E(G).ncard : ℝ)) :
    HasGraphModel (completeGraph p) G :=
  GM13.theorem_5_5_proof hp hfinV hfinE hne hsimple hedges

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (5.6)** (page 83):
"For every integer $p \ge 0$, every $2p$-connected simple graph $G$ with $|E(G)| \ge 8.04 p(\log_2
3p)^{1/2} |V(G)|$ is $p$-linked."

The proof uses (5.5) with $3p$ in place of $p$. We prove (5.5) for every $p \ge 1$
(`GraphMinor.Thomason.thomason84`), since Thomason's paper gives its constant only
asymptotically. -/
theorem theorem_5_6 {α : Type u} {β : Type v} {G : Graph α β} {p : ℕ} (hfinV : V(G).Finite)
    (hfinE : E(G).Finite) (hsimple : IsSimpleGraph G) (hconn : IsKConnectedGraph G (2 * p))
    (hedges : (8.04 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 (3 * p)) * (V(G).ncard : ℝ) ≤
      (E(G).ncard : ℝ)) :
    IsPLinked G p :=
  GM13.theorem_5_6_proof hfinV hfinE hsimple hconn hedges

/-! ## Section 6. What To Do with a Clique -/

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (6.1)** (pages 83–84):
"*Let $G$ be a digraph and let $Z \subseteq V(G)$ with $|Z| \le \xi$. Let $k = \lfloor
\frac{5}{2}\xi \rfloor + 3\delta + 1$ and let $G_1, \dots, G_k$ be mutually vertex-disjoint
connected subgraphs of $G$ such that for $1 \le i < j \le k$ there is an edge of $G$ between
$G_i$ and $G_j$. Let $(A, B)$ be a separation of $G$ such that*

*(i) $A \cap G_i$ is null for some $i$ ($1 \le i \le k$)*

*(ii) $Z \subseteq V(A)$*
…
*(iii) subject to (i) and (ii), $(A, B)$ has minimum order*

*(iv) subject to (i), (ii), and (iii), $A$ is maximal.*

*Let $v \in V(B) - V(A)$. Then $v$ is irrelevant to the $\delta$-folio of $G$ relative to $Z$.*" -/
theorem theorem_6_1 {α : Type u} {β : Type v} [Nonempty β] {G A B : Digraph α β} {Z : Set α}
    {ξ δ k : ℕ} (hfin : G.IsFinite) (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard ≤ ξ)
    (hk : k = (5 * ξ) / 2 + 3 * δ + 1) {sub : Fin k → Digraph α β}
    (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G) (hconn : ∀ i : Fin k, (sub i).IsConnected)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hadj : ∀ i j : Fin k, i < j → G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hsep : G.IsSeparation A B) (hi : ∃ i : Fin k, (G.interSub A (sub i)).IsNull)
    (hii : Z ⊆ A.vertexSet)
    (hiii : ∀ A' B' : Digraph α β, G.IsSeparation A' B' →
      (∃ i : Fin k, (G.interSub A' (sub i)).IsNull) → Z ⊆ A'.vertexSet →
      Digraph.separationOrder A B ≤ Digraph.separationOrder A' B')
    (hiv : ∀ A' B' : Digraph α β, G.IsSeparation A' B' →
      (∃ i : Fin k, (G.interSub A' (sub i)).IsNull) → Z ⊆ A'.vertexSet →
      Digraph.separationOrder A' B' ≤ Digraph.separationOrder A B → A.IsSubdigraph A' →
      A'.vertexSet = A.vertexSet ∧ A'.edgeSet = A.edgeSet) {v : α}
    (hv : v ∈ B.vertexSet \ A.vertexSet) :
    IsIrrelevantVertex G δ Z v :=
  GM13.theorem_6_1_proof hfin hZ hZcard hk hsub hconn hdisj hadj hsep hi hii hiii hiv hv

open scoped BigOperators in
open GraphMinor.Compute SimpleGraph in
/-- **Graph Minors XIII, (6.2)** (pages 84–85): "Algorithm. Input: A digraph $G$, a subset $Z
\subseteq V(G)$ with $|Z| \le \xi$, and $p$ mutually vertex-disjoint connected subgraphs $G_1,
\dots, G_p$ of $G$ such that for $1 \le i < j \le p$ there is an edge of $G$ between $G_i$ and
$G_j$. Output: A vertex of $G$ irrelevant to the $\delta$-folio of $G$ relative to $Z$. Running
time: $O(\varepsilon)$. Description: For each $i$ with $1 \le i \le p$ such that $Z \cap V(G_i) =
\emptyset$ we find a separation $(A_i, B_i)$ of $G$ with $Z \subseteq V(A_i)$ and $A_i \cap G_i$
null, of minimum order and subject to that with $A_i$ maximal. (The usual max-flow min-cut algorithm
provides a “min-cut” which yields a separation $(A, B)$ with $A$"

GM XIII (6.2) Algorithm (pages 84–85):
for fixed integers `ξ, δ ≥ 0` and `p = ⌊5ξ/2⌋ + 3δ + 1` (`alg62Param ξ δ`), given a multi-digraph
`G`, a subset `Z ⊆ V(G)` with `|Z| ≤ ξ`, and `p` mutually vertex-disjoint connected subgraphs
`G_1, …, G_p` forming a model of `K_p` in `G`, `alg62EndToEndProg ξ δ` finds a vertex `v ∈ V(G_i)`
together with `i` and a separation `(V_A, V_B)` satisfying conditions (i)–(iv) of (6.1) in time
`O(s + 1)` (`s = G.size = |V(G)| + G.numActivePairs`). -/
theorem algorithm_6_2 (ξ δ : ℕ) :
    ComputesArrRelInTime (alg62Size (ξ := ξ) (δ := δ)) (encAlg62In ξ δ)
    (fun x out => IsValidAlg62Output x (decAlg62Out ξ δ x out))
    (alg62EndToEndProg ξ δ) (fun s => s + 1) :=
  Compute.gm13_algorithm_6_2 ξ δ

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (6.2)** (pages 84–85): "Algorithm. Input: A digraph $G$, a subset $Z
\subseteq V(G)$ with $|Z| \le \xi$, and $p$ mutually vertex-disjoint connected subgraphs $G_1,
\dots, G_p$ of $G$ such that for $1 \le i < j \le p$ there is an edge of $G$ between $G_i$ and
$G_j$. Output: A vertex of $G$ irrelevant to the $\delta$-folio of $G$ relative to $Z$. Running
time: $O(\varepsilon)$. Description: For each $i$ with $1 \le i \le p$ such that $Z \cap V(G_i) =
\emptyset$ we find a separation $(A_i, B_i)$ of $G$ with $Z \subseteq V(A_i)$ and $A_i \cap G_i$
null, of minimum order and subject to that with $A_i$ maximal. (The usual max-flow min-cut algorithm
provides a “min-cut” which yields a separation $(A, B)$ with $A$"

Mathematical statement of Algorithm (6.2). -/
theorem theorem_6_2 {α : Type u} {β : Type v} [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ δ p : ℕ}
    (hfin : G.IsFinite) (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard ≤ ξ)
    (hp : p = (5 * ξ) / 2 + 3 * δ + 1) {sub : Fin p → Digraph α β}
    (hsub : ∀ i : Fin p, (sub i).IsSubdigraph G) (hconn : ∀ i : Fin p, (sub i).IsConnected)
    (hdisj : Pairwise (fun i j : Fin p => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hadj : ∀ i j : Fin p, i < j → G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet) :
    ∃ (i : Fin p) (v : α), v ∈ (sub i).vertexSet ∧ v ∈ G.vertexSet \ Z ∧
    IsIrrelevantVertex G δ Z v :=
  GM13.theorem_6_2_proof hfin hZ hZcard hp hsub hconn hdisj hadj

open GraphMinor.Compute SimpleGraph in
/-- **Graph Minors XIII, (6.3)** (page 85): "Algorithm. Input: An integer $k > 0$ and a non-null
simple graph $G$ with $|E(G)| \ge k |V(G)|$. Output: A subset $X \subseteq V(G)$ such that (i) the
restriction of $G$ to $X$ is non-null and connected (ii) $N(X)$ is non-null, and (iii) every vertex
of $N(X)$ has $\ge k$ neighbours in $N(X)$. Running time: $O(\nu\varepsilon)$. Description: (1)
Choose a component $H$ of $G$ with $|E(H)| \ge k |V(H)|$, and choose $v_1 \in V(H)$. (2) We perform
a recursion. Set $X_1 = \{v_1\}$. At the start of the $i$ th step of the recursion we have a subset
$X_i \subseteq V(H)$ with $|X_i| = i$ such that $X_i$ meets at most $|N(X_i)| + k(i - 1)$ edges, and
such that the restriction of $G$ to $X_i$ is connected. (3) If there exists $v \in N(X_i)$ with $<
k$ neighbours in $N(X_i)$, we set $X_{i+1} = X_i \cup \{v\}$ and return for the next iteration. To
check the inequality, let $v$ have $d_1$ neighbours in $N(X_i)$ and $d_2$ in $V(H) - (X_i \cup
N(X_i))$. Then $$ |N(X_{i+1})| = |N(X_i)| - 1 + d_2 $$"

End-to-end `O(vε)` complexity theorem for GM XIII Algorithm (6.3) (`alg63EndToEndProg`):
from any initial state whose `inArr` holds `encAlg63In x`, `alg63EndToEndProg` terminates in at
most `C * (alg63Size x + 1)` steps (where `alg63Size x = x.n * x.G.edgeFinset.card = vε`) and
leaves a bit array in `outArr` decoding via `decAlg63Out x.n` to a subset `X ⊆ V(G)` satisfying
`IsAlg63Output x X`. -/
theorem algorithm_6_3 :
    ComputesArrRelInTime alg63Size encAlg63In
    (fun x out => IsAlg63Output x (decAlg63Out x.n out)) alg63EndToEndProg (fun s => s + 1) :=
  Compute.gm13_algorithm_6_3

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (6.3)** (pages 85–86): "Algorithm. Input: An integer $k > 0$ and a non-null
simple graph $G$ with $|E(G)| \ge k |V(G)|$. Output: A subset $X \subseteq V(G)$ such that (i) the
restriction of $G$ to $X$ is non-null and connected (ii) $N(X)$ is non-null, and (iii) every vertex
of $N(X)$ has $\ge k$ neighbours in $N(X)$. Running time: $O(\nu\varepsilon)$. Description: (1)
Choose a component $H$ of $G$ with $|E(H)| \ge k |V(H)|$, and choose $v_1 \in V(H)$. (2) We perform
a recursion. Set $X_1 = \{v_1\}$. At the start of the $i$ th step of the recursion we have a subset
$X_i \subseteq V(H)$ with $|X_i| = i$ such that $X_i$ meets at most $|N(X_i)| + k(i - 1)$ edges, and
such that the restriction of $G$ to $X_i$ is connected. (3) If there exists $v \in N(X_i)$ with $<
k$ neighbours in $N(X_i)$, we set $X_{i+1} = X_i \cup \{v\}$ and return for the next iteration. To
check the inequality, let $v$ have $d_1$ neighbours in $N(X_i)$ and $d_2$ in $V(H) - (X_i \cup
N(X_i))$. Then $$ |N(X_{i+1})| = |N(X_i)| - 1 + d_2 $$"

Mathematical statement of Algorithm (6.3). -/
theorem theorem_6_3 {α : Type u} {β : Type v} {G : Digraph α β} {k : ℕ} (hk : 0 < k)
    (hfin : G.IsFinite) (hne : G.vertexSet.Nonempty) (hsimple : IsSimpleGraph G.toGraph)
    (hedges : k * G.vertexSet.ncard ≤ G.edgeSet.ncard) :
    ∃ X ⊆ G.vertexSet,
    (G.induce X).IsConnected ∧
    (G.extNeighbors X).Nonempty ∧
    ∀ v ∈ G.extNeighbors X, k ≤ ({u ∈ G.extNeighbors X | G.toGraph.Adj v u}).ncard :=
  GM13.theorem_6_3_proof hk hfin hne hsimple hedges

open scoped BigOperators in
open GraphMinor.Compute SimpleGraph in
/-- **Graph Minors XIII, (6.4)** (page 86): "Algorithm. Input: A non-null simple graph $G$ with
$|E(G)| \ge 2^{p-3} |V(G)|$. Output: A model of $K_p$ in $G$. Running time: $O(v^2)$. Description:
We may assume that $p \ge 3$, for otherwise the problem is trivial. (1) Choose a subgraph $H
\subseteq G$ with $V(H) = V(G)$ and $|E(H)| = 2^{p-3} |V(H)|$. (2) We perform a recursion. Let $Y_1
= V(H)$. At the start of the $i$ th iteration we have $i-1$ disjoint connected subgraphs $G_1,
\dots, G_{i-1} \subseteq H$ and a non-null subset $Y_i \subseteq V(H) - V(G_1 \cup \dots \cup
G_{i-1})$ such that (i) there are at least $2^{p-2-i} |Y_i|$ edges of $H$ with both ends in $Y_i$,
(ii) every vertex in $Y_i$ has a neighbour in each of $V(G_1), \dots, V(G_{i-1})$, and (iii) for $1
\le j < j' \le i-1$, each vertex of $V(G_{j'})$ has a neighbour in $V(G_j)$. The $i$ th iteration
proceeds as follows. (3) We apply (6.3) to the restriction of $H$ to $Y_i$, taking $k = 2^{p-2-i}$.
We obtain $X \subseteq Y_i$ such that the restriction of $H$ to $X$ is non-null and connected, $N(X)
\cap Y_i$ is non-null, and every vertex of $N(X) \cap Y_i$ has at least $2^{p-2-i}$ neighbours in
$N(X) \cap Y_i$. We set $G_i$ to be the restriction of $H$ to $X$, and $Y_{i+1} = N(X) \cap Y_i$. If
$i = p-2$ the recursion terminates, and otherwise we return for the next iteration. (4) Let
$G_{p-1}, G_p$ be one-vertex graphs with $V(G_{p-1}) = \{u\}$, $V(G_p) = \{v\}$, for some adjacent
$u, v \in Y_{p-1}$. (These exist since $Y_{p-1} \ne \emptyset$ and every"

End-to-end `O(v²)` complexity theorem for GM XIII Algorithm (6.4) (`alg64EndToEndProg p`):
for any fixed parameter `p : ℕ` and any valid input `x : Alg64Input p` whose flat encoding
`encAlg64In p x` is placed in `inArr`, `alg64EndToEndProg p` terminates in `O((v + 1)²)` steps
(where `v = alg64Size p x = x.n`) and writes `p` bitsets in `outArr` decoding via
`decAlg64Out p x.n` to a model of `K_p` in `x.G` (`IsCliqueModel x.G p`). -/
theorem algorithm_6_4 (p : ℕ) :
    ComputesArrRelInTime (alg64Size p) (encAlg64In p)
    (fun x out => IsCliqueModel x.G p (decAlg64Out p x.n out))
    (alg64EndToEndProg p) (fun v => (v + 1) ^ 2) :=
  Compute.gm13_algorithm_6_4 p

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (6.4)** (pages 86–87): "Algorithm. Input: A non-null simple graph $G$ with
$|E(G)| \ge 2^{p-3} |V(G)|$. Output: A model of $K_p$ in $G$. Running time: $O(v^2)$. Description:
We may assume that $p \ge 3$, for otherwise the problem is trivial. (1) Choose a subgraph $H
\subseteq G$ with $V(H) = V(G)$ and $|E(H)| = 2^{p-3} |V(H)|$. (2) We perform a recursion. Let $Y_1
= V(H)$. At the start of the $i$ th iteration we have $i-1$ disjoint connected subgraphs $G_1,
\dots, G_{i-1} \subseteq H$ and a non-null subset $Y_i \subseteq V(H) - V(G_1 \cup \dots \cup
G_{i-1})$ such that (i) there are at least $2^{p-2-i} |Y_i|$ edges of $H$ with both ends in $Y_i$,
(ii) every vertex in $Y_i$ has a neighbour in each of $V(G_1), \dots, V(G_{i-1})$, and (iii) for $1
\le j < j' \le i-1$, each vertex of $V(G_{j'})$ has a neighbour in $V(G_j)$. The $i$ th iteration
proceeds as follows. (3) We apply (6.3) to the restriction of $H$ to $Y_i$, taking $k = 2^{p-2-i}$.
We obtain $X \subseteq Y_i$ such that the restriction of $H$ to $X$ is non-null and connected, $N(X)
\cap Y_i$ is non-null, and every vertex of $N(X) \cap Y_i$ has at least $2^{p-2-i}$ neighbours in
$N(X) \cap Y_i$. We set $G_i$ to be the restriction of $H$ to $X$, and $Y_{i+1} = N(X) \cap Y_i$. If
$i = p-2$ the recursion terminates, and otherwise we return for the next iteration. (4) Let
$G_{p-1}, G_p$ be one-vertex graphs with $V(G_{p-1}) = \{u\}$, $V(G_p) = \{v\}$, for some adjacent
$u, v \in Y_{p-1}$. (These exist since $Y_{p-1} \ne \emptyset$ and every"

Mathematical statement of Algorithm (6.4). -/
theorem theorem_6_4 {α : Type u} {β : Type v} [Nonempty β] {G : Digraph α β} {p : ℕ} (hp : 1 ≤ p)
    (hfin : G.IsFinite) (hne : G.vertexSet.Nonempty) (hsimple : IsSimpleGraph G.toGraph)
    (hedges : 2 ^ (p - 3) * G.vertexSet.ncard ≤ G.edgeSet.ncard) :
    HasGraphModel (GM16.completeGraph p) G.toGraph :=
  GM13.theorem_6_4_proof hp hfin hne hsimple hedges

open GraphMinor.Compute SimpleGraph in
/-- **Graph Minors XIII, (6.5)** (page 87): "Algorithm. Input: A digraph $G$ and a subset $Z
\subseteq V(G)$ with $|Z| \le \xi$. Output: A subdigraph $G'$ of $G$ with $Z \subseteq V(G')$, such
that $G$ and $G'$ have the same $\delta$-folio relative to $Z$, and such that $|E(G')| \le
C|V(G')|$, where $C = \delta + 2(\delta+1)2^{p-3}$ and where $p = \lfloor\frac{5}{2}\xi\rfloor +
3\delta + 1$. Running time: $O(v^3)$. Description: (1) Let $H$ be a maximal subdigraph of $G$ with
at most $\delta$ loops at each vertex and at most $\delta+1$ edges with head $u$ and tail $v$, for
all distinct $u, v \in V(G)$. Certainly $G$ and $H$ have the same $\delta$-folios relative to $Z$.
(2) We set $G_1 = H$ and perform a recursion. At the start of the $i$ th iteration we have a
subdigraph $G_i$ of $H$ with $Z \subseteq V(G_i)$ and $|V(G_i)| = |V(H)| - i + 1$ such that $G_i$
and $H$ (and hence $G$) have the same $\delta$-folios relative to $Z$. If $|E(G_i)| \le C|V(G_i)|$
we set $G' = G_i$ and stop. Otherwise, the $i$ th iteration proceeds as follows. (3) Let $J_i$ be
the simple (undirected) graph underlying $G_i$. Then $$\begin{aligned} (\delta + 2(\delta+1)2^{p-3})
|V(J_i)| = C|V(G_i)| &\le |E(G_i)| \\ &\le \delta |V(J_i)| + 2(\delta+1) |E(J_i)| \end{aligned}$$
and so $2^{p-3} |V(J_i)| \le |E(J_i)|$. We apply (6.4) to $J_i$ and obtain a model of $K_p$ in $J_i$
(and hence in $G_i$). (4) We apply (6.2) to $G_i$ and the model of $K_p$ and find a vertex $v$ of
$G_i$ irrelevant to the $\delta$-folio of $G_i$ relative to $Z$. We set $G_{i+1} = G_i \setminus v$
and return for the next iteration."

(Robertson–Seymour, page 85 / page 87):
For fixed `ξ, δ : ℕ`, with `p = ⌊5ξ/2⌋ + 3δ + 1` (`alg62Param ξ δ`) and
`C = δ + 2(δ + 1)2^{p - 3}` (`alg65Const ξ δ`), there is a Word RAM program
`alg65EndToEndProg ξ δ` with running time `O(v³)` (`T(v) = (v + 1)³` with `v = |V(G)|`)
that takes any multi-digraph `G` and `Z ⊆ V(G)` with `|Z| ≤ ξ` and outputs a subdigraph `G'`
of `G` with `Z ⊆ V(G')` and `|E(G')| ≤ C |V(G')|` together with a valid Algorithm (6.5)
vertex-deletion trace from `G.cap δ` to `G'`. -/
theorem algorithm_6_5 (ξ δ : ℕ) :
    ComputesArrRelInTime (alg65Size (ξ := ξ) (δ := δ)) (encAlg65In (ξ := ξ) (δ := δ))
    (fun x out => IsValidAlg65Output ξ δ x (decAlg65Out x.n out))
    (alg65EndToEndProg ξ δ) (fun s => (s + 1) ^ 3) :=
  Compute.gm13_algorithm_6_5 ξ δ

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (6.5)** (page 87): "Algorithm. Input: A digraph $G$ and a subset $Z
\subseteq V(G)$ with $|Z| \le \xi$. Output: A subdigraph $G'$ of $G$ with $Z \subseteq V(G')$, such
that $G$ and $G'$ have the same $\delta$-folio relative to $Z$, and such that $|E(G')| \le
C|V(G')|$, where $C = \delta + 2(\delta+1)2^{p-3}$ and where $p = \lfloor\frac{5}{2}\xi\rfloor +
3\delta + 1$. Running time: $O(v^3)$. Description: (1) Let $H$ be a maximal subdigraph of $G$ with
at most $\delta$ loops at each vertex and at most $\delta+1$ edges with head $u$ and tail $v$, for
all distinct $u, v \in V(G)$. Certainly $G$ and $H$ have the same $\delta$-folios relative to $Z$.
(2) We set $G_1 = H$ and perform a recursion. At the start of the $i$ th iteration we have a
subdigraph $G_i$ of $H$ with $Z \subseteq V(G_i)$ and $|V(G_i)| = |V(H)| - i + 1$ such that $G_i$
and $H$ (and hence $G$) have the same $\delta$-folios relative to $Z$. If $|E(G_i)| \le C|V(G_i)|$
we set $G' = G_i$ and stop. Otherwise, the $i$ th iteration proceeds as follows. (3) Let $J_i$ be
the simple (undirected) graph underlying $G_i$. Then $$\begin{aligned} (\delta + 2(\delta+1)2^{p-3})
|V(J_i)| = C|V(G_i)| &\le |E(G_i)| \\ &\le \delta |V(J_i)| + 2(\delta+1) |E(J_i)| \end{aligned}$$
and so $2^{p-3} |V(J_i)| \le |E(J_i)|$. We apply (6.4) to $J_i$ and obtain a model of $K_p$ in $J_i$
(and hence in $G_i$). (4) We apply (6.2) to $G_i$ and the model of $K_p$ and find a vertex $v$ of
$G_i$ irrelevant to the $\delta$-folio of $G_i$ relative to $Z$. We set $G_{i+1} = G_i \setminus v$
and return for the next iteration."

Mathematical statement of Algorithm (6.5). -/
theorem theorem_6_5 {α : Type u} {β : Type v} [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ δ : ℕ}
    (hfin : G.IsFinite) (hZ : Z ⊆ G.vertexSet) (hZ_card : Z.ncard ≤ ξ) :
    let p := 5 * ξ / 2 + 3 * δ + 1
    let C := δ + 2 * (δ + 1) * 2 ^ (p - 3)
    ∃ G' : Digraph α β, G'.IsSubdigraph G ∧ Z ⊆ G'.vertexSet ∧
      HasSameDeltaFolioRel G G' δ Z ∧
      G'.edgeSet.ncard ≤ C * G'.vertexSet.ncard :=
  GM13.theorem_6_5_proof hfin hZ hZ_card

/-! ## Section 7. Walls -/

open GraphMinor.Compute GraphMinor GM13 in
/-- **Graph Minors XIII, (7.1)**, page 89:
"For $h \ge 2$, even, if every graph with branch-width $\ge \omega/3$ has a minor isomorphic to the
elementary wall of height $h$, then there is an algorithm as in (7.2), with running time $O(v^2 +
\varepsilon)$."
The integer threshold `(ω + 2) / 3` expresses branch-width at least `ω/3`.
The decomposition search uses `ω / 3`, so its output width is at most `ω`. -/
theorem algorithm_7_1 (h ω : ℕ) (hh : 2 ≤ h) (_he : Even h)
    (h71 : HasPlanarGridThreshold (elemWallEdges h) ((ω + 2) / 3)) :
    ∃ P : Cmd,
    ComputesArrRelInTime algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h)
      P (fun size => size) :=
  Compute.gm13_algorithm_7_1 h ω hh _he h71

open scoped BigOperators in
open GraphMinor.Compute SimpleGraph in
/-- **GM XIII (7.1)–(7.2) Algorithm joined with `gm13_algorithm_3_3` (`Join433.lean`),
`GM13.theorem_4_2_proof`, and `GM13.isPlanarGraph_elementaryWall` (`Join413.lean`) (page 89)**:
"(7.1) *For $h \ge 2$, even, if every graph with branch-width $\ge \omega/3$ has a minor
isomorphic to the elementary wall of height $h$, then there is an algorithm as in (7.2), with
running time $O(v^2 + \varepsilon)$.*
(7.2) Algorithm.
*Input:* A graph $G$.
*Output:* Either a branch-decomposition of $G$ of width $\le \omega$, or a wall of height $h$
which is a subgraph of $G$." -/
theorem algorithm_7_2 (h : ℕ) (hh : 2 ≤ h) (_he : Even h) :
    ∃ (ω₀ : ℕ) (P72 : Cmd),
    2 ≤ ω₀ ∧
    ComputesArrRelInTime alg72Size encAlg72In (IsAlg72Output h ω₀) P72 (fun m => m) :=
  Compute.gm13_algorithm_7_2 h hh _he

open Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09 SimpleGraph Hypergraph GraphMinor.GM10 GraphMinor.GM14 GraphMinor.GM16 in
/-- **Graph Minors XIII, (7.3)** (page 90): "Let $H$ be a wall of height $h$ with distance function
$d$ and let $v \in V(H)$. Let $r \ge 0$ be an integer with $h \ge 2r + 4$. Then there is a subgraph
$H'$ of $H$, which is a wall of height $h - 2r - 2$, such that (i) $d' \ge d - 4r - 4$, where $d'$
is the distance function in $H'$ (ii) there is no vertex $u$ of $H'$ with $d(u, v) \le r$."

(Section 7, page 90), in the form `GM13Theorem73Statement`:
`theorem_7_3_induced` without the description of the drawing of `H'`. -/
theorem theorem_7_3 {α : Type u} {β : Type v} (H : DrawnWall α β) (v : α) (r : ℕ) (hF : H.IsFigure1)
    (hv : v ∈ V(H.graph)) (hh : 2 * r + 4 ≤ H.height) :
    ∃ H' : DrawnWall α β, H'.IsFigure1 ∧ H'.graph ≤ H.graph ∧ H'.drawingU ⊆ H.drawingU ∧
    H'.vertexPoint = H.vertexPoint ∧ H'.height = H.height - 2 * r - 2 ∧
    DistGeSub H'.planeDist H.planeDist (4 * r + 4) ∧ ∀ u ∈ V(H'.graph), ¬ H.dist u v ≤ r :=
  GM13.theorem_7_3_proof H v r hF hv hh

open scoped BigOperators in
open GraphMinor.Compute SimpleGraph Classical in
/-- **Graph Minors XIII, (7.4)** (page 90, line 814): "For any $p \ge 2$ there exists $r \ge 0$ such
that the following holds. Let $H$ be a wall in a graph $G$. Let $P_1, \dots, P_{\binom{p}{2}}$ be
mutually vertex-disjoint $H$-paths in $G$, with their $p(p - 1)$ ends mutually at distance $\ge r$.
Then $G$ has a minor isomorphic to $K_p$. Moreover, there is an algorithm, with running time $\le
C\varepsilon(G)$, where $C$ depends only on $p$, which, given $G$, $H$, and $P_1, \dots,
P_{\binom{p}{2}}$ as above, finds a model of $K_p$ in $G$."

For every integer `p ≥ 2`, there exists `r ≥ 0` and a single height-independent Word RAM program `P`
(depending only on `p`) with running time `≤ C(p) * ε(G)` that outputs a model of $K_p$ in `G`. -/
theorem algorithm_7_4 (p : ℕ) (hp : 2 ≤ p) :
    ∃ r : ℕ, ∃ P : Cmd,
    ComputesArrRelInTime (alg74Size (p := p) (r := r)) (encAlg74In (p := p) (r := r))
    (IsAlg74Output p r) P (fun m => m) :=
  Compute.gm13_algorithm_7_4 p hp

open Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM14 in
/-- **Graph Minors XIII, (7.4)** (page 90): "For any $p \ge 2$ there exists $r \ge 0$ such that the
following holds. Let $H$ be a wall in a graph $G$. Let $P_1, \dots, P_{\binom{p}{2}}$ be mutually
vertex-disjoint $H$-paths in $G$, with their $p(p - 1)$ ends mutually at distance $\ge r$. Then $G$
has a minor isomorphic to $K_p$. Moreover, there is an algorithm, with running time $\le
C\varepsilon(G)$, where $C$ depends only on $p$, which, given $G$, $H$, and $P_1, \dots,
P_{\binom{p}{2}}$ as above, finds a model of $K_p$ in $G$."

For every `p` there is `r` such that, for every graph `G` with a wall
`H` drawn as in Fig. 1, `C(p, 2)` mutually vertex-disjoint `H`-paths of `G` whose ends are
mutually at distance at least `r` give a model of `K_p` in `G`. -/
theorem theorem_7_4 (p : ℕ) :
    ∃ r : ℕ, ∀ {α : Type u} {β : Type v},
    Theorem74For (α := α) (β := β) p r :=
  GM13.theorem_7_4_proof p

open Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM14 in
/-- **Graph Minors XIII, (7.5)** (page 91): "For any $p \ge 2$ there are integers $l \ge 3$, $m \ge
0$ with the following property. Let $G$ be a graph and let $H$ be a wall in $G$. Suppose that there
are $\binom{p}{2}$ external $(l, m)$-stars over $H$ with distinct centers (but not necessarily
disjoint). Then $G$ has a $K_p$-minor."

For every `p` there are `l = 2C(p,2)² - C(p,2) + 3` and `m` such that,
for every graph `G` with a wall `H` drawn as in Fig. 1, `C(p, 2)` external `(l, m)`-stars over
`H` with distinct centers give a model of `K_p` in `G`. -/
theorem theorem_7_5 (p : ℕ) :
    ∃ m : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β)
    (H : DrawnWall α β), H.IsFigure1 → IsWallIn G H.toWall →
    ∀ (S : Fin (p.choose 2) → Graph α β) (v : Fin (p.choose 2) → α),
      (∀ a, IsExternalLMStarOver G H (2 * p.choose 2 ^ 2 - p.choose 2 + 3) m (S a) (v a)) →
      Injective v → HasGraphModel (GM16.completeGraph p) G :=
  GM13.theorem_7_5_proof p

open Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09 in
/-- **Graph Minors XIII, (7.6)** (Section 7, page 92): "Let $H$ be a wall in a graph $G$. Suppose
there are $k$ $(l, m + 4k)$-stars in $G$ over $H$ with distinct centers $v_1, \dots, v_k$, where
$m \ge 3$. Then there is a wall $H' \subseteq H$ with $k$ external $(l, m)$-stars over $H'$, with
centers $v_1, \dots, v_k$." The wall `H` is drawn as in Fig. 1, and `H'` has "the drawing of
$H'$ obtained from the given drawing of $H$" (page 90): its point set is the image under `φ` of
the points of its vertices and edges in `Γ`, and its vertices keep their points.

The Lean proof corrects four steps of the paper's proof. See the corrections to the proof of (7.6)
in `corrections/GM13.md`. -/
theorem theorem_7_6 {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β) (hF : H.IsFigure1)
    (hHG : IsWallIn G H.toWall) (k l m : ℕ) (hm : 3 ≤ m) (S : Fin k → Graph α β) (v : Fin k → α)
    (hS : ∀ a, IsLMStarOver G H l (m + 4 * k) (S a) (v a)) (_hv : Injective v) :
    ∃ H' : DrawnWall α β, H'.graph ≤ H.graph ∧ H'.vertexPoint = H.vertexPoint ∧
    (∃ (φ : EuclideanPlane ≃ₜ EuclideanPlane) (Γ : GraphDrawing H.graph EuclideanPlane),
      IsFigure1CoordDrawing H.toWall Γ ∧ H.drawingU = φ '' Γ.drawing.U ∧
      (∀ (u : α) (hu : u ∈ V(H.graph)), H.vertexPoint u = φ (Γ.iso.vertexEquiv ⟨u, hu⟩).1) ∧
      H'.drawingU = φ '' indU Γ H'.toWall) ∧
    ∃ S' : Fin k → Graph α β, ∀ a, IsExternalLMStarOver G H' l m (S' a) (v a) :=
  GM13.theorem_7_6_proof G H hF hHG k l m hm S v hS _hv

open GraphMinor.Compute SimpleGraph Classical in
/-- **Graph Minors XIII, (7.7)** (page 93): "For any $p \ge 2$ there are integers $l \ge 3$, $m \ge
0$ with the following property. Let $G$ be a graph and let $H$ be a wall in $G$, so that there are
$\binom{p}{2}$ $(l, m)$-stars over $H$, with distinct centers; then $G$ has a $K_p$-minor. Moreover,
there is an algorithm, with running time $\le C\varepsilon(G)$, where $C$ depends only on $p$,
which, given $\binom{p}{2}$ $(l, m)$-stars with distinct centers over a wall $H$ in a graph $G$,
finds a model of $K_p$ in $G$."

(Section 7, page 93, line 890):
For every integer `p ≥ 2`, there exist `l, m` (`3 ≤ l`) and a Word RAM program `P` with running time
`≤ C(p) * ε(G)` that, given `p.choose 2` `(l, m)`-stars with distinct centers over a wall `W` in
`G`,
outputs a model of $K_p$ in `G`. -/
theorem algorithm_7_7 (p : ℕ) (hp : 2 ≤ p) :
    ∃ l m : ℕ, 3 ≤ l ∧ ∃ P : Cmd,
    ComputesArrRelInTime (alg77Size (p := p) (l := l) (m := m))
    (encAlg77In (p := p) (l := l) (m := m)) (IsAlg77Output p) P (fun s => s) :=
  Compute.gm13_algorithm_7_7 p hp

open Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09 SimpleGraph Hypergraph GraphMinor.GM10 GraphMinor.GM14 GraphMinor.GM16 in
/-- **Graph Minors XIII, (7.7)**, first assertion (Section 7, page 93): "For any $p \ge 2$ there
are integers $l \ge 3$, $m \ge 0$ with the following property. Let $G$ be a graph and let $H$ be
a wall in $G$, so that there are $\binom{p}{2}$ $(l, m)$-stars over $H$, with distinct centers;
then $G$ has a $K_p$-minor." "The first assertion is clear from (7.5) and (7.6)." By (7.6) there
is a wall `H' ≤ H` with external stars. To apply (7.5), we draw `H'` as in Fig. 1 itself; its
distances do not change, since both drawings are drawings on cells
(`DrawnOnCells.planeWallDist_eq`). -/
theorem theorem_7_7 (p : ℕ) (h1 : 2 ≤ p) :
    ∃ l m : ℕ, 3 ≤ l ∧ ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β),
    H.IsFigure1 → IsWallIn G H.toWall →
    ∀ (S : Fin (p.choose 2) → Graph α β) (v : Fin (p.choose 2) → α),
    (∀ a, IsLMStarOver G H l m (S a) (v a)) → Function.Injective v →
    HasGraphModel (GM16.completeGraph p) G :=
  GM13.theorem_7_7_proof p h1

/-! ## Section 8. The 2-Paths Problem -/

open GraphMinor.Compute GraphMinor.Compute.Crossing in
/-- Graph Minors XIII, Algorithm (8.1), page 93:
"(8.1) Algorithm.
*Input:* A society $(G, \Omega)$.
*Output:* A cross in $(G, \Omega)$ if one exists.
*Running time:* $O(v\varepsilon)$."
The program and its `O(vε)` bound use the proved external two-paths subroutine.

Shiloach's two-paths algorithm is replaced by a proved crossing extractor
(`docs/crossing/crossing_extractor.tex`). The society is first made simple, by removing loops and
parallel edges. Paths of the simple society lift to paths of the given one with the same vertices.
-/
theorem algorithm_8_1 :
    ∃ shiloachProg : Cmd,
    ComputesArrRelInTime alg81Size encAlg81In
      (fun x out => IsValidAlg81Output x (decAlg81Out x out))
      (alg81Prog shiloachProg) (fun s => s) :=
  Compute.algorithm_8_1_proved

open Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XIII, (8.1)** (page 93): "Algorithm. Input: A society $(G, \Omega)$. Output: A
cross in $(G, \Omega)$ if one exists. Running time: $O(v\varepsilon)$. Description: We assume that
$|\bar{\Omega}| \ge 4$, for otherwise no cross exists. Let $H$ be the cubic graph formed by two
vertex-disjoint circuits $C_1, C_2$, both of length $|\bar{\Omega}|$, and for $1 \le i \le
|\bar{\Omega}|$ an edge joining the $i$ th vertices of $C_1$ and $C_2$. Identify $V(C_2)$ with
$\bar{\Omega}$, in order, and let $s_1, s_2, t_1, t_2$ be distinct vertices of $C_1$, in order. We
apply an algorithm of Shiloach [27] to find two paths of $G \cup H$, vertex-disjoint, joining $s_1,
t_1$ and $s_2, t_2$, respectively, if they exist. If we find two such paths it is easy to derive a
cross in $(G, \Omega)$; and if there are not two such paths it is easy to see that $(G, \Omega)$ has
no cross. (Since Shiloach's algorithm has running time $O(v\varepsilon)$, so does (8.1).) $\square$"

Alias `theorem_8_1_proof` for `algorithm_8_1_correct` so that automated numbering checks see
`(8.1)`. -/
theorem theorem_8_1 {α : Type u} {β : Type v} (S : Society α β) :
    (S.Ω.bar.ncard < 4 → ¬ HasCross S) ∧
    ((∃ C : Graph α β, IsCrossSubgraph S C) ∧ HasCross S ∨ ¬ HasCross S) :=
  GM13.theorem_8_1_proof S

open Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XIII, (8.2)** (page 94): "Let $C$ be a core of $(G, \Omega)$, and let $v \in
V(C)$ not be 4-linked. Let $(A, B)$ be a separation of $C$ with $v \in V(A) - V(B)$ and
$\tilde{\Omega} \subseteq V(B)$, of minimum order, and let $C'$ be the simple graph obtained from
$B$ by adding edges joining all pairs of vertices in $V(A \cap B)$ if they are not already adjacent.
Then $C'$ is a core of $(G, \Omega)$, and each $v' \in V(C')$ which is 4-linked in $C$ is also
4-linked in $C'$."

(Section 8, pages 94–95):
“(8.2) *Let $C$ be a core of $(G, \Omega)$, and let $v \in V(C)$ not be 4-linked. Let $(A, B)$ be a
separation of $C$ with $v \in V(A) - V(B)$ and $\tilde{\Omega} \subseteq V(B)$, of minimum order,
and let $C'$ be the simple graph obtained from $B$ by adding edges joining all pairs of vertices in
$V(A \cap B)$ if they are not already adjacent. Then $C'$ is a core of $(G, \Omega)$, and each
$v' \in V(C')$ which is 4-linked in $C$ is also 4-linked in $C'$.*” -/
theorem theorem_8_2 {α : Type u} {β : Type v} {β' : Type w} {S : Society α β} {C A B : Graph α β'}
    {β'' : Type*} {C' : Graph α β''} {v : α} (hC : IsCoreOf S C) (hvC : v ∈ V(C))
    (hv_not_4 : ¬ IsFourLinkedVertexIn S C v) (hsep : IsGraphSeparation C A B)
    (hv_AB : v ∈ V(A) \ V(B)) (hbar : S.Ω.bar ⊆ V(B))
    (hmin : ∀ A' B' : Graph α β', IsGraphSeparation C A' B' → v ∈ V(A') \ V(B') → S.Ω.bar ⊆ V(B') →
      (V(A) ∩ V(B)).ncard ≤ (V(A') ∩ V(B')).ncard) (hC' : IsCoreStepGraph B (V(A) ∩ V(B)) C') :
    IsCoreOf S C' ∧ ∀ v' ∈ V(C'), IsFourLinkedVertexIn S C v' → IsFourLinkedVertexIn S C' v' :=
  GM13.theorem_8_2_proof hC hvC hv_not_4 hsep hv_AB hbar hmin hC'

open GraphMinor.Compute SimpleGraph in
/-- **Graph Minors XIII, (8.3)** (pages 93–94): "Algorithm. Input: A society $(G, \Omega)$. Output:
A 4-linked core of $(G, \Omega)$. Running time: $O(\nu\varepsilon)$. Description: Initially, set $C
= G$; then $C$ is a core, but it need not be 4-linked. For each vertex $v$ of $G$ in turn, if $v \in
V(C)$ test if $v$ is 4-linked in $C$; and if $v$ is not 4-linked in $C$, choose $(A, B)$ as in
(8.2), define $C'$ as in (8.2), and replace $C$ by $C'$. When this terminates, $C$ is a 4-linked
core, by the last assertion of (8.2). (For each $v \in V(G)$ this takes time $O(\varepsilon)$; and
so the total running time is $O(\nu\varepsilon)$.) $\square$"

Given a society `(G, Ω)`, `alg83Prog` computes in time `O(vε)` (`alg81Size x`) a 4-linked core
`(Z, C)` together with a valid sequence of (8.2) core steps (`Alg83Trace x Z C`) and four
`({v}, Ω)`-paths witnessing 4-linkedness for every vertex `v ∈ Z`.

The society is first made simple, by removing loops and parallel edges. Paths of the simple society
lift to paths of the given one with the same vertices. -/
theorem algorithm_8_3 :
    ComputesArrRelInTime alg81Size encAlg81In
    (fun x out => IsValidAlg83Output x (decAlg83Out x out))
    alg83Prog (fun s => s) :=
  Compute.gm13_algorithm_8_3

open Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XIII, (8.3)** (page 95): "Algorithm. Input: A society $(G, \Omega)$. Output: A
4-linked core of $(G, \Omega)$. Running time: $O(\nu\varepsilon)$. Description: Initially, set $C =
G$; then $C$ is a core, but it need not be 4-linked. For each vertex $v$ of $G$ in turn, if $v \in
V(C)$ test if $v$ is 4-linked in $C$; and if $v$ is not 4-linked in $C$, choose $(A, B)$ as in
(8.2), define $C'$ as in (8.2), and replace $C$ by $C'$. When this terminates, $C$ is a 4-linked
core, by the last assertion of (8.2). (For each $v \in V(G)$ this takes time $O(\varepsilon)$; and
so the total running time is $O(\nu\varepsilon)$.) $\square$"

Alias `theorem_8_3_proof` for `algorithm_8_3_correct` so that automated numbering checks see
`(8.3)`. -/
theorem theorem_8_3 {α : Type u} {β : Type v} (S : Society α β) :
    ∃ C : Graph α (Sym2 α), IsFourLinkedCore S C :=
  GM13.theorem_8_3_proof S

open Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XIII, (8.4)** (page 95): "If $C$ is a core of $(G, \Omega)$ then $(G, \Omega)$
has a cross if and only if $(C, \Omega)$ has a cross."

(Section 8, page 95):
“(8.4) *If $C$ is a core of $(G, \Omega)$ then $(G, \Omega)$ has a cross if and only if
$(C, \Omega)$ has a cross.*” -/
theorem theorem_8_4 {α : Type u} {β : Type v} {β' : Type w} {S : Society α β} {C : Graph α β'}
    (hC : IsCoreOf S C) :
    HasCross S ↔ HasCross (coreSociety S C hC) :=
  GM13.theorem_8_4_proof hC

open Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XIII, (8.5)** (page 95): "Let $C$ be a 4-linked core of $(G, \Omega)$. Then $(G,
\Omega)$ has no cross if and only if $(C, \Omega)$ is rural."

(Section 8, page 95):
“(8.5) *Let $C$ be a 4-linked core of $(G, \Omega)$. Then $(G, \Omega)$ has no cross if and only if
$(C, \Omega)$ is rural.*” -/
theorem theorem_8_5 {α : Type u} {β : Type v} {β' : Type w} {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) :
    ¬ HasCross S ↔ (coreSociety S C hC.isCore).IsRuralSociety :=
  GM13.theorem_8_5_proof hC

open GraphMinor.Compute GraphMinor.Compute.Crossing in
/-- Graph Minors XIII, Algorithm (8.6), page 96:
"(8.6) Algorithm.
*Input:* A society $(G, \Omega)$.
*Output:* Either a cross in $(G, \Omega)$, or a rural division of $(G, \Omega)$.
*Running time:* $O(\nu\varepsilon)$."
The program runs in `O(vε)` time.

The society is first made simple, by removing loops and parallel edges. Paths of the simple society
lift to paths of the given one with the same vertices. -/
theorem algorithm_8_6 :
    ∃ shiloachProg : Cmd,
    ComputesArrRelInTime alg81Size encAlg81In
      (fun x out => IsValidAlg86Output x (decAlg86Out x out))
      (alg86Prog shiloachProg) (fun s => s) :=
  Compute.algorithm_8_6_proved

open Classical Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 in
/-- **Graph Minors XIII, (8.6)** (page 96): "Algorithm. Input: A society $(G, \Omega)$. Output:
Either a cross in $(G, \Omega)$, or a rural division of $(G, \Omega)$. Running time:
$O(\nu\varepsilon)$. Description: First we use (8.1) to find a cross if there is one. If not, we use
(8.3) to find a 4-linked core $C$. Let $\mathcal{A}'$ be the set of all subgraphs $A$ of $G$ such
that either (i) $A$ consists of an edge of $G$ with both ends in $V(C)$, and its ends, or (ii) $A$
consists of a component of $G \setminus V(C)$, together with all edges of $G$ between this component
and $V(C)$, and their ends, or (iii) $A$ consists of a vertex $v \in \tilde{\Omega}$ incident with
no edges of $G$."

Alias of `algorithm_8_6_correct` under the paper's numbering `(8.6)`. -/
theorem theorem_8_6 {α : Type u} {β : Type v} (S : Society α β) :
    ((∃ C : Graph α β, IsCrossSubgraph S C) ∧ HasCross S) ∨
    (¬ HasCross S ∧ ∃ 𝒜 : Set (Graph α β), IsRuralDivision S 𝒜) :=
  GM13.theorem_8_6_proof S

/-! ## Section 9. Finding a Flat Section of a Wall -/

open scoped BigOperators in
open scoped BigOperators Graph in
open GraphMinor.Compute.Alg91 GraphMinor.Compute SimpleGraph Classical in
/-- **Graph Minors XIII, (9.1)** (page 98): "For any integer $p \ge 0$ there exist $k, r \ge 0$ such
that the following holds. Let $H$ be a wall in $G$, and let $H_1, \dots, H_k$ be subwalls of $H$
with $d(H_i, H_j) \ge r$ $(1 \le i < j \le k)$, where $d$ is the distance function of $H$. For $1
\le i \le k$, let $P_i \cup Q_i$ be a cross over $H_i$, such that (i) $(P_i \cup Q_i) \cap H
\subseteq H_i$, for $1 \le i \le k$ (ii) $(P_i \cup Q_i) \cap (P_j \cup Q_j)$ is null for $1 \le i <
j \le k$. Then $G$ has a $K_p$-minor. Moreover, a model of $K_p$ in $G$ can be found in time $\le
C\varepsilon(G)$, where $C$ depends only on $p$ and the height of $H$."

For every integer `p ≥ 0`, there exist `k, r ≥ 0` (`alg91K p` and `alg91R p`) such that for every
even height `h ≥ 2`, `alg91Prog p h` computes a valid model of $K_p$ in `G` in time `O(ε(G))`. -/
theorem algorithm_9_1 (p : ℕ) :
    ∃ k r : ℕ, ∀ h : ℕ, 2 ≤ h → Even h → ∃ P : Cmd,
    ComputesArrRelInTime (alg91Size (p := p) (h := h) (k := k) (r := r))
    (encAlg91In (p := p) (h := h) (k := k) (r := r)) (IsAlg91Output p) P (fun s => s) :=
  Compute.Alg91.gm13_algorithm_9_1 p

open Function Classical Graph SimpleGraph GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (9.1)** (page 98):
"For any integer $p \ge 0$ there exist $k, r \ge 0$ such that the following holds. Let $H$ be a wall
in $G$, and let $H_1, \dots, H_k$ be subwalls of $H$ with $d(H_i, H_j) \ge r$ $(1 \le i < j \le k)$,
where $d$ is the distance function of $H$. For $1 \le i \le k$, let $P_i \cup Q_i$ be a cross over
$H_i$, such that
(i) $(P_i \cup Q_i) \cap H \subseteq H_i$, for $1 \le i \le k$
(ii) $(P_i \cup Q_i) \cap (P_j \cup Q_j)$ is null for $1 \le i < j \le k$.
Then $G$ has a $K_p$-minor. Moreover, a model of $K_p$ in $G$ can be found in time $\le
C\varepsilon(G)$, where $C$ depends only on $p$ and the height of $H$." -/
theorem theorem_9_1 (p : ℕ) :
    ∃ k r : ℕ,
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β)
      (H_sub : Fin k → Wall α β) (P Q : Fin k → Graph α β),
      H.IsFigure1 →
      IsWallIn G H.toWall →
      (∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall) →
      (∀ i j : Fin k, i ≠ j → r ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
      (∀ i : Fin k, IsCrossOverWall G (H_sub i) (P i) (Q i)) →
      (∀ i : Fin k, (V(P i) ∪ V(Q i)) ∩ V(H.graph) ⊆ V((H_sub i).graph)) →
      Pairwise (fun i j : Fin k => Disjoint (V(P i) ∪ V(Q i)) (V(P j) ∪ V(Q j))) →
      HasGraphModel (GM16.completeGraph p) G :=
  GM13.theorem_9_1_proof p

open scoped BigOperators Graph in
open GraphMinor.Compute.Alg92 GraphMinor.Compute SimpleGraph Classical in
/-- **Graph Minors XIII, (9.2)** (page 99): "For any $l \ge 3$, and $m, p \ge 0$, there exist $k, r
\ge 0$ such that the following holds. Let $H$ be a wall with distance function $d$ in a graph $G$,
and let $H_1, \dots, H_k$ be non-dividing subwalls of $H$, with $$d(H_i, H_j) \ge r \quad (1 \le i <
j \le k).$$ Then either there is an $(l, m)$-star over $H$ or $G$ has a $K_p$-minor. Moreover, there
is an algorithm with running time $\le C\varepsilon(G)$, where $C$ depends only on $l, m, p$ and the
height of $H$, which given such subwalls $H_1, \dots, H_k$, finds either an $(l, m)$-star over $H$
or a model of $K_p$ in $G$."

On the Word RAM.

The algorithm finds a set `F` of bounded size in place of a minimal one. The paper uses the
minimality of `F` only to bound its size. -/
theorem algorithm_9_2 (l m p : ℕ) (h1 : 3 ≤ l) :
    ∃ k r : ℕ, ∀ h : ℕ, 2 ≤ h → Even h → ∃ P : Cmd,
    ComputesArrRelInTime (alg92Size (l := l) (m := m) (p := p) (h := h) (k := k) (r := r))
    (encAlg92In (l := l) (m := m) (p := p) (h := h) (k := k) (r := r)) (IsAlg92Output l m p) P
    (fun s => s) :=
  Compute.Alg92.gm13_algorithm_9_2 l m p h1

open Function Classical Graph SimpleGraph GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (9.2)** (page 99):
"For any $l \ge 3$, and $m, p \ge 0$, there exist $k, r \ge 0$ such that the following holds. Let
$H$ be a wall with distance function $d$ in a graph $G$, and let $H_1, \dots, H_k$ be non-dividing
subwalls of $H$, with
$$d(H_i, H_j) \ge r \quad (1 \le i < j \le k).$$
Then either there is an $(l, m)$-star over $H$ or $G$ has a $K_p$-minor. Moreover, there is an
algorithm with running time $\le C\varepsilon(G)$, where $C$ depends only on $l, m, p$ and the
height of $H$, which given such subwalls $H_1, \dots, H_k$, finds either an $(l, m)$-star over $H$
or a model of $K_p$ in $G$." -/
theorem theorem_9_2 (l m p : ℕ) (hl : 3 ≤ l) :
    ∃ k r : ℕ,
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β)
      (H_sub : Fin k → Wall α β),
      H.IsFigure1 →
      IsWallIn G H.toWall →
      (∀ i : Fin k, IsNonDividingSubwall G H.toWall (H_sub i)) →
      (∀ i j : Fin k, i ≠ j → r ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
      (∃ (S : Graph α β) (v : α), IsLMStarOver G H l m S v) ∨
        HasGraphModel (GM16.completeGraph p) G :=
  GM13.theorem_9_2_proof l m p hl

open Function Classical Graph SimpleGraph GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (9.3)** (page 101):
"For any $p \ge 0$ there exists $k, r \ge 0$ such that there is an algorithm as in (9.4), with
running time $\le C\varepsilon(G)$, where $C$ depends on $p, t$, and the height of $H$." -/
theorem theorem_9_3 (p : ℕ) :
    ∃ k r : ℕ,
    ∀ {α : Type u} {β : Type v} {t : ℕ} {G : Graph α β} {H : DrawnWall α β}
      (H_sub : Fin t → Wall α β),
      H.IsFigure1 →
      H.graph ≤ G →
      (∀ i : Fin t, (H_sub i).IsSubwallOf H.toWall) →
      (∀ i j : Fin t, i ≠ j → r ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
      HasGraphModel (GM16.completeGraph p) G ∨
        ∃ (X : Set α) (I : Finset (Fin t)),
          X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
          t - k ≤ I.card ∧
          ∀ i ∈ I, IsDividingSubwall
            (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H.toWall (H_sub i) :=
  GM13.theorem_9_3_proof p

open scoped BigOperators Graph in
open GraphMinor.Compute GraphMinor.Compute.Crossing SimpleGraph Classical in
/-- **Graph Minors XIII, (9.4)** (page 102): "Algorithm. Input: A graph $G$, a wall $H \subseteq G$
with distance function $d$, and subwalls $H_1, \dots, H_t$ of $H$ with $d(H_i, H_j) \ge r$ ($1 \le i
< j \le t$). Output: Either (i) a model of $K_p$ in $G$, or (ii) a subset $X \subseteq V(G)$ with
$|X| < \binom{p}{2}$ and a subset $I \subseteq \{1, \dots, t\}$ with $|I| \ge t - k$ such that for
all $i \in I$, $H_i$ is dividing in $(G \setminus X) \cup H$."

Graph Minors XIII, (9.3) and Algorithm (9.4), page 102: the linear-time
program, using the proved programs of (7.7) and (9.2). -/
theorem algorithm_9_4 (p : ℕ) :
    ∃ k r : ℕ, ∀ t h : ℕ, 2 ≤ h → Even h → ∃ P : Cmd,
    ComputesArrRelInTime (alg94Size (p := p) (t := t) (h := h) (k := k) (r := r))
    (encAlg94In (p := p) (t := t) (h := h) (k := k) (r := r)) (IsAlg94Output p t k) P (fun s => s) :=
  Compute.algorithm_9_4_proved p

open Function Classical Graph SimpleGraph GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, Algorithm (9.4)** (page 102):
"(9.4) Algorithm.
*Input:* A graph $G$, a wall $H \subseteq G$ with distance function $d$, and subwalls
$H_1, \dots, H_t$ of $H$ with $d(H_i, H_j) \ge r$ ($1 \le i < j \le t$).
*Output:* Either
(i) a model of $K_p$ in $G$, or
(ii) a subset $X \subseteq V(G)$ with $|X| < \binom{p}{2}$ and a subset $I \subseteq \{1, \dots,
t\}$
with $|I| \ge t - k$ such that for all $i \in I$, $H_i$ is dividing in $(G \setminus X) \cup H$."

Formalized as the recursive step of Algorithm (9.4): given `s ≤ p.choose 2` `(l, m)`-stars over
`H` in `G` with distinct centers `v : Fin s → α`, the recursion terminates in at most
`p.choose 2 - s` steps with either a `K_p`-model in `G` or a set `X ⊆ V(G)` of `< p.choose 2`
star centers and a subset `I ⊆ Finset.univ` of `≥ t - k` indices such that `H_sub i` is dividing in
`(G \ X) ∪ H` for all `i ∈ I`. -/
theorem theorem_9_4 {α : Type u} {β : Type v} {G : Graph α β} {H : DrawnWall α β} {p l m k r t : ℕ}
    (_hp : 2 ≤ p) (_hl : 3 ≤ l) (hHG : H.graph ≤ G) (H_sub : Fin t → Wall α β)
    (hsub : ∀ i : Fin t, (H_sub i).IsSubwallOf H.toWall)
    (_hdist : ∀ i j : Fin t, i ≠ j → r ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph)
    (h77_step : ∀ (S : Fin (p.choose 2) → Graph α β) (v : Fin (p.choose 2) → α),
      (∀ a, IsLMStarOver G H l m (S a) (v a)) → Function.Injective v →
      HasGraphModel (GM16.completeGraph p) G)
    (h92_step : ∀ (X : Set α) (emb : Fin k ↪ Fin t),
      (∀ a : Fin k,
        IsNonDividingSubwall (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H.toWall
        (H_sub (emb a))) →
      (∃ (S : Graph α β) (v : α),
        IsLMStarOver (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H l m S v) ∨
      HasGraphModel (GM16.completeGraph p) G) :
    ∀ (rem s : ℕ), rem = p.choose 2 - s → s ≤ p.choose 2 →
    ∀ (S : Fin s → Graph α β) (v : Fin s → α),
      (∀ a : Fin s, IsLMStarOver G H l m (S a) (v a)) →
      Function.Injective v →
      HasGraphModel (GM16.completeGraph p) G ∨
        ∃ (X : Set α) (I : Finset (Fin t)),
          X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
          t - k ≤ I.card ∧
          ∀ i ∈ I, IsDividingSubwall
            (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H.toWall (H_sub i) :=
  GM13.theorem_9_4_proof _hp _hl hHG H_sub hsub _hdist h77_step h92_step

open Function Graph SimpleGraph GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14 in
/-- **Graph Minors XIII, (9.5)** (page 102):
"Let $H$ be a wall in a graph $G$. If $H_1$ is a dividing subwall of $H$ with compass $K_1$, then
$K_1 \cap H \subseteq H_1$; and if $H_2$ is another dividing subwall of $H$ with compass $K_2$, and
$H_1 \cap H_2$ is null, then $K_1 \cap K_2$ is null." -/
theorem theorem_9_5 {α : Type u} {β : Type v} {G : Graph α β} {H H₁ H₂ : Wall α β}
    (hHG : H.graph ≤ G) (hsub₁ : IsProperSubwallOf H₁ H) (hdiv₁ : IsDividingSubwall G H H₁) :
    subgraphInter G (wallCompass G H₁) H.graph ≤ H₁.graph ∧
    (IsProperSubwallOf H₂ H →
      IsDividingSubwall G H H₂ →
      Disjoint V(H₁.graph) V(H₂.graph) →
      Disjoint V(wallCompass G H₁) V(wallCompass G H₂) ∧
        V(subgraphInter G (wallCompass G H₁) (wallCompass G H₂)) = ∅) :=
  GM13.theorem_9_5_proof hHG hsub₁ hdiv₁

open Function Classical Graph SimpleGraph GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (9.6)** (page 103):
"For any $p, s \ge 0$ and $h \ge 2$, even, there exists $h' \ge p^2 + 2$, even, and an algorithm as
in (9.7) with running time $O(v\varepsilon)$ for fixed $p, s, h$." -/
theorem theorem_9_6 (p s h : ℕ) (h2 : 2 ≤ h) (heven : Even h) :
    ∃ h' : ℕ,
    p ^ 2 + 2 ≤ h' ∧ Even h' ∧
    ∀ {α : Type u} {β : Type v} {G : Graph α β} {H : Wall α β},
      H.graph ≤ G →
      H.height = h' →
      HasGraphModel (GM16.completeGraph p) G ∨
        ∃ (X : Set α) (H_flat : Fin s → Wall α β),
          X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
          Pairwise (fun a b : Fin s => Disjoint V((H_flat a).graph) V((H_flat b).graph)) ∧
          ∀ a : Fin s,
            IsProperSubwallOf (H_flat a) H ∧
            (H_flat a).height = h ∧
            IsFlatWallIn (subgraphUnion G (G.induce (V(G) \ X)) H.graph) (H_flat a) ∧
            IsDividingSubwall (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H (H_flat a) ∧
            Disjoint V((H_flat a).graph) X :=
  GM13.theorem_9_6_proof p s h h2 heven

open scoped BigOperators Graph in
open GraphMinor.Compute GraphMinor.Compute.Crossing SimpleGraph Classical in
/-- **Graph Minors XIII, (9.7)** (page 103): "Algorithm. Input: A graph $G$, and a wall $H$ in $G$
of height $h'$. Output: Either (i) a model of $K_p$ in $G$, or (ii) a subset $X \subseteq V(G)$ with
$|X| < \binom{p}{2}$ and $s$ subwalls $H_1, \dots, H_s$ of $H$ of height $h$, mutually
vertex-disjoint, and each flat and dividing in $(G \setminus X) \cup H$, and each disjoint from
$X$."

Graph Minors XIII, (9.6) and Algorithm (9.7), page 103: the `O(vε)`
program, using the proved two-paths and (9.4) programs. -/
theorem algorithm_9_7 (p s h : ℕ) (h1 : 2 ≤ h) (h2 : Even h) :
    ∃ h' : ℕ, p ^ 2 + 2 ≤ h' ∧ Even h' ∧ ∃ P : Cmd,
    ComputesArrRelInTime (alg97Size (h' := h')) (encAlg97In (h' := h')) (IsAlg97Output p s h h') P
    (fun m => m) :=
  Compute.algorithm_9_7_proved p s h h1 h2

open Function Classical Graph SimpleGraph GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, Algorithm (9.7)** (page 103):
"(9.7) Algorithm.
*Input:* A graph $G$, and a wall $H$ in $G$ of height $h'$.
*Output:* Either
(i) a model of $K_p$ in $G$, or
(ii) a subset $X \subseteq V(G)$ with $|X| < \binom{p}{2}$ and $s$ subwalls $H_1, \dots, H_s$ of $H$
of height $h$, mutually vertex-disjoint, and each flat and dividing in $(G \setminus X) \cup H$, and
each disjoint from $X$."

Given `(k₁, r₁)` from (9.3) (`theorem_9_3_proof p`) and `(k₂, r₂)` from (9.1) (`theorem_9_1_proof
p`), for any
wall `H` in `G` of height
`h' = 2 * ((s + k₁ + k₂ + p.choose 2 + 1) * (h + max r₁ (max r₂ 1) + 4) + p ^ 2 + 2)`, we construct
a Fig. 1 plane drawing `H_drawn` of `H` (`H.exists_drawnWall_isFigure1`) and
`t = s + k₁ + k₂ + p.choose 2` proper subwalls `H_sub` of `H` of height `h` at pairwise distance
`≥ max r₁ (max r₂ 1)` (`DrawnWall.IsFigure1.exists_subwalls_far_apart`), apply (9.3)/(9.4), test
flatness of the dividing subwalls via (8.1), and either obtain a `K_p`-model by (9.5) and (9.1) or
select `s` flat dividing subwalls disjoint from `X`. -/
theorem theorem_9_7 {α : Type u} {β : Type v} {p s h : ℕ} (h2 : 2 ≤ h) (heven : Even h)
    {G : Graph α β} {H : Wall α β} (hHG : H.graph ≤ G)
    (hHh : H.height =
      let k₁ := Classical.choose.{1} (theorem_9_3_proof.{u, v} p)
      let r₁ := Classical.choose.{1} (Classical.choose_spec.{1} (theorem_9_3_proof.{u, v} p))
      let k₂ := Classical.choose.{1} (theorem_9_1_proof.{u, v} p)
      let r₂ := Classical.choose.{1} (Classical.choose_spec.{1} (theorem_9_1_proof.{u, v} p))
      2 * ((s + k₁ + k₂ + p.choose 2 + 1) *
        (h + max r₁ (max r₂ 1) + 4) + p ^ 2 + 2)) :
    HasGraphModel (GM16.completeGraph p) G ∨
    ∃ (X : Set α) (H_flat : Fin s → Wall α β),
      X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
      Pairwise (fun a b : Fin s => Disjoint V((H_flat a).graph) V((H_flat b).graph)) ∧
      ∀ a : Fin s,
        IsProperSubwallOf (H_flat a) H ∧
        (H_flat a).height = h ∧
        IsFlatWallIn (subgraphUnion G (G.induce (V(G) \ X)) H.graph) (H_flat a) ∧
        IsDividingSubwall (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H (H_flat a) ∧
        Disjoint V((H_flat a).graph) X :=
  GM13.theorem_9_7_proof h2 heven hHG hHh

open Function Classical Graph SimpleGraph GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, (9.8)** (page 104):
"For all $p \ge 0$ and $h \ge 2$, even, there exists $\omega \ge 0$ such that there is an algorithm
as in (9.9), with running time $O(v\varepsilon)$ for fixed $p, h$." -/
theorem theorem_9_8 (p h : ℕ) (h2 : 2 ≤ h) (heven : Even h) :
    ∃ ω : ℕ,
    ∀ {α : Type u} {β : Type v} {G : Graph α β},
      V(G).Finite → E(G).Finite →
      GraphBranchWidthLE G ω ∨
        HasGraphModel (GM16.completeGraph p) G ∨
        ∃ (X : Set α) (H_flat : Wall α β) (S : Society α β) (𝒜 : Set (Graph α β)),
          X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
          IsFlatWallIn (deleteVertices G X) H_flat ∧ H_flat.height = h ∧
          IsWallSociety (deleteVertices G X) H_flat S ∧
          IsRuralDivision S 𝒜 ∧
          ∀ A : Graph α β, IsInteriorMember H_flat 𝒜 A → GraphBranchWidthLE A ω :=
  GM13.theorem_9_8_proof p h h2 heven

open GraphMinor.Compute GraphMinor.Compute.Crossing in
/-- **Graph Minors XIII, (9.9)** (page 104): "Algorithm. Input: A graph $G$. Output: Either (i) a
branch-decomposition of $G$ of width $\le \omega$, or (ii) a model of $K_p$ in $G$, or (iii) a
subset $X \subseteq V$ with $|X| < \binom{p}{2}$ and a flat wall $H$ in $G \setminus X$ of height
$h$, and a rural division $\mathcal{A}$ of the society of $H$ in $G \setminus X$, and a
branch-decomposition of width $\le \omega$ of each interior member of $\mathcal{A}$."

Graph Minors XIII, (9.8) and Algorithm (9.9), pages 103–106: both the
standalone `O(vε)` program and its caller specification, using the proved
(7.2), (9.7), and Steps (5)–(7) programs. -/
theorem algorithm_9_9 : Algorithm99Statement case3Decoder :=
  Compute.gm13_algorithm_9_9

open Function Classical Graph SimpleGraph GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 in
/-- **Graph Minors XIII, Algorithm (9.9)** (pages 104–105):
"(9.9) Algorithm.
*Input:* A graph $G$.
*Output:* Either
(i) a branch-decomposition of $G$ of width $\le \omega$, or
(ii) a model of $K_p$ in $G$, or
(iii) a subset $X \subseteq V$ with $|X| < \binom{p}{2}$ and a flat wall $H$ in $G \setminus X$ of
height $h$, and a rural division $\mathcal{A}$ of the society of $H$ in $G \setminus X$, and a
branch-decomposition of width $\le \omega$ of each interior member of $\mathcal{A}$."

Recursive step of Algorithm (9.9) (Steps (2)–(8) of the proof of (9.8), pages 104–105), proved by
strong induction on `graphSize G_i = |E(G_i)| + |V(G_i)| + 1`. -/
theorem theorem_9_9 {α : Type u} {β : Type v} {p h ω : ℕ} (h2 : 2 ≤ h) (heven : Even h)
    {G : Graph α β} (hVG : V(G).Finite) (hEG : E(G).Finite)
    (h72_A : ∀ A : Graph α β, A ≤ G →
      (∃ W : Wall α β, IsWallIn A W ∧ W.height =
        Classical.choose.{1} (theorem_9_6_proof.{u, v} p (p.choose 2 + 5) h h2 heven)) ∨
      GraphBranchWidthLE A ω) :
    ∀ (n : ℕ) (G_i : Graph α β),
    graphSize G_i = n →
    ∀ (Z_i : Set α) (H_i : Wall α β),
      G_i ≤ G →
      Z_i ⊆ V(G_i) →
      Z_i.ncard ≤ p.choose 2 + 2 →
      (∀ v ∈ V(G_i) \ Z_i, ∀ e ∈ E(G), G.Inc e v → e ∈ E(G_i)) →
      H_i.graph ≤ G_i →
      H_i.height = Classical.choose.{1} (theorem_9_6_proof.{u, v} p (p.choose 2 + 5) h h2 heven) →
      HasGraphModel (GM16.completeGraph p) G ∨
        ∃ (X : Set α) (H_flat : Wall α β) (S : Society α β) (𝒜 : Set (Graph α β)),
          X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
          IsFlatWallIn (deleteVertices G X) H_flat ∧ H_flat.height = h ∧
          IsWallSociety (deleteVertices G X) H_flat S ∧
          IsRuralDivision S 𝒜 ∧
          ∀ A : Graph α β, IsInteriorMember H_flat 𝒜 A → GraphBranchWidthLE A ω :=
  GM13.theorem_9_9_proof h2 heven hVG hEG h72_A

/-! ## Section 10. Homogeneously Labelled Walls -/

open GraphMinor.Compute Function Graph SimpleGraph Classical GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13 in
/-- Graph Minors XIII, Algorithm (10.1), pages 106–107:
"*Input:* $G$, $X$, $H$, $\mathcal{A}$ satisfying Hypothesis C, and an integer $\delta \ge 0$,
and for each interior $A \in \mathcal{A}$ a branch-decomposition of $A$ of width $\le \omega$."
"*Output:* A vision."
"*Running time:* $O(\varepsilon^2)$."

The one program works for every wall height. Its correctness includes the
geometric vision data, the interior folios and their models. The only input
conditions are Hypothesis C and the supplied decompositions, as printed.

The width after adding vertices is `max ω 2 + q` (see the correction to (10.1) in
`corrections/GM13.md`). The wall is given by input arrays (its subdivision lists, its vertex set
and its perimeter), so that one program works for every wall height. -/
theorem algorithm_10_1 (p q δ ω : ℕ) :
    ∃ P : Cmd,
    ComputesRelInTime (alg101Size (q := q) (ω := ω)) (IsAlg101InputState p)
      (fun x s => IsAlg101Output δ x (s.arrs (a101_visBuf p)))
      P (fun ε => ε ^ 2) :=
  Compute.gm13_algorithm_10_1 p q δ ω

open Function Classical Graph SimpleGraph Hypergraph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 in
/-- **Graph Minors XIII, (10.1)** (page 106): "Algorithm. Input: $G$, $X$, $H$, $\mathcal{A}$
satisfying Hypothesis C, and an integer $\delta \ge 0$, and for each interior $A \in \mathcal{A}$ a
branch-decomposition of $A$ of width $\le \omega$. Output: A vision. Running time:
$O(\varepsilon^2)$. Description: First we compute an attachment sequence for each interior $A \in
\mathcal{A}$. For each $A$ this takes time $O(\varepsilon(G))$, and so we can compute all the
attachment sequences in time $O(\varepsilon^2)$, since $|\mathcal{A}| \le |E(G)|$."

Numbered alias for **(10.1)** (Graph Minors XIII, Section 10, pages 106–107):
“(10.1) Algorithm.
*Input:* $G$, $X$, $H$, $\mathcal{A}$ satisfying Hypothesis C, and an integer $\delta \ge 0$, and
for each interior $A \in \mathcal{A}$ a branch-decomposition of $A$ of width $\le \omega$. ...
*Output:* A vision.
*Running time:* $O(\varepsilon^2)$.”

The width after adding vertices is `max ω 2 + q`, not as printed. See the correction to (10.1) in
`corrections/GM13.md`. -/
theorem theorem_10_1 {α : Type u} {β : Type v} (q ω δ : ℕ) (G : Digraph α β) (X : Set α)
    (H : Wall α β) (S_H : Society α β) (𝒜 : Set (Graph α β)) (hC : HypothesisC G q X H S_H 𝒜)
    (hbw : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω) :
    ∃ vis : Vision G X H S_H 𝒜,
    ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A →
      IsAttachmentSequence S_H X vis.xSeq A (vis.pi A) ∧
      (vis.pi A).length ≤ q + 3 ∧
      GraphBranchWidthLE (vis.tildeA A).toGraph (max ω 2 + q) ∧
      ∃ hroots : ∀ x ∈ vis.pi A, x ∈ (vis.tildeA A).vertexSet,
        ∃ (vMod : RootedDigraph ℕ ℕ (vis.pi A).length → ℕ → Digraph α β)
          (eMod : RootedDigraph ℕ ℕ (vis.pi A).length → ℕ → β),
          IsDeltaFolioModelling
            (rootedDigraphOfList (vis.tildeA A) (vis.pi A) hroots) δ vMod eMod :=
  GM13.theorem_10_1_proof q ω δ G X H S_H 𝒜 hC hbw

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM05 GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 in
/-- **Graph Minors XIII, (10.2)** (page 563): "For any $q$, $\delta \ge 0$ and $h \ge 2$, even,
there exists $f(h) \ge h$, even, such that under Hypothesis C, if $H' \subseteq H$ is an
$h$-homogeneous subwall of height $f(h)$ then both middle vertices of $H'$ are irrelevant to the
$\delta$-folio of $G$ relative to $X$. (The middle vertices of a wall are the two vertices
corresponding to the two middle vertices of the elementary wall of which the wall is a subdivision.)
We use (10.2) to show"

(Section 10, page 107), proved in Graph Minors XXII, Section 8
(page 563) and instantiated at `GM21.theorem_1_1_proof`:
“(10.2) *For any $q$, $\delta \ge 0$ and $h \ge 2$, even, there exists $f(h) \ge h$, even, such
that under Hypothesis C, if $H' \subseteq H$ is an $h$-homogeneous subwall of height $f(h)$ then
both middle vertices of $H'$ are irrelevant to the $\delta$-folio of $G$ relative to $X$.*” -/
theorem theorem_10_2 (q δ h : ℕ) (h1 : 2 ≤ h) (h2 : Even h) :
    ∃ f_h : ℕ, h ≤ f_h ∧ Even f_h ∧
    ∀ {α : Type u} {β : Type v} (G : Digraph α β) (X : Set α) (H H' : Wall α β) (S_H : Society α β)
    (𝒜 : Set (Graph α β)) (vis : Vision G X H S_H 𝒜), HypothesisC G q X H S_H 𝒜 →
    IsHomogeneousSubwall vis δ h H' → H'.height = f_h → IsIrrelevantVertex G δ X H'.middleVertex₁ ∧
    IsIrrelevantVertex G δ X H'.middleVertex₂ :=
  GM13.theorem_10_2_proof q δ h h1 h2

open GraphMinor.Compute GraphMinor.Compute.Crossing in
/-- **Graph Minors XIII, (10.3)**, pages 107–108:
"For all $q$, $\delta \ge 0$ there exists $h \ge 0$, even, such that for all
$\omega \ge 0$ there is an algorithm as in (10.4) with running time $O(\varepsilon^2)$."
The array-layout parameter `p` is arbitrary. The chosen height is independent
of both `p` and the supplied branch-width bound. -/
theorem algorithm_10_3 (q δ : ℕ) :
    ∃ h : ℕ, 2 ≤ h ∧ Even h ∧ ∀ p ω : ℕ,
    Alg104Spec case3Decoder p q δ h ω :=
  Compute.gm13_algorithm_10_3 q δ

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM05 GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 GraphMinor.GM16 in
/-- **Graph Minors XIII, (10.3)** (Section 10, pages 107–108):
"(10.3) *For all $q$, $\delta \ge 0$ there exists $h \ge 0$, even, such that for all $\omega \ge 0$
there is an algorithm as in (10.4) with running time $O(\varepsilon^2)$.*"

Mathematical content of the proof of (10.3) (pages 107–108): given
`h = sec10WallHeight theorem_10_2_proof q δ` and input `G, X, H, S_H, 𝒜` satisfying Hypothesis C
with
`h ≤ H.height` (in particular when `H.height = h`) and branch-width `≤ ω` for each interior member
`A ∈ 𝒜`, Algorithm (10.1) finds a vision `vis`, and the subwall recursion maintaining invariants
(i)–(iii) terminates at some step `i` (`1 ≤ i ≤ |𝒯_1| + 1`) at an `h_{i+1}`-homogeneous subwall
`H_i` of `H` of height `h_i`, both of whose middle vertices are irrelevant to the `δ`-folio of `G`
relative to `X` by `(10.2)`.

The Word RAM program `GM13.algorithm_10_3` follows the paper (pages 107–108):
an `O(ε²)` Word RAM implementation calling Algorithm (10.1) (`O(ε²)`) to find a vision and then
running at most `|𝒯_1| + 1` iterations (`O(v)` per iteration, checking the bounded number of
subwalls of `H_i` of height `h_{i+1}`) to output a middle vertex of `H_i`. -/
theorem theorem_10_3 {α : Type u} {β : Type v} (q δ ω : ℕ) (G : Digraph α β) (X : Set α)
    (H : Wall α β) (S_H : Society α β) (𝒜 : Set (Graph α β)) (hC : HypothesisC G q X H S_H 𝒜)
    (hH_height : sec10WallHeight theorem_10_2_proof.{u, v} q δ ≤ H.height)
    (hbw : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω) :
    let n := (folioClassT1 q δ).ncard
    let h_seq := sec10HeightSeq theorem_10_2_proof.{u, v} q δ
    ∃ (vis : Vision G X H S_H 𝒜) (i : ℕ) (H_i : Wall α β)
      (𝒯_i : Set (Σ j : Fin (q + 4), Set (RootedDigraph ℕ ℕ j.val))),
      1 ≤ i ∧ i ≤ n + 1 ∧
      H_i.IsSubwallOf H ∧ H_i.height = h_seq i ∧
      𝒯_i ⊆ folioClassT1 q δ ∧ 𝒯_i.ncard = n + 1 - i ∧
      (∀ ⦃A : Graph α β⦄ (hInt : IsInteriorMember H 𝒜 A),
        vis.vOf A ∈ H_i.insideVerts →
        sigmaDeltaFolio q δ (Nat.lt_succ_of_le (vis.pi_properties hC hInt).2.1)
          (rootedDigraphOfList (vis.tildeA A) (vis.pi A) (vis.pi_properties hC hInt).2.2) ∈ 𝒯_i) ∧
      IsHomogeneousSubwall vis δ (h_seq (i + 1)) H_i ∧
      IsIrrelevantVertex G δ X H_i.middleVertex₁ ∧
      IsIrrelevantVertex G δ X H_i.middleVertex₂ :=
  GM13.theorem_10_3_proof q δ ω G X H S_H 𝒜 hC hH_height hbw

open GraphMinor.Compute Function Graph SimpleGraph GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13 in
/-- Graph Minors XIII, Algorithm (10.4), pages 107–108:
"A vertex irrelevant to the $\delta$-folio of $G$ relative to $X$."
The program of `Alg104Spec` computes this vertex in quadratic time, using the
proved (4.1) program and the homogeneous-wall recursion of (10.3). -/
theorem algorithm_10_4 (p q δ ω : ℕ) :
    Alg104Spec case3Decoder p q δ
    (GM13.sec10MaxWallHeight GM13.theorem_10_2_proof.{0, 0} q δ) ω :=
  Compute.gm13_algorithm_10_4 p q δ ω

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM05 GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 GraphMinor.GM16 in
/-- **Graph Minors XIII, (10.4)** (Section 10, page 107):
"(10.4) Algorithm.
*Input:* $G$, $X$, $H$, $\mathcal{A}$ satisfying Hypothesis C, where $H$ has height $h$, and for
each interior $A \in \mathcal{A}$ a branch-decomposition of $A$ of width $\le \omega$.
*Output:* A vertex irrelevant to the $\delta$-folio of $G$ relative to $X$." -/
theorem theorem_10_4 {α : Type u} {β : Type v} (q δ ω : ℕ) (G : Digraph α β) (X : Set α)
    (H : Wall α β) (S_H : Society α β) (𝒜 : Set (Graph α β)) (hC : HypothesisC G q X H S_H 𝒜)
    (hH_height : sec10WallHeight theorem_10_2_proof.{u, v} q δ ≤ H.height)
    (hbw : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω) :
    ∃ v ∈ G.vertexSet \ X, IsIrrelevantVertex G δ X v :=
  GM13.theorem_10_4_proof q δ ω G X H S_H 𝒜 hC hH_height hbw

open GraphMinor.Compute GraphMinor.Compute.Crossing in
/-- **Graph Minors XIII, (10.5)** (page 108): "Algorithm. Input: A digraph $G$ and a subset $Z
\subseteq V(G)$ with $|Z| \le \xi$. Output: The $\delta$-folio of $G$ relative to $Z$. Running time:
$O(v^3)$. Description: (1) Let $p$, $C$ be as in (6.5). We apply (6.5) to $G$, $Z$, and obtain a
subdigraph $G' \subseteq G$ with $Z \subseteq V(G')$ such that $G$ and $G'$ have the same
$\delta$-folio relative to $Z$ and such that $|E(G')| \le C|V(G')|$."

Graph Minors XIII, Algorithm (10.5), pages 108–109: for fixed root and
detail bounds, a program computes the folio in `O(v³)` time. The chosen
width and wall height come from the proved (9.9) and (10.3) programs.

Step (2) uses the width `max ω 2 + ξ`. See the correction to (10.5) in `corrections/GM13.md`. -/
theorem algorithm_10_5 (ξ δ : ℕ) :
    ∃ (ω : ℕ) (P : Cmd),
    ComputesArrRelInTime (folioSize (ξ := ξ)) encFolioIn
      (IsValidAlg105Output δ (max ω 2 + ξ)) P (fun v => (v + 1) ^ 3) :=
  Compute.algorithm_10_5_proved ξ δ

open Function Classical Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM05 GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 GraphMinor.GM16 in
/-- **Graph Minors XIII, (10.5)** (Section 10, pages 108–109):
"(10.5) Algorithm.
*Input:* A digraph $G$ and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$.
*Output:* The $\delta$-folio of $G$ relative to $Z$.
*Running time:* $O(v^3)$." -/
theorem theorem_10_5 {α : Type u} {β : Type v} [Nonempty β] (ξ δ : ℕ) :
    let p := 5 * ξ / 2 + 3 * δ + 1
    let C := δ + 2 * (δ + 1) * 2 ^ (p - 3)
    let q := p.choose 2 + ξ - 1
    let h := sec10MaxWallHeight theorem_10_2_proof.{u, v} q δ
    2 ≤ h ∧ Even h ∧
    ∃ (ω : ℕ),
      ∀ (G : Digraph α β) (Z : Set α),
        G.IsFinite → Z ⊆ G.vertexSet → Z.ncard ≤ ξ →
        ∃ (G' G_final : Digraph α β),
          G'.IsSubdigraph G ∧ Z ⊆ G'.vertexSet ∧
          HasSameDeltaFolioRel G G' δ Z ∧
          G'.edgeSet.ncard ≤ C * G'.vertexSet.ncard ∧
          G_final.IsSubdigraph G' ∧ Z ⊆ G_final.vertexSet ∧
          GraphBranchWidthLE G_final.toGraph (max ω 2 + ξ) ∧
          HasSameDeltaFolioRel G G_final δ Z ∧
          (∀ {k : ℕ} (r : Fin k → α) (hr : ∀ j, r j ∈ G_final.vertexSet)
            (hrG : ∀ j, r j ∈ G.vertexSet),
            Injective r → range r ⊆ Z →
            HasSameDeltaFolio (RootedDigraph.mk G r hrG) (RootedDigraph.mk G_final r hr) δ ∧
            (Nonempty α → ∃ (vMod : RootedDigraph ℕ ℕ k → ℕ → Digraph α β)
              (eMod : RootedDigraph ℕ ℕ k → ℕ → β),
              IsDeltaFolioModelling (RootedDigraph.mk G_final r hr) δ vMod eMod)) :=
  GM13.theorem_10_5_proof ξ δ

end GraphMinor.GM13
