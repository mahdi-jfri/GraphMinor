module

public import GraphMinor.GM02.Section4Counterexample

public import GraphMinor.GM02.FeasibilityCounterexample

public import GraphMinor.Compute.Bridge13
public import GraphMinor.Compute.DPStatement
public import GraphMinor.Compute.GM02Algorithm32
public import GraphMinor.Compute.GM02Algorithm46
public import GraphMinor.Compute.GM02Algorithm47
public import GraphMinor.Compute.GM02BalancedComplexity
public import GraphMinor.Compute.GM02MinorPatternScan
public import GraphMinor.Compute.GM13ClassRecognition
public import GraphMinor.GM02.BagSeparation
public import GraphMinor.GM02.Branches
public import GraphMinor.GM02.ClassRecognition
public import GraphMinor.GM02.CrossingScheme
public import GraphMinor.GM02.DisjointPaths
public import GraphMinor.GM02.ExtractedSchemeFeasible
public import GraphMinor.GM02.Feasibility
public import GraphMinor.GM02.Section4FeasibleForward
public import GraphMinor.GM02.Section4Split
public import GraphMinor.GM02.Section4Subdivision
public import GraphMinor.GM02.Section4Suppression
public import GraphMinor.GM02.Separation
public import GraphMinor.GM02.SeparatorComponents
public import GraphMinor.GM02.TreeDecomposition
public import GraphMinor.GM02.TreeSidePartition
public import GraphMinor.GM10.SubmodularBasic
public import GraphMinor.Minor.Basic
public import Mathlib.Combinatorics.Graph.Simple
import GraphMinor.GM02.BalancedSeparation
import GraphMinor.GM02.BalancedSeparationAlgorithm
import GraphMinor.GM02.BalancedSeparator
import GraphMinor.GM02.CrossingFeasibility
import GraphMinor.GM02.CrossingIndex
import GraphMinor.GM02.CrossingSchemeCount
import GraphMinor.GM02.FiniteObstructions
import GraphMinor.GM02.IsomorphicTopologicalAlgorithm
import GraphMinor.GM02.MinorAlgorithm
import GraphMinor.GM02.MinorTreeWidth
import GraphMinor.GM02.Section4Feasible
import GraphMinor.GM02.Section4Loops
import GraphMinor.GM02.TerminatedAlgorithm
import GraphMinor.GM02.TopologicalAlgorithm
import GraphMinor.GM02.TopologicalPatterns
import GraphMinor.GM02.MultiMinorScan
import GraphMinor.GM02.TreeWidthRecognition

/-!
# Graph Minors II. Algorithmic aspects of tree-width

N. Robertson and P. D. Seymour, J. Algorithms 7 (1986) 309–322.

This file lists every numbered result of the paper in order. The proofs are in the other
files of this folder and, for algorithms, in `GraphMinor/Compute/`. Where a printed statement
or proof has an error, the docstring says so and refers to `corrections/GM02.md`.
-/

public section

namespace GraphMinor.GM02

/-! ## Section 1. INTRODUCTION -/

section

open GraphMinor.Compute Graph Set Classical

/-- Graph Minors II, (1.1), page 310:
"For any fixed planar graph $H$, there is a polynomial algorithm to decide if
 the input graph has a minor isomorphic to $H$."

This is (4.1), as in the paper. The program returns zero when `H` is a minor
and one otherwise. Its time is polynomial in the vertex count. The proof runs
the program of (4.9) for `H`, with `w` from (4.10). -/
theorem algorithm_1_1 (H : Graph ℕ (ℕ × ℕ × ℕ)) (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hPlanar : IsPlanar H) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg =
          if ¬ IsIsoMinor H x.G.toGMDigraph.toGraph then 1 else 0)
        P (fun n => (n + 1) ^ c) := by exact GraphMinor.GM02.algorithm_1_1_proof H hVH hEH hPlanar

end

section

open Graph GraphMinor.Compute Set Classical

/-- Graph Minors II, (1.2), page 310:
"For any fixed integer $w$, there is a polynomial algorithm to decide if the
input graph has tree-width $\le w$."

This is (5.3), as in the paper. The existential natural bound expresses
comparison with the integer `w`, including negative `w`. The program returns
one for tree-width at most `w` and zero otherwise. Its time is polynomial in
the vertex count. -/
theorem algorithm_1_2 (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg = if (∃ k : ℕ, (k : ℤ) ≤ w ∧
          TreeWidthLE x.G.toGMDigraph.toGraph k) then 1 else 0)
        P (fun n => (n + 1) ^ c) := by exact GraphMinor.GM02.algorithm_1_2_proof w

end

section

open GraphMinor.Compute

/-- Graph Minors II, (1.3), page 310:
"For any fixed integers $k, w$ there is a polynomial algorithm to solve the
DISJOINT CONNECTING PATHS problem (stated below) for $k$ paths, in graphs of
tree-width $\le w$."

The proof rewrites the input as a terminated graph and runs the program of
(3.2). The number of paths is a natural number, and a negative width bound
gives an empty input promise. The `2k` ends must be distinct
(`IsTermination`), as in the paper's definition of a termination. The time
is polynomial in the number of vertices. -/
theorem algorithm_1_3 (k : ℕ) (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime (dpSize (k := k))
        (fun x s => s.arrs inArr = encDPIn x ∧ IsTermination x ∧
          ∃ q : ℕ, (q : ℤ) ≤ w ∧ TreeWidthLE x.G.toGMDigraph.toGraph q)
        IsValidDPOutput P (fun n => (n + 1) ^ c) := by exact GraphMinor.GM02.algorithm_1_3_proof k w

end

/-! ## Section 2. PRELIMINARIES -/

section

open Graph SimpleGraph Set Classical

universe u v w

/-- Graph Minors II, (2.1), page 311:
"For $i \in I$ and $v \in V(G)$, either $v \in X_i$, or there is a branch
of $T$ at $i$ which contains all $j \in I$ with $v \in X_j$."

Choose one bag containing `v` by (W1). Every tree path to another such bag
stays in bags containing `v`, by (W3), and hence avoids `i`. -/
theorem theorem_2_1 {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) (i : ι) (v : α) (hv : v ∈ V(G)) :
    v ∈ X i ∨ ∃ B : BranchAt T i, ∀ j, v ∈ X j → j ∈ branchVertices B := by exact GraphMinor.GM02.theorem_2_1_proof hD i v hv

end

section

open Graph SimpleGraph Set Classical

universe u v w

/-- Graph Minors II, (2.2), page 311:
"If $v, v' \notin X_i$ and $v, v'$ are adjacent in $G$ then $T_i(v) = T_i(v')$."

By (W2), both ends lie in one bag. Both branches contain its tree node,
so the branches are equal. -/
theorem theorem_2_2 {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) (i : ι)
    (v v' : (V(G) \ X i : Set α)) (hadj : G.Adj v.val v'.val) :
    vertexBranch hD i v = vertexBranch hD i v' := by exact GraphMinor.GM02.theorem_2_2_proof hD i v v' hadj

end

section

open Graph SimpleGraph Set Classical

universe u v w

/-- Graph Minors II, (2.3), pages 311–312:
"If $v, v \notin X_i$ and are not separated in $G$ by $X_i$, then
$T_i(v) = T_i(v')$."
The print has "$v, v \notin X_i$", a misprint for $v, v' \notin X_i$, which the Lean uses. See
the correction to (2.3) in `corrections/GM02.md`.

Apply (2.2) successively along a walk in the graph after deleting the bag. -/
theorem theorem_2_3 {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) (i : ι) (v v' : (V(G) \ X i : Set α))
    (hreach : Relation.ReflTransGen (G.induce (V(G) \ X i)).Adj v.val v'.val) :
    vertexBranch hD i v = vertexBranch hD i v' := by exact GraphMinor.GM02.theorem_2_3_proof hD i v v' hreach

end

section

open Graph Set SimpleGraph

universe u v w

/-- Graph Minors II, (2.4), page 312:
"Let $e$ be an edge of $T$ with ends $j, j'$ say, and $N, N'$ be the vertex
sets of the two components of $T \setminus e$. Then $X_j \cap X_{j'}$
separates $\bigcup(X_i : i \in N)$ and $\bigcup(X_i : i \in N')$."

Here the two components are identified by the ends they contain. By (W1)
and (W2), an equal or adjacent pair across them has a common bag. The tree
paths to this bag force one member of the pair into the intersection by
(W3), as in the paper's proof. -/
theorem theorem_2_4 {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) {j j' : ι} (hjj' : T.Adj j j') :
    Separates G (X j ∩ X j')
      (⋃ i ∈ GM10.treeComponent T j s(j, j'), X i)
      (⋃ i ∈ GM10.treeComponent T j' s(j', j), X i) := by exact GraphMinor.GM02.theorem_2_4_proof hD hjj'

end

section

open Graph Set Classical

universe u v t

/-- Graph Minors II, (2.5), page 312:
"If the tree-decomposition has width $< w$ and $Q \subseteq V(G)$, then there
exists $X \subseteq V(G)$ with $|X| \le w$ such that every component of
$G \setminus X$ has at most $\frac{1}{2} |Q - X|$ vertices which are in $Q$."

The bag bound is the equivalent integral form of width strictly less than `w`.
The doubled component count avoids division in the statement. The proof prints
"$|(W - Y) \cap Q| = |W' \cup Q|$" for $|W' \cap Q|$ on page 313; the Lean makes the two counts
equal, as meant. See the correction to the proof of (2.5) in `corrections/GM02.md`. -/
theorem theorem_2_5 {α : Type u} {β : Type v} {ι : Type t} [Fintype ι]
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α} {Q : Set α} {w : ℕ}
    (hD : IsTreeDecomposition G T X) (hG : (V(G)).Finite)
    (hwidth : ∀ i, (X i).ncard ≤ w) (hQ : Q ⊆ V(G)) :
    ∃ S ⊆ V(G), S.ncard ≤ w ∧ ∀ a ∈ V(G) \ S,
      2 * (deletedComponent G S a ∩ Q).ncard ≤ (Q \ S).ncard := by exact GraphMinor.GM02.theorem_2_5_proof hD hG hwidth hQ

end

section

open Graph Set Classical

universe u v

/-- Graph Minors II, (2.6), page 313:
"If $G$ has tree-width $< w$ and $Q \subseteq V(G)$, there exists a separation
$(H, H')$ of $G$ such that $|V(H) \cap V(H')| \le w$ and"
$$
\begin{aligned}
&|(V(H) - V(H')) \cap Q|, |(V(H') - V(H)) \cap Q| \\
&\quad \le \frac{2}{3} |Q - (V(H) \cap V(H'))|.
\end{aligned}
$$

The inequalities are multiplied by three to avoid division. -/
theorem theorem_2_6 {α : Type u} {β : Type v} (G : Graph α β)
    (hV : (V(G)).Finite) (hE : (E(G)).Finite) {w : ℕ} {Q : Set α}
    (hw : treeWidth G hV hE < w) (hQ : Q ⊆ V(G)) :
    ∃ H H', IsSeparation G H H' ∧ (V(H) ∩ V(H')).ncard ≤ w ∧
      3 * ((V(H) \ V(H')) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard ∧
      3 * ((V(H') \ V(H)) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard := by exact GraphMinor.GM02.theorem_2_6_proof G hV hE hw hQ

end

section

open Graph Set SimpleGraph Classical

universe u v u' v'

/-- Graph Minors II, (2.7), page 314:
"If $G$ has tree-width $< w$, so does every minor of $G$." -/
theorem theorem_2_7 {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} (hVG : (V(G)).Finite)
    (hEG : (E(G)).Finite) (hVH : (V(H)).Finite) (hEH : (E(H)).Finite)
    (hminor : IsIsoMinor H G) {w : ℕ} (hw : treeWidth G hVG hEG < w) :
    treeWidth H hVH hEH < w := by exact GraphMinor.GM02.theorem_2_7_proof hVG hEG hVH hEH hminor hw

end

section

open Graph Set Classical

universe u v

/-- **Graph Minors II, (2.8)** (page 315):
"The number of different crossing schemes for $\mathscr{A}_0$ with respect to $(H, H')$ is at most
$$
\max(2, (|X| + k)^{|X|}).
$$"

$\\max(2, (|X| + k)^{|X|})$.

The proof supplies the enumeration omitted in the paper. Finiteness is
included explicitly, so the natural cardinal bound cannot hold merely
because an infinite type has natural cardinal zero. -/
theorem theorem_2_8 {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hV : (V(G)).Finite) (hsep : IsSeparation G H H') (A₀ : Termination V(G)) :
    Finite (CrossingScheme G H H' A₀) ∧
      Nat.card (CrossingScheme G H H' A₀) ≤
        max 2 (((V(H) ∩ V(H')).ncard + A₀.index) ^ (V(H) ∩ V(H')).ncard) := by exact GraphMinor.GM02.theorem_2_8_proof hV hsep A₀

end

section

open Graph SimpleGraph Set
open GraphMinor.GM02.FeasibilityCounterexample

/- A crossing scheme satisfying the printed definition has both induced
terminated graphs feasible, although the original terminated graph is not.
Thus II (2.9), page 315, is false without a correction at original terminals. -/
example :
    IsSeparation star leftGraph rightGraph ∧
      ¬originals.Feasible star ∧
      scheme.left.Feasible (leftGraph.deleteVerts scheme.reservedLeft) ∧
      scheme.right.Feasible (rightGraph.deleteVerts scheme.reservedRight) := by exact GraphMinor.GM02.FeasibilityCounterexample.counterexample_2_9

end

section

open Graph Set

universe u v

/-- **Graph Minors II, (2.9)** (page 315):
"Let $(G, \mathscr{A}_0)$ be a terminated graph and let $(H, H')$ be a separation of $G$. Then $(G, \mathscr{A}_0)$ is feasible if and only if there is a crossing scheme for $\mathscr{A}_0$ with respect to $(H, H')$ such that both induced terminated graphs are feasible."

Graph Minors II, (2.9), page 315, with corrected induced graphs.
The statement printed in II is false: its deletions allow a side path
to pass internally through an original terminal assigned elsewhere.
`CrossingScheme.inducedLeft` and `CrossingScheme.inducedRight` also delete
such original separator terminals. The crossing-scheme conditions are
unchanged. With this correction, feasibility is equivalent to existence
of a crossing scheme with both induced terminated graphs feasible.

Each induced side also deletes original separator terminals absent from its new termination. This
corrects a false printed equivalence. See the correction to (2.9) in `corrections/GM02.md`. -/
theorem theorem_2_9 {α : Type u} {β : Type v} {G H H' : Graph α β}
    (A : Termination V(G)) (hsep : IsSeparation G H H') :
    A.Feasible G ↔ ∃ C : CrossingScheme G H H' A,
      C.left.Feasible C.inducedLeft ∧ C.right.Feasible C.inducedRight := by exact GraphMinor.GM02.theorem_2_9_proof A hsep

end

section

open Graph Set Classical

universe u v

/-- **Graph Minors II, (2.10)** (page 315):
"The index of any terminated graph induced by a crossing scheme for $\mathscr{A}_0$ with respect to $(H, H')$ is at most
$$
\begin{aligned}
&\frac{1}{2} |V(H) \cap V(H')| + \frac{1}{2} \max(|(V(H) - V(H')) \cap S(\mathscr{A}_0)|, \\
&\qquad |(V(H') - V(H)) \cap S(\mathscr{A}_0)|).
\end{aligned}
$$"

Graph Minors II, (2.10), page 315: the index of either induced
terminated graph is at most half the separator size plus half the larger
number of original terminals in an exclusive side. The induced graph's
vertex deletions do not change its termination or its index. -/
theorem theorem_2_10 {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hV : (V(G)).Finite) (hsep : IsSeparation G H H') (A : Termination V(G))
    (C : CrossingScheme G H H' A) :
    (C.left.index : ℚ) ≤ (V(H) ∩ V(H')).ncard / 2 +
      (max ((V(H) \ V(H')) ∩ A.support).ncard
        ((V(H') \ V(H)) ∩ A.support).ncard : ℕ) / 2 ∧
    (C.right.index : ℚ) ≤ (V(H) ∩ V(H')).ncard / 2 +
      (max ((V(H) \ V(H')) ∩ A.support).ncard
        ((V(H') \ V(H)) ∩ A.support).ncard : ℕ) / 2 := by exact GraphMinor.GM02.theorem_2_10_proof hV hsep A C

end

/-! ## Section 3. The Basic Algorithm -/

section

open GraphMinor.Compute

/-- Graph Minors II, (3.1), page 316:
"For any fixed integer $w$, there is a polynomial algorithm which has input
a simple graph $G$ and a subset $Q$ of $V(G)$, and which has output either"
a separation of order at most $w$ satisfying the two printed two-thirds
balance bounds, or "a (valid) statement that no such separation exists."

`GM02Alg31Input.correct` includes actual side arrays for a successful
separation, and excludes every such separation for a negative output.
The program follows the paper's exhaustive component test and component
grouping. Degree `w.toNat + 3` bounds its vertex-count running time. -/
theorem algorithm_3_1 (w : ℤ) :
    ∃ P : Cmd, ComputesRelInTime gm02Alg31Size (fun x s => s.arrs inArr = x.enc)
      (fun x s => x.correct w s) P (fun n => (n + 1) ^ (w.toNat + 3)) := by exact GraphMinor.GM02.algorithm_3_1_proof w

end

section

open GraphMinor.Compute

/-- Graph Minors II, (3.2), page 318:
"For any two fixed integers $w$, $k$ there is a polynomial algorithm which has input a terminated graph $(G, \mathcal{A})$ of index $\le k$, and outputs either"

"(i) $(G, \mathcal{A})$ is feasible, or"
"(ii) $(G, \mathcal{A})$ is not feasible, or"
"(iii) $G$ has tree-width $> w$."

Follow the paper's alternating recursion and its final underlying-simple
graph reduction. The input contains only original multiplicities and
terminal endpoints. The three flags have the stated meanings for the
original graph, including its loops and parallel edges. -/
theorem algorithm_3_2 (w k : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime gm02MultiTerminatedSize
        (fun x s => s.arrs inArr = x.enc ∧ (x.A.index : ℤ) ≤ k)
        (fun x s => x.correct w s) P (fun n => (n + 1) ^ c) := by exact GraphMinor.GM02.algorithm_3_2_proof w k

end

/-! ## Section 4. APPLICATIONS OF THE BASIC ALGORITHM -/

section

open GraphMinor.Compute Graph Set Classical

/-- Graph Minors II, (4.1), page 318:
"For any fixed planar graph $H$, there is a polynomial algorithm to decide if
 the input graph has a minor isomorphic to $H$."

The proof is the paper's: run the program of (4.9) for `H` with `w` from
(4.10). The answer "tree-width above `w`" means that `H` is a minor, by (4.10).
Zero means that the minor exists and one means it does not. -/
theorem algorithm_4_1 (H : Graph ℕ (ℕ × ℕ × ℕ)) (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hPlanar : IsPlanar H) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg =
          if ¬ IsIsoMinor H x.G.toGMDigraph.toGraph then 1 else 0)
        P (fun n => (n + 1) ^ c) := by exact GraphMinor.GM02.algorithm_4_1_proof H hVH hEH hPlanar

end

section

open Graph Set Relation

universe u v

/-- Graph Minors II, (4.2), page 318:
"*If $V(H) \subseteq V(G)$ and $e$ is a loop of $G$ incident with $v \in V(H)$, and
no loop of $H$ is incident with $v$, then $G$ topologically contains $H$ if and only
if $G \setminus e$ does.*"

The paper says this is clear. The hypotheses `V(H) ⊆ V(G)` and `v ∈ V(H)` are
not needed in the proof. -/
theorem theorem_4_2 {α : Type u} {β : Type v}
    {G H : Graph α β} {e : β} {v : α} (_hVH : V(H) ⊆ V(G))
    (he : G.IsLoopAt e v) (_hv : v ∈ V(H)) (hH : ∀ f, ¬ H.IsLoopAt f v) :
    TopologicallyContains G H ↔ TopologicallyContains (G.deleteEdges {e}) H := by exact GraphMinor.GM02.theorem_4_2_proof _hVH he _hv hH

end

section

open Graph Set Relation

universe u v

/-- Graph Minors II, (4.3), page 318:
"*If $V(H) \subseteq V(G)$, and $e$ is a loop of $G$ and $f$ is a loop of $H$, both
incident with the same vertex, then $G$ topologically contains $H$ if and only if
$G \setminus e$ topologically contains $H \setminus f$.*"

The paper says this is clear. The hypothesis `V(H) ⊆ V(G)` is not needed in the
proof. -/
theorem theorem_4_3 {α : Type u} {β : Type v}
    {G H : Graph α β} {e f : β} {v : α} (_hVH : V(H) ⊆ V(G))
    (he : G.IsLoopAt e v) (hf : H.IsLoopAt f v) :
    TopologicallyContains G H ↔
      TopologicallyContains (G.deleteEdges {e}) (H.deleteEdges {f}) := by exact GraphMinor.GM02.theorem_4_3_proof _hVH he hf

end

section

open Graph Set Classical

universe u v

/-- Graph Minors II, (4.4), page 319:
"*$G'$ has tree-width at most $2k$ more than the tree-width of $G$.*"

The paper's reason: "we may obtain a subgraph of $G$ by deleting $2k$ vertices of
$G'$". From a tree-decomposition of `G` we remove the vertices of `H` from
each bag and add the `2k` new vertices to each bag. The hypotheses before (4.4)
on loops and on `V(H) ⊆ V(G)` are not needed. -/
theorem theorem_4_4 {α : Type u} {β : Type v}
    (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) (hV : V(G).Finite)
    (hE : E(G).Finite) :
    treeWidth (splitGraph G H edge) (splitGraph_vertexSet_finite G H edge hV)
      (splitGraph_edgeSet_finite G H edge hV) ≤ treeWidth G hV hE + 2 * k := by exact GraphMinor.GM02.theorem_4_4_proof G H edge hV hE

end

section

open Graph Set Relation SimpleGraph Classical

/- Graph Minors II, (4.5), page 319, fails for a loop of `H`. -/
example :
    V(counterLoopH) ⊆ V(counterG) ∧
      (∀ e a, a ∈ V(counterLoopH) → ¬ counterG.IsLoopAt e a) ∧
      (splitTermination counterG counterLoopH counterLoopEdge).Feasible
        (splitGraph counterG counterLoopH counterLoopEdge) ∧
      ¬ TopologicallyContains counterG counterLoopH := by exact GraphMinor.GM02.counterexample_4_5_loop

end

section

open Graph Set Relation SimpleGraph Classical

/- Graph Minors II, (4.5), page 319, fails for two edges of `H` with the same
ends. -/
example :
    V(counterParH) ⊆ V(counterG) ∧
      (∀ e a, a ∈ V(counterParH) → ¬ counterG.IsLoopAt e a) ∧
      (splitTermination counterG counterParH counterParEdge).Feasible
        (splitGraph counterG counterParH counterParEdge) ∧
      ¬ TopologicallyContains counterG counterParH := by exact GraphMinor.GM02.counterexample_4_5_parallel

end

section

open Graph Set Relation SimpleGraph Classical

universe u v

/-- Graph Minors II, (4.5), page 319:
"*$G$ topologically contains $H$ if and only if $(G', \mathcal{A})$ is feasible.*"

Here `(G', 𝒜)` is `splitGraph G H edge` with `splitTermination G H edge`,
built in `Section4Split.lean` from the enumeration `edge` of the edges of `H`.
The paper says the result is "easy to see". As printed it is false when `H` has
a loop or two edges with the same ends (see the correction to (4.5) in `corrections/GM02.md`), so we
add the hypotheses `hHloop` and `hHpar`. The hypotheses printed before (4.4) are
`hVH` and `_hGloop`. The forward direction uses none of them. The converse
uses `hVH`, `hHloop` and `hHpar`, but not `_hGloop`.

The pattern has no loops or parallel edges, which the converse needs. -/
theorem theorem_4_5 {α : Type u} {β : Type v}
    {G H : Graph α β} {k : ℕ} (edge : Fin k ≃ E(H)) (hVH : V(H) ⊆ V(G))
    (_hGloop : ∀ e a, a ∈ V(H) → ¬ G.IsLoopAt e a)
    (hHloop : ∀ f a, ¬ H.IsLoopAt f a)
    (hHpar : ∀ f g a b, H.IsLink f a b → H.IsLink g a b → f = g) :
    TopologicallyContains G H ↔ (splitTermination G H edge).Feasible (splitGraph G H edge) := by exact GraphMinor.GM02.theorem_4_5_proof edge hVH _hGloop hHloop hHpar

end

section

open Graph Set GraphMinor.Compute

/-- **Graph Minors II, (4.6)** (page 319):
"For any fixed graph $H_0$ and fixed integer $w$, there is a polynomial algorithm which has input graphs $G$, $H$ with $V(H) \subseteq V(G)$ such that $H$ is isomorphic to a subgraph of $H_0$, and which has output either"

The input type supplies the vertex inclusion. The only remaining input
promise is isomorphism to a subgraph of the fixed graph. The split
construction uses edge vertices and incidence choices to cover loops
and parallel edges, where the printed (4.5) fails.

The corrected split construction reserves an original edge for each terminal and uses width bound
`max w 2 + 2k`. See the correction to (4.5) in `corrections/GM02.md`. -/
theorem algorithm_4_6 {A B : Type*} (H₀ : Graph A B)
    (hE : E(H₀).Finite) (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime gm02TopologicalSize
        (fun x s => s.arrs inArr = x.enc ∧
          ∃ L : Graph A B, L ≤ H₀ ∧ Nonempty (Iso x.H L))
        (fun x s => x.correct w s) P (fun n => (n + 1) ^ c) := by exact GraphMinor.GM02.algorithm_4_6_proof H₀ hE w

end

section

open Graph Set GraphMinor.Compute

/-- Graph Minors II, (4.7), page 319, with its proof on page 320:
"For any fixed graph $H$ and fixed integer $w$, there is a polynomial algorithm which has input a graph $G$, and which has output one of"

"(i) there is a graph isomorphic to $H$ topologically contained by $G$, or"
"(ii) there is no such graph, or"
"(iii) $G$ has tree-width $> w$."

Enumerate vertex injections as in the paper and run the complete (4.6)
program on each constructed labelled input. The fixed graph is numbered
once, and the host input contains only its original edge-list encoding. -/
theorem algorithm_4_7 {A B : Type*} (H : Graph A B)
    (hV : V(H).Finite) (hE : E(H).Finite) (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime GM02EdgeListInput.size (fun G s => s.arrs inArr = G.enc)
        (fun G s => gm02IsomorphicTopologicalCorrect H w G s) P (fun n => (n + 1) ^ c) := by exact GraphMinor.GM02.algorithm_4_7_proof H hV hE w

end

section

open Graph Set Classical

universe u v

/-- Graph Minors II, (4.8), page 320:
"For any graph $H$ there is a finite set $H_1, \dots, H_r$ of graphs such
that for any graph $G$, $G$ has a minor isomorphic to $H$ if and only if $G$
topologically contains a graph isomorphic to one of $H_1, \dots, H_r$."

The proof gives `F` as the set of splits of `H`, one of each up to
isomorphism (`GraphMinor.GM02.theorem_4_8_proof`). Graphs use the standard
numbered source types. -/
theorem theorem_4_8 {α : Type u} {β : Type v} (H : Graph α β)
    (hVH : V(H).Finite) (hEH : E(H).Finite) :
    ∃ F : Finset (Graph ℕ (ℕ × ℕ × ℕ)),
      (∀ J ∈ F, V(J).Finite ∧ E(J).Finite) ∧
      ∀ G : Graph ℕ (ℕ × ℕ × ℕ), V(G).Finite → E(G).Finite →
        (IsIsoMinor H G ↔ ∃ J ∈ F, ∃ L : Graph ℕ (ℕ × ℕ × ℕ),
          TopologicallyContains G L ∧ Nonempty (Iso J L)) := by
  obtain ⟨F, hsplit, -, hpatterns⟩ := GraphMinor.GM02.theorem_4_8_proof H hVH hEH
  exact ⟨F, fun J hJ => ⟨((hsplit J hJ).isIsoMinor hVH hEH).1, ((hsplit J hJ).isIsoMinor hVH hEH).2.1⟩, hpatterns⟩

end

section

open Graph Set GraphMinor.Compute

/-- Graph Minors II, (4.9), page 320:
"For any fixed graph $H$ and fixed number $w$, there is a polynomial algorithm which has input a graph $G$, and has output either"

"(i) $G$ has a minor isomorphic to $H$, or"
"(ii) $G$ has no minor isomorphic to $H$, or"
"(iii) $G$ has tree-width $> w$."

Apply the complete (4.7) program to the fixed finite pattern family of
(4.8), in order, exactly as in the paper's proof. Each pattern's input
is constructed from the ordinary host encoding by the RAM. -/
theorem algorithm_4_9 {A B : Type*} (H : Graph A B)
    (hV : V(H).Finite) (hE : E(H).Finite) (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime GM02EdgeListInput.size (fun G s => s.arrs inArr = G.enc)
        (fun G s => (s.regs outReg = 1 ∧ IsIsoMinor H G.graph) ∨
          (s.regs outReg = 0 ∧ ¬IsIsoMinor H G.graph) ∨
          (s.regs outReg = 2 ∧ w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ)))
        P (fun n => (n + 1) ^ c) := by exact GraphMinor.GM02.algorithm_4_9_proof H hV hE w

end

section

open Graph Set

universe u v u' v'

/-- Graph Minors II, (4.10), page 320, cited from Graph Minors V:
"For every planar graph $H$ there is a number $w$ such that every graph with no
minor isomorphic to $H$ has tree-width $\le w$."

This is V (1.5). V's vertex bags satisfy II's (W1)–(W3). -/
theorem theorem_4_10 {α' : Type u'} {β' : Type v'} (H : Graph α' β') (hH : IsPlanar H)
    {α : Type u} {β : Type v} :
    ∃ w : ℕ, ∀ G : Graph α β, V(G).Finite → E(G).Finite →
      ¬ IsIsoMinor H G → TreeWidthLE G w := by
  exact GraphMinor.GM02.theorem_4_10_proof H hH

end

/-! ## Section 5. AN ALGORITHM FOR TREE-WIDTH -/

section

open Graph Set

universe u v

/-- Graph Minors II, (5.1), page 320:
"Let $w$ be a number, and let $\mathcal{C}$ be a set of graphs each with
tree-width $\le w$. Suppose that no member of $\mathcal{C}$ is isomorphic to a
minor of another member. Then $\mathcal{C}$ is finite."

Apply the proved IV (1.5) to a sequence of distinct members if the class
were infinite. The comparable pair it gives contradicts the antichain.

The proof applies IV (1.5) after converting the width convention. -/
theorem theorem_5_1 {α : Type u} {β : Type v} (w : ℕ) (C : Set (Graph α β))
    (hV : ∀ G ∈ C, V(G).Finite) (hE : ∀ G ∈ C, E(G).Finite)
    (hwidth : ∀ G ∈ C, TreeWidthLE G w)
    (hanti : ∀ G ∈ C, ∀ H ∈ C, G ≠ H → ¬ IsIsoMinor G H) : C.Finite := by exact GraphMinor.GM02.theorem_5_1_proof w C hV hE hwidth hanti

end

section

open Graph Set

universe u v

/-- Graph Minors II, (5.2), pages 320–321:
"For any fixed number $w$, there is a finite set of graphs $H_1, \dots, H_r$
such that for any graph $G$, $G$ has tree-width $> w$ if and only if $G$ has a
minor isomorphic to one of $H_1, \dots, H_r$."

The proof is the paper's (page 321). Every graph of tree-width more than `w`
contains, as a subgraph, one of tree-width exactly `w + 1`. Graphs of
tree-width at most `w + 1` have no infinite antichain by IV (1.5), as in
(5.1), so finitely many of them cover all others. -/
theorem theorem_5_2 (w : ℕ) :
    ∃ B : Finset (Graph ℕ (ℕ × ℕ × ℕ)),
      (∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ ¬ TreeWidthLE H w) ∧
      ∀ G : Graph ℕ (ℕ × ℕ × ℕ), V(G).Finite → E(G).Finite →
        (¬ TreeWidthLE G w ↔ ∃ H ∈ B, IsIsoMinor H G) := by exact GraphMinor.GM02.theorem_5_2_proof w

end

section

open Graph GraphMinor.Compute Set Classical

/-- Graph Minors II, (5.3), page 321:
"For any fixed number $w$, there is a polynomial algorithm which, given a
graph $G$, decides if $G$ has tree-width $> w$."

The proof is the paper's: run the program of (4.9) for each graph of the
finite set of (5.2). The program returns zero exactly when the graph has
tree-width above `w`, and one otherwise. A negative `w` is allowed: then no
graph qualifies, and the program answers zero. -/
theorem algorithm_5_3 (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg = if (∃ k : ℕ, (k : ℤ) ≤ w ∧
          TreeWidthLE x.G.toGMDigraph.toGraph k) then 1 else 0)
        P (fun n => (n + 1) ^ c) := by exact GraphMinor.GM02.algorithm_5_3_proof w

end

section

open Graph GraphMinor.Compute Set Classical

/-- Graph Minors II, (5.4), page 321:
"Let $\mathcal{F}$ be a set of graphs, such that for any two graphs $G$, $G'$,
if $G \in \mathcal{F}$ and $G'$ is isomorphic to a minor of $G$ then
$G' \in \mathcal{F}$. Suppose that there is a number $w$ such that all members
of $\mathcal{F}$ have tree-width $\le w$. Then there is a polynomial algorithm
to test if an arbitrary graph is in $\mathcal{F}$."

The paper leaves the proof to the reader as an extension of (5.3). The
minimal graphs outside the class form a finite set, and the program of (4.9)
for these graphs decides membership. The program returns one for members and
zero otherwise. -/
theorem algorithm_5_4 (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ)))
    (hclosed : ∀ ⦃G₁ G₂ : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      V(G₁).Finite → E(G₁).Finite → V(G₂).Finite → E(G₂).Finite →
      IsIsoMinor G₁ G₂ → G₂ ∈ ℱ → G₁ ∈ ℱ)
    (w : ℕ)
    (hwidth : ∀ G ∈ ℱ, V(G).Finite → E(G).Finite → TreeWidthLE G w) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg = if x.G.toGMDigraph.toGraph ∈ ℱ then 1 else 0)
        P (fun n => (n + 1) ^ c) := by exact GraphMinor.GM02.algorithm_5_4_proof ℱ hclosed w hwidth

end

section

open GraphMinor.Compute Graph Set Classical

/-- Graph Minors II, (5.5), page 321:
"Let $\mathcal{F}$ be any set of graphs, membership of which is preserved under
isomorphism and under taking minors. Suppose that some planar graph is not in
$\mathcal{F}$. Then there is a polynomial algorithm to test if an arbitrary graph
is in $\mathcal{F}$."

The proof is the paper's: a member of the class has no minor isomorphic to the
planar graph `H` outside it, so (4.10) bounds its tree-width, and (5.4)
applies. Minor closure under `IsIsoMinor` includes preservation under
isomorphism. The program returns one for members and zero otherwise. -/
theorem algorithm_5_5 (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ)))
    (hclosed : ∀ ⦃G₁ G₂ : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      V(G₁).Finite → E(G₁).Finite → V(G₂).Finite → E(G₂).Finite →
      IsIsoMinor G₁ G₂ → G₂ ∈ ℱ → G₁ ∈ ℱ)
    (H : Graph ℕ (ℕ × ℕ × ℕ)) (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hPlanar : IsPlanar H) (hH : H ∉ ℱ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg = if x.G.toGMDigraph.toGraph ∈ ℱ then 1 else 0)
        P (fun n => (n + 1) ^ c) := by exact GraphMinor.GM02.algorithm_5_5_proof ℱ hclosed H hVH hEH hPlanar hH

end

end GraphMinor.GM02
