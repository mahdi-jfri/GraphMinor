module

public import GraphMinor.Compute.GM06Alg34Polynomial
public import GraphMinor.Compute.GM06Algorithm57
public import GraphMinor.Compute.GM06Algorithm57Loop
public import GraphMinor.Compute.GM06SuccessorDegreeTime
public import GraphMinor.GM06.Alg34ProgramExec
public import GraphMinor.GM06.Alg511Algorithm
public import GraphMinor.GM06.Alg511BinaryDecision
public import GraphMinor.GM06.Alg57InputRep
public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.DiscRegions
public import GraphMinor.GM06.EdgeChart
public import GraphMinor.GM06.Euler
public import GraphMinor.GM06.Section2Count
public import GraphMinor.GM06.Section2Dual
public import GraphMinor.GM06.Section3Basic
public import GraphMinor.GM06.Section3Main
public import GraphMinor.GM06.Section4
public import GraphMinor.GM06.Section5
public import GraphMinor.GM11.RadialBasics
public import GraphMinor.GM11.RadialChord
public import GraphMinor.Surface.ArcInPath
public import GraphMinor.Surface.ArcTools
public import GraphMinor.Surface.Jordan
import GraphMinor.GM06.Alg34Algorithm
import GraphMinor.GM06.Alg57Algorithm
import GraphMinor.GM06.DualExists
import GraphMinor.GM06.Section3Dual
import GraphMinor.GM06.Section4Conclusion
import GraphMinor.GM06.Section4Main
import GraphMinor.GM06.Section5Equivalence
import GraphMinor.GM06.Section5Feasibility
import GraphMinor.GM06.Section5HelixPullback
import GraphMinor.GM06.Section5Initial
import GraphMinor.GM06.Section5Interval
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5TightHelix

/-!
# Graph Minors VI. Disjoint paths across a disc

N. Robertson and P. D. Seymour, J. Combin. Theory Ser. B 41 (1986) 115–138.

This file lists every numbered result of the paper in order. The proofs are in the other
files of this folder and, for algorithms, in `GraphMinor/Compute/`. Where a printed statement
or proof has an error, the docstring says so and refers to `corrections/GM06.md`.
-/

public section

namespace GraphMinor.GM06

/-! ## Section 1. INTRODUCTION -/

/-! ## Section 2. DIVISIONS ON A CIRCLE -/

section

open Set Function Topology GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (2.1)** (page 117):
"$\Delta^*$ is cross-free, for any $\Delta$." -/
theorem theorem_2_1 :
  ∀ {S : Type u} [TopologicalSpace S] (C U : Set S) (Δ : Set (Set S)),
    IsOArc C → IsDivision Δ → divisionUnion Δ ⊆ C →
    IsDualPointSet C (divisionUnion Δ) U →
    IsCrossFree C (dualDivision C U Δ) := by exact GraphMinor.GM06.theorem_2_1_proof

end

section

open Set Function Topology GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (2.2)** (page 117):
"If $\Delta$ is cross-free then $\Delta^{**} = \Delta$." -/
theorem theorem_2_2 :
  ∀ {S : Type u} [TopologicalSpace S] (C U : Set S) (Δ : Set (Set S)),
    IsOArc C → IsDivision Δ → (divisionUnion Δ).Finite → divisionUnion Δ ⊆ C →
    IsDualPointSet C (divisionUnion Δ) U → IsCrossFree C Δ →
    doubleDualDivision C U Δ = Δ := by exact GraphMinor.GM06.theorem_2_2_proof

end

section

open Set Function Topology GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (2.3)** (page 118):
"If $W \ne \emptyset$, one of $\Delta, \Delta^*$ has a member with cardinality $1$." -/
theorem theorem_2_3 :
  ∀ {S : Type u} [TopologicalSpace S] (C U : Set S) (Δ : Set (Set S)),
    IsOArc C → IsDivision Δ → (divisionUnion Δ).Finite → divisionUnion Δ ⊆ C →
    IsDualPointSet C (divisionUnion Δ) U →
    (divisionUnion Δ ∪ U).Nonempty →
    ∃ γ ∈ Δ ∪ dualDivision C U Δ, γ.ncard = 1 := by exact GraphMinor.GM06.theorem_2_3_proof

end

section

open Set Function Topology GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (2.4)** (page 118):
"If $\Delta$ is cross-free and $x, y \in W$, then
$$\begin{aligned}
\Delta(x, y) - \Delta^*(x, y) &= 1 &&\text{if } x, y \in V \\
&= -1 &&\text{if } x, y \in U. \\
&= 0 &&\text{otherwise.}
\end{aligned}$$" -/
theorem theorem_2_4 :
  ∀ {S : Type u} [TopologicalSpace S] (C U : Set S) (Δ : Set (Set S)) (x y : S),
    IsOArc C → IsDivision Δ → (divisionUnion Δ).Finite → divisionUnion Δ ⊆ C →
    IsDualPointSet C (divisionUnion Δ) U → IsCrossFree C Δ →
    x ∈ divisionUnion Δ ∪ U → y ∈ divisionUnion Δ ∪ U →
    ((x ∈ divisionUnion Δ ∧ y ∈ divisionUnion Δ →
        (divisionCount C Δ x y : ℤ) - (divisionCount C (dualDivision C U Δ) x y : ℤ) = 1) ∧
     (x ∈ U ∧ y ∈ U →
        (divisionCount C Δ x y : ℤ) - (divisionCount C (dualDivision C U Δ) x y : ℤ) = -1) ∧
     (¬ (x ∈ divisionUnion Δ ∧ y ∈ divisionUnion Δ) → ¬ (x ∈ U ∧ y ∈ U) →
        (divisionCount C Δ x y : ℤ) - (divisionCount C (dualDivision C U Δ) x y : ℤ) = 0)) := by exact GraphMinor.GM06.theorem_2_4_proof

end

/-! ## Section 3. The Disjoint Subgraph Problem on a Disc -/

section

open Set Graph
open Set Function Topology Graph GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (3.1)** (page 120):
"If $G$ is connected and properly drawn on a disc $\Sigma$, then $G^{**} = G$. (More precisely, the
drawing of $G$ is a drawing of $G^{**}$.)" -/
theorem theorem_3_1 :
  ∀ {S : Type u} [TopologicalSpace S] (G G_dual : Drawing S),
    IsClosedDiscSpace S → IsGraphConnected G.toGraph →
    IsDiscDualDrawing G G_dual →
    IsDiscDualDrawing G_dual G := by exact GraphMinor.GM06.theorem_3_1_proof

end

section

open Set Function Topology Metric Graph GraphMinor.Surface GraphMinor.GM11
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (3.2)** (page 120):
"Let $G$ be a connected graph, properly drawn on a disc $\Sigma$. Let $\Delta$ be a
cross-free division with* $$\bigcup \Delta = V(G) \cap bd(\Sigma).$$ *Let the drawing of
$G^*$ be chosen so that* $$\bigcup \Delta^* = V(G^*) \cap bd(\Sigma).$$ *Then $\Delta$ is
feasible in $G$ if and only if $\Delta^*$ is feasible in $G^*$." -/
theorem theorem_3_2 :
  ∀ {S : Type u} [TopologicalSpace S] (G G_dual : Drawing S) (Δ : Set (Set S)),
    IsClosedDiscSpace S → IsGraphConnected G.toGraph →
    IsDivision Δ → divisionUnion Δ = G.V ∩ bd S →
    IsCrossFree (bd S) Δ → IsDiscDualDrawing G G_dual →
    (IsFeasible G.toGraph Δ ↔
      IsFeasible G_dual.toGraph (dualDivision (bd S) (G_dual.V ∩ bd S) Δ)) := by exact GraphMinor.GM06.theorem_3_2_proof

end

section

open Set Graph
open Set Function Topology Graph GraphMinor.Surface

universe u v

/-- **Graph Minors VI, (3.3)** (page 120):
"(i) If $|\delta| = 1$ for some $\delta \in \Delta$, and $\delta = \{v\}$ say, then $\Delta$ is feasible in $G$ if and only if $\Delta - \{\delta\}$ is feasible in the graph obtained from $G$ by deleting $v$.
(ii) If $G$ has a component $G'$ with no vertex in $bd(\Sigma)$ then $\Delta$ is feasible in $G$ if and only if it is feasible in the graph obtained from $G$ by deleting $V(G')$."

 -/
theorem theorem_3_3 :
    (∀ {α : Type u} {β : Type v} (G : Graph α β) (Δ : Set (Set α)) (v : α),
    IsDivision Δ → divisionUnion Δ ⊆ V(G) → {v} ∈ Δ →
    (IsFeasible G Δ ↔ IsFeasible (G.deleteVerts {v}) (Δ \ {{v}}))) ∧
    (∀ {S : Type u} [TopologicalSpace S] (G : Drawing S) (G' : Graph S (Set S)) (Δ : Set (Set S)),
    IsDivision Δ → divisionUnion Δ ⊆ G.V ∩ bd S →
    IsGraphComponent G' G.toGraph → Disjoint V(G') (bd S) →
    (IsFeasible G.toGraph Δ ↔ IsFeasible (G.toGraph.deleteVerts V(G')) Δ)) ∧
    (∀ {α : Type u} {β : Type v} (G : Graph α β) (Δ : Set (Set α)) (δ : Set α)
    (G₁ G₂ : Graph α β),
    δ ∈ Δ → IsGraphComponent G₁ G → IsGraphComponent G₂ G → G₁ ≠ G₂ →
    (δ ∩ V(G₁)).Nonempty → (δ ∩ V(G₂)).Nonempty →
    ¬ IsFeasible G Δ) ∧
    (∀ {S : Type u} [TopologicalSpace S] (G : Drawing S) (Δ : Set (Set S))
    (k : ℕ) (G_comp : Fin k → Graph S (Set S)) (Δ_part : Fin k → Set (Set S)),
    2 ≤ k → IsDivision Δ → divisionUnion Δ = G.V ∩ bd S →
    InjOn G_comp Set.univ →
    graphComponents G.toGraph = Set.range G_comp →
    (∀ i : Fin k, Δ_part i = {δ ∈ Δ | δ ⊆ V(G_comp i)}) →
    (∀ δ ∈ Δ, ∃ i : Fin k, δ ⊆ V(G_comp i)) →
    (IsFeasible G.toGraph Δ ↔ ∀ i : Fin k, IsFeasible (G_comp i) (Δ_part i))) := by exact GraphMinor.GM06.theorem_3_3_proof

end

section

open Compute

universe u

/-- Graph Minors VI, (3.4), page 121:

"(3.4) *Algorithm to decide if $\Delta$ is feasible in $G$.*"

The program reads only the supplied drawing and gap arrays. Its output
is Boolean and decides feasibility for every disc instance represented
by those arrays, in polynomial time with logarithmic machine words.

The Word RAM program uses an explicit queue in place of recursive calls, and a weighted termination
charge. These are choices of implementation: the reductions and the crossing check are the paper's.
-/
theorem algorithm_3_4 {X : GM06GapInput} {I : DiscDivInstance.{u}}
    (h : GM06GapInputRep X I.G I.Δ) {s : State}
    (hin : s.arrs 0 = X.drawing.words) (hgap : s.arrs 47 = X.discGapWords) :
    let size := X.drawing.size + X.discGapWords.length
    ∃ b s' t, Exec (wordSize 256 size) gm06Alg34Prog s s' t ∧
      t ≤ gm06Alg34TimeConstant * (size + 1) ^ 46 ∧
      s'.regs 0 = (if b then 1 else 0) ∧ (I.IsFeasibleInst ↔ b = true) := by exact GraphMinor.GM06.algorithm_3_4_proof h hin hgap

end

section

open Set Graph
open Set Function Topology Graph GraphMinor.Surface
open Classical
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (3.5)** (page 121):
"If $G$ is connected, any $(x, y)$-chain of $G^*$ corresponds to an $(x, y)$-chain of $G$, and if
$\Delta$ is cross-free the $\Delta^*$-redundancy of the first chain equals the $\Delta$-redundancy
of the second." -/
theorem theorem_3_5 :
  ∀ {S : Type u} [TopologicalSpace S] (G G_dual : Drawing S) (Δ : Set (Set S)) (x y : S)
    (A_dual : List (ChainTerm S)),
    IsClosedDiscSpace S → IsGraphConnected G.toGraph →
    IsDivision Δ → divisionUnion Δ = G.V ∩ bd S →
    IsCrossFree (bd S) Δ → IsDiscDualDrawing G G_dual →
    x ∈ (G_dual.V ∩ bd S) ∪ divisionUnion Δ →
    y ∈ (G_dual.V ∩ bd S) ∪ divisionUnion Δ →
    IsXYChain G_dual x y A_dual →
    ∃ A : List (ChainTerm S),
      IsXYChain G x y A ∧
      chainRedundancy G_dual (dualDivision (bd S) (G_dual.V ∩ bd S) Δ) x y A_dual =
        chainRedundancy G Δ x y A := by exact GraphMinor.GM06.theorem_3_5_proof

end

section

open Set Function Topology Metric unitInterval Complex GraphMinor.Surface GraphMinor.GM11
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (3.6)** (page 122):
"Let $G$ be properly drawn on a disc $\Sigma$, and let $\Delta$ be a division with"

**Graph Minors VI, (3.6)** (pages 121–122):
Let $\Gamma$ be a drawing in a closed disc $\Delta$, let $U$ be a dual point set for
$(\operatorname{bd}(\Delta), V(\Gamma) \cap \operatorname{bd}(\Delta))$, and let $\mathcal{D}$ be a
division of $V(\Gamma) \cap \operatorname{bd}(\Delta)$. Then $\mathcal{D}$ is feasible if and only
if $\mathcal{D}$ is cross-free and every $xy$-chain has non-negative redundancy, for all
$x, y \in U \cup (V(\Gamma) \cap \operatorname{bd}(\Delta))$. -/
theorem theorem_3_6 :
  ∀ {S : Type u} [TopologicalSpace S] (G : Drawing S) (Δ : Set (Set S)) (U : Set S),
    IsClosedDiscSpace S → G.IsProper →
    IsDivision Δ → divisionUnion Δ = G.V ∩ bd S →
    IsDualPointSet (bd S) (divisionUnion Δ) U →
    (IsFeasible G.toGraph Δ ↔
      IsCrossFree (bd S) Δ ∧
      ∀ x ∈ U ∪ divisionUnion Δ, ∀ y ∈ U ∪ divisionUnion Δ,
        ∀ A : List (ChainTerm S), IsXYChain G x y A →
          0 ≤ chainRedundancy G Δ x y A) := by exact GraphMinor.GM06.theorem_3_6_proof

end

/-! ## Section 4. The Cylinder -/

section

open Set GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (4.1)** (page 124):
"With $\Sigma, G, H$ as before, if there is a segment $S$ with distinct ends $s$, $t$, and $s, t$ are joined in $H$ by a path homotopic to $S$, and if either"

Graph Minors VI, (4.1), page 124: any of the three printed boundary-path
obstructions rules out a forest subgraph homotopic to the specified forest.
The proof supplies the minimal-path existence and uncrossing implicit in the
paper's statement that the proof is clear. -/
theorem theorem_4_1 :
  ∀ {S : Type u} [TopologicalSpace S] (G H : Drawing S),
    IsSurface S → G.IsProper → H.IsProper → IsGraphForest H.toGraph →
    H.V ∩ bd S = G.V ∩ bd S →
    Section4Condition41Applies G H →
    ¬ HasHomotopicForestSubgraph G H := by exact GraphMinor.GM06.theorem_4_1_proof

end

section

open Set GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- Graph Minors VI (4.2), page 125:
"If $\Sigma$ is a cylinder and neither (4.1) nor reduction 1 nor reduction 2 applies, then each component of $H$ has exactly one vertex in each cuff of $\Sigma$."
The proof on pages 125–127 uses both claims and the final comparison
graph argument.

The proof uses the paper's paragraph on page 126 only for consecutive base vertices, where the
subarc is a segment, and chains them. See the correction to the proof of (4.2) in
`corrections/GM06.md`. -/
theorem theorem_4_2 :
  ∀ (G H : Drawing ClosedCylinder),
    G.IsProper → H.IsProper → IsGraphForest H.toGraph →
    H.V ∩ bd ClosedCylinder = G.V ∩ bd ClosedCylinder →
    ¬ Section4Condition41Applies G H →
    ¬ Section4Reduction1Applies G H →
    ¬ Section4Reduction2Applies G H →
    ∀ H' : Graph ClosedCylinder (Set ClosedCylinder),
      IsGraphComponent H' H.toGraph →
      (V(H') ∩ cylinderCuff1).ncard = 1 ∧ (V(H') ∩ cylinderCuff2).ncard = 1 := by exact GraphMinor.GM06.theorem_4_2_proof

end

section

open Set Function Complex Real Topology Metric Graph GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (4.3)** (page 125):
"Let $\Sigma$ be a cylinder, and let $C$ be a cuff of $\Sigma$. Let $s, t \in C$ be distinct, and
let $S$ be a component of $C - \{s, t\}$. Let $K$ be a connected graph with $|V(K)| \ge 2$,
properly drawn on $\Sigma$ with $V(K) \subseteq S$. Then there is an edge of $K$ with distinct ends
$a, b$ say, such that $S(a, b) \cap V(K) = \emptyset$." -/
theorem theorem_4_3 :
  ∀ (C : Set ClosedCylinder) (s t : ClosedCylinder) (S_arc : Set ClosedCylinder)
    (K : Drawing ClosedCylinder),
    C ∈ cuffs ClosedCylinder → s ∈ C → t ∈ C → s ≠ t →
    S_arc ∈ componentsIn (C \ {s, t}) →
    K.IsProper → IsGraphConnected K.toGraph → 2 ≤ K.V.ncard → K.V ⊆ S_arc →
    ∃ e ∈ K.E, ∃ a ∈ K.V, ∃ b ∈ K.V,
      a ≠ b ∧ K.toGraph.IsLink e a b ∧ Disjoint (cuffSubArc C S_arc a b) K.V := by exact GraphMinor.GM06.theorem_4_3_proof

end

/-! ## Section 5. Disjoint Paths along a Cylinder -/

section

open Set GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (5.1)** (page 129):
"Suppose that none of reductions 1,..., 4 apply to $G$. Then either some $s_i$ has valency 1 and its neighbour is in $C_2$, or $\theta(\mathcal{L}) + 1/k$ is feasible.
Proof. We may assume that no $s_i$ has valency 1. But then for each $i$ the boundary of $R_i$ meets $P_i$ in exactly the vertex $s_i$; and meets $P_{i+1}$ in a vertex different from $s_{i+1}$. Thus there is a path $Q_i$ of $G$ with initial vertex $s_i$ and terminal vertex $t_i$ say, where $t_i$ is a vertex of $P_{i+1}$ different from $s_{i+1}$, with $Q_i \subseteq \Sigma_i \cup \{s_i, t_i\}$. Let $P'_i$ be the concatenation of $Q_i$ with the subpath of $P_{i+1}$ between $t_i$ and $C_2$. Then $\{P'_1, \dots, P'_k\}$ is a linkage $\mathcal{L}'$ with
$$\theta(\mathcal{L}') = \theta(\mathcal{L}) + \frac{1}{k}.$$
Now we turn to our characterization. If $f: [0, 1] \to \Sigma$ is continuous, we define
$$|f| = \{f(x): 0 \le x \le 1\}.$$
We say $f$ is $G$-normal if $e \cap |f| = \emptyset$ for every edge $e$ of $G$; that is, every point of $|f|$ is either a vertex or lies in some region of $G$. If $f$ is $G$-normal, we define $L(f) = L_G(f)$ to be
$$|\{x \in [0, 1]: f(x) \in V(G)\}|.$$"

Graph Minors VI, (5.1), page 129. In the unreduced situation,
either a valency-one start has its neighbour on the outer cuff, or
the cyclic region-path construction gives the next feasible winding. -/
theorem theorem_5_1 :
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (L : CylinderLinkage k G) (θ : ℝ),
    IsCylinderSection5Drawing k G → L.HasTheta θ →
    ¬ Section5AnyReductionApplies k G L →
    (∃ i : Fin k, vertexValency G.toGraph (cylinderM1Point k i) = 1 ∧
      ∃ e ∈ G.E, ∃ t ∈ G.V ∩ cylinderCuff2, G.toGraph.IsLink e (cylinderM1Point k i) t) ∨
    IsThetaFeasible k G (θ + 1 / (k : ℝ)) := by exact GraphMinor.GM06.theorem_5_1_proof

end

section

open Set Function Complex Real Topology Metric Graph GraphMinor.Surface GraphMinor.GM11
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (5.2)** (page 130):
"Let $\theta$ be feasible in $G$, and let $f$ be a helix. Then $L(f) \ge k|\theta(f) -
\theta|$, that is,* $$\theta(f) - k^{-1}L(f) \le \theta \le \theta(f) + k^{-1}L(f).$$"

Proved by lifting $f$ and the linkage paths to the universal cover $[1, 2] \times \mathbb{R}$,
applying `strip_crossing` (`disc_crossing`) to obtain a distinct vertex hit for each integer $m$
between $m_0$ and $m_0 + k(\theta(f) - \theta)$, and injecting into `curveVertexHits G f`. -/
theorem theorem_5_2 :
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ : ℝ) (f : Curve ClosedCylinder),
    IsCylinderSection5Drawing k G → IsThetaFeasible k G θ → IsHelix k G f →
    windingNumber f - (k : ℝ)⁻¹ * (curveL G f : ℝ) ≤ θ ∧
      θ ≤ windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ) := by exact GraphMinor.GM06.theorem_5_2_proof

end

section

open Set GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (5.3)** (page 130):
"If $\theta$ is feasible in $G$ and $\theta + 1/k$ is not, then there is a helix $f$ with $\phi(f) = \theta$.
We prove this by means of the following two lemmas.
(5.4) If $(G', \mathcal{L}')$ is produced from $(G, \mathcal{L})$ by one of the reductions 1,..., 4, and $\theta(\mathcal{L}') + 1/k$ is feasible in $G'$, then $\theta(\mathcal{L}) + 1/k$ is feasible in $G$.
Proof. This is trivial for reduction 4, and almost equally trivial for the other reductions.
(5.5) If $(G', \mathcal{L}')$ is produced from $(G, \mathcal{L})$ by one of the reductions 1,..., 4, and $f'$ is a helix in $G'$ then there is a helix $f$ in $G$ with $\phi_G(f) \le \phi_{G'}(f')$.
Proof. Again this is trivial for reduction 4, and quite easy for reductions 2 and 3. Let us deal with reduction 1. Suppose that $e$ is an edge of $G$ incident with $s_i$ but contained in $\Sigma_{i-1}$ for some $i$, and let $G'$ be obtained from $G$ by deleting $e$. Let $f'$ be a helix in $G'$. If $|f'| \cap e = \emptyset$ we may take $f = f'$ and the theorem is true. If $|f'| \cap e \ne \emptyset$, let $R'$ the region of $G'$ in which edge $e$ of $G$ is drawn; let
$$X = \{x \in [0, 1]: f'(x) \in R'\}$$
so that $X \ne \emptyset$; and let $\bar{X}$ be the closure of $X$. Choose $z_2 \in \bar{X}$, maximum. Then $f'(z_2) \in \bar{R}'$, and either $f'(z_2) \in N_2$ or $f'(z_2) \in V(G')$.
Now we may assume that
(1) There exists $z_1 \in [0, z_2)$ with $f'(z_1) \in V(G')$."

Graph Minors VI, (5.3), page 130, following the
induction on the sum of vertex and edge counts on pages 132–133.
Reduction 4 is followed by a proved application of Reduction 1, 2, or 3. -/
theorem theorem_5_3 :
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ : ℝ),
    IsCylinderSection5Drawing k G →
    IsThetaFeasible k G θ → ¬ IsThetaFeasible k G (θ + 1 / (k : ℝ)) →
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f = θ := by exact GraphMinor.GM06.theorem_5_3_proof

end

section

open Set Function Complex Real Topology Metric Graph unitInterval
open GraphMinor.Surface GraphMinor.GM11
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (5.4)** (page 130):
"If $(G', \mathcal{L}')$ is produced from $(G, \mathcal{L})$ by one of the reductions 1,..., 4, and
$\theta(\mathcal{L}') + 1/k$ is feasible in $G'$, then $\theta(\mathcal{L}) + 1/k$ is feasible in
$G$." -/
theorem theorem_5_4 :
  ∀ (k : ℕ) (G G' : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (L' : CylinderLinkage k G') (θ θ' : ℝ),
    IsCylinderSection5Drawing k G → IsCylinderSection5Drawing k G' →
    L.HasTheta θ → L'.HasTheta θ' →
    Section5ReductionStep k G L G' L' →
    IsThetaFeasible k G' (θ' + 1 / (k : ℝ)) →
    IsThetaFeasible k G (θ + 1 / (k : ℝ)) := by exact GraphMinor.GM06.theorem_5_4_proof

end

section

open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (5.5)** (page 130):
"If $(G', \mathcal{L}')$ is produced from $(G, \mathcal{L})$ by one of the reductions 1,..., 4, and $f'$ is a helix in $G'$ then there is a helix $f$ in $G$ with $\phi_G(f) \le \phi_{G'}(f')$.
Proof. Again this is trivial for reduction 4, and quite easy for reductions 2 and 3. Let us deal with reduction 1. Suppose that $e$ is an edge of $G$ incident with $s_i$ but contained in $\Sigma_{i-1}$ for some $i$, and let $G'$ be obtained from $G$ by deleting $e$. Let $f'$ be a helix in $G'$. If $|f'| \cap e = \emptyset$ we may take $f = f'$ and the theorem is true. If $|f'| \cap e \ne \emptyset$, let $R'$ the region of $G'$ in which edge $e$ of $G$ is drawn; let
$$X = \{x \in [0, 1]: f'(x) \in R'\}$$
so that $X \ne \emptyset$; and let $\bar{X}$ be the closure of $X$. Choose $z_2 \in \bar{X}$, maximum. Then $f'(z_2) \in \bar{R}'$, and either $f'(z_2) \in N_2$ or $f'(z_2) \in V(G')$.
Now we may assume that
(1) There exists $z_1 \in [0, z_2)$ with $f'(z_1) \in V(G')$."

Graph Minors VI (5.5), page 130: every reduction admits a
helix pullback with no increase in potential. The reductions use
the corrections for one path in `corrections/GM06.md`.

The one-path reductions retain the chosen side in the angular cover. See the correction to Reduction
1 and (5.5) in `corrections/GM06.md`. -/
theorem theorem_5_5 :
  ∀ (k : ℕ) (G G' : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (L' : CylinderLinkage k G') (f' : Curve ClosedCylinder),
    IsCylinderSection5Drawing k G → IsCylinderSection5Drawing k G' →
    Section5ReductionStep k G L G' L' →
    IsHelix k G' f' →
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f ≤ curvePhi k G' f' := by exact GraphMinor.GM06.theorem_5_5_proof

end

section

open Set GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (5.6)** (page 133):
"If $(G', \mathscr{L}')$ is produced from $(G, \mathscr{L})$ by one of the reductions 1,..., 4, then $\theta(\mathscr{L}') + 1/k$ is feasible in $G'$ if and only if $\theta(\mathscr{L}) + 1/k$ is feasible in $G$.
Proof. “Only if” follows from (5.4). To prove “if”, suppose that $\theta(\mathscr{L}') + 1/k$ is not feasible in $G'$. Then by (5.3) there is a helix $f'$ in $G'$ with $\phi(f') = \theta(\mathscr{L}')$, and by (5.5) there is a helix $f$ in $G$ with $\phi(f) \le \phi(f')$. But $\theta(\mathscr{L}') = \theta(\mathscr{L})$, and so
$$
\phi(f) \le \phi(f') = \theta(\mathscr{L}') = \theta(\mathscr{L}).
$$
Hence by (5.2), $\theta(\mathscr{L}) + 1/k$ is not feasible in $G$.
Let us state the algorithm.
(5.7) Algorithm to decide if $\theta(\mathscr{L}) + 1/k$ is feasible.
We apply any of the reductions which can be applied, transforming to smaller equivalent problems by (5.6). If none of the reductions apply we determine feasibility by (5.1).
The algorithm can easily be adapted to provide us with a linkage $\mathscr{L}'$ satisfying $\theta(\mathscr{L}') = \theta(\mathscr{L}) + 1/k$ if one exists. Its running time is polynomially bounded, as may easily be checked.
As further corollaries we have
(5.8) If $\theta$ is feasible in $G$, the following are equivalent:
(i) there is a helix $f$ in $G$ with $\phi(f) = \theta$
(ii) $\theta + 1/k$ is not feasible
(iii) no $\theta' > \theta$ is feasible.
Proof. By (5.2), (i) $\Rightarrow$ (iii). Trivially (iii) $\Rightarrow$ (ii), and by (5.3), (ii) $\Rightarrow$ (i)."

The one-path reductions retain the chosen side and lifted contact vertex. See the corrections to
Reduction 1 and (5.5) and to Reduction 4 and (5.6) in `corrections/GM06.md`. -/
theorem theorem_5_6 :
  ∀ (k : ℕ) (G G' : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (L' : CylinderLinkage k G') (θ θ' : ℝ),
    IsCylinderSection5Drawing k G → IsCylinderSection5Drawing k G' →
    L.HasTheta θ → L'.HasTheta θ' →
    Section5ReductionStep k G L G' L' →
    (IsThetaFeasible k G' (θ' + 1 / (k : ℝ)) ↔ IsThetaFeasible k G (θ + 1 / (k : ℝ))) := by exact GraphMinor.GM06.theorem_5_6_proof

end

section

open Compute GraphMinor.Surface

/-- Graph Minors VI, (5.7), page 133:

"(5.7) *Algorithm to decide if $\theta(\mathscr{L}) + 1/k$ is feasible.*"

The input consists of the ordinary graph, the augmented rotations,
both cuff orders and the given linkage rows. The output bit decides
next-winding feasibility. A positive answer includes ordinary directed
path rows encoding a successor linkage in the original graph. The
concrete program runs in polynomial time with logarithmic words. -/
theorem algorithm_5_7 {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {θ : ℝ}
    {L : CylinderLinkage k G} (input : GM06SuccessorInputRep x G L)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    {s : State} (hinput : s.arrs 0 = gm06EncodeSuccessorInput x) :
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06Algorithm57Prog s sf t ∧
      t ≤ 85217050012103 * (gm06SuccessorInputSize x + 1) ^ 5 ∧
      GM06SuccessorOutputRep input θ (sf.regs 0) (sf.arrs 8) := by exact GraphMinor.GM06.algorithm_5_7_proof input hG hθ hinput

end

section

open GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- Graph Minors VI, (5.8), page 133, from (5.3):
"If $\theta$ is feasible in $G$, the following are equivalent:"
The three conditions are a tight helix, failure of the next winding number,
and failure of every larger winding number. -/
theorem theorem_5_8 :
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ : ℝ),
    IsCylinderSection5Drawing k G → IsThetaFeasible k G θ →
    (((∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f = θ) ↔
        ¬ IsThetaFeasible k G (θ + 1 / (k : ℝ))) ∧
     (¬ IsThetaFeasible k G (θ + 1 / (k : ℝ)) ↔
        ∀ θ' : ℝ, θ < θ' → ¬ IsThetaFeasible k G θ')) := by exact GraphMinor.GM06.theorem_5_8_proof

end

section

open GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- Graph Minors VI, (5.9), page 134, from (5.3) through (5.8):
"If $\theta_1 \le \theta_2 \le \theta_3$ and $\theta_1, \theta_3$ are feasible in $G$ and $k\theta_2$
is an integer, then $\theta_2$ is feasible in $G$."
The integer gap from the first winding number counts the applications of (5.8). -/
theorem theorem_5_9 :
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ₁ θ₂ θ₃ : ℝ),
    IsCylinderSection5Drawing k G →
    θ₁ ≤ θ₂ → θ₂ ≤ θ₃ →
    IsThetaFeasible k G θ₁ → IsThetaFeasible k G θ₃ →
    (∃ m : ℤ, (k : ℝ) * θ₂ = m) →
    IsThetaFeasible k G θ₂ := by exact GraphMinor.GM06.theorem_5_9_proof

end

section

open Set GraphMinor.Surface
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (5.10)** (page 134):
"$\theta$ is feasible in $G$ if and only if
(i) $k\theta$ is an integer;
(ii) there is some linkage in $G$; and
(iii) for every helix $f$, $\theta(f) - k^{-1}L(f) \le \theta \le \theta(f) + k^{-1}L(f)$.
Proof. Necessity is clear. For sufficiency, let $\theta_1$ be maximum and $\theta_2$ minimum such that $\theta_1, \theta_2$ are feasible. (This is possible by (ii).) Then there is a helix $f_1$ in $G$ with
$$
\theta(f_1) + k^{-1}L(f_1) = \theta_1
$$
by (5.3); and similarly (reversing the orientation of the plane) there is a helix $f_2$ with
$$
\theta(f_2) - k^{-1}L(f_2) = \theta_2.
$$
Hence by (iii), $\theta_2 \le \theta \le \theta_1$, and so by (i) and (5.9), $\theta$ is feasible in $G$.
For an algorithm, we have
(5.11) Algorithm to decide if $\theta$ is feasible in $G$.
We check that conditions (i) and (ii) of (5.10) hold; if not then $\theta$ is not feasible. Checking (ii) is simply a maximum-flow problem and so can be done efficiently. We assume that we find a linkage $\mathscr{L}$, and (by reversing the orientation of the plane if necessary) that $\theta(\mathscr{L}) \le \theta$. If $\theta(\mathscr{L}) = \theta$ we are finished. If not, we use (5.7) to test if $\theta(\mathscr{L}) + 1/k$ is feasible, and if so to find a linkage $\mathscr{L}'$ with $\theta(\mathscr{L}') = \theta(\mathscr{L}) + 1/k$. (If there is no such linkage then $\theta$ is not feasible.) If we find $\mathscr{L}'$, we replace $\mathscr{L}$ by $\mathscr{L}'$ and continue. At each replacement the magnitude of $\theta - \theta(\mathscr{L})$ is reduced by $1/k$, and so the algorithm terminates.
To estimate the running time, we need to bound the number of applications of (5.7). This is bounded by
$$
1 + \max |k(\theta_1 - \theta_2)|,
$$"

Graph Minors VI (5.10), page 134, in both directions: winding
integrality, existence of a linkage and all helix bounds characterize feasibility. -/
theorem theorem_5_10 :
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ : ℝ),
    IsCylinderSection5Drawing k G →
    (IsThetaFeasible k G θ ↔
      (∃ m : ℤ, (k : ℝ) * θ = m) ∧
      Nonempty (CylinderLinkage k G) ∧
      ∀ f : Curve ClosedCylinder, IsHelix k G f →
        windingNumber f - (k : ℝ)⁻¹ * (curveL G f : ℝ) ≤ θ ∧
          θ ≤ windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ)) := by exact GraphMinor.GM06.theorem_5_10_proof

end

section

open GraphMinor.Compute GraphMinor.Surface

/-- Graph Minors VI, (5.11), page 134:

"(5.11) *Algorithm to decide if $\theta$ is feasible in $G$.*"

The program checks (5.10)(i) and (ii), orients the computed linkage,
and applies the proved (5.7) command until the target is reached or
its next value is infeasible. The call bound is (5.12). The supplied
input contains the drawing and the rational target, with all integer
signs and digits counted in its length. The output is Boolean and
its exact feasibility meaning holds for every represented instance.
The constants and degree are independent of all input data.

The finite input also gives signed integer edge turns, because the ends, the rotations and the cuff
data do not determine the absolute winding. For one path, a radial edge and a spiral edge with the
same ends have the same such data but windings zero and one. -/
theorem algorithm_5_11 :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ (x : GM06Alg511BinaryInput) (G : Drawing ClosedCylinder)
        (_rep : GM06Alg511BinaryDrawingRep x G), IsCylinderSection5Drawing x.pathCount G →
      ∀ (s : State), s.arrs 0 = gm06Alg511BinarySearchWords x →
      ∃ t u, Exec (wordSize c (gm06Alg511BinarySearchWords x).length) gm06Algorithm511Prog s t u ∧
        u ≤ C * ((gm06Alg511BinarySearchWords x).length + 1) ^ 11 ∧
        t.regs 0 < 2 ∧
        (t.regs 0 = 1 ↔ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) ∧
        (t.regs 0 = 0 ↔ ¬ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) := by exact GraphMinor.GM06.algorithm_5_11_proof

end

section

open Set Function Complex Real Topology Metric Graph GraphMinor.Surface GraphMinor.GM11
open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VI, (5.12)** (page 135):
"If $\theta_1, \theta_2$ are both feasible in $G$ then* $$|\theta_1 - \theta_2| \le
\frac{1}{k^2} |V(G)|.$$" -/
theorem theorem_5_12 :
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ₁ θ₂ : ℝ),
    IsCylinderSection5Drawing k G →
    IsThetaFeasible k G θ₁ → IsThetaFeasible k G θ₂ →
    |θ₁ - θ₂| ≤ (1 / ((k : ℝ) ^ 2)) * (G.V.ncard : ℝ) := by exact GraphMinor.GM06.theorem_5_12_proof

end

/-! ## Section 6. CONCLUSION -/

end GraphMinor.GM06
