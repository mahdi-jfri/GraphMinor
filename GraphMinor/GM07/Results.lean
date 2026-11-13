module

public import GraphMinor.GM07.AlphaExists
public import GraphMinor.GM07.Bridge
public import GraphMinor.GM07.CuffCollarBuild
public import GraphMinor.GM07.CuffFinal
public import GraphMinor.GM07.CuffStep
public import GraphMinor.GM07.CuffWalk
public import GraphMinor.GM07.CutBounds
public import GraphMinor.GM07.CutEdges
public import GraphMinor.GM07.CutFeasible
public import GraphMinor.GM07.CylinderGrid
public import GraphMinor.GM07.Defs
public import GraphMinor.GM07.DiscPlace
public import GraphMinor.GM07.ForestFlat
public import GraphMinor.GM07.ForestParts
public import GraphMinor.GM07.ForestQuotient
public import GraphMinor.GM07.GoodEdge
public import GraphMinor.GM07.GrowForest
public import GraphMinor.GM07.Matched
public import GraphMinor.GM07.Open
public import GraphMinor.GM07.Section11
public import GraphMinor.GM07.Section11a
public import GraphMinor.GM07.Section11b
public import GraphMinor.GM07.Section11d
public import GraphMinor.GM07.Section11g
public import GraphMinor.GM07.Section2
public import GraphMinor.GM07.Section2Converse
public import GraphMinor.GM07.Section26
public import GraphMinor.GM07.Section2Base
public import GraphMinor.GM07.Section2Euler
public import GraphMinor.GM07.Section2MinVal
public import GraphMinor.GM07.Section3
public import GraphMinor.GM07.Section35
public import GraphMinor.GM07.Section41
public import GraphMinor.GM07.Section46Deficient
public import GraphMinor.GM07.Section46Universe
public import GraphMinor.GM07.Section5
public import GraphMinor.GM07.Section5a
public import GraphMinor.GM07.Section6
public import GraphMinor.GM07.Section7
public import GraphMinor.GM07.Section9CoreProved
public import GraphMinor.GM07.Section9Grid
public import GraphMinor.GM07.TreeStep
public import GraphMinor.GM11.ArcDrawings
public import GraphMinor.GM11.DrawingOps
public import GraphMinor.GM11.Nice73
public import GraphMinor.GM11.PolarChart
public import GraphMinor.GM12.Section3ModelComplexity
public import GraphMinor.GM12.Section4FiniteLineDrawing
public import GraphMinor.GM14.RigidMap
public import GraphMinor.Menger.SimpleGraph
public import GraphMinor.Surface.Cuffs
public import GraphMinor.Surface.CutOArc
public import GraphMinor.Surface.CutParallel
public import GraphMinor.Surface.DiscMerge
public import GraphMinor.Surface.DiscsInSurface
public import GraphMinor.Surface.ModelCriterion
public import GraphMinor.Surface.PasteDisc
public import GraphMinor.Surface.PushOff
public import GraphMinor.Surface.SurfacePull
import GraphMinor.GM07.CylinderCap
import GraphMinor.GM07.PushForest
import GraphMinor.GM07.Section4
import GraphMinor.GM07.Section43
import GraphMinor.GM07.Section44
import GraphMinor.GM07.Section46Final
import GraphMinor.GM07.Section5b
import GraphMinor.GM07.Section9

/-!
# Graph Minors VII. Disjoint paths on a surface

N. Robertson and P. D. Seymour, J. Combin. Theory Ser. B 45 (1988) 212–254.

This file lists every numbered result of the paper in order. The proofs are in the other
files of this folder and, for algorithms, in `GraphMinor/Compute/`. The errors of the paper, and how
the Lean statements and proofs correct them, are listed in `corrections/GM07.md`.
-/

public section

namespace GraphMinor.GM07

/-! ## Section 1. Introduction -/

/-! ## Section 2. Surfaces and Nets -/

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- **Graph Minors VII, (2.1)** (page 215): "Let $J$ be a graph in $\Sigma$. Then $J$ is a seam
graph for some net if and only if"

The printed converse is false. The empty graph in the sphere satisfies (i)–(iv) and is not a seam
graph, since a seam graph is defined only "provided that $\Pi \ne \emptyset$", so it has a vertex.
This is the counterexample below. Graphs whose point set is not connected also fail, for example two
disjoint edges in the sphere, since the point set of a seam graph is the image of a circle. The
corrected form `theorem_2_1` adds the hypothesis that `U(J)` is connected, which includes that it is
non-empty. See the correction to (2.1) in `corrections/GM07.md`. -/
theorem not_theorem_2_1 :
    ¬ ∀ (S : Type) [TopologicalSpace S] [T1Space S], IsSurface S → ConnectedSpace S →
      ∀ J : Drawing S,
        (bd S ⊆ J.U ∧ ∀ e ∈ J.E, e ⊆ bd S ∨ e ∩ bd S = ∅) →
        HasNoIsolatedVertices (deleteBd J) →
        J.R.ncard = 1 →
        (∀ r ∈ J.R, ∀ F : Set S, F ⊆ r → IsOArc F → IsNullHomotopicOArc F) →
        IsSeamGraph J := by exact GraphMinor.GM07.not_theorem_2_1_proof

/-- **Graph Minors VII, (2.1)** (page 215): "Let $J$ be a graph in $\Sigma$. Then $J$ is a seam
graph for some net if and only if (i) $bd(\Sigma) \subseteq U(J)$, and for every edge $e$ of $J$,
either $e \subseteq bd(\Sigma)$ or $e \cap bd(\Sigma) = \emptyset$, (ii) $J - bd(\Sigma)$ has no
isolated vertices, (iii) $J$ has a unique region, and (iv) every $O$-arc included in that region is
null-homotopic." Here `deleteBd J` is the paper's `J - bd(Σ)` (page 214).

The hypothesis that `U(J)` is connected is added; the print is false without it
(`not_theorem_2_1`). The forward direction holds as printed, without this hypothesis
(`GM07.theorem_2_1_forward`). The converse follows the paper's proof: cut `Σ` along
`U(J - bd(Σ))` and show that the result is a closed disc. The step "by (iv) every $O$-arc included
in $\Delta - bd(\Delta)$ is null-homotopic" needs the connectedness of `U(J)`. See the
correction to (2.1) in `corrections/GM07.md`. -/
theorem theorem_2_1 {S : Type u} [TopologicalSpace S] [T1Space S]
    (hS : IsSurface S) (J : Drawing S) (hJc : IsConnected J.U) :
    IsSeamGraph J ↔
      (bd S ⊆ J.U ∧ ∀ e ∈ J.E, e ⊆ bd S ∨ e ∩ bd S = ∅) ∧
      HasNoIsolatedVertices (deleteBd J) ∧
      J.R.ncard = 1 ∧
      (∀ r ∈ J.R, ∀ F : Set S, F ⊆ r → IsOArc F → IsNullHomotopicOArc F) := by
  exact GraphMinor.GM07.theorem_2_1_proof hS J hJc

end

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- Graph Minors VII, (2.2) (page 216):
"(2.2) *Let $\Sigma \cong \Sigma(a, b, c)$ and let $J$ be a seam graph in $\Sigma$ for some net.
Suppose that every vertex of $J$ has valency at least $3$. Then $|V(J)| \le 2(2a + b + c - 1)$, and
$|E(J)| \le 3(2a + b + c - 1)$.*" -/
theorem theorem_2_2 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) {a b c : ℕ}
    (he : Nonempty (S ≃ₜ SurfaceModel a b c)) (J : Drawing S)
    (hSeam : IsSeamGraph J) (hval : ∀ v ∈ J.V, 3 ≤ vertexValency J v) :
    J.V.ncard ≤ 2 * (2 * a + b + c - 1) ∧ J.E.ncard ≤ 3 * (2 * a + b + c - 1) := by exact GraphMinor.GM07.theorem_2_2_proof hS he J hSeam hval

end

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- **Graph Minors VII, (2.3)** (page 216):
"Let $\Sigma$ be a connected surface with $\Sigma \not\cong \Sigma(0, 0, 0)$, $\Sigma(0, 0, 1)$,"

Graph Minors VII, (2.3) (pages 216–217): -/
theorem theorem_2_3 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) [hConn : ConnectedSpace S]
    (h000 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 0))
    (h001 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 1))
    (h010 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 1 0))
    {G J : Drawing S} {N : Net S}
    (hG : G.IsProper) (hMin : N.IsMinimalFor G) (hSeam : N.IsSeamGraphFor J) :
    ∀ v ∈ J.V, 3 ≤ vertexValency J v := by exact GraphMinor.GM07.theorem_2_3_proof hS h000 h001 h010 hG hMin hSeam

end

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- Graph Minors VII, (2.4) (page 217):
"(2.4) *If $\Sigma \cong \Sigma(a, b, c)$ where $2a + b + c > 1$, and $J$ is the seam graph for
some minimal net for $\Sigma$ (with respect to some $G$), then $|V(J)| \le 2(2a + b + c - 1)$ and
$|E(J)| \le 3(2a + b + c - 1)$.*" -/
theorem theorem_2_4 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (habc : 2 * a + b + c > 1)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    {G J : Drawing S} {N : Net S}
    (hG : G.IsProper) (hMin : N.IsMinimalFor G) (hSeam : N.IsSeamGraphFor J) :
    J.V.ncard ≤ 2 * (2 * a + b + c - 1) ∧ J.E.ncard ≤ 3 * (2 * a + b + c - 1) := by exact GraphMinor.GM07.theorem_2_4_proof hS habc he hG hMin hSeam

end

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- Graph Minors VII, (2.5) (page 217):
"(2.5) *There is a path of $J'$ between $\phi(s)$ and $\phi(t)$ with no edges of type (iii) or
(iv).*" -/
theorem theorem_2_5 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) (N : Net S) (J J' : Drawing S)
    (hSeam : N.IsSeamGraphFor J) {s t : N.D} (hs : s ∈ bd N.D) (ht : t ∈ bd N.D) (hst : s ≠ t)
    {C₁ C₂ : Set N.D} (hcomp : componentsIn (bd N.D \ {s, t}) = {C₁, C₂}) (hC12 : C₁ ≠ C₂)
    (hJ'U : J'.U = J.U) (hJ'V : J'.V = J.V ∪ {N.φ s, N.φ t}) :
    ∃ P : Drawing S, P.IsSubdrawing J' ∧ P.IsPathBetween (N.φ s) (N.φ t) ∧
      ∀ e ∈ P.E, ¬ IsNetEdgeType3 N C₁ e ∧ ¬ IsNetEdgeType4 N C₂ e := by exact GraphMinor.GM07.theorem_2_5_proof hS N J J' hSeam hs ht hst hcomp hC12 hJ'U hJ'V

end

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- **Graph Minors VII, (2.6)** (page 218):
"Let $(\Delta, \Pi)$ be a minimal net with respect to a proper graph $G$ in $\Sigma$, where $\Sigma \cong \Sigma(a, b, c)$ and $2a + b + c > 1$. Let $J$ be the associated seam graph and let $\phi$ be the associated surjection. Let $F$ be a $\phi^{-1}(G)$-normal proper $I$-arc in $\Delta$ with ends $s, t$, and let $F^ = F - \{s, t\}$. Then there is a $G$-normal $O$-arc $A$ in $\Sigma$ with
$$
|A \cap V(G)| \le 2(2a + b + c)(|\phi(F^) \cap V(G)| + 1) + |bd(\Sigma) \cap V(G)|
$$
and with $\phi(F) \subseteq A \subseteq \phi(F) \cup U(J)$."

The proof sums the exact endpoint contact balance and uses the refined net, in which a pasted pair
that contains $\phi(s)$ or $\phi(t)$ is split at that point. See the correction to the proof of
(2.6) in `corrections/GM07.md`. -/
theorem theorem_2_6 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (habc : 2 * a + b + c > 1)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    {G J : Drawing S} {N : Net S}
    (hG : G.IsProper) (hMin : N.IsMinimalFor G) (hSeam : N.IsSeamGraphFor J)
    {G_D : Drawing N.D} (hPull : IsPullbackDrawing N.φ G G_D)
    {F : Set N.D} {s t : N.D}
    (hNorm : G_D.IsNormal F) (hProperF : IsProperIArc F) (hEnds : IsLineWithEnds F s t) :
    ∃ A : Set S, G.IsNormal A ∧ IsOArc A ∧
      (A ∩ G.V).ncard ≤
        2 * (2 * a + b + c) * ((N.φ '' (F \ {s, t}) ∩ G.V).ncard + 1) +
          (bd S ∩ G.V).ncard ∧
      N.φ '' F ⊆ A ∧ A ⊆ N.φ '' F ∪ J.U := by exact GraphMinor.GM07.theorem_2_6_proof hS habc he hG hMin hSeam hPull hNorm hProperF hEnds

end

/-! ## Section 3. Matchings and Forests -/

section

open Set Function Topology Classical GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- Graph Minors VII, (3.1) (page 218):
"(3.1) *For any fixed $\Sigma$ there are only finitely many similarity classes.*" -/
theorem theorem_3_1 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) :
    ∃ 𝓕 : Set (Set S), 𝓕.Finite ∧ ∀ F : Set S, IsProperIArc F →
      ∃ F₀ ∈ 𝓕, AreSimilarIArcs F₀ F := by exact GraphMinor.GM07.theorem_3_1_proof hS

end

section

open Set Function Topology Classical GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- Graph Minors VII, (3.2) (page 219):
"(3.2) *For any fixed $\Sigma$ and $s, t \in bd(\Sigma)$, there are only finitely many parallel
classes of $I$-arcs with ends $s, t$.*"

The signature also records the permutation of the two ends. See the correction to the proof of (3.2)
in `corrections/GM07.md`. -/
theorem theorem_3_2 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (s t : S) :
    ∃ 𝓖 : Set (Set S), 𝓖.Finite ∧
      (∀ F₀ ∈ 𝓖, F₀ ∩ bd S = {s, t} ∧ IsLineWithEnds F₀ s t) ∧
      ∀ F : Set S, F ∩ bd S = {s, t} → IsLineWithEnds F s t →
        ∃ F₀ ∈ 𝓖, AreParallelIArcs F₀ F := by exact GraphMinor.GM07.theorem_3_2_proof hS s t

end

section

open Set Function Topology Classical GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- Graph Minors VII, (3.3) (page 219):
"(3.3) *For any surface $\Sigma$ and finite $X \subseteq bd(\Sigma)$, there are only finitely many
congruence classes of $X$-matchings.*" -/
theorem theorem_3_3 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {X : Set S} (hX : X ⊆ bd S) (hXfin : X.Finite) :
    ∃ 𝓜 : Set (Drawing S), 𝓜.Finite ∧
      (∀ G₀ ∈ 𝓜, IsXMatching X G₀) ∧
      ∀ G : Drawing S, IsXMatching X G → ∃ G₀ ∈ 𝓜, AreCongruentMatchings G₀ G := by exact GraphMinor.GM07.theorem_3_3_proof hS hX hXfin

end

section

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

universe u

/-- Graph Minors VII, (3.4) (page 220):
"(3.4) *For any surface $\Sigma$ and finite $Y \subseteq bd(\Sigma)$, there are only finitely many
homoplasty classes of $Y$-forests.*"

The surrounding relation distinguishes forest components in a region. See the correction to the
proof of (3.4) in `corrections/GM07.md`. -/
theorem theorem_3_4 {S' : Type u} [TopologicalSpace S']
    (hS : IsSurface S') {Y : Set S'} (hY : Y ⊆ bd S') (hYfin : Y.Finite) :
    ∃ 𝓗 : Set (Drawing S'), 𝓗.Finite ∧
      (∀ H₀ ∈ 𝓗, IsYForest Y H₀) ∧
      ∀ H : Drawing S', IsYForest Y H → ∃ H₀ ∈ 𝓗, ForestsHomoplastic H₀ H := by exact GraphMinor.GM07.theorem_3_4_proof hS hY hYfin

end

section

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

universe u

/-- Graph Minors VII, (3.5) (page 221):
"(3.5) *For every matching $G$ in $\Sigma$ and every homoplasty class $\mathscr{B}$ there exists
$H \in \mathscr{B}$ with $U(G) \cap U(H)$ finite.*" -/
theorem theorem_3_5 {S' : Type u} [TopologicalSpace S']
    (hS : IsSurface S') (G H₀ : Drawing S') (hG : IsMatching G) (hH₀ : IsSurfaceForest H₀) :
    ∃ H : Drawing S', IsSurfaceForest H ∧ ForestsHomoplastic H₀ H ∧ (G.U ∩ H.U).Finite := by exact GraphMinor.GM07.theorem_3_5_proof hS G H₀ hG hH₀

end

section

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

universe u

/-- Graph Minors VII, (3.6) (page 221):
"(3.6) *For every surface $\Sigma$ and all integers $k, n \ge 0$ there is an integer
$w(\Sigma, k, n)$ such that for every matching $G$ in $\Sigma$ with $|V(G)| \le 2n$ and every
forest $H$ in $\Sigma$ with $|V(H) \cap bd(\Sigma)| \le k$, there is a forest $H'$ homoplastic to
$H$ with $|U(G) \cap U(H')| \le w(\Sigma, k, n)$.*" -/
theorem theorem_3_6 {S' : Type u} [TopologicalSpace S']
    (hS : IsSurface S') (k n : ℕ) :
    IsW36Bound S' k n (wSurface S' k n) := by exact GraphMinor.GM07.theorem_3_6_proof hS k n

end

/-! ## Section 4. The Main Result, First Version -/

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- Graph Minors VII, (4.1) (page 221; Theorem (3.6) of Graph Minors VI, `GM06.Statement36`):
"(4.1) *Let $G$ be a proper graph in a closed disc $\Delta$ and let $H$ be a forest in $\Delta$
with $V(H) \cap bd(\Delta) = V(G) \cap bd(\Delta)$. Then $H$ is $G$-feasible if and only if for
every $G$-normal proper $I$-arc $F$ with ends $s, t$ say, $|V(G) \cap (F - \{s, t\})| \ge |\Lambda|$
where $C_1, C_2$ are the two components of $bd(\Delta) - \{s, t\}$, and $\Lambda$ is the set of
vertex sets of the components of $H$ which intersect both $C_1$ and $C_2$, and contain neither $s$
nor $t$.*" -/
theorem theorem_4_1 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) (hDisc : IsClosedDisc (univ : Set S))
    (G H : Drawing S) (hG : G.IsProper) (hH : IsSurfaceForest H)
    (hbd : H.V ∩ bd S = G.V ∩ bd S) :
    IsGFeasible G H ↔
      ∀ (F : Set S) (s t : S) (C₁ C₂ : Set S),
        G.IsNormal F → IsProperIArc F → IsLineWithEnds F s t →
        componentsIn (bd S \ {s, t}) = {C₁, C₂} → C₁ ≠ C₂ →
        {V₀ : Set S | ∃ H' : Drawing S,
          GM06.IsGraphComponent H'.toGraph H.toGraph ∧ V₀ = H'.V ∧
          (V₀ ∩ C₁).Nonempty ∧ (V₀ ∩ C₂).Nonempty ∧ s ∉ V₀ ∧ t ∉ V₀}.ncard ≤
          (G.V ∩ (F \ {s, t})).ncard := by exact GraphMinor.GM07.theorem_4_1_proof hS hDisc G H hG hH hbd

end

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- Graph Minors VII, (4.2) (page 222):
"(4.2) *Let $\Sigma$ be a connected surface with $bd(\Sigma) = \emptyset$, and let
$Y \subseteq \Sigma$ be connected and open. Suppose that every $O$-arc included in $Y$ bounds a
disc included in $Y$. Then either $\Sigma$ is a sphere and $Y = \Sigma$, or $Y$ is an open disc.*"
Proved unconditionally from `Surface.open_disc` and `isClosedSurface_of_bd_eq_empty`. -/
theorem theorem_4_2 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [hConn : ConnectedSpace S] (hbd : bd S = ∅)
    (Y : Set S) (hY_conn : IsConnected Y) (hY_open : IsOpen Y)
    (hY_oarc : ∀ F : Set S, IsOArc F → F ⊆ Y →
      ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ⊆ Y) :
    (IsSphere S ∧ Y = univ) ∨ IsOpenDisc Y := by exact GraphMinor.GM07.theorem_4_2_proof hS hbd Y hY_conn hY_open hY_oarc

end

section

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Graph Minors VII, (4.3) (pages 222–223):
"(4.3) *Let $\Sigma$ be a connected surface with at least two cuffs, and let $G$ be a proper graph
in $\Sigma$. Let $v \ge 0$ be an integer, and suppose that every $G$-normal $O$-arc $F$ with
$F \cap bd(\Sigma) = \emptyset$ and $|V(G) \cap F| \le v$ is null-homotopic. Let $C$ be a cuff.
Then there are at least $v + 1$ paths of $G$, each with one end in $C$ and the other in
$bd(\Sigma) - C$, mutually vertex-disjoint except for their ends.*"

Read with distinct paths the printed statement fails when one edge joins $C$ to $bd(\Sigma) - C$. So
the conclusion here is a family of paths whose internal vertices are disjoint, in which a path with
no internal vertex may repeat. See the correction to (4.3) in `corrections/GM07.md`. -/
theorem theorem_4_3 {S : Type} [TopologicalSpace S] [T1Space S] (hS : IsSurface S) [hConn : ConnectedSpace S]
    (hcuffs : 2 ≤ (cuffs S).ncard) (G : Drawing S) (v : ℕ) (hG : G.IsProper)
    (hNull : ∀ F : Set S, G.IsNormal F → IsOArc F → F ∩ bd S = ∅ → (G.V ∩ F).ncard ≤ v →
      IsNullHomotopicOArc F)
    {C : Set S} (hC : C ∈ cuffs S) :
    ∃ (P : Fin (v + 1) → Drawing S) (s t : Fin (v + 1) → S),
      (∀ i : Fin (v + 1), (P i).IsSubdrawing G ∧ s i ∈ C ∧ t i ∈ bd S \ C ∧
        (P i).IsPathBetween (s i) (t i)) ∧
      (∀ i j : Fin (v + 1), i ≠ j →
        Disjoint ((P i).V \ {s i, t i}) ((P j).V \ {s j, t j})) := by exact GraphMinor.GM07.theorem_4_3_proof hS hcuffs G v hG hNull hC

end

section

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- **Graph Minors VII, (4.4)** (page 223):
"Let $L$ be a proper graph in $\Sigma$ with no isolated vertices, such that no $F \subseteq U(L)$ is an $O$-arc or an $I$-arc. Let $\Sigma'$ be the surface obtained from $\Sigma$ by cutting along $U(L)$, and let $\phi \colon \Sigma' \to \Sigma$ be the associated surjection. Let $H_0$ be a forest in $\Sigma$, and for each $z \in V(H_0) \cap bd(\Sigma)$, let $l(z) \in \phi^{-1}(z)$. Then there is a forest $H$ in $\Sigma$, homotopic to $H_0$, such that $U(H) \cap U(L) \subseteq bd(\Sigma)$, and for each $z \in V(H_0) \cap bd(\Sigma)$ every member of $\phi^{-1}(z) - \{l(z)\}$ is an isolated vertex of $\phi^{-1}(H)$."

**(4.4) of Graph Minors VII** (page 223). Let `L` be a proper graph with no isolated vertices in `Σ`, such that no subset of `U(L)` is an `O`-arc or an `I`-arc, and let `φ` be the map of the cut along `U(L)`. Let `H₀` be a forest in `Σ`, and for each vertex `z` of `H₀` on `bd(Σ)` let `l z` be a point of `φ⁻¹(z)`. Then there is a forest `H` homotopic to `H₀` with `U(H) ∩ U(L) ⊆ bd(Σ)`, such that every point of `φ⁻¹(z)` other than `l z` is an isolated vertex of `φ⁻¹(H)`. -/
theorem theorem_4_4 {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
    (hS : IsSurface S) (L : Drawing S) (φ : S' → S) (hJ : IsCutAlongGraph L S' φ) (hNoArc : ∀ F : Set S, F ⊆ L.U → ¬ IsOArc F ∧ ¬ IsIArc F) (H₀ : Drawing S) (l : S → S') (hH₀ : IsSurfaceForest H₀) (hl : ∀ z ∈ H₀.V ∩ bd S, φ (l z) = z) :
    ∃ (H : Drawing S) (H' : Drawing S'), IsSurfaceForest H ∧ ForestsHomotopic H H₀ ∧ H.U ∩ L.U ⊆ bd S ∧ IsPullbackDrawing φ H H' ∧ ∀ z ∈ H₀.V ∩ bd S, ∀ z' ∈ φ ⁻¹' {z} \ {l z}, IsIsolatedVertex H' z' := by exact GraphMinor.GM07.theorem_4_4_proof hS L φ hJ hNoArc H₀ l hH₀ hl

end

section

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Graph Minors VII, (4.5) (page 223):
"(4.5) *Let $J$ be a proper graph in $\Sigma$ with no isolated vertices. Let $\Sigma'$ be the
surface obtained from $\Sigma$ by cutting along $U(J)$ and let $\phi \colon \Sigma' \to \Sigma$ be
the associated surjection. Let $H$ be a forest in $\Sigma$ such that $U(J)$ is $H$-normal. Then
$\phi^{-1}(H)$ is a forest in $\Sigma'$. Moreover, if $H'$ is a forest in $\Sigma'$ homoplastic to
$\phi^{-1}(H)$, then $\phi(H')$ is a forest in $\Sigma$ homoplastic to $H$.*" -/
theorem theorem_4_5 {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
    (hS : IsSurface S) (J H : Drawing S) (φ : S' → S) (hCut : IsCutAlongGraph J S' φ) (hH : IsSurfaceForest H) (hNorm : H.IsNormal J.U) :
    ∃ H_pull : Drawing S',
      IsPullbackDrawing φ H H_pull ∧ IsSurfaceForest H_pull ∧
      ∀ H' : Drawing S', IsSurfaceForest H' → ForestsHomoplastic H' H_pull →
        ∃ H_push : Drawing S,
          IsImageDrawing φ H' H_push ∧ IsSurfaceForest H_push ∧
          ForestsHomoplastic H_push H := by exact GraphMinor.GM07.theorem_4_5_proof hS J H φ hCut hH hNorm

end

section

open Set Topology GraphMinor.Surface

universe u

/-- Graph Minors VII, (4.6) (pages 224–230):
"(4.6) *Let $\Sigma$ be a connected surface with at least two cuffs and let $k \ge 0$ be an
integer. Let $G$ be a proper graph in $\Sigma$, with $|V(G) \cap bd(\Sigma)| \le 2k$, such that*
*(i) for every $G$-normal $I$-arc $B$ with $|V(G) \cap B| \le v(\Sigma, k)$ the ends of $B$ are in
the same cuff of $\Sigma$,*
*(ii) for every $G$-normal $O$-arc $B$ with $|V(G) \cap B| \le v(\Sigma, k)$ either $B$ is
null-homotopic, or for some cuff $C$, $B$ is null-homotopic in $\Sigma + \hat{C}$ and
$V(G) \cap C \subseteq B$, and*
*(iii) for every cuff $C$, $|V(G) \cap C| \ge 2$.*
*Let $H$ be a forest in $\Sigma$ with $V(G) \cap bd(\Sigma) = V(H) \cap bd(\Sigma)$. Then $H$ is
$G$-feasible.*"

The proof uses the corrected reference and weak endpoint indices (see the corrections to the proof
of (4.6) in `corrections/GM07.md`). It takes $v(\Sigma, k)$ to be the least value over the triples
$(a, b, c)$ with $\Sigma \cong \Sigma(a, b, c)$. The paper does not say which triple to use when
there are several. With the least value the hypotheses are weakest, so the result holds for every
choice of the triple. -/
theorem theorem_4_6 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) [hConn : ConnectedSpace S]
    (hcuffs : 2 ≤ (cuffs S).ncard) (k : ℕ) (G H : Drawing S)
    (hG : G.IsProper) (hbd_card : (G.V ∩ bd S).ncard ≤ 2 * k)
    (hi : ∀ B : Set S, G.IsNormal B → IsIArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      ∃ C ∈ cuffs S, lineEnds B ⊆ C)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    (hH : IsSurfaceForest H) (hbd_eq : G.V ∩ bd S = H.V ∩ bd S) :
    IsGFeasible G H := by exact GraphMinor.GM07.theorem_4_6_proof hS hcuffs k G H hG hbd_card hi hii hiii hH hbd_eq

end

/-! ## Section 5. The Main Result, Second Version -/

section

open Set Function Topology Metric unitInterval OnePoint Classical
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

/-- Graph Minors VII, (5.1) (page 230):
"If $\Sigma$ is connected and $X \subseteq \Sigma$ is solid and $X \ne \Sigma$, then $X$ is planar if and only if every $O$-arc included in $X$ is null-homotopic." -/
theorem theorem_5_1 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S] {X : Set S}
    (hX_solid : IsSolid X) (hX_ne : X ≠ univ) :
    IsPlanar X ↔ ∀ F : Set S, IsOArc F → F ⊆ X → IsNullHomotopicOArc F := by exact GraphMinor.GM07.theorem_5_1_proof hS hX_solid hX_ne

end

section

open Set Function Topology unitInterval GraphMinor.Surface GraphMinor.GM11

universe u

/-- Graph Minors VII, (5.2) (page 230):
"If $X \subseteq \Sigma$ is solid and $X$ is planar in $\Sigma + \hat{C}$, where $C$ is a cuff,
then $X$ surrounds $C$ in $\Sigma$ if and only if some $O$-arc included in $X$ surrounds $C$." -/
theorem theorem_5_2 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {X C : Set S}
    (hX_solid : IsSolid X) (hXC : IsPlanarInCappedCuff C X) :
    SurroundsCuff X C ↔ ∃ F : Set S, IsOArc F ∧ F ⊆ X ∧ SurroundsCuff F C := by exact GraphMinor.GM07.theorem_5_2_proof hS hX_solid hXC

end

section

open Set Function Topology unitInterval GraphMinor.Surface GraphMinor.GM11

universe u

/-- Graph Minors VII, (5.3) (page 231):
"If $\Sigma \not\cong \Sigma(0, 0, 2)$ and $G$ is a proper graph in $\Sigma$, and $C$, $C'$
are distinct cuffs and $r$, $r' \ge 0$ are integers with $r + r' < \alpha(G)$ then
$\mathscr{A}_r(C) \cap \mathscr{A}_{r'}(C') = \emptyset$." -/
theorem theorem_5_3 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S]
    (hnot_cyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    (G : Drawing S) {C C' : Set S} (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) (hne : C ≠ C')
    {r r' : ℕ} (hr : r + r' < alpha G) :
    scriptA G r C ∩ scriptA G r' C' = ∅ := by exact GraphMinor.GM07.theorem_5_3_proof hS hnot_cyl G hC hC' hne hr

end

section

open Set Function Topology unitInterval GraphMinor.Surface GraphMinor.GM11

universe u

/-- Graph Minors VII, (5.4) (page 231):
"Let $F$, $F_0$ be $O$-arcs in $\Sigma$, where $F_0$ is null-homotopic. Let $r > 0$, and let
$v_1, \dots, v_r \in F$ be distinct, and in order on $F$. Let the components of $F - \{v_1,
\dots, v_r\}$ be $A_1, \dots, A_r$, where $\{v_{i-1}, v_i\} \subseteq \bar{A}_i$ ($1 \le i
\le r$). (Throughout, subscripts should be read modulo $r$.) Let $P_1, \dots, P_r$ be $[0,
1]$-arcs, such that for $1 \le i \le r$, $v_i$ is one end of $P_i$ and the other end ($u_i$
say) is in $F_0$. For $1 \le i \le r$, let $B_i = \emptyset$ if $u_{i-1} = u_i$, and be a
component of $F_0 - \{u_{i-1}, u_i\}$ if $u_{i-1} \ne u_i$. Suppose that $P_{i-1} \cup P_i
\cup A_i \cup B_i$ is planar ($1 \le i \le r$). Then $F$ is null-homotopic."

Here the cyclic order of $v_0, \dots, v_{r-1}$ on $F$ and the open arcs $A_0, \dots, A_{r-1}$ are
given by a homeomorphism $\phi \colon S^1 \cong F$ and a monotone partition
$0 = s_0 \le s_1 \le \dots \le s_r = 1$ of $[0, 1]$ under `arcParam 1` such that for each
$i < r$, $v_i = \phi(\text{arcParam } 1\ (s_{i+1}))$ and
$\phi(\text{arcParam } 1 '' (s_i, s_{i+1})) \subseteq A_i \subseteq F$. -/
theorem theorem_5_4 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {F F₀ : Set S}
    (_hF : IsOArc F) (hF₀ : IsOArc F₀) (hF₀_null : IsNullHomotopicOArc F₀)
    {r : ℕ} (hr : 0 < r)
    (φ : Circle ≃ₜ F) (s : ℕ → I) (hs0 : s 0 = 0) (hsr : s r = 1)
    (hs_mono : ∀ i < r, s i ≤ s (i + 1))
    (v u : ℕ → S) (A P B : ℕ → Set S)
    (hv : ∀ i ≤ r, v i = (φ (arcParam 1 (s i))).1)
    (hA : ∀ i < r, (fun t => (φ (arcParam 1 t)).1) '' Ioo (s i) (s (i + 1)) ⊆ A i ∧ A i ⊆ F)
    (hP : ∀ i ≤ r, IsLineWithEnds (P i) (v i) (u i) ∧ u i ∈ F₀)
    (hP_wrap : P 0 = P r ∧ u 0 = u r)
    (hB : ∀ i < r, (u i = u (i + 1) ∧ B i = ∅) ∨
      (u i ≠ u (i + 1) ∧ B i ∈ componentsIn (F₀ \ {u i, u (i + 1)})))
    (hPlanar : ∀ i < r, IsPlanar (P i ∪ P (i + 1) ∪ A i ∪ B i)) :
    IsNullHomotopicOArc F := by exact GraphMinor.GM07.theorem_5_4_proof hS _hF hF₀ hF₀_null hr φ s hs0 hsr hs_mono v u A P B hv hA hP hP_wrap hB hPlanar

end

section

open Set Function Topology Filter unitInterval
open GraphMinor.Surface GraphMinor.GM11

universe u

/-- **(5.5)** of Graph Minors VII (Section 5, page 231):
"Let $G$ be a proper graph in a connected surface $\Sigma$, and let $Z$ be the closure of the
union of some of the regions of $G$, with $Z \ne \Sigma$. Then $Z$ is planar if and only if
every $G$-normal $O$-arc included in $Z$ is null-homotopic." -/
theorem theorem_5_5 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {ℛ : Set (Set S)} (hℛ : ℛ ⊆ G.R)
    {Z : Set S} (hZ : Z = closure (⋃₀ ℛ)) (hZ_ne : Z ≠ univ) :
    IsPlanar Z ↔ ∀ F : Set S, F ⊆ Z → G.IsNormal F → IsOArc F → IsNullHomotopicOArc F := by exact GraphMinor.GM07.theorem_5_5_proof hS hG hℛ hZ hZ_ne

end

section

open Set Function Topology Filter unitInterval
open GraphMinor.Surface GraphMinor.GM11

universe u

/-- Graph Minors VII, (5.6) (page 232):
"Let $\Sigma$ be a connected surface such that $\Sigma \not\cong \Sigma(0, 0, c)(c = 0, 1,
2)$, and let $G$ be a proper graph in $\Sigma$. Let $C$ be a cuff of $\Sigma$, and let $F_0$
be a $G$-normal $O$-arc surrounding $C$. Let $t$ be an integer with* $$ |V(G) \cap F_0| \le
t \le \frac{2}{9}\alpha(G) - 1. $$ *Then $Y_t(F_0)$ is planar in $\Sigma + \hat{C}$." -/
theorem theorem_5_6 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S]
    (hnot_small : ∀ c ≤ 2, IsEmpty (S ≃ₜ SurfaceModel 0 0 c))
    {G : Drawing S} (hG : G.IsProper)
    {C F₀ : Set S} (hC : C ∈ cuffs S)
    (hF₀_oarc : IsOArc F₀) (hF₀_norm : G.IsNormal F₀) (hF₀_surr : SurroundsCuff F₀ C)
    {t : ℕ} (ht_low : (G.V ∩ F₀).ncard ≤ t) (ht_high : 9 * (t + 1) ≤ 2 * alpha G) :
    IsPlanarInCappedCuff C (nearSet G t F₀) := by exact GraphMinor.GM07.theorem_5_6_proof hS hnot_small hG hC hF₀_oarc hF₀_norm hF₀_surr ht_low ht_high

end

section

open Set Function Topology Filter unitInterval
open GraphMinor.Surface GraphMinor.GM11

universe u

/-- Graph Minors VII, (5.7) (page 232):
"Let $\Sigma \cong \Sigma(a, b, c)$, where $3a + 3b + c \ge 3$, and let $G$ be a proper graph in
$\Sigma$. Let $C$ be a cuff, and let $r \ge 0$ be an integer with $r \le \frac{2}{9}\alpha(G) - 1$.
Then $\mathscr{A}_r(C)$ is planar in $\Sigma + \hat{C}$." -/
theorem theorem_5_7 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S]
    {a b c : ℕ} (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    (habc : 3 ≤ 3 * a + 3 * b + c)
    {G : Drawing S} (hG : G.IsProper)
    {C : Set S} (hC : C ∈ cuffs S)
    {r : ℕ} (hr : 9 * (r + 1) ≤ 2 * alpha G) :
    IsPlanarInCappedCuff C (scriptA G r C) := by exact GraphMinor.GM07.theorem_5_7_proof hS hmodel habc hG hC hr

end

section

open Set Topology Function Graph GraphMinor.Surface GraphMinor.GM11

universe u

/-- Graph Minors VII, (5.8) (page 233; essentially Theorem (4.1) of Graph Minors III):
"(5.8) *Let $\Sigma$ be a cylinder and let $C_1, C_2$ be the two cuffs. Let $G$ be a proper graph in
$\Sigma$. Let $r, s \ge 0$ be integers. Suppose that*
*(i) every $G$-normal $O$-arc $F$ with $|F \cap V(G)| < r$ is null-homotopic, and*
*(ii) every $G$-normal $I$-arc $F$ with $|F \cap V(G)| < s$ has both its ends in the same cuff.*
*Then there are mutually vertex-disjoint paths $P_1, \dots, P_r$ of $G$, each between $C_1$ and
$C_2$, and mutually vertex-disjoint circuits $B_1, \dots, B_s$ of $G$, none null-homotopic, such
that for $1 \le i \le r$ and $1 \le j \le s$ the intersection of $P_i$ and $B_j$ is a path.*"

The paper omits the proof and refers to (4.1) of Graph Minors III, which needs disjoint inner and
outer bounding circuits. Here the circuits may touch the cuffs, so the proof caps each cuff with a
disc containing a wheel before using planar nest uncrossing. -/
theorem theorem_5_8 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) (he : Nonempty (S ≃ₜ SurfaceModel 0 0 2)) {C₁ C₂ : Set S} (hcuffs : cuffs S = {C₁, C₂}) (hne : C₁ ≠ C₂) (G : Drawing S) (r s : ℕ) (hG : G.IsProper)
    (hi : ∀ F : Set S, G.IsNormal F → IsOArc F → (F ∩ G.V).ncard < r → IsNullHomotopicOArc F)
    (hii : ∀ F : Set S, G.IsNormal F → IsIArc F → (F ∩ G.V).ncard < s → lineEnds F ⊆ C₁ ∨ lineEnds F ⊆ C₂) :
    ∃ (P : Fin r → Drawing S) (u v : Fin r → S) (B : Fin s → Drawing S),
      (∀ i : Fin r, (P i).IsSubdrawing G ∧ u i ∈ C₁ ∧ v i ∈ C₂ ∧ (P i).IsPathBetween (u i) (v i)) ∧
      (∀ i i' : Fin r, i ≠ i' → Disjoint (P i).V (P i').V) ∧
      (∀ j : Fin s, (B j).IsSubdrawing G ∧ IsOArc (B j).U ∧ ¬ IsNullHomotopicOArc (B j).U) ∧
      (∀ j j' : Fin s, j ≠ j' → Disjoint (B j).V (B j').V) ∧
      (∀ (i : Fin r) (j : Fin s), ∃ Q : Drawing S, ∃ x y : S, Q.U = (P i).U ∩ (B j).U ∧ Q.V = (P i).V ∩ (B j).V ∧ Q.IsPathBetween x y) := by exact GraphMinor.GM07.theorem_5_8_proof hS he hcuffs hne G r s hG hi hii

end

section

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

/-- Graph Minors VII, (5.9) (pages 233–237):
"(5.9) *Let $\Sigma \cong \Sigma(a, b, c)$, where $c \ge 2$ and $(a, b, c) \ne (0, 0, 2)$. Let
$k \ge 0$ be an integer. Let $G$ be a boundary-linked proper graph in $\Sigma$ with
$|V(G) \cap \mathrm{bd}(\Sigma)| \le 2k$ and with $\alpha(G) > 9k v(\Sigma, k)$, such that for
every cuff $C$, $|V(G) \cap C| \ge 2$. Let $H$ be a forest in $\Sigma$ with
$V(G) \cap \mathrm{bd}(\Sigma) = V(H) \cap \mathrm{bd}(\Sigma)$. Then $H$ is $G$-feasible.*"

See `IsCuffCore` for the parts of the proof at one cuff, `IsCuffCollar` for what they give, and `isGFeasible_of_collars` for the final step.

The proof treats all cuffs at once. The cut surface $\Sigma'$ is the part of $\Sigma$ above the
collars, carried onto $\Sigma$ by a collapse map homotopic to the identity. This avoids building
$\Sigma'$ as a new space with a homeomorphism onto it, which the paper itself treats loosely. -/
theorem theorem_5_9 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (hc : 2 ≤ c) (hne : (a, b, c) ≠ (0, 0, 2))
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (k : ℕ) (G H : Drawing S)
    (hBL : IsBoundaryLinked G) (hbd_card : (G.V ∩ bd S).ncard ≤ 2 * k)
    (halpha : 9 * k * vSurface S k < alpha G)
    (hcuff2 : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    (hH : IsSurfaceForest H) (hbd_eq : G.V ∩ bd S = H.V ∩ bd S) :
    IsGFeasible G H := by exact GraphMinor.GM07.theorem_5_9_proof hS hc hne he k G H hBL hbd_card halpha hcuff2 hH hbd_eq

end

/-! ## Section 6. Allowing Smaller Cuffs -/

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- Graph Minors VII, (6.1) (pages 237–238):
"(6.1) *Let $\Sigma \cong \Sigma(a, b, c)$, where $c \ge 2$ and $(a, b, c) \ne (0, 0, 2)$. Let
$k \ge 0$ be an integer. Let $G$ be a boundary-linked proper graph in $\Sigma$ with
$|V(G) \cap bd(\Sigma)| \le 2k - 2c$ and with $\alpha(G) > 9kv(\Sigma, k)$. Let $H$ be a forest in
$\Sigma$ with $V(G) \cap bd(\Sigma) = V(H) \cap bd(\Sigma)$. Then $H$ is $G$-feasible.*" -/
theorem theorem_6_1 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (hc : 2 ≤ c) (hne : (a, b, c) ≠ (0, 0, 2))
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (k : ℕ) (G H : Drawing S)
    (hBL : IsBoundaryLinked G)
    (hbd_card : (G.V ∩ bd S).ncard ≤ 2 * k - 2 * c)
    (halpha : 9 * k * vSurface S k < alpha G)
    (hH : IsSurfaceForest H) (hbd_eq : G.V ∩ bd S = H.V ∩ bd S) :
    IsGFeasible G H := by exact GraphMinor.GM07.theorem_6_1_proof hS hc hne he k G H hBL hbd_card halpha hH hbd_eq

end

/-! ## Section 7. Adding New Cuffs -/

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- Graph Minors VII, (7.1) (pages 238–239):
"(7.1) *Suppose that $\Sigma$, $G$ are as above, and $2 \le r \le \frac{2}{9}\alpha(G)$, and that
$e$ is an edge of $G$, not a loop, with $e \notin \Delta_{r-1}$ and with
$\bar{e} \cap bd(\Sigma) = \emptyset$. Then $\alpha(\phi_e^{-1}(G \setminus e)) \ge r$.*"

The cuff-inside set is the filled union of generating sets and inner holes, since the $O$-arc
$A_r(C)$ of the paper does not exist as printed. See the correction on page 238 in
`corrections/GM07.md`. -/
theorem theorem_7_1 {S : Type u} [TopologicalSpace S]
    {S_e : Type u} [TopologicalSpace S_e] [T1Space S] [T1Space S_e]
    (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he_model : Nonempty (S ≃ₜ SurfaceModel a b c))
    (G : Drawing S) (r : ℕ) (e : Set S) (φ_e : S_e → S) (G_e : Drawing S_e)
    (hG : G.IsProper) (hr : 2 ≤ r) (halpha : 9 * r ≤ 2 * alpha G)
    (hnot_in : ¬ (e ⊆ allCuffsInsideSet G (r - 1)))
    (hCut : IsCutAlongEdge G e a b c S_e φ_e G_e) :
    r ≤ alpha G_e := by exact GraphMinor.GM07.theorem_7_1_proof hS h3 he_model G r e φ_e G_e hG hr halpha hnot_in hCut

end

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- Graph Minors VII, (7.2) (page 239):
"(7.2) *Let $\Sigma \cong \Sigma(a, b, c)$, where $3a + 3b + c \ge 3$, and let $G$ be a
boundary-linked proper graph in $\Sigma$. Let $e$ be an edge of $G$ which is not a loop, such that
$\bar{e} \cap bd(\Sigma) = \emptyset$, and there is no null-homotopic $G$-normal $O$-arc $A$ with
$|V(G) \cap A| \le 1$ and with $e$ inside $A$. Then $\phi_e^{-1}(G \setminus e)$ is boundary-linked
in $\Sigma_e$.*" -/
theorem theorem_7_2 {S : Type u} [TopologicalSpace S]
    {S_e : Type u} [TopologicalSpace S_e] [T1Space S] [T1Space S_e]
    (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he_model : Nonempty (S ≃ₜ SurfaceModel a b c))
    (G : Drawing S) (e : Set S) (φ_e : S_e → S) (G_e : Drawing S_e)
    (hBL : IsBoundaryLinked G)
    (hNoNull : ¬ ∃ A : Set S, G.IsNormal A ∧ IsNullHomotopicOArc A ∧
      (G.V ∩ A).ncard ≤ 1 ∧ IsInsideOArc e A)
    (hCut : IsCutAlongEdge G e a b c S_e φ_e G_e) :
    IsBoundaryLinked G_e := by exact GraphMinor.GM07.theorem_7_2_proof hS h3 he_model G e φ_e G_e hBL hNoNull hCut

end

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- Graph Minors VII, (7.3) (pages 239–240):
"(7.3) *Let $\Sigma \cong \Sigma(a, b, c)$ where $3a + 3b + c \ge 3$. Let $G$ be a proper graph in
$\Sigma$, and let $r$ be an integer with $|V(G) \cap C| \le r - 1$ for every cuff $C$ of $\Sigma$,
and with $2 \le r \le \frac{2}{9}\alpha(G)$. Then there is an edge $e$ of $G$ which is not a loop,
such that $e \notin \Delta_{r-1}$ and $\bar{e} \cap bd(\Sigma) = \emptyset$, and such that there is
no $G$-normal null-homotopic $O$-arc $F$ with $|V(G) \cap F| \le 1$ and with $e$ inside $F$.*"

The proof uses the filled cuff-inside set (see the correction on page 238 in `corrections/GM07.md`)
and a direct pruning inequality. Where the paper says that $\alpha(G') = \alpha(G)$ is easy to see,
the proof shows only $\alpha(G) \le \alpha(G')$, which is all that the induction uses. -/
theorem theorem_7_3 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he_model : Nonempty (S ≃ₜ SurfaceModel a b c))
    (G : Drawing S) (r : ℕ) (hG : G.IsProper)
    (hcuff : ∀ C ∈ cuffs S, (G.V ∩ C).ncard ≤ r - 1)
    (hr : 2 ≤ r) (halpha : 9 * r ≤ 2 * alpha G) :
    ∃ (e : Set S) (S_e : Type u) (_ : TopologicalSpace S_e) (_ : T1Space S_e)
      (φ_e : S_e → S) (G_e : Drawing S_e),
      IsCutAlongEdge G e a b c S_e φ_e G_e ∧
      ¬ (e ⊆ allCuffsInsideSet G (r - 1)) ∧
      (¬ ∃ F : Set S, G.IsNormal F ∧ IsNullHomotopicOArc F ∧
        (G.V ∩ F).ncard ≤ 1 ∧ IsInsideOArc e F) := by exact GraphMinor.GM07.theorem_7_3_proof hS h3 he_model G r hG hcuff hr halpha

end

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- Graph Minors VII, (7.4) (page 240):
"(7.4) *Let $\Sigma \cong \Sigma(a, b, c)$, where $3a + 3b + c \ge 3$, and let $G$ be a
boundary-linked proper graph in $\Sigma$ with $\alpha(G) \ge \frac{9}{2}r$, where $r \ge 2$ is an
integer, and $|V(G) \cap C| \le r-1$ for every cuff $C$. Then there is an edge $e$ of $G$ which is
not a loop, with $\bar{e} \cap bd(\Sigma) = \emptyset$, such that $\phi_e^{-1}(G \setminus e)$ is
boundary-linked in $\Sigma_e$ and*
$$\alpha(\phi_e^{-1}(G \setminus e)) \ge r.$$"
Proved directly by combining `(7.1)`, `(7.2)`, and `(7.3)`. -/
theorem theorem_7_4 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he_model : Nonempty (S ≃ₜ SurfaceModel a b c))
    (G : Drawing S) (r : ℕ) (hBL : IsBoundaryLinked G)
    (halpha : 9 * r ≤ 2 * alpha G) (hr : 2 ≤ r)
    (hcuff : ∀ C ∈ cuffs S, (G.V ∩ C).ncard ≤ r - 1) :
    ∃ (e : Set S) (S_e : Type u) (_ : TopologicalSpace S_e) (_ : T1Space S_e)
      (φ_e : S_e → S) (G_e : Drawing S_e),
      IsCutAlongEdge G e a b c S_e φ_e G_e ∧
      IsBoundaryLinked G_e ∧
      r ≤ alpha G_e := by exact GraphMinor.GM07.theorem_7_4_proof hS h3 he_model G r hBL halpha hr hcuff

end

section

open Set Topology Classical GraphMinor.Surface

universe u

/-- Graph Minors VII, (7.5) (pages 240–241):
"(7.5) *Let $\Sigma \cong \Sigma(a, b, c)$, where $3a + 3b + c \ge 3$. Let $k \ge 0$ be an
integer, and let $v = v(\Sigma(a, b, c+1), k)$. Let $G$ be a boundary-linked proper graph in
$\Sigma$ with $\alpha(G) \ge 42kv$ and with $|V(G) \cap bd(\Sigma)| \le 2k - 2c - 2$. Let $H$ be a
forest in $\Sigma$ with $V(G) \cap bd(\Sigma) = V(H) \cap bd(\Sigma)$. Then $H$ is $G$-feasible.*"

The proof uses the stronger one-cuff bound proved within (6.1). See the correction to the proof of
(7.5) in `corrections/GM07.md`. -/
theorem theorem_7_5 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (k : ℕ) (G H : Drawing S)
    (hBL : IsBoundaryLinked G)
    (halpha : 42 * k * vModel a b (c + 1) k ≤ alpha G)
    (hbd_card : (G.V ∩ bd S).ncard + 2 * c + 2 ≤ 2 * k)
    (hH : IsSurfaceForest H) (hbd_eq : G.V ∩ bd S = H.V ∩ bd S) :
    IsGFeasible G H := by exact GraphMinor.GM07.theorem_7_5_proof hS h3 he k G H hBL halpha hbd_card hH hbd_eq

end

/-! ## Section 8. SCHISMS -/

/-! ## Section 9. MINORS -/

section

open Set Topology GraphMinor.Surface

universe u

/-- **Graph Minors VII, (9.1)** (page 242):
"Let $\Sigma \cong \Sigma(a, b, c)$ where $3a + 3b + c \ge 3$. Let $(H, H^+, H^-)$ be a proper digraph in $\Sigma$. Let $g$ be the number of isolated vertices of $H$ which are not in $bd(\Sigma)$. Let $k$ be an integer with
$$2k \ge 4|E(H)| + 4g + |V(H) \cap bd(\Sigma)| + 2c + 2$$
and let $c_0$ be an integer with $c_0 \ge c + |E(H)| + g + 1$. Let $(G, G^+, G^-)$ be a proper digraph in $\Sigma$ such that" -/
theorem theorem_9_1 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) (a b c : ℕ) (h3 : 3 * a + 3 * b + c ≥ 3)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (H : SurfaceDigraph S) (hH : H.IsProper)
    (k c₀ : ℕ)
    (hk : 2 * k ≥ 4 * H.G.E.ncard + 4 * numInternalIsolatedVertices H.G +
      (H.G.V ∩ bd S).ncard + 2 * c + 2)
    (hc₀ : c₀ ≥ c + H.G.E.ncard + numInternalIsolatedVertices H.G + 1)
    (G : SurfaceDigraph S) (hG : G.IsProper)
    (hbd_eq : G.G.V ∩ bd S = H.G.V ∩ bd S)
    (hBL : IsBoundaryLinked G.G)
    (halpha : alpha G.G ≥
      42 * k * 5 ^ (numInternalIsolatedVertices H.G + H.G.E.ncard) * vModel a b c₀ k) :
    IsBoundaryRootedMinor H G := by exact GraphMinor.GM07.theorem_9_1_proof hS a b c h3 he H hH k c₀ hk hc₀ G hG hbd_eq hBL halpha

end

section

open Set Topology GraphMinor.Surface

universe u

/-- Graph Minors VII, (9.2) (page 244):
"(9.2) *Let $\Sigma \cong \Sigma(a, b, 0)$ where $a + b \ge 1$, and let $(H, H^+, H^-)$ be a digraph
in $\Sigma$. Then there is a number $N$ such that $(H, H^+, H^-)$ is a minor of every digraph
$(G, G^+, G^-)$ in $\Sigma$ with $\alpha(G) \ge N$.*"
Proved directly from `theorem_9_1` by setting `k = 2 * |E(H)| + 2 * g + 1`,
`c₀ = |E(H)| + g + 1`, and `N = 42 * k * 5 ^ (g + |E(H)|) * vModel a b c₀ k`. -/
theorem theorem_9_2 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) (a b : ℕ) (hab : a + b ≥ 1)
    (he : Nonempty (S ≃ₜ SurfaceModel a b 0))
    (H : SurfaceDigraph S) :
    ∃ N : ℕ, ∀ G : SurfaceDigraph S, alpha G.G ≥ N → IsDigraphMinor H G := by exact GraphMinor.GM07.theorem_9_2_proof hS a b hab he H

end

section

open Set Topology GraphMinor.Surface

universe u

/-- Graph Minors VII, (9.3) (pages 244–245):
"(9.3) *Let $\Sigma$ be a cylinder with cuffs $C_1$ and $C_2$. Let $(H, H^+, H^-)$ be a proper
digraph in $\Sigma$. Let $t = |V(H)| + |E(H)|$, and let $r = 84(t+2) 5^t v(\Sigma(0, 0, t+4), 2t+4)$.
Let $(G, G^+, G^-)$ be a proper digraph in $\Sigma$ such that
$V(G) \cap \mathrm{bd}(\Sigma) = V(H) \cap \mathrm{bd}(\Sigma)$. Suppose that there are disjoint
$G$-normal $O$-arcs $F_1, F_2$ with the following properties:*
(i) *$F_1, F_2$ are not null-homotopic, and $C_1, F_2, F_1, C_2$ occur on $\Sigma$ in that order
(in the natural sense),*
(ii) *$|V(G) \cap F| \ge 2r$ for every $G$-normal $[0, 1]$-arc $F$ with
$F \cap F_1 \ne \emptyset \ne F \cap F_2$,*
(iii) *$k(F_1, F_2) \ge r$, and*
(iv) *$k(F_i, C_i) \ge |V(G) \cap C_i| \ (i = 1, 2)$.*
*Then $(H, H^+, H^-)$ is a boundary-rooted minor of $(G, G^+, G^-)$.*"

The bound `r` is `rCylinderBound H.G * 5 ^ t`, as printed. -/
theorem theorem_9_3 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) (he : Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {C₁ C₂ : Set S} (hcuffs : cuffs S = {C₁, C₂}) (hne : C₁ ≠ C₂)
    (H G : SurfaceDigraph S) (hH : H.IsProper) (hG : G.IsProper)
    (hbd_eq : G.G.V ∩ bd S = H.G.V ∩ bd S)
    {F₁ F₂ : Set S} (hF₁ : G.G.IsNormal F₁) (hF₂ : G.G.IsNormal F₂)
    (hOrder : CylinderOArcsInOrder C₁ F₂ F₁ C₂)
    (hInC₁ : ∀ x ∈ F₂, IsPointInsideSurroundingOArc C₁ F₁ x)
    (hbd₁ : Disjoint F₁ (bd S)) (hbd₂ : Disjoint F₂ (bd S))
    (hLine : ∀ F : Set S, G.G.IsNormal F → IsLine F →
      (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      2 * (rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) ≤ (G.G.V ∩ F).ncard)
    (hk12 : rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ maxDisjointPaths G.G F₁ F₂)
    (hkC₁ : (G.G.V ∩ C₁).ncard ≤ maxDisjointPaths G.G F₁ C₁)
    (hkC₂ : (G.G.V ∩ C₂).ncard ≤ maxDisjointPaths G.G F₂ C₂) :
    IsBoundaryRootedMinor H G := by exact GraphMinor.GM07.theorem_9_3_proof hS he hcuffs hne H G hH hG hbd_eq hF₁ hF₂ hOrder hInC₁ hbd₁ hbd₂ hLine hk12 hkC₁ hkC₂

end

section

open Set Topology GraphMinor.Surface

universe u

/-- Graph Minors VII, (9.4) (page 246):
"(9.4) *Let $\Sigma$ be a closed disc with cuff $C$ and let $(H, H^+, H^-)$ be a proper digraph in
$\Sigma$. Let $r$ be defined as in (9.3). Let $(G, G^+, G^-)$ be a proper digraph in $\Sigma$, such
that $V(G) \cap \mathrm{bd}(\Sigma) = V(H) \cap \mathrm{bd}(\Sigma)$. Suppose that there are
disjoint $G$-normal $O$-arcs $F_1, F_2$ of $\Sigma$, with $F_1$ inside $F_2$, such that*
(i) *$|V(G) \cap F| \ge 2r$ for every $G$-normal $[0, 1]$-arc $F$ with
$F \cap F_1 \ne \emptyset \ne F \cap F_2$,*
(ii) *$k(F_1, F_2) \ge r$, and*
(iii) *$k(F_1, C) \ge |V(G) \cap C|$.*
*Then $(H, H^+, H^-)$ is a boundary-rooted minor of $(G, G^+, G^-)$.*" -/
theorem theorem_9_4 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) (hD : IsClosedDisc (univ : Set S))
    {C : Set S} (hcuffs : cuffs S = {C})
    (H G : SurfaceDigraph S) (hH : H.IsProper) (hG : G.IsProper)
    (hbd_eq : G.G.V ∩ bd S = H.G.V ∩ bd S)
    {F₁ F₂ : Set S} (hF₁ : G.G.IsNormal F₁) (hF₂ : G.G.IsNormal F₂)
    (hO₁ : IsOArc F₁) (hO₂ : IsOArc F₂) (hDisj : Disjoint F₁ F₂)
    (hInside : IsInsideOArc F₁ F₂) (hbd₂ : Disjoint F₂ (bd S))
    (hLine : ∀ F : Set S, G.G.IsNormal F → IsLine F →
      (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      2 * (rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) ≤ (G.G.V ∩ F).ncard)
    (hk12 : rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ maxDisjointPaths G.G F₁ F₂)
    (hkC : (G.G.V ∩ C).ncard ≤ maxDisjointPaths G.G F₁ C) :
    IsBoundaryRootedMinor H G := by exact GraphMinor.GM07.theorem_9_4_proof hS hD hcuffs H G hH hG hbd_eq hF₁ hF₂ hO₁ hO₂ hDisj hInside hbd₂ hLine hk12 hkC

end

section

open Set Topology GraphMinor.Surface

universe u

/-- Graph Minors VII, (9.5) (page 246):
"(9.5) *Let $\Sigma$ be a sphere, and let $(H, H^+, H^-)$ be a proper digraph in $\Sigma$. Let $r$
be defined as in (9.3). Let $(G, G^+, G^-)$ be a proper digraph in $\Sigma$. Suppose that there are
disjoint $G$-normal $O$-arcs $F_1, F_2$ of $\Sigma$ satisfying (i) and (ii) of (9.4). Then
$(H, H^+, H^-)$ is a boundary-rooted minor of $(G, G^+, G^-)$.*" -/
theorem theorem_9_5 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) (hSph : IsSphere S)
    (H G : SurfaceDigraph S) (hH : H.IsProper) (hG : G.IsProper)
    {F₁ F₂ : Set S} (hF₁ : G.G.IsNormal F₁) (hF₂ : G.G.IsNormal F₂)
    (hO₁ : IsOArc F₁) (hO₂ : IsOArc F₂) (hDisj : Disjoint F₁ F₂)
    (hLine : ∀ F : Set S, G.G.IsNormal F → IsLine F →
      (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      2 * (rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) ≤ (G.G.V ∩ F).ncard)
    (hk12 : rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ maxDisjointPaths G.G F₁ F₂) :
    IsBoundaryRootedMinor H G := by exact GraphMinor.GM07.theorem_9_5_proof hS hSph H G hH hG hF₁ hF₂ hO₁ hO₂ hDisj hLine hk12

end

section

open Set Topology GraphMinor.Surface

universe u

/-- Graph Minors VII, (9.6) (page 246):
"(9.6) *Let $(G, G^+, G^-)$, $(H, H^+, H^-)$ be directed graphs in a sphere $\Sigma$, where $G$ is
isomorphic to an $N \times N$-grid. If $N$ is sufficiently large (bounded below by a function of
$H$) then $(H, H^+, H^-)$ is a minor of $(G, G^+, G^-)$.*" -/
theorem theorem_9_6 {S : Type u} [TopologicalSpace S]
    [T1Space S] (hS : IsSurface S) (hSph : IsSphere S)
    (H : SurfaceDigraph S) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) (G : SurfaceDigraph S),
      N₀ ≤ N → IsGridDrawing G.G N → IsDigraphMinor H G := by exact GraphMinor.GM07.theorem_9_6_proof hS hSph H

end

/-! ## Section 10. An Algorithm -/

/-! ## Section 11. APPENDIX -/

section

open Set Function Topology Metric unitInterval OnePoint Classical
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

/-- Graph Minors VII, (11.1) (page 249):
"If $\Sigma$ is a surface and $\phi \colon [0, 1] \to \Sigma$ is continuous with $\phi(0) \ne \phi(1)$, there is a $[0, 1]$-arc included in $|\phi|$ with ends $\phi(0), \phi(1)$." -/
theorem theorem_11_1 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (φ : C(unitInterval, S)) (hne : φ 0 ≠ φ 1) :
    ∃ L : Set S, L ⊆ range φ ∧ IsLineWithEnds L (φ 0) (φ 1) := by exact GraphMinor.GM07.theorem_11_1_proof hS φ hne

end

section

open Set Function Topology Metric unitInterval OnePoint Classical
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

/-- Graph Minors VII, (11.2) (page 249):
"If $\Sigma$ is a surface, and $\phi \colon S^1 \to \Sigma$ is continuous and non-null-homotopic, there is a non-null-homotopic $O$-arc included in $|\phi|$." -/
theorem theorem_11_2 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (φ : C(Circle, S))
    (hφ : ¬ ClosedCurveIsNullHomotopicIn univ φ) :
    ∃ F : Set S, IsOArc F ∧ F ⊆ range φ ∧ ¬ IsNullHomotopicOArc F := by exact GraphMinor.GM07.theorem_11_2_proof hS φ hφ

end

section

open Set Function Topology Metric unitInterval OnePoint Classical
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

/-- Graph Minors VII, (11.3) (page 249):
"Let $\Sigma$ be a connected surface, let $\Delta \subseteq \Sigma$ be a closed disc, and let $Y \subseteq \Sigma$ be such that $Y \cap bd(\Delta)$ is arc-connected. Then any continuous map $\phi \colon S^1 \to Y \cup (\Delta - bd(\Delta))$ is homotopic to a map $\psi \colon S^1 \to Y$ with $|\psi| \subseteq |\phi| \cup bd(\Delta)$. In particular, if $Y$ is flat then so is $Y \cup (\Delta - bd(\Delta))$." -/
theorem theorem_11_3 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {Δ Y : Set S} (hΔ : IsClosedDisc Δ)
    (hY_arc : IsArcConnected (Y ∩ discBd Δ)) :
    (∀ φ : C(Circle, S), range φ ⊆ Y ∪ (Δ \ discBd Δ) →
      ((∃ z : Circle, φ z ∉ Δ \ discBd Δ) ∨ (Y ∩ discBd Δ).Nonempty) →
      ∃ ψ : C(Circle, S), range ψ ⊆ Y ∧ range ψ ⊆ range φ ∪ discBd Δ ∧
        ClosedCurvesHomotopicIn univ φ ψ) ∧
    (IsFlat Y → IsFlat (Y ∪ (Δ \ discBd Δ))) := by exact GraphMinor.GM07.theorem_11_3_proof hS hΔ hY_arc

end

section

open Set Function Topology Metric unitInterval OnePoint Classical
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

/-- Graph Minors VII, (11.4) (page 251):
"If $Z$ is connected and l.a.c. then $Z$ is arc-connected." -/
theorem theorem_11_4 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {Z : Set S}
    (hconn : IsConnected Z) (hlac : IsLocallyArcConnected Z) :
    IsArcConnected Z := by exact GraphMinor.GM07.theorem_11_4_proof hS hconn hlac

end

section

open Set Function Topology Metric unitInterval OnePoint Classical
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

/-- Graph Minors VII, (11.5) (page 251):
"If $Z \subseteq \Sigma$ is flat and l.a.c., there is an open, flat, l.a.c. set $Y \subseteq \Sigma$ with $Z \subseteq Y$, which may be chosen arc-connected if $Z$ is arc-connected." -/
theorem theorem_11_5 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {Z : Set S} (hZ_flat : IsFlat Z) (hZ_lac : IsLocallyArcConnected Z) :
    ∃ Y : Set S, Z ⊆ Y ∧ IsOpen Y ∧ IsFlat Y ∧ IsLocallyArcConnected Y ∧
      (IsArcConnected Z → IsArcConnected Y) := by exact GraphMinor.GM07.theorem_11_5_proof hS hZ_flat hZ_lac

end

section

open Set Function Topology Metric unitInterval OnePoint Classical
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

/-- Graph Minors VII, (11.6) (page 252):
"If $Z_1, Z_2 \subseteq \Sigma$ are solid, so is $Z_1 \cup Z_2$." -/
theorem theorem_11_6 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {Z₁ Z₂ : Set S}
    (h₁ : IsSolid Z₁) (h₂ : IsSolid Z₂) :
    IsSolid (Z₁ ∪ Z₂) := by exact GraphMinor.GM07.theorem_11_6_proof hS h₁ h₂

end

section

open Set Function Topology Metric unitInterval OnePoint Classical
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

/-- Graph Minors VII, (11.7) (page 253):
"If $Z \subseteq \Sigma$ is solid and flat, and $\Sigma$ is connected, there exists $Y \subseteq \Sigma$ with $Z \subseteq Y$ such that $Y$ is solid, flat, and arc-connected." -/
theorem theorem_11_7 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S] {Z : Set S}
    (hZ_solid : IsSolid Z) (hZ_flat : IsFlat Z) :
    ∃ Y : Set S, Z ⊆ Y ∧ IsSolid Y ∧ IsFlat Y ∧ IsArcConnected Y := by exact GraphMinor.GM07.theorem_11_7_proof hS hZ_solid hZ_flat

end

section

open Set Function Topology Metric unitInterval OnePoint Classical
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

/-- Graph Minors VII, (11.8) (page 253):
"If $Z \subseteq \Sigma$ is open, flat, and arc-connected, there is an open, simply connected set $Y \subseteq \Sigma$ with $Z \subseteq Y$." -/
theorem theorem_11_8 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {Z : Set S}
    (hZ_open : IsOpen Z) (hZ_flat : IsFlat Z) (hZ_arc : IsArcConnected Z) :
    ∃ Y : Set S, Z ⊆ Y ∧ IsOpen Y ∧ IsSimplyConnectedSubset Y := by exact GraphMinor.GM07.theorem_11_8_proof hS hZ_open hZ_flat hZ_arc

end

section

open Set Function Topology Metric unitInterval OnePoint Classical
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

/-- Graph Minors VII, (11.9) (page 253):
"If $\Sigma$ is connected and $Z \subseteq \Sigma$ is flat and l.a.c., and either $Z$ is closed or $Z$ is arc-connected, then there is an open simply connected subset $Y \subseteq \Sigma$ with $Z \subseteq Y$."

`theorem_11_9_closed` (`GraphMinor/GM07/Section11.lean`) restates it for surfaces with empty
boundary, with simple connectivity in the sense of `GM14.IsArcSimplyConnected`. -/
theorem theorem_11_9 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S] {Z : Set S}
    (hZ_flat : IsFlat Z) (hZ_lac : IsLocallyArcConnected Z)
    (hZ_cl_or_arc : IsClosed Z ∨ IsArcConnected Z) :
    ∃ Y : Set S, Z ⊆ Y ∧ IsOpen Y ∧ IsSimplyConnectedSubset Y ∧ Y.Nonempty := by exact GraphMinor.GM07.theorem_11_9_proof hS hZ_flat hZ_lac hZ_cl_or_arc

end

section

open Set Function Topology Metric unitInterval OnePoint Classical
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

/-- Graph Minors VII, (11.10) (page 253):
"If $\Sigma$ is connected and $Z \subseteq \Sigma$ is solid and flat, then either $Z = \Sigma$ or $Z$ is planar." -/
theorem theorem_11_10 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [ConnectedSpace S] {Z : Set S}
    (hZ_solid : IsSolid Z) (hZ_flat : IsFlat Z) :
    Z = univ ∨ IsPlanar Z := by exact GraphMinor.GM07.theorem_11_10_proof hS hZ_solid hZ_flat

end

end GraphMinor.GM07
