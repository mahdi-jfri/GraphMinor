module

public import GraphMinor.GM16.Defs
public import GraphMinor.GM16.InductionsProved
public import GraphMinor.GM16.Introduction
public import GraphMinor.GM16.Section1Proof
public import GraphMinor.GM16.Section1Statements
public import GraphMinor.GM16.Section2
public import GraphMinor.GM16.Section3
public import GraphMinor.GM16.Section4
public import GraphMinor.GM16.Section4Proof
public import GraphMinor.GM16.Section5
public import GraphMinor.GM16.Section5Five
public import GraphMinor.GM16.Section5Four
public import GraphMinor.GM16.Section5Proof
public import GraphMinor.GM16.Section6
public import GraphMinor.GM16.Section6Proof
public import GraphMinor.GM16.Section7
public import GraphMinor.GM16.Section7ProperProof
public import GraphMinor.GM16.Section8
public import GraphMinor.GM16.Section8Main
public import GraphMinor.GM16.Section8Proof
public import GraphMinor.GM16.Section9Proof
public import GraphMinor.GM16.Wagner

/-!
# Graph Minors XVI: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XVI. Excluding a non-planar graph*, J. Combin. Theory
Ser. B **89** (2003), 43–76.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. The docstrings say where the Lean differs from the print, and
`corrections/GM16.md` lists the corrections to the paper.
-/

public section

namespace GraphMinor.GM16

open Set Function Topology

universe u_1 u_2 u_3 u_4 u v w u' v'

/-! ## Section 1. Introduction -/

open Graph in
/-- **Graph Minors XVI, (1.1)**, page 44:
"For any planar graph $L$ there is a number $N$ such that every graph with no $L$-minor has
tree-width $\le N$."

This is proved by `GM05.Full.theorem_1_5`, allowing loops and parallel edges
in both graphs. The host has finite vertex and edge sets.

The Lean applies the planar exclusion theorem of Graph Minors V directly, since the paper quotes
(1.1) as the main theorem of Graph Minors V. -/
theorem theorem_1_1 {α β α' β' : Type*} (L : Graph α' β') (hL : IsPlanar L) :
    ∃ N : ℕ, ∀ G : Graph α β, V(G).Finite → E(G).Finite →
    ¬ IsIsoMinor L G → GM05.Full.TreeWidthLE G N :=
  theorem_1_1_proof L hL

open Graph in
/-- **Graph Minors XVI, (1.2)** (Wagner).

"**1.2.** *A graph $G$ has no $K_5$ minor if and only if $G$ is a tree-structure over the class of
all graphs which are either planar or isomorphic to $V_8$.*"

The paper quotes Wagner's theorem and does not prove it. We prove it by our own route, with the
pieces in `GraphMinor/Wagner/`. The graph is lifted to new edge labels by `liftEdgeInl`, because a
clique-sum may need edges that the edge type `β` has no room for. -/
theorem theorem_1_2 {α : Type u_1} {β : Type u_2} (G : Graph α β) (hV : V(G).Finite)
    (hE : E(G).Finite) :
    ¬ IsIsoMinor (completeGraph 5) G ↔
    HasTreeStructureOver
      {H : Graph α (β ⊕ ℕ) | IsPlanar H ∨ Nonempty (Iso H wagnerGraphV8)} (liftEdgeInl G) :=
  theorem_1_2_proof G hV hE

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM15 Surface in
/-- **Graph Minors XVI, (1.3)** (pages 46 and 51–52):
"Let $L$ be a nonplanar graph, and let $\Sigma_1, \dots, \Sigma_s$ be all the connected surfaces
(up to homeomorphism) in which $L$ cannot be drawn. Then there are numbers $r, d, w$ such that
every graph with no $L$-minor may be constructed by clique-sums, starting from graphs $G'$ with the
following property: $G'$ is a $(\le w)$-vertex extension of an outgrowth by $\le d$ $r$-rings of a
graph that can be drawn in one of $\Sigma_1, \dots, \Sigma_s$."

Because the enlargement vertex set $Z$ on page 48 may meet $V(H_0)$ for a torso $H_0$ of a design in
$\mathscr{D}$, deleting the $\le w_0$ vertices $Z$ from $G'$ yields $H_0 \setminus Z$ rather than
$H_0$
itself; applying `IsOutgrowthByRings.deleteVertices` shows that $H_0 \setminus Z$ is an outgrowth by
$\le d$ rings of parameter $r = (w_0 + 1)(2\rho + 1)$ (instead of the paper's $2\rho + 1$).

Clique-sums use new edge labels, since a clique-sum may need edges that the edge type `β` has no
room for. The proof takes `r = (w + 1)(2ρ + 1)`, because deleting a perimeter vertex from an
`r`-ring need not leave an `r`-ring, and (1.3) says only that `r` exists. The proof corrects a step
of the paper's proof: see the correction to the proof of (1.3) in `corrections/GM16.md`. -/
theorem theorem_1_3 {α' : Type u'} {β' : Type v'} (L : Graph α' β') (hVL : V(L).Finite)
    (hEL : E(L).Finite)
    (hNonplanar : ∀ (S : Type w) [TopologicalSpace S] [T2Space S], IsSphere S → ¬ CanBeDrawnIn S L) :
    ∃ r d w₀ : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β), V(G).Finite → E(G).Finite →
    ¬ IsIsoMinor L G →
    HasTreeStructureOver
    {H : Graph α (β ⊕ ℕ) | ∃ (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
      (H₀ : Graph α (β ⊕ ℕ)), IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
      IsVertexExtension w₀ H H₀ ∧ IsOutgrowthByRings S H₀ d r} (liftEdgeInl G) :=
  GM16.theorem_1_3_proof L hVL hEL hNonplanar

/-! ## Section 2. Structure relative to a tangle -/

open Graph SimpleGraph Hypergraph GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (2.1)** (page 48):
"For any $\theta \ge 1$, let $\mathscr{D}$ be a class of designs which is $\theta$-pervasive in a
graph $G$. Then $G$ has a tree-decomposition $(T, \tau)$ such that for each $t \in V(T)$, the
design of $t$ in $(T, \tau)$ belongs to $\mathscr{D}^{3\theta-2} \cup \mathscr{R}_{4\theta-3}$." -/
theorem theorem_2_1 {α : Type u} {β : Type v} {G : Graph α β} {θ : ℕ} {𝒟 : Set (GraphDesign α β)}
    (hV : V(G).Finite) (hE : E(G).Finite) (hθ : 1 ≤ θ) (hperv : IsGraphPervasive G θ 𝒟) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Graph α β),
    IsGraphTreeDecompositionOver G
      (graphEnlargementClass 𝒟 (3 * θ - 2) ∪ smallGraphDesignClass (4 * θ - 3)) T τ :=
  GM16.theorem_2_1_proof hV hE hθ hperv

open Graph SimpleGraph Hypergraph GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (2.2)** (page 48):
"Let $\mathscr{D}$ be a class of designs, and let $\mathscr{D}'$ be the class of torsos of members
of $\mathscr{D}$. If $G$ is a graph with a tree-decomposition $(T, \tau)$ such that $\mathscr{D}$
contains the design of $t$ in $(T, \tau)$ for each $t \in V(T)$, then $G$ is a tree-structure over
$\mathscr{D}'$." -/
theorem theorem_2_2 {α : Type u} {β : Type v} {ι : Type*} [Fintype ι] {G : Graph α (β ⊕ ℕ)}
    {𝒟 : Set (GraphDesign α (β ⊕ ℕ))} {T : SimpleGraph ι} {τ : ι → Graph α (β ⊕ ℕ)}
    (hV : V(G).Finite) (hE : E(G).Finite) (hover : IsGraphTreeDecompositionOver G 𝒟 T τ) :
    HasTreeStructureOver (torsosOfClass 𝒟) G :=
  GM16.theorem_2_2_proof hV hE hover

open Graph SimpleGraph Hypergraph GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (2.3)** (page 48):
"For any $\theta \ge 1$, let $\mathscr{D}$ be a class of designs which is $\theta$-pervasive in a
graph $G$. Then $G$ may be constructed by clique-sums starting from graphs $G'$ such that either
* $|V(G')| \le 4\theta - 3$, or
* $G'$ is a $(\le 3\theta - 2)$-vertex extension of a torso of a member of $\mathscr{D}$."

Note: This theorem is stated with the loose notion `IsLooseVertexExtension` (`G' \ Z = H \ Z` for a
subgraph `H ≤ G'` with `|Z| ≤ 3θ - 2`), because the sentence preceding (2.3) on page 48 ("every
torso of a member of $\mathscr{D}^n$ is a $(\le n)$-vertex extension of a torso of a
member of $\mathscr{D}$") fails with
the strict definition `deleteVertices G' Z = H` when the enlargement set `Z` meets `V(H)`.

The Lean uses a loose vertex extension, in which the smaller graph may keep the vertices of `Z`. See
the correction on page 48 in `corrections/GM16.md`. -/
theorem theorem_2_3 {α : Type u} {β : Type v} {G : Graph α (β ⊕ ℕ)} {θ : ℕ}
    {𝒟 : Set (GraphDesign α (β ⊕ ℕ))} (hV : V(G).Finite) (hE : E(G).Finite) (hθ : 1 ≤ θ)
    (hperv : IsGraphPervasive G θ 𝒟) :
    HasTreeStructureOver
    {G' : Graph α (β ⊕ ℕ) | V(G').ncard ≤ 4 * θ - 3 ∨
      ∃ H ∈ torsosOfClass 𝒟, IsLooseVertexExtension (3 * θ - 2) G' H} G :=
  GM16.theorem_2_3_proof hV hE hθ hperv

/-! ## Section 3. Surfaces, societies and segregations -/

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (3.1)** (page 49): "For any graph $L$, there are integers $\kappa, \rho,
\zeta \ge 0$ and $\theta \ge 1$ with the following property. Let $\mathscr{T}$ be a tangle of order
$\ge \theta$ in a graph $G$, controlling no $L$-minor of $G$. Then there exists $Z \subseteq V(G)$
with $|Z| \le \zeta$, and a $\mathscr{T} \setminus Z$-central segregation of $G \setminus Z$ of type
$(\rho, \kappa)$ which has a proper arrangement in some surface in which $L$ cannot be drawn."

Graph Minors XVI, (3.1), pages 49 and 54, by induction over the
surface tower, starting with the proved sphere span (4.2) and using
the proved animal reduction (4.1). No result of XVI is assumed. -/
theorem theorem_3_1 {α' : Type*} {β' : Type*} (L : Graph α' β') (h1 : V(L).Finite)
    (h2 : E(L).Finite) :
    ∃ κ ρ ζ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
    (T : Set (Hypergraph α β × Hypergraph α β)) (hT : IsGraphTangle G θ_G T), θ ≤ θ_G →
    ¬ ControlsMinor G L T →
    ∃ (Z : Set α) (S_seg : Set (Society α β)) (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
    (α_disc : Society α β → Set S) (α_pt : α → S), Z ⊆ V(G) ∧ Z.ncard ≤ ζ ∧ Z.ncard < θ_G ∧
    IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
    IsCentralSegregation (deleteVertices G Z)
    (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T θ_G) S_seg ∧
    IsSegregationOfType (deleteVertices G Z) ρ κ S_seg ∧ IsProperArrangement S_seg α_disc α_pt :=
  GM16.theorem_3_1_proof L h1 h2

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (3.2)** (page 50): "Let $(G, \Omega)$ be a $\rho$-vortex, and let the
vertices in $\bar{\Omega}$ be $t_1, \ldots, t_n$ in order, where $n \ge 1$. Then there are
separations $(A_1, B_1), \ldots, (A_n, B_n)$ of $G$, such that:"

Graph Minors XVI, (3.2), page 50, by the paper's linear
 decomposition and the separator sets of consecutive pieces. -/
theorem theorem_3_2 {α : Type u} {β : Type v} (S : Society α β) (ρ n : ℕ) (t : Fin n → α)
    (hn : 1 ≤ n) (hvortex : IsRhoVortex S ρ) (ht_inj : Injective t) (ht_range : range t = S.Ω.bar)
    (ht_cw : S.Ω.IsClockwiseSeq (List.ofFn t)) :
    ∃ A B : Fin n → Graph α β, (∀ i : Fin n, IsGraphSeparation S.G (A i) (B i)) ∧
    (∀ i j : Fin n, t j ∈ V(B i)) ∧ (∀ i : Fin n, t i ∈ V(A i)) ∧
    IsGraphLocation S.G (range fun i : Fin n => (A i, B i)) ∧
    (∀ i : Fin n, (V(A i) ∩ V(B i)).ncard ≤ 2 * ρ + 1) ∧
    (∀ H' : Graph α β,
      IsTorsoOfDesign (graphLocationDesign S.G (range fun i : Fin n => (A i, B i))) H' →
      IsRRing H' (2 * ρ + 1) (List.ofFn t)) :=
  GM16.theorem_3_2_proof S ρ n t hn hvortex ht_inj ht_range ht_cw

/-! ## Section 4. Induction on the surface -/

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (4.1)** (page 52): "Let $\Sigma$ be a surface and let $p \ge 0$, $\phi \ge
1$. Then there exist $\kappa, \rho, \zeta \ge 0$ and $\theta \ge 1$ such that if $\mathscr{T}^*$ is
a tangle in a graph $G$, and there is a $\Sigma$-span of order $\ge \theta$, then either"

Graph Minors XVI, (4.1), pages 52 and 58, by the backward induction
on the number of horns, using the proved (5.1) and (5.5). -/
theorem theorem_4_1 {S : Type w} [TopologicalSpace S] [T2Space S] (h1 : IsClosedSurface S)
    (h2 : ConnectedSpace S) (p φ : ℕ) (h3 : 1 ≤ φ) :
    ∃ κ ρ ζ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (H : Drawing S) (η : SpanEmbedding H G)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (hT : IsGraphTangle G θ_star T_star),
    θ ≤ θ_span → IsSigmaSpan G H η θ_star θ_span T_star T →
    (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S') (H' : Drawing S')
      (η' : SpanEmbedding H' G) (θ_span' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))), IsClosedSurface S' ∧
      ConnectedSpace S' ∧ IsObtainedByAddingHandleOrCrosscap S S' ∧ φ ≤ θ_span' ∧
      IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
    (∃ (Z : Set α) (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S), Z ⊆
      V(G) ∧ Z.ncard ≤ ζ ∧ Z.ncard < θ_star ∧
      IsCentralSegregation (deleteVertices G Z)
      (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
      IsSegregationOfType (deleteVertices G Z) ρ κ S_seg ∧ IsProperArrangement S_seg α_disc α_pt) ∨
    ControlsMinor G (completeGraph p) T_star :=
  GM16.theorem_4_1_proof h1 h2 p φ h3

open Graph Hypergraph Surface GM10 GM14 GM15 SimpleGraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (4.2)** (page 53): "For any integer $\theta \ge 1$ there exists $\theta^*
\ge 1$ such that if $\mathscr{T}^*$ is a tangle of order $\ge \theta^*$ in a graph $G$, there is a
$\Sigma$-span of order $\ge \theta$, where $\Sigma$ is the sphere."

Graph Minors XVI, (4.2), pages 53–54. Every sufficiently high-order
graph tangle has a sphere span of the prescribed order. The wall,
subdivision, drawing, and induced-tangle steps of the paper are all
proved; the initial height is increased to an even value at least four. -/
theorem theorem_4_2 (θ : ℕ) (_hθ : 1 ≤ θ) :
    ∃ θ_star : ℕ, 1 ≤ θ_star ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)), IsGraphTangle G θ_G T_star → θ_star ≤ θ_G →
    ∀ (S : Type w) [TopologicalSpace S] [T2Space S], IsClosedSurface S → ConnectedSpace S →
    IsSphere S →
    ∃ (H : Drawing S) (η : SpanEmbedding H G) (θ_span : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))), θ ≤ θ_span ∧
    IsSigmaSpan G H η θ_G θ_span T_star T :=
  GM16.theorem_4_2_proof θ _hθ

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (4.3)** (page 54, citing Graph Minors XII, (4.3)):
"If $L$ is a graph and $\Sigma$ is a surface such that $L$ can be drawn in $\Sigma$, there is an
integer $\theta \ge 1$ with the following property. If $\mathscr{T}^*$ is a tangle in a graph $G$
controlling no $L$ minor, then there is no $\Sigma$-span of order $\ge \theta$." -/
theorem theorem_4_3 {S : Type w} [TopologicalSpace S] [T2Space S] {α' : Type u'} {β' : Type v'}
    (L : Graph α' β') (hS : IsClosedSurface S) (hconn : ConnectedSpace S) (hVL : V(L).Finite)
    (hEL : E(L).Finite) (hdraw : CanBeDrawnIn S L) :
    ∃ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_span : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
    IsGraphTangle G θ_star T_star → ¬ ControlsMinor G L T_star → θ ≤ θ_span →
    ¬ IsSigmaSpan G H η θ_star θ_span T_star T :=
  GM16.theorem_4_3_proof L hS hconn hVL hEL hdraw

/-! ## Section 5. Induction on horns -/

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (5.1)** (page 55): "Let $\Sigma$ be a surface and let $p, \tau, \chi \ge 0$
and $\phi, \psi \ge 1$. Then there exist $\sigma, \kappa, \rho, \zeta \ge 0$ and $\theta \ge 1$ such
that if $\mathscr{T}^*$ is a tangle in a graph $G$, and there is a hairless animal with $\chi$
horns, of strength $\ge (\theta, \sigma)$, then either: 1. there is a $\Sigma'$-span of order $\ge
\phi$, for some surface $\Sigma'$ obtained from $\Sigma$ by adding a handle or a crosscap, or 2.
there is a hairless animal with $\chi + 1$ horns, of strength $\ge (\psi, \tau)$, or 3. there exists
$Z \subseteq V(G)$ with $|Z| \le \zeta$, and a $\mathscr{T}^* \setminus Z$-central segregation of $G
\setminus Z$ of type $(\rho, \kappa)$ with a proper arrangement in $\Sigma$, or 4. $\mathscr{T}^*$
controls a $K_p$-minor of $G$."

Graph Minors XVI, (5.1), pages 55 and 61, by the backward induction
on the number of hairs, using the proved (6.1) and (6.3). -/
theorem theorem_5_1 {S : Type w} [TopologicalSpace S] [T2Space S] (h1 : IsClosedSurface S)
    (h2 : ConnectedSpace S) (p τ χ φ ψ : ℕ) (h3 : 1 ≤ φ) (h4 : 1 ≤ ψ) :
    ∃ σ κ ρ ζ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (hT : IsGraphTangle G θ_star T_star),
    HasHairlessAnimal S G T_star θ_star χ θ σ →
    (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S') (H' : Drawing S')
      (η' : SpanEmbedding H' G) (θ_span' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))), IsClosedSurface S' ∧
      ConnectedSpace S' ∧ IsObtainedByAddingHandleOrCrosscap S S' ∧ φ ≤ θ_span' ∧
      IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
    HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ ∨
    (∃ (Z : Set α) (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S), Z ⊆
      V(G) ∧ Z.ncard ≤ ζ ∧ Z.ncard < θ_star ∧
      IsCentralSegregation (deleteVertices G Z)
      (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
      IsSegregationOfType (deleteVertices G Z) ρ κ S_seg ∧ IsProperArrangement S_seg α_disc α_pt) ∨
    ControlsMinor G (completeGraph p) T_star :=
  GM16.theorem_5_1_proof h1 h2 p τ χ φ ψ h3 h4

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (5.2)** (page 55, citing Graph Minors XII, (4.4)):
"Let $\Sigma$ be a surface and let $p \ge 0$. Then there exists $\theta \ge 1$ such that if
$\mathscr{T}^*$ is a tangle in a graph $G$, and $H, \eta, \mathscr{T}$ is a $\Sigma$-span of order
$\ge \theta$ with metric $d$, and
* $s_1, t_1, \dots, s_\mu, t_\mu$ are distinct vertices of $H$, where $\mu = \frac{1}{2}p(p - 1)$,
  such that $d(u, v) \ge \theta$ for all distinct $u, v \in \{s_1, t_1, \dots, s_\mu, t_\mu\}$, and
* $Q_1, \dots, Q_\mu$ are mutually disjoint $\eta(H)$-paths, such that $Q_i$ has ends
  $\eta(s_i), \eta(t_i) (1 \le i \le \mu)$,
then $\mathscr{T}^*$ controls a $K_p$-minor of $G$." -/
theorem theorem_5_2 {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hconn : ConnectedSpace S) (p : ℕ) :
    ∃ θ : ℕ, 1 ≤ θ ∧
    let μ := p * (p - 1) / 2
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (H : Drawing S) (η : SpanEmbedding H G)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (s t : Fin μ →
      S) (Q : Fin μ → Graph α β), IsSigmaSpan G H η θ_star θ_span T_star T →
    HasTangleMetric H θ_span T d → θ ≤ θ_span → (∀ i : Fin μ, s i ∈ H.V ∧ t i ∈ H.V ∧ s i ≠ t i) →
    Injective s → Injective t → Disjoint (range s) (range t) →
    (∀ u ∈ range s ∪ range t, ∀ v ∈ range s ∪ range t, u ≠ v → θ ≤ d {u} {v}) →
    (∀ i : Fin μ, IsHPathWithEnds G η.imageGraph (Q i) (η.vMap (s i)) (η.vMap (t i))) →
    Pairwise (fun i j => Disjoint V(Q i) V(Q j)) → ControlsMinor G (completeGraph p) T_star :=
  GM16.theorem_5_2_proof hS hconn p

open Graph SimpleGraph GraphMinor.Surface GraphMinor.GM09 Hypergraph GraphMinor.GM06 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (5.3)** (page 56): "Let $G$ be a graph and let $Y \subseteq V(G)$, such that
no component of $G$ contains exactly one vertex in $Y$. If $\mu, \tau \ge 0$ are integers and $|Y| >
\tau(\mu - 1)$, then either: there are $\mu$ disjoint paths of $G$ each with both ends distinct and
in $Y$ and with no internal vertex in $Y$, or there exist $v \in V(G)$ and $\tau$ paths $P_1, \dots,
P_\tau$ of $G$, with ends $v, u_i (1 \le i \le \tau)$ respectively, mutually disjoint except for
$v$, and such that for $1 \le i \le \tau, u_i \in Y$ and $u_i \ne v$, and no internal vertex of
$P_i$ is in $Y$."

A minimal forest preserving
the connections between marked vertices gives the subtree packing and
covering alternative. If the packing is too small, first-hit paths to
the cover and the paper's pigeonhole count give the required fan. -/
theorem theorem_5_3 {α : Type u} {β : Type v} (G : Graph α β) (Y : Set α) (μ τ : ℕ)
    (hV : V(G).Finite) (hE : E(G).Finite) (hYG : Y ⊆ V(G))
    (hcomp : ∀ y ∈ Y, ∃ y' ∈ Y, y' ≠ y ∧ Relation.ReflTransGen G.Adj y y')
    (hcount : τ * (μ - 1) < Y.ncard) :
    (∃ (P : Fin μ → Graph α β) (s t : Fin μ → α), Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      ∀ i : Fin μ, s i ∈ Y ∧ t i ∈ Y ∧ s i ≠ t i ∧ IsGraphPathWithEnds G (P i) (s i) (t i) ∧
      V(P i) ∩ Y = {s i, t i}) ∨
    (∃ (v : α) (P : Fin τ → Graph α β) (u : Fin τ → α), v ∈ V(G) ∧
      (∀ i j : Fin τ, i ≠ j → V(P i) ∩ V(P j) = {v} ∧ Disjoint E(P i) E(P j)) ∧ ∀ i : Fin τ,
      u i ∈ Y ∧ u i ≠ v ∧ IsGraphPathWithEnds G (P i) v (u i) ∧ V(P i) ∩ Y ⊆ {v, u i}) :=
  GM16.theorem_5_3_proof G Y μ τ hV hE hYG hcomp hcount

open Graph GraphMinor.Surface GraphMinor.GM09 SimpleGraph Hypergraph GraphMinor.GM06 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (5.4)** (pages 56–57): "Let $G$ be a graph, and let $v \in V(G)$. For $1 \le
i \le n$ let $P_i$ be a path of $G$ with distinct ends $v, u_i$, such that $P_1, \dots, P_n$ are
mutually disjoint except for $v$. Let $Q_1, \dots, Q_m$ be mutually disjoint paths of $G$, not
passing through $v$, such that $Q_i$ has ends $s_i, t_i$ for $1 \le i \le m$. Let $$Z = \{u_1,
\dots, u_n, s_1, t_1, \dots, s_m, t_m\}.$$ If $n \ge 5m + 2$, there are $m + 1$ mutually disjoint
paths of $G$, each with distinct ends both in $Z$."

, with the distinct-end
correction documented in `GM16Theorem54Statement`. We retain unmarked
components when applying (5.3). This has no effect on its paths, whose
ends lie in components containing two marked vertices. -/
theorem theorem_5_4 {α : Type u} {β : Type v} (G : Graph α β) (v : α) (n m : ℕ)
    (P : Fin n → Graph α β) (u : Fin n → α) (Q : Fin m → Graph α β) (s t : Fin m → α)
    (hV : V(G).Finite) (hE : E(G).Finite) (hv : v ∈ V(G))
    (hP : ∀ i : Fin n, u i ≠ v ∧ IsGraphPathWithEnds G (P i) v (u i))
    (hPP : ∀ i j : Fin n, i ≠ j → V(P i) ∩ V(P j) = {v} ∧ Disjoint E(P i) E(P j))
    (hQ : ∀ j : Fin m, v ∉ V(Q j) ∧ IsGraphPathWithEnds G (Q j) (s j) (t j))
    (hst : ∀ j : Fin m, s j ≠ t j) (hQQ : Pairwise (fun i j => Disjoint V(Q i) V(Q j)))
    (hn : 5 * m + 2 ≤ n) :
    let Z := range u ∪ range s ∪ range t
    ∃ (R : Fin (m + 1) → Graph α β) (a b : Fin (m + 1) → α),
    Pairwise (fun i j => Disjoint V(R i) V(R j)) ∧ ∀ i : Fin (m + 1), a i ∈ Z ∧ b i ∈ Z ∧
    a i ≠ b i ∧ IsGraphPathWithEnds G (R i) (a i) (b i) :=
  GM16.theorem_5_4_proof G v n m P u Q s t hV hE hv hP hPP hQ hst hQQ hn

open Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 SimpleGraph Hypergraph GraphMinor.GM06 GraphMinor.GM10 in
/-- **Graph Minors XVI, (5.5)** (pages 57–58): "For any surface $\Sigma$ and integer $p \ge 0$,
there exists $\theta \ge 1$ such that, if $\mathscr{T}^*$ is a tangle in a graph $G$ and there is a
hairless animal with $\frac{1}{2}p(p - 1)$ horns and with strength $\ge (\theta, 4p(p - 1))$, then
$\mathscr{T}^*$ controls a $K_p$-minor of $G$."

, by the paper's induction
on disjoint paths and then (5.2). The metric laws are supplied by XI (9.1),
and (5.2) uses XII (4.4). No statement of XVI is assumed. -/
theorem theorem_5_5 {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) (p : ℕ) :
    ∃ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)), IsGraphTangle G θ_star T_star →
    HasHairlessAnimal S G T_star θ_star (p * (p - 1) / 2) θ (4 * p * (p - 1)) →
    ControlsMinor G (completeGraph p) T_star :=
  GM16.theorem_5_5_proof hS hConn p

/-! ## Section 6. Induction on hairs -/

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (6.1)** (page 58): "Let $\Sigma$ be a surface, and let $p, \tau, \chi,
\delta \ge 0$ and $\phi, \psi \ge 1$. Then there exist $\sigma, \kappa, \rho, \zeta \ge 0$ and
$\theta \ge 1$ such that if $\mathscr{T}^*$ is a tangle in a graph $G$, and there is an animal with
$\chi$ horns and $\delta$ hairs, of strength $\ge (\theta, \sigma)$, then either 1. there is a
$\Sigma'$-span of order $\ge \phi$, for some surface $\Sigma'$ obtained from $\Sigma$ by adding a
handle or a crosscap, or 2. there is an animal with $\chi$ horns and $\delta + 1$ hairs, of strength
$\ge (\psi, \tau)$, or 3. there exists $Z \subseteq V(G)$ with $|Z| \le \zeta$, and a $\mathscr{T}^*
\setminus Z$-central segregation of $G \setminus Z$ of type $(\rho, \kappa)$ with a proper
arrangement in $\Sigma$, or 4. $\mathscr{T}^*$ controls a $K_p$-minor of $G$."

Graph Minors XVI, (6.1), pages 58 and 63, from the proved animal
step (7.1), the proper arrangement theorem (7.2), and tangle deletion. -/
theorem theorem_6_1 {S : Type w} [TopologicalSpace S] [T2Space S] (h1 : IsClosedSurface S)
    (h2 : ConnectedSpace S) (p τ χ δ φ ψ : ℕ) (h3 : 1 ≤ φ) (h4 : 1 ≤ ψ) :
    ∃ σ κ ρ ζ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (hT : IsGraphTangle G θ_star T_star),
    HasAnimal S G T_star θ_star χ δ θ σ →
    (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S') (H' : Drawing S')
      (η' : SpanEmbedding H' G) (θ_span' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))), IsClosedSurface S' ∧
      ConnectedSpace S' ∧ IsObtainedByAddingHandleOrCrosscap S S' ∧ φ ≤ θ_span' ∧
      IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨ HasAnimal S G T_star θ_star χ (δ + 1) ψ τ ∨
    (∃ (Z : Set α) (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S), Z ⊆
      V(G) ∧ Z.ncard ≤ ζ ∧ Z.ncard < θ_star ∧
      IsCentralSegregation (deleteVertices G Z)
      (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) S_seg ∧
      IsSegregationOfType (deleteVertices G Z) ρ κ S_seg ∧ IsProperArrangement S_seg α_disc α_pt) ∨
    ControlsMinor G (completeGraph p) T_star :=
  GM16.theorem_6_1_proof h1 h2 p τ χ δ φ ψ h3 h4

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (6.2)** (page 59): "Let $\Sigma$ be a surface and let $\sigma \ge 0$ be an
integer. Let $\mathcal{T}^*$ be a tangle in a graph $G$, and let $H, \mathcal{T}$ be a $\Sigma$-span
of order $\theta$. Let $\lambda \ge 2$ be an integer with $\theta \ge 4\lambda + 3$, let $\Lambda
\subseteq \Sigma$ be a $\lambda$-zone such that $H \cap (\Sigma \setminus \Lambda)$ is rigid, and
let $\mathcal{T}'$ be the tangle in $H' = H \cap (\Sigma \setminus \Lambda)$ of order $\theta -
4\lambda - 2$ which is a $(4\lambda + 2)$-compression of $\mathcal{T}$. Let $v \in V(G) \setminus
V(H)$, such that there is a horn at $v$ over $H, \mathcal{T}$ with cardinality $\sigma + 1$ and
breadth $\ge \theta$. Then there is a horn at $v$ over $H', \mathcal{T}'$ with cardinality $\sigma$
and breadth $\ge \theta - 4\lambda - 2$."

Clearing a `λ`-zone `Λ` (where `2 ≤ λ` and `4λ + 3 ≤ θ`) contains at most one end `u_i` of a horn
`{P_1, …, P_{σ+1}}` of breadth `≥ θ`, leaving a horn of cardinality `σ` and breadth
`≥ θ - 4λ - 2` over `H' = H ∩ (Σ \ Λ)` and the cleared tangle `T'`. -/
theorem theorem_6_2 {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hconn : ConnectedSpace S) {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ lam σ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (H : Drawing S) (η : SpanEmbedding H G)
    (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d d' : Set S → Set S → ℕ)
    (Λ : Set S) (v : α) (P : Fin (σ + 1) → Graph α β) (u : Fin (σ + 1) → S)
    (h1 : IsSigmaSpan G H η θ_star θ T_star T) (h2 : HasTangleMetric H θ T d) (h3 : 2 ≤ lam)
    (h4 : 4 * lam + 3 ≤ θ) (h5 : IsLambdaZone H d lam Λ) (h6 : IsRigid (clearedSubdrawing H Λ))
    (h7 : IsClearedTangle H T d θ lam Λ T' d') (h8 : IsHorn G H η d v θ (σ + 1) P u) :
    ∃ (P' : Fin σ → Graph α β) (u' : Fin σ → S),
    IsHorn G (clearedSubdrawing H Λ) (restrictCleared η Λ) d' v (θ - 4 * lam - 2) σ P' u' :=
  GM16.theorem_6_2_proof hS hconn G θ_star θ lam σ T_star H η T T' d d' Λ v P u h1 h2 h3 h4 h5 h6 h7 h8

open Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 SimpleGraph Hypergraph GraphMinor.GM10 in
/-- **Graph Minors XVI, (6.3)** (pages 59–61): "Let $\Sigma$ be a surface, and let $p, \tau, \chi
\ge 0$ and $\psi \ge 1$ be integers. Then there exists $\delta \ge 0$ and $\theta \ge 1$ such that
if $\mathcal{T}^*$ is a tangle in a graph $G$, and there is an animal with $\chi$ horns and $\delta$
hairs of strength $\ge (\theta, \tau + 1)$, then either - there is a hairless animal with $\chi + 1$
horns of strength $\ge (\psi, \tau)$, or - $\mathcal{T}^*$ controls a $K_p$-minor of $G$."

, by the two applications
of (5.3), the maximal separated hair family, and clearing the far-end
cluster. The page-60 typo concerning the vertices of `H₂` is corrected
by joining the far ends inside the smaller closed zone.

The Lean proof corrects a step of the paper's proof. See the correction to the proof of (6.3) in
`corrections/GM16.md`. -/
theorem theorem_6_3 {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) (p τ χ ψ : ℕ) (hψ : 1 ≤ ψ) :
    ∃ δ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)), IsGraphTangle G θ_star T_star →
    HasAnimal S G T_star θ_star χ δ θ (τ + 1) → HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ ∨
    ControlsMinor G (completeGraph p) T_star :=
  GM16.theorem_6_3_proof hS hConn p τ χ ψ hψ

/-! ## Section 7. The Giant Steps application -/

open Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 SimpleGraph Hypergraph GraphMinor.GM06 in
/-- **Graph Minors XVI, (7.1)** (page 62): "Let $\Sigma$ be a surface, and let $\tau, \chi, \delta,
\lambda \ge 0, \theta' \ge 1$ and $\phi, \psi \ge 3$. Then there exist $\theta \ge 1$ and $\sigma
\ge 0$ such that if $\mathcal{T}^*$ is a tangle in a graph $G$, and there is an animal with $\chi$
horns and $\delta$ hairs, of strength $\ge (\theta, \sigma)$, then either - there is a
$\Sigma'$-span of order $\ge \phi$, for some surface $\Sigma'$ obtained from $\Sigma$ by adding a
handle, or - there is an animal with $\chi$ horns and $\delta + 1$ hairs, of strength $\ge (\psi,
\tau)$, or - there exists $Z \subseteq V(G)$ with $|Z| \le \chi + \frac{1}{2}\delta^2\phi^2$ such
that some $\Sigma$-span of order $\ge \theta'$ in $G\setminus Z$ with respect to
$\mathcal{T}^*\setminus Z$ is $(\lambda, 2\psi)$-level."

Graph Minors XVI, (7.1), pages 62 and 69–70, by the complete
proof using (8.1), (8.2), and (8.3), with all horns and hairs after
clearing constructed. No statement of XVI is assumed. -/
theorem theorem_7_1 {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) (τ χ δ lam θ' φ ψ : ℕ) (hθreq : 1 ≤ θ') (hφ : 3 ≤ φ) (hψ : 3 ≤ ψ) :
    ∃ θ σ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (hT : IsGraphTangle G θ_star T_star),
    HasAnimal S G T_star θ_star χ δ θ σ →
    (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S') (H' : Drawing S')
      (η' : SpanEmbedding H' G) (θ_span' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))), IsClosedSurface S' ∧
      ConnectedSpace S' ∧ IsObtainedByAddingHandle S S' ∧ φ ≤ θ_span' ∧
      IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨ HasAnimal S G T_star θ_star χ (δ + 1) ψ τ ∨
    (∃ (Z : Set α) (H_l : Drawing S) (η_l : SpanEmbedding H_l (GM09.deleteVertices G Z)) (θ_l : ℕ)
      (T_l : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d_l : Set S → Set S → ℕ), Z ⊆
      V(G) ∧ Z.ncard ≤ χ + δ ^ 2 * φ ^ 2 / 2 ∧ Z.ncard < θ_star ∧ θ' ≤ θ_l ∧
      IsLevelSpan (GM09.deleteVertices G Z) H_l η_l (θ_star - Z.ncard) θ_l lam (2 * ψ)
      (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) T_l d_l) :=
  GM16.theorem_7_1_proof hS hConn τ χ δ lam θ' φ ψ hθreq hφ hψ

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15 GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (7.2)** (page 62): "Let $\Sigma$ be a surface and let $p, \phi, \mu \ge 0$.
Then there exist $\kappa, \lambda, \rho \ge 0$ and $\theta \ge 1$ such that if $\mathcal{T}^*$ is a
tangle in a graph $G$, and some $\Sigma$-span of order $\ge \theta$ is $(\lambda, \mu)$-level, then
either: 1. there is a $\Sigma'$-span of order $\phi$, for some surface $\Sigma'$ obtained from
$\Sigma$ by adding a crosscap, or 2. there is a $\mathcal{T}^*$-central segregation of $G$ of type
$(\rho, \kappa)$ with a proper arrangement in $\Sigma$, or 3. $\mathcal{T}^*$ controls a $K_p$ minor
of $G$."

Graph Minors XVI, (7.2), page 62. The properness omitted from the
statement of XV (8.4) is proved at the construction of its arrangements
in XV (7.7) and retained through the downward eye induction. -/
theorem theorem_7_2 {S : Type w} [TopologicalSpace S] [T2Space S] (hClosed : IsClosedSurface S)
    (hConn : ConnectedSpace S) (p φ μ : ℕ) :
    ∃ κ lam ρ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (H : Drawing S) (η : SpanEmbedding H G)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ),
    IsGraphTangle G θ_star T_star → θ ≤ θ_span → IsLevelSpan G H η θ_star θ_span lam μ T_star T d →
    (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S') (H' : Drawing S')
      (η' : SpanEmbedding H' G) (θ_span' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))), IsClosedSurface S' ∧
      ConnectedSpace S' ∧ IsObtainedByAddingCrosscap S S' ∧ φ ≤ θ_span' ∧
      IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
    (∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S),
      IsCentralSegregation G T_star S_seg ∧ IsSegregationOfType G ρ κ S_seg ∧
      IsProperArrangement S_seg α_disc α_pt) ∨ ControlsMinor G (completeGraph p) T_star :=
  GM16.theorem_7_2_proof hClosed hConn p φ μ

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (7.3)** (page 63): "Let $\mathcal{T}^*$ be a tangle in a graph $G$, let $Z
\subseteq V(G)$ with $|Z| < ord(\mathcal{T}^*)$, and let $(A, B)$ be a separation of $G$ of order $<
ord(\mathcal{T}^*) - |Z|$. Then $(A, B) \in \mathcal{T}^*$ if and only if $$(A \setminus (Z \cap
V(A)), B \setminus (Z \cap V(B))) \in \mathcal{T}^* \setminus Z.$$"

For any separation `(A, B)` of `G` of order `< θ_star - |Z|`, `(A, B) ∈ T*` if and only if
`(A \ Z, B \ Z) ∈ T* \ Z`. -/
theorem theorem_7_3 {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (hT : IsGraphTangle G θ_star T_star)
    (Z : Set α) (A B : Hypergraph α β) (hZ_sub : Z ⊆ V(G)) (hZ_lt : Z.ncard < θ_star)
    (hsep : (Hypergraph.ofGraph G hT.finite_V hT.finite_E).IsSeparation A B)
    (hord : separationOrder A B < θ_star - Z.ncard) :
    ((A, B) ∈ T_star ↔
    (A.deleteVertices (Z ∩ A.vertexSet),
      B.deleteVertices (Z ∩ B.vertexSet)) ∈ deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z
    T_star θ_star) :=
  GM16.theorem_7_3_proof G θ_star T_star hT Z A B hZ_sub hZ_lt hsep hord

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (7.4)** (page 63): "Let $\mathcal{T}^*$ be a tangle in $G$, and let $Z
\subseteq V(G)$ with $|Z| < ord(\mathcal{T}^*)$. If $H, \eta, \mathcal{T}$ is a $\Sigma$-span in $G
\setminus Z$ with respect to $\mathcal{T}^* \setminus Z$ then $H, \eta, \mathcal{T}$ is a
$\Sigma$-span in $G$ with respect to $\mathcal{T}^*$."

Every `Σ`-span in `G \ Z` with respect to `T* \ Z` is a `Σ`-span in `G` with respect to `T*`. -/
theorem theorem_7_4 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (θ_star θ : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (hT : IsGraphTangle G θ_star T_star) (Z : Set α) (H : Drawing S)
    (η : SpanEmbedding H (GM09.deleteVertices G Z))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (hZ_sub : Z ⊆ V(G))
    (hZ_lt : Z.ncard < θ_star)
    (hSpan : IsSigmaSpan (GM09.deleteVertices G Z) H η (θ_star - Z.ncard) θ
      (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) T) :
    IsSigmaSpan G H (liftSpanEmbedding η (G.induce_le sdiff_subset)) θ_star θ T_star T :=
  GM16.theorem_7_4_proof G θ_star θ T_star hT Z H η T hZ_sub hZ_lt hSpan

/-! ## Section 8. Non-Level $\Sigma$-Spans -/

open Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 SimpleGraph Hypergraph GraphMinor.GM06 GraphMinor.GM10 in
/-- **Graph Minors XVI, (8.1)** (page 64): "Let $\Sigma$ be a surface and let $\delta \ge 0$ and
$\phi, \psi \ge 3$. Then there exists $\gamma \ge 0$ and $\theta > (4\gamma + 2)\delta$ such that if
$\mathcal{T}^*$ is a tangle in a graph $G$ and $H, \mathcal{T}$ is a $\Sigma$-span of order $\ge
\theta$, and $Y \subseteq V(H)$ satisfies $|Y| = \delta$ and $d(y, y') \ge \theta$ for all distinct
$y, y' \in Y$ (where $d$ is the metric of $\mathcal{T}$), then either: 1. there is a $\Sigma'$-span
of order $\ge \phi$ for some surface $\Sigma'$ obtained from $\Sigma$ by adding a handle, or 2.
there is an $H$-path in $G$ with ends $s, t$, such that $d(s, t) \ge \psi$ and $d(s, y) \ge \psi$
for all $y \in Y$, or 3. there is a $\gamma$-envelope $(\Lambda_y\colon y \in Y)$ around $Y$, and
there exists $Z \subseteq V(G) \setminus V(H')$ with $|Z| \le \frac{1}{2}\delta^2\phi^2$, such that
$Z$ meets every $H'$-path in $G$ with ends $s, t$, satisfying $d'(s, t) \ge 2\psi$, where $H' = H
\cap (\Sigma \setminus \cup (\Lambda_y\colon y \in Y))$ and $d'$ is the metric of the $(4\gamma +
2)\delta$-compression of $\mathcal{T}$ in $H'$."

Graph Minors XVI, (8.1), with the printed statement. The proof
above also records that its chosen zone radius is at least two. -/
theorem theorem_8_1 {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) (δ φ ψ : ℕ) (hφ : 3 ≤ φ) (hψ : 3 ≤ ψ) :
    ∃ γ θ : ℕ, (4 * γ + 2) * δ < θ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (H : Drawing S) (η : SpanEmbedding H G)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (Y : Set S), θ ≤
    θ_span → IsSigmaSpan G H η θ_star θ_span T_star T → HasTangleMetric H θ_span T d → Y ⊆ H.V →
    Y.ncard = δ → (∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → θ ≤ d {y₁} {y₂}) →
    (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S') (H' : Drawing S')
      (η' : SpanEmbedding H' G) (θ_span' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))), IsObtainedByAddingHandle S S' ∧
      φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
    (∃ (P : Graph α β) (s t : S), s ∈ H.V ∧ t ∈ H.V ∧
      IsHPathWithEnds G η.imageGraph P (η.vMap s) (η.vMap t) ∧ ψ ≤ d {s} {t} ∧ ∀ y ∈ Y, ψ ≤
      d {s} {y}) ∨
    (∃ (Λ : S →
        Set S) (Z : Set α) (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S →
        Set S → ℕ), IsEnvelope H d Y γ Λ ∧ Z ⊆
      V(G) \ V((restrictCleared η (⋃ y ∈ Y, Λ y)).imageGraph) ∧ Z.ncard ≤ (δ ^ 2 * φ ^ 2) / 2 ∧
      IsSigmaSpan G (clearEnvelopeDrawing H Y Λ) (restrictCleared η (⋃ y ∈ Y,
          Λ y)) θ_star (θ_span - (4 * γ + 2) * δ) T_star T' ∧
      IsLambdaCompression H (clearEnvelopeDrawing H Y Λ) θ_span ((4 * γ + 2) * δ) T T' d d' ∧
      ∀ (P : Graph α β) (s t : S), s ∈ (clearEnvelopeDrawing H Y Λ).V →
      t ∈ (clearEnvelopeDrawing H Y Λ).V →
      IsHPathWithEnds G (restrictCleared η (⋃ y ∈ Y, Λ y)).imageGraph P (η.vMap s) (η.vMap t) →
      2 * ψ ≤ d' {s} {t} → (Z ∩ V(P)).Nonempty) :=
  GM16.theorem_8_1_proof hS hConn δ φ ψ hφ hψ

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XVI, (8.2)** (pages 64–65): "Let $\mathcal{T}^*$ be a tangle in a graph $G$, and
let $H, \mathcal{T}$ be a $\Sigma$-span. Let $Z \subseteq V(G) \setminus V(H)$ with $|Z| <
ord(\mathcal{T})$, let $1 \le \theta' \le ord(\mathcal{T}) - |Z|$, and let $\mathcal{T}'$ be the
truncation of $\mathcal{T}$ to order $\theta'$. Then $H, \mathcal{T}'$ is a $\Sigma$-span in $G
\setminus Z$ with respect to $\mathcal{T}^* \setminus Z$."

If `H, η, T` is a `Σ`-span of order `θ` in `G` with respect to `T*`, `Z ⊆ V(G) \ V(η(H))` has
`|Z| < θ`, and `1 ≤ θ' ≤ θ - |Z|`, then the truncation `GM10.truncation T θ'` is a `Σ`-span in
`G \ Z` with respect to `T* \ Z`. -/
theorem theorem_8_2 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (θ_star θ θ' : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (H : Drawing S) (η : SpanEmbedding H G) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (Z : Set α) (hSpan : IsSigmaSpan G H η θ_star θ T_star T) (h1 : Z ⊆ V(G))
    (hZ_disj : Disjoint V(η.imageGraph) Z) (h2 : Z.ncard < θ) (h3 : 1 ≤ θ') (h4 : θ' ≤ θ - Z.ncard) :
    IsSigmaSpan (GM09.deleteVertices G Z) H (restrictDeleteVertices η Z hZ_disj) (θ_star - Z.ncard)
    θ'
    (deleteGraphVerticesTangle G hSpan.isControlling.isTangle_star.finite_V
      hSpan.isControlling.isTangle_star.finite_E Z T_star θ_star) (GM10.truncation T θ') :=
  GM16.theorem_8_2_proof G θ_star θ θ' T_star H η T Z hSpan h1 hZ_disj h2 h3 h4

open Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 SimpleGraph Hypergraph GraphMinor.GM06 GraphMinor.GM10 in
/-- **Graph Minors XVI, (8.3)** (page 65): "Let $\Sigma$ be a surface, and let $\tau, \chi, \delta,
\lambda, \zeta \ge 0$ and $\psi \ge 3$. Then there exists $\theta > \zeta$ such that if
$\mathcal{T}^*$ is a tangle in a graph $G$, and $(H, \mathcal{T}, X, Y)$ is an animal with $\chi$
horns and $\delta$ hairs, of strength $\ge (\theta, \zeta + \tau)$, and $Z \subseteq V(G) \setminus
V(H)$ with $X \subseteq Z$ and $|Z| \le \zeta$, then either: - there is an animal with $\chi$ horns
and $\delta + 1$ hairs of strength $\ge (\psi, \tau)$, or - there is an $H$-path in $G \setminus Z$
with ends $s_1, s_2$ and there are distinct $y_1, y_2 \in Y$ with $d(s_1, y_1), d(s_2, y_2) < \psi$,
where $d$ is the metric of $\mathcal{T}$, or - $H, \mathcal{T}_0$ is a $(\lambda, 2\psi)$-level
$\Sigma$-span of order $\theta - |Z|$ in $G \setminus Z$ with respect to $\mathcal{T}^* \setminus
Z$, where $\mathcal{T}_0$ is the truncation of $\mathcal{T}$ to order $\theta - |Z|$."

Graph Minors XVI, (8.3), with its printed statement. The strengthened
proof also permits any prescribed lower bound on the chosen threshold,
as used in the proof of (7.1) on page 69. -/
theorem theorem_8_3 {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) (τ χ δ lam ζ ψ : ℕ) (hψ : 3 ≤ ψ) :
    ∃ θ : ℕ, ζ < θ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (H : Drawing S) (η : SpanEmbedding H G)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S →
      ℕ) (X : Set α) (Y : Set S) (Z : Set α)
    (hAnim : IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ (ζ + τ)) (_ : Z ⊆
      V(G)) (hZ_disj : Disjoint V(η.imageGraph) Z) (_ : X ⊆ Z) (_ : Z.ncard ≤ ζ),
    HasAnimal S G T_star θ_star χ (δ + 1) ψ τ ∨
    (∃ (P : Graph α β) (s₁ s₂ y₁ y₂ : S), s₁ ∈ H.V ∧ s₂ ∈ H.V ∧ y₁ ∈ Y ∧ y₂ ∈ Y ∧ y₁ ≠ y₂ ∧
      IsHPathWithEnds (GM09.deleteVertices G Z) η.imageGraph P (η.vMap s₁) (η.vMap s₂) ∧
      d {s₁} {y₁} < ψ ∧ d {s₂} {y₂} < ψ) ∨
    (∃ d₀ : Set S → Set S → ℕ,
      IsLevelSpan (GM09.deleteVertices G Z) H (restrictDeleteVertices η Z hZ_disj)
      (θ_star - Z.ncard) (θ - Z.ncard) lam (2 * ψ)
      (deleteGraphVerticesTangle G hAnim.2.2.1.isControlling.isTangle_star.finite_V
        hAnim.2.2.1.isControlling.isTangle_star.finite_E Z T_star θ_star)
      (GM10.truncation T (θ - Z.ncard)) d₀) :=
  GM16.theorem_8_3_proof hS hConn τ χ δ lam ζ ψ hψ

/-! ## Section 9. The main proof -/

end GraphMinor.GM16
