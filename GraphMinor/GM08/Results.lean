module

public import GraphMinor.GM06.DualExists
public import GraphMinor.GM07.CylinderGrid
public import GraphMinor.GM07.Defs
public import GraphMinor.GM07.DiscChain
public import GraphMinor.GM08.Defs
public import GraphMinor.GM08.Defs6to18
public import GraphMinor.GM08.Section1
public import GraphMinor.GM08.Section11Data
public import GraphMinor.GM08.Section11Ring
public import GraphMinor.GM08.Section13
public import GraphMinor.GM08.Section14
public import GraphMinor.GM08.Section14Chain
public import GraphMinor.GM08.Section14Sim
public import GraphMinor.GM08.Section15
public import GraphMinor.GM08.Section15Printed
public import GraphMinor.GM08.Section15PrintedCases
public import GraphMinor.GM08.Section15PrintedConcat
public import GraphMinor.GM08.Section16Defs
public import GraphMinor.GM08.Section16PrintedDefs
public import GraphMinor.GM08.Section17Defs
public import GraphMinor.GM08.Section18CircleTouch
public import GraphMinor.GM08.Section18CutStep
public import GraphMinor.GM08.Section18LeafDrawing
public import GraphMinor.GM08.Section18Minor
public import GraphMinor.GM08.Section18Reduction
public import GraphMinor.GM08.Section18Universes
public import GraphMinor.GM08.Section18X2Cut
public import GraphMinor.GM08.Section2Surface
public import GraphMinor.GM08.Section3
public import GraphMinor.GM08.Section4
public import GraphMinor.GM08.Section7Model
public import GraphMinor.GM08.Section8Cut
public import GraphMinor.GM08.Section8Defs
public import GraphMinor.GM08.Section8Sleeve
public import GraphMinor.GM08.Section9
public import GraphMinor.GM11.OArcCircuit
public import GraphMinor.GM12.Section3AmbientTransfer
public import GraphMinor.GM12.Section3MeetingDiscs
public import GraphMinor.GM12.Section3SubgraphDrawing
public import GraphMinor.Surface.Defs
public import Mathlib.Combinatorics.Graph.Lattice
import GraphMinor.GM08.Section10
import GraphMinor.GM08.Section1Proof
import GraphMinor.GM08.Section11
import GraphMinor.GM08.Section11b
import GraphMinor.GM08.Section15Conclusion
import GraphMinor.GM08.Section15PrintedFinal
import GraphMinor.GM08.Section16
import GraphMinor.GM08.Section16Conclusion
import GraphMinor.GM08.Section17
import GraphMinor.GM08.Section18Closed
import GraphMinor.GM08.Section18ClosedGraft
import GraphMinor.GM08.Section18Leaf
import GraphMinor.GM08.Section18Main
import GraphMinor.GM08.Section18OneCuff
import GraphMinor.GM08.Section18PinchedDisc
import GraphMinor.GM08.Section18Rootless
import GraphMinor.GM08.Section2
import GraphMinor.GM08.Section2Valency
import GraphMinor.GM08.Section6
import GraphMinor.GM08.Section7
import GraphMinor.GM08.Section8
public import GraphMinor.GM08.Section9Boundary
import GraphMinor.GM08.Section9Conclusion
import GraphMinor.GM08.Section9Simulation
import GraphMinor.GM08.Section9Width

/-!
# Graph Minors VIII. A Kuratowski theorem for general surfaces

N. Robertson and P. D. Seymour, J. Combin. Theory Ser. B 48 (1990) 255–288.

This file lists every numbered result of the paper in order. The proofs are in the other
files of this folder and, for algorithms, in `GraphMinor/Compute/`. The errors of the paper, and how
the Lean statements and proofs correct them, are listed in `corrections/GM08.md`.
-/

public section

namespace GraphMinor.GM08

/-! ## Section 1. INTRODUCTION -/

section

open Set Function Topology Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VIII, (1.1)** (page 256):
"(1.1) *For any number $g$, every antichain of graphs all of genus $\le g$ is finite.*"
The proof is the paper's (page 257): finitely many surfaces carry every graph of genus at most
$g$, and (1.2) applies to each. -/
theorem theorem_1_1 {α : Type u} {β : Type v} (g : ℕ)
    {A : Set (Graph α β)} (hA : IsGraphAntichain A)
    (_hGenus : ∀ G ∈ A, graphGenus G ≤ g) :
    A.Finite := by exact GraphMinor.GM08.theorem_1_1_proof g hA _hGenus

end

section

open Set Function Topology Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VIII, (1.2)** (page 257):
"(1.2) *For any surface $\Sigma$, every antichain whose members can all be drawn in $\Sigma$ is
finite.*"
The proof is the paper's: (1.2) is the case of (6.1) with index zero (page 263). -/
theorem theorem_1_2 {α : Type u} {β : Type v} (S : Type w) [TopologicalSpace S]
    (_hS : IsSurface S) {A : Set (Graph α β)}
    (hA : IsGraphAntichain A) (_hDraw : ∀ G ∈ A, GM16.CanBeDrawnIn S G) :
    A.Finite := by exact GraphMinor.GM08.theorem_1_2_proof S _hS hA _hDraw

end

/-! ## Section 2. ERDŐS' PROBLEM IN MINORS -/

section

open Graph Set Relation

universe u v u' v' u'' v'' w

/-- **(2.1)** (Graph Minors VIII, Section 2, page 257):
"(2.1) *For any hereditary property $P$, $T(P)$ is finite up to isomorphism if and only if $S(P)$
is finite up to isomorphism.*" -/
theorem theorem_2_1 {α : Type u} {β : Type v} {P : Set (Graph α β)}
    (hP : IsHereditaryProperty P) :
    IsFiniteUpToIso (topMinimalOut P) ↔ IsFiniteUpToIso (minorMinimalOut P) := by exact GraphMinor.GM08.theorem_2_1_proof hP

end

section

open Graph Set Relation

universe u v u' v' u'' v'' w

/-- **(2.2)** (Graph Minors VIII, Section 2, page 258):
"(2.2) *If $H$ is a minor of $G$, there is a graph $H'$ which can be obtained from $H$ by splitting
vertices and which is topologically contained in $G$.*" -/
theorem theorem_2_2 {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'}
    (hfin : IsFiniteGraph G) (hmin : IsIsoMinor H G) :
    ∃ H' : Graph α β, ObtainedBySplittingVertices H' H ∧ IsTopologicallyContained H' G := by exact GraphMinor.GM08.theorem_2_2_proof hfin hmin

end

section

open Set Function Relation Graph

universe u v u' v'

/-- **Graph Minors VIII, (2.3)** (page 259):
"(2.3) *For any graph $H$, $Z(H)$ is finite up to isomorphism.*" -/
theorem theorem_2_3 {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} (hH : IsFiniteGraph H) :
    IsFiniteUpToIso (splitClass H : Set (Graph α β)) := by exact GraphMinor.GM08.theorem_2_3_proof hH

end

/-! ## Section 3. Well-Quasi-Orders -/

section

open Set Function Relation

universe u v

/-- **Graph Minors VIII, (3.1)** (page 259):
"(3.1) *If $\mathbf{Q} = (Q, \le)$ is a well-quasi-order then every countable sequence
$q_1, q_2, \dots$ of members of $Q$ has a countable subsequence $q_{i_1}, q_{i_2}, \dots$ (where
$i_1 < i_2 < \dots$) such that $q_{i_1} \le q_{i_2} \le \dots$.*" -/
theorem theorem_3_1 {Q : Type u} {le : Q → Q → Prop}
    (hQ : IsWellQuasiOrder le) (q : ℕ → Q) :
    ∃ φ : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → le (q (φ m)) (q (φ n)) := by exact GraphMinor.GM08.theorem_3_1_proof hQ q

end

section

open Set Function Relation

universe u v

/-- **Graph Minors VIII, (3.2)** (page 260):
"(3.2) *If $\mathbf{Q}_1$ and $\mathbf{Q}_2$ are well-quasi-orders, so is
$\mathbf{Q}_1 \times \mathbf{Q}_2$.*" -/
theorem theorem_3_2 {Q₁ : Type u} {Q₂ : Type v}
    {le₁ : Q₁ → Q₁ → Prop} {le₂ : Q₂ → Q₂ → Prop}
    (hQ₁ : IsWellQuasiOrder le₁) (hQ₂ : IsWellQuasiOrder le₂) :
    IsWellQuasiOrder (prodLE le₁ le₂) := by exact GraphMinor.GM08.theorem_3_2_proof hQ₁ hQ₂

end

section

open Set Function Relation

universe u v

/-- **Graph Minors VIII, (3.3)** (page 260, Higman's lemma):
"(3.3) *If $\mathbf{Q}$ is a well-quasi-order then so is $\mathbf{Q}^{<\omega}$.*" -/
theorem theorem_3_3 {Q : Type u} {le : Q → Q → Prop}
    (hQ : IsWellQuasiOrder le) :
    IsWellQuasiOrder (seqLE le) := by exact GraphMinor.GM08.theorem_3_3_proof hQ

end

/-! ## Section 4. Grafts -/

section

open Set Function Relation Graph

universe u v u' v' u'' v''

/-- **Graph Minors VIII, (4.1)** (page 260):
"If $\mathscr{A}$ is well-rooted then it has an index."

**Graph Minors VIII, (4.1)** (page 260): -/
theorem theorem_4_1 {α : Type u} {β : Type v} {𝒜 : Set (Graft α β)}
    (h𝒜 : IsWellRootedGraftClass 𝒜) :
    HasGraftClassIndex 𝒜 := by exact GraphMinor.GM08.theorem_4_1_proof h𝒜

end

section

open Set Function Relation Graph

universe u v u' v' u'' v''

/-- **Graph Minors VIII, (4.2)** (page 261):
"(4.2) *If $\mathscr{A}_1, \mathscr{A}_2$ are well-rooted then so is
$\mathscr{A}_1 \cup \mathscr{A}_2$.*" -/
theorem theorem_4_2 {α : Type u} {β : Type v} {𝒜₁ 𝒜₂ : Set (Graft α β)}
    (h₁ : IsWellRootedGraftClass 𝒜₁) (h₂ : IsWellRootedGraftClass 𝒜₂) :
    IsWellRootedGraftClass (𝒜₁ ∪ 𝒜₂) := by exact GraphMinor.GM08.theorem_4_2_proof h₁ h₂

end

section

open Set Function Relation Graph

universe u v u' v' u'' v''

/-- **Graph Minors VIII, (4.3)** (page 261):
"(4.3) *Let $\mathscr{A}$ be a well-rooted class of grafts, and let $\mathscr{B}$ be a class of
rooted graphs of bounded index, such that for each member of $\mathscr{B}$, its underlying graft is
in $\mathscr{A}$. Then $\mathscr{B}$ is well-rooted.*" -/
theorem theorem_4_3 {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {ℬ : Set (RootedGraph α β)}
    (h𝒜 : IsWellRootedGraftClass 𝒜)
    (hB_idx : HasBoundedRootedGraphIndex ℬ)
    (hB_graft : ∀ X ∈ ℬ, X.toGraft ∈ 𝒜) :
    IsWellRootedRootedGraphClass ℬ := by exact GraphMinor.GM08.theorem_4_3_proof h𝒜 hB_idx hB_graft

end

/-! ## Section 5. Drawings of Grafts -/

/-! ## Section 6. Foundations on a Disc -/

section

open Set GraphMinor.Surface

universe u v w u' v'

/-- **Graph Minors VIII, (6.1)** (page 263):
"If $\mathcal{A}$ is a class of graphs with bounded index, and some surface $\Sigma$ embeds $\mathcal{A}$, then $\mathcal{A}$ is well-rooted."

**VIII (6.1)**, page 263: if `𝒜` is a class of grafts with bounded index,
and some surface embeds `𝒜`, then `𝒜` is well-rooted. -/
theorem theorem_6_1 :
  ∀ (α : Type u) (β : Type v) (𝒜 : Set (Graft α β)), HasGraftClassIndex 𝒜 →
    (∃ (S : Type w) (_ : TopologicalSpace S), IsSurface S ∧ EmbedsGraftClass S 𝒜) →
    IsWellRootedGraftClass 𝒜 := by exact GraphMinor.GM08.theorem_6_1_proof

end

section

open Set Topology Surface

universe u

/-- **Graph Minors VIII, (6.2)** (page 264):
"Let $\Sigma$ be a sphere and let $F_1, F_2$ be $O$-arcs of $\Sigma$ with $|F_1 \cap F_2| \ge 2$. Let $z \in \Sigma - (F_1 \cup F_2)$. Then there is an $O$-arc $F_3 \subseteq F_1 \cup F_2$ such that the component of $\Sigma - F_3$ which contains $z$ contains no point of $F_1 \cup F_2$."

**(6.2)** Let `S` be a sphere and let `F₁, F₂` be O-arcs of `S` with `|F₁ ∩ F₂| ≥ 2`.
Let `z ∈ S - (F₁ ∪ F₂)`. Then there is an O-arc `F₃ ⊆ F₁ ∪ F₂` such that the component of
`S - F₃` which contains `z` contains no point of `F₁ ∪ F₂`.
(GM VIII Section 6, page 264.) -/
theorem theorem_6_2 {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {F₁ F₂ : Set S} (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂)
    (hcard : (F₁ ∩ F₂).Nontrivial)
    {z : S} (hz : z ∉ F₁ ∪ F₂) :
    ∃ F₃ : Set S, IsOArc F₃ ∧ F₃ ⊆ F₁ ∪ F₂ ∧
      Disjoint (connectedComponentIn (F₃ᶜ) z) (F₁ ∪ F₂) := by exact GraphMinor.GM08.theorem_6_2_proof hS hsph hF₁ hF₂ hcard hz

end

section

open Set Topology Surface

universe u

/-- **Graph Minors VIII, (6.3)** (page 264):
"Let $\Sigma$ be a sphere and let $F_1, F_2$ be $O$-arcs in $\Sigma$. Let $z_1, z_2 \in \Sigma - (F_1 \cup F_2)$, and be in distinct components of $\Sigma - F_i$ ($i = 1, 2$). Then there are $O$-arcs $F_3, F_4$ in $\Sigma$ such that"

**(6.3)** Let `S` be a sphere and let `F₁, F₂` be O-arcs in `S`. Let `z₁, z₂ ∈ S - (F₁ ∪ F₂)`,
and be in distinct components of `S - Fᵢ` (`i = 1, 2`). Then there are O-arcs `F₃, F₄` in `S` such
that
(i) `F₃ ∪ F₄ ⊆ F₁ ∪ F₂`, `F₃ ∩ F₄ ⊆ F₁ ∩ F₂`,
(ii) the component of `S - F₃` which contains `z₁` contains no point of `F₁ ∪ F₂`,
(iii) the component of `S - F₄` which contains `z₂` contains no point of `F₁ ∪ F₂`.
(GM VIII Section 6, page 264.) -/
theorem theorem_6_3 {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {F₁ F₂ : Set S} (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂)
    {z₁ z₂ : S} (hz₁ : z₁ ∉ F₁ ∪ F₂) (hz₂ : z₂ ∉ F₁ ∪ F₂)
    (hsep₁ : connectedComponentIn (F₁ᶜ) z₁ ≠ connectedComponentIn (F₁ᶜ) z₂)
    (hsep₂ : connectedComponentIn (F₂ᶜ) z₁ ≠ connectedComponentIn (F₂ᶜ) z₂) :
    ∃ F₃ F₄ : Set S, IsOArc F₃ ∧ IsOArc F₄ ∧
      F₃ ∪ F₄ ⊆ F₁ ∪ F₂ ∧ F₃ ∩ F₄ ⊆ F₁ ∩ F₂ ∧
      Disjoint (connectedComponentIn (F₃ᶜ) z₁) (F₁ ∪ F₂) ∧
      Disjoint (connectedComponentIn (F₄ᶜ) z₂) (F₁ ∪ F₂) := by exact GraphMinor.GM08.theorem_6_3_proof hS hsph hF₁ hF₂ hz₁ hz₂ hsep₁ hsep₂

end

section

open Set Topology Surface

universe u

/-- **Graph Minors VIII, (6.4)** (page 264):
"Let $\Gamma$ be a drawing in a disc $\Sigma$, and let $C_1, C_2$ be circuits of $\Gamma$. Let $F_i$ be a $C_i$-ring ($i = 1, 2$), such that some point of $C_1$ is inside $F_2$, and no point of $F_2$ is inside $C_1$. Then there is a $C_1$-ring enclosed by both $F_1$ and $F_2$."

**(6.4)** Let `D` be a drawing in a disc `Δ`, and let `C₁, C₂` be circuits of `D`.
Let `Fᵢ` be a `Cᵢ`-ring (`i = 1, 2`), such that some point of `C₁` is inside `F₂`, and no point
of `F₂` is inside `C₁`. Then there is a `C₁`-ring enclosed by both `F₁` and `F₂`.
(GM VIII Section 6, page 264.) -/
theorem theorem_6_4 {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {C₁ C₂ : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hF₁ : IsCRing C₁ F₁) (hF₂ : IsCRing C₂ F₂)
    (hin : ∃ x ∈ C₁.U, InsideOArc Δ F₂ x)
    (hout : ∀ x ∈ F₂, ¬ InsideOArc Δ C₁.U x) :
    ∃ F₃ : Set S, IsCRing C₁ F₃ ∧ OArcEncloses Δ F₁ F₃ ∧ OArcEncloses Δ F₂ F₃ := by exact GraphMinor.GM08.theorem_6_4_proof hΔ hF₁ hF₂ hin hout

end

section

open Set Topology Surface

universe u

/-- **Graph Minors VIII, (6.5)** (page 265):
"Let $\Gamma$ be a drawing in a disc $\Sigma$, and let $C_1, C_2$ be circuits of $\Gamma$. Let $F_i$ be a $C_i$-ring ($i = 1, 2$), such that $F_1$ and $C_2$ bound disjoint open discs, and $F_2$ and $C_1$ bound disjoint open discs. Then there is a $C_1$-ring $F_3$ and a $C_2$-ring $F_4$ such that $F_1$ encloses $F_3$, $F_2$ encloses $F_4$, and $F_3$ and $F_4$ bound disjoint open discs."

**(6.5)** Let `D` be a drawing in a disc `Δ`, and let `C₁, C₂` be circuits of `D`.
Let `Fᵢ` be a `Cᵢ`-ring (`i = 1, 2`), such that `F₁` and `C₂` bound disjoint open discs, and
`F₂` and `C₁` bound disjoint open discs. Then there is a `C₁`-ring `F₃` and a `C₂`-ring `F₄`
such that `F₁` encloses `F₃`, `F₂` encloses `F₄`, and `F₃` and `F₄` bound disjoint open discs.
(GM VIII Section 6, page 265.) -/
theorem theorem_6_5 {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {C₁ C₂ : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hF₁ : IsCRing C₁ F₁) (hF₂ : IsCRing C₂ F₂)
    (hdis₁ : BoundDisjointOpenDiscs Δ F₁ C₂.U)
    (hdis₂ : BoundDisjointOpenDiscs Δ F₂ C₁.U) :
    ∃ F₃ F₄ : Set S, IsCRing C₁ F₃ ∧ IsCRing C₂ F₄ ∧
      OArcEncloses Δ F₁ F₃ ∧ OArcEncloses Δ F₂ F₄ ∧
      BoundDisjointOpenDiscs Δ F₃ F₄ := by exact GraphMinor.GM08.theorem_6_5_proof hΔ hF₁ hF₂ hdis₁ hdis₂

end

section

open Set Topology Surface

universe u

/-- **Graph Minors VIII, (6.6)** (page 266):
"Let $\Gamma$ be a drawing in a disc $\Sigma$, and let $C$ be a circuit of $\Gamma$. If $F_1, F_2$ are minimal $C$-rings then $\Gamma(F_1) = \Gamma(F_2)$."

**(6.6)** Let `D` be a drawing in a disc `Δ`, and let `C` be a circuit of `D`.
If `F₁, F₂` are minimal `C`-rings then `Γ(F₁) = Γ(F₂)`.
(GM VIII Section 6, page 266.) -/
theorem theorem_6_6 {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {C : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hF₁ : IsMinimalCRing C F₁) (hF₂ : IsMinimalCRing C F₂) :
    edgesInsideOArc D Δ F₁ = edgesInsideOArc D Δ F₂ := by exact GraphMinor.GM08.theorem_6_6_proof hΔ hF₁ hF₂

end

section

open Set Topology Surface

universe u

/-- **Graph Minors VIII, (6.7)** (page 266):
"Let $\Gamma$ be a drawing in a disc $\Sigma$, and let $C_1, C_2$ be bosses. Then either $\Delta(C_1) \subseteq \Delta(C_2)$, or $\Delta(C_2) \subseteq \Delta(C_1)$, or $\Delta(C_1) \cap \Delta(C_2) = \emptyset$."

**(6.7)** Let `D` be a drawing in a disc `Δ`, and let `C₁, C₂` be bosses.
Then either `Δ(C₁) ⊆ Δ(C₂)`, or `Δ(C₂) ⊆ Δ(C₁)`, or `Δ(C₁) ∩ Δ(C₂) = ∅`.
(GM VIII Section 6, page 266.) -/
theorem theorem_6_7 {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {C₁ C₂ : DiscCircuit D Δ}
    (hB₁ : IsBoss D Δ C₁) (hB₂ : IsBoss D Δ C₂) :
    bossDelta D Δ C₁ ⊆ bossDelta D Δ C₂ ∨
      bossDelta D Δ C₂ ⊆ bossDelta D Δ C₁ ∨
      Disjoint (bossDelta D Δ C₁) (bossDelta D Δ C₂) := by exact GraphMinor.GM08.theorem_6_7_proof hΔ hB₁ hB₂

end

/-! ## Section 7. Tree-Width -/

section

open Set Function Topology Graph SimpleGraph Surface GM11

/-- **(7.1)** (Graph Minors VIII, Section 7, page 267):
"Let $r, s \ge 0$ be integers. Then there is an integer $w$ such that every drawing in a disc
with no $(r, s)$-nest has tree-width $\le w$." -/
theorem theorem_7_1 (r s : ℕ) :
    ∃ w : ℕ, ∀ {S : Type*} [TopologicalSpace S] (D : Drawing S) (Δ : Set S),
      IsClosedDisc Δ → D.U ⊆ Δ → IsEmpty (DrawingNest D Δ r s) → DrawingTreeWidthLE D w := by exact GraphMinor.GM08.theorem_7_1_proof r s

end

/-! ## Section 8. Centred O-Arcs -/

section

open Set Function Topology Graph
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM07 GraphMinor.GM09.PlanarNests

universe u

/-- **Graph Minors VIII, (8.1)** (page 268):
"If $F$ is centred, there is a $(r, s)$-nest $(C_1, \dots, C_s)$ (where $r, s$ are as above) such that each $C_i$ is inside $F$, and there are $r$ mutually disjoint paths $P_1, \dots, P_r$ of $\Gamma$ between $C_1$ and $F$, such that the intersection of each $P_i$ and each $C_j$ is a path."

**(8.1)** *If $F$ is centred, there is a $(r, s)$-nest $(C_1, \dots, C_s)$ (where $r, s$ are as
above) such that each $C_i$ is inside $F$, and there are $r$ mutually disjoint paths $P_1, \dots, P_r$
of $\Gamma$ between $C_1$ and $F$, such that the intersection of each $P_i$ and each $C_j$ is a path.*
(GM VIII Section 8, page 268.) -/
theorem theorem_8_1 {S : Type u} [TopologicalSpace S] {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hc : IsCentredOArc D Δ F) :
    Nonempty (SleeveData D Δ F) := by exact GraphMinor.GM08.theorem_8_1_proof hΔ hDU hc

end

section

open Set Function Topology Graph
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM07 GraphMinor.GM09.PlanarNests

universe u

/-- **Graph Minors VIII, (8.2)** (page 268):
"If $C$ is a boss of $\Gamma$ then every $C$-ring is centred."

**(8.2)** *If $C$ is a boss of $\Gamma$ then every $C$-ring is centred.*
(GM VIII Section 8, page 268.) -/
theorem theorem_8_2 {S : Type u} [TopologicalSpace S] {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hprop : D.IsNormal (discBd Δ))
    {C : DiscCircuit D Δ} (hboss : IsBoss D Δ C) (hF : IsCRing C F) :
    IsCentredOArc D Δ F := by exact GraphMinor.GM08.theorem_8_2_proof hΔ hDU hprop hboss hF

end

section

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM07

universe u

/-- **Graph Minors VIII, (8.3)** (page 268):
"Let $F$ be a $\Gamma$-normal centred $O$-arc. Let $I$ be a $\Gamma$-normal $[0, 1]$-arc with ends in $F$ and with all its other points inside $F$. Then
$$|I \cap V(\Gamma)| \ge \min(|F_1 \cap V(\Gamma)|, |F_2 \cap V(\Gamma)|),$$
where $F_1, F_2$ are the closures of the two components into which the ends of $I$ divide $F$."

**(8.3)** *Let $F$ be a $\Gamma$-normal centred $O$-arc. Let $I$ be a $\Gamma$-normal $[0, 1]$-arc with ends in $F$ and with all its other points inside $F$. Then*
$$|I \cap V(\Gamma)| \ge \min(|F_1 \cap V(\Gamma)|, |F_2 \cap V(\Gamma)|),$$
*where $F_1, F_2$ are the closures of the two components into which the ends of $I$ divide $F$.*
(GM VIII Section 8, page 268.) -/
theorem theorem_8_3 {S : Type u} [TopologicalSpace S] {D : Drawing S} {Δ F I : Set S}
    {a b : S} {A₁ A₂ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (hc : IsCentredOArc D Δ F)
    (hInorm : D.IsNormal I) (hIline : IsLineWithEnds I a b)
    (haF : a ∈ F) (hbF : b ∈ F)
    (hIin : SetInsideOArc Δ F (I \ {a, b}))
    (hcomp : componentsIn (F \ {a, b}) = {A₁, A₂}) (hAne : A₁ ≠ A₂) :
    min (closure A₁ ∩ D.V).ncard (closure A₂ ∩ D.V).ncard ≤ (I ∩ D.V).ncard := by exact GraphMinor.GM08.theorem_8_3_proof hΔ hDU hc hInorm hIline haF hbF hIin hcomp hAne

end

section

open Set Function Topology Graph
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM06 GraphMinor.GM07

universe u

/-- **(8.4)** (Graph Minors VIII, Section 8, page 269):
"Let $F$ be a $\Gamma$-normal centred $O$-arc and let $\Xi$ be a drawing of a forest in $\Sigma$,
such that $U(\Xi) \cap F \subseteq V(\Gamma)$, and $U(\Xi)$ is enclosed by $F$. Then $\Gamma$ has
a subdrawing $\Xi'$, which is a drawing of a forest, with $U(\Xi')$ enclosed by $F$, such that for
all $u, v \in V(\Gamma) \cap F$, there is a component of $\Xi$ containing both $u$ and $v$ if and
only if there is a component of $\Xi'$ containing them both." -/
theorem theorem_8_4 {S : Type u} [TopologicalSpace S] {D Ξ : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (hc : IsCentredOArc D Δ F)
    (hΞforest : IsGraphForest Ξ.toGraph)
    (hΞF : Ξ.U ∩ F ⊆ D.V)
    (hΞenc : OArcEncloses Δ F Ξ.U) :
    ∃ Ξ' : Drawing S,
      Ξ'.IsSubdrawing D ∧ IsGraphForest Ξ'.toGraph ∧ OArcEncloses Δ F Ξ'.U ∧
      ∀ u ∈ D.V ∩ F, ∀ v ∈ D.V ∩ F,
        (∃ C, GM06.IsGraphComponent C Ξ.toGraph ∧ u ∈ V(C) ∧ v ∈ V(C)) ↔
          (∃ C', GM06.IsGraphComponent C' Ξ'.toGraph ∧ u ∈ V(C') ∧ v ∈ V(C')) := by exact GraphMinor.GM08.theorem_8_4_proof hΔ hDU hc hΞforest hΞF hΞenc

end

/-! ## Section 9. Boundary-Linked Nests -/

section

open Set Topology Surface

universe u

/-- **Graph Minors VIII, (9.1)** (page 269):
"Let $\Gamma^$ be a truncation of $\Gamma$, and let $r, s$ be integers with $r, s \ge k$. Every $(r, s)$-nest of $\Gamma^$ is boundary-linked in $\Gamma$."

Graph Minors VIII, (9.1), pages 269–270: every `(r,s)`-nest of a
truncation is boundary-linked in the original drawing when `r,s ≥ k`.
Properness is part of the paper's drawing definition, Section 5(iii), page 262.
The sleeve contradiction uses a corrected count of enclosed circuits.

The proof keeps enough enclosed circuits to cover the one-circuit sleeve case. See the correction to
the proof of (9.1) in `corrections/GM08.md`. -/
theorem theorem_9_1 {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) {D Dstar : Drawing S} (hprop : D.IsProper)
    (htrunc : IsTruncation D univ Dstar) {r s : ℕ}
    (hr : (D.V ∩ discBd (univ : Set S)).ncard ≤ r)
    (hs : (D.V ∩ discBd (univ : Set S)).ncard ≤ s) (N : DrawingNest Dstar univ r s) :
    IsBoundaryLinkedNest D univ (N.ofSubdrawing htrunc.isSubdrawing) := by exact GraphMinor.GM08.theorem_9_1_proof hS hprop htrunc hr hs N

end

section

open Set Surface

universe u

/-- **Graph Minors VIII, (9.2)** (page 270):
"If $r, s \ge k$ there is a number $N$ such that for any drawing $\Gamma$ with $|V(\Gamma) \cap bd\ \Sigma| = k$, if $\Gamma$ has no boundary-linked $(r, s)$-nest, then every truncation $\Gamma^$ has tree-width $\le N$."

Graph Minors VIII, (9.2), page 270: when `r,s ≥ k`, drawings without a
boundary-linked `(r,s)`-nest have all truncations of bounded tree-width.
Properness is the drawing condition of Section 5(iii), page 262. -/
theorem theorem_9_2 (k r s : ℕ) (hr : k ≤ r) (hs : k ≤ s) :
    ∃ w : ℕ, ∀ {S : Type u} [TopologicalSpace S] (_hS : IsClosedDisc (univ : Set S))
      (D : Drawing S), D.IsProper → (D.V ∩ discBd (univ : Set S)).ncard = k →
      (∀ N : DrawingNest D univ r s, ¬ IsBoundaryLinkedNest D univ N) →
      ∀ Dstar : Drawing S, IsTruncation D univ Dstar → DrawingTreeWidthLE Dstar w := by exact GraphMinor.GM08.theorem_9_2_proof k r s hr hs

end

section

open Set Surface Graph

universe u v u' v' w

/-- **Graph Minors VIII, (9.3)** (page 270):
"Let $(H, U)$ be a graft which embeds in a disc $\Sigma$, with $|U| = k$. Then there are integers $r, s \ge k$ such that for every graft $(G, T)$ with $|T| = k$, if $(G, T)$ has a drawing in $\Sigma$ with a boundary-linked $(r, s)$-nest, then $(H, U)$ is simulated in $(G, T)$."

Graph Minors VIII, (9.3), page 270: a sufficiently large
boundary-linked nest simulates any fixed disc-embeddable graft of the
same index. The proof applies Graph Minors VII (9.4). -/
theorem theorem_9_3 {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'} {S : Type w} [TopologicalSpace S]
    (hΔ : IsClosedDisc (univ : Set S)) (Y : Graft α β) (hY : EmbedsGraft S Y) :
    ∃ r s : ℕ, Y.index ≤ r ∧ Y.index ≤ s ∧
      ∀ (X : Graft α' β') (_hX : X.index = Y.index)
        (gd : GraftDrawing X.G X.T S) (N : DrawingNest gd.drawing univ r s),
        IsBoundaryLinkedNest gd.drawing univ N → IsGraftSimulatedIn Y X := by exact GraphMinor.GM08.theorem_9_3_proof hΔ Y hY

end

section

open Set Surface

universe u v u' v' w

/-- **Graph Minors VIII, (9.4)** (page 270):
"Let $(H, U)$ be a graft which embeds in a disc $\Sigma$ with $|U| = k$. Then there is a number $w$ such that for every graft $(G, T)$ with $|T| = k$, if $(H, U)$ is not simulated in $(G, T)$ then every truncation of every drawing of $(G, T)$ in $\Sigma$ has tree-width $\le w$."

Graph Minors VIII, (9.4), page 270: excluding a fixed disc-embeddable
graft bounds the tree-width of every truncation of every drawing of a
host graft of the same index. This follows from (9.2) and (9.3). -/
theorem theorem_9_4 {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {S : Type w} [TopologicalSpace S] (hΔ : IsClosedDisc (univ : Set S))
    (Y : Graft α β) (hY : EmbedsGraft S Y) :
    ∃ width : ℕ, ∀ (X : Graft α' β'), X.index = Y.index →
      ¬ IsGraftSimulatedIn Y X → ∀ (gd : GraftDrawing X.G X.T S)
        (Dstar : Drawing S), IsTruncation gd.drawing univ Dstar →
        DrawingTreeWidthLE Dstar width := by exact GraphMinor.GM08.theorem_9_4_proof hΔ Y hY

end

/-! ## Section 10. Paintings -/

section

open Set Topology Surface

universe u w

/-- **Graph Minors VIII, (10.1)** (page 271): "(10.1) *Let* $\mathbf{Q}$ *be a well-quasi-order, and let* $k, w \ge 0$ *be integers. Let* $P_1, P_2, \dots$ *be a countable sequence of* $\mathbf{Q}$*-portraits all with index* $k$ *and tree-width* $\le w$. *Then there exist* $j > i \ge 1$ *such that* $P_i$ *is simulated in* $P_j$." Here `S` is the disc $\Sigma$ of Section 10, and the sequence is indexed
from `0`. The proof applies Graph Minors IV, (9.2), as the paper does.

The cited IV (9.2) is for closed surfaces, so the proof embeds the disc in the sphere. It adds the
boundary nodes to every bag, as in the remark after (10.1). -/
theorem theorem_10_1 {S : Type u} [TopologicalSpace S]
    {Q : Type w} {le : Q → Q → Prop} (hQ : IsWellQuasiOrder le)
    (hS : IsClosedDisc (univ : Set S)) (k w : ℕ) (P : ℕ → QPortrait Q S)
    (hindex : ∀ i, (P i).index = k) (htw : ∀ i, PortraitTreeWidthLE (P i) w) :
    ∃ i j, i < j ∧ IsPortraitSimulatedIn le (P i) (P j) := by exact GraphMinor.GM08.theorem_10_1_proof hQ hS k w P hindex htw

end

/-! ## Section 11. Paintings from Foundations -/

section

open Set Graph GM03 GM06 GM09 Surface

universe u w u' v'

/-- Graph Minors VIII, (11.1) (page 272):
"(11.1) *With notation as above, the tree-width of* $(U', V')$ *is no greater than the tree-width of any corresponding truncation of* $\Gamma$."
Here $(U', V')$ is the painting $(U', N')$ of the portrait `P` derived via `gd` and `F`, and the
truncation is one induced by the same foundation `F`. The proof is on page 273. The paper applies
the strengthened III (3.8), which is about a cylinder, while a truncation has a sleeve in its place.
As the paper does, we contract each sleeve onto the cylinder (`GM08.exists_ring_decomposition`).

The derived painting includes isolated nodes. See the corrections on page 272 in
`corrections/GM08.md`. -/
theorem theorem_11_1 {S : Type u} [TopologicalSpace S]
    {α : Type u'} {β : Type v'} {k : ℕ} (hS : IsClosedDisc (univ : Set S))
    {X : RootedGraph α β} {gd : Surface.GraftDrawing X.G X.toGraft.T S} {t : ℕ}
    {F : Fin t → Set S} {P : QPortrait (QKElem α β S ((k : ℤ) - 1)) S}
    (hP : IsDerivedPortraitVia X gd F P) {Dstar : Drawing S}
    (hD : IsTruncationInducedBy gd.drawing univ F Dstar) {w : ℕ}
    (hw : DrawingTreeWidthLE Dstar w) : PortraitTreeWidthLE P w := by exact GraphMinor.GM08.theorem_11_1_proof hS hP hD hw

end

section

open Set Topology Surface Graph

universe u u' v'

/-- **(11.2)** (page 273): "(11.2) *Let* $(G_1, \tau_1), (G_2, \tau_2) \in \mathscr{A}(k)$, *both
with index* $k$. *Let* $P_i$ *be a* $\mathbf{Q}_{k - 1}$*-portrait derived from* $(G_i, \tau_i)$
$(i = 1, 2)$. *If* $P_1$ *is simulated in* $P_2$ *then* $(G_1, \tau_1)$ *is simulated in*
$(G_2, \tau_2)$."

The proof uses label comparison and the forest replacement with a vertex hypothesis. See the
corrections to the proof of (11.2) in `corrections/GM08.md`. The paper leaves the rest of the
verification to the reader, and the Lean proof writes it out. -/
theorem theorem_11_2 {S : Type u} [TopologicalSpace S]
    {α : Type u'} {β : Type v'} {k : ℕ} (hS : IsClosedDisc (univ : Set S))
    {X₁ X₂ : RootedGraph α β} (h₁ : X₁ ∈ discRootedClassA S k) (h₂ : X₂ ∈ discRootedClassA S k)
    (hk₁ : X₁.index = k) (hk₂ : X₂.index = k)
    {P₁ P₂ : QPortrait (QKElem α β S ((k : ℤ) - 1)) S} (hP₁ : IsDerivedPortrait X₁ P₁)
    (hP₂ : IsDerivedPortrait X₂ P₂)
    (hsim : IsPortraitSimulatedIn (qkLE S ((k : ℤ) - 1)) P₁ P₂) :
    IsRootedGraphSimulatedIn X₁ X₂ := by exact GraphMinor.GM08.theorem_11_2_proof hS h₁ h₂ hk₁ hk₂ hP₁ hP₂ hsim

end

/-! ## Section 12. Conclusion of the Disc Case -/

/-! ## Section 13. Vertex Identification -/

section

open Set Function Relation Graph

universe u v

/-- **Graph Minors VIII, (13.1)** (page 274):
"(13.1) *If* $\mathscr{A}, \mathscr{B}$ *are well-rooted then so is* $\mathscr{A} \oplus \mathscr{B}$." -/
theorem theorem_13_1 {α : Type u} {β : Type v}
    {𝒜 ℬ : Set (Graft α β)}
    (h𝒜 : IsWellRootedGraftClass 𝒜) (hℬ : IsWellRootedGraftClass ℬ) :
    IsWellRootedGraftClass (graftDirectSumClass 𝒜 ℬ) := by exact GraphMinor.GM08.theorem_13_1_proof h𝒜 hℬ

end

section

open Set Function Relation Graph

universe u v

/-- **Graph Minors VIII, (13.2)** (page 274):
"(13.2) *If* $\mathscr{A}$ *is well-rooted, then the class of all grafts which can be obtained from
a member of* $\mathscr{A}$ *by a vertex identification is well-rooted*." -/
theorem theorem_13_2 {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} (h𝒜 : IsWellRootedGraftClass 𝒜) :
    IsWellRootedGraftClass (W1GraftClass 𝒜) := by exact GraphMinor.GM08.theorem_13_2_proof h𝒜

end

section

open Set Function Relation Graph

universe u v

/-- **Graph Minors VIII, (13.3)** (page 275):
"(13.3) *If $\mathcal{A}$ is well-rooted then so is $W(\mathcal{A})$.*" -/
theorem theorem_13_3 {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} (h𝒜 : IsWellRootedGraftClass 𝒜) :
    IsWellRootedGraftClass (WGraftClass 𝒜) := by exact GraphMinor.GM08.theorem_13_3_proof h𝒜

end

/-! ## Section 14. Chains, Trains, and Concatenations -/

section

open Set Function Relation Graph

universe u v

/-- **Graph Minors VIII, (14.1)** (page 275):
"Let $(G, T)$ be a $k$-chain, and let $(G_i, Y_{i-1}, Y_i)$ ($1 \le i \le r$) be a path-decomposition with $|Y_i| = k$ ($0 \le i \le r$). Let $P_1, \dots, P_k$ be mutually disjoint paths of $G$ from $Y_0$ to $Y_r$. Then"

**Graph Minors VIII, (14.1)** (pages 275–276): -/
theorem theorem_14_1 {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {k : ℕ} (hY_card : ∀ i : Fin (D.r + 1), (D.Y i).ncard = k)
    {P : Fin k → Graph α β}
    (hP_path : ∀ p : Fin k,
      IsGraphPathFromTo X.G (P p) (D.Y ⟨0, Nat.zero_lt_succ D.r⟩) (D.Y (Fin.last D.r)))
    (hP_disj : ∀ p q : Fin k, p ≠ q → Disjoint V(P p) V(P q)) :
    (∀ (i : Fin D.r) (e : β) (x y : α),
      X.G.IsLink e x y →
      x ∈ (⋃ (j : Fin D.r) (_ : j < i), V(D.G j)) →
      y ∈ (⋃ (j : Fin D.r) (_ : i < j), V(D.G j)) →
      x ∈ V(D.G i) ∨ y ∈ V(D.G i)) ∧
    (∀ (h i j : Fin D.r), h ≤ i → i ≤ j →
      ∀ Q : Graph α β, IsGraphPathFromTo X.G Q V(D.G h) V(D.G j) →
        (V(Q) ∩ V(D.G i)).Nonempty) ∧
    (∀ (i : Fin (D.r + 1)) (p : Fin k), (D.Y i ∩ V(P p)).ncard = 1) ∧
    (∀ (i : Fin D.r) (p : Fin k), IsGraphPath X.G (P p ⊓ D.G i)) ∧
    (∀ p : Fin k, IsConcatenatedPath X.G (P p) (fun i : Fin D.r => P p ⊓ D.G i)) := by exact GraphMinor.GM08.theorem_14_1_proof D hY_card hP_path hP_disj

end

section

open Set Function Relation Graph
open Classical

universe u v

/-- **Graph Minors VIII, (14.2)** (page 276):
"If $\mathcal{A}$ is well-rooted and $k \ge 0$ is an integer, the class of all $k$-chains over $\mathcal{A}$ is well-rooted."

**Graph Minors VIII, (14.2)** (pages 276–278): -/
theorem theorem_14_2 {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} (h𝒜 : IsWellRootedGraftClass 𝒜) (k : ℕ) :
    IsWellRootedGraftClass (kChainClass 𝒜 k) := by exact GraphMinor.GM08.theorem_14_2_proof h𝒜 k

end

section

open Set Function Relation Graph

universe u v u' v'

/-- **Graph Minors VIII, (14.3)** (page 279):
"(14.3) *Every $k$-train over $\mathcal{A}$ belongs to
$W(\mathcal{A}^* \oplus \mathcal{B}^* \oplus \mathcal{A}^*) \cup
W(\mathcal{A}^* \oplus \mathcal{A}^*) \cup \mathcal{A}$ where $\mathcal{B}$ is the class of all
$k$-chains over $\mathcal{A}$.*" -/
theorem theorem_14_3 {α : Type u} {β : Type v} [Infinite α]
    (𝒜 : Set (Graft α β)) (k : ℕ) :
    let ℬ := kChainClass 𝒜 k
    LKGraftClass k 𝒜 ⊆
      WGraftClass (graftDirectSumClass (isoGraftClass 𝒜)
        (graftDirectSumClass (isoGraftClass ℬ) (isoGraftClass 𝒜))) ∪
      WGraftClass (graftDirectSumClass (isoGraftClass 𝒜) (isoGraftClass 𝒜)) ∪
      𝒜 := by exact GraphMinor.GM08.theorem_14_3_proof 𝒜 k

end

section

open Set Function Relation Graph

universe u v u' v'

/-- **Graph Minors VIII, (14.4)** (page 279):
"(14.4) *If $\mathcal{A}$ is well-rooted then so is $L^k(\mathcal{A})$.*" -/
theorem theorem_14_4 {α : Type u} {β : Type v} [Infinite α]
    (𝒜 : Set (Graft α β)) (k : ℕ) (h𝒜 : IsWellRootedGraftClass 𝒜) :
    IsWellRootedGraftClass (LKGraftClass k 𝒜) := by exact GraphMinor.GM08.theorem_14_4_proof 𝒜 k h𝒜

end

section

open Set Function Relation Graph

universe u v u' v'

/-- **Graph Minors VIII, (14.5)** (page 279):
"(14.5) *If $\mathcal{A}$ is well-rooted, then the class of all concatenations over $\mathcal{A}$
is well-rooted.*" -/
theorem theorem_14_5 {α : Type u} {β : Type v} [Infinite α]
    (𝒜 : Set (Graft α β)) (h𝒜 : IsWellRootedGraftClass 𝒜) :
    IsWellRootedGraftClass (concatenationClass 𝒜) := by exact GraphMinor.GM08.theorem_14_5_proof 𝒜 h𝒜

end

/-! ## Section 15. TUBES -/

section

open Set Graph GraphMinor.Surface

universe u v w

/-- **Graph Minors VIII, (15.1)** (page 280):
"Every tubular graft of width $\ge r$ and index $\le k$ is an $r$-train of tubular grafts of width $\ge r + 1$ and index $\le k + 2r$."

Here the width of a tube is the printed one of page 280 (`Tube.printedWidth`), and the width of a
tubular graft is the largest printed width of its framings (`tubularPrintedWidth`).

This is the printed-width form, including the pocket cases omitted by the printed chain argument.
See the correction to the proof of (15.1) in `corrections/GM08.md`. -/
theorem theorem_15_1 {α : Type u} {β : Type v}
    (r k : ℕ) :
    printedTubularClass (α := α) (β := β) r k ⊆
      LKGraftClass r (printedTubularClass (r + 1) (k + 2 * r)) := by exact GraphMinor.GM08.theorem_15_1_printed r k

end

section

open Set

universe u v w

/-- **Graph Minors VIII, (15.2)** (page 281):
"(15.2) *Let $(G, T)$ be a tubular graft of index $\le k$ and let $r \ge 0$ be an
integer. Then $(G, T)$ is a concatenation of tubular grafts of width $\ge r$ and
index $\le k + r(r - 1)$.*"
The width is the printed one. The proof is the induction of page 281, run with
(15.1) for the side-qualified width (`GM08.theorem_15_2_proof_sideQualified`). -/
theorem theorem_15_2 {α : Type u} {β : Type v} {X : Graft α β} {k : ℕ} (r : ℕ)
    (hX : IsTubularGraft X) (hk : X.index ≤ k) :
    X ∈ concatenationClass (printedTubularClass r (k + r * (r - 1))) := by exact GraphMinor.GM08.theorem_15_2_proof r hX hk

end

section

open Set

universe u v w

/-- **Graph Minors VIII, (15.3)** (page 281):
"If $(G, T) \in \mathcal{A}(k, r, s)$, then $(G, T)$ is a concatenation of tubular grafts of length $< s$ and index $\le k + r(r - 1)$."

Graph Minors VIII, (15.3), pages 281–282, for the printed width:
every member of `𝒜(k,r,s)` is a concatenation of tubular grafts of
length less than `s` and index at most `k + r(r - 1)`. The decomposition
only needs the weaker side-qualified no-inner-tube condition. -/
theorem theorem_15_3 {α : Type u} {β : Type v} (k r s : ℕ) :
    printedClassA (α := α) (β := β) k r s ⊆
      concatenationClass
        {Y : Graft α β | IsTubularGraft Y ∧ tubularLength Y < s ∧ Y.index ≤ k + r * (r - 1)} := by exact GraphMinor.GM08.theorem_15_3_proof k r s

end

section

open Set GraphMinor.Surface

universe u v

/-- **Graph Minors VIII, (15.4)** (page 282):
"For any integers $k, r, s \ge 0$, $\mathcal{A}(k, r, s)$ is well-rooted."

Graph Minors VIII, (15.4), page 282: for all nonnegative integers
`k`, `r`, and `s`, the printed class `𝒜(k,r,s)` is well-rooted. The proof
uses Section 12, the short-tube disc cut, (13.3), (15.3), and (14.5). -/
theorem theorem_15_4 {α : Type u} {β : Type v} (k r s : ℕ) :
    IsWellRootedGraftClass (printedClassA (α := α) (β := β) k r s) := by exact GraphMinor.GM08.theorem_15_4_proof k r s

end

/-! ## Section 16. BOUNDARY-LINKING IN TUBES -/

section



universe u v

/-- **Graph Minors VIII, (16.1)** (page 282): "(16.1) *If $\mathcal{B}(k - 1)$ is
well-rooted then so is $\mathcal{B}(k, r, s)$, for any integers $k, r, s \ge 0$.*"
For an infinite label type this is the paper's proof (`GM08.theorem_16_1_proof_of_infinite`).
For a finite label type every class of grafts is well-rooted
(`GM08.isWellRootedGraftClass_of_finite`).

For finite label types, the proof uses finite sets and Dickson’s lemma. The paper's proof applies
(16.2), whose pieces may need labels that a finite label type does not have. -/
theorem theorem_16_1 {α : Type u} {β : Type v} (k r s : ℕ)
    (hprev : IsWellRootedGraftClass (classB (α := α) (β := β) ((k : ℤ) - 1))) :
    IsWellRootedGraftClass (printedClassBUnlinked (α := α) (β := β) k r s) := by exact GraphMinor.GM08.theorem_16_1_proof k r s hprev

end

section

open Set GraphMinor.Surface GraphMinor.GM11

universe u v

/-- **Graph Minors VIII, (16.2)** (page 282):
"$\mathcal{B}(k, r, s) \subseteq \mathcal{A}(k, r, s) \cup W(\mathcal{B}(k - 1) \oplus \mathcal{A}(2k, r, s + 2)) \cup W(\mathcal{B}(k - 1) \oplus \mathcal{B}(k - 1)).$"

Graph Minors VIII (16.2), pages 282–284. The three minimum-hoop cases
use exactly the printed width exceptions. In Case 2 the exceptional-hoop
replacement supplies the width step and its required length estimate. -/
theorem theorem_16_2 {α : Type u} {β : Type v} [Infinite α] (k r s : ℕ) :
    printedClassBUnlinked (α := α) (β := β) k r s ⊆ printedClassA k r s ∪
      WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (printedClassA (2 * k) r (s + 2))) ∪
      WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (classB ((k : ℤ) - 1))) := by exact GraphMinor.GM08.theorem_16_2_proof k r s

end

/-! ## Section 17. Conclusion of the Cylinder Case -/

section

open Set GraphMinor.Surface

universe u v

/-- **Graph Minors VIII, (17.1)** (page 284):
"For any integer $k \ge 0$, $\mathscr{B}(k) = \bigcup (\mathscr{B}(k_1, k_2))$, the union being taken over all integers $k_1, k_2 \ge 0$ with $k_1 + k_2 \le k$.
We shall need the following lemma, which is a consequence of [11, Theorem (9.3)].
(17.2) Let $(H, U) \in \mathscr{B}(k_1, k_2)$. Then there are integers $r, s \ge 0$ such that for every $(G, T) \in \mathscr{B}(k_1, k_2)$, either $(H, U)$ is simulated in $(G, T)$ or $(G, T) \in \mathscr{B}(k_1 + k_2, r, s)$.
From this we deduce the following.
(17.3) For any integer $k \ge 0$, $\mathscr{B}(k)$ is well-rooted.
Proof. We proceed by induction on $k$, and assume that $\mathscr{B}(k - 1)$ is well-rooted. (We recall that $\mathscr{B}(-1)$ is interpreted as $\emptyset$, which is certainly well-rooted.) By (17.1) and (4.2), it suffices to prove that $\mathscr{B}(k_1, k_2)$ is well-rooted for all choices of $k_1, k_2$ with $k_1 + k_2 \le k$. Let us then choose integers $k_1, k_2 \ge 0$ with $k_1 + k_2 \le k$. Let $(G_1, T_1), (G_2, T_2), \dots$ be a countable sequence of members of $\mathscr{B}(k_1, k_2)$. We wish to show that there exist $j > i \ge 1$ such that $(G_i, T_i)$ is simulated in $(G_j, T_j)$. If $(G_1, T_1)$ is simulated in $(G_i, T_i)$ for some $i > 1$ we are done, and so we assume that this is false. By (17.2) there are integers $r, s \ge 0$ such that $(G_i, T_i) \in \mathscr{B}(k_1 + k_2, r, s)$ for all $i \ge 2$. But $\mathscr{B}(k_1 + k_2, r, s) \subseteq \mathscr{B}(k, r, s)$, and $\mathscr{B}(k, r, s)$ is well-rooted by (16.1) and our inductive hypothesis that $\mathscr{B}(k - 1)$ is well-rooted. Hence there exist $j > i \ge 2$ such that $(G_i, T_i)$ is simulated in $(G_j, T_j)$, as required. \square"

Graph Minors VIII, (17.1), page 284: `ℬ(k)` is the union of the
fixed-cuff classes `ℬ(k₁,k₂)` over all `k₁ + k₂ ≤ k`, in a fixed
cylinder with its two cuffs ordered as `C,D`. -/
theorem theorem_17_1 {S : Type} [TopologicalSpace S] (hS : IsCylinder S)
    {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    {α : Type u} {β : Type v} (k : ℕ) :
    classB (α := α) (β := β) (k : ℤ) =
      ⋃ p ∈ {p : ℕ × ℕ | p.1 + p.2 ≤ k}, classBCuffCounts S C D p.1 p.2 := by exact GraphMinor.GM08.theorem_17_1_proof hS hC hD hCD k

end

section

open Set GraphMinor.Surface

universe u v

/-- **Graph Minors VIII, (17.2)** (page 284): "*Let* $(H, U) \in \mathscr{B}(k_1, k_2)$.
*Then there are integers* $r, s \ge 0$ *such that for every*
$(G, T) \in \mathscr{B}(k_1, k_2)$, *either* $(H, U)$ *is simulated in* $(G, T)$
*or* $(G, T) \in \mathscr{B}(k_1 + k_2, r, s)$." -/
theorem theorem_17_2 {S : Type} [TopologicalSpace S] (hS : IsCylinder S)
    {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    {α : Type u} {β : Type v} {k₁ k₂ : ℕ} {Y : Graft α β}
    (hY : Y ∈ classBCuffCounts S C D k₁ k₂) :
    ∃ r s : ℕ, ∀ X : Graft α β, X ∈ classBCuffCounts S C D k₁ k₂ →
      IsGraftSimulatedIn Y X ∨ X ∈ printedClassBUnlinked (k₁ + k₂) r s := by exact GraphMinor.GM08.theorem_17_2_proof hS hC hD hCD hY

end

section

open Set GraphMinor.Surface

universe u v

/-- **Graph Minors VIII, (17.3)** (page 284): "*For any integer* $k \ge 0$,
$\mathscr{B}(k)$ *is well-rooted.*" The proof is by induction on `k`, starting
from `ℬ(-1) = ∅`. -/
theorem theorem_17_3 {α : Type u} {β : Type v} (k : ℕ) :
    IsWellRootedGraftClass (classB (α := α) (β := β) (k : ℤ)) := by exact GraphMinor.GM08.theorem_17_3_proof k

end

/-! ## Section 18. The General Surface -/

section

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- **Graph Minors VIII, (18.1)** (page 285):
"Let $\Sigma$ be a connected surface, not a sphere, disc, or cylinder. Let $\Delta$ be a drawing of a graft $(H, U)$ in $\Sigma$. Then there is a number $N$ such that for"

The closed-surface case of Graph Minors VIII (18.1), pages 285–286,
for drawings of abstract grafts. A model of the closed surface is supplied
explicitly. The cuff alternatives are empty in this case.

The printed statement fails on a three-cuff surface. The root-leaf form is the closest correction
for arbitrary surfaces: it keeps outcomes (i) and (ii) and applies (iii) and (iv) to the drawing
with root leaves. See the correction to (18.1) in `corrections/GM08.md`. -/
theorem theorem_18_1_closed {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) (a b : ℕ) (hab : 1 ≤ a + b)
    (he : Nonempty (S ≃ₜ SurfaceModel a b 0)) {α : Type u} {β : Type v}
    (Y : Graft α β) (DY : GraftDrawing Y.G Y.T S) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      IsGraftSimulatedIn Y X ∨
      ∃ F : Set S, GM07.IsSchism F ∧ DX.drawing.IsNormal F ∧
        (DX.drawing.V ∩ F).ncard ≤ N := by exact GraphMinor.GM08.Proofs.theorem_18_1_closed hS hns a b hab he Y DY

end

section

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- **Graph Minors VIII, (18.1)** (page 285):
"Let $\Sigma$ be a connected surface, not a sphere, disc, or cylinder. Let $\Delta$ be a drawing of a graft $(H, U)$ in $\Sigma$. Then there is a number $N$ such that for"

The closed-surface case of VIII (18.1), pages 285–286, for the grafts
represented by surface digraphs. Cuff alternatives are absent because the
surface is closed. VII (9.2) is itself the closed-surface application of
VII (9.1) used by the paper.

The printed statement fails on a three-cuff surface. The root-leaf form is the closest correction
for arbitrary surfaces: it keeps outcomes (i) and (ii) and applies (iii) and (iv) to the drawing
with root leaves. See the correction to (18.1) in `corrections/GM08.md`. -/
theorem theorem_18_1_closed_model {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) (a b : ℕ) (hab : 1 ≤ a + b)
    (he : Nonempty (S ≃ₜ SurfaceModel a b 0)) (H : GM07.SurfaceDigraph S) :
    ∃ N : ℕ, ∀ G : GM07.SurfaceDigraph S,
      IsGraftSimulatedIn (boundaryGraft H.G) (boundaryGraft G.G) ∨
      ∃ F : Set S, GM07.IsSchism F ∧ G.G.IsNormal F ∧ (G.G.V ∩ F).ncard ≤ N := by exact GraphMinor.GM08.Proofs.theorem_18_1_closed_model hS hns a b hab he H

end

section

open Set Topology Function Graph GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11

universe u v w

/-- **Graph Minors VIII, (18.1)** (page 285):
"Let $\Sigma$ be a connected surface, not a sphere, disc, or cylinder. Let $\Delta$ be a drawing of a graft $(H, U)$ in $\Sigma$. Then there is a number $N$ such that for"

**VIII (18.1) for root-leaf drawings.** Let `S` have a cuff and not be a
sphere, disc or cylinder, and let `Y` be drawn in `S`. Then there is `N` such
that for every graft `X` drawn in `S`, either `Y` is simulated in `X`, or the
cuff counts differ, or the root-leaf graft of `X` has a drawing in `S` with the
same cuff counts as `X` in which (18.1)(iv) holds, or there is a normal schism
with at most `N` vertices that misses the boundary.

The printed statement fails on a three-cuff surface. The root-leaf form is the closest correction
for arbitrary surfaces: it keeps outcomes (i) and (ii) and applies (iii) and (iv) to the drawing
with root leaves. See the correction to (18.1) in `corrections/GM08.md`. -/
theorem theorem_18_1_leaf {S : Type w} [TopologicalSpace S]
    [T1Space S] [ConnectedSpace S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c) (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (hcuffs : (cuffs S).Nonempty)
    {α : Type u} {β : Type v} {Y : Graft α β} (DY : GraftDrawing Y.G Y.T S) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      IsGraftSimulatedIn Y X ∨
      (∃ C ∈ cuffs S, (DX.drawing.V ∩ C).ncard ≠ (DY.drawing.V ∩ C).ncard) ∨
      ∃ DX' : GraftDrawing (rootLeafGraft X).G (rootLeafGraft X).T S,
        (∀ C ∈ cuffs S, DX'.drawing.V ∩ C = DX.drawing.V ∩ C) ∧
        ((∃ C ∈ cuffs S, ∃ F : Set S, DX'.drawing.IsNormal F ∧ IsOArc F ∧
            GM07.SurroundsCuff F C ∧ F ∩ bd S ⊆ C ∧
            (DX'.drawing.V ∩ F).ncard < (DX'.drawing.V ∩ C).ncard) ∨
          ∃ F : Set S, GM07.IsSchism F ∧ DX'.drawing.IsNormal F ∧ F ∩ bd S = ∅ ∧
            (DX'.drawing.V ∩ F).ncard ≤ N) := by exact GraphMinor.GM08.Proofs.theorem_18_1_leaf hS a b c h3 he hncyl hcuffs DY

end

section

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- **Graph Minors VIII, (18.1)** (page 285):
"Let $\Sigma$ be a connected surface, not a sphere, disc, or cylinder. Let $\Delta$ be a drawing of a graft $(H, U)$ in $\Sigma$. Then there is a number $N$ such that for"

Graph Minors VIII (18.1), pages 285–286, for a surface with exactly
one cuff. These are all four printed alternatives, with no extra proof
hypotheses.

The printed statement fails on a three-cuff surface. The root-leaf form is the closest correction
for arbitrary surfaces: it keeps outcomes (i) and (ii) and applies (iii) and (iv) to the drawing
with root leaves. See the correction to (18.1) in `corrections/GM08.md`. -/
theorem theorem_18_1_one_cuff {S : Type w} [TopologicalSpace S]
    [T1Space S] [ConnectedSpace S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {C : Set S} (hc : cuffs S = {C})
    {α : Type u} {β : Type v} {Y : Graft α β} (DY : GraftDrawing Y.G Y.T S) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      IsGraftSimulatedIn Y X ∨
      (∃ C ∈ cuffs S, (DX.drawing.V ∩ C).ncard ≠ (DY.drawing.V ∩ C).ncard) ∨
      (∃ F : Set S, GM07.IsSchism F ∧ DX.drawing.IsNormal F ∧
        (DX.drawing.V ∩ F).ncard ≤ N) ∨
      (∃ C ∈ cuffs S, ∃ F : Set S, DX.drawing.IsNormal F ∧ IsOArc F ∧ GM07.SurroundsCuff F C ∧
        F ∩ bd S ⊆ C ∧ (DX.drawing.V ∩ F).ncard < (DX.drawing.V ∩ C).ncard) := by exact GraphMinor.GM08.Proofs.theorem_18_1_one_cuff hS a b c h3 he hncyl hc DY

end

section

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- **Graph Minors VIII, (18.1)** (page 285):
"Let $\Sigma$ be a connected surface, not a sphere, disc, or cylinder. Let $\Delta$ be a drawing of a graft $(H, U)$ in $\Sigma$. Then there is a number $N$ such that for"

Graph Minors VIII (18.1), pages 285–286, when the target graft has
no roots. The proof applies on a surface with any number of cuffs.

The printed statement fails on a three-cuff surface. The root-leaf form is the closest correction
for arbitrary surfaces: it keeps outcomes (i) and (ii) and applies (iii) and (iv) to the drawing
with root leaves. See the correction to (18.1) in `corrections/GM08.md`. -/
theorem theorem_18_1_rootless {S : Type w} [TopologicalSpace S]
    [T1Space S] [ConnectedSpace S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {α : Type u} {β : Type v} {Y : Graft α β} (DY : GraftDrawing Y.G Y.T S)
    (hroot : Y.T = ∅) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      IsGraftSimulatedIn Y X ∨
      (∃ C ∈ cuffs S, (DX.drawing.V ∩ C).ncard ≠ (DY.drawing.V ∩ C).ncard) ∨
      (∃ F : Set S, GM07.IsSchism F ∧ DX.drawing.IsNormal F ∧
        (DX.drawing.V ∩ F).ncard ≤ N) ∨
      (∃ C ∈ cuffs S, ∃ F : Set S, DX.drawing.IsNormal F ∧ IsOArc F ∧ GM07.SurroundsCuff F C ∧
        F ∩ bd S ⊆ C ∧ (DX.drawing.V ∩ F).ncard < (DX.drawing.V ∩ C).ncard) := by exact GraphMinor.GM08.Proofs.theorem_18_1_rootless hS a b c h3 he hncyl DY hroot

end

section

open Set Topology GraphMinor.Surface GraphMinor.GM11
open Set GraphMinor.Surface

universe w

/-- **Graph Minors VIII, (18.2)** (page 286):
"Let $\Sigma$ be a connected surface, not a sphere, disc or cylinder, and let $X$ be a schism in $\Sigma$. Let $\Sigma'$ be obtained from $\Sigma$ by cutting along $X$. Then $g(\Sigma') < g(\Sigma)$.
Proof. Let $\Sigma_1$ be a component of $\Sigma'$ and $\Sigma_2$ be the union of the other components. Let $\Sigma, \Sigma', \Sigma_1, \Sigma_2$ have Euler characteristics $e, e', e_1, e_2$ and have $c, c', c_1, c_2$ cuffs, respectively. Let $a, b, c, k_2, a_2, b_2, c_2$ be such that $\Sigma \cong \Sigma(a, b, c)$, and $\Sigma_2$ has $k_2$ components, and $\Sigma_2$ may be obtained from the union of $k_2$ disjoint spheres by adding $a_2$ handles and $b_2$ cross-caps and removing the interiors of $c_2$ disjoint closed discs (where of course $k_2 = a_2 = b_2 = c_2 = 0$ if $\Sigma'$ is connected). The schism $X$ is of one of the types listed in the definition of "schism," which gives us several cases to consider. In each case we can find $e' - e$ by considering a triangulation of $\Sigma$ in which $X$ is a union of $0$- and $1$-simplices, and it can be verified that
$$2(e' - e) + e' - c + 4a_2 + 2b_2 + c_2 > 4k_2.$$
But $e' = e_1 + 2k_2 - 2a_2 - b_2 - c_2$ and $c' = c_1 + c_2$, and it follows by substitution that $2e_1 + c_1 > 2e + c$. Now $g(\Sigma_1) = 4 - 2e_1 - c_1$, and $g(\Sigma) = 4 - 2e - c$, and so $g(\Sigma_1) < g(\Sigma)$. Since this holds for every component $\Sigma_1$ of $\Sigma'$ we deduce that $g(\Sigma') < g(\Sigma)$, as required. \square
We come now to the proof of (6.1). If $\Sigma$ is a surface and $k \ge 0$ is an integer, we define $\mathscr{C}(\Sigma, k)$ to be the class of all grafts of index $\le k$ which embed in $\Sigma$. If $h, k \ge 0$ are integers, we define $\mathscr{C}(h, k)$ to be the union of $\mathscr{C}(\Sigma, k)$, taken over all surfaces $\Sigma$ with $g(\Sigma) \le h$. Then (6.1) is a consequence of the following.
(18.3) For any integers $h, k \ge 0$, $\mathscr{C}(h, k)$ is well-rooted."

**VIII (18.2)**, page 286, with no hypothesis: cutting a connected surface
that is not a sphere, disc or cylinder along a schism lowers `g`.

The paper cuts along a schism "in the natural way". The cut here has finite fibres, with the correct
number of sides at each boundary point. The Euler calculation uses the corrected cuff term (see the
correction to the proof of (18.2) in `corrections/GM08.md`). -/
theorem theorem_18_2 :
  ∀ (S : Type w) [TopologicalSpace S] [ConnectedSpace S], IsSurface S →
    ∀ (a b c : ℕ), 3 ≤ 3 * a + 3 * b + c → Nonempty (S ≃ₜ SurfaceModel a b c) →
    ∀ X : Set S, GM07.IsSchism X →
      ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
        GM07.IsCutAlongSet X ψ ∧ surfaceComplexity T < surfaceComplexity S := by exact GraphMinor.GM08.theorem_18_2_proof

end

section

open Set GraphMinor.Surface

universe u v w u' v'

/-- **Graph Minors VIII, (18.3)** (page 286):
"For any integers $h, k \ge 0$, $\mathscr{C}(h, k)$ is well-rooted."

**VIII (18.3)**, page 286: for any integers `h, k ≥ 0`, `𝒞(h, k)` is
well-rooted.

The proof uses the root-leaf form of (18.1) and corrects the reference to its fourth outcome. See
the corrections to (18.1) and to the proof of (18.3) in `corrections/GM08.md`. -/
theorem theorem_18_3 :
  ∀ (α : Type u) (β : Type v) (h k : ℕ),
    IsWellRootedGraftClass (classC.{u, v, w} (α := α) (β := β) h k) := by exact GraphMinor.GM08.theorem_18_3_proof

end

end GraphMinor.GM08
