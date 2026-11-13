module

public import GraphMinor.GM11.Nice73
public import GraphMinor.GM11.Restraints
public import GraphMinor.GM11.Section3
public import GraphMinor.GM11.Section4
public import GraphMinor.GM11.Section4b
public import GraphMinor.GM11.Section4c
public import GraphMinor.GM11.Section5
public import GraphMinor.GM11.Section5c
public import GraphMinor.GM11.Section6Pretangle
public import GraphMinor.GM11.Section7
public import GraphMinor.GM11.Section79
public import GraphMinor.GM11.Section7b
public import GraphMinor.GM11.Section8
public import GraphMinor.GM11.Section81
public import GraphMinor.GM11.Section810
public import GraphMinor.GM11.Section85
public import GraphMinor.GM11.Section87
public import GraphMinor.GM11.Section88
public import GraphMinor.GM11.Section89
public import GraphMinor.GM11.Section91
public import GraphMinor.GM11.Section92
public import GraphMinor.GM11.Theorem61
public import GraphMinor.GM11.Theorem63
public import GraphMinor.GM11.Theorem64
public import GraphMinor.GM11.Theorem65
public import GraphMinor.GM11.Theorem66
public import GraphMinor.GM11.Theorem75
public import GraphMinor.GM14.Cited

/-!
# Graph Minors XI: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XI. Circuits on a surface*, J. Combin. Theory Ser. B
**60** (1994), 72–106.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. The errors of the paper, and how the Lean corrects them, are listed in
`corrections/GM11.md`.
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u u_1 u_2

/-! ## Section 1. Introduction -/

/-! ## Section 2. Hypergraphs and Tangles -/

/-! ## Section 3. Surfaces, Drawings, and Homotopy -/

/-- **Graph Minors XI, (3.1)** (page 76): "If $X, Y \subseteq \Sigma$ are closed, and $X$ is
simply-connected and $X \cap Y$ is non-empty and arc-wise connected, then any continuous $\phi
\colon S^1 \to X \cup Y$ is homotopic in $X \cup Y$ to a continuous $\phi' \colon S^1 \to Y$."

If `X, Y ⊆ Σ` are closed, and `X` is
simply-connected and `X ∩ Y` is non-empty and arc-wise connected, and moreover `X` deforms locally
into `X ∩ Y` (`IsLocalDeformationRetract`), then any continuous `φ : S¹ → X ∪ Y` is homotopic in
`X ∪ Y` to a continuous `φ' : S¹ → Y`.

The paper has no local hypothesis, and without one the statement is false. The hypothesis holds in
the paper's uses: there `X` is a closed disc and `X ∩ Y` is its boundary
(`IsClosedDisc.isLocalDeformationRetract`), except in (7.8) as used in (8.8), where `X` and `Y` are
unions of vertices, edges and regions of a drawing. The space need not be a surface.

The print is false for general closed sets, so the Lean adds the hypothesis
`IsLocalDeformationRetract X (X ∩ Y)`, which holds where the paper uses (3.1). See the correction
to (3.1) in `corrections/GM11.md`. -/
theorem theorem_3_1 {S : Type u} [TopologicalSpace S] {X Y : Set S} (hX : IsClosed X)
    (hY : IsClosed Y) (hsc : IsSimplyConnectedSet X) (hL : IsPathConnected (X ∩ Y))
    (hloc : IsLocalDeformationRetract X (X ∩ Y)) (φ : C(Circle, S)) (hφ : range φ ⊆ X ∪ Y) :
    ∃ φ' : C(Circle, S), range φ' ⊆ Y ∧ ClosedCurvesHomotopicIn (X ∪ Y) φ φ' :=
  theorem_3_1_proof hX hY hsc hL hloc φ hφ

/-! ## Section 4. Slopes -/

open Hypergraph in
/-- **Graph Minors XI, (4.1)** (page 78): "Let $\Sigma$ be a connected surface, not a sphere, let
$\theta \ge 1$, and let $\Gamma$ be a $\theta$-representative $2$-cell painting or drawing in
$\Sigma$. Then there is a unique respectful tangle in $\Gamma$ of order $\theta$."

A `θ`-representative 2-cell painting or drawing in a connected surface other than
the sphere has a unique respectful tangle of order `θ`. -/
theorem theorem_4_1 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {θ : ℕ}
    {Γ : PaintingOrDrawing S} (hS : IsClosedSurface S) (hns : ¬ IsSphere S) (hθ : 1 ≤ θ)
    (hT2 : Γ.IsTwoCell) (hrep : Γ.IsRepresentative θ) :
    ∃! T, GM10.IsTangle Γ.toHypergraph θ T ∧ Γ.IsRespectful θ T :=
  theorem_4_1_proof hS hns hθ hT2 hrep

/-- **Graph Minors XI, (4.2)** (page 79): "Let $\Gamma'$ be a subdrawing of $\Gamma$. Then the
restriction of $\text{ins}$ to the set
circuits of $\Gamma'$ of length $< 2\theta$ is a slope of order $\theta$ in $\Gamma'$." -/
theorem theorem_4_2 {S : Type u} [TopologicalSpace S] [T2Space S] {Γ Γ' : Drawing S} {k : ℕ}
    {ins : Drawing S → Set S} (hs : IsSlope Γ k ins) (hsub : Γ'.IsSubdrawing Γ) :
    IsSlope Γ' k ins :=
  theorem_4_2_proof hs hsub

open Hypergraph in
/-- **Graph Minors XI, (4.3)** (page 79): "Let $\Gamma'$ be a confined subdrawing of $\Gamma$, and
let $C$ be a circuit of $\Gamma'$ with $\text{ins}(C)$ maximal. Then
(i) $U(P) \subseteq \text{ins}(C)$ for every path $P$ of $\Gamma'$ with both ends in $V(C)$,
(ii) for every edge $e$ of $C$, $\Gamma'$ does not capture the region of $\Gamma$ incident with $e$
not included in $\text{ins}(C)$, and
(iii) if $\Gamma'$ is non-separable then $\text{ins}(\Gamma') = \text{ins}(C)$." -/
theorem theorem_4_3 {S : Type u} [TopologicalSpace S] [T2Space S] {Γ Γ' C : Drawing S} {k : ℕ}
    {ins : Drawing S → Set S} (hs : IsSlope Γ k ins) (hsub : Γ'.IsSubdrawing Γ)
    (hconf : IsConfined k Γ') (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ')
    (hmax : ∀ C' : Drawing S, C'.IsCircuit → C'.IsSubdrawing Γ' → ins C ⊆ ins C' → ins C' ⊆ ins C) :
    (∀ (P : Drawing S) (a b : S), P.IsPathBetween a b → P.IsSubdrawing Γ' →
      a ∈ C.V → b ∈ C.V → P.U ⊆ ins C) ∧
    (∀ e r : Set S, e ∈ C.E → (e ∩ closure r).Nonempty → ¬ r ⊆ ins C →
      ¬ Captures ins k Γ' r) ∧
    (Γ'.IsNonSeparable → insOf ins Γ' = ins C) :=
  theorem_4_3_proof hs hsub hconf hC hCs hmax

/-- **Graph Minors XI, (4.4)** (page 80): "If $\Gamma'$ is confined then $\Sigma -
\operatorname{ins}(\Gamma')$ is a region of $\Gamma'$."
Here `Σ` is a connected closed surface. -/
theorem theorem_4_4 {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    (hS : IsClosedSurface S) [ConnectedSpace S] {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope Γ k ins) {Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ) (hconf : IsConfined k Γ') :
    univ \ insOf ins Γ' ∈ Γ'.R :=
  theorem_4_4_proof hS hs hsub hconf

/-- **Graph Minors XI, (4.5)** (pages 80–81): "Let $\Gamma' \subseteq \Gamma$ be confined, and let
$r' \in R(\Gamma')$. Suppose that
$\Gamma$ captures $r'$. Then so does $\Gamma'$." The paper takes a circuit of `Γ'` bounding a closed
disc
in `ins(C)` around `r'`. We replace this step by `captures_aux`. -/
theorem theorem_4_5 {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    (hS : IsClosedSurface S) [PreconnectedSpace S] {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope Γ k ins) {Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ) (hconf : IsConfined k Γ')
    {r' : Set S} (hr' : r' ∈ Γ'.R) (hcap : Captures ins k Γ r') : Captures ins k Γ' r' :=
  theorem_4_5_proof hS hs hsub hconf hr' hcap

/-! ## Section 5. Small Sets -/

/-- **Graph Minors XI, (5.1)** (page 81): "Let $Z \subseteq R(\Gamma)$, and let $\Gamma' \subseteq
\Gamma$. Let $r'$ be a region of
$\Gamma'$. If there are regions $r_1 \in Z$, $r_2 \in R(\Gamma) - Z$ with $r_1, r_2
\subseteq r'$, then there are such regions $r_1, r_2$ which in addition are incident with
some edge $e$ of $\Gamma$ with $e \notin E(\Gamma')$." -/
theorem theorem_5_1 {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    (hS : IsClosedSurface S) {Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ) {Z : Set (Set S)}
    {r' r₁ r₂ : Set S} (hr' : r' ∈ Γ'.R) (h₁ : r₁ ∈ Γ.R) (hz₁ : r₁ ∈ Z) (h₂ : r₂ ∈ Γ.R)
    (hz₂ : r₂ ∉ Z) (hs₁ : r₁ ⊆ r') (hs₂ : r₂ ⊆ r') :
    ∃ e ∈ Γ.E, e ∉ Γ'.E ∧ ∃ a b : Set S, a ∈ Z ∧ b ∉ Z ∧ a ⊆ r' ∧ b ⊆ r' ∧
    Γ.EdgeRegionIncident e a ∧ Γ.EdgeRegionIncident e b :=
  theorem_5_1_proof hS hsub hr' h₁ hz₁ h₂ hz₂ hs₁ hs₂

/-- **Graph Minors XI, (5.2)** (page 81): "If $Z \subseteq R(\Gamma)$ and $|\Omega \cap V(N(Z))| <
\omega$, then exactly one of $Z$,
$R(\Gamma) - Z$ is small." -/
theorem theorem_5_2 {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    (hS : IsClosedSurface S) [ConnectedSpace S] {k ω : ℕ} {ins : Drawing S → Set S} {Ω : Set S}
    {Z : Set (Set S)} (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω) (hZ : Z ⊆ Γ.R)
    (hlt : (Ω ∩ (boundaryDrawing Γ Z).V).ncard < ω) :
    (IsSmall Γ ins k Ω ω Z ∨ IsSmall Γ ins k Ω ω (Γ.R \ Z)) ∧
    ¬ (IsSmall Γ ins k Ω ω Z ∧ IsSmall Γ ins k Ω ω (Γ.R \ Z)) :=
  theorem_5_2_proof hS hs hw hZ hlt

/-- **Graph Minors XI, (5.3)** (page 82): "If $Z \subseteq R(\Gamma)$ is small, $Z' \subseteq Z$,
and $|\Omega \cap V(N(Z'))| <
\omega$, then $Z'$ is small." -/
theorem theorem_5_3 {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    (hS : IsClosedSurface S) [ConnectedSpace S] {k ω : ℕ} {ins : Drawing S → Set S} {Ω : Set S}
    {Z Z' : Set (Set S)} (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω) (hZ : Z ⊆ Γ.R)
    (hsm : IsSmall Γ ins k Ω ω Z) (hZ' : Z' ⊆ Z) (hlt : (Ω ∩ (boundaryDrawing Γ Z').V).ncard < ω) :
    IsSmall Γ ins k Ω ω Z' :=
  theorem_5_3_proof hS hs hw hZ hsm hZ' hlt

/-- **(5.4)** of Graph Minors XI (page 82): "If $(Z_1, Z_2, Z_3)$ is a partition of $R(\Gamma)$,
then one of $Z_1, Z_2, Z_3$ is not
small." -/
theorem theorem_5_4 {S : Type u} [TopologicalSpace S] {Γ : Drawing S} {k ω : ℕ}
    {ins : Drawing S → Set S} {Ω : Set S} [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω) :
    PartitionNotSmall Γ ins k Ω ω :=
  theorem_5_4_proof hS hs hw

/-- **(5.5)** of Graph Minors XI (page 86): "If $Z_1, Z_2, Z_3 \subseteq R(\Gamma)$ are small, then
$Z_1 \cup Z_2 \cup Z_3 \ne
R(\Gamma)$." -/
theorem theorem_5_5 {S : Type u} [TopologicalSpace S] {Γ : Drawing S} {k ω : ℕ}
    {ins : Drawing S → Set S} {Ω : Set S} [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Z₁ Z₂ Z₃ : Set (Set S)} (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω)
    (h₁ : IsSmall Γ ins k Ω ω Z₁) (h₂ : IsSmall Γ ins k Ω ω Z₂) (h₃ : IsSmall Γ ins k Ω ω Z₃) :
    Z₁ ∪ Z₂ ∪ Z₃ ≠ Γ.R :=
  theorem_5_5_proof hS hs hw h₁ h₂ h₃

/-! ## Section 6. Tangles and Slopes -/

open Hypergraph in
/-- **Graph Minors XI, (6.1)** (page 87): "Let $\Gamma$ be a 2-cell painting or drawing in a
connected surface $\Sigma$, with $E(\Gamma) \ne \emptyset$, and let $\Gamma'$ be a radial drawing of
$\Gamma$. For $A \subseteq \Gamma$, let $Z(A)$ denote the set of regions of $\Gamma'$ which include
an edge of $A$. Let $\theta \ge 1$ be an integer, let $\text{ins}$ be a slope in $\Gamma'$ of order
$\theta$, and let $\mathscr{T}$ be the set of all separations $(A, B)$ of $\Gamma$ of order $<
\theta$ such that $Z(A)$ is small with respect to the weighting $(V(\Gamma), \theta)$ of $\Gamma'$.
Then $\mathscr{T}$ is a respectful pretangle in $\Gamma$ and $\text{ins}$ is the slope derived from
it." -/
theorem theorem_6_1 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {Γ : PaintingOrDrawing S} {Γ' : Drawing S} {θ : ℕ} {ins : Drawing S → Set S}
    (hS : IsClosedSurface S) (hE : Γ.E.Nonempty) (hrad : Γ.IsRadialDrawing Γ') (hθ : 1 ≤ θ)
    (hsl : IsSlope Γ' (2 * θ) ins) :
    IsPretangle Γ.toHypergraph θ (inducedPretangle Γ Γ' θ ins) ∧
    Γ.IsRespectful θ (inducedPretangle Γ Γ' θ ins) ∧
    IsDerivedSlope Γ Γ' θ (inducedPretangle Γ Γ' θ ins) ins :=
  theorem_6_1_proof hS hE hrad hθ hsl

open Hypergraph GraphMinor.GM10 in
/-- **Graph Minors XI, (6.2)** (page 89):
"(6.2) *Let $\mathscr{T}$ be a pretangle in a hypergraph $G$, and let $(A, B) \in \mathscr{T}$. Then
there do not exist $(A_1, B_2), \dots, (A_k, B_k) \in \mathscr{T}$ such that
$V(A_i \cap B_i) \subseteq V(A \cap B)$ ($1 \le i \le k$) and $B \subseteq A_1 \cup \cdots \cup
A_k$.*"
(Here $(A_1, B_2)$ in the paper is a misprint for $(A_1, B_1)$.) -/
theorem theorem_6_2 {α : Type u_1} {β : Type u_2} {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsPretangle G θ 𝒯) {A B : Hypergraph α β}
    (hAB : (A, B) ∈ 𝒯) (L : List (Hypergraph α β × Hypergraph α β)) (hL : ∀ p ∈ L, p ∈ 𝒯)
    (hLW : ∀ p ∈ L, (p.1 ∩ p.2).vertexSet ⊆ (A ∩ B).vertexSet)
    (hV : ∀ v ∈ B.vertexSet, ∃ p ∈ L, v ∈ p.1.vertexSet)
    (hE : ∀ e ∈ B.edgeSet, ∃ p ∈ L, e ∈ p.1.edgeSet) : False :=
  GM11.theorem_6_2_proof h𝒯 hAB L hL hLW hV hE

open GraphMinor.GM14 Graph GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XI, (6.3)** (page 89): "Let $\Gamma$ be a 2-cell painting or drawing in a
connected surface $\Sigma$ with $E(\Gamma) \ne \emptyset$, and let $\mathscr{T}$ be a respectful
pretangle in $\Gamma$ of order $\theta \ge 1$. Let $\Gamma'$ be a radial drawing of $\Gamma$, and
let $ins$ be the derived slope. Then for every separation $(A, B)$ of $\Gamma$ of order $< \theta$,
the following are equivalent: (i) $(A, B) \in \mathscr{T}$ (ii) there are circuits $C_1, \dots, C_k$
of $\Gamma'$ with $V(C_i) \cap V(\Gamma) \subseteq V(A \cap B)$ ($1 \le i \le k$), such that every
edge of $A$ is a subset of one of $ins(C_1), \dots, ins(C_k)$. In particular, $\mathscr{T}$ is the
pretangle induced from $ins$." -/
theorem theorem_6_3 (S : Type u) [TopologicalSpace S] [T1Space S] (hS : IsClosedSurface S)
    (hc : ConnectedSpace S) (Γ : PaintingOrDrawing S) (Γ' : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (ins : Drawing S → Set S)
    (h1 : Γ.IsTwoCell) (hE : Γ.E.Nonempty) (hT : IsPretangle Γ.toHypergraph θ T)
    (h2 : Γ.IsRespectful θ T) (hrad : Γ.IsRadialDrawing Γ') (hd : IsDerivedSlope Γ Γ' θ T ins) :
    (∀ A B : Hypergraph S (Set S), Γ.toHypergraph.IsSeparation A B → separationOrder A B < θ →
      ((A, B) ∈ T ↔ ∃ (k : ℕ) (C : Fin k → Drawing S),
        (∀ i : Fin k, (C i).IsCircuit ∧ (C i).IsSubdrawing Γ' ∧ (C i).length < 2 * θ ∧
          (C i).V ∩ Γ.V ⊆ (A ∩ B).vertexSet) ∧ ∀ e ∈ A.edgeSet, ∃ i : Fin k, e ⊆ ins (C i))) ∧ T =
    inducedPretangle Γ Γ' θ ins :=
  GM11.theorem_6_3_proof S hS hc Γ Γ' θ T ins h1 hE hT h2 hrad hd

open Hypergraph in
/-- **Graph Minors XI, (6.4)** (page 90): "Let $\Gamma$ be a 2-cell painting or drawing in a
connected surface $\Sigma$ which is not a sphere, and let $\mathscr{T}$ be a respectful pretangle in
$\Gamma$, of order $\theta \ge 1$. Let $(A, B)$ be a separation of $\Gamma$ of order $< \theta$.
Then the following are equivalent: (i) $(A, B) \in \mathscr{T}$ (ii) $U(A)$ includes no
non-null-homotopic $O$-arc (iii) $U(B) - U(A)$ includes a non-null-homotopic $O$-arc. In particular,
$\mathscr{T}$ is a tangle." -/
theorem theorem_6_4 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] {Γ : PaintingOrDrawing S}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} (hS : IsClosedSurface S)
    (hns : ¬ IsSphere S) (hT2 : Γ.IsTwoCell) (hT : IsPretangle Γ.toHypergraph θ T)
    (hresp : Γ.IsRespectful θ T) :
    (∀ A B : Hypergraph S (Set S), Γ.toHypergraph.IsSeparation A B → separationOrder A B < θ →
    ((A, B) ∈ T ↔ ∀ F : Set S, F ⊆ PaintingOrDrawing.underlying A → IsOArc F → IsNullHomotopicOArc F) ∧
    ((A, B) ∈ T ↔ ∃ F : Set S, IsOArc F ∧
      F ⊆ PaintingOrDrawing.underlying B \ PaintingOrDrawing.underlying A ∧ ¬ IsNullHomotopicOArc F)) ∧
    GM10.IsTangle Γ.toHypergraph θ T :=
  theorem_6_4_proof hS hns hT2 hT hresp

open Hypergraph in
/-- **Graph Minors XI, (6.5)** (pages 91–92): "Let $\Gamma$ be a 2-cell painting or drawing in a
connected surface $\Sigma$ with"

, for a drawing, with the correction for loops at `θ = 2`.

At `θ = 2` the converse fails for a drawing with a loop, so the converse assumes `θ ≠ 2` or that
every edge has two ends. See the correction to (6.5) in `corrections/GM11.md`. -/
theorem theorem_6_5 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {Γ' : Drawing S} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S} {Γ : Drawing S} (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
    (hT : IsPretangle Γ.toHypergraph θ T) (hresp : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hrad : (PaintingOrDrawing.drawing Γ).IsRadialDrawing Γ')
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) Γ' θ T ins) :
    (GM10.IsTangle Γ.toHypergraph θ T → IsEvenSlope Γ' (2 * θ) ins) ∧
    ((θ ≠ 2 ∨ ∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y}) → IsEvenSlope Γ' (2 * θ) ins →
      GM10.IsTangle Γ.toHypergraph θ T) :=
  theorem_6_5_proof hS hE hT hresp hrad hd

open Hypergraph in
/-- **Graph Minors XI, (6.6)** (pages 92–93): "Let $\Gamma$, $\Gamma^*$ be dual 2-cell drawings in a
connected surface, with a common radial drawing $\Gamma'$, and let $\theta \ge 1$ be an integer.
There is a bijection $\mathscr{T} \leftrightarrow \mathscr{T}^*$ between respectful tangles
$\mathscr{T}$ of order $\theta$ in $\Gamma$, and respectful tangles $\mathscr{T}^*$ of order
$\theta$ in $\Gamma^*$, such that for each such $\mathscr{T}$, the slopes in $\Gamma'$ derived from
$\mathscr{T}$ and from $\mathscr{T}^*$ are equal. In particular, $\Gamma$ has a tangle of order
$\theta$ if and only if $\Gamma^*$ does."

, for drawings with a common radial drawing, with the correction for loops at
`θ = 2`: there is a bijection between respectful tangles, and the two sides of it have the same
derived slopes.

At `θ = 2` the bijection fails when a drawing has a loop, so the Lean assumes `θ ≠ 2` or that
neither drawing has a loop. See the correction to (6.6) in `corrections/GM11.md`. -/
theorem theorem_6_6 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {Γ Γs Γ' : Drawing S} {θ : ℕ} (hS : IsClosedSurface S) (hE : Γ.E.Nonempty) (hEs : Γs.E.Nonempty)
    (hrad : (PaintingOrDrawing.drawing Γ).IsRadialDrawing Γ')
    (hrads : (PaintingOrDrawing.drawing Γs).IsRadialDrawing Γ')
    (hloop : θ ≠ 2 ∨ (∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y}) ∧ ∀ e ∈ Γs.E, ∃ x y,
      x ≠ y ∧ closure e ∩ Γs.V = {x, y}) :
    ∃ φ : RespectfulTangle Γ θ ≃ RespectfulTangle Γs θ, ∀ (T : RespectfulTangle Γ θ) (ins : Drawing S → Set S),
    IsDerivedSlope (PaintingOrDrawing.drawing Γ) Γ' θ T.1 ins ↔
      IsDerivedSlope (PaintingOrDrawing.drawing Γs) Γ' θ (φ T).1 ins :=
  theorem_6_6_proof hS hE hEs hrad hrads hloop

/-! ## Section 7. Some Topological Lemmas -/

/-- **(7.1)** of Graph Minors XI (page 93): "If $M$ is a triangulable connected 2-manifold, then any
null-homotopic $O$-arc in $M$ bounds a disc in $M$."
This is D. B. A. Epstein, *Curves on 2-manifolds and isotopies*, Acta Math. 115 (1966) 83–107,
Theorem 1.7; see `GraphMinor.Surface.epstein`. -/
theorem theorem_7_1 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    {F : Set S} (hF : IsOArc F) (hbd : Disjoint F (bd S)) (hn : IsNullHomotopicOArcIn univ F) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F :=
  theorem_7_1_proof hS hF hbd hn

/-- **(7.2)** of Graph Minors XI (page 93): "If $\Sigma$ is a connected surface, $Z \subseteq
\Sigma$, and $F \subseteq Z$ is an $O$-arc
null-homotopic in $Z$, then $F$ bounds a disc $\Delta \subseteq Z$." This is the first part of
Epstein's
theorem. -/
theorem theorem_7_2 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Z F : Set S} (hF : IsOArc F) (hFZ : F ⊆ Z) (hn : IsNullHomotopicOArcIn Z F) :
    ∃ Δ : Set S, Δ ⊆ Z ∧ IsClosedDisc Δ ∧ subBd Δ = F :=
  theorem_7_2_proof hS hF hFZ hn

/-- **(7.3)** of Graph Minors XI (page 93), for closed nice sets: "If $Z \subseteq \Sigma$ is nice
and $\phi \colon S^1 \to Z$ is continuous and not null-homotopic in $Z$, then there is an $O$-arc $F
\subseteq |\phi|$ which is not null-homotopic in $Z$." -/
theorem theorem_7_3 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Z : Set S} (hZ : IsClosed Z) (hZn : IsNice Z) (φ : C(Circle, S))
    (hφ : range φ ⊆ Z) (hnot : ¬ ClosedCurveIsNullHomotopicIn Z φ) :
    ∃ F : Set S, IsOArc F ∧ F ⊆ range φ ∧ ¬ IsNullHomotopicOArcIn Z F :=
  theorem_7_3_proof hS hZ hZn φ hφ hnot

/-- **(7.4)** of Graph Minors XI (page 94), for closed nice sets: "If $\Sigma$ is connected and $X
\subseteq \Sigma$ is nice, then $X$ is simply-connected if
and only if $X$ is arc-wise connected and every $O$-arc $F \subseteq X$ bounds a disc in
$X$." Here
`X` is non-empty, since our simply-connected sets are. -/
theorem theorem_7_4 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {X : Set S} (hc : IsClosed X) (hn : IsGammaNice Γ X)
    (hne : X.Nonempty) :
    IsSimplyConnectedSet X ↔ IsArcConnected X ∧
    ∀ F : Set S, F ⊆ X → IsOArc F → ∃ Δ : Set S, Δ ⊆ X ∧ IsClosedDisc Δ ∧ subBd Δ = F :=
  theorem_7_4_proof hS hc hn hne

/-- **(7.5)** of Graph Minors XI (page 94): "If $\Sigma$ is connected, $X \subseteq \Sigma$ is
closed and nice and $X \ne \Sigma$, and $Y
\subseteq \Sigma$ is finite, and $X \cap Y = \emptyset$, and every $O$-arc in $X$ is
null-homotopic in $\Sigma - Y$, then there is a closed disc $\Delta \subseteq \Sigma - Y$
with $X \subseteq \Delta$." -/
theorem theorem_7_5 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {X Y : Set S} (hXc : IsClosed X) (hXn : IsNice X) (hu : X ≠ univ) (hY : Y.Finite)
    (hXY : Disjoint X Y) (hall : ∀ F : Set S, F ⊆ X → IsOArc F → IsNullHomotopicOArcIn (univ \ Y) F) :
    ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ univ \ Y ∧ X ⊆ Δ :=
  theorem_7_5_proof hS hXc hXn hu hY hXY hall

/-- **(7.6)** of Graph Minors XI (page 94): "If $\Sigma$ is connected, and $X \subseteq \Sigma$ is
closed, nice, and simply-connected,
then $\Sigma - X$ is arc-wise connected." Here `X` is non-empty and `Γ`-nice. -/
theorem theorem_7_6 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {X : Set S} (hXc : IsClosed X) (hXn : IsGammaNice Γ X)
    (hXs : IsSimplyConnectedSet X) (hne : X.Nonempty) : IsArcConnected Xᶜ :=
  theorem_7_6_proof hS hXc hXn hXs hne

/-- **Graph Minors XI, (7.7)** (page 94): "If $\Sigma$ is connected, $X, Y \subseteq \Sigma$ and
$bd(X)$, $bd(Y)$ are both arc-wise
connected, and $X \cap Y \ne \emptyset$, $X \cup Y \ne \Sigma$, and $bd(X) \cap bd(Y) =
\emptyset$, then either $X \subseteq Y$ or $Y \subseteq X$." We assume only that the two boundaries
are preconnected. -/
theorem theorem_7_7 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] {X Y : Set S}
    (hX : IsPreconnected (subBd X)) (hY : IsPreconnected (subBd Y)) (hne : (X ∩ Y).Nonempty)
    (hun : X ∪ Y ≠ univ) (hdisj : Disjoint (subBd X) (subBd Y)) :
    X ⊆ Y ∨ Y ⊆ X :=
  theorem_7_7_proof hX hY hne hun hdisj

/-- **(7.8)** of Graph Minors XI (page 94): "If $X, Y \subseteq \Sigma$ are closed and
simply-connected and $X \cap Y \ne \emptyset$ is
arc-wise connected, then $X \cup Y$ is simply-connected." The hypothesis `hpush` is the
conclusion of (3.1). `theorem_3_1_proof` gives it for a tame intersection, and `nice_31` for nice
sets. -/
theorem theorem_7_8 {S : Type u} [TopologicalSpace S] {X Y : Set S} (hsX : IsSimplyConnectedSet X)
    (hsY : IsSimplyConnectedSet Y) (hL : IsPathConnected (X ∩ Y)) (hpush : CanPush X Y) :
    IsSimplyConnectedSet (X ∪ Y) :=
  theorem_7_8_proof hsX hsY hL hpush

/-- **(7.9)** of Graph Minors XI (page 95): "If $\Sigma$ is connected, $X, Y \subseteq \Sigma$ are
simply-connected, and $X \cap Y \ne
\emptyset$ is arc-wise connected and nice, and $X \cup Y \ne \Sigma$, then $X \cap Y$ is
simply-connected." We ask that
`X ∩ Y` be closed, for `nice_73`. -/
theorem theorem_7_9 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {X Y : Set S} (hXs : IsSimplyConnectedSet X) (hYs : IsSimplyConnectedSet Y)
    (hc : IsClosed (X ∩ Y)) (hn : IsGammaNice Γ (X ∩ Y)) (hp : IsPathConnected (X ∩ Y))
    (hu : X ∪ Y ≠ univ) : IsSimplyConnectedSet (X ∩ Y) :=
  theorem_7_9_proof hS hXs hYs hc hn hp hu

/-- **Graph Minors XI, (7.10)** (page 95): "If $X \subseteq \Sigma$ is arc-wise connected, $Y
\subseteq \Sigma$ is closed, $bd(Y)$ is
arc-wise connected, and $\emptyset \ne bd(Y) \subseteq X$, then $X \cap Y$ is arc-wise
connected." -/
theorem theorem_7_10 {S : Type u} [TopologicalSpace S] {X Y : Set S} (hX : IsPathConnected X)
    (hY : IsClosed Y) (hb : IsPathConnected (subBd Y)) (hsub : subBd Y ⊆ X) :
    IsPathConnected (X ∩ Y) :=
  theorem_7_10_proof hX hY hb hsub

/-- **(7.11)** of Graph Minors XI (page 95): "If $X \subseteq \Sigma$ is closed and arc-wise
connected and $Y_1, \dots, Y_r \subseteq
\Sigma$ are closed discs with boundary in $X$, and $Z = X \cup Y_1 \cup \dots \cup Y_r$, and
every continuous $\phi \colon S^1 \to X$ is null-homotopic in $Z$, then every continuous
$\phi \colon S^1 \to Z$ is null-homotopic in $Z$."
We also record that `Z` is arc-wise connected, as the induction shows. The hypothesis `hpush` is the
conclusion of (3.1), for the steps of the paper's induction. -/
theorem theorem_7_11 {S : Type u} [TopologicalSpace S] [T1Space S] (hS : IsClosedSurface S)
    {X : Set S} (hX : IsClosed X) (hp : IsPathConnected X) {L : List (Set S)}
    (hL : ∀ Y ∈ L, IsClosedDisc Y ∧ frontier Y ⊆ X)
    (hpush : ∀ Y L', (Y :: L') <:+ L → IsPathConnected (Y ∩ withDiscs X L') →
      CanPush Y (withDiscs X L'))
    (hnull : ∀ φ : C(Circle, S), range φ ⊆ X → ClosedCurveIsNullHomotopicIn (withDiscs X L) φ) :
    IsSimplyConnectedSet (withDiscs X L) :=
  theorem_7_11_proof hS hX hp hL hpush hnull

/-! ## Section 8. Restraints -/

open OnePoint in
/-- **(8.1)** of Graph Minors XI (page 96), for a collar `h` of a closed, simply-connected, nice set
`X` with
`X ≠ ∅, Σ`: "if $A, B \subseteq X$ are arc-wise connected and $v_{i_1}, v_{i_3} \in A$ and $v_{i_2},
v_{i_4} \in B$, then $A \cap B \ne \emptyset$". Here the points `v_i` are points `h(e^{2π i s_j},
0)` of the circle of the collar. -/
theorem theorem_8_1 {S : Type u} [TopologicalSpace S] [T2Space S] {X A : Set S}
    (hS : IsClosedSurface S) (hA : IsOpenDisc A) (hXA : X ⊆ A) (hXp : IsPathConnected X)
    {h : C(Circle × I, S)} (hinj : InjOn h {p | 0 < p.2})
    (hoff : ∀ p : Circle × I, 0 < p.2 → h p ∉ X) (hbot : ∀ z, h (z, 0) ∈ X) {s₁ s₂ s₃ s₄ : ℝ}
    (h₁₂ : s₁ ≤ s₂) (h₂₃ : s₂ ≤ s₃) (h₃₄ : s₃ ≤ s₄) (h₄₁ : s₄ ≤ s₁ + 1) {P Q : Set S}
    (hP : IsPathConnected P) (hQ : IsPathConnected Q) (hPX : P ⊆ X) (hQX : Q ⊆ X)
    (hP₁ : h (circlePt s₁, 0) ∈ P) (hP₃ : h (circlePt s₃, 0) ∈ P) (hQ₂ : h (circlePt s₂, 0) ∈ Q)
    (hQ₄ : h (circlePt s₄, 0) ∈ Q) : (P ∩ Q).Nonempty :=
  theorem_8_1_proof hS hA hXA hXp hinj hoff hbot h₁₂ h₂₃ h₃₄ h₄₁ hP hQ hPX hQX hP₁ hP₃ hQ₂ hQ₄

/-- **(8.2)** of Graph Minors XI (page 96):
"(8.2) *Let $W_1, W_2, W_3$ be closed walks of $\Gamma$, each of length $<2\theta$. Then there is a
region $r$ of $\Gamma$ with $r \notin \mathrm{ins}(W_1) \cup \mathrm{ins}(W_2) \cup
\mathrm{ins}(W_3)$.*"
(Here $r \notin \dots$ in the paper means $r \not\subseteq \dots$; we prove that $r$ lies in none of
the three, which is what the paper's proof gives.) -/
theorem theorem_8_2 {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {k : ℕ}
    {ins : Drawing S → Set S} [ConnectedSpace S] (hS : IsClosedSurface S) (hs : IsSlope Γ k ins)
    {u₁ u₂ u₃ : S} (W₁ : GraphWalk Γ.toGraph u₁ u₁) (W₂ : GraphWalk Γ.toGraph u₂ u₂)
    (W₃ : GraphWalk Γ.toGraph u₃ u₃) (h₁ : W₁.length < k) (h₂ : W₂.length < k) (h₃ : W₃.length < k) :
    ∃ r ∈ Γ.R, ¬ r ⊆ insWalk ins Γ W₁ ∧ ¬ r ⊆ insWalk ins Γ W₂ ∧ ¬ r ⊆ insWalk ins Γ W₃ :=
  theorem_8_2_proof hS hs W₁ W₂ W₃ h₁ h₂ h₃

/-- **(8.3)** of Graph Minors XI (page 97): "If $X \subseteq \Sigma$ is a restraint, then
$\mathrm{ins}(\Gamma \cap bd(X)) = X$." -/
theorem theorem_8_3 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {X : Set S} {ins : Drawing S → Set S} {k : ℕ}
    (hs : IsSlope Γ k ins) (hr : IsRestraint Γ ins k X) :
    insOf ins (Γ.interSet (subBd X)) = X :=
  theorem_8_3_proof hS hs hr

/-- **(8.4)** of Graph Minors XI (page 97): "If $X_1, X_2, X_3$ are restraints then $X_1 \cup X_2
\cup X_3 \ne \Sigma$." -/
theorem theorem_8_4 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {ins : Drawing S → Set S} {k : ℕ}
    (hs : IsSlope Γ k ins) {X₁ X₂ X₃ : Set S} (h₁ : IsRestraint Γ ins k X₁)
    (h₂ : IsRestraint Γ ins k X₂) (h₃ : IsRestraint Γ ins k X₃) : X₁ ∪ X₂ ∪ X₃ ≠ univ :=
  theorem_8_4_proof hS hs h₁ h₂ h₃

/-- **(8.5)** of Graph Minors XI (page 97): "Let $W$ be a closed walk in $\Gamma$ of length $<
2\theta$. Then $\mathrm{ins}(W)$ is a
restraint and $l(\mathrm{ins}(W)) \le l(W)$." -/
theorem theorem_8_5 {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {k : ℕ}
    {ins : Drawing S → Set S} [ConnectedSpace S] (hS : IsClosedSurface S) (hs : IsSlope Γ k ins)
    {u : S} (W : GraphWalk Γ.toGraph u u) (hW : W.length < k) :
    IsRestraint Γ ins k (insWalk ins Γ W) ∧ perimeterWalkLength Γ (insWalk ins Γ W) ≤ W.length :=
  theorem_8_5_proof hS hs W hW

/-- **(8.6)** of Graph Minors XI (page 97): "If $X, Y$ are restraints, and $X \cup Y$ is
simply-connected and $l(X \cup Y) < 2\theta$,
then $X \cup Y$ is a restraint." -/
theorem theorem_8_6 {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {k : ℕ}
    {ins : Drawing S → Set S} [ConnectedSpace S] (hS : IsClosedSurface S) (hs : IsSlope Γ k ins)
    {X Y : Set S} (hX : IsRestraint Γ ins k X) (hY : IsRestraint Γ ins k Y)
    (hsc : IsSimplyConnectedSet (X ∪ Y)) (hl : perimeterWalkLength Γ (X ∪ Y) < k) :
    IsRestraint Γ ins k (X ∪ Y) :=
  theorem_8_6_proof hS hs hX hY hsc hl

/-- **(8.7)** of Graph Minors XI (page 98): "Let $X$ be an extreme restraint, and let $a, b \in
V(\Gamma \cap bd(X))$ be distinct. Let
$P$ be a walk in $\Gamma$ from $a$ to $b$, such that no edge or internal vertex of $P$ is in
$X$. Then there is a walk of $\Gamma \cap bd(X)$ from $a$ to $b$ which is shorter than $P$." -/
theorem theorem_8_7 {S : Type u} [TopologicalSpace S] {Γ : Drawing S} [T2Space S] {k : ℕ}
    {ins : Drawing S → Set S} [ConnectedSpace S] (hS : IsClosedSurface S) (hs : IsSlope Γ k ins)
    {X : Set S} (hX : IsExtremeRestraint Γ ins k X) {a b : S} (ha : a ∈ (Γ.interSet (subBd X)).V)
    (hb : b ∈ (Γ.interSet (subBd X)).V) (hab : a ≠ b) (P : GraphWalk Γ.toGraph a b)
    (hPe : ∀ e ∈ P.edges, ¬ e ⊆ X) (hPv : ∀ x ∈ P.support, x ∈ X → x = a ∨ x = b) :
    ∃ R : GraphWalk (Γ.interSet (subBd X)).toGraph a b, R.length < P.length :=
  theorem_8_7_proof hS hs hX ha hb hab P hPe hPv

/-- **(8.8)** of Graph Minors XI (page 98): "If $X_1, X_2$ are extreme restraints and $X_1 \cap X_2
\ne \emptyset$ then $X_1 \cap X_2$
and $X_1 \cup X_2$ are simply-connected." -/
theorem theorem_8_8 {S : Type u} [TopologicalSpace S] {Γ : Drawing S} [T2Space S] [ConnectedSpace S]
    {k : ℕ} {ins : Drawing S → Set S} (hS : IsClosedSurface S) (hs : IsSlope Γ k ins)
    {X₁ X₂ : Set S} (h₁ : IsExtremeRestraint Γ ins k X₁) (h₂ : IsExtremeRestraint Γ ins k X₂)
    (hne : (X₁ ∩ X₂).Nonempty) :
    IsSimplyConnectedSet (X₁ ∩ X₂) ∧ IsSimplyConnectedSet (X₁ ∪ X₂) :=
  theorem_8_8_proof hS hs h₁ h₂ hne

/-- **(8.9)** of Graph Minors XI (page 100): "Let $a, b \in \Sigma$, let $X'$ be an $a, b$-optimal
restraint, and let $X$ be an extreme
restraint with $a, b \in X$. Then $X' \subseteq X$." -/
theorem theorem_8_9 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ : Drawing S}
    {k : ℕ} {ins : Drawing S → Set S} (hS : IsClosedSurface S) (hs : IsSlope Γ k ins) {a b : S}
    {X X' : Set S} (hX' : IsOptimalRestraint Γ ins k a b X') (hX : IsExtremeRestraint Γ ins k X)
    (ha : a ∈ X) (hb : b ∈ X) : X' ⊆ X :=
  theorem_8_9_proof hS hs hX' hX ha hb

/-- **(8.10)** of Graph Minors XI (page 100): "Let $c \in \Sigma$, let $0 \le k < 2\theta$, and let
$Z$ be the union of all restraints $X$
with $l(X) \le k$ and $c \in X$. Then $Z$ is simply-connected."

The paper's "simply-connected" holds for the empty set, and Mathlib's path-connected sets are not
empty, so the Lean says "$Z$ is empty or simply-connected". The proof is the paper's. -/
theorem theorem_8_10 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {Γ : Drawing S} {k K : ℕ} {ins : Drawing S → Set S} (hS : IsClosedSurface S)
    (hs : IsSlope Γ K ins) (c : S) :
    restraintUnion Γ ins K c k = ∅ ∨ IsSimplyConnectedSet (restraintUnion Γ ins K c k) :=
  theorem_8_10_empty_or hS hs c k

/-- **(8.11)** of Graph Minors XI (page 101): "Let $c \in \Sigma$, let $0 \le k < 2\theta$, and let
$Z$ be the union of all restraints $X$
with $l(X) \le k$ and $c \in X$. Then for any restraint $Y$ with $c \in Y$, if $bd(Y)
\subseteq Z$ then $Y \subseteq Z$." -/
theorem theorem_8_11 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {Γ : Drawing S} {k K : ℕ} {ins : Drawing S → Set S} (hS : IsClosedSurface S)
    (hs : IsSlope Γ K ins) {c : S} {Y : Set S} (hY : IsRestraint Γ ins K Y) (hc : c ∈ Y)
    (hbd : frontier Y ⊆ restraintUnion Γ ins K c k) : Y ⊆ restraintUnion Γ ins K c k :=
  theorem_8_11_proof hS hs hY hc hbd

/-- **(8.12)** of Graph Minors XI (page 102): "If $c \in \Sigma$, there is a region $r$ of $\Gamma$
such that there is no restraint $X$
with $c \in X$ and $r \subseteq X$." -/
theorem theorem_8_12 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {Γ : Drawing S} {K : ℕ} {ins : Drawing S → Set S} (hS : IsClosedSurface S)
    (hs : IsSlope Γ K ins) (c : S) :
    ∃ r ∈ Γ.R, ∀ X : Set S, IsRestraint Γ ins K X → ¬ (c ∈ X ∧ r ⊆ X) :=
  theorem_8_12_proof hS hs c

/-- **(8.13)** of Graph Minors XI (page 103): "Let $a, b \in \Sigma$ with $\{a, b\} \cap U(\Gamma)
\subseteq V(\Gamma)$; and let $X$ be a
restraint with $a, b \in X$. Suppose that there is no restraint $Y$ with $X \subseteq Y$ and
$l(Y) < l(X)$. Then $X$ includes an $a, b$-optimal restraint."

The paper subdivides the edges, so that `X` becomes extreme in the new drawing, and applies (8.9)
there. There is a
shorter proof, in which `{a, b} ∩ U(Γ) ⊆ V(Γ)` is not used. Let `E` be an extreme `a, b`-optimal
restraint. The proof
of (8.8) needs that one of the two restraints is extreme, and of the other only what we know of `X`
(`simplyConnected_inter_union`). Then `l(X ∪ E) + l(X ∩ E) ≤ l(X) + l(E)` and `l(X) ≤ l(X ∪ E)`, and
so `X ∩ E` is
`a, b`-optimal. -/
theorem theorem_8_13 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {Γ : Drawing S} {k : ℕ} {ins : Drawing S → Set S} (hS : IsClosedSurface S)
    (hs : IsSlope Γ k ins) {a b : S} {X : Set S} (hX : IsRestraint Γ ins k X) (ha : a ∈ X)
    (hb : b ∈ X)
    (hmax : ∀ Y : Set S, IsRestraint Γ ins k Y → X ⊆ Y → ¬ perimeterWalkLength Γ Y <
      perimeterWalkLength Γ X) :
    ∃ Y : Set S, Y ⊆ X ∧ IsOptimalRestraint Γ ins k a b Y :=
  theorem_8_13_proof hS hs hX ha hb hmax

/-! ## Section 9. The Distance Function -/

open GraphMinor.GM14 (IsCorrespondingAtom tangleMetric HasTangleMetric) in
/-- **(9.1)** of Graph Minors XI (page 104): "If $a, b, c \in A(\Gamma)$ then $d(a, b) + d(b, c) \ge
d(a, c)$." Here
`twiceDistance` is `2d`.

The Lean states the triangle inequality as printed. -/
theorem theorem_9_1 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ : Drawing S}
    {K : ℕ} {ins : Drawing S → Set S} (hS : IsClosedSurface S) (hs : IsSlope Γ K ins)
    {a b c : Set S} (hb : b.Nonempty) :
    twiceDistance Γ ins K a c ≤ twiceDistance Γ ins K a b + twiceDistance Γ ins K b c :=
  GM11.theorem_9_1_proof hS hs hb

/-- **(9.2)** of Graph Minors XI (page 105): "Let $a, b \in A(\Gamma)$ and let $Y$ be a restraint
with $a, b \subseteq Y$. Then there is a
tie $X$ with $a, b \subseteq X \subseteq Y$ and $l(X) \le l(Y)$." -/
theorem theorem_9_2 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ : Drawing S}
    {ins : Drawing S → Set S} {k : ℕ} {Y : Set S} (hS : IsClosedSurface S) (hs : IsSlope Γ k ins)
    {a b : Set S} (ha : a ∈ Γ.A) (hb : b ∈ Γ.A) (hY : IsRestraint Γ ins k Y) (haY : a ⊆ Y)
    (hbY : b ⊆ Y) :
    ∃ X, IsTie Γ ins k X ∧ a ⊆ X ∧ b ⊆ X ∧ X ⊆ Y ∧
    perimeterWalkLength Γ X ≤ perimeterWalkLength Γ Y :=
  theorem_9_2_proof hS hs ha hb hY haY hbY

end GraphMinor.GM11
