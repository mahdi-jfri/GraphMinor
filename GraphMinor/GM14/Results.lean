module

public import GraphMinor.GM14.Adapted
public import GraphMinor.GM14.Form84
public import GraphMinor.GM14.Section10
public import GraphMinor.GM14.Section3
public import GraphMinor.GM14.Section3b
public import GraphMinor.GM14.Section5
public import GraphMinor.GM14.Section6
public import GraphMinor.GM14.Section6a
public import GraphMinor.GM14.Section6c
public import GraphMinor.GM14.Section7
public import GraphMinor.GM14.Section7a
public import GraphMinor.GM14.Section7b
public import GraphMinor.GM14.Section8
public import GraphMinor.GM14.Section83Proof
public import GraphMinor.GM14.Section8Core
public import GraphMinor.GM14.Section8a
public import GraphMinor.GM14.Section9
public import GraphMinor.GM14.Section9a
public import GraphMinor.GM14.Section9b
public import GraphMinor.GM15.Cited
public import GraphMinor.GM16.Cited

/-!
# Graph Minors XIV: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser.
B **65** (1995), 23–50.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. The docstrings say where the Lean differs from the print, and
`corrections/GM14.md` lists the corrections to the paper.
-/

public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor GraphMinor.Surface

universe u v w

/-! ## Section 1. Introduction -/

open GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XIV, (1.1)** (pages 24–25):
"Let $G$ be a 4-connected graph, and let $H$ be a subgraph of $G$ which is a subdivision of a
simple 3-connected graph. Let $\Sigma$ be a connected surface without boundary, not a
sphere, and let $H$ be drawn in $\Sigma$. Suppose that every closed curve in $\Sigma$ that
meets $H$ at most 208 times is null-homotopic. For such a curve $\phi$, let
$\operatorname{ins}(\phi)$ denote the union of the points of $\Sigma$ appearing in $\phi$
together with all discs in $\Sigma$ with boundary in this set. Then either* (i) *the drawing
of $H$ can be extended to one of $G$, or* (ii) *there is a path of $G$ with distinct ends
$u, v \in V(H)$ and with no other vertex or edge in $H$, such that there is no closed curve
$\phi$ meeting $H$ at most 3 times with $u, v \in \operatorname{ins}(\phi)$, or* (iii)
*there is a circuit $C$ of $H$ bounding an open disc $\Lambda \subseteq \Sigma$, and a point
$x$ of $\Lambda$, and four vertices $a, b, c, d$ of $C$ in order, such that* ... (i) *$H \cap
(\Sigma - \Lambda)$ is a subdivision of a simple 3-connected graph* (ii) *for every $y \in
\Lambda$ there is a closed curve $\phi$ meeting $H$ at most 39 times, with $\{x, y\}
\subseteq \operatorname{ins}(\phi)$* (iii) *$\operatorname{bd}(\Delta) - \Lambda$ meets $H$
at least 4 times, for every closed disc $\Delta \subseteq \Sigma$ with $a, b, c, d \in
\Delta$, and* (iv) *there are two disjoint paths of $G$ with ends $a, c$ and $b, d$ each
meeting $H$ only within $\Lambda \cup \{a, b, c, d\}$." -/
theorem theorem_1_1 {S : Type u} [TopologicalSpace S] [T2Space S] {α : Type v} {β : Type w}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hnot_sphere : ¬ IsSphere S) (G : Graph α β)
    (H : Drawing S) (η : SpanEmbedding H G) (hV_fin : V(G).Finite) (hE_fin : E(G).Finite)
    (hG_4conn : 5 ≤ V(G).ncard ∧ ∀ G₁ G₂ : Graph α β, IsGraphSeparation G G₁ G₂ →
      (V(G₁) ∩ V(G₂)).ncard < 4 → V(G₁) = V(G) ∨ V(G₂) = V(G))
    (hH_subdiv : IsSubdivisionOfSimpleThreeConnected η.imageGraph) (hrep : H.IsRepresentative 209) :
    -- `(i)` The drawing of `H` can be extended to one of `G`, OR
    (∃ (Γ_G : GraphDrawing G S), H.IsSubdrawing Γ_G.drawing) ∨
    -- `(ii)` There is an `H`-path in `G` whose ends are not enclosed by any closed curve meeting
    -- `H` at most 3 times, OR
    (∃ (P_G : Graph α β) (u_H v_H : S),
      u_H ∈ H.V ∧ v_H ∈ H.V ∧
      IsHPathWithEnds G η.imageGraph P_G (η.vMap u_H) (η.vMap v_H) ∧
      ¬ ∃ φ : C(Circle, S),
        (range φ ∩ H.U).encard ≤ 3 ∧ u_H ∈ curveIns φ ∧ v_H ∈ curveIns φ) ∨
    -- `(iii)` There is an eye configuration `(C, Λ₀, x, a, b, c, d)` satisfying `(iii)(i)–(iv)`:
    (∃ (C : Drawing S) (Λ₀ : Set S) (x : S) (a b c d_v : S) (P₁ P₂ : Graph α β),
      C.IsCircuit ∧ C.IsSubdrawing H ∧ IsOpenDisc Λ₀ ∧ subBd Λ₀ = C.U ∧ x ∈ Λ₀ ∧
      a ∈ C.V ∧ b ∈ C.V ∧ c ∈ C.V ∧ d_v ∈ C.V ∧
      OccurInCircuitOrder C a b c d_v ∧
      IsSubdivisionOfSimpleThreeConnected (clearedSubdrawing H Λ₀).toGraph ∧
      (∀ y ∈ Λ₀, ∃ φ : C(Circle, S),
        (range φ ∩ H.U).encard ≤ 39 ∧ x ∈ curveIns φ ∧ y ∈ curveIns φ) ∧
      (∀ Δ : Set S, IsClosedDisc Δ → ({a, b, c, d_v} : Set S) ⊆ Δ →
        4 ≤ ((subBd Δ \ Λ₀) ∩ H.U).encard) ∧
      Disjoint V(P₁) V(P₂) ∧
      IsGraphPathWithEnds G P₁ (η.vMap a) (η.vMap c) ∧
      IsGraphPathWithEnds G P₂ (η.vMap b) (η.vMap d_v)) :=
  GM14.theorem_1_1_proof hS hConn hnot_sphere G H η hV_fin hE_fin hG_4conn hH_subdiv hrep

/-! ## Section 2. Surfaces -/

/-! ## Section 3. Tangles -/

open GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XIV, (3.1)** (page 28):
"If $W$ is a closed walk of $K$ with length $<2\theta$ (so that $ins(W)$ is defined), and $x
\in A(H)$, and $x'$ is the corresponding atom of $K$, then $x' \subseteq ins(W)$ if and only
if $x \cap ins(W) \ne \emptyset$." -/
theorem theorem_3_1 {S : Type u} [TopologicalSpace S] [T1Space S] {H K : Drawing S}
    (hS : IsClosedSurface S) (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins) {x x' : Set S}
    (hx : IsCorrespondingAtom H K x x') {u : S} (W : GraphWalk K.toGraph u u)
    (hl : W.length < 2 * θ) :
    x' ⊆ insWalk ins K W ↔ (x ∩ insWalk ins K W).Nonempty :=
  GM14.theorem_3_1_proof hS hK hd hx W hl

open GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XIV, (3.2)** (page 28):
"If $\theta \ge 4\lambda + 3$ then there is a unique tangle of order $\theta - 4\lambda - 2$
obtained by clearing $\Lambda$." -/
theorem theorem_3_2 {S : Type u} [TopologicalSpace S] [T1Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {H : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ} {z Λ : Set S}
    (hθ : 4 * lam + 3 ≤ θ) (hMetric : HasTangleMetric H θ T d)
    (hZone : IsLambdaZoneAround H d lam z Λ) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ),
    IsClearedTangle H T d θ lam Λ T' d' ∧
    ∀ (T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d'' : Set S → Set S → ℕ),
      IsClearedTangle H T d θ lam Λ T'' d'' → T'' = T' :=
  GM14.theorem_3_2_proof hS hConn hθ hMetric hZone

/-! ## Section 4. Statement of the Theorem -/

open GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XIV, (4.1)** (page 30):
"Let $H$ be a 2-cell rigid drawing in a surface $\Sigma$, and let $\mathscr{T}$ be a
respectful tangle in $H$ of order $\theta \ge 209$ with metric $d$. Let $H$ be a subgraph of
$G$, and suppose that* (i) *$d(u, v) \le 3$ for every $H$-path in $G$ with ends $u, v$, and*
(ii) *if $\mathscr{T}'$ is the tangle of order $\theta - 158$ obtained by clearing some
39-zone $\Lambda$ such that $H \cap (\Sigma - \Lambda)$ is a rigid drawing in $\Sigma$, then
$\Lambda$ is not an eye of $H \cap (\Sigma - \Lambda)$ in $G$ with respect to
$\mathscr{T}'$.* *Then there is a $\mathscr{T}$-local 3-segregation of $G$ and an
arrangement of it in $\Sigma$ compatible with $H$."

Proved by setting `β = 12` in `(10.1)` (`theorem_10_1_proof`), since `16 * 12 + 17 = 209`,
`3 * 12 + 3 = 39`, `4 * 39 + 2 = 158`, and `3 < 12`. -/
theorem theorem_4_1 {S : Type u} [TopologicalSpace S] [T2Space S] {α : Type v} {β : Type w}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (G : Graph α β) (H : Drawing S)
    (η : SpanEmbedding H G) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (θ : ℕ) (hV_fin : V(G).Finite) (hE_fin : E(G).Finite)
    (h2cell : H.IsTwoCell) (hrigid : IsRigid H) (hT : IsRespectfulDrawingTangle H θ T)
    (hmetric : HasTangleMetric H θ T d) (hθ : 209 ≤ θ)
    (hi_path : ∀ (P : Graph α β) (u v : S), u ∈ H.V → v ∈ H.V →
      IsHPathWithEnds G η.imageGraph P (η.vMap u) (η.vMap v) → d {u} {v} ≤ 3)
    (hii_no_eye : ∀ (Λ : Set S) (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (η_cl : SpanEmbedding (clearedSubdrawing H Λ) G),
      IsLambdaZone H d 39 Λ → IsRigid (clearedSubdrawing H Λ) → IsClearedTangle H T d θ 39 Λ T' d' →
      (∀ v ∈ (clearedSubdrawing H Λ).V, η_cl.vMap v = η.vMap v) →
      (∀ e ∈ (clearedSubdrawing H Λ).E, η_cl.eMap e = η.eMap e) →
      ¬ IsDrawingEye G (clearedSubdrawing H Λ) η_cl (θ - 158) T' Λ) :
    ∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S),
    IsThreeSegregation G S_seg ∧ IsTangleLocal G H η T S_seg ∧
    IsSurfaceArrangement S_seg α_disc α_pt ∧ IsCompatibleWith G H η S_seg α_disc α_pt :=
  GM14.theorem_4_1_proof hS hConn G H η T d θ hV_fin hE_fin h2cell hrigid hT hmetric hθ hi_path hii_no_eye

/-! ## Section 5. Circuits in Cylinders -/

open Function GraphMinor.GM11 in
/-- **Graph Minors XIV, (5.1)** (page 31):
"Let $H$ be a drawing in a surface $\Sigma$, and let $\Delta \subseteq \Sigma$ be a closed
disc. Let $\mathscr{R}$ be a non-empty connected set of regions of $H$, such that $r
\subseteq \Delta - \text{bd}(\Delta)$ for all $r \in \mathscr{R}$. Then there is a circuit
$C$ of $H$ with $U(C) \subseteq \Delta$, bounding a disc in $\Delta$ including each member
of $\mathscr{R}$, and such that every edge of $C$ is incident with a member of
$\mathscr{R}$." -/
theorem theorem_5_1 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ : Set S} (hΔ : IsClosedDisc Δ) {R_set : Set (Set S)} (hne : R_set.Nonempty)
    (hconn : IsConnectedRegionSet H R_set) (hsub : ∀ r ∈ R_set, r ⊆ Δ \ subBd Δ) :
    ∃ (C : Drawing S) (Λ : Set S),
    C.IsSubdrawing H ∧ C.IsCircuit ∧ C.U ⊆ Δ ∧
    IsOpenDisc Λ ∧ closure Λ ⊆ Δ ∧ IsClosedDisc (closure Λ) ∧
    subBd Λ = C.U ∧ subBd (closure Λ) = C.U ∧ closure Λ \ C.U = Λ ∧
    (∀ r ∈ R_set, r ⊆ Λ) ∧
    ∀ e ∈ C.E, ∃ r ∈ R_set, H.EdgeRegionIncident e r :=
  GM14.theorem_5_1_proof hS H hΔ hne hconn hsub

open Function GraphMinor.GM11 in
/-- **Graph Minors XIV, (5.2)** (page 31), cited in Graph Minors XIX (Section 7, page 344):
"(5.2) *Let $H$ be a drawing in $\Sigma$, and let $\Delta \subseteq \Sigma$ be a closed disc.
Let $Z \subseteq \Delta - \text{bd}(\Delta)$ be non-empty and arc-wise connected, and such
that $r \subseteq \Delta - \text{bd}(\Delta)$ for every region $r$ of $H$ with $\bar{r} \cap
Z \ne \emptyset$. Then there is a circuit $C$ of $H$ with $U(C) \subseteq \Delta$, bounding
an open disc in $\Delta$ including $Z$, such that every edge of $C$ is incident with a
region $r$ of $H$ satisfying $\bar{r} \cap Z \ne \emptyset$." -/
theorem theorem_5_2 (S : Type u) [TopologicalSpace S] [T1Space S] (hS : IsClosedSurface S)
    (hconnS : ConnectedSpace S) (H : Drawing S) (Δ Z : Set S) (hΔ : IsClosedDisc Δ)
    (h1 : Z ⊆ Δ \ subBd Δ) (hZne : Z.Nonempty) (hZconn : IsArcConnected Z)
    (hsub : ∀ r ∈ H.R, (closure r ∩ Z).Nonempty → r ⊆ Δ \ subBd Δ) :
    ∃ (C : Surface.Drawing S) (Λ : Set S), C.IsSubdrawing H ∧ C.IsCircuit ∧ C.U ⊆ Δ ∧ IsOpenDisc Λ ∧
    Λ ⊆ Δ ∧ subBd Λ = C.U ∧ Z ⊆ Λ ∧ ∀ e ∈ C.E, ∃ r ∈ H.R, H.EdgeRegionIncident e r ∧
    (closure r ∩ Z).Nonempty :=
  GM14.theorem_5_2_proof S hS hconnS H Δ Z hΔ h1 hZne hZconn hsub

open Function GraphMinor.GM11 in
/-- **Graph Minors XIV, (5.3)** (page 32):
"Let $H$ be a drawing in $\Sigma$, and let $\Delta \subseteq \Sigma$ be a closed disc. Let $Z
\subseteq \Delta - \text{bd}(\Delta)$ be non-empty and arc-wise connected, such that the
regional distance between $Z$ and $\Sigma - \Delta$ is $\ge k \ge 2$. Then there is a
circuit $C$ of $H$ with $U(C) \subseteq \Delta$, bounding an open disc $\Lambda$ including
$Z$, such that the regional distance between $\bar{\Lambda}$ and $\Sigma - \Delta$ is $\ge k
- 1$." -/
theorem theorem_5_3 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ Z : Set S} (hΔ : IsClosedDisc Δ) (_hZ : Z ⊆ Δ \ subBd Δ) (hZne : Z.Nonempty)
    (hZconn : IsArcConnected Z) {k : ℕ} (hk2 : 2 ≤ k) (hdist : k ≤ regionalDistance H Z (univ \ Δ)) :
    ∃ (C : Drawing S) (Λ : Set S),
    C.IsSubdrawing H ∧ C.IsCircuit ∧ C.U ⊆ Δ ∧
    IsOpenDisc Λ ∧ closure Λ ⊆ Δ ∧ IsClosedDisc (closure Λ) ∧ subBd Λ = C.U ∧
    Z ⊆ Λ ∧ k - 1 ≤ regionalDistance H (closure Λ) (univ \ Δ) :=
  GM14.theorem_5_3_proof hS H hΔ _hZ hZne hZconn hk2 hdist

open Function GraphMinor.GM11 in
/-- **Graph Minors XIV, (5.4)** (page 32):
"Let $H, \Sigma, \Delta, Z, k$ be as in (5.3). Then there are mutually disjoint circuits
$C_1, \dots, C_{k-1}$ of $H$ with $U(C_1), \dots, U(C_{k-1}) \subseteq \Delta$, all bounding
open discs including $Z$." -/
theorem theorem_5_4 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ Z : Set S} (hΔ : IsClosedDisc Δ) (_hZ : Z ⊆ Δ \ subBd Δ) (hZne : Z.Nonempty)
    (hZconn : IsArcConnected Z) {k : ℕ} (hk2 : 2 ≤ k) (hdist : k ≤ regionalDistance H Z (univ \ Δ)) :
    ∃ (C : Fin (k - 1) → Drawing S) (Λ : Fin (k - 1) → Set S),
    (∀ i : Fin (k - 1), (C i).IsSubdrawing H ∧ (C i).IsCircuit ∧ (C i).U ⊆ Δ ∧
      IsOpenDisc (Λ i) ∧ closure (Λ i) ⊆ Δ ∧ subBd (Λ i) = (C i).U ∧ Z ⊆ Λ i) ∧
    (∀ i j : Fin (k - 1), i < j → closure (Λ i) ⊆ Λ j) ∧
    Pairwise (fun i j => Disjoint (C i).U (C j).U) :=
  GM14.theorem_5_4_proof hS H hΔ _hZ hZne hZconn hk2 hdist

open Function GraphMinor.GM11 in
/-- **Graph Minors XIV, (5.5)** (page 32):
"Let $H$ be a drawing in $\Sigma$, and let $\Delta \subseteq \Sigma$ be a closed disc. Let $Z
\subseteq \Delta - \text{bd}(\Delta)$ be non-empty and arc-wise connected, such that the
regional distance between $Z$ and $\text{bd}(\Delta)$ is $\ge k \ge 1$. Then there are $k -
1$ mutually disjoint circuits $C_1, \dots, C_{k-1}$ of $H$ with $U(C_1), \dots, U(C_{k-1})
\subseteq \Delta - \text{bd}(\Delta)$, all bounding open discs including $Z$." -/
theorem theorem_5_5 {S : Type u} [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ Z : Set S} (hΔ : IsClosedDisc Δ) (hZ : Z ⊆ Δ \ subBd Δ) (hZne : Z.Nonempty)
    (hZconn : IsArcConnected Z) {k : ℕ} (hk1 : 1 ≤ k) (hdist : k ≤ regionalDistance H Z (subBd Δ)) :
    ∃ (C : Fin (k - 1) → Drawing S) (Λ : Fin (k - 1) → Set S),
    (∀ i : Fin (k - 1), (C i).IsSubdrawing H ∧ (C i).IsCircuit ∧ (C i).U ⊆ Δ \ subBd Δ ∧
      IsOpenDisc (Λ i) ∧ closure (Λ i) ⊆ Δ \ subBd Δ ∧ IsClosedDisc (closure (Λ i)) ∧
      subBd (Λ i) = (C i).U ∧ subBd (closure (Λ i)) = (C i).U ∧
      closure (Λ i) \ (C i).U = Λ i ∧ Z ⊆ Λ i) ∧
    (∀ i j : Fin (k - 1), i < j → closure (Λ i) ⊆ Λ j) ∧
    Pairwise (fun i j => Disjoint (C i).U (C j).U) :=
  GM14.theorem_5_5_proof hS H hΔ hZ hZne hZconn hk1 hdist

/-! ## Section 6. Rigidity -/

open Function Hypergraph unitInterval GraphMinor.GM11 in
/-- **Graph Minors XIV, (6.1)** (page 33):
"Let $H$ be a rigid drawing in a surface $\Sigma$, and let $\Sigma' \subseteq \Sigma$ be a
surface, such that $\text{bd}(\Sigma') \cap U(H) \subseteq V(H)$. Suppose that for every
closed disc $\Delta' \subseteq \Sigma$ with $\Delta' \cap \Sigma' = \text{bd}(\Delta')
\subseteq \text{bd}(\Sigma')$ there is a circuit $C$ of $H$ with $U(C) \subseteq \Delta'$.
Then $H \cap \Sigma'$ is a rigid drawing in $\Sigma'$." -/
theorem theorem_6_1 {S : Type u} [TopologicalSpace S] [T2Space S] {H : Drawing S} {S' : Set S}
    (hRig : IsRigid H) (hS'_cl : IsClosed S') (hbd : subBd S' ∩ H.U ⊆ H.V)
    (hSubsurf : ∀ Δ : Set S, IsClosedDisc Δ → subBd Δ ⊆ S' → ¬ (Δ ⊆ S') → ∃ Δ' : Set S,
      IsClosedDisc Δ' ∧ Δ' ⊆ Δ ∧ Δ' ∩ S' = subBd Δ' ∧ subBd Δ' ⊆ subBd S')
    (hCirc : ∀ Δ' : Set S, IsClosedDisc Δ' → Δ' ∩ S' = subBd Δ' → subBd Δ' ⊆ subBd S' →
      ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing H ∧ C.U ⊆ Δ') :
    IsRigidIn (H.interSet S') S' :=
  GM14.theorem_6_1_proof hRig hS'_cl hbd hSubsurf hCirc

open Function Hypergraph unitInterval GraphMinor.GM11 in
/-- **Graph Minors XIV, (6.2)** (page 33):
"Let $H$ be a rigid drawing in a surface $\Sigma$. Let $v \in V(H)$, and let the regions of
$H$ incident with $v$ be $r_1, \dots, r_k$, enumerated in the cyclic order of their
occurrence around $v$. Then $r_1, \dots, r_k$ are all distinct. Consequently $\bar{r}$ is
simply-connected for every region $r$ of $H$." -/
theorem theorem_6_2 {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {H : Drawing S} (hRig : IsRigid H) :
    (∀ {γ : Set S → I → S} {v : S}, v ∈ H.V →
      ∀ {next : halfEdges H γ v → halfEdges H γ v}
        {ρ P Q : halfEdges H γ v → Set S} {W : Set S} {τ : halfEdges H γ v → I},
        IsSectors H γ v next ρ P W Q τ → Function.Injective ρ) ∧
    (∀ r ∈ H.R, IsArcSimplyConnected r) :=
  GM14.theorem_6_2_proof hS hRig

open Function Hypergraph unitInterval GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIV, (6.3)** (page 33):
"Let $H$ be a rigid drawing in a surface $\Sigma$, and let $\Lambda \subseteq \Sigma$ be an
open disc with $\text{bd}(\Lambda) \subseteq U(H)$ such that $\text{bd}(\Lambda)$ is an
O-arc. Suppose that $\bar{r} \cap \bar{\Lambda}$ is null or connected for every region $r$
of $H$ with $r \cap \Lambda = \emptyset$. Then $H \cap (\Sigma - \Lambda)$ is a rigid
drawing in $\Sigma$." -/
theorem theorem_6_3 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H C : Drawing S} {Λ : Set S} (hRig : IsRigid H)
    (hΛ_open : IsOpenDisc Λ) (hΛ_cl : IsClosedDisc (closure Λ)) (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing H) (hbd : subBd Λ = C.U)
    (hconn : ∀ r ∈ H.R, Disjoint r Λ → IsPreconnected (closure r ∩ closure Λ)) :
    IsRigid (clearedSubdrawing H Λ) :=
  GM14.theorem_6_3_proof hS hRig hΛ_open hΛ_cl hC hCs hbd hconn

open Function GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 in
/-- **Graph Minors XIV, (6.4)** (page 34):
"Let $\Delta$ be a closed disc, let $H_1, H_2$ be drawings in $\Delta$ with $V(H_1) \cap
\text{bd}(\Delta) = V(H_2) \cap \text{bd}(\Delta)$, and let $\phi \colon H_1 \to H_2$ be an
isomorphism such that $\phi(v) = v$ for all $v \in V(H_1) \cap \text{bd}(\Delta)$. If $H_1$ is
rigid in $\Delta$ then there is a homeomorphism $\psi \colon \Delta \to \Delta$ extending $\phi$."
-/
theorem theorem_6_4 {S : Type u} [TopologicalSpace S] [T2Space S] {Δ : Set S} (hΔ : IsClosedDisc Δ)
    (hbdΔ : subBd Δ = discBd Δ) {H₁ H₂ : Drawing S} (hH₁Δ : H₁.U ⊆ Δ) (hH₂Δ : H₂.U ⊆ Δ)
    (hH₁bd : H₁.U ∩ subBd Δ ⊆ H₁.V) (hH₂bd : H₂.U ∩ subBd Δ ⊆ H₂.V)
    (hbdV : H₁.V ∩ subBd Δ = H₂.V ∩ subBd Δ) (φ : Iso H₁.toGraph H₂.toGraph)
    (hφ_bd : ∀ v : V(H₁.toGraph), v.1 ∈ subBd Δ → (φ.vertexEquiv v).1 = v.1)
    (hrigid : ∀ F : Set S, F ⊆ Δ → IsOArc F → F ∩ H₁.U ⊆ H₁.V → (F ∩ H₁.V).ncard ≤ 2 → ∃ Δ' : Set S,
      Δ' ⊆ Δ ∧ IsDial H₁ F Δ') :
    ∃ ψ : S ≃ₜ S,
    ψ '' Δ = Δ ∧
    (∀ v : V(H₁.toGraph), ψ v.1 = (φ.vertexEquiv v).1) ∧
    (∀ e : E(H₁.toGraph), ψ '' e.1 = (φ.edgeEquiv e).1) ∧
    ψ '' H₁.V = H₂.V ∧
    ψ '' H₁.U = H₂.U ∧
    (∀ v ∈ H₁.V ∩ subBd Δ, ψ v = v) ∧
    (∀ x ∈ subBd Δ, ψ x = x) :=
  GM14.theorem_6_4_proof hΔ hbdΔ hH₁Δ hH₂Δ hH₁bd hH₂bd hbdV φ hφ_bd hrigid

open Function GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 in
/-- **Graph Minors XIV, (6.5)** (pages 34–35):
"Let $H$ be a rigid drawing in a closed disc $\Delta$. Let $H$ be a subgraph of $G$, let
$\mathscr{S}$ be a 3-segregation of $G$ with $V(H) \cap \text{bd}(\Delta) \subseteq
V(\mathscr{S})$, and let $\alpha$ be an arrangement of $\mathscr{S}$ in $\Delta$ such that
$\alpha(v) = v$ for all $v \in V(H) \cap \text{bd}(\Delta)$. Then there is an arrangement
$\alpha'$ of $\mathscr{S}$ in $\Delta$ such that $\alpha'$ is compatible with $H$."

The Lean proof corrects a step of the paper's proof. See the correction to the proof of (6.5) in
`corrections/GM14.md`. -/
theorem theorem_6_5 {S : Type u} [TopologicalSpace S] [T2Space S] {α : Type v} {β : Type w}
    {G : Graph α β} {H : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ) (hbdΔ : subBd Δ = discBd Δ)
    (hHΔ : H.U ⊆ Δ) (hHbd : H.U ∩ subBd Δ ⊆ H.V)
    (hrigid : ∀ F : Set S, F ⊆ Δ → IsOArc F → F ∩ H.U ⊆ H.V → (F ∩ H.V).ncard ≤ 2 → ∃ Δ' : Set S,
      Δ' ⊆ Δ ∧ IsDial H F Δ') (η : SpanEmbedding H G) {S_seg : Set (Society α β)}
    (hseg : IsThreeSegregation G S_seg)
    (hbd_in_seg : ∀ v ∈ H.V ∩ subBd Δ, η.vMap v ∈ segregationVertices S_seg)
    {α_disc : Society α β → Set S} {α_pt : α → S} (harr : IsSurfaceArrangement S_seg α_disc α_pt)
    (harr_Δ : ∀ S₀ ∈ S_seg, α_disc S₀ ⊆ Δ) (hα_id : ∀ v ∈ H.V ∩ subBd Δ, α_pt (η.vMap v) = v)
    (hα_bd : ∀ v ∈ H.V, η.vMap v ∈ segregationVertices S_seg → α_pt (η.vMap v) ∈ subBd Δ →
      v ∈ subBd Δ) :
    ∃ (α'_disc : Society α β → Set S) (α'_pt : α → S),
    IsSurfaceArrangement S_seg α'_disc α'_pt ∧
    (∀ S₀ ∈ S_seg, α'_disc S₀ ⊆ Δ) ∧
    IsCompatibleWith G H η S_seg α'_disc α'_pt ∧
    (∀ x, α_pt x ∈ subBd Δ → α'_pt x = α_pt x) ∧
    (∀ x, α_pt x ∈ Δ \ subBd Δ → α'_pt x ∈ Δ \ subBd Δ) ∧
    (∀ S₀ ∈ S_seg, α'_disc S₀ ∩ subBd Δ = α_disc S₀ ∩ subBd Δ) :=
  GM14.theorem_6_5_proof hΔ hbdΔ hHΔ hHbd hrigid η hseg hbd_in_seg harr harr_Δ hα_id hα_bd

/-! ## Section 7. Distance and Freedom -/

open GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XIV, (7.1)** (page 35):
"Let $H$ be a 2-cell drawing with $|E(H)| \ge 2$ in a surface $\Sigma$, and let $\mathscr{T}$
be a respectful tangle in $H$ of order $\theta \ge 1$, with metric $d$. Then for every $z
\in A(H)$ there exists $e \in E(H)$ with $d(z, e) = \theta$." -/
theorem theorem_7_1 {S : Type u} [TopologicalSpace S] [T1Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric H θ T d) (hE2 : 2 ≤ H.E.ncard) {z : Set S} (hz : z ∈ H.A) :
    ∃ e ∈ H.E, d z e = θ :=
  GM14.theorem_7_1_proof hS hConn hMetric hE2 hz

open GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XIV, (7.2)** (page 36):
"Let $H$ be a 2-cell drawing in $\Sigma$ with $E(H) \ne \emptyset$, and let $\mathscr{T}$ be
a respectful tangle in $H$. Let $K$ be a radial drawing of $H$, and let $(A, B) \in
\mathscr{T}$. Then for every edge $e$ of $A$ there is a circuit $D$ of $K$ with $V(D) \cap
V(H) \subseteq V(A \cap B)$ and with $e \subseteq ins(D)$." -/
theorem theorem_7_2 {S : Type u} [TopologicalSpace S] [T1Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    {A B : Hypergraph S (Set S)} {e : Set S} (hE : H.E.Nonempty)
    (hResp : IsRespectfulDrawingTangle H θ T) (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins) (hAB : (A, B) ∈ T)
    (he : e ∈ A.edgeSet) :
    ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing K ∧ D.length < 2 * θ ∧
    D.V ∩ H.V ⊆ (A ∩ B).vertexSet ∧ e ⊆ ins D :=
  GM14.theorem_7_2_proof hS hConn hE hResp hK hd hAB he

open GraphMinor.GM15 GraphMinor.GM10 GraphMinor.GM11 Hypergraph Function SimpleGraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XIV, (7.3)** (page 36), proving `GM15.GM14Theorem73Statement`:
"Let $H$ be a 2-cell drawing in $\Sigma$ with $E(H) \ne \emptyset$, and let $\mathscr{T}$ be
a respectful tangle in $H$ of order $\theta$, with metric $d$. Let $z \in A(H)$, and let
$(A, B) \in \mathscr{T}$ with $E(B) \ne \{z\}$. Then there exists $e \in E(B)$ with $d(z, e)
\ge \theta - |V(A \cap B)|$."

The Lean proof corrects a step of the paper's proof. See the correction to the proof of (7.3) in
`corrections/GM14.md`. -/
theorem theorem_7_3 {S : Type u} [TopologicalSpace S] [T2Space S] (H : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (A B : Hypergraph S (Set S)) (z : Set S) (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hE : H.E.Nonempty) (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A) (hAB₀ : (A, B) ∈ T)
    (hBz₀ : B.edgeSet ≠ {z}) : ∃ e ∈ B.edgeSet, θ - separationOrder A B ≤ d z e :=
  GM14.theorem_7_3_proof H θ T d A B z hS hConn hE hMetric hz hAB₀ hBz₀

open GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XIV, (7.4)** (page 36):
"Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in
$H$. Let $K$ be a radial drawing of $H$, let $(A, B) \in \mathscr{T}$, and let $C$ be a
circuit of $A$ with $|V(B \cap C)| \le 1$. Then there is a circuit $D$ of $K$ with $V(D)
\cap V(H) \subseteq V(A \cap B)$ and $U(C) \subseteq ins(D)$." -/
theorem theorem_7_4 {S : Type u} [TopologicalSpace S] [T1Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {H K C : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    {A B : Hypergraph S (Set S)} (hResp : IsRespectfulDrawingTangle H θ T)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins) (hAB : (A, B) ∈ T)
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing H) (hCA : C.V ⊆ A.vertexSet ∧ C.E ⊆ A.edgeSet)
    (hBC : (B.vertexSet ∩ C.V).ncard ≤ 1) :
    ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing K ∧ D.length < 2 * θ ∧
    D.V ∩ H.V ⊆ (A ∩ B).vertexSet ∧ C.U ⊆ ins D :=
  GM14.theorem_7_4_proof hS hConn hResp hK hd hAB hC hCs hCA hBC

open GraphMinor.GM16 GraphMinor.GM10 GraphMinor.GM11 Hypergraph Function SimpleGraph GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XIV, (7.5)** (pages 36–37), proving `GM16.GM14Theorem75Statement`:
"Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in $H$ of
order $\theta$. Let $\lambda \ge 0$ be an integer, and let $\Lambda \subseteq \Sigma$ be an
$\lambda$-zone. Let $K$ be ... a radial drawing of $H$, and let $D$ be a circuit of $K$ with $U(D)
\subseteq \bar{\Lambda}$ and $|E(D)| < 2(\theta - \lambda)$. Then $ins(D) \subseteq
\bar{\Lambda}$." -/
theorem theorem_7_5 {S : Type w} [TopologicalSpace S] [T2Space S] (H K D : Drawing S) (θ lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (ins : Drawing S → Set S) (z Λ : Set S) (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hMetric : HasTangleMetric H θ T d) (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hZone : IsLambdaZoneAround H d lam z Λ) (hD : D.IsCircuit) (hDs : D.IsSubdrawing K)
    (hDU_sub : D.U ⊆ closure Λ) (hDlen : D.length < 2 * (θ - lam)) : ins D ⊆ closure Λ :=
  GM14.theorem_7_5_proof H K D θ lam T d ins z Λ hS hConn hMetric hK hd hZone hD hDs hDU_sub hDlen

open GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XIV, (7.6)** (page 37):
"Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in $H$
of order $\theta$. Let $\lambda \ge 0$ be an integer, and let $\Lambda \subseteq \Sigma$ be
a $\lambda$-zone. Let $K$ be a radial drawing of $H$, and let $D$ be a circuit of $K$ with
$|E(D)| < 2(\theta - \lambda)$ and $bd(\Lambda) \subseteq ins(D)$. Then $\bar{\Lambda}
\subseteq ins(D)$." -/
theorem theorem_7_6 {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {H K D : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    {ins : Drawing S → Set S} {z Λ : Set S} (hMetric : HasTangleMetric H θ T d)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hZone : IsLambdaZoneAround H d lam z Λ) (hD : D.IsCircuit) (hDs : D.IsSubdrawing K)
    (hDlen : D.length < 2 * (θ - lam)) (hbd_sub : subBd Λ ⊆ ins D) :
    closure Λ ⊆ ins D :=
  GM14.theorem_7_6_proof hS hConn hMetric hK hd hZone hD hDs hDlen hbd_sub

open Function Hypergraph GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIV, (7.7)** (pages 37–38):
"Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in $H$
of order $\theta \ge 6$. Let $z \in A(H)$, let $C_1$, $C_2$ be disjoint circuits of $H$, and
let $U(C_1)$, $U(C_2)$ bound closed discs $\Delta_1$, $\Delta_2 \subseteq \Sigma$ with the
following properties:* (i) $z \subseteq \Delta_2 - bd(\Delta_2)$, and $\Delta_2 \subseteq
\Delta_1 - bd(\Delta_1)$ (ii) $d(z, x) \le \theta - 4$ for all $x \in A(H)$ with $x
\subseteq \Delta_1$ (iii) $x \subseteq \Delta_2 - bd(\Delta_2)$ for all $x \in A(H)$ with
$d(z, x) \le 3$. *Let $H$ be a subgraph of $G$, let $\mathscr{S}$ be a $\mathscr{T}$-local
3-segregation of $G$, and let $\alpha$ be an arrangement of $\mathscr{S}$ in $\Sigma$
compatible with $H$. Then there is an $\alpha$-normal $O$-arc $F \subseteq \Delta_1$,
bounding a closed disc in $\Delta_1$ including $\Delta_2$." -/
theorem theorem_7_7 {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {α : Type v} {β : Type w} {G : Graph α β} {H C₁ C₂ : Drawing S}
    {η : SpanEmbedding H G} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Δ₁ Δ₂ : Set S} {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S} {α_pt : α → S} (hθ : 6 ≤ θ) (hd : HasTangleMetric H θ T d)
    (hz : z ∈ H.A) (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂) (hz_sub : z ⊆ Δ₂ \ subBd Δ₂)
    (hΔ₂_sub₁ : Δ₂ ⊆ Δ₁ \ subBd Δ₁) (hii : ∀ x ∈ H.A, x ⊆ Δ₁ → d z x ≤ θ - 4)
    (hiii : ∀ x ∈ H.A, d z x ≤ 3 → x ⊆ Δ₂ \ subBd Δ₂) (hC₁ : C₁.IsCircuit)
    (hC₁s : C₁.IsSubdrawing H) (hbd₁ : subBd Δ₁ = C₁.U) (hC₂ : C₂.IsCircuit)
    (hC₂s : C₂.IsSubdrawing H) (hbd₂ : subBd Δ₂ = C₂.U) (hdisj : Disjoint C₁.V C₂.V)
    (hSeg : IsThreeSegregation G S_seg) (hLoc : IsTangleLocal G H η T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G H η S_seg α_disc α_pt) :
    ∃ F Δ : Set S,
    IsOArc F ∧ F ⊆ Δ₁ ∧ IsArrangementNormal S_seg α_disc α_pt F ∧
    IsClosedDisc Δ ∧ subBd Δ = F ∧ Δ ⊆ Δ₁ ∧ Δ₂ ⊆ Δ :=
  GM14.theorem_7_7_proof hS hConn hθ hd hz hΔ₁ hΔ₂ hz_sub hΔ₂_sub₁ hii hiii hC₁ hC₁s hbd₁ hC₂ hC₂s hbd₂ hdisj hSeg hLoc hArr hComp

open Function SimpleGraph Hypergraph Surface GM09 GM10 GM11 in
/-- **Graph Minors XIV, (7.8)** (pages 38–39):
"Let $\beta \ge 4$ be even, let $\lambda \ge 0$, and let $\theta \ge 4\lambda + 2$. Let $H$
be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in $H$ of
order $\theta$. Let $z \in A(H)$, let $C_1$, $C_2$ be disjoint circuits of $H$, and let
$U(C_1)$, $U(C_2)$ bound closed discs $\Delta_1$, $\Delta_2 \subseteq \Sigma$ with the
following properties:* (i) $z \subseteq \Delta_2 - bd(\Delta_2)$, and $\Delta_2 \subseteq
\Delta_1 - bd(\Delta_1)$ (ii) $\Delta_1 - bd(\Delta_1)$ is a $(\theta - \beta - 4\lambda -
2)$-zone around $z$ (iii) $\Delta_2 - bd(\Delta_2)$ is a $\lambda$-zone around $z$ (iv) $x
\subseteq \Delta_1 - bd(\Delta_1)$ for every $x \in A(H)$ with $d(z, x) < \beta$, and (v)
*there are circuits $C_3, \dots, C_{\beta/2}$ of $H \cap \Delta_1$ such that $C_1$, $C_2$,
$\dots$, $C_{\beta/2}$ are mutually disjoint and $U(C_3), \dots, U(C_{\beta/2})$ all bound
closed discs in $\Delta_1$ including $\Delta_2$.* ... *Let $P_1, \dots, P_\beta$ be disjoint
paths of $H$ from $V(C_2)$ to $V(C_1)$, such that for $1 \le i \le \beta$, $P_i$ has initial
vertex $v_i \in V(C_2)$ and $U(P_i) \cap (\Delta_2 - bd(\Delta_2)) = \emptyset$. Then
$\{v_1, \dots, v_\beta\}$ is free with respect to the tangle of order $\theta - 4\lambda -
2$ obtained from $\mathscr{T}$ by clearing the $\lambda$-zone $\Delta_2 - bd(\Delta_2)$." -/
theorem theorem_7_8 {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {H C₁ C₂ : Drawing S} {θ beta lam : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d d' : Set S → Set S → ℕ}
    {z Δ₁ Δ₂ : Set S} {C : Fin (beta / 2) → Drawing S} {Δ : Fin (beta / 2) → Set S}
    {P : Fin beta → Drawing S} {v u : Fin beta → S} (_hbeta : 4 ≤ beta) (heven : Even beta)
    (hθ : beta + 4 * lam + 2 ≤ θ) (hMetric : HasTangleMetric H θ T d)
    (hCleared : IsClearedTangle H T d θ lam (Δ₂ \ subBd Δ₂) T' d') (_hC₁ : C₁.IsCircuit)
    (hC₁s : C₁.IsSubdrawing H) (hΔ₁ : IsClosedDisc Δ₁) (hbd₁ : subBd Δ₁ = C₁.U)
    (_hC₂ : C₂.IsCircuit) (hC₂s : C₂.IsSubdrawing H) (hΔ₂ : IsClosedDisc Δ₂)
    (hbd₂ : subBd Δ₂ = C₂.U) (hi : z ⊆ Δ₂ \ subBd Δ₂ ∧ Δ₂ ⊆ Δ₁ \ subBd Δ₁)
    (hii : IsLambdaZoneAround H d (θ - beta - 4 * lam - 2) z (Δ₁ \ subBd Δ₁))
    (hiii : IsLambdaZoneAround H d lam z (Δ₂ \ subBd Δ₂))
    (hiv : ∀ x ∈ H.A, d z x < beta → x ⊆ Δ₁ \ subBd Δ₁)
    (hv_C : ∀ i : Fin (beta / 2), (C i).IsCircuit ∧ (C i).IsSubdrawing H ∧ IsClosedDisc (Δ i) ∧
      subBd (Δ i) = (C i).U ∧ Δ₂ ⊆ Δ i ∧ Δ i ⊆ Δ₁)
    (hv_dis : Pairwise (fun i₁ i₂ : Fin (beta / 2) => Disjoint (C i₁).V (C i₂).V))
    (hP : ∀ j : Fin beta, (P j).IsPathBetween (v j) (u j) ∧ (P j).IsSubdrawing H ∧ v j ∈ C₂.V ∧
      u j ∈ C₁.V ∧ Disjoint (P j).U (Δ₂ \ subBd Δ₂))
    (hP_dis : Pairwise (fun j₁ j₂ : Fin beta => Disjoint (P j₁).V (P j₂).V)) :
    IsFreeSet (clearedSubdrawing H (Δ₂ \ subBd Δ₂)).toHypergraph T' (θ - 4 * lam - 2) (range v) :=
  GM14.theorem_7_8_proof hS hConn _hbeta heven hθ hMetric hCleared _hC₁ hC₁s hΔ₁ hbd₁ _hC₂ hC₂s hΔ₂ hbd₂ hi hii hiii hiv hv_C hv_dis hP hP_dis

/-! ## Section 8. Segregation in a Rural Neighbourhood -/

open GraphMinor.GM09 GraphMinor.GM06 Function GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XIV, (8.1)** (page 40):
"A society $(G, \Omega)$ has no cross if and only if there is a 3-segregation $\mathscr{S}$
of $G$ with $\bar{\Omega} \subseteq V(\mathscr{S})$ and an arrangement $\alpha$ of
$\mathscr{S}$ in a closed disc $\Delta$ with $\Omega = \alpha^{-1}(bd(\Delta))$." -/
theorem theorem_8_1 {D : Type w} [TopologicalSpace D] [T2Space D] {α : Type u} {β : Type v}
    (S : Society α β) (h1 : IsSurface D) (hD : Nonempty (D ≃ₜ ClosedUnitDisc)) :
    ((∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ 2) ↔
    ∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set D) (α_pt : α → D),
    IsThreeSegregation S.G S_seg ∧ S.Ω.bar ⊆ segregationVertices S_seg ∧
    IsSurfaceArrangement S_seg α_disc α_pt ∧ IsPullbackPerm S_seg α_pt (bd D) S.Ω) :=
  GM14.theorem_8_1_proof S h1 hD

open Function GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XIV, (8.2)** (page 40):
"Let $\pi \ge 0$ be an integer with $\pi \ne 1, 3$, and let $(G, \Omega_1)$ be the
composition of a society $(G_2, \Omega_2)$ with a rural neighbourhood $(G_1, \Omega_1,
\Omega_2)$ of breadth $\ge \pi + 5$. Suppose that $X \subseteq \bar{\Omega}_1$ and there are
$2\pi + 8$ mutually disjoint paths of $G_1$, each from $X$ to $\bar{\Omega}_2$ with no
vertex in $\bar{\Omega}_1$ except its initial vertex. If there is a crooked transaction
$\mathscr{P}$ in $(G, \Omega_1)$ with cardinality $\ge \pi$, then $\mathscr{P}$ may be
chosen so that in addition $V(\mathscr{P}) \subseteq X$ and no member of $\mathscr{P}$ has
any internal vertex in $\bar{\Omega}_1$." -/
theorem theorem_8_2 {α : Type u} {β : Type v} (pi : ℕ) (S_comp S₂ : Society α β)
    (N : Neighborhood α β) (X : Set α) (P : Fin (2 * pi + 8) → Graph α β)
    (x y : Fin (2 * pi + 8) → α) (P_set : Set (Graph α β)) (hpi1 : pi ≠ 1) (hpi3 : pi ≠ 3)
    (hcomp : S_comp.IsComposition S₂ N) (hbreadth : N.HasBreadthGe (pi + 5)) (hX : X ⊆ N.Ω.bar)
    (hP_path : ∀ i, IsFromToPathWithEnds N.G (P i) N.Ω.bar N.Ω₀.bar (x i) (y i) ∧ x i ∈ X)
    (hP_disj : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hCrooked : S_comp.IsCrookedTransaction P_set) (hcard : pi ≤ P_set.ncard) :
    ∃ P_set' : Set (Graph α β),
    S_comp.IsCrookedTransaction P_set' ∧
    pi ≤ P_set'.ncard ∧
    S_comp.transactionEnds P_set' ⊆ X ∧
    ∀ Q ∈ P_set', Disjoint (pathInternalVerts S_comp.G Q) S_comp.Ω.bar :=
  GM14.theorem_8_2_proof pi S_comp S₂ N X P x y P_set hpi1 hpi3 hcomp hbreadth hX hP_path hP_disj hCrooked hcard

open Function GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 in
/-- **Graph Minors XIV, (8.3)** (pages 40–41):
"Let $(G, \Omega_1)$ be the composition of a society $(G_2, \Omega_2)$ with a rural neighbourhood
$(G_1, \Omega_1, \Omega_2)$ of breadth $\ge 3$. Suppose that $X \subseteq \bar{\Omega}_1$ and
there are $4$ mutually disjoint paths in $G_1$, each from $X$ to $\bar{\Omega}_2$ with no vertex
in $\bar{\Omega}_1$ except its initial vertex. If there is a cross $\mathscr{P}$ in $(G, \Omega_1)$
then $\mathscr{P}$ may be chosen so that in addition $V(\mathscr{P}) \subseteq X$ and no member of
$\mathscr{P}$ has any internal vertex in $\bar{\Omega}$." -/
theorem theorem_8_3 {α : Type u} {β : Type v} (S_comp S₂ : Society α β) (N : Neighborhood α β)
    (X : Set α) (P : Fin 4 → Graph α β) (x y : Fin 4 → α) (P_set : Set (Graph α β))
    (hcomp : S_comp.IsComposition S₂ N) (hbreadth : N.HasBreadthGe 3) (hX : X ⊆ N.Ω.bar)
    (hP_path : ∀ i, IsFromToPathWithEnds N.G (P i) N.Ω.bar N.Ω₀.bar (x i) (y i) ∧ x i ∈ X)
    (hP_disj : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hCrooked : S_comp.IsCrookedTransaction P_set) (hcard : P_set.ncard = 2) :
    ∃ P_set' : Set (Graph α β),
    S_comp.IsCrookedTransaction P_set' ∧
    P_set'.ncard = 2 ∧
    S_comp.transactionEnds P_set' ⊆ X ∧
    ∀ Q ∈ P_set', Disjoint (pathInternalVerts S_comp.G Q) S_comp.Ω.bar :=
  GM14.theorem_8_3_proof S_comp S₂ N X P x y P_set hcomp hbreadth hX hP_path hP_disj hCrooked hcard

open Function GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM16 in
/-- **Graph Minors XIV, (8.4)** (pages 41–42):
"Let $\Sigma$ be a closed cylinder with ends $F_1, F_2$, and let $H$ be a rigid drawing in
$\Sigma$. Let $C_1, C_2$ be disjoint circuits of $H$, both winding around $\Sigma$, and such
that $F_2$ and $U(C_2)$ both lie in the same component of $\Sigma - U(C_1)$. Let $\pi \ge 0$
with $\pi \ne 1, 3$ and let the regional distance between $U(C_1)$ and $U(C_2)$ be at least
$\pi + 4$. Let $X \subseteq V(C_1)$, and let there be $2\pi + 8$ mutually disjoint paths of
$H$ from $X$ to $V(C_2)$, each with no vertex in $C_1$ except its initial vertex. Let $H$ be
a subgraph of $G_1$, let $\mathscr{S}$ be a 3-segregation of $G_1$, and let $\alpha$ be an
arrangement of $\mathscr{S}$ in $\Sigma$ compatible with $H$. Let $\Omega_i =
\alpha^{-1}(F_i) \, (i = 1, 2)$, and let $\Omega_0$ be a natural order of $V(C_1)$ from
$U(C_1)$. Now let $(G, \Omega_1)$ be a society which is the composition of a society $(G_2,
\Omega_2)$ and the neighbourhood $(G_1, \Omega_1, \Omega_2)$, and let $(G, \Omega_1)$ have a
crooked transaction of cardinality $\ge \pi$. Then $(G, \Omega_0)$ has a crooked transaction
$\mathscr{P}$ of cardinality $\ge \pi$ such that for each $P \in \mathscr{P}$ with ends $u,
v$ say, $u, v \in X$ and $U(P \cap H) - \{u, v\}$ is included in the component of $\Sigma -
U(C_1)$ which includes $U(C_2)$."

The Lean proof corrects two steps of the paper's proof. See the corrections to the proof of (8.4) in
`corrections/GM14.md`. -/
theorem theorem_8_4 {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {α : Type u}
    {β : Type v} {H C₁ C₂ : Drawing S} {D D₂ E₁ E₂ X : Set S} {pi : ℕ} {N : Neighborhood α β}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    {S_G S₂ S_G0 : Society α β} {μ : α → S} (P : Fin (2 * pi + 8) → Graph S (Set S))
    (η : SpanEmbedding H N.G) (hS : IsClosedSurface S) (hD : IsClosedDisc D) (h1 : IsClosedDisc D₂)
    (hE₁ : IsClosedDisc E₁) (hE₂ : IsClosedDisc E₂) (h2 : D₂ ⊆ E₂) (h3 : E₂ ⊆ E₁ \ C₁.U)
    (h4 : E₁ ⊆ D) (h5 : IsRigidIn H (D \ discInt D₂)) (h6 : C₁.IsCircuit ∧ C₁.IsSubdrawing H)
    (h7 : C₂.IsCircuit ∧ C₂.IsSubdrawing H) (h8 : discBd E₁ = C₁.U) (h9 : discBd E₂ = C₂.U)
    (h10 : pi ≠ 1) (h11 : pi ≠ 3) (h12 : pi + 4 ≤ regionalDistance H C₂.U C₁.U) (h13 : X ⊆ C₁.V)
    (h14 : ∀ i, ∃ x ∈ X, ∃ y ∈ C₂.V, IsGraphPathWithEnds H.toGraph (P i) x y ∧ V(P i) ∩ C₁.V = {x})
    (h15 : Pairwise fun i j => Disjoint V(P i) V(P j)) (h16 : IsThreeSegregation N.G S_seg)
    (h17 : IsSurfaceArrangement S_seg α_disc α_pt)
    (h18 : IsCompatibleWith N.G H η S_seg α_disc α_pt)
    (h19 : ∀ S₀ ∈ S_seg, α_disc S₀ ⊆ D \ discInt D₂)
    (h20 : IsPullbackPerm S_seg α_pt (discBd D) N.Ω)
    (h21 : IsPullbackPerm S_seg α_pt (discBd D₂) N.Ω₀) (h22 : S_G.IsComposition S₂ N)
    (h23 : S_G0.G = S_G.G) (h24 : S_G0.Ω.bar = η.vMap '' C₁.V) (h25 : ∀ v ∈ C₁.V, μ (η.vMap v) = v)
    (h26 : IsNaturalOrderFrom μ S_G0.Ω (discBd E₁))
    (h27 : ∃ P_set : Set (Graph α β), S_G.IsCrookedTransaction P_set ∧ pi ≤ P_set.ncard) :
    ∃ P_set : Set (Graph α β), S_G0.IsCrookedTransaction P_set ∧ pi ≤ P_set.ncard ∧
    S_G0.transactionEnds P_set ⊆ η.vMap '' X ∧ ∀ p ∈ P_set, ∃ a b : α,
    S_G0.IsOmegaPathWithEnds p a b ∧
    (∀ v ∈ H.V, η.vMap v ∈ V(p) → η.vMap v = a ∨ η.vMap v = b ∨ v ∈ E₁ \ C₁.U) ∧
    (∀ e ∈ H.E, η.eMap e ∈ E(p) → e ⊆ E₁ \ C₁.U) :=
  GM14.theorem_8_4_proof P η hS hD h1 hE₁ hE₂ h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27

/-! ## Section 9. Constant Radius Discs -/

open Function Hypergraph Metric GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIV, (9.1)** (page 43):
"Let $H$ be a 2-cell drawing in $\Sigma$, with radial drawing $K$. Let $\mathscr{T}$ be a
respectful tangle in $H$ of order $\theta$, let $\kappa$ be an integer with $1 \le \kappa
\le \theta$, let $z \in A(K)$, and let $Z$ be the union of $ins(W)$, taken over all closed
walks $W$ of $K$ of length $< 2\kappa$ with $z \subseteq ins(W)$. Then there is a closed
disc $\Delta \subseteq \Sigma$ with $Z \subseteq \Delta - bd(\Delta)$." -/
theorem theorem_9_1 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H K : Drawing S} {θ κ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S} {z : Set S}
    (hResp : IsRespectfulDrawingTangle H θ T) (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins) (hκ1 : 1 ≤ κ) (hκθ : κ ≤ θ)
    (hz : z ∈ K.A) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ walkUnion K ins (2 * κ) z ⊆ Δ \ subBd Δ :=
  GM14.theorem_9_1_proof hS hResp hK hd hκ1 hκθ hz

open GraphMinor.GM16 Function Hypergraph Metric GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 SimpleGraph GraphMinor.GM06 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XIV, (9.2)** (page 43), proving `GM16.GM14Theorem92Statement`:
"Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in $H$
of order $\theta$, with metric $d$. Let $z \in A(H)$ and let $\kappa$ be an integer with $2
\le \kappa \le \theta - 3$. Then there is a $(\kappa + 2)$-zone $\Lambda$ around $z$ such
that $x \subseteq \Lambda$ for every $x \in A(H)$ with $d(z, x) < \kappa$." -/
theorem theorem_9_2 {S : Type w} [TopologicalSpace S] [T2Space S] (H : Drawing S) (θ κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (z : Set S)
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hMetric : HasTangleMetric H θ T d)
    (hz : z ∈ H.A) (hκ2 : 2 ≤ κ) (hκθ : κ + 3 ≤ θ) :
    ∃ Λ : Set S, IsLambdaZoneAround H d (κ + 2) z Λ ∧ ∀ x ∈ H.A, d z x < κ → x ⊆ Λ :=
  GM14.theorem_9_2_proof H θ κ T d z hS hConn hMetric hz hκ2 hκθ

open GraphMinor.GM16 Function GraphMinor.GM09 GraphMinor.GM09.PlanarNests GraphMinor.GM10 GraphMinor.GM11 Hypergraph SimpleGraph GraphMinor.GM06 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XIV, (9.3)** (page 44), proving `GM16.GM14Theorem93Statement`:
"Let $H$ be a 2-cell rigid drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle
in $H$ of order $\theta$, with metric $d$. Let $z \in A(H)$, and let $\kappa$ be an integer
with $2 \le \kappa \le \theta - 6$. Then there is a $(\kappa + 5)$-zone $\Lambda$ around $z$
such that $H \cap (\Sigma - \Lambda)$ is rigid and $x \subseteq \Lambda$ for every $x \in
A(H)$ with $d(z, x) < \kappa$." -/
theorem theorem_9_3 {S : Type w} [TopologicalSpace S] [T2Space S] (H : Drawing S) (θ κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (z : Set S)
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hRig : IsRigid H)
    (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A) (hκ2 : 2 ≤ κ) (hκθ : κ + 6 ≤ θ) :
    ∃ Λ : Set S, IsLambdaZoneAround H d (κ + 5) z Λ ∧ IsRigid (clearedSubdrawing H Λ) ∧ ∀ x ∈ H.A,
    d z x < κ → x ⊆ Λ :=
  GM14.theorem_9_3_proof H θ κ T d z hS hConn hRig hMetric hz hκ2 hκθ

open Function Hypergraph Metric GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIV, (9.4)** (page 45):
"Let $H$ be a 2-cell drawing in $\Sigma$, let $z \in A(H)$, and let $\mathscr{T}$ be a respectful
tangle in $H$ of order $\theta$, with metric $d$. Let $1 \le \kappa \le \theta - 7$, and let
$\Lambda$ be a $\kappa$-zone around $z$, including every $x \in A(H)$ with $d(z, x) \le 3$. Let $H$
be a subgraph of $G$, let $\mathscr{S}$ be a $\mathscr{T}$-local 3-segregation of $G$, and let
$\alpha$ be an arrangement of $\mathscr{S}$ in $\Sigma$ compatible with $H$. Then there is a closed
disc $\Delta \subseteq \Sigma$ such that $\Lambda \subseteq \Delta$, $bd(\Delta)$ is
$\alpha$-normal, $H \cap \Sigma - \Delta$ has a circuit, and $d(z, x) \le \kappa + 3$ for all $x
\in A(H)$ with $x \cap \Delta \ne \emptyset$." -/
theorem theorem_9_4 {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) {α : Type v} {β : Type w} {G : Graph α β} {H : Drawing S}
    {η : SpanEmbedding H G} {θ κ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Λ : Set S} {S_seg : Set (Society α β)} {α_disc : Society α β → Set S}
    {α_pt : α → S} (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A) (hκ1 : 1 ≤ κ)
    (hκθ : κ + 7 ≤ θ) (hZone : IsLambdaZoneAround H d κ z Λ) (hΛ_le3 : ∀ x ∈ H.A, d z x ≤ 3 → x ⊆ Λ)
    (hSeg : IsThreeSegregation G S_seg) (hLoc : IsTangleLocal G H η T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G H η S_seg α_disc α_pt) :
    ∃ (F Δ : Set S) (C_out : Drawing S),
    IsOArc F ∧ IsArrangementNormal S_seg α_disc α_pt F ∧
    IsClosedDisc Δ ∧ subBd Δ = F ∧ closure Λ ⊆ Δ ∧
    C_out.IsCircuit ∧ C_out.IsSubdrawing (H.interSet (closure (univ \ Δ))) ∧
    C_out.IsSubdrawing (clearedSubdrawing H Δ) ∧
    ∀ x ∈ H.A, (x ∩ Δ).Nonempty → d z x ≤ κ + 3 :=
  GM14.theorem_9_4_proof hS hConn hMetric hz hκ1 hκθ hZone hΛ_le3 hSeg hLoc hArr hComp

open GraphMinor.GM16 Function GraphMinor.GM09 GraphMinor.GM09.PlanarNests GraphMinor.GM10 GraphMinor.GM11 Hypergraph SimpleGraph GraphMinor.GM06 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XIV, (9.5)** (pages 45–47), proving `GM16.GM14Theorem95Statement`:
"Let $H$ be a 2-cell, rigid drawing in $\Sigma$, let $z \in A(H)$, and let $\mathscr{T}$ be a
respectful tangle in $H$ of order $\theta$. Let $\beta \ge 4$ be an even integer with
$\theta \ge 16\beta + 17$. Then there is a battlefield around $z$ of size $\beta$." -/
theorem theorem_9_5 {S : Type w} [TopologicalSpace S] [T2Space S] (H : Drawing S) (θ β : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (z : Set S)
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hRig : IsRigid H)
    (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A) (hbeta : 4 ≤ β) (heven : Even β)
    (hθ : 16 * β + 17 ≤ θ) :
    ∃ (Λ : Set S) (C : Drawing S) (X : Set S), IsBattlefieldData H T d θ β z Λ C X :=
  GM14.theorem_9_5_proof H θ β T d z hS hConn hRig hMetric hz hbeta heven hθ

open Function GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XIV, (9.6)** (pages 47–49):
"Let $H$ be a 2-cell, rigid drawing in $\Sigma$, let $z \in A(H)$, and let $\mathscr{T}$ be a
respectful tangle in $H$ of order $\theta$, with metric $d$. Let $\pi \ge 0$ with $\pi \ne 1, 3$,
let $\beta \ge 2\pi + 8$ be even, and let $\theta \ge 16\beta + 17$. Let $H$ be a subgraph of $G$,
let $J$ be the union of some bridges of $H$ in $G$ such that $d(z, v) < \beta$ for each ... $v \in
V(H
\cap J)$, and let $G'$ be the union of $H$ and all the other bridges of $H$ in $G$. Let
$\mathscr{S}$ be a $\mathscr{T}$-local 3-segregation of $G'$, and let $\alpha$ be an arrangement of
$\mathscr{S}$ in $\Sigma$ compatible with $H$. Then there is a $(3\beta + 3)$-zone $\Lambda$ around
$z$, and a closed disc $\Delta \subseteq \Sigma$ with $bd(\Delta)$ $\alpha$-normal and with
$\Lambda \subseteq \Delta$, with the following properties:
(i) $d(z, x) \le 3\beta + 6$ for all $x \in A(H)$ with $x \cap \Delta \ne \emptyset$
(ii) $x \subseteq \Delta - bd(\Delta)$ for all $x \in A(H)$ with $d(z, x) < \beta$
(iii) $H \cap \overline{\Sigma - \Delta}$ has a circuit, and $H \cap (\Sigma - \Lambda)$ is a rigid
drawing in $\Sigma$
(iv) one of the following alternatives holds:
(a) there is a crooked transaction $\mathscr{P}$ of cardinality $\ge \pi$ in $(G, \Omega_0)$ (where
$\Omega_0$ is a natural order of $V(H) \cap bd(\Lambda)$ from $bd(\Lambda)$), such that
$V(\mathscr{P})$ is free with respect to the tangle of order $\theta - 4(3\beta + 3) - 2$ obtained
from $\mathscr{T}$ by clearing $\Lambda$, and each $P \in \mathscr{P}$ meets $H \cap (\Sigma -
\Lambda)$ in precisely the ends of $P$
(b) there is no crooked transaction of cardinality $\ge \pi$ in $(\alpha^{-1}(\Delta) \cup J,
\alpha^{-1}(bd(\Delta)))$."

The proof uses a battlefield with the corrected clause (v) (see the correction on page 45 in
`corrections/GM14.md`), and with its set `X` cut down to `β` vertices, as in the step "We may
assume that $|X_i| = \beta$" of Graph Minors XVI, page 71. Where the paper says only that a society
"is the composition of" two pieces (page 48), the proof adds a one-vertex society for each vertex
of $H \cap (\Sigma - \Lambda)$ outside these pieces, so that every vertex of the segregation has a
place in the arrangement. -/
theorem theorem_9_6 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G_amb G G' J : Graph α β) (B_J B_rem : Set (Graph α β)) (H : Drawing S)
    (η : SpanEmbedding H G_amb) (η' : SpanEmbedding H G') (θ π beta : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (z : Set S)
    (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S)
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hV_fin : V(G_amb).Finite)
    (hE_fin : E(G_amb).Finite) (hRig : IsRigid H) (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A)
    (hπ1 : π ≠ 1) (hπ3 : π ≠ 3) (hbeta : 2 * π + 8 ≤ beta) (heven : Even beta)
    (hθ : 16 * beta + 17 ≤ θ) (hB_J : ∀ B ∈ B_J, IsBridge G_amb η.imageGraph B)
    (hB_rem : ∀ B ∈ B_rem, IsBridge G_amb η.imageGraph B) (hDisj_B : Disjoint B_J B_rem)
    (hJ_eq : J = subgraphSUnion G_amb B_J)
    (hG'_eq : G' = subgraphSUnion G_amb {η.imageGraph, subgraphSUnion G_amb B_rem})
    (hG_eq : G = subgraphUnion G_amb G' J) (hη'_v : ∀ v ∈ H.V, η'.vMap v = η.vMap v)
    (hη'_e : ∀ e ∈ H.E, η'.eMap e = η.eMap e)
    (hJ_dist : ∀ v ∈ H.V, η.vMap v ∈ V(J) → d z {v} < beta) (hSeg : IsThreeSegregation G' S_seg)
    (hLoc : IsTangleLocal G' H η' T S_seg) (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt) :
    ∃ (Λ Δ : Set S)
    (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d₁ : Set S → Set S → ℕ)
    (η_Λ : SpanEmbedding (clearedSubdrawing H Λ) G_amb)
    (soc_Λ soc_star : Society α β),
    IsLambdaZoneAround H d (3 * beta + 3) z Λ ∧
    IsClearedTangle H T d θ (3 * beta + 3) Λ T₁ d₁ ∧
    IsClosedDisc Δ ∧
    IsArrangementNormal S_seg α_disc α_pt (subBd Δ) ∧
    Λ ⊆ Δ ∧
    (∀ x ∈ H.A, (x ∩ Δ).Nonempty → d z x ≤ 3 * beta + 6) ∧
    (∀ x ∈ H.A, d z x < beta → x ⊆ Δ \ subBd Δ) ∧
    (∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing (H.interSet (closure (univ \ Δ)))) ∧
    IsRigid (clearedSubdrawing H Λ) ∧
    (∀ v ∈ (clearedSubdrawing H Λ).V, η_Λ.vMap v = η.vMap v) ∧
    (∀ e ∈ (clearedSubdrawing H Λ).E, η_Λ.eMap e = η.eMap e) ∧
    soc_Λ.G = G ∧
    soc_Λ.Ω.bar = η_Λ.vMap '' ((clearedSubdrawing H Λ).V ∩ subBd Λ) ∧
    (∃ inv_v : α → S,
      (∀ x ∈ soc_Λ.Ω.bar, inv_v x ∈ (clearedSubdrawing H Λ).V ∩ subBd Λ ∧ η_Λ.vMap (inv_v x) = x) ∧
      IsNaturalOrderFrom inv_v soc_Λ.Ω (subBd Λ)) ∧
    soc_star.G = subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc α_pt Δ) ∧
    IsPullbackPerm S_seg α_pt (subBd Δ) soc_star.Ω ∧
    ((∃ (P_set : Set (Graph α β)) (X : Set S),
        soc_Λ.IsCrookedTransaction P_set ∧
        π ≤ P_set.ncard ∧
        (∀ P ∈ P_set, ∀ a b : α,
          soc_Λ.IsOmegaPathWithEnds P a b →
          IsHPathWithEnds G_amb η_Λ.imageGraph P a b) ∧
        X ⊆ (clearedSubdrawing H Λ).V ∩ subBd Λ ∧
        soc_Λ.transactionEnds P_set = η_Λ.vMap '' X ∧
        IsFreeSet (clearedSubdrawing H Λ).toHypergraph T₁ (θ - 4 * (3 * beta + 3) - 2) X) ∨
     (∀ P_set : Set (Graph α β), soc_star.IsCrookedTransaction P_set → ¬ π ≤ P_set.ncard)) :=
  GM14.theorem_9_6_proof G_amb G G' J B_J B_rem H η η' θ π beta T d z S_seg α_disc α_pt hS hConn hV_fin hE_fin hRig hMetric hz hπ1 hπ3 hbeta heven hθ hB_J hB_rem hDisj_B hJ_eq hG'_eq hG_eq hη'_v hη'_e hJ_dist hSeg hLoc hArr hComp

/-! ## Section 10. The Main Proof -/

open GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 Hypergraph in
/-- **Graph Minors XIV, (10.1)** (pages 49–50):
"Let $H$ be a 2-cell, rigid drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle
in $H$ of order $\theta$, with metric $d$. Let $H$ be a subgraph of $G$, let $\beta \ge 12$
be an even integer with $\theta \ge 16\beta + 17$, and suppose that* (i) $d(u, v) < \beta$
*for every $H$-path in $G$ with ends $u$, $v$ and* (ii) *if $\mathscr{T}'$ is the tangle of
order $\theta - 4(3\beta + 3) - 2$ obtained from $\mathscr{T}$ by clearing some $(3\beta +
3)$-zone $\Lambda$ such that $H \cap (\Sigma - \Lambda)$ is a rigid drawing in $\Sigma$,
then $\Lambda$ is not an eye of $H \cap (\Sigma - \Lambda)$ in $G$ with respect to
$\mathscr{T}'$.* *Then there is a $\mathscr{T}$-local 3-segregation of $G$ and an
arrangement of it in $\Sigma$ compatible with $H$." -/
theorem theorem_10_1 {S : Type u} [TopologicalSpace S] [T2Space S] {α : Type v} {β : Type w}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (G : Graph α β) (H : Drawing S)
    (η : SpanEmbedding H G) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (θ beta : ℕ) (hV_fin : V(G).Finite) (hE_fin : E(G).Finite)
    (_h2cell : H.IsTwoCell) (hrigid : IsRigid H) (_hT : IsRespectfulDrawingTangle H θ T)
    (hmetric : HasTangleMetric H θ T d) (hbeta : 12 ≤ beta ∧ Even beta) (hθ : 16 * beta + 17 ≤ θ)
    (hi_path : ∀ (P : Graph α β) (u v : S), u ∈ H.V → v ∈ H.V →
      IsHPathWithEnds G η.imageGraph P (η.vMap u) (η.vMap v) → d {u} {v} < beta)
    (hii_no_eye : ∀ (Λ : Set S) (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (η_cl : SpanEmbedding (clearedSubdrawing H Λ) G),
      IsLambdaZone H d (3 * beta + 3) Λ → IsRigid (clearedSubdrawing H Λ) →
      IsClearedTangle H T d θ (3 * beta + 3) Λ T' d' →
      (∀ v ∈ (clearedSubdrawing H Λ).V, η_cl.vMap v = η.vMap v) →
      (∀ e ∈ (clearedSubdrawing H Λ).E, η_cl.eMap e = η.eMap e) →
      ¬ IsDrawingEye G (clearedSubdrawing H Λ) η_cl (θ - 4 * (3 * beta + 3) - 2) T' Λ) :
    ∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S),
    IsThreeSegregation G S_seg ∧ IsTangleLocal G H η T S_seg ∧
    IsSurfaceArrangement S_seg α_disc α_pt ∧ IsCompatibleWith G H η S_seg α_disc α_pt :=
  GM14.theorem_10_1_proof hS hConn G H η T d θ beta hV_fin hE_fin _h2cell hrigid _hT hmetric hbeta hθ hi_path hii_no_eye

end GraphMinor.GM14
