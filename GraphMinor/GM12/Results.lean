module

public import GraphMinor.GM12.Section1
public import GraphMinor.GM12.Section1b
public import GraphMinor.GM12.Section2Theorem
public import GraphMinor.GM12.Section3GeometricReduction
public import GraphMinor.GM12.Section3Theorem
public import GraphMinor.GM12.Section4
public import GraphMinor.GM12.Section4Monotone
public import GraphMinor.GM12.Section4Theorem43
public import GraphMinor.GM12.Section4Theorem44
public import GraphMinor.GM12.Section4Theorem45
public import GraphMinor.GM12.Section5Final
public import GraphMinor.GM12.Section5Respect
public import GraphMinor.GM12.Section6
public import GraphMinor.GM12.Section7
public import GraphMinor.GM12.Section710
public import GraphMinor.GM12.Section711
public import GraphMinor.GM12.Section72
public import GraphMinor.GM12.Section73
public import GraphMinor.GM12.Section74
public import GraphMinor.GM12.Section75Proof
public import GraphMinor.GM12.Section76
public import GraphMinor.GM12.Section77
public import GraphMinor.GM12.Section79
public import GraphMinor.GM12.Section7Proved
public import GraphMinor.GM15.Cited

/-!
# Graph Minors XII: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XII. Distance on a surface*, J. Combin. Theory Ser. B
**64** (1995), 240–272.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. The errors of the paper, and how the Lean corrects them, are listed in
`corrections/GM12.md`.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

universe u u_1 u_2 u_3 u_4 u_5 u_6 w

/-! ## Section 1. Introduction -/

open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 Hypergraph in
/-- **Graph Minors XII, (1.1)** (page 242): "In these circumstances, let $E(\Gamma) \ne \emptyset$,
and let $(A, B)$ be a separation of $\Gamma$ of order $<\theta$. Then $(A, B) \in \mathscr{T}$ if
and only if for every edge $e$ of $A$ there is a circuit $C$ of $K$ with $V(C) \cap V(\Gamma)
\subseteq V(A \cap B)$ and with $e \subseteq ins(C)$."

Graph Minors XII, (1.1), page 242. A small side belongs to the tangle exactly when each
of its edges lies inside a radial circuit whose original vertices lie in the separator.
This is the drawing case of Graph Minors XI, (6.3). The finite family required there is obtained
by choosing one circuit for each edge of the small side. -/
theorem theorem_1_1 {S : Type u} [TopologicalSpace S] [T1Space S] {Γ K : Drawing S}
    (hS : IsClosedSurface S) [ConnectedSpace S] {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hT : IsRespectfulDrawingTangle Γ θ T) (hE : Γ.E.Nonempty)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins) {A B : Hypergraph S (Set S)}
    (hAB : Γ.toHypergraph.IsSeparation A B) (ho : separationOrder A B < θ) :
    (A, B) ∈ T ↔ ∀ e ∈ A.edgeSet, ∃ C : Drawing S,
    C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ ∧
      C.V ∩ Γ.V ⊆ (A ∩ B).vertexSet ∧ e ⊆ ins C :=
  GM12.theorem_1_1_proof hS hT hE hK hd hAB ho

open GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph in
/-- **Graph Minors XII, (1.2)** (page 242): "Let $\mathscr{T}$ be a respectful tangle of order
$\theta \ge 2$ in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$, and let its metric be
$d$. Let $c \in A(\Gamma)$; then there is an edge $e$ of $\Gamma$ with $d(c, e) = \theta$."

Graph Minors XII, (1.2), page 242, with the necessary hypothesis that there are at least
two edges, as in XIV (7.1). The proof uses the established XI (8.5) and (8.12).

The print fails when `Γ` has one edge, so the Lean assumes `2 ≤ Γ.E.ncard`. See the correction to
(1.2) in `corrections/GM12.md`. -/
theorem theorem_1_2 {S : Type u} [TopologicalSpace S] [T1Space S] (hS : IsClosedSurface S)
    [ConnectedSpace S] {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hd : HasTangleMetric Γ θ T d) (hE : 2 ≤ Γ.E.ncard) {c : Set S} (hc : c ∈ Γ.A) :
    ∃ e ∈ Γ.E, d c e = θ :=
  GM12.theorem_1_2_proof hS hd hE hc

/-! ## Section 2. The Trace of a Closed Curve -/

open GM11 in
/-- **Graph Minors XII, (2.1)** (page 243): "Let $\Gamma$ be a 2-cell drawing in a connected surface
$\Sigma$, with a radial drawing $K$. Let $\mathscr{T}$ be a respectful tangle in $\Gamma$ of order
$\theta \ge 1$, let $\phi \colon S^1 \to \Sigma$ be continuous, of length $<\theta$, such that
$|\phi|$ is $\Gamma$-normal, and let $W$ be a trace of $\phi$. Then $ins(W)$ is defined. Moreover,
for any atom $c$ of $\Gamma$, if there is an $O$-arc $F \subseteq |\phi|$ with $c \cap ins(F) \ne
\emptyset$, then $c \cap ins(W) \ne \emptyset$."

Graph Minors XII, (2.1), pages 243--244. The trace is short enough
for its inside to be defined. Every atom meeting the tangle-selected
disc bounded by a circle in the original image meets that trace inside.
The selected disc explicitly represents `ins(F)` from the paper.

The definition of a trace indexes its intervals as the paper means, not as printed. See the
correction on page 243 in `corrections/GM12.md`. -/
theorem theorem_2_1 {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) {ins : Drawing S → Set S}
    (hd : IsDerivedSlope (.drawing Γ) K θ T ins) {φ : C(Circle, S)} {u : S}
    (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W) (hlen : curveLength Γ φ < θ)
    {F D c : Set S} (hF : IsOArc F) (hFφ : F ⊆ range φ) (hD : IsClosedDisc D) (hbdD : subBd D = F)
    (hmD : ((PaintingOrDrawing.drawing Γ).inter D,
        (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T) (hc : c ∈ Γ.A) (hcD : (c ∩ D).Nonempty) :
    W.length < 2 * θ ∧ (c ∩ insWalk ins K W).Nonempty :=
  GM12.theorem_2_1_proof hS hT hrespect hK hd W hW hlen hF hFφ hD hbdD hmD hc hcD

/-! ## Section 3. Disjoint Connecting Subgraphs -/

/-- **Graph Minors XII, (3.1)** (page 245): "With notation as above, suppose that either $\Sigma$ is
not a sphere or $t \ge 3$. Then there is an integer $N$, depending on $\Sigma$, $t$, $|Z|$ but not
on $\Gamma$, such that for every $\Gamma$ and partition $(Z_j \colon 1 \le j \le p)$ of $Z$ the
following is true. Suppose that (i) if $F \subseteq \Sigma^*$ is a $\Gamma$-normal $O$-arc with $|F
\cap V(\Gamma)| \le N$ then $F$ bounds a closed disc $\Delta \subseteq \Sigma$ which includes at
most one of $\Delta_1, \dots, \Delta_t$, (ii) for every triple $F_1$, $F_2$, $F_3 \subseteq
\Sigma^*$ such that $F_1$, $F_2$ are $\Gamma$-normal $O$-arcs bounding disjoint closed discs in
$\Sigma$ which each include exactly one of $\Delta_1, \dots, \Delta_t$, and $F_3$ is a
$\Gamma$-normal line with an end in $F_1$ and an end in $F_2$ and no other point in $F_1 \cup F_2$,
we have $|(F_1 \cup F_2 \cup F_3) \cap V(\Gamma)| > N$ (iii) for every pair $F_1$, $F_2 \subseteq
\Sigma^*$ of $\Gamma$-normal $O$-arcs bounding closed discs $D_1$, $D_2 \subseteq \Sigma$ which each
include exactly one of $\Delta_1, \dots, \Delta_t$, and with $|D_1 \cap D_2| = 1$, we have $|(F_1
\cup F_2) \cap V(\Gamma)| > N$ (iv) if $\Sigma$ is a sphere and $t = 3$, and $F_1$, $F_2$, $F_3
\subseteq \Sigma^*$ are $\Gamma$-normal lines which have common ends but are otherwise mutually
disjoint, and the $O$-arcs $F_2 \cup F_3$, $F_3 \cup F_1$, $F_1 \cup F_2$ respectively bound closed
discs $D_1$, $D_2$, $D_3 \subseteq \Sigma$, say, where $F_i \not\subseteq D_i$ and $\Delta_i \subseteq D_i$
$(i = 1, 2, 3)$, then |(F_1 \cup F_2 \cup F_3) \cap V(\Gamma)| > N$ (v) for every $\Gamma$-normal
$O$-arc $F \subseteq \Sigma^*$ which bounds a closed disc in $\Sigma$ including exactly one of
$\Delta_1, \dots, \Delta_t$, ($\Delta_i$ say) we have $|F \cap V(\Gamma)| \ge |\text{bd}(\Delta_i)
\cap V(\Gamma)|$, and (vi) the topological feasibility condition is satisfied."

Graph Minors XII, (3.1), page 245. The geometric conditions
(i)--(vi) give disjoint connected subdrawings for the prescribed
boundary partition, with one threshold for all drawings and disc
placements on the fixed surface. -/
theorem theorem_3_1 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t z : ℕ) (hcase : ¬ IsSphere S ∨ 3 ≤ t) :
    ∃ N : ℕ, ∀ (Γ : Drawing S) (Δ : Fin t → Set S)
    (_hΔ : ∀ i, IsClosedDisc (Δ i))
    (_hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (_havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
    (p : ℕ) (Zs : Fin p → Set S)
    (_hsmall : ∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
      (Γ.V ∩ F).ncard ≤ N →
      ∃ D : Set S, IsClosedDisc D ∧ discBd D = F ∧
        ∀ i j, Δ i ⊆ D → Δ j ⊆ D → i = j)
    (_hii : ∀ (A B P D E : Set S) (u v : S),
      Γ.IsNormal (A ∪ B ∪ P) → IsOArc A → IsOArc B → IsLineWithEnds P u v →
      u ∈ A → v ∈ B → P ∩ A = {u} → P ∩ B = {v} →
      A ∪ B ∪ P ⊆ discComplement Δ → IsClosedDisc D → IsClosedDisc E →
      discBd D = A → discBd E = B → Disjoint D E →
      (∃ i, ∀ l, Δ l ⊆ D ↔ l = i) → (∃ j, ∀ l, Δ l ⊆ E ↔ l = j) →
      N < (Γ.V ∩ (A ∪ B ∪ P)).ncard)
    (_hiii : ∀ A B D E : Set S,
      Γ.IsNormal (A ∪ B) → IsOArc A → IsOArc B → A ∪ B ⊆ discComplement Δ →
      IsClosedDisc D → IsClosedDisc E → discBd D = A → discBd E = B →
      (D ∩ E).ncard = 1 →
      (∃ i, ∀ l, Δ l ⊆ D ↔ l = i) → (∃ j, ∀ l, Δ l ⊆ E ↔ l = j) →
      N < (Γ.V ∩ (A ∪ B)).ncard)
    (_hiv : ∀ ht : t = 3, IsSphere S → ∀ (P D : Fin 3 → Set S) (a b : S), a ≠ b →
      Γ.IsNormal (⋃ i, P i) → (∀ i, IsLineWithEnds (P i) a b) →
      (∀ i j, i ≠ j → P i ∩ P j = {a, b}) → (⋃ i, P i) ⊆ discComplement Δ →
      (∀ i, IsClosedDisc (D i) ∧
        discBd (D i) = ⋃ j : {j // j ≠ i}, P j.val ∧ Δ (Fin.cast ht.symm i) ⊆ D i ∧ ¬ P i ⊆ D i) →
      N < (Γ.V ∩ ⋃ i, P i).ncard),
    (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
    (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) →
    IsTopologicallyFeasible Δ Zs →
    (∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
      ∀ D : Set S, IsClosedDisc D → discBd D = F →
      ∀ i, (∀ j, Δ j ⊆ D ↔ j = i) →
        (Γ.V ∩ discBd (Δ i)).ncard ≤ (Γ.V ∩ F).ncard) →
    (discBoundaryVertices Γ Δ).ncard ≤ z →
    HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs :=
  theorem_3_1_proof hS t z hcase

open GM14 in
/-- **Graph Minors XII, (3.2)** (page 246): "For every connected surface $\Sigma$ and all integers
$t \ge 0$ and $z \ge 0$, there exists an integer $\theta \ge 1$ such that the following is true. Let
$\Delta_1, \dots, \Delta_t$ be mutually disjoint closed discs in $\Sigma$, and let $\Gamma$ be a
$2$-cell drawing in $\Sigma$ such that $U(\Gamma) \cap \Delta_i = V(\Gamma) \cap
\text{bd}(\Delta_i)$ for $1 \le i \le t$. Let $|Z| \le z$, where $$Z = \bigcup_{1 \le i \le t}
V(\Gamma) \cap \text{bd}(\Delta_i),$$ and let $(Z_j \colon 1 \le j \le p)$ be a partition of $Z$
satisfying the topological feasibility condition above. Let $\mathscr{T}$ be a respectful tangle of
order $\ge \theta$ in $\Gamma$, with metric $d$, such that (i) $d(r_i, r_j) \ge \theta$ for $1 \le i
< j \le t$, where $r_i$ is the region of $\Gamma$ meeting $\Delta_i$ for $1 \le i \le t$, and (ii)
$V(\Gamma) \cap \text{bd}(\Delta_i)$ is free for $1 \le i \le t$."

Graph Minors XII, (3.2), pages 245--248. A uniform separation
threshold for the prescribed regions and free boundary vertices
ensures disjoint connected subdrawings realizing every topologically
feasible boundary partition. -/
theorem theorem_3_2 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t z : ℕ) :
    ∃ η : ℕ, 1 ≤ η ∧ ∀ (Δ : Fin t → Set S) (Γ : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (p : ℕ) (Zs : Fin p → Set S),
    (∀ i, IsClosedDisc (Δ i) ∧ Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i)) →
    Pairwise (fun i j => Disjoint (Δ i) (Δ j)) →
    (discBoundaryVertices Γ Δ).ncard ≤ z →
    (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
    (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) → IsTopologicallyFeasible Δ Zs →
    η ≤ θ → HasTangleMetric Γ θ T d →
    (∀ i j, i ≠ j → ∀ ri ∈ Γ.R, (ri ∩ Δ i).Nonempty →
      ∀ rj ∈ Γ.R, (rj ∩ Δ j).Nonempty → η ≤ d ri rj) →
    (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ i))) →
    HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs :=
  GM12.theorem_3_2_proof hS t z

/-! ## Section 4. Clique Minors -/

open GM10 GM11 GM14 Hypergraph in
/-- **Graph Minors XII, (4.1)** (page 248): "Let $\mathscr{T}$ be a respectful tangle in a 2-cell
drawing $\Gamma$ in a connected surface $\Sigma$, with metric $d$. Let $u, v \in V(\Gamma)$, and let
$P$ be a path of $\Gamma$ between $u$ and $v$. If $(A, B) \in \mathscr{T}$ and $V(P) \subseteq V(A)$
then $(A, B)$ has order $\ge \frac{1}{2} d(u, v)$."

Graph Minors XII, (4.1), page 248. A path whose vertices lie on a
small side has endpoint distance at most twice the separation order. -/
theorem theorem_4_1 {S : Type u} [TopologicalSpace S] [T2Space S] (Γ P : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (A B : Hypergraph S (Set S)) (u v : S) (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hMetric : HasTangleMetric Γ θ T d) (hu : u ∈ Γ.V) (hv : v ∈ Γ.V) (hP : P.IsPathBetween u v)
    (hPs : P.IsSubdrawing Γ) (hAB : (A, B) ∈ T) (hPV : P.V ⊆ A.vertexSet) :
    d {u} {v} ≤ 2 * separationOrder A B :=
  GM12.theorem_4_1_proof Γ P θ T d A B u v hS hConn hMetric hu hv hP hPs hAB hPV

open Graph Hypergraph in
/-- **Graph Minors XII, (4.2)** (page 249): "If $L$ is isomorphic to a minor of $L'$, and
$\mathscr{T}$ is a tangle in a graph $G$, and $\mathscr{T}$ controls an $L'$ minor of $G$ then
$\mathscr{T}$ controls an $L$ minor of $G$."

Graph Minors XII, (4.2), page 249. Control passes to any target minor.
The inhabited host edge-label assumption accounts for total edge maps
in `ControlsMinor`; it is automatic for drawings.

The edge map of `ControlsMinor` is defined on the whole edge type, so the Lean assumes `[Nonempty
β]`. This is only an encoding. -/
theorem theorem_4_2 {α β γ δ γ' δ' : Type*} [Nonempty β] {G : Graph α β} (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) {L : Graph γ δ} {L' : Graph γ' δ'} (hV' : L'.vertexSet.Finite)
    (hE' : L'.edgeSet.Finite) (hminor : IsIsoMinor L L') {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)}
    (hc : ControlsMinor (Hypergraph.ofGraph G hV hE) θ T L') :
    ControlsMinor (Hypergraph.ofGraph G hV hE) θ T L :=
  theorem_4_2_proof hV hE hV' hE' hminor hc

open GM14 in
/-- **Graph Minors XII, (4.3)** (page 249): "For any connected surface $\Sigma$ and any graph $L$
which can be drawn in $\Sigma$, there is an integer $\theta \ge 1$ such that the following is true.
Let $G$ be a graph, let $\Gamma$ be a subgraph of $G$ which is a 2-cell drawing in $\Sigma$, and let
$\mathscr{T}$ be a respectful tangle in $\Gamma$ of order $\ge \theta$. Then the tangle in $G$
induced by $\mathscr{T}$ controls an $L$ minor of $G$."

Graph Minors XII (4.3), pages 249--251. The tangle induced in
an overgraph controls every drawable target once its order exceeds
the threshold. The overgraph is written as a hypergraph with the
same vertex and edge labels as the drawing. -/
theorem theorem_4_3 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {α β : Type*} {L : Graph α β} (D : GraphDrawing L S) :
    ∃ N : ℕ, 1 ≤ N ∧
    ∀ (Γ : Drawing S) (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (G : Hypergraph S (Set S)),
    HasTangleMetric Γ θ T d → N ≤ θ → Γ.toHypergraph ≤ G →
    ControlsMinor G θ (inducedBySubgraph G Γ.toHypergraph θ T) L :=
  GM12.theorem_4_3_proof hS D

open Graph Hypergraph GM14 GM15 in
/-- **Graph Minors XII, (4.4)** (page 251): "For any connected surface $\Sigma$ and any integer $p
\ge 0$, there is an integer $\theta \ge 1$ such that the following is true. Let $\Gamma$ be a 2-cell
drawing in $\Sigma$, with a respectful tangle $\mathscr{T}$ of order $\ge \theta$. Let $\Gamma$ be a
subgraph of a graph $G$, let $q = \frac{1}{2} p(p - 1)$, and for $1 \le i \le q$, let $P_i$ be a
path of $G$ with distinct ends $u_i, v_i \in V(\Gamma)$ and with no other vertex or edge in
$\Gamma$. Let $P_1, \dots, P_q$ be mutually disjoint, and for all distinct $u, v \in \{u_1, v_1,
\dots, u_q, v_q\}$ let $d(u, v) \ge \theta$, where $d$ is the metric of $\mathscr{T}$. Then the
tangle in $G$ induced by $\mathscr{T}$ controls a $K_p$ minor of $G$."

Graph Minors XII (4.4), pages 251--252, for the tangle induced
from a literal drawn subgraph of the ambient graph. All vertex and
edge names are shared with the drawing, as in the paper. -/
theorem theorem_4_4 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
    ∀ (Γ : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (G : Graph S (Set S))
      (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite),
    Γ.toGraph ≤ G → HasTangleMetric Γ θ T d → N ≤ θ →
    ∀ (s r : Fin (p * (p - 1) / 2) → S) (P : Fin (p * (p - 1) / 2) → Graph S (Set S)),
    (∀ i, s i ∈ Γ.V ∧ r i ∈ Γ.V ∧ s i ≠ r i) →
    Function.Injective s → Function.Injective r → Disjoint (range s) (range r) →
    (∀ x ∈ range s ∪ range r, ∀ y ∈ range s ∪ range r, x ≠ y → N ≤ d {x} {y}) →
    (∀ i, IsHPathWithEnds G Γ.toGraph (P i) (s i) (r i)) →
    Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) →
    ControlsMinor (Hypergraph.ofGraph G hV hE) θ
      (inducedBySubgraph (Hypergraph.ofGraph G hV hE) Γ.toHypergraph θ T) (GM16.completeGraph p) :=
  GM12.theorem_4_4_proof hS p

open Graph Hypergraph GM14 GM15 in
/-- **Graph Minors XII, (4.5)** (page 252): "Let $\Sigma$ be a connected surface, and let $p \ge 0$
be an integer. Then there are integers $\theta \ge 1$ and $t \ge 0$ such that the following is true.
Let $\Gamma$ be a 2-cell drawing in $\Sigma$, with a respectful tangle $\mathscr{T}$ of order $\ge
\theta$, with metric $d$. Let $r_1, \dots, r_t$ be distinct regions of $\Gamma$ such that $d(r_i,
r_j) \ge \theta$ for $1 \le i < j \le t$. For $1 \le i \le t$, let $C_i$ be a circuit of $\Gamma$
such that $U(C_i)$ bounds $r_i$; and let $a_i, b_i, c_i, d_i \in V(C_i)$ be distinct, so that $a_i,
b_i, c_i, d_i$ occur in $V(C_i)$ in that order, and $\{a_i, b_i, c_i, d_i\}$ is free with respect to
$\mathscr{T}$. Let $\Gamma$ be a subgraph of a graph $G$, and for $1 \le i \le t$ let $P_i, Q_i$ be
paths of $G$ with ends $a_i, c_i$ and $b_i, d_i$, respectively, and with no other vertices or edges
in $\Gamma$. Let $P_1, Q_1, \dots, P_t, Q_t$ be mutually disjoint. Then the tangle in $G$ induced by
$\mathscr{T}$ controls a $K_p$ minor."

Graph Minors XII (4.5), pages 252--253, for a literal drawn
subgraph of the ambient graph and its induced tangle, as in the
paper. The eye data are the circuit, free four-vertex set, and
two external paths stated there. -/
theorem theorem_4_5 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p : ℕ) :
    ∃ k N : ℕ, 1 ≤ N ∧ ∀ (Γ : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (G : Graph S (Set S))
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite),
    Γ.toGraph ≤ G → HasTangleMetric Γ θ T d → N ≤ θ →
    ∀ (r : Fin k → Set S) (C : Fin k → Drawing S) (a b c d' : Fin k → S)
      (P Q : Fin k → Graph S (Set S)),
    Function.Injective r → (∀ i, r i ∈ Γ.R) →
    (∀ i, (C i).IsCircuit ∧ (C i).IsSubdrawing Γ ∧ (C i).U = subBd (r i)) →
    (∀ i, a i ∈ (C i).V ∧ b i ∈ (C i).V ∧ c i ∈ (C i).V ∧ d' i ∈ (C i).V) →
    (∀ i, ([a i, b i, c i, d' i]).Nodup ∧ OccurInCircuitOrder (C i) (a i) (b i) (c i) (d' i)) →
    (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ {a i, b i, c i, d' i}) →
    (∀ i, IsHPathWithEnds G Γ.toGraph (P i) (a i) (c i) ∧
      IsHPathWithEnds G Γ.toGraph (Q i) (b i) (d' i)) →
    (∀ i, Disjoint (P i).vertexSet (Q i).vertexSet) →
    (∀ i j, i ≠ j → N ≤ d (r i) (r j)) →
    (∀ i j, i ≠ j → Disjoint ((P i).vertexSet ∪ (Q i).vertexSet)
      ((P j).vertexSet ∪ (Q j).vertexSet)) →
    ControlsMinor (Hypergraph.ofGraph G hV hE) θ
      (inducedBySubgraph (Hypergraph.ofGraph G hV hE) Γ.toHypergraph θ T)
      (GM16.completeGraph p) :=
  GM12.theorem_4_5_proof hS p

/-! ## Section 5. Preserving Respect -/

open GraphMinor.GM15 GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph Function Graph SimpleGraph GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XII, (5.1)** (page 254): "Let $\Sigma_2$ be a handle of $\Sigma$, and let
$\Sigma_1, \hat{\Sigma}_1$ be defined as above. Let the two components of $\Sigma_1 \cap \Sigma_2$
be $C_1, C_2$. Let $\Gamma$ be a drawing in $\Sigma$ such that $C_1, C_2$ are $\Gamma$-normal, and
$$|V(\Gamma) \cap C_1| = |V(\Gamma) \cap C_2| = \theta,$$ and such that $\Gamma \cap \Sigma_2$ has
$\theta$ components, each a path with one end in $C_1$ and the other in $C_2$. Suppose that every
$\Gamma$-normal line $F \subseteq \Sigma_1$ with one end in $C_1$ and one end in $C_2$ satisfies $|F
\cap V(\Gamma)| \ge \theta$. Let $\mathscr{T}_1$ be a tangle in $\Gamma \cap \hat{\Sigma}_1$,
respectful towards $\hat{\Sigma}_1$, of order $\theta$, such that $V(\Gamma) \cap C_1, V(\Gamma)
\cap C_2$ are free with respect to $\mathscr{T}_1$. Then the tangle in $\Gamma$ induced by
$\mathscr{T}_1$ is respectful towards $\Sigma$." -/
theorem theorem_5_1 {S : Type w} [TopologicalSpace S] [T2Space S] {S_hat : Type w}
    [TopologicalSpace S_hat] [T2Space S_hat] (C : Fin 2 → Set S) (P₁ P₂ : Set S) (ι : P₁ → S_hat)
    (D : Fin 2 → Set S_hat) (Γ : Drawing S) (Γ₁ : Drawing S_hat) (θ : ℕ)
    (T₁ : Set (Hypergraph S_hat (Set S_hat) × Hypergraph S_hat (Set S_hat))) (P : Fin θ → Drawing S)
    (a b : Fin θ → S) (h1 : IsClosedSurface S) (h2 : ConnectedSpace S)
    (hsplit : GM12.IsHandleSplit C P₁ P₂ ι D) (hΓ : GM12.IsCappedDrawing ι Γ Γ₁)
    (hN0 : Γ.IsNormal (C 0)) (hN1 : Γ.IsNormal (C 1)) (hc0 : (Γ.V ∩ C 0).ncard = θ)
    (hc1 : (Γ.V ∩ C 1).ncard = θ)
    (hpath : ∀ i : Fin θ, a i ∈ Γ.V ∩ C 0 ∧ b i ∈ Γ.V ∩ C 1 ∧ (P i).IsPathBetween (a i) (b i) ∧
      (P i).IsSubdrawing (Γ.interSet P₂)) (hd : Pairwise (fun i j => Disjoint (P i).U (P j).U)) :
    (Γ.interSet P₂).U = ⋃ i : Fin θ, (P i).U →
    (∀ F : Set S, IsLine F → Γ.IsNormal F → F ⊆ P₁ → (F ∩ C 0).Nonempty → (F ∩ C 1).Nonempty → θ ≤
      (F ∩ Γ.V).ncard) → IsTangle Γ₁.toHypergraph θ T₁ →
    (PaintingOrDrawing.drawing Γ₁).IsRespectful θ T₁ →
    IsFreeSet Γ₁.toHypergraph T₁ θ (ι '' ((↑) ⁻¹' (Γ.V ∩ C 0))) →
    IsFreeSet Γ₁.toHypergraph T₁ θ (ι '' ((↑) ⁻¹' (Γ.V ∩ C 1))) →
    (PaintingOrDrawing.drawing Γ).IsRespectful θ (GM12.inducedAcross ι Γ Γ₁ θ T₁) :=
  GM12.theorem_5_1_proof C P₁ P₂ ι D Γ Γ₁ θ T₁ P a b h1 h2 hsplit hΓ hN0 hN1 hc0 hc1 hpath hd

open GraphMinor.GM15 GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph Function Graph SimpleGraph GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XII, (5.2)** (page 254): "Let $\Sigma_2$ be a crosscap of $\Sigma$, and let
$\Sigma_1, \hat{\Sigma}_1$ be defined as above. Let $\Gamma$ be a drawing in $\Sigma$ such that
$\Sigma_1 \cap \Sigma_2$ is $\Gamma$-normal, and $|V(\Gamma) \cap \Sigma_1 \cap \Sigma_2| =
2\theta$, and $\Gamma \cap \Sigma_2$ has $\theta$ components, each a path with ends some opposite
pair of vertices in $V(\Gamma) \cap \Sigma_1 \cap \Sigma_2$, in the natural sense. Suppose that
$\mathscr{T}_1$ is a tangle in $\Gamma \cap \hat{\Sigma}_1$, respectful towards $\hat{\Sigma}_1$, of
order $\theta$, and every subset $V(\Gamma) \cap \Sigma_1 \cap \Sigma_2$ of cardinality $\le \theta$
is free with respect to $\mathscr{T}_1$. Then the tangle in $\Gamma$ induced by $\mathscr{T}_1$ is
respectful towards $\Sigma$."

, for `θ ≥ 2`. The statement fails for `θ = 1`, because a
path with ends on the boundary of the band need not cross it.

The print fails at `θ = 1`, so the Lean assumes `2 ≤ θ`. See the corrections to (5.2) and to the
proof of (5.3) in `corrections/GM12.md`. -/
theorem theorem_5_2 {S : Type w} [TopologicalSpace S] [T2Space S] {S_hat : Type w}
    [TopologicalSpace S_hat] [T2Space S_hat] (C : Fin 1 → Set S) (P₁ P₂ : Set S) (ι : P₁ → S_hat)
    (D : Fin 1 → Set S_hat) (Γ : Drawing S) (Γ₁ : Drawing S_hat) (θ : ℕ)
    (T₁ : Set (Hypergraph S_hat (Set S_hat) × Hypergraph S_hat (Set S_hat))) (P : Fin θ → Drawing S)
    (a b : Fin θ → S) (hθ : 2 ≤ θ) (h1 : IsClosedSurface S) (h2 : ConnectedSpace S)
    (hsplit : GM12.IsCrosscapSplit C P₁ P₂ ι D) (hΓ : GM12.IsCappedDrawing ι Γ Γ₁)
    (hN0 : Γ.IsNormal (C 0)) (hc : (Γ.V ∩ C 0).ncard = 2 * θ)
    (h3 : (List.ofFn a ++ List.ofFn b).Nodup)
    (hord : GM12.IsListedInOrderOn (C 0) (List.ofFn a ++ List.ofFn b))
    (hrange : range a ∪ range b = Γ.V ∩ C 0)
    (hpath : ∀ i : Fin θ, (P i).IsPathBetween (a i) (b i) ∧ (P i).IsSubdrawing (Γ.interSet P₂))
    (hd : Pairwise (fun i j => Disjoint (P i).U (P j).U)) :
    (Γ.interSet P₂).U = ⋃ i : Fin θ, (P i).U → IsTangle Γ₁.toHypergraph θ T₁ →
    (PaintingOrDrawing.drawing Γ₁).IsRespectful θ T₁ →
    (∀ X ⊆ ι '' ((↑) ⁻¹' (Γ.V ∩ C 0)), X.ncard ≤ θ → IsFreeSet Γ₁.toHypergraph T₁ θ X) →
    (PaintingOrDrawing.drawing Γ).IsRespectful θ (GM12.inducedAcross ι Γ Γ₁ θ T₁) :=
  GM12.theorem_5_2_proof C P₁ P₂ ι D Γ Γ₁ θ T₁ P a b hθ h1 h2 hsplit hΓ hN0 hc h3 hord hrange hpath hd

open Metric GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph in
/-- **Graph Minors XII, (5.3)** (page 255): "Let $\Sigma$ be a connected surface, and let $C_1,
\dots, C_t$ be mutually disjoint $O$-arcs in $\Sigma$. Let $\Sigma_1, \Sigma_2$ be 2-manifolds with
boundary, such that $\Sigma_1 \cup \Sigma_2 = \Sigma$ and $$\Sigma_1 \cap \Sigma_2 = bd(\Sigma_1) =
bd(\Sigma_2) = C_1 \cup \dots \cup C_t.$$ Let $\hat{\Sigma}_1$ be a surface with $\Sigma_1 \subseteq
\hat{\Sigma}_1$, such that each $C_i$ bounds an open disc $D_i \subseteq \hat{\Sigma}_1$, and $D_1,
\dots, D_t$ are mutually disjoint, and $\hat{\Sigma}_1 - \Sigma_1 = D_1 \cup \dots \cup D_t$. Let
$\Gamma$ be a drawing in $\Sigma$, such that $C_1 \cup \dots \cup C_t$ is $\Gamma$-normal, and let
$\Gamma_1 = \Gamma \cap \hat{\Sigma}_1$. Let $\mathscr{T}_1$ be a tangle in $\Gamma_1$ of order
$\theta$, respectful towards $\hat{\Sigma}_1$, and let $\mathscr{T}$ be a tangle in $\Gamma$ induced
by $\mathscr{T}_1$. Suppose that (i) for $1 \le i < j \le t$, every $\Gamma_1$-normal line $F
\subseteq \Sigma_1$ with one end in $C_i$ and the other in $C_j$ satisfies $|F \cap V(\Gamma_1)| \ge
\theta$ (ii) for $1 \le i \le t$, $|C_i \cap V(\Gamma_1)| \ge \theta$ and every $X \subseteq C_i
\cap V(\Gamma)$ with $|X| \le \theta$ is free with respect to $\mathscr{T}_1$, and (iii) every
continuous $\phi \colon S^1 \to \Sigma_2$ of length $< \theta$ with $|\phi|$ $\Gamma$-normal is
null-homotopic in $\Sigma_2$. Then $\mathscr{T}$ is respectful towards $\Sigma$."

The Lean proof corrects a step of the paper's proof. See the correction to the proof of (5.3) in
`corrections/GM12.md`. -/
theorem theorem_5_3 {S T : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T]
    {n : ℕ} {C : Fin n → Set S} {P₁ P₂ : Set S} {ι : ↑P₁ → T} {D : Fin n → Set T} {Γ : Drawing S}
    {Γ₁ : Drawing T} {θ : ℕ} {𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))} [NeZero n]
    [ConnectedSpace T] (h : IsCappedSplit C P₁ P₂ ι D) (hΓ : IsCappedDrawing ι Γ Γ₁)
    (hN : ∀ k, Γ.IsNormal (C k)) (hT : IsTangle Γ₁.toHypergraph θ 𝒯)
    (hR : (PaintingOrDrawing.drawing Γ₁).IsRespectful θ 𝒯)
    (hi : ∀ k l, k ≠ l → ∀ F : Set S, IsLine F → Γ.IsNormal F → F ⊆ P₁ → (F ∩ C k).Nonempty →
      (F ∩ C l).Nonempty → θ ≤ (F ∩ Γ.V).ncard) (hm : ∀ k, θ ≤ (Γ.V ∩ C k).ncard)
    (hf : ∀ k, ∀ X ⊆ capUp ι (Γ.V ∩ C k), X.ncard ≤ θ → IsFreeSet Γ₁.toHypergraph 𝒯 θ X)
    (hiii : CurvesNull Γ P₂ θ) :
    (PaintingOrDrawing.drawing Γ).IsRespectful θ (inducedAcross ι Γ Γ₁ θ 𝒯) :=
  GM12.theorem_5_3_proof h hΓ hN hT hR hi hm hf hiii

open Metric GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph in
/-- **Graph Minors XII, (5.4)** (page 255): "Under the same hypotheses, let $F$ be a $\Gamma$-normal
line with $F \subseteq \Sigma_1$, with ends in $C_1 \cup \dots \cup C_t$, and with no other point in
$C_1 \cup \dots \cup C_t$, such that $|F \cap V(\Gamma)| < \theta$. Then there is a $\Gamma$-normal
line $\tilde{F} \subseteq C_1 \cup \dots \cup C_t$, with the same ends as $F$, such that $|\tilde{F}
\cap V(\Gamma)| \le |F \cap V(\Gamma)|$, and such that there is a closed disc $\Delta \subseteq
\Sigma_1$ bounded by $F \cup \tilde{F}$, with $(\Gamma_1 \cap \Delta, \Gamma_1 \cap
\overline{\Sigma_1 - \Delta}) \in \mathscr{T}_1$."

, for a `Γ`-normal line `F` in `Σ₁` with ends `s, t` on
the common boundary `⋃ k, C k` and no other point on it: there is a `Γ`-normal line `R` in
`⋃ k, C k` with the same ends as `F` and at most as many vertices of `Γ`, bounding with `F` a
closed disc `Δ ⊆ Σ₁` whose capped separation lies in `𝒯`. -/
theorem theorem_5_4 {S T : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T]
    {n : ℕ} {C : Fin n → Set S} {P₁ P₂ : Set S} {ι : ↑P₁ → T} {D : Fin n → Set T} {Γ : Drawing S}
    {Γ₁ : Drawing T} {θ : ℕ} {𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))}
    [ConnectedSpace T] (h : IsCappedSplit C P₁ P₂ ι D) (hΓ : IsCappedDrawing ι Γ Γ₁)
    (hN : ∀ k, Γ.IsNormal (C k)) (hT : IsTangle Γ₁.toHypergraph θ 𝒯)
    (hR : (PaintingOrDrawing.drawing Γ₁).IsRespectful θ 𝒯)
    (hi : ∀ k l, k ≠ l → ∀ F : Set S, IsLine F → Γ.IsNormal F → F ⊆ P₁ → (F ∩ C k).Nonempty →
      (F ∩ C l).Nonempty → θ ≤ (F ∩ Γ.V).ncard) (hm : ∀ k, θ ≤ (Γ.V ∩ C k).ncard)
    (hf : ∀ k, ∀ X ⊆ capUp ι (Γ.V ∩ C k), X.ncard ≤ θ → IsFreeSet Γ₁.toHypergraph 𝒯 θ X) {F : Set S}
    {s t : S} (hF : IsLineWithEnds F s t) (hst : s ≠ t) (hFN : Γ.IsNormal F)
    (hsmall : (F ∩ Γ.V).ncard < θ) (hFP : F ⊆ P₁) (hs : s ∈ ⋃ k, C k) (ht : t ∈ ⋃ k, C k)
    (hmeet : ∀ x ∈ F, x ∈ ⋃ k, C k → x = s ∨ x = t) :
    ∃ R : Set S, ∃ Δ : Set S, ∃ Δ₁ : Set T,
    IsLineWithEnds R s t ∧ Γ.IsNormal R ∧ R ⊆ ⋃ k, C k ∧
    (R ∩ Γ.V).ncard ≤ (F ∩ Γ.V).ncard ∧
    IsClosedDisc Δ ∧ Δ ⊆ P₁ ∧ discBd Δ = F ∪ R ∧
    IsClosedDisc Δ₁ ∧ capUp ι Δ ⊆ Δ₁ ∧
    (∀ x ∈ frontier Δ₁, x ∈ range ι → x ∈ capUp ι F) ∧
    ((PaintingOrDrawing.drawing Γ₁).inter Δ₁,
      (PaintingOrDrawing.drawing Γ₁).interOutside Δ₁) ∈ 𝒯 :=
  GM12.theorem_5_4_proof h hΓ hN hT hR hi hm hf hF hst hFN hsmall hFP hs ht hmeet

/-! ## Section 6. Filling in a Disc -/

open GraphMinor.GM15 GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph Function Graph SimpleGraph GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XII, (6.1)** (page 258): "In these circumstances, $d(e_1, e_{\theta/2}) \ge
\theta$."

`d(e₁, e_{θ/2}) ≥ θ`.

The print fails at `θ = 2`, so the Lean assumes `4 ≤ θ`. The Lean proof fills a gap in the paper's
proof, which computes the metric in a special radial drawing. See the corrections to (6.1) and to
its proof in `corrections/GM12.md`. -/
theorem theorem_6_1 {S : Type w} [TopologicalSpace S] [T2Space S] (Γ : Drawing S) (F Δ : Set S)
    (k θ₁ : ℕ) (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (a b : Fin k → S) (P : Fin k → Drawing S) (e_path : Fin k → Set S) (i₀ i_last : Fin k)
    (hS : IsClosedSurface S) (hconn : ConnectedSpace S) (hk : 2 ≤ k) (hθ : 2 * k < θ₁)
    (h2c : (PaintingOrDrawing.drawing Γ).IsTwoCell) (hF : IsOArc F) (hN : Γ.IsNormal F)
    (hΔ : IsClosedDisc Δ) (hb : subBd Δ = F) (hnd : (List.ofFn a ++ (List.ofFn b).reverse).Nodup)
    (hord : GM12.IsListedInOrderOn F (List.ofFn a ++ (List.ofFn b).reverse))
    (hV : range a ∪ range b = F ∩ Γ.V)
    (hP : ∀ i : Fin k, (P i).IsPathBetween (a i) (b i) ∧ (P i).IsSubdrawing (Γ.interSet Δ))
    (hdis : Pairwise (fun i j => Disjoint (P i).U (P j).U)) :
    (Γ.interSet Δ).U = ⋃ i : Fin k, (P i).U → (∀ i : Fin k, e_path i ∈ (P i).E) →
    (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ Δ)))).IsTwoCell →
    IsRespectfulDrawingTangle (Γ.interSet (closure (univ \ Δ))) θ₁ T₁ →
    HasTangleMetric Γ θ₁
    (GM12.inducedBySubgraph Γ.toHypergraph (Γ.interSet (closure (univ \ Δ))).toHypergraph θ₁ T₁) d →
    IsFreeSet (Γ.interSet (closure (univ \ Δ))).toHypergraph T₁ θ₁
    (F ∩ (Γ.interSet (closure (univ \ Δ))).V) → i₀.1 = 0 → i_last.1 = k - 1 → 2 * k ≤
    d (e_path i₀) (e_path i_last) :=
  GM12.theorem_6_1_proof Γ F Δ k θ₁ T₁ d a b P e_path i₀ i_last hS hconn hk hθ h2c hF hN hΔ hb hnd hord hV hP hdis

/-! ## Section 7. Deletion -/

open Hypergraph GraphMinor.GM10 in
/-- **(7.1)** of Graph Minors XII (page 267): "Let* $\mathscr{T}$ *be a tangle of order* $\theta \ge
1$ *in a graph* $G$, *and let* $(A',
B') \in \mathscr{T}$ *have order* $1$. *Let* $$\mathscr{T}' = \{(A \cap B', B \cap B') : (A,
B) \in \mathscr{T}\};$$ *then* $\mathscr{T}'$ *is a tangle in* $B'$ *of order* $\theta$." The proof
works for hypergraphs. -/
theorem theorem_7_1 {α : Type u_1} {β : Type u_2} {G A' B' : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (hT : IsTangle G θ 𝒯) (hm : (A', B') ∈ 𝒯)
    (h1 : separationOrder A' B' = 1) :
    IsTangle B' θ (restrictTangle 𝒯 B') :=
  GM12.theorem_7_1_proof hT hm h1

open GM11 GM14 Hypergraph in
/-- **Graph Minors XII, (7.2)** (page 259): "Let $\mathscr{T}$ be a respectful tangle of order
$\theta \ge 2$ in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$, and let its metric be
$d$. Let $F$ be a $\Gamma$-normal $O$-arc in $\Sigma$ with $|F \cap V(\Gamma)| = 1$; let $F \cap
V(\Gamma) = \{v\}$, let $r$ be the region of $\Gamma$ including $F - \{v\}$, let $\text{ins}(F) =
\Delta$, and let $\Gamma' = \Gamma | \overline{\Sigma - \Delta}$. Then $\Gamma'$ is 2-cell, and
$d(a, \{v\}) \le 1$ for all $a \in A(\Gamma) - A(\Gamma')$. Moreover, let $$\mathscr{T}' = \{(A \cap
\Gamma', B \cap \Gamma') : (A, B) \in \mathscr{T}\};$$ then $\mathscr{T}'$ is a respectful tangle in
$\Gamma'$ of order $\theta$. Let its metric be $d'$, and let $r'$ be the region of $\Gamma'$
including $r$; then (i) $d'(a, b) \ge d(a, b)$ for all $a, b \in A(\Gamma) \cap A(\Gamma')$, and
(ii) $d'(a, r') \ge d(a, r)$ for all $a \in A(\Gamma) \cap A(\Gamma')$."

Graph Minors XII, (7.2), pages 259–260. Deleting the selected
inside of a normal circle through one vertex preserves the order of
the respectful tangle. Distances between shared atoms, and distances
from shared atoms to the enlarged region, do not decrease. -/
theorem theorem_7_2 {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ)
    (hd : HasTangleMetric Γ θ T d) {D F r : Set S} {v : S} (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v}) (hr : r ∈ Γ.R)
    (hFr : F \ {v} ⊆ r)
    (hm : ((PaintingOrDrawing.drawing Γ).inter D, (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T) :
    (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ D)))).IsTwoCell ∧
    (∀ a ∈ Γ.A \ (Γ.interSet (closure (univ \ D))).A, d a {v} ≤ 1) ∧
    ∃ (d' : Set S → Set S → ℕ) (r' : Set S),
      HasTangleMetric (Γ.interSet (closure (univ \ D))) θ
        (restrictTangle T (Γ.interSet (closure (univ \ D))).toHypergraph) d' ∧
      r' ∈ (Γ.interSet (closure (univ \ D))).R ∧ r ⊆ r' ∧
      (∀ a ∈ Γ.A ∩ (Γ.interSet (closure (univ \ D))).A,
        ∀ b ∈ Γ.A ∩ (Γ.interSet (closure (univ \ D))).A, d a b ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ (Γ.interSet (closure (univ \ D))).A, d a r ≤ d' a r') :=
  GM12.theorem_7_2_proof hS hθ hd hD hbd hn hFV hr hFr hm

open GM11 GM10 GM14 Hypergraph in
/-- **Graph Minors XII, (7.3)** (page 261): "Let $\mathscr{T}$ be a respectful tangle of order
$\theta \ge 2$ in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$, and let its metric be
$d$. Let $v \in V(\Gamma)$, such that $\Gamma \setminus v$ is 2-cell. Then there is a respectful
tangle $\mathscr{T}'$ of order $\theta - 1$ in $\Gamma \setminus v$, with metric $d'$, such that if
$r'$ is the region of $\Gamma \setminus v$ containing $v$, then (i) $d'(a, b) \ge d(a, b) - 2$ for
all $a, b \in A(\Gamma) \cap A(\Gamma \setminus v)$, and (ii) $d'(a, r') \ge d(a, \{v\}) - 1$ for
all $a \in A(\Gamma) \cap A(\Gamma \setminus v)$."

Graph Minors XII, (7.3), pages 261--262. A two-cell vertex
deletion has a respectful tangle of order one less, with shared
atom distances decreasing by at most two and distance to the
merged region decreasing by at most one. The finite selected-disc
reduction corrects the paper's assertion that the old
radial drawing has no parallel spokes at the vertex, which fails
when there is a contractible loop at the vertex. See the correction
to the proof of (7.3) in `corrections/GM12.md`. -/
theorem theorem_7_3 {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ)
    (hd : HasTangleMetric Γ θ T d) {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d' : Set S → Set S → ℕ) (r : Set S),
    HasTangleMetric (deleteVertices Γ {v}) (θ - 1) T' d' ∧
    r ∈ (deleteVertices Γ {v}).R ∧ v ∈ r ∧
    (∀ a ∈ Γ.A ∩ (deleteVertices Γ {v}).A,
      ∀ b ∈ Γ.A ∩ (deleteVertices Γ {v}).A, d a b - 2 ≤ d' a b) ∧
    (∀ a ∈ Γ.A ∩ (deleteVertices Γ {v}).A, d a {v} - 1 ≤ d' a r) :=
  GM12.theorem_7_3_proof hS hθ hd hv htwo

open GM11 GM10 GM14 in
/-- **Graph Minors XII, (7.4)** (page 262): "Let $\mathscr{T}$ be a respectful tangle of order
$\theta \ge 2$ in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$, and let its metric be
$d$. Let $v \in V(\Gamma)$. Then there is a 2-cell component $\Gamma'$ of $\Gamma \setminus v$ and a
respectful tangle $\mathscr{T}'$ of order $\theta - 1$ in $\Gamma'$, with metric $d'$, such that if
$r'$ is the region of $\Gamma'$ containing $v$, then (i) $U(\Gamma) \subseteq U(\Gamma') \cup r'$
(ii) $d'(a, b) \ge d(a, b) - 2$ for all $a, b \in A(\Gamma) \cap A(\Gamma')$ (iii) $d'(a, r') \ge
d(a, \{v\}) - 1$ for all $a \in A(\Gamma) \cap A(\Gamma')$, and (iv) $d(a, \{v\}) \le 2$ for all $a
\in A(\Gamma)$ with $a \subseteq r'$."

Graph Minors XII, (7.4), pages 262--263. Vertex deletion has
a two-cell component with a respectful tangle of order one less,
shared-atom distances decreasing by at most two, and distance
to its region of the deleted vertex decreasing by at most one.
All original atoms contained in that region have old distance
at most two from the deleted vertex. The component condition
uses the connected components of the drawing's point set. -/
theorem theorem_7_4 {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ)
    (hd : HasTangleMetric Γ θ T d) {v : S} (hv : v ∈ Γ.V) :
    ∃ (Γ' : Drawing S) (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d' : Set S → Set S → ℕ) (r : Set S),
    Γ'.IsSubdrawing (deleteVertices Γ {v}) ∧
    Γ'.U ∈ componentsIn (deleteVertices Γ {v}).U ∧
    HasTangleMetric Γ' (θ - 1) T' d' ∧ r ∈ Γ'.R ∧ v ∈ r ∧
    Γ.U ⊆ Γ'.U ∪ r ∧
    (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 2 ≤ d' a b) ∧
    (∀ a ∈ Γ.A ∩ Γ'.A, d a {v} - 1 ≤ d' a r) ∧
    (∀ a ∈ Γ.A, a ⊆ r → d a {v} ≤ 2) :=
  GM12.theorem_7_4_proof hS hθ hd hv

open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph Function in
/-- **Graph Minors XII, (7.5)** (page 263): "Let $\mathscr{T}$ be a respectful tangle of order
$\theta \ge 3$ in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$, and let its metric be
$d$. Let $r$ be a region of $\Gamma$, and let $Z$ be the set of vertices of $\Gamma$ incident with
$r$. Then there is a 2-cell"

The Lean proof fills a gap in Case 2 of the paper's proof (see the correction to the proof of
(7.5) in `corrections/GM12.md`). It also writes out the steps that the paper leaves out. -/
theorem theorem_7_5 (S : Type u) [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (r : Set S)
    (hθ : 3 ≤ θ) (hd : HasTangleMetric Γ θ T d) (hr : r ∈ Γ.R) :
    ∃ (Γ' : Drawing S) (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S →
      Set S → ℕ) (r' : Set S), Γ'.IsSubdrawing (deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}) ∧
    (PaintingOrDrawing.drawing Γ').IsTwoCell ∧ HasTangleMetric Γ' (θ - 2) T' d' ∧ r' ∈ Γ'.R ∧ r ⊆
    r' ∧ Γ.U ⊆ Γ'.U ∪ r' ∧ (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 ≤ d' a b) ∧
    (∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 ≤ d' a r') ∧ (∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 3) :=
  GM12.theorem_7_5_proof S hS Γ θ T d r hθ hd hr

open Function GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph in
/-- **(7.6)** of Graph Minors XII (page 266):
"(7.6) *Let $k \ge 0$ be an integer, and let $\mathscr{T}$ be a respectful tangle of order
$\theta \ge 2k + 1$ in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$. Let its metric be
$d$. Let $r$ be a region of $\Gamma$, and let $Z$ be the set of all vertices $v$ of $\Gamma$ such
that there is a $\Gamma$-normal line $F$ with $v \in F$, $F \cap r \ne \emptyset$ and
$|F \cap V(\Gamma)| \le k$. Then there is a 2-cell subdrawing $\Gamma'$ of $\Gamma \setminus Z$, and
a respectful tangle $\mathscr{T}'$ of order $\theta - 2k$ in $\Gamma'$, with metric $d'$, such that
if $r'$ is the region of $\Gamma'$ with $r \subseteq r'$, then*
$$
\begin{aligned}
\text{(i)} \quad & U(\Gamma) \subseteq U(\Gamma') \cup r' \\
\text{(ii)} \quad & d'(a, b) \ge d(a, b) - 4k \text{ for all } a, b \in A(\Gamma) \cap A(\Gamma') \\
\text{(iii)} \quad & d'(a, r') \ge d(a, r) - 2k \text{ for all } a \in A(\Gamma) \cap A(\Gamma'),
\text{ and} \\
\text{(iv)} \quad & d(a, r) \le 2k + 1 \text{ for all } a \in A(\Gamma) \text{ with } a \subseteq
r'.
\end{aligned}
$$
*In particular, if $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a \subseteq a'$ and
$b \subseteq b'$, then $d'(a', b') \ge d(a, b) - 4k - 2$.*" -/
theorem theorem_7_6 {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    [ConnectedSpace S] {Γ : Drawing S} {θ : ℕ} (k : ℕ)
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ} {r : Set S}
    (hθ : 2 * k + 1 ≤ θ) (hd : HasTangleMetric Γ θ T d) (hr : r ∈ Γ.R) :
    ∃ (Γ' : Drawing S)
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d' : Set S → Set S → ℕ) (r' : Set S),
    Γ'.IsSubdrawing (deleteVertices Γ (regionLineVertices Γ r k)) ∧
    (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
    HasTangleMetric Γ' (θ - 2 * k) T' d' ∧
    r' ∈ Γ'.R ∧ r ⊆ r' ∧
    Γ.U ⊆ Γ'.U ∪ r' ∧
    (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 * k ≤ d' a b) ∧
    (∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 * k ≤ d' a r') ∧
    (∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 2 * k + 1) ∧
    (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
      a ⊆ a' → b ⊆ b' → d a b - 4 * k - 2 ≤ d' a' b') :=
  GM12.theorem_7_6_proof hS k hθ hd hr

open Function unitInterval GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph in
/-- **(7.7)** of Graph Minors XII (page 268):
"(7.7) *Let $\mathscr{T}$ be a respectful tangle of order $\theta$ in a 2-cell drawing $\Gamma$ in a
connected surface $\Sigma$; let its metric be $d$. Let $\Gamma'$ be a 2-cell subdrawing of $\Gamma$,
and let $\mathscr{T}'$ be a respectful tangle of order $\theta' \le \theta$ in $\Gamma'$, with
metric $d'$. Then*
(i) *for $k \ge 0$, if $d'(a', b') \ge d(a, b) - k$ for all $a, b \in A(\Gamma)$ and
$a', b' \in A(\Gamma')$ with $a \subseteq a'$ and $b \subseteq b'$, then
$d(a, b) \ge \min(d'(a', b'), \theta - k)$ for all such $a, b, a', b'$*
(ii) *if $\theta = \theta'$ and $\mathscr{T}$ is the tangle in $\Gamma$ induced by $\mathscr{T}'$,
then $d(a, b) \ge d'(a', b')$ for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with
$a \subseteq a'$ and $b \subseteq b'$.*" -/
theorem theorem_7_7 {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    [ConnectedSpace S] {Γ Γ' : Drawing S} {θ θ' : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d d' : Set S → Set S → ℕ}
    (hd : HasTangleMetric Γ θ T d) (hsub : Γ'.IsSubdrawing Γ)
    (htc' : (PaintingOrDrawing.drawing Γ').IsTwoCell) (hθ : θ' ≤ θ)
    (hd' : HasTangleMetric Γ' θ' T' d') :
    (∀ k : ℕ,
      (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d a b - k ≤ d' a' b') →
      ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → min (d' a' b') (θ - k) ≤ d a b) ∧
    (θ = θ' → T = inducedBySubgraph Γ.toHypergraph Γ'.toHypergraph θ' T' →
      ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d' a' b' ≤ d a b) :=
  GM12.theorem_7_7_proof hS hd hsub htc' hθ hd'

open Function GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph in
/-- **(7.8)** of Graph Minors XII (page 268):
"Let $k \ge 0$ be an integer, and let $\mathscr{T}$ be a respectful tangle of order $\theta
\ge 2k + 2$ in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$. Let its metric be
$d$. Let $c \in A(\Gamma)$, and let $\Gamma'$ be a 2-cell subdrawing of $\Gamma$ such that
$d(c, e) \le k$ for all $e \in E(\Gamma) - E(\Gamma')$, and such that if $c \in E(\Gamma')$
then $k \ge 2$. Then there is a respectful tangle $\mathscr{T}'$ of order $\theta - 2k$ in
$\Gamma'$, with metric $d'$, such that $d'(a', b') \ge d(a, b) - 4k - 2$ for all $a, b \in
A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a \subseteq a'$ and $b \subseteq b'$."

Note on the paper: the printed statement of (7.8) writes "if `c ∈ E(Γ')` then `k ≥ 2`", which is a
misprint for "if `c ∈ E(Γ) - E(Γ')` then `k ≥ 2`" (as used on page 269 line 806: "Since $e \in
E(\Gamma) - E(\Gamma')$ ... and since $k \ge 2$ if $e = c$", and as printed in (7.10) on page 270).
We
state `theorem_7_8_proof` with the weaker, intended hypothesis `c ∈ Γ.E \ Γ'.E → 2 ≤ k`.

The print fails for `c ∈ E(Γ) - E(Γ')` at `k = 0`, so the Lean assumes `2 ≤ k` in that case. See
the correction to (7.8) in `corrections/GM12.md`. -/
theorem theorem_7_8 {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    [ConnectedSpace S] {Γ Γ' : Drawing S} {θ k : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ} {c : Set S}
    (hθ : 2 * k + 2 ≤ θ) (hd : HasTangleMetric Γ θ T d) (hc : c ∈ Γ.A) (hSub : Γ'.IsSubdrawing Γ)
    (h2cell' : (PaintingOrDrawing.drawing Γ').IsTwoCell) (hdist : ∀ e ∈ Γ.E \ Γ'.E, d c e ≤ k)
    (hck : c ∈ Γ.E \ Γ'.E → 2 ≤ k) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d' : Set S → Set S → ℕ),
    HasTangleMetric Γ' (θ - 2 * k) T' d' ∧
    ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
      a ⊆ a' → b ⊆ b' → d a b - 4 * k - 2 ≤ d' a' b' :=
  GM12.theorem_7_8_proof hS hθ hd hc hSub h2cell' hdist hck

open Function GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph in
/-- **(7.9)** of Graph Minors XII (page 270):
"Let $k \ge 0$ be an integer. Let $\mathscr{T}$ be a respectful tangle of order $\theta > k$
in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$; let its metric be $d$. Let
$\Gamma'$ be a 2-cell subdrawing of $\Gamma$, and let $\mathscr{T}'$ be a respectful tangle
of order $\theta - k$ in $\Gamma'$, with metric $d'$, such that $d'(a', b') \ge d(a, b) - k$
for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a \subseteq a'$ and $b
\subseteq b'$. Then $(A \cap \Gamma', B \cap \Gamma') \in \mathscr{T}'$ for all $(A, B) \in
\mathscr{T}$ of order $< \theta - k$. Moreover, if $\mathscr{T}''$ is another respectful
tangle of order $\theta - k$ in $\Gamma'$, with metric $d''$, and again $d''(a', b') \ge
d(a, b) - k$ for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a \subseteq a'$
and $b \subseteq b'$, then $\mathscr{T}'' = \mathscr{T}'$." -/
theorem theorem_7_9 {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    [ConnectedSpace S] {Γ Γ' : Drawing S} {θ k : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d d' : Set S → Set S → ℕ}
    (hd : HasTangleMetric Γ θ T d) (hSub : Γ'.IsSubdrawing Γ)
    (h2cell' : (PaintingOrDrawing.drawing Γ').IsTwoCell) (hk : k < θ)
    (hd' : HasTangleMetric Γ' (θ - k) T' d')
    (hge' : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A, a ⊆ a' → b ⊆ b' → d a b - k ≤ d' a' b') :
    (∀ A B : Hypergraph S (Set S),
      (A, B) ∈ T → separationOrder A B < θ - k →
        (A ∩ Γ'.toHypergraph, B ∩ Γ'.toHypergraph) ∈ T') ∧
    (∀ (T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d'' : Set S → Set S → ℕ),
      HasTangleMetric Γ' (θ - k) T'' d'' →
      (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d a b - k ≤ d'' a' b') →
      T'' = T') :=
  GM12.theorem_7_9_proof hS hd hSub h2cell' hk hd' hge'

open Function GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph in
/-- **(7.10)** of Graph Minors XII (pages 270–271):
"Let $k \ge 0$ be an integer, and let $\mathscr{T}$ be a respectful tangle of order $\ge 4k +
3$ in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$. Let its metric be $d$. Let
$c \in A(\Gamma)$, and let $\Gamma'$ be a 2-cell subdrawing of $\Gamma$ such that $d(c, e)
\le k$ for all $e \in E(\Gamma) - E(\Gamma')$, and such that if $c \in E(\Gamma) -
E(\Gamma')$ then* ... *$k \ge 2$. Then there is a respectful tangle $\mathscr{T}'$ of order
$\theta - 4k - 2$ in $\Gamma'$, with metric $d'$, such that $d'(a', b') \ge d(a, b) - 4k -
2$ for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a \subseteq a'$ and $b
\subseteq b'$. Moreover,* (i) *$\mathscr{T}'$ is unique* (ii) *$(A \cap \Gamma', B \cap
\Gamma') \in \mathscr{T}'$ for all $(A, B) \in \mathscr{T}$ of order $< \theta - 4k - 2$,*
(iii) *$d'(a', b') \le d(a, b)$ for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$
with $a \subseteq a'$ and $b \subseteq b'$." -/
theorem theorem_7_10 {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    [ConnectedSpace S] {Γ Γ' : Drawing S} {θ k : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ} {c : Set S}
    (hθ : 4 * k + 3 ≤ θ) (hd : HasTangleMetric Γ θ T d) (hc : c ∈ Γ.A) (hSub : Γ'.IsSubdrawing Γ)
    (h2cell' : (PaintingOrDrawing.drawing Γ').IsTwoCell) (hdist : ∀ e ∈ Γ.E \ Γ'.E, d c e ≤ k)
    (hck : c ∈ Γ.E \ Γ'.E → 2 ≤ k) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d' : Set S → Set S → ℕ),
    IsClearedTangleAux Γ Γ' T d θ k T' d' ∧
    ∀ (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d₁ : Set S → Set S → ℕ),
      HasTangleMetric Γ' (θ - 4 * k - 2) T₁ d₁ →
      (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d a b - 4 * k - 2 ≤ d₁ a' b') →
      T₁ = T' :=
  GM12.theorem_7_10_proof hS hθ hd hc hSub h2cell' hdist hck

open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15 in
/-- **Graph Minors XII, (7.11)** (page 271): "Let $\Gamma$ be a 2-cell drawing with $E(\Gamma) \ne
\emptyset$, in a connected surface $\Sigma$, with a respectful tangle $\mathscr{T}$ of order
$\theta$, with metric $d$. Let $z \in A(\Gamma)$ and let $\lambda \ge 0$ be an integer with $\lambda
< \theta$. Let $\Gamma'$ be the subdrawing of $\Gamma$ formed by all edges $e$ of $\Gamma$ with
$d(z, e) > \lambda$ and their ends. Then $\Gamma'$ is 2-cell."

Let `H` be a 2-cell drawing in a connected surface `S` with `E(H) ≠ ∅`, let `T` be a respectful
tangle in `H` of order `θ` with metric `d`, let `z ∈ A(H)` and let `λ ≥ 0` be an integer with
`z ∈ E(H) → 2 ≤ λ`. Let `Γ'` be the subdrawing of `H` formed by the edges `e` of `H` with
`d(z, e) > λ` and their ends. Suppose that `E(Γ') ≠ ∅`. Then `Γ'` is a 2-cell drawing in `S`.

The paper omits the hypothesis `z ∈ E(H) → 2 ≤ λ`, which (7.8) and (7.10) include. Without it the
statement is false, so the Lean keeps `E(H) ≠ ∅` and adds this hypothesis, as
`GM15.GM12Theorem711Statement` does. See the correction to (7.11) in `corrections/GM12.md`.

In place of `λ < θ`, the Lean assumes `E(Γ') ≠ ∅`. This implies `λ < θ`, because `d(z, e) ≤ θ` for
every edge `e` of `H`. The form with `λ < θ` and without `E(Γ') ≠ ∅` is `theorem_7_11_span` in
`GraphMinor/GM12/Section711.lean`. -/
theorem theorem_7_11 {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    [ConnectedSpace S] {H : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric H θ T d) (hE : H.E.Nonempty) {z : Set S} (hz : z ∈ H.A)
    (hz_lam : z ∈ H.E → 2 ≤ lam) (hΓ'E : (H.span ∅ {f ∈ H.E | lam < d z f}).E.Nonempty) :
    (PaintingOrDrawing.drawing (H.span ∅ {f ∈ H.E | lam < d z f})).IsTwoCell :=
  GM12.theorem_7_11_proof hS hMetric hE hz hz_lam hΓ'E

end GraphMinor.GM12
