module

public import GraphMinor.GM09.Basic
public import GraphMinor.GM09.CircleCut
public import GraphMinor.GM09.CliqueDiscs
public import GraphMinor.GM09.Defs
public import GraphMinor.GM09.DiscDrawing
public import GraphMinor.GM09.PlanarNests
public import GraphMinor.GM09.Restriction
public import GraphMinor.GM09.Section10c
public import GraphMinor.GM09.Section10d
public import GraphMinor.GM09.Section10f
public import GraphMinor.GM09.Section11a
public import GraphMinor.GM09.Section11b
public import GraphMinor.GM09.Section2c
public import GraphMinor.GM09.Section4b
public import GraphMinor.GM09.Section6
public import GraphMinor.GM09.Section6b
public import GraphMinor.GM09.Section6c
public import GraphMinor.GM09.Section7
public import GraphMinor.Surface.Crossing
import GraphMinor.GM09.NestUncrossing
import GraphMinor.GM09.Park
import GraphMinor.GM09.Section10
import GraphMinor.GM09.Section10e
import GraphMinor.GM09.Section10g
import GraphMinor.GM09.Section11d
import GraphMinor.GM09.Section2b
import GraphMinor.GM09.Section2d
import GraphMinor.GM09.Section2e
import GraphMinor.GM09.Section3a
import GraphMinor.GM09.Section3b
import GraphMinor.GM09.Section3c
import GraphMinor.GM09.Section4a
import GraphMinor.GM09.Section4c
import GraphMinor.GM09.Section5a
import GraphMinor.GM09.Section5b
import GraphMinor.GM09.Section8
import GraphMinor.GM09.Section9

/-!
# Graph Minors IX. Disjoint crossed paths

N. Robertson and P. D. Seymour, J. Combin. Theory Ser. B 49 (1990) 40–77.

This file lists every numbered result of the paper in order. The proofs are in the other
files of this folder and, for algorithms, in `GraphMinor/Compute/`. The errors of the paper, and how
the Lean statements and proofs correct them, are listed in `corrections/GM09.md`.
-/

public section

namespace GraphMinor.GM09

/-! ## Section 1. Introduction -/

/-! ## Section 2. Two Crossing Paths -/

section

open Set Graph GraphMinor.Surface GraphMinor.GM06

universe u v

/-- **Graph Minors IX, (2.1)** (page 43):
"Let $G$ be a simple graph and let $Z \subseteq V(G)$. Let $s, t \in V(G)$ be distinct and
such that there is a path between $s$ and $t$ avoiding $Z$. Choose a subgraph $H$ of $G$
maximal such that $Z$ catches $H$, and there is a path of $G$ between $s$ and $t$ avoiding
$V(H)$. Let $K = G \setminus V(H)$, and let $P$ be a path of $K$ between $s$ and $t$. Then
either $P = K$, or there is a separation $(G_1, G_2)$ of $G$ with $\{s, t\} \subseteq
V(G_1)$, $|V(G_1 \cap G_2)| = 2$, $E(P \cap G_2) \ne \emptyset$ (and hence $G_1 \cap G_2
\subseteq P$), $H \subseteq G_1$, and $V(G_1) \ne V(G)$." -/
theorem theorem_2_1 {α : Type u} {β : Type v}
    {G H P : Graph α β} {Z : Set α} {s t : α}
    (hG_loopless : ∀ x : α, ¬ G.Adj x x)
    (hG_simple : ∀ e₁ e₂ x y, G.IsLink e₁ x y → G.IsLink e₂ x y → e₁ = e₂)
    (hst : s ≠ t)
    (hHG : H ≤ G) (hZ : Catches Z H)
    (hmax : ∀ H' : Graph α β, H ≤ H' → H' ≤ G → Catches Z H' →
      (∃ Q : Graph α β, IsGraphPathWithEnds G Q s t ∧ Avoids Q V(H')) → H' = H)
    (hPK : IsGraphPathWithEnds (deleteVertices G V(H)) P s t) :
    P = deleteVertices G V(H) ∨
      ∃ G₁ G₂ : Graph α β,
        IsGraphSeparation G G₁ G₂ ∧
        {s, t} ⊆ V(G₁) ∧
        (V(G₁) ∩ V(G₂)).ncard = 2 ∧
        (E(P) ∩ E(G₂)).Nonempty ∧
        subgraphInter G G₁ G₂ ≤ P ∧
        H ≤ G₁ ∧
        V(G₁) ≠ V(G) := by exact GraphMinor.GM09.theorem_2_1_proof hG_loopless hG_simple hst hHG hZ hmax hPK

end

section

open Set Graph Surface

universe u v

/-- **Graph Minors IX, (2.2)** (page 44):
"Let $G$ be a graph and let $X, Y \subseteq V(G)$. Let $k \ge 0$ be an integer such that there are
$k$ mutually disjoint $X \to Y$ paths. Let $X' \subseteq X$, $Y' \subseteq Y$ be such that
$|X'| = |Y'| \le k$ and such that $X' \Rightarrow Y'$ with respect to $X, Y$. Then there exist
$X'' \subseteq X$ and $Y'' \subseteq Y$ such that $X' \subseteq X''$, $Y' \subseteq Y''$,
$|X''| = |Y''| = k$ and $X'' \Rightarrow Y''$ with respect to $X, Y$." -/
theorem theorem_2_2 {α : Type u} {β : Type v}
    {G : Graph α β} [Finite V(G)] {X Y X' Y' : Set α} {k : ℕ}
    (hX : X ⊆ V(G)) (hY : Y ⊆ V(G))
    (hk : ∃ Q : Fin k → Graph α β, Pairwise (fun i j => Disjoint V(Q i) V(Q j)) ∧
      ∀ i : Fin k, IsFromToPath G (Q i) X Y)
    (hX' : X' ⊆ X) (hY' : Y' ⊆ Y) (_hcard : X'.ncard = Y'.ncard) (hle : X'.ncard ≤ k)
    (hred : RedirectsTo G X Y X' Y') :
    ∃ X'' Y'' : Set α, X'' ⊆ X ∧ Y'' ⊆ Y ∧ X' ⊆ X'' ∧ Y' ⊆ Y'' ∧
      X''.ncard = k ∧ Y''.ncard = k ∧ RedirectsTo G X Y X'' Y'' := by exact GraphMinor.GM09.theorem_2_2_proof hX hY hk hX' hY' _hcard hle hred

end

section

open Set Graph GraphMinor.Surface GraphMinor.GM06

universe u v

/-- **Graph Minors IX, (2.3)** (page 44):
"Suppose that $\{P_1, P_2, P_3\}$ is a tripod in $(G, \Omega)$. Then either $(G, \Omega)$"

**Graph Minors IX, (2.3)** (pages 44–45): -/
theorem theorem_2_3 {α : Type u} {β : Type v}
    (S : Society α β) {P₁ P₂ P₃ : Graph α β}
    (htripod : S.IsTripod P₁ P₂ P₃) :
    (∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂) ∨
    (∃ G₁ G₂ : Graph α β, S.IsInternalKSeparation 3 G₁ G₂ ∧
      subgraphUnion S.G (subgraphUnion S.G P₁ P₂) P₃ ≤ G₁) := by exact GraphMinor.GM09.theorem_2_3_proof S htripod

end

section

open Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11
open Classical
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (2.4)** (page 45):
"Let $(G, \Omega)$ be a 3-connected society with no cross or tripod. Then $(G, \Omega)$ is rural."

Dot-notation alias for `theorem_2_4`. -/
theorem theorem_2_4 {α : Type u} {β : Type v}
    (S : Society α β)
    (hconn : S.IsKConnected 3)
    (hnocross : ¬ ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂)
    (hnotripod : ¬ ∃ T₁ T₂ T₃ : Graph α β, S.IsTripod T₁ T₂ T₃) :
    S.IsRuralSociety := by exact GraphMinor.GM09.Society.theorem_2_4_proof S hconn hnocross hnotripod

end

/-! ## Section 3. ATTACHMENTS -/

section

open Set Graph GraphMinor GraphMinor.Surface
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (3.1)** (page 47):
"Any crooked transaction has at most one overpass." -/
theorem theorem_3_1 {α : Type u} {β : Type v}
    (S : Society α β) {P_set : Set (Graph α β)}
    (_hcrooked : S.IsCrookedTransaction P_set)
    {P₁ P₂ : Graph α β} (h₁ : S.IsOverpass P_set P₁) (h₂ : S.IsOverpass P_set P₂) :
    P₁ = P₂ := by exact GraphMinor.GM09.Society.theorem_3_1_proof S _hcrooked h₁ h₂

end

section

open Set Graph GraphMinor GraphMinor.Surface
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (3.2)** (page 47):
"Every attachment to a crooked transaction that is not exchangeable is an overpass attachment." -/
theorem theorem_3_2 {α : Type u} {β : Type v}
    (S : Society α β)
    {P_set : Set (Graph α β)} {P : Graph α β}
    (hcrooked : S.IsCrookedTransaction P_set)
    (hatt : S.IsAttachment P_set P)
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P) :
    S.IsOverpassAttachment P_set P := by exact GraphMinor.GM09.Society.theorem_3_2_proof S hcrooked hatt hnot_exch

end

section

open Set Graph GraphMinor GraphMinor.Surface
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (3.3)** (page 48):
"Let $\mathscr{P}$ be a crooked transaction in $(G, \Omega)$. If $P$ and $P'$ are both
non-exchangeable attachments to $\mathscr{P}$ and $P, P'$ are disjoint, then there is a
crooked transaction $\mathscr{P}'$ with $|\mathscr{P}'| = |\mathscr{P}| + 1$ and* $$ \bigcup
\mathscr{P}' \subseteq \bigcup \mathscr{P} \cup (P \cup P'). $$ *Moreover, the two
attachments have a common leg, which is an overpass of $\mathscr{P}$, and no edge of this
leg between the two feet is in $\bigcup \mathscr{P}'$." -/
theorem theorem_3_3 {α : Type u} {β : Type v}
    (S : Society α β)
    {P_set : Set (Graph α β)} {P P' : Graph α β}
    (hcrooked : S.IsCrookedTransaction P_set)
    (hatt : S.IsAttachment P_set P)
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P)
    (hatt' : S.IsAttachment P_set P')
    (hnot_exch' : ¬ S.IsExchangeableAttachment P_set P')
    (hdisj_PP' : Disjoint V(P) V(P')) :
    ∃ P₁ ∈ P_set,
      S.IsOverpass P_set P₁ ∧
      S.IsLeg P_set P P₁ ∧
      S.IsLeg P_set P' P₁ ∧
      ∃ b b' : α,
        S.IsFoot P_set P b ∧ b ∈ V(P₁) ∧
        S.IsFoot P_set P' b' ∧ b' ∈ V(P₁) ∧
        ∃ M : Graph α β,
          M ≤ P₁ ∧ IsGraphPathWithEnds P₁ M b b' ∧
          ∃ P_set' : Set (Graph α β),
            S.IsCrookedTransaction P_set' ∧
            P_set'.ncard = P_set.ncard + 1 ∧
            S.transactionUnion P_set' ≤
              subgraphUnion S.G (S.transactionUnion P_set) (subgraphUnion S.G P P') ∧
            Disjoint E(M) E(S.transactionUnion P_set') := by exact GraphMinor.GM09.Society.theorem_3_3_proof S hcrooked hatt hnot_exch hatt' hnot_exch' hdisj_PP'

end

section

open Set Graph GraphMinor GraphMinor.Surface
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (3.4)** (page 48):
"Let $p \ge 2$ be an integer, with $p \ne 3$. If $\mathscr{P}$ is a crooked transaction of
cardinality $\ge p$ then some subset of $\mathscr{P}$ is a crooked transaction of cardinality $p$." -/
theorem theorem_3_4 {α : Type u} {β : Type v}
    (S : Society α β) {p : ℕ} (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    {P_set : Set (Graph α β)} (hcrooked : S.IsCrookedTransaction P_set)
    (hcard : p ≤ P_set.ncard) :
    ∃ P_set' ⊆ P_set, P_set'.ncard = p ∧ S.IsCrookedTransaction P_set' := by exact GraphMinor.GM09.Society.theorem_3_4_proof S hp2 hp3 hcrooked hcard

end

/-! ## Section 4. Separating $\Omega$-Paths -/

section

open Set Graph GraphMinor GraphMinor.Surface
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (4.1)** (page 49):
"Let $\mathscr{P}$ be a transaction in $(G, \Omega)$, such that every peripheral member is
non-separating. Then there is a crooked transaction $\mathscr{P}'$ in $(G, \Omega)$ with
$|\mathscr{P}'| \ge |\mathscr{P}|$." -/
theorem theorem_4_1 {α : Type u} {β : Type v} (S : Society α β)
    {P_set : Set (Graph α β)}
    (htrans : S.IsTransaction P_set)
    (hnonsep : ∀ P ∈ P_set, S.IsPeripheralIn P_set P → S.IsNonSeparatingOmegaPath P) :
    ∃ P_set' : Set (Graph α β), S.IsCrookedTransaction P_set' ∧ P_set.ncard ≤ P_set'.ncard := by exact GraphMinor.GM09.Society.theorem_4_1_proof S htrans hnonsep

end

section

open Set Graph GraphMinor GraphMinor.Surface
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (4.2)** (page 50):
"Let* **S** *be true. Suppose that $w, w' \in W(\mathscr{Q})$ are distinct, and that neither
of the corresponding attachments is exchangeable. Then $w, w'$ are both ends of the same
member of $\mathscr{Q}$." -/
theorem theorem_4_2 {α : Type u} {β : Type v} (S : Society α β)
    {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B)
    {w w' : α} (_hw_ne : w ≠ w')
    {P P' : Graph α β}
    (hatt : S.IsCorrespondingAttachment P_set Q_set w P)
    (hatt' : S.IsCorrespondingAttachment P_set Q_set w' P')
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P)
    (hnot_exch' : ¬ S.IsExchangeableAttachment P_set P') :
    ∃ Q ∈ Q_set, w ∈ pathEnds S.G Q ∧ w' ∈ pathEnds S.G Q := by exact GraphMinor.GM09.Society.theorem_4_2_proof S hS _hw_ne hatt hatt' hnot_exch hnot_exch'

end

section

open Set Graph GraphMinor GraphMinor.Surface
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (4.3)** (page 50):
"Let* **S** *be true. For every $Q \in \mathscr{Q}$ except possibly one, either* (i) *$Q \cap
\bigcup \mathscr{P} = \emptyset$, or* (ii) *both ends of $Q$ are in $V(\mathscr{P})$, or*
(iii) *$Q$ meets exactly one member $P$ of $\mathscr{P}$, $P \cap Q$ is a path, and $P, Q$
and $P \cap Q$ have a common end, and the other end of $Q$ is not in $V(\mathscr{P})$.* *If
(i), (ii), (iii) are all false for some $Q \in \mathscr{Q}$ then $\mathscr{P}$ has an
overpass." -/
theorem theorem_4_3 {α : Type u} {β : Type v} (S : Society α β)
    {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B) :
    (∀ Q₁ ∈ Q_set, ∀ Q₂ ∈ Q_set,
      ¬ (Disjoint V(Q₁) V(S.transactionUnion P_set) ∨
          pathEnds S.G Q₁ ⊆ S.transactionEnds P_set ∨
          S.IsHalfCovered P_set Q₁) →
      ¬ (Disjoint V(Q₂) V(S.transactionUnion P_set) ∨
          pathEnds S.G Q₂ ⊆ S.transactionEnds P_set ∨
          S.IsHalfCovered P_set Q₂) →
      Q₁ = Q₂) ∧
    (∀ Q ∈ Q_set,
      ¬ (Disjoint V(Q) V(S.transactionUnion P_set) ∨
          pathEnds S.G Q ⊆ S.transactionEnds P_set ∨
          S.IsHalfCovered P_set Q) →
      ∃ P₁ ∈ P_set, S.IsOverpass P_set P₁) := by exact GraphMinor.GM09.Society.theorem_4_3_proof S hS

end

section

open Set Graph GraphMinor
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (4.4)** (page 50):
"Let S be true, and let $Q_1, Q_2, Q_3 \in \mathscr{Q}$ be in order, where $Q_2$ is"

**Graph Minors IX, (4.4)** (pages 50–51): -/
theorem theorem_4_4 {α : Type u} {β : Type v} (S : Society α β)
    {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B)
    {Q₁ Q₂ Q₃ : Graph α β}
    (_hQ₁ : Q₁ ∈ Q_set) (_hQ₂ : Q₂ ∈ Q_set) (_hQ₃ : Q₃ ∈ Q_set)
    (hord : S.AreInOrder [Q₁, Q₂, Q₃])
    (hsep₂ : S.IsSeparatingOmegaPath Q₂)
    (hcov₁ : S.IsHalfCovered P_set Q₁)
    (hcov₂ : S.IsHalfCovered P_set Q₂)
    (hcov₃ : S.IsHalfCovered P_set Q₃) :
    ∃ a₂ ∈ A, ∃ b₂ ∈ B, S.IsOmegaPathWithEnds Q₂ a₂ b₂ := by exact GraphMinor.GM09.Society.theorem_4_4_proof S hS _hQ₁ _hQ₂ _hQ₃ hord hsep₂ hcov₁ hcov₂ hcov₃

end

section

open Set Function Graph GraphMinor GraphMinor.Surface
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (4.5)** (pages 51–52):
"(4.5) *Let S be true, and let $Q_1, Q_2, Q_3, Q_4, Q_5 \in \mathscr{Q}$ be in order. Suppose that
$Q_2, Q_3, Q_4$ are all separating. Then not all of $Q_1, ..., Q_5$ are half-covered.*" -/
theorem theorem_4_5 {α : Type u} {β : Type v} (S : Society α β)
    {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B)
    {Q₁ Q₂ Q₃ Q₄ Q₅ : Graph α β}
    (_hQ₁ : Q₁ ∈ Q_set) (_hQ₂ : Q₂ ∈ Q_set) (hQ₃ : Q₃ ∈ Q_set)
    (_hQ₄ : Q₄ ∈ Q_set) (_hQ₅ : Q₅ ∈ Q_set)
    (hord : S.AreInOrder [Q₁, Q₂, Q₃, Q₄, Q₅])
    (hsep₂ : S.IsSeparatingOmegaPath Q₂)
    (hsep₃ : S.IsSeparatingOmegaPath Q₃)
    (hsep₄ : S.IsSeparatingOmegaPath Q₄) :
    ¬ (S.IsHalfCovered P_set Q₁ ∧ S.IsHalfCovered P_set Q₂ ∧ S.IsHalfCovered P_set Q₃ ∧
       S.IsHalfCovered P_set Q₄ ∧ S.IsHalfCovered P_set Q₅) := by exact GraphMinor.GM09.Society.theorem_4_5_proof S hS _hQ₁ _hQ₂ hQ₃ _hQ₄ _hQ₅ hord hsep₂ hsep₃ hsep₄

end

section

open Set Function Graph GraphMinor GraphMinor.Surface
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (4.6)** (page 52):
"Let $S$ be true, with $p \ge 2$ and $p \ne 3$, let $|\mathcal{Q}| = p + 4$, and let every
member of $\mathcal{Q}$ be separating. Then $Q \cap \bigcup \mathcal{P}$ is null for some $Q
\in \mathcal{Q}$." -/
theorem theorem_4_6 {α : Type u} {β : Type v} (S : Society α β)
    {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B) (hp3 : p ≠ 3)
    (hcard_Q : Q_set.ncard = p + 4)
    (hsep : ∀ Q ∈ Q_set, S.IsSeparatingOmegaPath Q) :
    ∃ Q ∈ Q_set, Disjoint V(Q) V(S.transactionUnion P_set) := by exact GraphMinor.GM09.Society.theorem_4_6_proof S hS hp3 hcard_Q hsep

end

/-! ## Section 5. SEPARATIONS AND CROSSES -/

section

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (5.1)** (page 52):
"Let $Q$ be a separating $\Omega$-path in $(G, \Omega)$ with ends $a, b$. If $\mathcal{P}$ is
a crooked transaction in $(G, \Omega)$ with $Q \cap \bigcup \mathcal{P}$ null and with
$V(\mathcal{P}) \cap \Omega(a, b) \ne \emptyset$ then there is a cross $\mathcal{P}'
\subseteq \mathcal{P}$ with all four ends in $\Omega(a, b)$." -/
theorem theorem_5_1 {α : Type u} {β : Type v} (S : Society α β)
    {Q : Graph α β} {a b : α} {P_set : Set (Graph α β)}
    (hQ_ends : S.IsOmegaPathWithEnds Q a b)
    (hQ_sep : S.IsSeparatingOmegaPath Q)
    (hcrooked : S.IsCrookedTransaction P_set)
    (hdisj : Disjoint V(Q) V(S.transactionUnion P_set))
    (hne : (S.transactionEnds P_set ∩ S.Ω.interval a b).Nonempty) :
    ∃ P₁ ∈ P_set, ∃ P₂ ∈ P_set,
      S.OmegaPathsCross P₁ P₂ ∧
      pathEnds S.G P₁ ⊆ S.Ω.interval a b ∧
      pathEnds S.G P₂ ⊆ S.Ω.interval a b := by exact GraphMinor.GM09.Society.theorem_5_1_proof S hQ_ends hQ_sep hcrooked hdisj hne

end

section

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (5.2)** (pages 52–53):
"Let $(G, \Omega)$ have a crooked transaction with cardinality $p \ge 2$ and $p \ne 3$. Let
$\{Q_1, \dots, Q_{p+4}\}$ be a transaction in $(G, \Omega)$ such that for $1 \le i \le p+4$,
$Q_i$ is separating, and has no internal vertex in $\bar{\Omega}$, and has ends $a_i, b_i$,
where $(a_{p+4}, a_{p+3}, \dots, a_1, b_1, b_2, \dots, b_{p+4})$ is clockwise. Let $(G_1,
G_2)$ be a separation of $G$ with $V(G_1 \cap G_2) = V(Q_{p+4})$, $\Omega(a_{p+4}, b_{p+4})
\subseteq V(G_1)$ and $\Omega(b_{p+4}, a_{p+4}) \subseteq V(G_2)$. Then either* (i) *there
is a cross $\{P_1, P_2\}$ of $(G, \Omega)$ with $P_1 \cap G_2$ and $P_2 \cap G_2$ both null,
or* (ii) *there is a crooked transaction $\mathcal{P}$ in $(G, \Omega)$ with cardinality $p$
and with $\Omega(a_1, b_1) \cap V(\mathcal{P}) = \emptyset$." -/
theorem theorem_5_2 {α : Type u} {β : Type v} (S : Society α β)
    [Finite V(S.G)] [Finite E(S.G)] {p : ℕ} (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    (hex_cr : ∃ P₀ : Set (Graph α β), S.IsCrookedTransaction P₀ ∧ p ≤ P₀.ncard)
    {Q : Fin (p + 4) → Graph α β} {a b : Fin (p + 4) → α}
    (hinj_Q : Function.Injective Q)
    (htr_Q : S.IsTransaction (range Q))
    (hsep_Q : ∀ i : Fin (p + 4), S.IsSeparatingOmegaPath (Q i))
    (hno_int : ∀ i : Fin (p + 4), Disjoint (pathInternalVerts S.G (Q i)) S.Ω.bar)
    (hends_Q : ∀ i : Fin (p + 4), S.IsOmegaPathWithEnds (Q i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    {G₁ G₂ : Graph α β} (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q ⟨p + 3, by omega⟩))
    (hint_G₁ : S.Ω.interval (a ⟨p + 3, by omega⟩) (b ⟨p + 3, by omega⟩) ⊆ V(G₁))
    (_hint_G₂ : S.Ω.interval (b ⟨p + 3, by omega⟩) (a ⟨p + 3, by omega⟩) ⊆ V(G₂)) :
    (∃ P₁ P₂ : Graph α β, S.OmegaPathsCross P₁ P₂ ∧
      Disjoint V(P₁) V(G₂) ∧ Disjoint V(P₂) V(G₂)) ∨
    (∃ P_set : Set (Graph α β), S.IsCrookedTransaction P_set ∧ P_set.ncard = p ∧
      Disjoint (S.Ω.interval (a ⟨0, by omega⟩) (b ⟨0, by omega⟩)) (S.transactionEnds P_set)) := by exact GraphMinor.GM09.Society.theorem_5_2_proof S hp2 hp3 hex_cr hinj_Q htr_Q hsep_Q hno_int hends_Q hcw hsep_G hinter_G hint_G₁ _hint_G₂

end

section

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (5.3)** (page 53):
"Let $Q$ be an induced $\Omega$-path in $(K, \Omega)$ with ends $a, b$ such that $\Omega(a,
b) = \emptyset$ and $\bar{\Omega} - \{a, b\}$ catches $K \setminus V(Q)$, and no internal
vertex of $Q$ is in $\bar{\Omega}$. Let $r \in V(Q) - \{a, b\}$, and let $\Omega_1$ be the
cyclic permutation in $V(K)$ with $\bar{\Omega}_1 = \bar{\Omega} \cup \{r\}$ and $\Omega_1
\mid \bar{\Omega} = \Omega$, and with $(a, r, b)$ $\Omega_1$-clockwise. If $(K, \Omega_1)$
has a cross then $(K, \Omega)$ has a cross or tripod." -/
theorem theorem_5_3 {α : Type u} {β : Type v} (S : Society α β)
    [Finite V(S.G)] [Finite E(S.G)]
    {S₁ : Society α β} {Q : Graph α β} {a b r : α}
    (hG : S₁.G = S.G)
    (hQ : S.IsOmegaPathWithEnds Q a b)
    (hQ_ind : S.G.induce V(Q) = Q)
    (hab_empty : S.Ω.interval a b = ∅)
    (hcatch : Catches (S.Ω.bar \ {a, b}) (deleteVertices S.G V(Q)))
    (hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hr_Q : r ∈ V(Q) \ {a, b})
    (hbar₁ : S₁.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₁ : S₁.Ω.IsRestriction S.Ω.bar S.Ω)
    (hcw_arb : S₁.Ω.IsClockwise3 a r b)
    (hcross₁ : ∃ P₁ P₂ : Graph α β, S₁.IsCross P₁ P₂) :
    (∃ M₁ M₂ : Graph α β, S.IsCross M₁ M₂) ∨
      (∃ N₁ N₂ N₃ : Graph α β, S.IsTripod N₁ N₂ N₃) := by exact GraphMinor.GM09.Society.theorem_5_3_proof S hG hQ hQ_ind hab_empty hcatch hno_int hr_Q hbar₁ hrest₁ hcw_arb hcross₁

end

section

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (5.4)** (page 54):
"Let $(G, \Omega)$ be internally 4-connected. Let $Q$ be a separating $\Omega$-path with ends
$a, b$ and with no internal vertex in $\bar{\Omega}$, and let $(G_1, G_2)$ be a separation
of $G$ such that $V(G_1 \cap G_2) = V(Q)$, $\Omega(a, b) \subseteq V(G_1)$ and $\Omega(b, a)
\subseteq V(G_2)$. Let $G' = G \setminus V(G_2)$, let $\Omega' = \Omega \mid V(G')$, and let
$\Omega_1 = \Omega \mid V(G_1)$. If $(G', \Omega')$ has a tripod then $(G_1, \Omega_1)$ has
a cross." -/
theorem theorem_5_4 {α : Type u} {β : Type v} (S : Society α β)
    (hconn : S.IsInternallyKConnected 4)
    {Q G₁ G₂ : Graph α β} {a b : α}
    (hQ : S.IsOmegaPathWithEnds Q a b)
    (_hsep_Q : S.IsSeparatingOmegaPath Q)
    (_hno_int : Disjoint (pathInternalVerts S.G Q) S.Ω.bar)
    (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q))
    (hQ_G₁ : Q ≤ G₁)
    (_hint_G₁ : S.Ω.interval a b ⊆ V(G₁))
    (_hint_G₂ : S.Ω.interval b a ⊆ V(G₂))
    {S' S₁ : Society α β}
    (hG' : S'.G = deleteVertices S.G V(G₂))
    (hΩ' : S.Ω.IsRestriction V(deleteVertices S.G V(G₂)) S'.Ω)
    (hG₁ : S₁.G = G₁)
    (hΩ₁ : S.Ω.IsRestriction V(G₁) S₁.Ω)
    (htripod : ∃ P₁ P₂ P₃ : Graph α β, S'.IsTripod P₁ P₂ P₃) :
    ∃ M₁ M₂ : Graph α β, S₁.IsCross M₁ M₂ := by exact GraphMinor.GM09.Society.theorem_5_4_proof S hconn hQ _hsep_Q _hno_int hsep_G hinter_G hQ_G₁ _hint_G₁ _hint_G₂ hG' hΩ' hG₁ hΩ₁ htripod

end

section

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (5.5)** (pages 54–55):
"Let $(G, \Omega)$ be internally 4-connected and let $p \ge 2$ with $p \ne 3$. Let $\{Q_1,
\dots, Q_{p+5}\}$ be a transaction such that for $1 \le i \le p+5$, $Q_i$ is separating, has
no internal vertex in $\bar{\Omega}$, and has ends $a_i, b_i$, where $(a_{p+5}, a_{p+4},
\dots, a_1, b_1, b_2, \dots, b_{p+5})$ is clockwise. Let $\Omega(a_1, b_1) = \emptyset$, and
let $r \in V(Q_1) - \{a_1, b_1\}$. Let $(G_1, G_2)$ be a separation of $G$ with $V(G_1 \cap
G_2) = V(Q_{p+5})$, $\Omega(a_{p+5}, b_{p+5}) \subseteq V(G_1)$, and $\Omega(b_{p+5},
a_{p+5}) \subseteq V(G_2)$. Let $\Omega_0$ be the cyclic permutation with $\bar{\Omega}_0 =
\bar{\Omega} \cup \{r\}$ and $\Omega_0 \mid \bar{\Omega} = \Omega$, such that $(a_1, r,
b_1)$ is $\Omega_0$-clockwise. Suppose that $Q_1$ is induced, that $\bar{\Omega} - \{a_1,
b_1\}$ catches $G \setminus V(Q_1)$, that $(G, \Omega_0)$ has a crooked transaction of
cardinality $p$ and that $(G, \Omega)$ has no crooked transaction of cardinality $p$. Then
there is a non-separating $\Omega$-path $P$ of $(G, \Omega)$ with $P \subseteq G_1$." -/
theorem theorem_5_5 {α : Type u} {β : Type v} (S : Society α β)
    {S₀ : Society α β} {p : ℕ}
    (hconn : S.IsInternallyKConnected 4)
    (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    {Q : Fin (p + 5) → Graph α β} {a b : Fin (p + 5) → α} {r : α}
    (hinj_Q : Function.Injective Q)
    (htr_Q : S.IsTransaction (range Q))
    (hsep_Q : ∀ i : Fin (p + 5), S.IsSeparatingOmegaPath (Q i))
    (hno_int : ∀ i : Fin (p + 5), Disjoint (pathInternalVerts S.G (Q i)) S.Ω.bar)
    (hends_Q : ∀ i : Fin (p + 5), S.IsOmegaPathWithEnds (Q i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    (hab_empty : S.Ω.interval (a 0) (b 0) = ∅)
    (hr_Q0 : r ∈ V(Q 0) \ {a 0, b 0})
    {G₁ G₂ : Graph α β} (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q ⟨p + 4, by omega⟩))
    (hQm_G₁ : Q ⟨p + 4, by omega⟩ ≤ G₁)
    (hint_G₁ : S.Ω.interval (a ⟨p + 4, by omega⟩) (b ⟨p + 4, by omega⟩) ⊆ V(G₁))
    (hint_G₂ : S.Ω.interval (b ⟨p + 4, by omega⟩) (a ⟨p + 4, by omega⟩) ⊆ V(G₂))
    (hG₀ : S₀.G = S.G)
    (hbar₀ : S₀.Ω.bar = S.Ω.bar ∪ {r})
    (hrest₀ : S₀.Ω.IsRestriction S.Ω.bar S.Ω)
    (hcw_arb : S₀.Ω.IsClockwise3 (a 0) r (b 0))
    (hQ0_ind : S.G.induce V(Q 0) = Q 0)
    (hcatches : Catches (S.Ω.bar \ {a 0, b 0}) (deleteVertices S.G V(Q 0)))
    (hex_cr₀ : ∃ P₀ : Set (Graph α β), S₀.IsCrookedTransaction P₀ ∧ p ≤ P₀.ncard)
    (hno_cr : ∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ p) :
    (∃ P₁ P₂ : Graph α β, P₁ ≤ G₁ ∧ P₂ ≤ G₁ ∧ S.IsCross P₁ P₂) ∧
    (∃ P : Graph α β, S.IsNonSeparatingOmegaPath P ∧ P ≤ G₁) := by exact GraphMinor.GM09.Society.theorem_5_5_proof S hconn hp2 hp3 hinj_Q htr_Q hsep_Q hno_int hends_Q hcw hab_empty hr_Q0 hsep_G hinter_G hQm_G₁ hint_G₁ hint_G₂ hG₀ hbar₀ hrest₀ hcw_arb hQ0_ind hcatches hex_cr₀ hno_cr

end

/-! ## Section 6. THE MAIN THEOREM -/

section

open Set Function Graph GraphMinor
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (6.1)** (page 55):
"Let $p \ge 2$ be an integer with $p \ne 3$, and let $(G, \Omega)$ be a 3-connected,
internally 4-connected society, in which there is no crooked transaction of cardinality $p$.
Then the sophistication of $(G, \Omega)$ is at most $3p + 7$." -/
theorem theorem_6_1 {α : Type u} {β : Type v} {S : Society α β}
    {p : ℕ} (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    (hconn3 : S.IsKConnected 3)
    (hconn4 : S.IsInternallyKConnected 4)
    (hno_crooked : ∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ p) :
    S.HasSophisticationLE (3 * p + 7) ∧ S.sophistication ≤ 3 * p + 7 := by exact GraphMinor.GM09.Society.theorem_6_1_proof hp2 hp3 hconn3 hconn4 hno_crooked

end

/-! ## Section 7. SOME SPECIAL TRANSACTIONS -/

section

open Set Function Graph GraphMinor
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (7.1)** (page 59):
"Let $r \ge 2$, $s \ge 3$, $t \ge 4$ be integers. Let $\mathcal{P}$ be a crooked transaction
in $(G, \Omega)$ such that $|\mathcal{P}| \ge (r - 1)(2s + t - 7)$. Then there exists
$\mathcal{P}' \subseteq \mathcal{P}$ such that either* (i) *|\mathcal{P}'| = r and
\mathcal{P}' is a crosscap, or* (ii) *|\mathcal{P}'| = s and \mathcal{P}' is a leap, or*
(iii) *|\mathcal{P}'| = t and \mathcal{P}' is a doublecross." -/
theorem theorem_7_1 {α : Type u} {β : Type v} (S : Society α β)
    {P_set : Set (Graph α β)}
    {r s t : ℕ} (hr : 2 ≤ r) (hs : 3 ≤ s) (ht : 4 ≤ t)
    (hcrooked : S.IsCrookedTransaction P_set)
    (hcard : (r - 1) * (2 * s + t - 7) ≤ P_set.ncard) :
    ∃ P_set' ⊆ P_set,
      (P_set'.ncard = r ∧ S.IsCrosscapTransaction P_set') ∨
      (P_set'.ncard = s ∧ S.IsLeapTransaction P_set') ∨
      (P_set'.ncard = t ∧ S.IsDoublecrossTransaction P_set') := by exact GraphMinor.GM09.Society.theorem_7_1_proof S hr hs ht hcrooked hcard

end

/-! ## Section 8. Societies with No Large Transaction -/

section

open Set Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
open GraphMinor.GM09.Society

universe u v

/-- **Graph Minors IX, (8.1)** (page 60):
"Every society with no transaction of cardinality $>k$ has a linear decomposition of depth
$\le k$."

*Note on the hypothesis `hne : S.Ω.bar.Nonempty ∨ S.G = ⊥`:*
In a linear decomposition `({t₁, …, t_n}, (X_i : 1 ≤ i ≤ n))` of `(G, Ω)`, `{t₁, …, t_n} = Ω̄` and
`(i) ⋃ (X_i : 1 ≤ i ≤ n) = G`. When `Ω̄ = ∅`, we must have `n = 0`, so the union `(i)` is the null
graph `⊥`, which equals `G` if and only if `G = ⊥`. When `Ω̄ ≠ ∅`, `n = |Ω̄| ≥ 1` and the proof in
the paper constructs a linear decomposition `(X_i : 1 ≤ i ≤ n)` of depth `≤ k` for any society
`(G, Ω)` with no transaction of cardinality `> k`.

The boundary order is nonempty unless the graph is null. See the correction to (8.1) in
`corrections/GM09.md`. -/
theorem theorem_8_1 {α : Type u} {β : Type v}
    (S : Society α β) (hne : S.Ω.bar.Nonempty ∨ S.G = ⊥) (k : ℕ)
    (hno_trans : ∀ P_set : Set (Graph α β), S.IsTransaction P_set → P_set.ncard ≤ k) :
    S.HasLinearDecompositionOfDepthLE k := by exact GraphMinor.GM09.Society.theorem_8_1_proof S hne k hno_trans

end

/-! ## Section 9. Removing a Rural Neighborhood -/

section

open Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06

universe u v w

/-- **Graph Minors IX, (9.1)** (pages 62–63):
"If the composition of a society $(G, \Omega)$ with some rural neighborhood has a crooked
transaction of cardinality $\ge p$, then so does $(G, \Omega)$." -/
theorem theorem_9_1 {α : Type u} {β : Type v}
    {S S_comp : Society α β} {N : Neighborhood α β} {p : ℕ}
    (hcomp : S_comp.IsComposition S N) (hrural : N.IsRural)
    {P_set₀ : Set (Graph α β)}
    (hcrooked₀ : S_comp.IsCrookedTransaction P_set₀) (hcard₀ : p ≤ P_set₀.ncard) :
    ∃ P_set : Set (Graph α β), S.IsCrookedTransaction P_set ∧ p ≤ P_set.ncard := by exact GraphMinor.GM09.theorem_9_1_proof hcomp hrural hcrooked₀ hcard₀

end

/-! ## Section 10. Exploiting a Rural Neighborhood -/

section

open Set Graph GraphMinor GraphMinor.Surface
open PlanarNests (exists_first_hit_split not_isLink_self_of_mem_edges_of_isSimple)
open Topology Metric

universe u v

/-- **Graph Minors IX, (10.1)** (page 64):
"Let $(G, \Omega, \Omega_0)$ be a rural neighborhood and let $(\Sigma, \Gamma, \Delta, \Delta_0)$ be
a presentation with an $s$-nest. Let $X \subseteq \bar{\Omega}$ be weakly-linked, with $|X| = r$.
Then we may choose an $s$-nest $(C_1, \dots, C_s)$ and disjoint paths $P_1, \dots, P_r$ of $G$ each
with one end in $X$ and the other in $\bar{\Omega}_0$, such that for $1 \le i \le r$ and
$1 \le j \le s$, $P_i \cap C_j$ is a path." -/
theorem theorem_10_1 {α : Type u} {β : Type v}
    {N : Neighborhood α β} (P_pres : Presentation N) {s : ℕ}
    (h_nest : ∃ C₀ : Fin s → Graph α β, N.IsNest P_pres C₀)
    {X : Set α} (hX : N.IsWeaklyLinked X) :
    ∃ (C : Fin s → Graph α β) (P : Fin X.ncard → Graph α β),
      N.IsNest P_pres C ∧
      (∀ i, IsFromToPath N.G (P i) X N.Ω₀.bar) ∧
      Pairwise (fun i₁ i₂ => Disjoint V(P i₁) V(P i₂)) ∧
      ∀ (i : Fin X.ncard) (j : Fin s), IsGraphPath N.G (subgraphInter N.G (P i) (C j)) := by exact GraphMinor.GM09.theorem_10_1_proof P_pres h_nest hX

end

section

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

/-- **Graph Minors IX, (10.2)** (page 64), with the numbering of the circuits corrected as in the module docstring:
"Let $(G, \Omega, \Omega_0)$ be a rural neighborhood of breadth $\ge s$, and let $\{a_1, a_2,
\dots, a_s, b_1, b_2, \dots, b_s\} \subseteq \bar{\Omega}$ be weakly-linked, where $(a_s,
a_{s-1}, \dots, a_1, b_1, b_2, \dots, b_s)$ is clockwise. Then there is a transaction
$\{Q_1, \dots, Q_s\}$ in $(G, \Omega)$ such that $Q_i$ has ends $a_i, b_i$ and $Q_i$ meets
every path from $\Omega(a_i, b_i)$ to $\Omega(b_i, a_i) \cup \bar{\Omega}_0$ $(1 \le i \le
s)$."
That `Q_i` meets every such path we state with a separation with `V(G₁ ∩ G₂) = V(Q_i)`. -/
theorem theorem_10_2 {α : Type u} {β : Type v}
    {N : Neighborhood α β} (P_pres : Presentation N) {s : ℕ}
    (h_nest : ∃ C₀ : Fin s → Graph α β, N.IsNest P_pres C₀) {a b : Fin s → α}
    (hX : N.IsWeaklyLinked (range a ∪ range b))
    (hcw : N.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b)) :
    ∃ Q : Fin s → Graph α β, (∀ i, IsGraphPathWithEnds N.G (Q i) (a i) (b i)) ∧
      Pairwise (fun i j => Disjoint V(Q i) V(Q j)) ∧
      ∀ i, ∃ G₁ G₂ : Graph α β, IsGraphSeparation N.G G₁ G₂ ∧ V(G₁) ∩ V(G₂) = V(Q i) ∧
        Q i ≤ G₁ ∧ N.Ω.interval (a i) (b i) ⊆ V(G₁) ∧ N.Ω.interval (b i) (a i) ⊆ V(G₂) ∧
        N.Ω₀.bar ⊆ V(G₂) := by exact GraphMinor.GM09.theorem_10_2_proof P_pres h_nest hX hcw

end

section

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

/-- **Graph Minors IX, (10.3)** (page 64):
"Let $p \ge 2$ with $p \ne 3$. Let $(G, \Omega, \Omega_0)$ be a rural neighborhood of breadth
$\ge p + 4$, and let $X \subseteq \bar{\Omega}$ be weakly-linked, with $|X| \ge 2p + 8$."

The paper gives no reason that the extended paths still cross. The proof checks that extending the
paths preserves the cyclic order of their ends. -/
theorem theorem_10_3 {α : Type u} {β : Type v}
    {S_comp S₀ : Society α β} {N : Neighborhood α β} {p : ℕ} {X : Set α}
    (hp2 : 2 ≤ p) (hp3 : p ≠ 3) (hrural : N.IsRural) (hbreadth : N.HasBreadthGe (p + 4))
    (hX : N.IsWeaklyLinked X) (hcard : 2 * p + 8 ≤ X.ncard) (hcomp : S_comp.IsComposition S₀ N)
    {P₀ : Set (Graph α β)} (hP₀ : S_comp.IsCrookedTransaction P₀) (hp : p ≤ P₀.ncard) :
    ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ p ≤ P'.ncard ∧
      S_comp.transactionEnds P' ⊆ X := by exact GraphMinor.GM09.theorem_10_3_proof hp2 hp3 hrural hbreadth hX hcard hcomp hP₀ hp

end

section

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

/-- **Graph Minors IX, (10.4)** (page 65):
"Let $p \ge 2$ with $p \ne 3$. Let $(G, \Omega, \Omega_0)$ be a rural neighborhood of breadth
$\ge p + 5$, and let $X \subseteq \bar{\Omega}$ be linked with $|X| \ge 2p + 8$." -/
theorem theorem_10_4 {α : Type u} {β : Type v}
    {S_comp S₀ : Society α β} {N : Neighborhood α β} {p : ℕ} {X : Set α}
    (hp2 : 2 ≤ p) (hp3 : p ≠ 3) (hbreadth : N.HasBreadthGe (p + 5))
    (hX : N.IsLinked X) (hcard : 2 * p + 8 ≤ X.ncard) (hcomp : S_comp.IsComposition S₀ N)
    {P₀ : Set (Graph α β)} (hP₀ : S_comp.IsCrookedTransaction P₀) (hp : p ≤ P₀.ncard) :
    ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ p ≤ P'.ncard ∧
      S_comp.transactionEnds P' ⊆ X ∧
      ∀ P ∈ P', Disjoint (pathInternalVerts S_comp.G P) S_comp.Ω.bar := by exact GraphMinor.GM09.theorem_10_4_proof hp2 hp3 hbreadth hX hcard hcomp hP₀ hp

end

section

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06

universe u v w

/-- **Graph Minors IX, (10.5)** (page 66):
"Let $p \ge 0$ and let $(G, \Omega, \Omega_0)$ be a rural neighborhood of breadth
$\ge \frac{1}{2} p + 1$. Let $X \subseteq \bar{\Omega}$ be linked, with $|X| \ge p$. Let
$(G \cup G_0, \Omega)$ be the composition of some society $(G_0, \Omega_0)$ with $(G, \Omega, \Omega_0)$,
and let $Y \subseteq V(G_0)$. Then either there are $p$ mutually disjoint paths of $G \cup G_0$ from
$X$ to $Y$, each with only its initial vertex in $\bar{\Omega}$, or there exists
$W \subseteq V(G \cup G_0)$ with $|W| < p$ and $W \cap \bar{\Omega} = \emptyset$ such that every path of
$G \cup G_0$ from $\bar{\Omega}$ to $Y$ has a vertex in $W$." -/
theorem theorem_10_5 {α : Type u} {β : Type v}
    {S_comp S₀ : Society α β} {N : Neighborhood α β}
    {p : ℕ} {X Y : Set α}
    (_hrural : N.IsRural) (hbreadth : N.HasBreadthGe ((p + 1) / 2 + 1))
    (hX : N.IsLinked X) (hpX : p ≤ X.ncard)
    (hcomp : S_comp.IsComposition S₀ N) (hY : Y ⊆ V(S₀.G)) :
    (∃ P : Fin p → Graph α β,
      (∀ i, ∃ x ∈ X, ∃ y ∈ Y, IsFromToPathWithEnds S_comp.G (P i) S_comp.Ω.bar Y x y) ∧
      Pairwise (fun i j => Disjoint V(P i) V(P j))) ∨
    (∃ W ⊆ V(S_comp.G), W.ncard < p ∧ Disjoint W S_comp.Ω.bar ∧
      ∀ P : Graph α β, IsFromToPath S_comp.G P S_comp.Ω.bar Y → (V(P) ∩ W).Nonempty) := by exact GraphMinor.GM09.theorem_10_5_proof _hrural hbreadth hX hpX hcomp hY

end

/-! ## Section 11. Coping with Connectivity Failure -/

section

open Set Topology Graph GraphMinor.Surface GraphMinor.GM06

universe u v w

/-- **Graph Minors IX, (11.1)** (page 67):
"If $L, L'$ are distinct lawns then every element of $L \cap L'$ is the image under $\Gamma$
of a common end of the two corresponding prominences." -/
theorem theorem_11_1 {α : Type u} {β : Type v}
    {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres)
    {P P' : Graph α β} {L L' : Set EuclideanPlane}
    (hL : IsProminenceWithDisc P_pres P L)
    (hL' : IsProminenceWithDisc P_pres P' L')
    (hne : L ≠ L') {x : EuclideanPlane} (hx : x ∈ L ∩ L') :
    ∃ v ∈ pathEnds N.G P ∩ pathEnds N.G P', x ∈ graphDrawingVertexSet P_pres.Γ v := by exact GraphMinor.GM09.theorem_11_1_proof hreg hL hL' hne hx

end

section

open Set Topology Graph GraphMinor.Surface GraphMinor.GM06

universe u v w

/-- **Graph Minors IX, (11.2)** (pages 67–68):
"If $e$ is an external edge of $G$ with both ends drawn in the wall, then its ends are both
middle vertices of prominences." -/
theorem theorem_11_2 {α : Type u} {β : Type v}
    {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) (hsimple : IsSimpleGraph N.G)
    {e : β} {u v : α} (he : IsExternalEdge P_pres e) (hl : N.G.IsLink e u v)
    (hu_wall : graphDrawingVertexSet P_pres.Γ u ⊆ wall P_pres)
    (hv_wall : graphDrawingVertexSet P_pres.Γ v ⊆ wall P_pres) :
    (∃ P₁ : Graph α β, IsProminence P_pres P₁ ∧ u ∈ pathInternalVerts N.G P₁) ∧
      (∃ P₂ : Graph α β, IsProminence P_pres P₂ ∧ v ∈ pathInternalVerts N.G P₂) := by exact GraphMinor.GM09.theorem_11_2_proof hreg hsimple he hl hu_wall hv_wall

end

section

open Set Topology Graph GraphMinor.Surface GraphMinor.GM06

universe u v w

/-- **Graph Minors IX, (11.3)** (page 68):
"No triangle in $G$ has an internal edge and an external edge." -/
theorem theorem_11_3 {α : Type u} {β : Type v}
    {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) (hsimple : IsSimpleGraph N.G)
    {T : Graph α β} (hT : IsTriangle N.G T)
    {e₂ e₃ : β} (he₂T : e₂ ∈ E(T)) (he₃T : e₃ ∈ E(T))
    (he₂ : IsInternalEdge P_pres e₂) (he₃ : IsExternalEdge P_pres e₃) : False := by exact GraphMinor.GM09.theorem_11_3_proof hreg hsimple hT he₂T he₃T he₂ he₃

end

section

open Set Topology Graph GraphMinor.Surface GraphMinor.GM06

universe u v w

/-- **Graph Minors IX, (11.4)** (pages 68–69):
"If $(G_0 \cup G^*, \Omega^*)$ is the composition of a park $(G^*, \Omega^*, \Omega_0)$ with
a society $(G_0, \Omega_0)$, and $(G_0, \Omega_0)$ has no transaction of cardinality $> p$,
then $(G_0 \cup G^*, \Omega^*)$ has no transaction of cardinality $> p + 2$." -/
theorem theorem_11_4 {α : Type u} {β : Type v}
    {S S₀ : Society α β} {N_star : Neighborhood α β} {p : ℕ}
    (hpark : N_star.IsRegularPark)
    (hcomp : S.IsComposition S₀ N_star)
    (hno : ∀ Q_set : Set (Graph α β), S₀.IsTransaction Q_set → Q_set.ncard ≤ p)
    {P_set : Set (Graph α β)} (hP_set : S.IsTransaction P_set) :
    P_set.ncard ≤ p + 2 := by exact GraphMinor.GM09.theorem_11_4_proof hpark hcomp hno hP_set

end

section

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

/-- **Graph Minors IX, (11.5)** (pages 69–70):
"Let $G$ be simple, and let $(G, \Omega)$ have sophistication $\le p$. Then there is a
society $(G_1, \Omega_1)$ and a rural neighborhood $(G_2, \Omega, \Omega_1)$ such that* (i)
$G_1, G_2 \subseteq G$, $G_1 \cup G_2 = G$ *and* $V(G_1 \cap G_2) = \bar{\Omega}_1$, (ii)
$(G_1, \Omega_1)$ *has no transaction of cardinality* $> p + 2$ (iii) *for every triangle
$T$ of $G$, either $T \subseteq G_1$ or $T \subseteq G_2$." -/
theorem theorem_11_5 {α : Type u} {β : Type v}
    (S : Society α β) (hsimple : IsSimpleGraph S.G) {p : ℕ}
    (hsoph : S.HasSophisticationLE p) :
    ∃ (S₁ : Society α β) (N₂ : Neighborhood α β),
      N₂.IsRural ∧
      N₂.Ω = S.Ω ∧
      N₂.Ω₀ = S₁.Ω ∧
      S₁.G ≤ S.G ∧
      N₂.G ≤ S.G ∧
      subgraphUnion S.G S₁.G N₂.G = S.G ∧
      V(subgraphInter S.G S₁.G N₂.G) = S₁.Ω.bar ∧
      (∀ Q_set : Set (Graph α β), S₁.IsTransaction Q_set → Q_set.ncard ≤ p + 2) ∧
      (∀ T : Graph α β, IsTriangle S.G T → T ≤ S₁.G ∨ T ≤ N₂.G) := by exact GraphMinor.GM09.theorem_11_5_proof S hsimple hsoph

end

section

open Set Graph GraphMinor.Surface GraphMinor.GM06

universe u v w

/-- **Graph Minors IX, (11.6)** (page 70):
"Every society has a consolidation." -/
theorem theorem_11_6 {α : Type u} {β : Type v}
    (S : Society α β) : ∃ D_set : Set (Graph α β × Graph α β), IsConsolidation S D_set := by exact GraphMinor.GM09.theorem_11_6_proof S

end

section

open Set Graph GraphMinor.Surface GraphMinor.GM06

universe u v w

/-- **Graph Minors IX, (11.7)** (page 70):
"If $\mathcal{D}$ is a consolidation of $(G, \Omega)$ and $C = \bigcap (B: (A, B) \in
\mathcal{D})$ then $E(C) = \emptyset$, $\bar{\Omega} \subseteq V(C)$, $A \cap B \subseteq C$
for every $(A, B) \in \mathcal{D}$ and $A_1 \cap A_2 \subseteq C$ for every two distinct
separations $(A_1, B_1), (A_2, B_2) \in \mathcal{D}$." -/
theorem theorem_11_7 {α : Type u} {β : Type v}
    {S : Society α β} {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set) :
    let C := consolidationBInter S D_set
    E(C) = ∅ ∧ S.Ω.bar ⊆ V(C) ∧ (∀ ⦃A B : Graph α β⦄, (A, B) ∈ D_set → subgraphInter S.G A B ≤ C) ∧
    (∀ ⦃A₁ B₁ A₂ B₂ : Graph α β⦄,
      (A₁, B₁) ∈ D_set → (A₂, B₂) ∈ D_set → (A₁, B₁) ≠ (A₂, B₂) → subgraphInter S.G A₁ A₂ ≤ C) := by exact GraphMinor.GM09.theorem_11_7_proof hD

end

section

open Set Graph GraphMinor.Surface GraphMinor.GM06

universe u v w

/-- **Graph Minors IX, (11.8)** (page 70):
"Let $\mathcal{D}$ be a consolidation of $(G, \Omega)$ with core $C$. Let $C_1, C_2 \subseteq C$ with $C_1 \cup C_2 = C$ and $\bar{\Omega} \subseteq V(C_2)$. Let $\mathcal{D} = \mathcal{D}_1 \cup \mathcal{D}_2$, where $\mathcal{D}_1 \cap \mathcal{D}_2 = \emptyset$ and $V(A \cap B) \subseteq V(C_i)$ for $i = 1, 2$ and all $(A, B) \in \mathcal{D}_i$. Let $C^$ be the graph with $V(C^) = V(C_1 \cap C_2)$ and $E(C^) = \emptyset$. Let"

**Graph Minors IX, (11.8)** (pages 70–71): -/
theorem theorem_11_8 {α : Type u} {β : Type v}
    {S : Society α β} {D_set D₁ D₂ : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set) {C₁ C₂ : Graph α (Sym2 α)}
    (hC₁ : C₁ ≤ consolidationCore S D_set) (hC₂ : C₂ ≤ consolidationCore S D_set)
    (_hC_union : subgraphUnion (consolidationCore S D_set) C₁ C₂ = consolidationCore S D_set)
    (hΩ : S.Ω.bar ⊆ V(C₂)) (hD_union : D₁ ∪ D₂ = D_set) (hD_disj : Disjoint D₁ D₂)
    (hD₁ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → V(A) ∩ V(B) ⊆ V(C₁))
    (hD₂ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₂ → V(A) ∩ V(B) ⊆ V(C₂)) :
    let C := consolidationCore S D_set
    let C_star : Graph α β := (S.G.induce (V(C₁) ∩ V(C₂))).restrict ∅
    let G₁ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₁))
    let G₂ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₂))
    S.IsSocietySeparation G₁ G₂ ∧ subgraphInter S.G G₁ G₂ = C_star ∧
    V(G₁) ∩ V(C) = V(C₁) ∧ V(G₂) ∩ V(C) = V(C₂) := by exact GraphMinor.GM09.theorem_11_8_proof hD hC₁ hC₂ _hC_union hΩ hD_union hD_disj hD₁ hD₂

end

section

open Set Graph GraphMinor.Surface GraphMinor.GM06

universe u v w

/-- **Graph Minors IX, (11.9)** (page 71):
"Let $\mathcal{D}$ be a consolidation of $(G, \Omega)$ chosen so that its core $C$ has as few
vertices as possible. Then $(C, \Omega)$ is 4-connected." -/
theorem theorem_11_9 {α : Type u} {β : Type v}
    (S : Society α β) (D_set : Set (Graph α β × Graph α β)) (hD : IsConsolidation S D_set)
    (hmin : ∀ D' : Set (Graph α β × Graph α β), IsConsolidation S D' →
      V(consolidationCore S D_set).ncard ≤ V(consolidationCore S D').ncard) :
    (consolidationCoreSociety S D_set hD).IsKConnected 4 := by exact GraphMinor.GM09.theorem_11_9_proof S D_set hD hmin

end

section

open Set Graph GraphMinor.Surface GraphMinor.GM06

universe u v w

/-- **Graph Minors IX, (11.10)** (page 73):
"Let $C$ be the core of a consolidation $\mathcal{D}$ of $(G, \Omega)$. For any $\Pi$, there
is a transaction in $(G, \Omega)$ with pattern $\Pi$ if and only if there is such a
transaction in $(C, \Omega)$." -/
theorem theorem_11_10 {α : Type u} {β : Type v}
    (S : Society α β) (D_set : Set (Graph α β × Graph α β)) (hD : IsConsolidation S D_set)
    (P_pat : Set (Set α)) :
    (∃ P_set : Set (Graph α β), S.IsTransaction P_set ∧ S.transactionPattern P_set = P_pat) ↔
      (∃ Q_set : Set (Graph α (Sym2 α)), (consolidationCoreSociety S D_set hD).IsTransaction Q_set ∧
        (consolidationCoreSociety S D_set hD).transactionPattern Q_set = P_pat) := by exact GraphMinor.GM09.theorem_11_10_proof S D_set hD P_pat

end

section

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

/-- **Graph Minors IX, (11.11)** (pages 74–77):
"Let $p \ge 2$, with $p \neq 3$. Let $(G, \Omega)$ be a society with no crooked transaction
of cardinality $p$. Then there is a feasible segregation $\{(A_0, \Omega_0), \dots, (A_k,
\Omega_k)\}$ of $(G, \Omega)$ such that $|\bar{\Omega}_1|, \dots, |\bar{\Omega}_k| \le 3$
and $(A_0, \Omega_0)$ has no transaction of cardinality $> 3p + 9$." -/
theorem theorem_11_11 {α : Type u} {β : Type v}
    (S : Society α β) (p : ℕ) (hp2 : 2 ≤ p) (hp3 : p ≠ 3)
    (hno_crooked : ∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ p) :
    ∃ (k : ℕ) (S₀ : Society α β) (S_fam : Fin k → Society α β),
      IsFeasibleSegregation S S₀ S_fam ∧
      (∀ i : Fin k, (S_fam i).Ω.bar.ncard ≤ 3) ∧
      (∀ P_set : Set (Graph α β), S₀.IsTransaction P_set → P_set.ncard ≤ 3 * p + 9) := by exact GraphMinor.GM09.theorem_11_11_proof S p hp2 hp3 hno_crooked

end

end GraphMinor.GM09
