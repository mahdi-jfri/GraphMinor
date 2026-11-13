module

public import GraphMinor.GM22.GM21Proved
public import GraphMinor.GM22.Section2
public import GraphMinor.GM22.Section2Basic
public import GraphMinor.GM22.Section2Forest
public import GraphMinor.GM22.Section3
public import GraphMinor.GM22.Section3Haven
public import GraphMinor.GM22.Section3Lemma33
public import GraphMinor.GM22.Section4
public import GraphMinor.GM22.Section4Sleeve
public import GraphMinor.GM22.Section5
public import GraphMinor.GM22.Section6
public import GraphMinor.GM22.Section7
public import GraphMinor.GM22.Section7b
public import GraphMinor.GM22.Section7c5
public import GraphMinor.GM22.Section7d5
public import GraphMinor.GM22.Section8a
public import GraphMinor.GM22.Section8c

/-!
# Graph Minors XXII: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*, J.
Combin. Theory Ser. B **102** (2012), 530–563.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. The docstrings say where the Lean differs from the print, and
`corrections/GM22.md` lists the corrections to the paper.
-/

public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph Hypergraph

universe u v w u' v' uH vH u₁ v₁

/-! ## Section 1. Introduction -/

/-- **Graph Minors XXII, 1.1** (Section 1, page 531):
"**1.1.** *For every integer $p \ge 0$ there exists $w \ge 0$ such that every graph with a vital
$p$-linkage has tree-width $\le w$.*"

The paper quotes this as Theorem 1.1 of Graph Minors XXI, and the proof is the proof of XXI (1.1)
(`GM21.theorem_1_1_proof`), read in the definitions of this paper, which agree with those of XXI. -/
theorem theorem_1_1 (p : ℕ) :
    ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G L : Graph α β), V(G).Finite → E(G).Finite →
    IsVitalPLinkage G L p → TreeWidthLE G w :=
  gm21Theorem11Statement_iff_gm21.mpr GM21.theorem_1_1_proof p

/-! ## Section 2. Vital subgraphs -/

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XXII, 2.1** (Section 2, page 531, proved on page 532):
"For every integer $p \ge 0$, there exists $w \ge 0$ such that, if a graph $G$ has a subgraph which
is vital for some $Z \subseteq V(G)$ with $|Z| \le p$, then $G$ has tree-width $\le w$." -/
theorem theorem_2_1 (p : ℕ) :
    ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G L : Graph α β) (Z : Set α),
    V(G).Finite → E(G).Finite → Z ⊆ V(G) → Z.ncard ≤ p →
    IsVitalFor G L Z → TreeWidthLE G w :=
  GM22.theorem_2_1_proof p

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XXII, 2.2** (Section 2, page 531):
"If $L$ is a subgraph of $G$, and $L$ is vital for $Z \subseteq V(G)$, then $L$ is a forest,
$V(L) = V(G)$, and every vertex of $L$ not in $Z$ has degree at least 2 in $L$." -/
theorem theorem_2_2 {α : Type u} {β : Type v} {G L : Graph α β} {Z : Set α} (hE : E(G).Finite)
    (_hZ : Z ⊆ V(G)) (hvit : IsVitalFor G L Z) :
    IsGraphForest L ∧ V(L) = V(G) ∧ ∀ v ∈ V(L) \ Z, 2 ≤ vertexValency L v :=
  GM22.theorem_2_2_proof hE _hZ hvit

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XXII, 2.3** (Section 2, page 531):
"Let $L$ be a forest, and for each $v \in V(L)$ let $d(v)$ be the degree of $v$ in $L$.
Suppose that there are at most $p$ vertices of $L$ with $d(v) \le 1$. Then for all
$Y \subseteq V(L)$, $\sum_{y \in Y} d(y) \le 2|Y| + p$." -/
theorem theorem_2_3 {α : Type u} {β : Type v} {L : Graph α β} (hV : V(L).Finite) (hE : E(L).Finite)
    (hF : IsGraphForest L) {p : ℕ} (hp : {v ∈ V(L) | vertexValency L v ≤ 1}.ncard ≤ p) {Y : Set α}
    (hY : Y ⊆ V(L)) :
    (∑ᶠ y ∈ Y, vertexValency L y) ≤ 2 * Y.ncard + p :=
  GM22.theorem_2_3_proof hV hE hF hp hY

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XXII, 2.4** (Section 2, page 532):
"Let $L$ be a subgraph of $G$, vital for $Z \subseteq V(G)$, and let $e \in E(L)$ with both ends
in $Z$. Then $L \setminus \{e\}$ is vital for $Z$ in $G$." -/
theorem theorem_2_4 {α : Type u} {β : Type v} {G L : Graph α β} {Z : Set α} {e : β} {u₀ v₀ : α}
    (hZ : Z ⊆ V(G)) (hvit : IsVitalFor G L Z) (hlink : L.IsLink e u₀ v₀) (hu₀ : u₀ ∈ Z)
    (hv₀ : v₀ ∈ Z) :
    IsVitalFor G (L.deleteEdges {e}) Z :=
  GM22.theorem_2_4_proof hZ hvit hlink hu₀ hv₀

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XXII, 2.5** (Section 2, pages 532–533):
"Let $L$ be a subgraph of a graph $G$, let $Z \subseteq V(G)$, and let $\{A_1, \ldots, A_k\}$ be a
$Z$-division of $G$. Let $G'$ be a graph, let $Z' \subseteq V(G')$, and let $\{A'_1, \ldots, A'_k\}$
be a $Z'$-division of $G'$. Let $\alpha : Z' \to Z$ be a function, and for $1 \le i \le k$ let
$L'_i \subseteq A'_i$, such that
(a) for $1 \le i \le k$, $\alpha$ maps $Z' \cap V(A'_i)$ onto $Z \cap V(A_i)$, and"
"(b) if $u, v \in Z'$ are distinct and $\alpha(u) = \alpha(v)$ then $u, v \in V(A'_i)$ for some $i$
($1 \le i \le k$),
(c) for $1 \le i \le k$, $u, v \in Z' \cap V(A'_i)$ are $L'_i$-connected if and only if
$\alpha(u), \alpha(v)$ are $L \cap A_i$-connected.
Let $L' = L'_1 \cup \cdots \cup L'_k$. Then $L'_i = L' \cap A'_i$ for $1 \le i \le k$, and
$u, v \in Z'$ are $L'$-connected if and only if $\alpha(u), \alpha(v)$ are $L$-connected." -/
theorem theorem_2_5 {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'} {ι : Type w} [Fintype ι]
    {G L : Graph α β} {Z : Set α} {A : ι → Graph α β} {G' : Graph α' β'} {Z' : Set α'}
    {A' : ι → Graph α' β'} {α_map : α' → α} {L' : ι → Graph α' β'} (hLG : L ≤ G) (_hZ : Z ⊆ V(G))
    (hdiv : IsIndexedZDivision G Z A) (hZ' : Z' ⊆ V(G')) (hdiv' : IsIndexedZDivision G' Z' A')
    (hL'_le : ∀ i : ι, L' i ≤ A' i) (h_a : ∀ i : ι, α_map '' (Z' ∩ V(A' i)) = Z ∩ V(A i))
    (h_b : ∀ u ∈ Z', ∀ v ∈ Z', u ≠ v → α_map u = α_map v → ∃ i : ι, u ∈ V(A' i) ∧ v ∈ V(A' i))
    (h_c : ∀ i : ι, ∀ u ∈ Z' ∩ V(A' i), ∀ v ∈ Z' ∩ V(A' i), AreConnectedIn (L' i) u v ↔
      AreConnectedIn (subgraphInter G L (A i)) (α_map u) (α_map v)) :
    (∀ i : ι, L' i = subgraphInter G' (subgraphSUnion G' (range L')) (A' i)) ∧
    (∀ u ∈ Z', ∀ v ∈ Z',
      AreConnectedIn (subgraphSUnion G' (range L')) u v ↔
        AreConnectedIn L (α_map u) (α_map v)) :=
  GM22.theorem_2_5_proof hLG _hZ hdiv hZ' hdiv' hL'_le h_a h_b h_c

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XXII, 2.6** (Section 2, page 534):
"Let $(A, B)$ be a separation of a graph $G$, let $Z \subseteq V(G)$ with $V(A \cap B) \subseteq Z$,
and let $L' \subseteq A$ with the same effect on $Z \cap V(A)$ as $L \cap A$. Then
$L' \cup (L \cap B) \subseteq G$ has the same effect on $Z$ as $L$." -/
theorem theorem_2_6 {α : Type u} {β : Type v} {G L A B L' : Graph α β} {Z : Set α} (hLG : L ≤ G)
    (hsep : IsGraphSeparation G A B) (hZ : Z ⊆ V(G)) (hAB_Z : V(A) ∩ V(B) ⊆ Z) (hL'A : L' ≤ A)
    (heff : effectOn L' (Z ∩ V(A)) = effectOn (subgraphInter G L A) (Z ∩ V(A))) :
    effectOn (subgraphUnion G L' (subgraphInter G L B)) Z = effectOn L Z :=
  GM22.theorem_2_6_proof hLG hsep hZ hAB_Z hL'A heff

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XXII, 2.7** (Section 2, page 534):
"Let $L$ be a subgraph of $G$, vital for $Z \subseteq V(G)$, and let $(A, B)$ be a separation of
$G$.
Then $L \cap A$ is vital for $(Z \cap V(A)) \cup V(A \cap B)$ in $A$." -/
theorem theorem_2_7 {α : Type u} {β : Type v} {G L A B : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G))
    (hvit : IsVitalFor G L Z) (hsep : IsGraphSeparation G A B) :
    IsVitalFor A (subgraphInter G L A) ((Z ∩ V(A)) ∪ (V(A) ∩ V(B))) :=
  GM22.theorem_2_7_proof hZ hvit hsep

/-! ## Section 3. Drawings in a disc -/

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **3.1** (Graph Minors XXII, page 534):
"For every integer $p \ge 0$ there exists $h \ge 1$ with the following property. Let $\Gamma, K$
be subgraphs of a graph $G$ with $G = \Gamma \cup K$, and let $\Gamma$ be a drawing in a surface
$\Sigma$. Let $v \in V(\Gamma)$ be $h$-insulated from $V(\Gamma \cap K)$ by $\Gamma$, let
$Z \subseteq V(K)$ with $|Z| \le p$, and let $L \subseteq G$. Then there is a subgraph $L'$ of
$G \setminus \{v\}$ with the same effect on $Z$ as $L$ and with $L' \cap K \subseteq L$."

The haven of large order comes from Graph Minors X, (5.2), not from Seymour and Thomas: a bramble of
large order gives a haven of the same order. The proof of Claim (7) prints $2t \le \omega + 1$ for
$2t \le w + 1$ (see the correction to the proof of (3.1) in `corrections/GM22.md`). -/
theorem theorem_3_1 (p : ℕ) :
    ∃ h ≥ 1, ∀ {S : Type w} [TopologicalSpace S] [T2Space S], IsSurface S →
    ∀ {α : Type u} {β : Type v} (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D.V, IsInsulated D (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L :=
  GM22.theorem_3_1_proof p

open SimpleGraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 in
/-- **Graph Minors XXII, 3.2** (page 534):
"Let $C_1, \ldots, C_h$ be mutually vertex-disjoint connected subgraphs of a graph $G$, and also
let $D_1, \ldots, D_h$ be mutually vertex-disjoint connected subgraphs of $G$. Suppose that
$C_i \cap D_j$ is non-null for $1 \le i, j \le h$. Then $G$ has tree-width at least $h - 1$." -/
theorem theorem_3_2 {α : Type u} {β : Type v} {G : Graph α β} (hVG : V(G).Finite) {h : ℕ}
    (C D : Fin h → Graph α β) (hC_le : ∀ i : Fin h, C i ≤ G)
    (hC_conn : ∀ i : Fin h, IsGraphConnected (C i))
    (hC_disj : Pairwise fun i j : Fin h => Disjoint V(C i) V(C j)) (hD_le : ∀ j : Fin h, D j ≤ G)
    (hD_conn : ∀ j : Fin h, IsGraphConnected (D j))
    (hD_disj : Pairwise fun i j : Fin h => Disjoint V(D i) V(D j))
    (hCD_inter : ∀ i j : Fin h, (V(C i) ∩ V(D j)).Nonempty) :
    (∀ w : ℕ, TreeWidthLE G w → h ≤ w + 1) ∧ (h : ℤ) - 1 ≤ graphTreeWidth G :=
  GM22.theorem_3_2_proof hVG C D hC_le hC_conn hC_disj hD_le hD_conn hD_disj hCD_inter

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 GraphMinor.GM12 in
/-- **Graph Minors XXII, (3.3)** (page 535):
"Let $\Gamma$ be a drawing in a closed disc $\Delta$, and let $L \subseteq \Gamma$ with
$V(\Gamma) \cap bd(\Delta) \subseteq V(L)$. Let $v \in V(\Gamma) \setminus bd(\Delta)$, and suppose
that there is no subgraph of $\Gamma \setminus \{v\}$ with the same effect on
$V(\Gamma) \cap bd(\Delta)$ as $L$. Then there is a $\Gamma$-normal proper line $F \subseteq \Delta$
with $v \in F \cap V(\Gamma)$, such that there are $F \cap V(\Gamma)$ components of $L$ with a
vertex in $F \cap V(\Gamma)$."

The Lean conclusion also records the ends $x, y \in \operatorname{bd}(\Delta)$ of $F$ and the fact
from the proof of 3.3 that for any decomposition $\operatorname{bd}(\Delta) = F_1 \cup F_2$ into two
lines with ends $x, y$, each of the $|F \cap V(\Gamma)|$ components of $L$ also meets $F_1$ and
$F_2$. -/
theorem theorem_3_3 {S : Type u} [TopologicalSpace S] (hDisc : IsClosedDiscSpace S) {Γ : Drawing S}
    (hProper : Γ.IsProper) {L : Graph S (Set S)} (hL : L ≤ Γ.toGraph) (hbd : Γ.V ∩ bd S ⊆ V(L))
    {v : S} (hv : v ∈ Γ.V \ bd S)
    (hno : ¬ ∃ L' ≤ Γ.toGraph.deleteVerts {v}, HasSameEffectOn L' L (Γ.V ∩ bd S)) :
    ∃ x ∈ bd S, ∃ y ∈ bd S, x ≠ y ∧
    ∃ F : Set S, Γ.IsNormal F ∧ IsProperLine F ∧ IsLineWithEnds F x y ∧
      F ∩ bd S = {x, y} ∧ v ∈ F ∧
      ∀ F₁ F₂ : Set S,
        IsLineWithEnds F₁ x y → IsLineWithEnds F₂ x y →
        F₁ ∩ F₂ = {x, y} → bd S = F₁ ∪ F₂ →
        ∃ C_set ⊆ graphComponents L,
          C_set.ncard = (F ∩ Γ.V).ncard ∧
          ∀ C ∈ C_set, (V(C) ∩ F₁).Nonempty ∧ (V(C) ∩ F₂).Nonempty ∧
            (V(C) ∩ (F ∩ Γ.V)).Nonempty :=
  GM22.theorem_3_3_proof hDisc hProper hL hbd hv hno

/-! ## Section 4. Changing the drawing -/

open unitInterval GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM16 in
/-- **4.1** (Graph Minors XXII, page 537):
"For every integer $p \ge 0$ there exists $h \ge 1$ with the following property. Let $\Gamma, K$ be
subgraphs of a graph $\Gamma \cup K$, let $\Gamma$ be a drawing in a surface $\Sigma$ and let $T$ be
the set of all points of $\Sigma$ that are $h$-insulated from $V(\Gamma \cap K)$ by $\Gamma$. Let
$\Gamma'$ be a $T$-variant of $\Gamma$ in $\Sigma$ with $\Gamma' \cap K = \Gamma \cap K$, let
$L' \subseteq \Gamma' \cup K$, and let $Z \subseteq V(K)$ with $|Z| \le p$. Then there exists a
subgraph $L$ of $\Gamma \cup K$ with the same effect on $Z$ as $L'$, with $L \cap K \subseteq L'$."
-/
theorem theorem_4_1 (p : ℕ) :
    ∃ h ≥ 1, ∀ (S : Type w) [TopologicalSpace S] [T2Space S], IsSurface S →
    ∀ {α : Type u} {β : Type v} (G Γ K G' Γ' L' : Graph α β),
    V(G).Finite → E(G).Finite → V(G').Finite → E(G').Finite →
    Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
    Γ' ≤ G' → K ≤ G' → V(G') = V(Γ') ∪ V(K) → E(G') = E(Γ') ∪ E(K) →
    subgraphInter G Γ K = subgraphInter G' Γ' K →
    ∀ (D D' : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β),
    Γ = D.toEmbeddedGraph ιV ιE → Γ' = D'.toEmbeddedGraph ιV ιE →
    IsVariant D D' (insulatedSet D (ιV ⁻¹' (V(Γ) ∩ V(K))) h) →
    ∀ (Z : Set α), Z ⊆ V(K) → Z.ncard ≤ p → L' ≤ G' →
    ∃ L ≤ G, HasSameEffectOn L L' Z ∧ subgraphInter G L K ≤ L' :=
  GM22.theorem_4_1_proof p

open scoped Pointwise in
open unitInterval GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM16 GraphMinor.GM19 in
/-- **4.2** (Graph Minors XXII, page 538):
"For every integer $p \ge 0$ there exists $h \ge 1$ with the following property. Let $\Gamma, K$ be
subgraphs of a graph $\Gamma \cup K$, let $\Gamma$ be a drawing in a surface $\Sigma$, and let
$$Z \subseteq V(K) \cup (V(\Gamma) \cap \text{bd}(\Sigma)),$$
with $|Z| \le p$. For each cuff $C$ of $\Sigma$ let $S(C)$ be a sleeve for $C$ in $\Gamma$, so that
$S(C_1) \cap S(C_2) = \emptyset$ for all distinct cuffs $C_1, C_2$. Let $S$ be the union of
$\Sigma \cap S(C)$ over all cuffs $C$, and let $T$ be the set of all points of $\Sigma$ that are
$h$-insulated in $\hat{\Sigma}$ from $V(\Gamma \cap K) \cup (V(\Gamma) \cap \text{bd}(\Sigma))$ by
$\Gamma$. Suppose that
(i) for each cuff $C$ there are $|V(\Gamma) \cap C|$ mutually vertex-disjoint paths of $\Gamma$
between $V(\Gamma) \cap C$ and $V(\Gamma) \cap \text{bd}(S(C))$,
(ii) for each cuff $C$, $\text{bd}(S(C)) \subseteq T$ and $S(C) \cap V(\Gamma \cap K) = \emptyset$.
Then for every $(S \cup T)$-variant $\Gamma'$ of $\Gamma$ with $\Gamma' \cap K = \Gamma \cap K$ and
$V(\Gamma') \cap \text{bd}(\Sigma) = V(\Gamma) \cap \text{bd}(\Sigma)$, and for every
$L' \subseteq \Gamma' \cup K$, there exists $L \subseteq \Gamma \cup K$ with the same effect on $Z$
as $L'$, with $L \cap K \subseteq L'$." -/
theorem theorem_4_2 (p : ℕ) :
    ∃ h ≥ 1, ∀ (S Shat : Type w) [TopologicalSpace S] [T2Space S]
    [TopologicalSpace Shat] [T2Space Shat],
    (hS : IsSurface S) → (cap : GM19.IsCappedSurface S Shat) →
    ∀ {α : Type u} {β : Type v} (G Γ K G' Γ' L' : Graph α β),
    V(G).Finite → E(G).Finite → V(G').Finite → E(G').Finite →
    Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
    Γ' ≤ G' → K ≤ G' → V(G') = V(Γ') ∪ V(K) → E(G') = E(Γ') ∪ E(K) →
    subgraphInter G Γ K = subgraphInter G' Γ' K →
    ∀ (D D' : Surface.Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β),
    Γ = D.toEmbeddedGraph ιV ιE → Γ' = D'.toEmbeddedGraph ιV ιE →
    D.U ∩ bd S ⊆ D.V → D'.V ∩ bd S = D.V ∩ bd S →
    ∀ (S_sleeve : Set S → Set Shat),
    (∀ C ∈ cuffs S, IsSleeve cap D C (S_sleeve C)) →
    (∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S, C₁ ≠ C₂ → Disjoint (S_sleeve C₁) (S_sleeve C₂)) →
    (∀ C ∈ cuffs S, ∃ P : ↑(D.V ∩ C) → Graph S (Set S),
      (∀ x : ↑(D.V ∩ C), ∃ y ∈ D.V ∩ cap.emb ⁻¹' subBd (S_sleeve C),
        IsGraphPathWithEnds D.toGraph (P x) x.1 y) ∧
      Pairwise (fun x₁ x₂ => Disjoint V(P x₁) V(P x₂))) →
    (∀ C ∈ cuffs S,
      subBd (S_sleeve C) ⊆
        cap.emb '' (cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
          (cap.emb '' ((ιV ⁻¹' (V(Γ) ∩ V(K))) ∪ (D.V ∩ bd S))) h) ∧
      Disjoint (S_sleeve C) (cap.emb '' (ιV ⁻¹' (V(Γ) ∩ V(K))))) →
    IsVariant D D'
      ((⋃ C ∈ cuffs S, cap.emb ⁻¹' S_sleeve C) ∪
        cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
          (cap.emb '' ((ιV ⁻¹' (V(Γ) ∩ V(K))) ∪ (D.V ∩ bd S))) h) →
    ∀ (Z : Set α), Z ⊆ V(K) ∪ ιV '' (D.V ∩ bd S) → Z.ncard ≤ p → L' ≤ G' →
    ∃ L ≤ G, HasSameEffectOn L L' Z ∧ subgraphInter G L K ≤ L' :=
  GM22.theorem_4_2_proof p

/-! ## Section 5. Tangles -/

open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 in
/-- **5.1** (Graph Minors XXII, page 539):
"Let $\Gamma$ be a 2-cell drawing in a surface $\Sigma$ with $\text{bd}(\Sigma) = \emptyset$, and
let $\mathcal{T}$ be a respectful tangle in $\Gamma$, with metric $d$. Let $z \in A(H)$, and
let $\kappa$ be an integer with $2 \le \kappa \le \text{ord}(\mathcal{T}) - 3$. Then there is a
closed disc $\Delta \subseteq \Sigma$ satisfying
(i) $\text{bd}(\Delta) \subseteq U(\Gamma)$,
(ii) $d(z, x) \le \kappa + 2$ for all $x \in A(\Gamma)$ with $x \cap \Delta \ne \emptyset$,
(iii) $d(z, x) \ge \kappa$ for all $x \in A(\Gamma)$ with
$x \nsubseteq \Delta \setminus \text{bd}(\Delta)$ (and in particular,
$z \subseteq \Delta \setminus \text{bd}(\Delta)$)."
The print has "$z \in A(H)$", a misprint for $z \in A(\Gamma)$: no $H$ is defined there, and
$d(z, x)$ needs $z$ to be an atom of $\Gamma$. The Lean takes $z \in A(\Gamma)$. See the correction
on page 539 in `corrections/GM22.md`. -/
theorem theorem_5_1 {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) (Γ : Surface.Drawing S) (ord κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (z : Set S)
    (hMetric : HasTangleMetric Γ ord T d) (hz : z ∈ Γ.A) (hκ2 : 2 ≤ κ) (hκ_ord : κ + 3 ≤ ord) :
    ∃ Δ : Set S,
    IsClosedDisc Δ ∧
    subBd Δ ⊆ Γ.U ∧
    (∀ x ∈ Γ.A, (x ∩ Δ).Nonempty → d z x ≤ κ + 2) ∧
    (∀ x ∈ Γ.A, ¬ (x ⊆ Δ \ subBd Δ) → κ ≤ d z x) ∧
    z ⊆ Δ \ subBd Δ :=
  GM22.theorem_5_1_proof hS hConn Γ ord κ T d z hMetric hz hκ2 hκ_ord

open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 in
/-- **5.2** (Graph Minors XXII, page 540):
"Let $h \ge 1$ be an integer, let $\Gamma$ be a 2-cell drawing in a surface $\Sigma$ with
$\text{bd}(\Sigma) = \emptyset$, and let $\mathcal{T}$ be a respectful tangle in $\Gamma$ of order
$\ge 2h + 5$, with metric $d$. Let $x \in \Sigma$, and let $Y$ be the union of all atoms
$y \in A(\Gamma)$ with $d(y, z) \ge 2h + 5$, where $z$ is the atom of $\Gamma$ with $x \in z$. Then
$x$ is $h$-insulated from $Y$ by $\Gamma$." -/
theorem theorem_5_2 {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) (Γ : Surface.Drawing S) (ord h : ℕ) (hh : 1 ≤ h)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (hMetric : HasTangleMetric Γ ord T d) (hord : 2 * h + 5 ≤ ord) (x : S) (z Y : Set S)
    (hz : z ∈ Γ.A) (hxz : x ∈ z) (hY : Y ⊆ ⋃ y ∈ {y ∈ Γ.A | 2 * h + 5 ≤ d y z}, y) :
    IsInsulated Γ Y h x :=
  GM22.theorem_5_2_proof hS hConn Γ ord h hh T d hMetric hord x z Y hz hxz hY

open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 in
/-- **5.3** (Graph Minors XXII, page 540):
"For every integer $p \ge 0$ there exists $\theta > p$ with the following property. Let $\Gamma, K$
be subgraphs of a graph $\Gamma \cup K$, let $\Gamma$ be a 2-cell drawing in a surface $\Sigma$ with
$\text{bd}(\Sigma) = \emptyset$, and let $\mathcal{T}$ be a respectful tangle in $\Gamma$ of order
$\ge \theta$, with metric $d$. Let $Z \subseteq V(\Gamma \cup K)$ with $|Z| \le p$, and let
$F_1, \ldots, F_t$ be $\Gamma$-normal $O$-arcs, such that
$$(F_1 \cup \cdots \cup F_t) \cap V(\Gamma) \subseteq Z \subseteq
((F_1 \cup \cdots \cup F_t) \cap V(\Gamma)) \cup V(K)$$
and $\text{ins}(F_1), \ldots, \text{ins}(F_t)$ are mutually disjoint. Suppose that
(i) for $1 \le i \le t$, there is no $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with
$|F \cap V(\Gamma)| < |F_i \cap V(\Gamma)|$ and $\text{ins}(F_i) \subseteq \text{ins}(F)$,
(ii) for $1 \le i < j \le t$, $d(\text{ins}(F_i), \text{ins}(F_j)) \ge \theta$,
(iii) for $1 \le i \le k$, $d(\text{ins}(F_i), v) \ge \theta$ for every $v \in V(\Gamma \cap K)$.
Let $R$ be the union of all atoms $z$ of $\Gamma$ with $d(z, v) \ge \theta$ for all
$v \in V(\Gamma \cap K)$, and let
$$\Sigma' = \Sigma \setminus \bigcup_{1 \le i \le t} (\text{ins}(F_i) \setminus F_i).$$
Let $\Gamma'$ be an $(R \cap \Sigma')$-variant of $\Gamma$ in $\Sigma$ with
$\Gamma' \cap K = \Gamma \cap K$ and with $\Gamma \cap \text{ins}(F_i) =
\Gamma' \cap \text{ins}(F_i)$ ($1 \le i \le t$), and let $L' \subseteq (\Gamma' \cap \Sigma') \cup
K$.
Then there exists $L \subseteq (\Gamma \cap \Sigma') \cup K$ with the same effect on $Z$ as $L'$,
such that $L \cap K \subseteq L'$." -/
theorem theorem_5_3 (p : ℕ) :
    ∃ θ : ℕ, p < θ ∧
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
      {α : Type u} {β : Type v}
      (ιV : S ↪ α) (ιE : Set S ↪ β)
      (Γ Γ' : Surface.Drawing S) (K L' : Graph α β)
      (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (ins : Set S → Set S) (d : Set S → Set S → ℕ)
      (Z : Set α) (t : ℕ) (F : Fin t → Set S),
      IsClosedSurface S →
      V(K).Finite → E(K).Finite →
      (Γ.toEmbeddedGraph ιV ιE).Compatible K →
      Γ.IsTwoCell →
      θ ≤ ord →
      HasTangleMetric Γ ord T d →
      (∀ F₀ : Set S, IsOArc F₀ → Γ.IsNormal F₀ → (F₀ ∩ Γ.V).ncard < ord →
        IsTangleIns Γ T F₀ (ins F₀)) →
      Z ⊆ V(graphUnion (Γ.toEmbeddedGraph ιV ιE) K) →
      Z.ncard ≤ p →
      (∀ i : Fin t, IsOArc (F i) ∧ Γ.IsNormal (F i)) →
      ιV '' ((⋃ i : Fin t, F i) ∩ Γ.V) ⊆ Z →
      Z ⊆ ιV '' ((⋃ i : Fin t, F i) ∩ Γ.V) ∪ V(K) →
      Pairwise (fun i j : Fin t => Disjoint (ins (F i)) (ins (F j))) →
      (∀ i : Fin t, ¬ ∃ F₀ : Set S, IsOArc F₀ ∧ Γ.IsNormal F₀ ∧
        (F₀ ∩ Γ.V).ncard < (F i ∩ Γ.V).ncard ∧ ins (F i) ⊆ ins F₀) →
      (∀ i j : Fin t, i ≠ j → θ ≤ subsetTangleDist Γ ord d (ins (F i)) (ins (F j))) →
      (∀ i : Fin t, ∀ v ∈ Γ.V, ιV v ∈ V(K) →
        θ ≤ subsetTangleDist Γ ord d (ins (F i)) {v}) →
      let R := ⋃ z ∈ {z ∈ Γ.A | ∀ v ∈ Γ.V, ιV v ∈ V(K) → θ ≤ d z {v}}, z
      let S' := Set.univ \ ⋃ i : Fin t, (ins (F i) \ F i)
      IsVariant Γ Γ' (R ∩ S') →
      (Γ'.toEmbeddedGraph ιV ιE).Compatible K →
      (Γ'.toEmbeddedGraph ιV ιE) ⊓ K = (Γ.toEmbeddedGraph ιV ιE) ⊓ K →
      (∀ i : Fin t, Γ.interSet (ins (F i)) = Γ'.interSet (ins (F i))) →
      L' ≤ graphUnion ((Γ'.interSet S').toEmbeddedGraph ιV ιE) K →
      ∃ L ≤ graphUnion ((Γ.interSet S').toEmbeddedGraph ιV ιE) K,
        effectOn L Z = effectOn L' Z ∧ L ⊓ K ≤ L' :=
  GM22.theorem_5_3_proof p

/-! ## Section 6. Rooted digraphs -/

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XXII, 6.1** (Section 6, page 542):
"If $H$ has detail $\le \delta$, every basis for $\phi$ includes a basis of cardinality
$\le q + 3\delta$." -/
theorem theorem_6_1 {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH} {q δ : ℕ}
    {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q} {φV : αH → Graph α β} {φE : βH → β}
    {Z : Set α} (hdetail : R_H.HasDetailLE δ) (hφ : IsRootedDigraphModel R_G R_H φV φE)
    (hZ : IsModelBasis R_G R_H φV φE Z) :
    ∃ Z₀ ⊆ Z, Z₀.Finite ∧ Z₀.ncard ≤ q + 3 * δ ∧ IsModelBasis R_G R_H φV φE Z₀ :=
  GM22.theorem_6_1_proof hdetail hφ hZ

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XXII, 6.2** (Section 6, page 542):
"Let $\phi$ be a model of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$, let $Z$ be a basis for
$\phi$, let $L = \bigcup(\phi(v) : v \in V(H))$, and let $L' \subseteq G \setminus \phi(E(H))$ with
the same effect on $Z$ as $L$. Define $\phi'(e) = \phi(e)$ ($e \in E(H)$), and for $v \in V(H)$ let
$\phi'(v)$ be the component $T$ of $L'$ with $V(T) \cap Z = V(\phi(v)) \cap Z$. Then $\phi'$ is a
model of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$." -/
theorem theorem_6_2 {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH} {q : ℕ}
    {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q} {φV : αH → Graph α β} {φE : βH → β}
    {Z : Set α} {L' : Graph α β} (hφ : IsRootedDigraphModel R_G R_H φV φE)
    (hZ : IsModelBasis R_G R_H φV φE Z)
    (hL'_le : L' ≤ R_G.G.toGraph.deleteEdges (φE '' E(R_H.G.toGraph)))
    (heff : effectOn L' Z = effectOn (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))) Z) :
    ∃ φV' : αH → Graph α β,
    (∀ v ∈ V(R_H.G.toGraph),
      IsGraphComponent (φV' v) L' ∧ V(φV' v) ∩ Z = V(φV v) ∩ Z) ∧
    IsRootedDigraphModel R_G R_H φV' φE :=
  GM22.theorem_6_2_proof hφ hZ hL'_le heff

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XXII, (6.3)** (page 543): "Suppose that the following hold:"

Without the root-preservation hypothesis $\alpha(u'_r) = u_r$ ($1 \le r \le q$) used in
Claim (9) on page 545, the statement of **Graph Minors XXII, (6.3)** (page 543) is false:
take $q = 1$, $k = 1$, $\delta = 0$, $G = G' = (\{\text{false}, \text{true}\}, \emptyset)$ with
roots $u_1 = u'_1 = \text{false}$, $H = (\{()\}, \emptyset)$ with root $v_1 = ()$,
$Z = Z' = \{\text{false}, \text{true}\}$, $A_0 = A'_0 = G$,
$A_1 = (\{\text{false}\}, \emptyset)$, $A'_1 = (\{\text{true}\}, \emptyset)$,
$\pi_1 = (\text{false})$, $\pi'_1 = (\text{true})$, $\alpha = \text{not}$,
$\phi(()) = A_1$, and $L'_0 = A'_0$.

So (6.3) is false as printed. The corrected `theorem_6_3` below adds the hypothesis `α(u'_j) = u_j`,
which is the closest form that holds, and which the paper's one use of (6.3) satisfies. See the
correction to (6.3) in `corrections/GM22.md`. -/
theorem not_theorem_6_3_without_roots :
    ¬ (∀ {α : Type} {β : Type} {α' : Type}
    {αH : Type} {βH : Type} {q k δ : ℕ}
    {R_G : RootedDigraph α β q} {R_G' : RootedDigraph α' β q}
    {R_H : RootedDigraph αH βH q}
    {Z : Set α} {A : Fin (k + 1) → Graph α β}
    {n : Fin k → ℕ} {π : ∀ i : Fin k, Fin (n i) → α}
    {Z' : Set α'} {A' : Fin (k + 1) → Graph α' β}
    {π' : ∀ i : Fin k, Fin (n i) → α'}
    {α_map : α' → α}
    {φV : αH → Graph α β} {φE : βH → β}
    {L'0 : Graph α' β}
    (hdiv : IsIndexedZDivision R_G.G.toGraph Z A)
    (hπ : ∀ i : Fin k, IsOrderingOf (Z ∩ V(A i.succ)) (π i))
    (hdiv' : IsIndexedZDivision R_G'.G.toGraph Z' A')
    (hπ' : ∀ i : Fin k, IsOrderingOf (Z' ∩ V(A' i.succ)) (π' i)),
    Z ⊆ V(R_G.G.toGraph) →
    (∀ r : Fin q, R_G.roots r ∈ Z) →
    Z ⊆ V(A 0) →
    Z' ⊆ V(R_G'.G.toGraph) →
    (∀ r : Fin q, R_G'.roots r ∈ Z') →
    Z' ⊆ V(A' 0) →
    R_H.HasDetailLE δ →
    (∀ i : Fin k,
      HasSameDeltaFolio
        (subRootedDigraph R_G'.G (A' i.succ) (hdiv'.1 i.succ) (π' i)
          (fun j => ((hπ' i).2 ▸ mem_range_self j).2))
        (subRootedDigraph R_G.G (A i.succ) (hdiv.1 i.succ) (π i)
          (fun j => ((hπ i).2 ▸ mem_range_self j).2))
        δ) →
    α_map '' Z' = Z →
    (∀ i : Fin k, ∀ j : Fin (n i), α_map (π' i j) = π i j) →
    IsRootedDigraphModel R_G R_H φV φE →
    (∀ e ∈ E(R_H.G.toGraph), ∃ i : Fin k, φE e ∈ E(A i.succ)) →
    (∀ v ∈ V(R_H.G.toGraph), ∃ i : Fin k, (V(φV v) ∩ V(A i.succ)).Nonempty) →
    L'0 ≤ A' 0 →
    (∀ u ∈ Z', ∀ v ∈ Z',
      AreConnectedIn L'0 u v ↔
        AreConnectedIn
          (subgraphInter R_G.G.toGraph (minimalModelSubgraph R_G R_H φV Z) (A 0))
          (α_map u) (α_map v)) →
    ∃ (φV' : αH → Graph α' β) (φE' : βH → β),
      IsRootedDigraphModel R_G' R_H φV' φE' ∧
      (∀ e ∈ E(R_H.G.toGraph), ∃ i : Fin k, φE' e ∈ E(A' i.succ)) ∧
      (∀ v ∈ V(R_H.G.toGraph), ∃ i : Fin k, (V(φV' v) ∩ V(A' i.succ)).Nonempty)) :=
  GM22.not_theorem_6_3_without_roots_proof

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 in
/-- **Graph Minors XXII, 6.3** (Section 6, pages 543–545):
"Suppose that the following hold:
• $(G, u_1, \ldots, u_q)$, $(G', u'_1, \ldots, u'_q)$ and $(H, v_1, \ldots, v_q)$ are rooted
digraphs;
• $Z \subseteq V(G)$ with $u_1, \ldots, u_q \in Z$; $\{A_0, A_1, \ldots, A_k\}$ is a $Z$-division of
  $G$ with $Z \subseteq V(A_0)$, and for $1 \le i \le k$, $\pi_i$ is an ordering of $Z \cap V(A_i)$;
• $Z' \subseteq V(G')$ with $u'_1, \ldots, u'_q \in Z'$; $\{A'_0, A'_1, \ldots, A'_k\}$ is a
  $Z'$-division of $G'$ with $Z' \subseteq V(A'_0)$; and for $1 \le i \le k$, $\pi'_i$ is an
  ordering of $Z' \cap V(A'_i)$;
• $\delta \ge 0$ is an integer such that $(H, v_1, \ldots, v_q)$ has detail $\le \delta$, and for
  $1 \le i \le k$, $(A'_i, \pi'_i)$ has the same $\delta$-folio as $(A_i, \pi_i)$;
• $\alpha \colon Z' \to Z$ is a function mapping $Z'$ onto $Z$ and for $1 \le i \le k$ mapping
  $\pi'_i$ to $\pi_i$;
• $\phi$ is a model of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$ such that
  $\phi(E(H)) \subseteq E(A_1 \cup \dots \cup A_k)$ and $\phi(v) \cap (A_1 \cup \dots \cup A_k)$ is
  non-null for each $v \in V(H)$;
• there exists $L'_0 \subseteq A'_0$ such that $u, v \in Z'$ are $L'_0$-connected if and only if
  $\alpha(u), \alpha(v)$ are $(L \cap A_0)$-connected, where $L \subseteq G$ is minimal such that
  $Z \subseteq V(L)$ and $\phi(v) \subseteq L$ for each $v \in V(H)$.

*Then there is a model $\phi'$ of $(H, v_1, \ldots, v_q)$ in $(G', u'_1, \ldots, u'_q)$ such that*
$$
\phi'(E(H)) \subseteq E(A'_1 \cup \dots \cup A'_k)
$$
*and $\phi'(v) \cap (A'_1 \cup \dots \cup A'_k)$ is non-null for each $v \in V(H)$.*"

The Lean adds the hypothesis `α(u'_j) = u_j`, which the proof of Claim (9) uses. See the correction
to (6.3) in `corrections/GM22.md`. The proof prints $P_i$ and $p_i$ for $P_j$ and $p_j$ on pages 543
and 544 (see the correction to the proof of (6.3) in the same file). -/
theorem theorem_6_3 {α : Type u} {β : Type v} {α' : Type u'} {αH : Type uH} {βH : Type vH}
    {q k δ : ℕ} {R_G : RootedDigraph α β q} {R_G' : RootedDigraph α' β q}
    {R_H : RootedDigraph αH βH q} {Z : Set α} {A : Fin (k + 1) → Graph α β} {n : Fin k → ℕ}
    {π : ∀ i : Fin k, Fin (n i) → α} {Z' : Set α'} {A' : Fin (k + 1) → Graph α' β}
    {π' : ∀ i : Fin k, Fin (n i) → α'} {α_map : α' → α} {φV : αH → Graph α β} {φE : βH → β}
    {L'0 : Graph α' β} (hZ : Z ⊆ V(R_G.G.toGraph)) (hroots_Z : ∀ r : Fin q, R_G.roots r ∈ Z)
    (hdiv : IsIndexedZDivision R_G.G.toGraph Z A) (hZ_A0 : Z ⊆ V(A 0))
    (hπ : ∀ i : Fin k, IsOrderingOf (Z ∩ V(A i.succ)) (π i)) (hZ' : Z' ⊆ V(R_G'.G.toGraph))
    (hroots_Z' : ∀ r : Fin q, R_G'.roots r ∈ Z') (hdiv' : IsIndexedZDivision R_G'.G.toGraph Z' A')
    (hZ'_A'0 : Z' ⊆ V(A' 0)) (hπ' : ∀ i : Fin k, IsOrderingOf (Z' ∩ V(A' i.succ)) (π' i))
    (hdetail : R_H.HasDetailLE δ)
    (hfolio : ∀ i : Fin k,
      HasSameDeltaFolio
      (subRootedDigraph R_G'.G (A' i.succ) (hdiv'.1 i.succ) (π' i)
        (fun j => ((hπ' i).2 ▸ mem_range_self j).2))
      (subRootedDigraph R_G.G (A i.succ) (hdiv.1 i.succ) (π i)
        (fun j => ((hπ i).2 ▸ mem_range_self j).2)) δ) (hα_surj : α_map '' Z' = Z)
    (hα_π : ∀ i : Fin k, ∀ j : Fin (n i), α_map (π' i j) = π i j)
    (hα_roots : ∀ r : Fin q, α_map (R_G'.roots r) = R_G.roots r)
    (hφ : IsRootedDigraphModel R_G R_H φV φE)
    (hφE_mem : ∀ e ∈ E(R_H.G.toGraph), ∃ i : Fin k, φE e ∈ E(A i.succ))
    (hφV_meets : ∀ v ∈ V(R_H.G.toGraph), ∃ i : Fin k, (V(φV v) ∩ V(A i.succ)).Nonempty)
    (hL'0_le : L'0 ≤ A' 0)
    (hL'0_conn : ∀ u ∈ Z', ∀ v ∈ Z', AreConnectedIn L'0 u v ↔
      AreConnectedIn (subgraphInter R_G.G.toGraph (minimalModelSubgraph R_G R_H φV Z) (A 0))
      (α_map u) (α_map v)) :
    ∃ (φV' : αH → Graph α' β) (φE' : βH → β),
    IsRootedDigraphModel R_G' R_H φV' φE' ∧
    (∀ e ∈ E(R_H.G.toGraph), ∃ i : Fin k, φE' e ∈ E(A' i.succ)) ∧
    (∀ v ∈ V(R_H.G.toGraph), ∃ i : Fin k, (V(φV' v) ∩ V(A' i.succ)).Nonempty) :=
  GM22.theorem_6_3_proof hZ hroots_Z hdiv hZ_A0 hπ hZ' hroots_Z' hdiv' hZ'_A'0 hπ' hdetail hfolio hα_surj hα_π hα_roots hφ hφE_mem hφV_meets hL'0_le hL'0_conn

/-! ## Section 7. A generalization -/

open GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 in
/-- **Graph Minors XXII, (7.1)** (pages 546–547):
"Let (J1)–(J6) hold, and let $K_1 = K \cup \bigcup(A \in \mathcal{A} : d(D(A), \Sigma \setminus
\Delta) \ge \theta)$. Then
(i) $d(V(\Gamma \cap K_1), \Sigma \setminus \Delta) \ge \theta$,
(ii) for $A \in \mathcal{A}$, if $d(D(A), \Sigma \setminus \Delta) < \theta$ then $E(A \cap K_1) =
\emptyset$ and $V(A \cap K_1) \subseteq \bar{\pi}(A) \cup W$,
(iii) for $A \in \mathcal{A}$, if $d(D(A), \Sigma \setminus \Delta) < \theta - 3$ then $A \cap K_1 =
N_W$."
The proof of (iii) prints "Choose $z \in Z(\Gamma)$", a misprint for $z \in A(\Gamma)$; the proof in
Lean takes $z$ to be an atom of $\Gamma$. See the correction to the proof of (7.1) in
`corrections/GM22.md`. -/
theorem theorem_7_1 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    {αH : Type u₁} {βH : Type v₁} {q : ℕ} {ιV : S ↪ α} {ιE : Set S ↪ β} {R_G : RootedDigraph α β q}
    {W : Set α} {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ}
    {πS : ∀ A : Graph α β, Fin (πLen A) → S} {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Set S → Set S}
    {d : Set S → Set S → ℕ} {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q} {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE) :
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph
      {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})
    ((∀ v ∈ Γ.V, ιV v ∈ V(K₁) → θ ≤ subsetTangleDist Γ ord d {v} (Set.univ \ Δ)) ∧
      θ ≤ subsetTangleDist Γ ord d {v ∈ Γ.V | ιV v ∈ V(K₁)} (Set.univ \ Δ)) ∧
    (∀ A ∈ 𝒜, subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ →
      E(A ⊓ K₁) = ∅ ∧ V(A ⊓ K₁) ⊆ (ιV '' Set.range (πS A)) ∪ W) ∧
    (∀ A ∈ 𝒜, subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ - 3 →
      A ⊓ K₁ = Graph.noEdge W β) :=
  GM22.theorem_7_1_proof hJ

open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 in
/-- **Graph Minors XXII, (7.2)** (page 547):
"For all $q, \delta \ge 0$ there exists $\theta \ge 4$ with the following property. Let (J1)–(J6)
hold, and let $\mathcal{A}' \subseteq \mathcal{A}$ be adequate for some model $\phi'$ of
$(H, \chi)$ in $(G, \omega)$, where $d(v^*, D(A)) \ge \theta$ for all $A \in \mathcal{A}'$. Then
there is a model of $(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$." -/
theorem theorem_7_2 (q δ : ℕ) :
    ∃ θ : ℕ, 4 ≤ θ ∧
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
      {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
      (ιV : S ↪ α) (ιE : Set S ↪ β)
      (R_G : RootedDigraph α β q) (W : Set α)
      (𝒜 𝒜' : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
      (Γ : Drawing S) (orient : GM19.SurfaceOrientation S)
      (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (ins : Set S → Set S) (d : Set S → Set S → ℕ)
      (D : Graph α β → Set S)
      (N K : Graph α β) (Δ : Set S) (v_star : S)
      (R_H : RootedDigraph αH βH q)
      (φV φV' : αH → Graph α β) (φE φE' : βH → β)
      (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE),
      IsRootedDigraphModel R_G R_H φV' φE' →
      IsAdequateFor ιV ιE W 𝒜 𝒜' Γ K R_H φV' φE' →
      (∀ A ∈ 𝒜', θ ≤ subsetTangleDist Γ ord d {v_star} (D A)) →
      HasRootedDigraphModel
        (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
          R_G.roots hJ.roots_mem_deleteVerts_v_star)
        R_H :=
  GM22.theorem_7_2_proof q δ

open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 in
/-- **Graph Minors XXII, (7.3)** (pages 547–548):
"For all integers $q, \delta, \tau \ge 0$ there exists $\theta \ge 5$ with the following property.
Let (J1)–(J6) hold, and let $\mathcal{B} \subseteq \mathcal{A}$ be adequate for $\phi$. Let
$A_1, \dots, A_t \in \mathcal{B}$ where $t \le \tau$, and let
$d(D(A), \Sigma \setminus \Delta) \ge \theta$ for every
$A \in \mathcal{B} \setminus \{A_1, \dots, A_t\}$. Let $A_1', \dots, A_t' \in \mathcal{A}$, and
suppose that
(i) for $1 \le i \le t$, $(A_i', \pi(A_i') + \omega)$ has the same $\delta$-folio as
$(A_i, \pi(A_i) + \omega)$,
(ii) for $1 \le i \le t$, $D(A_i) \cap \Delta = \emptyset$,
(iii) for $1 \le i \le t$, $d(v^*, D(A_i')) \ge \theta$ and $D(A_i') \cap \Delta = \emptyset$,"
"(iv) for $1 \le i < j \le t$, $d(D(A_i'), D(A_j')) \ge \theta$,
(v) for $1 \le i \le t$, there is no $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with
$|F \cap V(\Gamma)| < |\bar{\pi}(A_i')|$ and with $D(A_i') \subseteq ins(F)$.
Then there is a model of $(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$." -/
theorem theorem_7_3 (q δ τ : ℕ) :
    ∃ θ : ℕ, 5 ≤ θ ∧
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
      {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
      (ιV : S ↪ α) (ιE : Set S ↪ β)
      (R_G : RootedDigraph α β q) (W : Set α)
      (𝒜 ℬ : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
      (Γ : Drawing S) (orient : GM19.SurfaceOrientation S)
      (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (ins : Set S → Set S) (d : Set S → Set S → ℕ)
      (D : Graph α β → Set S)
      (N K : Graph α β) (Δ : Set S) (v_star : S)
      (R_H : RootedDigraph αH βH q)
      (φV : αH → Graph α β) (φE : βH → β)
      (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE),
      IsAdequateFor ιV ιE W 𝒜 ℬ Γ K R_H φV φE →
      ∀ (t : ℕ) (A_fam A_fam' : Fin t → Graph α β),
      t ≤ τ →
      (∀ i : Fin t, A_fam i ∈ ℬ) →
      (∀ i : Fin t, A_fam' i ∈ 𝒜) →
      (∀ A ∈ ℬ \ Set.range A_fam,
        θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)) →
      ∀ (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i)),
      (∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
        (hπi : ∀ k : Fin (πLen (A_fam i) + q),
          seqConcat (ιV ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
        (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
          seqConcat (fun k : Fin (πLen (A_fam i)) =>
            ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
        HasSameDeltaFolio
          (subRootedDigraph R_G.G (A_fam' i) hA'i
            (seqConcat (fun k : Fin (πLen (A_fam i)) =>
              ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
          (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (ιV ∘ πS (A_fam i)) R_G.roots) hπi) δ) →
      (∀ i : Fin t, Disjoint (D (A_fam i)) Δ) →
      (∀ i : Fin t, θ ≤ subsetTangleDist Γ ord d {v_star} (D (A_fam' i))) →
      (∀ i : Fin t, Disjoint (D (A_fam' i)) Δ) →
      (∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j))) →
      (∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
        (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F) →
      HasRootedDigraphModel
        (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
          R_G.roots hJ.roots_mem_deleteVerts_v_star)
        R_H :=
  GM22.theorem_7_3_proof q δ τ

open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 in
/-- **Graph Minors XXII, (7.4)** (pages 552–553):
"For all integers $q, \delta, \tau \ge 0$ there exists $\theta \ge 4$ with the following property.
Let (J1)–(J7) hold, and let $\mathcal{B} \subseteq \mathcal{A}$ be sufficient for $\phi$. Let
$A_1, \ldots, A_t \in \mathcal{B}$ where $t \le \tau$, and let
$d(D(A), \Sigma \setminus \Delta) \ge \theta$ for every
$A \in \mathcal{B} \setminus \{A_1, \ldots, A_t\}$. Let $A'_1, \ldots, A'_t \in \mathcal{A}$, and
suppose that"
"(i) for $1 \le i \le t$, $(A'_i, \pi(A'_i) + \omega)$ has the same $\delta$-folio as
$(A_i, \pi(A_i) + \omega)$,
(ii) for $1 \le i \le t$, $D(A_i) \cap \Delta = \emptyset$,
(iii) for $1 \le i \le t$, $d(v^*, D(A'_i)) \ge \theta$ and $D(A'_i) \cap \Delta = \emptyset$,
(iv) for $1 \le i < j \le t$, $d(D(A'_i), D(A'_j)) \ge \theta$.
Then there is a model of $(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$."
The proof prints "$d$ and $d'$" for "$d$ by $d'$" (page 553) and $N_w$ for $N_W$ (page 554). See
the corrections to the proof of (7.4) in `corrections/GM22.md`. -/
theorem theorem_7_4 (q δ τ : ℕ) :
    ∃ θ : ℕ, 4 ≤ θ ∧
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
      {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
      (ιV₀ : S ↪ α) (ιE₀ : Set S ↪ β)
      (R_G : RootedDigraph α β q) (W : Set α)
      (𝒜 ℬ : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
      (Γ₀ : Drawing S) (orient : GM19.SurfaceOrientation S)
      (ord₀ : ℕ) (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (ins₀ : Set S → Set S) (d₀ : Set S → Set S → ℕ)
      (D : Graph α β → Set S)
      (N K : Graph α β) (Δ : Set S) (v_star : S)
      (R_H : RootedDigraph αH βH q)
      (φV₀ : αH → Graph α β) (φE₀ : βH → β)
      (hJ₀ : SystemJ1ToJ6 ιV₀ ιE₀ R_G W 𝒜 πLen πS Γ₀ orient θ ord₀ T₀ ins₀ d₀ D N K Δ v_star δ R_H φV₀ φE₀),
      ConditionJ7 ιV₀ ιE₀ R_G.G.toGraph W 𝒜 πLen πS Γ₀ T₀ →
      IsSufficientFor W 𝒜 ℬ K R_H φV₀ φE₀ →
      ∀ (t : ℕ) (A_fam A_fam' : Fin t → Graph α β),
      t ≤ τ →
      (∀ i : Fin t, A_fam i ∈ ℬ) →
      (∀ i : Fin t, A_fam' i ∈ 𝒜) →
      (∀ A ∈ ℬ \ Set.range A_fam,
        θ ≤ subsetTangleDist Γ₀ ord₀ d₀ (D A) (Set.univ \ Δ)) →
      ∀ (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i)),
      (∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
        (hπi : ∀ k : Fin (πLen (A_fam i) + q),
          seqConcat (ιV₀ ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
        (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
          seqConcat (fun k : Fin (πLen (A_fam i)) =>
            ιV₀ (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
        HasSameDeltaFolio
          (subRootedDigraph R_G.G (A_fam' i) hA'i
            (seqConcat (fun k : Fin (πLen (A_fam i)) =>
              ιV₀ (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
          (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (ιV₀ ∘ πS (A_fam i)) R_G.roots) hπi) δ) →
      (∀ i : Fin t, Disjoint (D (A_fam i)) Δ) →
      (∀ i : Fin t, θ ≤ subsetTangleDist Γ₀ ord₀ d₀ {v_star} (D (A_fam' i))) →
      (∀ i : Fin t, Disjoint (D (A_fam' i)) Δ) →
      (∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ₀ ord₀ d₀ (D (A_fam' i)) (D (A_fam' j))) →
      HasRootedDigraphModel
        (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV₀ v_star}) Graph.deleteVerts_le
          R_G.roots hJ₀.roots_mem_deleteVerts_v_star)
        R_H :=
  GM22.theorem_7_4_proof q δ τ

/-! ## Section 8. Homogeneity -/

open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 in
/-- **Graph Minors XXII, (8.1)** (page 556): "Let (J1)–(J6) hold. Then there exists $\mathcal{A}'
\subseteq \mathcal{A}$, sufficient for some model of $(H, \chi)$ in $(G, \omega)$, such that
$d(D(A), \Sigma \setminus \Delta) < \theta$ for at most $3q + 5\delta$ members $A$ of
$\mathcal{A}'$."

(Section 8, page 556):
*Let (J1)–(J6) hold. Then there exists $$\mathcal{A}' \subseteq \mathcal{A}$$, sufficient for some
model of $$(H, \chi)$$ in $$(G, \omega)$$, such that there are at most $$3q + 5\delta$$ members
$$A$$ of $$\mathcal{A}'$$ with $$d(D(A), \Sigma \setminus \Delta) < \theta$$.* -/
theorem theorem_8_1 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    {αH : Type u₁} {βH : Type v₁} {q : ℕ} {ιV : S ↪ α} {ιE : Set S ↪ β} {R_G : RootedDigraph α β q}
    {W : Set α} {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ}
    {πS : ∀ A : Graph α β, Fin (πLen A) → S} {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Set S → Set S}
    {d : Set S → Set S → ℕ} {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q} {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE) :
    ∃ (𝒜' : Set (Graph α β)) (φV' : αH → Graph α β) (φE' : βH → β),
    IsRootedDigraphModel R_G R_H φV' φE' ∧
    IsSufficientFor W 𝒜 𝒜' K R_H φV' φE' ∧
    {A ∈ 𝒜' | subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ}.ncard ≤ 3 * q + 5 * δ :=
  GM22.theorem_8_1_proof hJ

open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 in
/-- **Graph Minors XXII, (8.2)** (page 557): "For all integers $q, \delta, \eta \ge 0$ there exists
$\theta \ge 4$ with the following property. Let (J1)–(J7) hold, and suppose that for every $A \in
\mathcal{A}$ with $D(A) \cap \Delta = \emptyset$ and every $v \in V(\Gamma)$ with $v \notin \Delta$,
there exists $A' \in \mathcal{A}$ with $d(v, D(A')) \le \eta$ such that $(A', \pi(A') + \omega)$ has
the same $\delta$-folio as $(A, \pi(A) + \omega)$. Suppose also that $d(v^*, \Delta) \ge \theta$.
Then there is a model of $(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$."

(Section 8, page 557):
*For all integers $$q, \delta, \eta \ge 0$$ there exists $$\theta \ge 4$$ with the following
property. Let (J1)–(J7) hold, and suppose that for every $$A \in \mathcal{A}$$ with
$$D(A) \cap \Delta = \emptyset$$ and every $$v \in V(\Gamma)$$ with $$v \notin \Delta$$, there
exists $$A' \in \mathcal{A}$$ with $$d(v, D(A')) \le \eta$$ such that
$$(A', \pi(A') + \omega)$$ has the same $$\delta$$-folio as $$(A, \pi(A) + \omega)$$. Suppose also
that $$d(v^*, \Delta) \ge \theta$$. Then there is a model of $$(H, \chi)$$ in
$$(G \setminus \{v^*\}, \omega)$$.* -/
theorem theorem_8_2 (q δ η : ℕ) :
    ∃ θ : ℕ, 4 ≤ θ ∧
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
      {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
      (ιV : S ↪ α) (ιE : Set S ↪ β)
      (R_G : RootedDigraph α β q) (W : Set α)
      (𝒜 : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
      (Γ : Drawing S) (orient : GM19.SurfaceOrientation S)
      (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (ins : Set S → Set S) (d : Set S → Set S → ℕ)
      (D : Graph α β → Set S)
      (N K : Graph α β) (Δ : Set S) (v_star : S)
      (R_H : RootedDigraph αH βH q)
      (φV : αH → Graph α β) (φE : βH → β)
      (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE),
      ConditionJ7 ιV ιE R_G.G.toGraph W 𝒜 πLen πS Γ T →
      (∀ A ∈ 𝒜, Disjoint (D A) Δ → ∀ v ∈ Γ.V, v ∉ Δ →
        ∃ A' ∈ 𝒜, subsetTangleDist Γ ord d {v} (D A') ≤ η ∧
          ∃ hlen : πLen A' = πLen A,
            ∀ (hA : A ≤ R_G.G.toGraph) (hA' : A' ≤ R_G.G.toGraph)
              (hπ : ∀ k : Fin (πLen A + q),
                seqConcat (ιV ∘ πS A) R_G.roots k ∈ V(A))
              (hπ' : ∀ k : Fin (πLen A + q),
                seqConcat (fun k : Fin (πLen A) =>
                  ιV (πS A' (Fin.cast hlen.symm k))) R_G.roots k ∈ V(A')),
              HasSameDeltaFolio
                (subRootedDigraph R_G.G A' hA'
                  (seqConcat (fun k : Fin (πLen A) =>
                    ιV (πS A' (Fin.cast hlen.symm k))) R_G.roots) hπ')
                (subRootedDigraph R_G.G A hA
                  (seqConcat (ιV ∘ πS A) R_G.roots) hπ) δ) →
      θ ≤ subsetTangleDist Γ ord d {v_star} Δ →
      HasRootedDigraphModel
        (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
          R_G.roots hJ.roots_mem_deleteVerts_v_star)
        R_H :=
  GM22.theorem_8_2_proof q δ η

open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM19 in
/-- **Graph Minors XXII, (8.3)** (Section 8, pages 559–560):
"For all $q, \delta \ge 0$ and $h \ge 4$, there exists $\theta \ge h$ with the following property.
Let $G$ be a digraph, let $W \subseteq V(G)$ with $|W| = q$, and let $\omega$ be an ordering of $W$.
Let $\Gamma \subseteq G \setminus W$ satisfy the following. ... Then $(G \setminus \{v^*\}, \omega)$
has the same $\delta$-folio as $(G, \omega)$." -/
theorem theorem_8_3 (q δ h : ℕ) :
    ∃ θ : ℕ, h ≤ θ ∧ 4 ≤ θ ∧
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
      {α : Type u} {β : Type v}
      (ιV : S ↪ α) (ιE : Set S ↪ β)
      (R_G : RootedDigraph α β q) (W : Set α)
      (Γ C₀ : GM19.Drawing S) (r₀ : Set S) (orient : GM19.SurfaceOrientation S)
      (PiSet : Set S)
      (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ)
      (J : Graph α β) (Z : Set α) (𝒜 : Set (Graph α β))
      (πLen : Graph α β → ℕ) (πA : ∀ A : Graph α β, Fin (πLen A) → α)
      (vA : Graph α β → S) (D_disc : Set S) (v_star : S)
      (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
        πLen πA vA D_disc v_star),
      HasSameDeltaFolio
        (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
          R_G.roots h83.roots_mem_deleteVerts_v_star)
        R_G δ :=
  GM22.theorem_8_3_proof q δ h

end GraphMinor.GM22
