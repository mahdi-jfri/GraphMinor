module

public import GraphMinor.GM21.Final
public import GraphMinor.GM21.Parallel
public import GraphMinor.GM21.Section10
public import GraphMinor.GM21.Section11One
public import GraphMinor.GM21.Section12One
public import GraphMinor.GM21.Section12Width
public import GraphMinor.GM21.Section12ThreeStep
public import GraphMinor.GM21.Section12Four
public import GraphMinor.GM21.Section11Three
public import GraphMinor.GM21.Section11Two
public import GraphMinor.GM21.Section1Two
public import GraphMinor.GM21.Section2
public import GraphMinor.GM21.Section3
public import GraphMinor.GM21.Section4
public import GraphMinor.GM21.Section4Tangle
public import GraphMinor.GM21.Section5
public import GraphMinor.GM21.Section5One
public import GraphMinor.GM21.Section6
public import GraphMinor.GM21.Section6Five
public import GraphMinor.GM21.Section6Four
public import GraphMinor.GM21.Section6Universe
public import GraphMinor.GM21.Section6Three
public import GraphMinor.GM21.Section7
public import GraphMinor.GM21.Section7ThreeProof
public import GraphMinor.GM21.Section8
public import GraphMinor.GM21.Section8Free
public import GraphMinor.GM21.Section9

/-!
# Graph Minors XXI: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XXI. Graphs with unique linkages*, J. Combin. Theory
Ser. B **99** (2009), 583–616.

Page numbers of Graph Minors XXI, here and in every file of this repository, are those of the
authors' version of April 18, 2011 (the preprint), not those of the journal.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. Where the Lean differs from the paper, the docstring of the result says so,
and `corrections/GM21.md` lists the corrections.
-/

public section

namespace GraphMinor.GM21

open Set Topology Function Hypergraph

universe u v w

/-! ## Section 1. Introduction -/

open GraphMinor.GM21.Final Graph SimpleGraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 in
/-- **Graph Minors XXI, (1.1)** (Section 1, page 1 of the preprint):
"**1.1** *For every integer $p \ge 0$ there exists $w \ge 0$ such that every graph with a vital
$p$-linkage has tree-width $\le w$.*" -/
theorem theorem_1_1 (p : ℕ) :
    ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G L : Graph α β), V(G).Finite → E(G).Finite →
    Final.IsVitalPLinkage G L p → Final.TreeWidthLE G w :=
  GM21.Final.theorem_1_1_proof p

open GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (1.2)** (page 2 of the preprint):
"**1.2** *If $L$ is a vital $5$-linkage in a simple graph $G$, then either some two terminals in
different components of $L$ are adjacent in $G$, or some terminal has the same degree in $G$ and in
$L$, or $G$ is null.*"

"Simple" is written as: `G` is a graph, each edge has two ends, and no two edges have the same
ends. The paper gives no proof, and the Lean proof is our own. If the first two outcomes fail,
then every terminal has an edge of `G` that is not in `L`, and this edge ends inside another path
of `L`. So the ends of each of the two paths with an edge send edges into the inside of the other,
and exchanging the two paths gives another linkage with the same pattern, against vitality. -/
theorem theorem_1_2 {α : Type u} {β : Type v} {G L : Hypergraph α β} (hG : G.IsGraph)
    (h2 : ∀ e ∈ G.edgeSet, (G.ends e).ncard = 2)
    (hinj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, G.ends e₁ = G.ends e₂ → e₁ = e₂)
    (hL : IsVitalPLinkage G L 5) :
    (∃ t₁ ∈ terminals L, ∃ t₂ ∈ terminals L,
      (¬ ∃ C, IsComponentOf L C ∧ t₁ ∈ C.vertexSet ∧ t₂ ∈ C.vertexSet) ∧ G.skeleton.Adj t₁ t₂) ∨
    (∃ t ∈ terminals L, vertexDegree G t = vertexDegree L t) ∨ G.vertexSet = ∅ :=
  GM21.theorem_1_2_proof hG h2 hinj hL

/-! ## Section 2. Some basic lemmas -/

open GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (2.1)** (page 2 of the preprint):
"If $L$ is a vital $p$-linkage in $G$, and $X \subseteq V(G)$, then $L \setminus X$ is a vital
$(p + 2|X|)$-linkage in $G \setminus X$." -/
theorem theorem_2_1 {α : Type u} {β : Type v} {G L : Hypergraph α β} {p : ℕ} {X : Set α}
    (hL : IsVitalPLinkage G L p) (hX : X ⊆ G.vertexSet) :
    IsVitalPLinkage (G.deleteVertices X) (L.deleteVertices X) (p + 2 * X.ncard) :=
  GM21.theorem_2_1_proof hL hX

open GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (2.2)** (page 2 of the preprint):
"If $L$ is a linkage in $G$ with set of terminals $X$, and $(A, B)$ is a separation of $G$, then
$L \cap B$ is a linkage in $B$ with set of terminals a subset of
$(X \setminus V(A)) \cup V(A \cap B)$." -/
theorem theorem_2_2 {α : Type u} {β : Type v} {G L A B : Hypergraph α β} (hL : IsLinkage G L)
    (hsep : G.IsSeparation A B) :
    IsLinkage B (L ∩ B) ∧
    terminals (L ∩ B) ⊆ (terminals L \ A.vertexSet) ∪ (A ∩ B).vertexSet :=
  GM21.theorem_2_2_proof hL hsep

open GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (2.3)** (page 2 of the preprint):
"If $L$ is a linkage in $G$, and $(A, B)$ is a separation of $G$, and $L'$ is a linkage in $B$
with the same pattern as $L \cap B$, then $(L \cap A) \cup L'$ is a linkage in $G$ with the same
pattern as $L$. In particular, if $L$ is a vital linkage in $G$ then $L \cap B$ is a vital linkage
in $B$."

In the first conclusion, `(L ∩ A)` is formalized as `prunedLeft L A B`, which removes
vertices of `V(L ∩ A ∩ B)` that are internal (degree `2`) in `L ∩ B` so that routing `L'` away
from such a separator vertex does not leave an uncancelled degree-`0` terminal in the union. As
printed, the first claim is false. See the correction to (2.3) in `corrections/GM21.md`. -/
theorem theorem_2_3 {α : Type u} {β : Type v} {G L A B : Hypergraph α β} (hL : IsLinkage G L)
    (hsep : G.IsSeparation A B) :
    (∀ L' : Hypergraph α β,
      IsLinkage B L' →
      linkagePattern L' = linkagePattern (L ∩ B) →
      IsLinkage G (prunedLeft L A B ∪ L') ∧
        linkagePattern (prunedLeft L A B ∪ L') = linkagePattern L) ∧
    (IsVitalLinkage G L → IsVitalLinkage B (L ∩ B)) :=
  GM21.theorem_2_3_proof hL hsep

open GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (2.4)** (page 3 of the preprint):
"If $G'$ is obtained from $G$ by splitting a vertex $v$, and $G$ has a vital $p$-linkage, then
$G'$ has a vital $(p+2)$-linkage." -/
theorem theorem_2_4 {α : Type u} {β : Type v} {G G' : Hypergraph α β} {p : ℕ}
    (hsplit : ObtainedBySplittingVertex G G') (hL : HasVitalPLinkage G p) :
    HasVitalPLinkage G' (p + 2) :=
  GM21.theorem_2_4_proof hsplit hL

open GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (2.5)** (page 3 of the preprint):
"Let $p, k \ge 0$ and let $n = (2p + 1)(p + k + 1)^{2(p+k)} + 1$. Let $L$ be a vital $p$-linkage
in a graph $G$, and for $1 \le i \le n$ let $(A_i, B_i)$ be a separation of $G$ of order $k$, such
that
1. $A_i \subseteq A_j$ and $B_j \subseteq B_i$ for $1 \le i < j \le n$, and
2. for $1 \le i < n$, there is a linkage $M_i$ in $B_i \cap A_{i+1}$ with $k$ components, each with
one end in $V(A_i \cap B_i)$ and the other in $V(A_{i+1} \cap B_{i+1})$.
Then there exists $i$ with $1 \le i < n$ such that $L \cap B_i \cap A_{i+1} = M_i$." -/
theorem theorem_2_5 {α : Type u} {β : Type v} (p k : ℕ) (G L : Hypergraph α β)
    (A B : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k)) + 1) → Hypergraph α β)
    (M : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k))) → Hypergraph α β)
    (hL : IsVitalPLinkage G L p)
    (hsep : ∀ r : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k)) + 1), G.IsSeparation (A r) (B r) ∧
      separationOrder (A r) (B r) = k)
    (hmono : ∀ r₁ r₂ : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k)) + 1), r₁ < r₂ → A r₁ ≤ A r₂ ∧
      B r₂ ≤ B r₁)
    (hM : ∀ r : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k))),
      IsLinkage (B r.castSucc ∩ A r.succ) (M r) ∧ (linkagePattern (M r)).ncard = k ∧
      ∀ P ∈ linkagePattern (M r), ∃ u ∈ (A r.castSucc ∩ B r.castSucc).vertexSet,
      ∃ w ∈ (A r.succ ∩ B r.succ).vertexSet, P = {u, w}) :
    ∃ r : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k))),
    L ∩ B r.castSucc ∩ A r.succ = M r :=
  GM21.theorem_2_5_proof p k G L A B M hL hsep hmono hM

open GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (2.6)** (pages 6–7 of the preprint):
"For all integers $p, k \ge 0$ there exists $n \ge 0$ with the following property. Let $L$ be a
vital $p$-linkage in a graph $G$, and for $1 \le i \le n$ let $(A_i, B_i)$ be a separation of $G$
of order $\le k$, such that ...
1. $A_i \subseteq A_j$ and $B_j \subseteq B_i$, for $1 \le i < j \le n$
2. if $1 \le i < i' \le n$, and $|V(A_i \cap B_i)| = |V(A_{i'} \cap B_{i'})| = k'$ say, and
$|V(A_j \cap B_j)| > k'$ for all $j$ with $i < j < i'$, then there is a linkage $M_{ii'}$ in
$B_i \cap A_{i'}$ with $k'$ components, each with one end in $V(A_i \cap B_i)$ and the other in
$V(A_{i'} \cap B_{i'})$.
Then there exist $i, i'$ as in (ii) such that $L \cap B_i \cap A_{i'} = M_{ii'}$." -/
theorem theorem_2_6 (p k : ℕ) :
    ∃ n : ℕ, 2 ≤ n ∧
    ∀ {α : Type u} {β : Type v} (G L : Hypergraph α β)
      (A B : Fin n → Hypergraph α β)
      (M : Fin n → Fin n → Hypergraph α β),
      IsVitalPLinkage G L p →
      (∀ i : Fin n, G.IsSeparation (A i) (B i) ∧ separationOrder (A i) (B i) ≤ k) →
      (∀ i j : Fin n, i < j → A i ≤ A j ∧ B j ≤ B i) →
      (∀ i i' : Fin n, i < i' →
        separationOrder (A i) (B i) = separationOrder (A i') (B i') →
        (∀ j : Fin n, i < j → j < i' →
          separationOrder (A i) (B i) < separationOrder (A j) (B j)) →
        IsLinkage (B i ∩ A i') (M i i') ∧
        (linkagePattern (M i i')).ncard = separationOrder (A i) (B i) ∧
        ∀ P ∈ linkagePattern (M i i'),
          ∃ u ∈ (A i ∩ B i).vertexSet,
            ∃ w ∈ (A i' ∩ B i').vertexSet, P = {u, w}) →
      ∃ i i' : Fin n, i < i' ∧
        separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
        (∀ j : Fin n, i < j → j < i' →
          separationOrder (A i) (B i) < separationOrder (A j) (B j)) ∧
        L ∩ B i ∩ A i' = M i i' :=
  GM21.theorem_2_6_proof p k

open GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (2.7)** (page 8 of the preprint):
"For all integers $p, k \ge 0$ there exists $n \ge 0$ with the following property. Let $L, L'$ be
vital $p$-linkages in a graph $G$, and for $1 \le i \le n$ let $(A_i, B_i)$ be as in (2.6),
satisfying (2.6)(i) and (ii). Then there exist $i, i'$ as in (ii) such that
$L \cap B_i \cap A_{i'} = L' \cap B_i \cap A_{i'} = M_{ii'}$." -/
theorem theorem_2_7 {α : Type u} {β : Type v} (p k : ℕ) :
    ∃ n : ℕ, 2 ≤ n ∧
    ∀ (G L L' : Hypergraph α β)
      (A B : Fin n → Hypergraph α β)
      (M : Fin n → Fin n → Hypergraph α β),
      IsVitalPLinkage G L p →
      IsVitalPLinkage G L' p →
      (∀ i : Fin n, G.IsSeparation (A i) (B i) ∧ separationOrder (A i) (B i) ≤ k) →
      (∀ i j : Fin n, i < j → A i ≤ A j ∧ B j ≤ B i) →
      (∀ i i' : Fin n, i < i' →
        separationOrder (A i) (B i) = separationOrder (A i') (B i') →
        (∀ j : Fin n, i < j → j < i' →
          separationOrder (A i) (B i) < separationOrder (A j) (B j)) →
        IsLinkage (B i ∩ A i') (M i i') ∧
        (linkagePattern (M i i')).ncard = separationOrder (A i) (B i) ∧
        ∀ P ∈ linkagePattern (M i i'),
          ∃ u ∈ (A i ∩ B i).vertexSet,
            ∃ w ∈ (A i' ∩ B i').vertexSet, P = {u, w}) →
      ∃ i i' : Fin n, i < i' ∧
        separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
        (∀ j : Fin n, i < j → j < i' →
          separationOrder (A i) (B i) < separationOrder (A j) (B j)) ∧
        L ∩ B i ∩ A i' = M i i' ∧
        L' ∩ B i ∩ A i' = M i i' :=
  GM21.theorem_2_7_proof p k

/-! ## Section 3. Tangles -/

open GraphMinor.GM10 in
/-- **Graph Minors XXI, (3.1)** (Section 3, page 8 of the preprint):
"If a graph $G$ has tree-width $w$, then $G$ has a tangle of order $\ge \frac{2}{3}(w + 1)$, and
has no tangle of order $> w + 1$."
Proved from Graph Minors X, (5.2) (`GM10.theorem_5_2`). -/
theorem theorem_3_1 {α : Type u} {β : Type v} (G : Hypergraph α β) (w : ℕ)
    (hw : treeWidthPlusOne G = w + 1) :
    (∃ (θ : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle G θ 𝒯 ∧ 2 * (w + 1) ≤ 3 * θ) ∧
    (∀ (θ : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle G θ 𝒯 → θ ≤ w + 1) :=
  GM21.theorem_3_1_proof G w hw

open GraphMinor.GM10 in
/-- **Graph Minors XXI, (3.2)** (Section 3, page 9 of the preprint):
"With $\mathcal{T}, \theta, G, W$ as above, $\mathcal{T} \setminus W$ is a tangle of order
$\theta - |W|$ in $G \setminus W$."
Proved from Graph Minors X, (8.5) (`GM10.theorem_8_5`). -/
theorem theorem_3_2 {α : Type u} {β : Type v} {G : Hypergraph α β} (hG : G.IsGraph) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) {W : Set α}
    (hW : W ⊆ G.vertexSet) (hcard : W.ncard < θ) :
    IsTangle (G.deleteVertices W) (θ - W.ncard) (deleteVerticesTangle G W 𝒯 θ) :=
  GM21.theorem_3_2_proof hG h𝒯 hW hcard

open GraphMinor.GM10 in
/-- **Graph Minors XXI, (3.3)** (Section 3, page 9 of the preprint):
"Let $\mathcal{T}$ be a tangle in a graph $G$, and let $(C, D) \in \mathcal{T}$ of order $0$. Let
$$\mathcal{T}' = \{(A \cap D, B \cap D) : (A, B) \in \mathcal{T}\}.$$
Then $\mathcal{T}'$ is a tangle in $B$ of the same order as $\mathcal{T}$."

The print's $B$ is a misprint for $D$, and Lean uses $D$ (see the correction to (3.3) in
`corrections/GM21.md`). -/
theorem theorem_3_3 {α : Type u} {β : Type v} {G C D : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) (hCD : (C, D) ∈ 𝒯)
    (hord0 : separationOrder C D = 0) :
    IsTangle D θ (restrictOrderZeroTangle D 𝒯) :=
  GM21.theorem_3_3_proof h𝒯 hCD hord0

open GraphMinor.GM10 in
/-- **Graph Minors XXI, (3.4)** (Section 3, page 9 of the preprint):
"Let $G'$ be a subgraph of $G$, and let $\mathcal{T}'$ be a tangle in $G'$. Let $\mathcal{T}$ be
the set of all separations $(A, B)$ of $G$ of order $< ord(\mathcal{T}')$ such that
$(A \cap G', B \cap G') \in \mathcal{T}'$. Then $\mathcal{T}$ is a tangle in $G$ of order
$ord(\mathcal{T}')$." -/
theorem theorem_3_4 {α : Type u} {β : Type v} {G G' : Hypergraph α β} (hG' : G' ≤ G) {θ : ℕ}
    {𝒯' : Set (Hypergraph α β × Hypergraph α β)} (h𝒯' : IsTangle G' θ 𝒯') :
    IsTangle G θ (GM12.inducedBySubgraph G G' θ 𝒯') :=
  GM21.theorem_3_4_proof hG' h𝒯'

open GraphMinor.GM10 in
/-- **Graph Minors XXI, (3.5)** (Section 3, page 9 of the preprint):
"Let $\mathcal{T}$ be a tangle in $G$ and let $(A_0, B_0) \in \mathcal{T}$. Then there is a tangle
$\mathcal{T}_0$ in $B_0$ of order $ord(\mathcal{T}) - |V(A_0 \cap B_0)|$, such that
$(A \cap B_0, B \cap B_0) \in \mathcal{T}_0$ for every $(A, B) \in \mathcal{T}$ of order
$< ord(\mathcal{T}) - |V(A_0 \cap B_0)|$." -/
theorem theorem_3_5 {α : Type u} {β : Type v} {G A₀ B₀ : Hypergraph α β} (hG : G.IsGraph) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) (hAB₀ : (A₀, B₀) ∈ 𝒯) :
    ∃ 𝒯₀ : Set (Hypergraph α β × Hypergraph α β),
    IsTangle B₀ (θ - separationOrder A₀ B₀) 𝒯₀ ∧
    ∀ A B : Hypergraph α β, (A, B) ∈ 𝒯 →
      separationOrder A B < θ - separationOrder A₀ B₀ →
      (A ∩ B₀, B ∩ B₀) ∈ 𝒯₀ :=
  GM21.theorem_3_5_proof hG h𝒯 hAB₀

open GraphMinor.GM10 in
/-- **Graph Minors XXI, (3.6)** (Section 3, page 10 of the preprint):
"If $G'$ can be obtained from $G$ by splitting a vertex, and $\mathcal{T}$ is a tangle in $G$ of
order $\ge 2$, there is a tangle in $G'$ of order $ord(\mathcal{T}) - 1$." -/
theorem theorem_3_6 {α : Type u} {β : Type v} {G G' : Hypergraph α β} (hG : G.IsGraph)
    (hsplit : ObtainedBySplittingVertex G G') {θ : ℕ} (hθ : 2 ≤ θ)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    ∃ 𝒯' : Set (Hypergraph α β × Hypergraph α β), IsTangle G' (θ - 1) 𝒯' :=
  GM21.theorem_3_6_proof hG hsplit hθ h𝒯

open GraphMinor.GM10 in
/-- **Graph Minors XXI, (3.7)** (Section 3, page 10 of the preprint):
"If $\mathcal{T}$ is a tangle in $G$, and $\theta$ is an integer with $1 \le \theta \le
ord(\mathcal{T})$,
then the set of all members of $\mathcal{T}$ of order $< \theta$ is a tangle in $G$ of order
$\theta$." -/
theorem theorem_3_7 {α : Type u} {β : Type v} {G : Hypergraph α β} {θ₀ θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ₀ 𝒯) (h1 : 1 ≤ θ) (hle : θ ≤ θ₀) :
    IsTangle G θ (truncation 𝒯 θ) :=
  GM21.theorem_3_7_proof h𝒯 h1 hle

/-! ## Section 4. Surfaces -/

open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM19 in
/-- **Graph Minors XXI, (4.1)** (page 11 of the preprint):
"Let $\Sigma$ be a surface, and let $\Sigma'$ be obtained by cutting along $F \subseteq \Sigma$.
1. If $F$ is a proper line with ends in different cuffs then $\hat{\Sigma}'$ is homeomorphic to
$\hat{\Sigma}$ and $c(\hat{\Sigma}') = c(\hat{\Sigma}) - 1$.
2. If $F$ is a proper line with ends in the same cuff and $\Sigma'$ is connected then
$\hat{\Sigma}'$ is simpler than $\hat{\Sigma}$.
3. If $bd(\Sigma) = \emptyset$ and $F$ is an $O$-arc and $\Sigma'$ is connected then
$\hat{\Sigma}'$ is simpler than $\Sigma$."

Note: in (1), `c(Σ)` is the number of cuffs of `Σ`, which the paper writes `c(\hat{\Sigma})` by a
typographical slip for `c(\Sigma)`.

Clause (i) is stated as `(cuffs S').ncard + 1 = (cuffs S).ncard`. See the correction to (4.1) in
`corrections/GM21.md`. -/
theorem theorem_4_1 {S Shat S' Shat' : Type} [TopologicalSpace S] [TopologicalSpace Shat]
    [TopologicalSpace S'] [TopologicalSpace Shat'] (hS : IsSurface S) [ConnectedSpace S]
    (hS' : IsSurface S') {F : Set S} {ψ : S' → S} (hcut : IsCutting ψ F)
    (cap : IsCappedSurface S Shat) (cap' : IsCappedSurface S' Shat') :
    (∀ (s t : S) (C₁ C₂ : Set S),
      C₁ ∈ cuffs S → C₂ ∈ cuffs S → C₁ ≠ C₂ →
      s ∈ C₁ → t ∈ C₂ → IsProperLineInSurface F s t →
      Nonempty (Shat' ≃ₜ Shat) ∧
        (cuffs S').ncard + 1 = (cuffs S).ncard) ∧
    (∀ (s t : S) (C : Set S),
      C ∈ cuffs S → s ∈ C → t ∈ C → IsProperLineInSurface F s t →
      ConnectedSpace S' →
      IsSimplerThan Shat' Shat) ∧
    (bd S = ∅ → IsOArc F → ConnectedSpace S' →
      IsSimplerThan Shat' S) :=
  GM21.theorem_4_1_proof hS hS' hcut cap cap'

open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM19 in
/-- **Graph Minors XXI, (4.2)** (page 11 of the preprint):
"Let $\Sigma$ be a surface, and let $\Sigma_1, \Sigma_2 \subseteq \Sigma$ be surfaces with
$\Sigma_1 \cup \Sigma_2 = \Sigma$ and $\Sigma_1 \cap \Sigma_2 = F$.
1. If $F$ is a proper line in $\Sigma$ with both ends in the same cuff, then either $\hat{\Sigma}_2$
is simpler than $\hat{\Sigma}$ or $\hat{\Sigma}_1$ is a sphere.
2. If $F$ is a proper line in $\Sigma$ with both ends in the same cuff, and $\hat{\Sigma}_1$ is a
sphere, then $\hat{\Sigma}_2$ is homeomorphic to $\hat{\Sigma}$; and either $c(\Sigma_2) <
c(\Sigma)$,
or $c(\Sigma_2) = c(\Sigma)$ and there is a closed disc $\Delta \subseteq \Sigma$ with
$F \subseteq bd(\Delta) \subseteq F \cup bd(\Sigma)$.
3. If $bd(\Sigma) = \emptyset$ and $F$ is an $O$-arc in $\Sigma$, then either $\hat{\Sigma}_2$ is
simpler than $\hat{\Sigma}$ or $\Sigma_1$ is a closed disc." -/
theorem theorem_4_2 {S Shat Shat₁ Shat₂ : Type} [TopologicalSpace S] [TopologicalSpace Shat]
    [TopologicalSpace Shat₁] [TopologicalSpace Shat₂] (hS : IsSurface S) [ConnectedSpace S]
    {S₁ S₂ F : Set S} (hS₁ : IsSurface S₁) [ConnectedSpace S₁] (hS₂ : IsSurface S₂)
    [ConnectedSpace S₂] (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F) (cap : IsCappedSurface S Shat)
    (cap₁ : IsCappedSurface S₁ Shat₁) (cap₂ : IsCappedSurface S₂ Shat₂) :
    (∀ (s t : S) (C : Set S),
      C ∈ cuffs S → s ∈ C → t ∈ C → IsProperLineInSurface F s t →
      IsSimplerThan Shat₂ Shat ∨ IsSphere Shat₁) ∧
    (∀ (s t : S) (C : Set S),
      C ∈ cuffs S → s ∈ C → t ∈ C → IsProperLineInSurface F s t →
      IsSphere Shat₁ →
      Nonempty (Shat₂ ≃ₜ Shat) ∧
        ((cuffs S₂).ncard < (cuffs S).ncard ∨
          ((cuffs S₂).ncard = (cuffs S).ncard ∧
            ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S))) ∧
    (bd S = ∅ → IsOArc F →
      IsSimplerThan Shat₂ Shat ∨ IsClosedDisc S₁) :=
  GM21.theorem_4_2_proof hS hS₁ hS₂ hun hint cap cap₁ cap₂

open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM19 in
/-- **Graph Minors XXI, (4.3)** (page 12 of the preprint):
"If $bd(\Sigma) = \emptyset$, a drawing $\Gamma$ in $\Sigma$ is 2-cell if and only if
$V(\Gamma) \ne \emptyset$, $\Gamma$ is connected, and for every $O$-arc $F \subseteq \Sigma$ with
$F \cap U(\Gamma) = \emptyset$, there is a closed disc $\Delta \subseteq \Sigma$ with
$bd(\Delta) = F$." -/
theorem theorem_4_3 {S : Type} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hbd : bd S = ∅) (Γ : Surface.Drawing S) :
    Γ.IsTwoCell ↔
    (Γ.V.Nonempty ∧ IsPreconnected Γ.U ∧
     ∀ F : Set S, IsOArc F → Disjoint F Γ.U →
       ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F) :=
  GM21.theorem_4_3_proof hS hbd Γ

open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM19 in
/-- **Graph Minors XXI, (4.4)** (page 12 of the preprint):
"If $bd(\Sigma) = \emptyset$, an $O$-arc $F \subseteq \Sigma$ bounds a closed disc in $\Sigma$ if
and only if $F$ is null-homotopic in $\Sigma$." -/
theorem theorem_4_4 {S : Type} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hbd : bd S = ∅) {F : Set S} (hF : IsOArc F) :
    (∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F) ↔ IsNullHomotopicOArc F :=
  GM21.theorem_4_4_proof hS hbd hF

open GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM19 in
/-- **Graph Minors XXI, (4.5)** (page 12 of the preprint):
"For every surface $\Sigma$ with $bd(\Sigma) = \emptyset$ and every integer $\theta' \ge 1$ there
is an integer $\theta \ge 1$ such that, if $\Gamma$ is a drawing in $\Sigma$ with a tangle of order
$\ge \theta$, and $\Gamma'$ is obtained from $\Gamma$ by deleting some vertices and edges, all
incident with one region of $\Gamma$ in $\Sigma$, then $\Gamma'$ has a tangle of order
$\ge \theta'$."

The Lean proof corrects a step of the paper's proof. See the correction to the proof of (4.5) in
`corrections/GM21.md`. -/
theorem theorem_4_5 {S : Type} [TopologicalSpace S] (hS : IsSurface S) [ConnectedSpace S]
    (hbd : bd S = ∅) {θ' : ℕ} (hθ' : 1 ≤ θ') :
    ∃ θ : ℕ, 1 ≤ θ ∧
    ∀ (Γ Γ' : Surface.Drawing S) (r : Set S),
      r ∈ Γ.R →
      Γ'.IsSubdrawing Γ →
      Γ.V \ Γ'.V ⊆ closure r →
      (∀ e ∈ Γ.E \ Γ'.E, (e ∩ closure r).Nonempty ∨ (closure e ∩ (Γ.V \ Γ'.V)).Nonempty) →
      (∃ (θ₀ : ℕ) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
        θ ≤ θ₀ ∧ IsTangle Γ.toHypergraph θ₀ 𝒯) →
      ∃ (θ₁ : ℕ) (𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
        θ' ≤ θ₁ ∧ IsTangle Γ'.toHypergraph θ₁ 𝒯' :=
  GM21.theorem_4_5_proof hS hbd hθ'

open GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM19 in
/-- **Graph Minors XXI, (4.6)** (page 14 of the preprint):
"For any surface $\Sigma$ with $bd(\Sigma) = \emptyset$, and all integers $\theta' \ge 1$ and
$\rho \ge 0$, there exists $\theta \ge 1$ such that, if $\Gamma$ is a drawing in $\Sigma$ with a
tangle of order $\ge \theta$, and $r_1, \dots, r_\rho$ are regions of $\Gamma$ in $\Sigma$, and
$\Gamma'$ is obtained from $\Gamma$ by deleting some vertices and edges each incident with one of
$r_1, \dots, r_\rho$, then $\Gamma'$ has a tangle of order $\ge \theta'$." -/
theorem theorem_4_6 {S : Type} [TopologicalSpace S] (hS : IsSurface S) [ConnectedSpace S]
    (hbd : bd S = ∅) {θ' : ℕ} (hθ' : 1 ≤ θ') (ρ : ℕ) :
    ∃ θ : ℕ, 1 ≤ θ ∧
    ∀ (Γ Γ' : Surface.Drawing S) (r : Fin ρ → Set S),
      (∀ i, r i ∈ Γ.R) →
      Γ'.IsSubdrawing Γ →
      (∀ v ∈ Γ.V \ Γ'.V, ∃ i, v ∈ closure (r i)) →
      (∀ e ∈ Γ.E \ Γ'.E, (∃ i, (e ∩ closure (r i)).Nonempty) ∨ (closure e ∩ (Γ.V \ Γ'.V)).Nonempty) →
      (∃ (θ₀ : ℕ) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
        θ ≤ θ₀ ∧ IsTangle Γ.toHypergraph θ₀ 𝒯) →
      ∃ (θ₁ : ℕ) (𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
        θ' ≤ θ₁ ∧ IsTangle Γ'.toHypergraph θ₁ 𝒯' :=
  GM21.theorem_4_6_proof hS hbd hθ' ρ

/-! ## Section 5. Linkages on surfaces -/

open GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM19 in
/-- **Graph Minors XXI, (5.1)** (page 15 of the preprint):
"For every surface $\Sigma$ and integer $p \ge 0$, there exists $\theta > p$ with the following
property. Let $\Gamma$ be a drawing in $\Sigma$ with $|V(\Gamma) \cap bd(\Sigma)| = p$, and let
$\mathcal{T}$ be a respectful tangle in $\Gamma$ of order $\ge \theta$. Suppose that
(i) there is no $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ such that
$|F \cap V(\Gamma)| < |C \cap V(\Gamma)|$ and $C \subseteq ins(F)$ for some cuff $C$ of $\Sigma$,
and
(ii) for every two cuffs $C_1, C_2$, the corresponding cuff regions $r_1, r_2$ satisfy
$d(r_1, r_2) \ge \theta$ where $d$ is the metric of $\mathcal{T}$.
Then there is no vital linkage in $\Gamma$ with set of terminals $V(\Gamma) \cap bd(\Sigma)$."

The Lean proof corrects a step of the paper's proof. See the correction to the proof of (5.1) in
`corrections/GM21.md`. -/
theorem theorem_5_1 {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) (p : ℕ) :
    ∃ θ : ℕ, p < θ ∧ ∀ (Γ : Surface.Drawing S), Γ.IsProper →
    (Γ.V ∩ bd S).ncard = p →
    ∀ (θ₀ : ℕ), θ ≤ θ₀ →
    ∀ (T : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat)))
      (d : Set Shat → Set Shat → ℕ),
    HasTangleMetric (capDrawing hS cap Γ) θ₀ T d →
    (∀ (F : Set S) (D : Set Shat) (C : Set S),
      (PaintingOrDrawing.drawing Γ).IsNormal F → IsOArc F →
      (F ∩ Γ.V).ncard < (C ∩ Γ.V).ncard → C ∈ cuffs S →
      IsClosedDisc D → subBd D = cap.emb '' F →
      ((PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter D,
        (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).interOutside D) ∈ T →
      ¬ cap.emb '' C ⊆ D) →
    (∀ (C₁ C₂ : Set S) (r₁ r₂ : Set Shat),
      C₁ ≠ C₂ → IsCuffRegion hS cap Γ C₁ r₁ → IsCuffRegion hS cap Γ C₂ r₂ →
      θ ≤ d r₁ r₂) →
    ∀ (L : Hypergraph S (Set S)), IsVitalLinkage Γ.toHypergraph L →
      terminals L ≠ Γ.V ∩ bd S :=
  GM21.theorem_5_1_proof hS cap p

open GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM17 GraphMinor.GM19 in
/-- **Graph Minors XXI, (5.2)** (page 17 of the preprint):
"For every surface $\Sigma$ with $bd(\Sigma) = \emptyset$ and every integer $p \ge 0$ there exists
$\theta \ge 1$ such that every drawing in $\Sigma$ with a tangle of order $\ge \theta$ has no vital
$p$-linkage."

The Lean proof corrects two steps of the paper's proof, in Claims (5) and (12). See the corrections
to the proof of (5.2) in `corrections/GM21.md`. -/
theorem theorem_5_2 {S₀ : Type} [TopologicalSpace S₀] [ConnectedSpace S₀] (hS₀ : IsSurface S₀)
    (hbd₀ : bd S₀ = ∅) (p : ℕ) :
    ∃ θ : ℕ, 1 ≤ θ ∧
    ∀ (Γ : Surface.Drawing S₀) (θ_G : ℕ)
      (𝒯 : Set (Hypergraph S₀ (Set S₀) × Hypergraph S₀ (Set S₀))),
      θ ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p :=
  GM21.theorem_5_2_proof hS₀ hbd₀ p

/-! ## Section 6. Presentations -/

open GraphMinor.GM19 hiding Drawing in
open Classical GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM21.Supports in
/-- **Graph Minors XXI, (6.1)** (page 22 of the preprint):
"**6.1** *Let* $\Gamma, F_1^*, \dots, F_r^*, H_1, \dots, H_r, \mu$ *be a presentation of* $G$ *in*
$\Sigma$. *Let* $a, b, a', b' \in F_1^* \cap V(\Gamma)$ *be in order and let* $I, I' \subseteq
F_1^*$
*be the supports with ends* $a, b$ *and* $a', b'$ *respectively. Let* $|\mu(a)| = q$; *let*
$P_1, \dots, P_q$ *be mutually vertex-disjoint paths of* $\mu(I)$ *between* $V(\mu(a))$ *and*
$V(\mu(b))$; *and let* $P_1', \dots, P_q'$ *be mutually vertex-disjoint paths of* $\mu(I')$
*between*
$V(\mu(a'))$ *and* $V(\mu(b'))$.
(i) *For* $1 \le i, i' \le q$, *if* $v \in V(P_i \cap P_{i'}')$, *then*
$v \in V(\mu(b) \cap \mu(a'))$ *and* $v$ *is an end of* $P_i$ *and of* $P_{i'}'$.
(ii) *If* $a' = b$, *then* $P_1, \dots, P_q$ *can be renumbered so that*
$P_1 \cup P_1', \dots, P_q \cup P_q'$ *are mutually vertex-disjoint paths of* $\mu(I \cup I')$
*between* $V(\mu(a))$ *and* $V(\mu(b'))$.
(iii) *If* $|\mu(a) \cup \mu(b')| = |\mu(a') \cup \mu(b)| = k$ *say, then*
$\{P_1, \dots, P_q, P_1', \dots, P_q'\}$ *has cardinality* $k$, *and its members are* $k$
*mutually vertex-disjoint paths of* $\mu(I) \cup \mu(I')$ *between* $V(\mu(a) \cup \mu(b'))$
*and* $V(\mu(b) \cup \mu(a'))$."

As in `theorem_6_1_i`, the binders `hJ_sub : J ⊆ F_star j`, `hJ_ends : SupportHasEnds Γ J b b'`,
`hIJ_inter : I ∩ J = {b}`, and `hI'J : I' ⊆ J` state that $a, b, a', b'$ are in order along
$F_j^*$ (see `exists_support_J_iff_areInOrderInSupport`). -/
theorem theorem_6_1 {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] {G : Hypergraph α β}
    {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β} {r : ℕ}
    {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β} {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r)
    {a b a' b' : S} {I I' J : Set S} (hI_sub : I ⊆ F_star j) (hI_ends : SupportHasEnds Γ I a b)
    (hI'_sub : I' ⊆ F_star j) (hI'_ends : SupportHasEnds Γ I' a' b') (hJ_sub : J ⊆ F_star j)
    (hJ_ends : SupportHasEnds Γ J b b') (hIJ_inter : I ∩ J = {b}) (hI'J : I' ⊆ J)
    {uP vP uP' vP' : Fin (q j) → α}
    (P : ∀ i : Fin (q j), (supportGraph G Γ μ I).skeleton.Walk (uP i) (vP i))
    (P' : ∀ i : Fin (q j), (supportGraph G Γ μ I').skeleton.Walk (uP' i) (vP' i))
    (huP : ∀ i, uP i ∈ (μ (.vertex a)).vertexSet) (hvP : ∀ i, vP i ∈ (μ (.vertex b)).vertexSet)
    (hP_path : ∀ i, (P i).IsPath)
    (hP_disj : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint {x | x ∈ (P i₁).support} {x | x ∈ (P i₂).support})
    (huP' : ∀ i, uP' i ∈ (μ (.vertex a')).vertexSet)
    (hvP' : ∀ i, vP' i ∈ (μ (.vertex b')).vertexSet) (hP'_path : ∀ i, (P' i).IsPath)
    (hP'_disj : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint {x | x ∈ (P' i₁).support} {x | x ∈ (P' i₂).support}) :
    ((∀ (i i' : Fin (q j)) {v : α},
       v ∈ (P i).support → v ∈ (P' i').support →
       v ∈ (μ (.vertex b)).vertexSet ∩ (μ (.vertex a')).vertexSet ∧
       v = vP i ∧ v = uP' i') ∧
    (a' = b →
       ∃ (σ : Equiv.Perm (Fin (q j))) (hσ : ∀ i : Fin (q j), vP (σ i) = uP' i),
         let Q : ∀ i : Fin (q j),
             (supportGraph G Γ μ (I ∪ I')).skeleton.Walk (uP (σ i)) (vP' i) :=
           fun i =>
             ((P (σ i)).mapLe (supportGraph_skeleton_mono subset_union_left)).append
               (((P' i).copy (hσ i).symm rfl).mapLe (supportGraph_skeleton_mono subset_union_right))
         (∀ i : Fin (q j), uP (σ i) ∈ (μ (.vertex a)).vertexSet) ∧
         (∀ i : Fin (q j), vP' i ∈ (μ (.vertex b')).vertexSet) ∧
         (∀ i : Fin (q j), (Q i).IsPath) ∧
         (∀ i₁ i₂ : Fin (q j), i₁ ≠ i₂ →
           Disjoint {x | x ∈ (Q i₁).support} {x | x ∈ (Q i₂).support})) ∧
    (∀ k : ℕ,
       ((μ (.vertex a)).vertexSet ∪ (μ (.vertex b')).vertexSet).ncard = k →
       ((μ (.vertex a')).vertexSet ∪ (μ (.vertex b)).vertexSet).ncard = k →
       let P_set : Set (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton.Subgraph :=
         Set.range (fun i =>
           ((P i).mapLe (skeleton_le_union_left (supportGraph G Γ μ I) (supportGraph G Γ μ I'))).toSubgraph) ∪
         Set.range (fun i =>
           ((P' i).mapLe (skeleton_le_union_right (supportGraph G Γ μ I) (supportGraph G Γ μ I'))).toSubgraph)
       P_set.ncard = k ∧
       (∀ Q₁ ∈ P_set, ∀ Q₂ ∈ P_set, Q₁ ≠ Q₂ → Disjoint Q₁.verts Q₂.verts) ∧
       (∀ Q ∈ P_set, ∃ (u v : α)
         (w : (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton.Walk u v),
         w.IsPath ∧
         u ∈ (μ (.vertex a)).vertexSet ∪ (μ (.vertex b')).vertexSet ∧
         v ∈ (μ (.vertex b)).vertexSet ∪ (μ (.vertex a')).vertexSet ∧
         w.toSubgraph = Q))) :=
  GM21.theorem_6_1_proof h_pres j hI_sub hI_ends hI'_sub hI'_ends hJ_sub hJ_ends hIJ_inter hI'J P P' huP hvP hP_path hP_disj huP' hvP' hP'_path hP'_disj

open GraphMinor.GM19 hiding Drawing in
open Classical GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM21.Supports in
/-- **Graph Minors XXI, (6.2)** (page 23 of the preprint):
"Let $\Gamma, F_1^*, \ldots, F_r^*, H_1, \ldots, H_r, \mu$ be a presentation of a graph $G$ in some
surface $\Sigma$. Let $I \subseteq F_1^*$ be a support with ends $a, b$. Then there are
$|V(\mu(a))|$ mutually vertex-disjoint paths of $\mu(I)$ between $V(\mu(a))$ and $V(\mu(b))$." -/
theorem theorem_6_2 {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] {G : Hypergraph α β}
    {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β} {r : ℕ}
    {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β} {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r) {I : Set S}
    {a b : S} (hI_sub : I ⊆ F_star j) (hI_ends : SupportHasEnds Γ I a b) :
    HasDisjointPaths (supportGraph G Γ μ I).skeleton
    (μ (.vertex a)).vertexSet (μ (.vertex b)).vertexSet (q j) :=
  GM21.theorem_6_2_proof h_pres j hI_sub hI_ends

open Induction GraphMinor.Surface GraphMinor.GM10 in
/-- **Graph Minors XXI, (6.3)** (page 24 of the preprint):
"**6.3** *For every surface $\Sigma$ and all integers $p, r \ge 0$ and $q \ge 1$, there exists
$\lambda \ge 0$ such that, if $G$ is a graph with a presentation in $\Sigma$ of depth $\le q$ and
defect $\le r$, and there is an exhaustive vital $p$-linkage in $G$, then there are at most
$\lambda$ $\Sigma$-jumps.*"

For a surface in `Type`, every connected surface has a type (`exists_hasType`), and
`boundForType_all` gives the bound for it. A surface in any other universe is homeomorphic to a
model surface in `Type`, by the classification of surfaces, and the presentation moves along the
homeomorphism (`GM21.theorem_6_3_proof`).

The Lean proof corrects several steps of the paper's proof, in Claims (2), (3) and (4). See the
corrections to the proof of (6.3) in `corrections/GM21.md`. -/
theorem theorem_6_3 (S : Type w) [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (p r q : ℕ) (hq : 1 ≤ q) :
    ∃ lam : ℕ,
    ∀ {α : Type u} {β : Type v} (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
    (ιV : S → α) (ιE : Set S → β) (r' : ℕ) (F_star : Fin r' → Set S) (H : Fin r' →
      Hypergraph α β) (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β), G.IsGraph → r' ≤
    r → PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q →
    IsExhaustiveLinkage G Γ_sub r' H L → IsPLinkage G L p → (sigmaJumps Γ Γ_sub ιV).encard ≤ lam :=
  GM21.theorem_6_3_proof S hS p r q hq

open GraphMinor.Surface GraphMinor.GM21.Cuts in
/-- **Graph Minors XXI, (6.4)** (page 24 of the preprint): "*For all integers $p \ge 0$ and
$q \ge 1$ there exists $\lambda \ge 0$ such that, if $G$ has a presentation in a disc $\Sigma$ of
depth $\le q$ and defect 1, and there is an exhaustive vital $p$-linkage in $G$, then there are at
most $\lambda$ $\Sigma$-jumps.*"

A disc is a space homeomorphic to the closed unit disc (`GM06.IsClosedDiscSpace`). The proof
follows the paper: the regions of `Γ` form a tree whose edges match the jumps, and the tree has at
most `n^n` edges (`RegionTree.ncard_jumpSet_le`). The paper's bound on the paths of the tree holds
only for paths from the region outside `F*`. See the correction to the proof of (6.4) in
`corrections/GM21.md`. -/
theorem theorem_6_4 (p q : ℕ) (_hq : 1 ≤ q) :
    ∃ lam : ℕ, ∀ {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α)
    (ιE : Set S → β) (F_star : Fin 1 → Set S) (H : Fin 1 → Hypergraph α β)
    (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
    GM06.IsClosedDiscSpace S → G.IsGraph →
    PresentationHasDepthLe G Γ Γ_sub ιV ιE 1 F_star H μ q →
    IsExhaustiveLinkage G Γ_sub 1 H L → IsPLinkage G L p →
    (sigmaJumps Γ Γ_sub ιV).encard ≤ lam :=
  GM21.theorem_6_4_proof p q _hq

open GraphMinor.Surface GraphMinor.GM21.Cuts in
/-- **Graph Minors XXI, (6.5)** (page 25 of the preprint): "*For all integers $p \ge 0$ and
$q \ge 1$ there exists $\lambda \ge 0$ such that, if $G$ has a presentation in a disc $\Sigma$ of
depth $\le q$ and defect 2, and there is an exhaustive vital $p$-linkage in $G$, then there are at
most $\lambda$ $\Sigma$-jumps.*"

Follows the paper's proof: choose $n$ from (2.6) for $(p, 2q)$ and $\lambda'$ from (6.4) for
$(p + 2q, q)$, and set $\lambda = n(2\lambda' + 1)$.

The Lean proof corrects two steps of the paper's proof. See the corrections to the proof of (6.5)
in `corrections/GM21.md`. -/
theorem theorem_6_5 (p q : ℕ) (hq : 1 ≤ q) :
    ∃ lam : ℕ, ∀ {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α)
    (ιE : Set S → β) (F_star : Fin 2 → Set S) (H : Fin 2 → Hypergraph α β)
    (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
    GM06.IsClosedDiscSpace S → G.IsGraph →
    PresentationHasDepthLe G Γ Γ_sub ιV ιE 2 F_star H μ q →
    IsExhaustiveLinkage G Γ_sub 2 H L → IsPLinkage G L p →
    (sigmaJumps Γ Γ_sub ιV).encard ≤ lam :=
  GM21.theorem_6_5_proof p q hq

open GraphMinor.Surface GraphMinor.GM21.Cuts in
/-- **Graph Minors XXI, (6.6)** (page 27 of the preprint): "*For all integers $p \ge 0$ and
$q \ge 1$ there exists $\lambda \ge 0$ such that, if $G$ has a presentation in a disc $\Sigma$ of
depth $\le q$ and defect $3$, and there is an exhaustive vital $p$-linkage $G$, then there are at
most $\lambda$ $\Sigma$-jumps.*"

Follows the paper's proof: choose $\lambda'$ from (6.5) for $(p + 2q, q)$, set $\lambda =
3\lambda'$,
and cut $\Sigma$ into three closed discs $\Delta_1, \Delta_2, \Delta_3$ through a region $r_0$
incident with vertices in all three supports (`ThreeSupports.encard_sigmaJumps_le_three_of_region`).

The Lean reads "in `G`", and the proof does the "easy exercise". See the corrections to (6.6) and
to its proof in `corrections/GM21.md`. -/
theorem theorem_6_6 (p q : ℕ) (hq : 1 ≤ q) :
    ∃ lam : ℕ, ∀ {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α)
    (ιE : Set S → β) (F_star : Fin 3 → Set S) (H : Fin 3 → Hypergraph α β)
    (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
    GM06.IsClosedDiscSpace S → G.IsGraph →
    PresentationHasDepthLe G Γ Γ_sub ιV ιE 3 F_star H μ q →
    IsExhaustiveLinkage G Γ_sub 3 H L → IsPLinkage G L p →
    (sigmaJumps Γ Γ_sub ιV).encard ≤ lam :=
  GM21.theorem_6_6_proof p q hq

open GraphMinor.Surface GraphMinor.GM21.Cuts in
/-- **Graph Minors XXI, (6.7)** (page 27 of the preprint): "*For all integers $p, r \ge 0$
and $q \ge 1$ there exists $\lambda \ge 0$ such that, if $G$ has a presentation in a disc
$\Sigma$ of depth $\le q$ and defect $\le r$, and there is an exhaustive vital $p$-linkage in
$G$, then there are at most $\lambda$ $\Sigma$-jumps.*"

Follows the paper's proof by induction on $r$: for $r \le 3$ the result follows from (6.4), (6.5)
and (6.6); for $r \ge 4$, set $\lambda = 2\lambda'$ where $\lambda'$ is from the induction
hypothesis for $(p + 2q, r - 1, q)$, and cut $\Sigma$ along a proper line in a region incident with
three supports (`ThreeSupports.encard_sigmaJumps_le_two_of_region_three`). -/
theorem theorem_6_7 (p r q : ℕ) (hq : 1 ≤ q) :
    ∃ lam : ℕ, ∀ {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v} {r' : ℕ}
    (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α)
    (ιE : Set S → β) (F_star : Fin r' → Set S) (H : Fin r' → Hypergraph α β)
    (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
    r' ≤ r → GM06.IsClosedDiscSpace S → G.IsGraph →
    PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q →
    IsExhaustiveLinkage G Γ_sub r' H L → IsPLinkage G L p →
    (sigmaJumps Γ Γ_sub ιV).encard ≤ lam :=
  GM21.theorem_6_7_proof p r q hq

/-! ## Section 7. Presentations and tree-width -/

open GraphMinor.GM19 hiding Drawing in
open Classical GraphMinor.Surface GraphMinor.Hypergraph GraphMinor.GM10 GraphMinor.GM17 GraphMinor.GM21.Supports in
/-- **Graph Minors XXI, (7.1)** (pages 29–30 of the preprint):
"If $\mathcal{T}$ is a tangle in $G$, and $A \subseteq G$, then the following are equivalent:
(i) $A$ is small with respect to $\mathcal{T}$;
(ii) if $X$ denotes the set of vertices of $A$ incident with edges of $G$ not $A$, then
$|X| < ord(\mathcal{T})$, and $(A, B) \in \mathcal{T}$ where
$V(B) = (V(G) \setminus V(A)) \cup X$ and $E(B) = E(G) \setminus E(A)$;
(iii) there is a separation $(A, B)$ of order $< ord(\mathcal{T})$, and $\mathcal{T}$ contains
every such separation."

Proof: (i) gives (ii) by XVII (4.1)(i); (ii) gives (iii) by XVII (4.1)(i) again; (iii) gives (i)
since some separation $(A, B)$ has order $< ord(\mathcal{T})$, so $|X| < ord(\mathcal{T})$. -/
theorem theorem_7_1 {α : Type u} {β : Type v} {G A : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : GM10.IsTangle G θ 𝒯) (hA : A ≤ G) :
    (IsSmallSubgraph 𝒯 A ↔
      ((GM17.attachments G A).ncard < θ ∧ (A, GM17.complSubhypergraph G A) ∈ 𝒯)) ∧
    (((GM17.attachments G A).ncard < θ ∧ (A, GM17.complSubhypergraph G A) ∈ 𝒯) ↔
      ((∃ B : Hypergraph α β, G.IsSeparation A B ∧ Hypergraph.separationOrder A B < θ) ∧
        ∀ B : Hypergraph α β, G.IsSeparation A B →
          Hypergraph.separationOrder A B < θ → (A, B) ∈ 𝒯)) :=
  GM21.theorem_7_1_proof h𝒯 hA

open GraphMinor.GM19 hiding Drawing in
open Classical GraphMinor.Surface GraphMinor.Hypergraph GraphMinor.GM10 GraphMinor.GM17 GraphMinor.GM21.Supports in
/-- **Graph Minors XXI, (7.2)** (page 30 of the preprint):
"Let $\theta \ge 1$, and let $\Gamma, F_1^*, \dots, F_r^*, H_1, \dots, H_r, \mu$ be a presentation
of a graph $G$ in a surface $\Sigma$, of depth $\le q$, and surrounding a tangle of order
$\ge q\theta$. Then $\Gamma^+$ has a tangle of order $\ge \theta$."

The print fails at `q = 0`, so the Lean assumes `1 ≤ q`. See the correction to (7.2) in
`corrections/GM21.md`. -/
theorem theorem_7_2 {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] {G : Hypergraph α β}
    {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β} {r : ℕ}
    {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β} {μ : BoundaryUnit S → Hypergraph α β}
    {q θ θ_𝒯 : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (hG_graph : G.IsGraph) (hθ : 1 ≤ θ)
    (hq : 1 ≤ q) (h_depth : PresentationHasDepthLe G Γ Γ_sub ιV ιE r F_star H μ q)
    (h𝒯 : GM10.IsTangle G θ_𝒯 𝒯) (hθ_𝒯 : q * θ ≤ θ_𝒯)
    (h_surr : PresentationSurroundsTangle Γ r F_star μ 𝒯) :
    ∃ 𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)),
    GM10.IsTangle (drawingPlusHypergraph Γ h_depth.spaces_finite) θ 𝒯' :=
  GM21.theorem_7_2_proof hG_graph hθ hq h_depth h𝒯 hθ_𝒯 h_surr

open GraphMinor.GM10 GraphMinor.Surface GraphMinor.GM19 in
/-- **Graph Minors XXI, (7.3)** (page 31 of the preprint):
"**7.3** *For every surface $\Sigma$ and all integers $p, r \ge 0$ and $q \ge 1$, there exists
$\theta \ge 1$ such that, if a graph $G$ has a presentation in $\Sigma$ of depth $\le q$, and
defect $\le r$ which surrounds a tangle of order $\ge \theta$, then $G$ has no vital
$p$-linkage.*"

The paper's count of the components of $L \cap \Gamma$ needs a small correction (see the correction
to the proof of (7.3) in `corrections/GM21.md`). The paper gives no reason for the step "it is a
$p$-linkage". The Lean proves that each component of $L$ includes at most one component of
$L \cap G'$, and then counts terminals. -/
theorem theorem_7_3 (S : Type) [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (p r q : ℕ) (hq : 1 ≤ q) :
    ∃ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Hypergraph α β) (Γ : Surface.Drawing S) (Γ_sub : Hypergraph α β)
    (ιV : S → α) (ιE : Set S → β) (r' : ℕ) (F_star : Fin r' → Set S) (H : Fin r' →
      Hypergraph α β) (μ : BoundaryUnit S →
      Hypergraph α β) (θ_G : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)), G.IsGraph → r' ≤ r →
    PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q → θ ≤ θ_G → IsTangle G θ_G 𝒯 →
    PresentationSurroundsTangle Γ r' F_star μ 𝒯 → ¬ HasVitalPLinkage G p :=
  GM21.theorem_7_3_proof S hS p r q hq

/-! ## Section 8. Pseudo-Presentations -/

open GraphMinor.GM19 (cuffPoint) in
open Classical GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (8.1)** (page 32 of the preprint):
"Let $\Gamma, F_1^*, \dots, F_r^*, \mu$ be a disjointed pseudo-presentation of a graph $G$ in a
surface $\Sigma$. Then $\Gamma, F_1^*, \dots, F_r^*, \mu(F_1^*), \dots, \mu(F_r^*), \mu$ is a
presentation of $G$ in $\Sigma$." -/
theorem theorem_8_1 {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] {G : Hypergraph α β}
    {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β} {r : ℕ}
    {F_star : Fin r → Set S} {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (hpp : IsDisjointedPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) :
    IsPresentation G Γ Γ_sub ιV ιE r F_star (fun j => supportGraph G Γ μ (F_star j)) μ q :=
  GM21.theorem_8_1_proof hpp

open GraphMinor.GM19 (cuffPoint) in
open Classical GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (8.2)** (page 34 of the preprint):
"$\Sigma, F_1^*, \dots, F_r^*, \mu'$ is a pseudo-presentation of $G'$."

The print's $\Sigma$ is a misprint for $\Gamma$, and Lean uses $\Gamma$ (see the correction to
(8.2) in `corrections/GM21.md`). -/
theorem theorem_8_2 {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] {G : Hypergraph α β}
    {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β} {r : ℕ}
    {F_star : Fin r → Set S} {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    {C s_star : Set S} {u₁ u₂ : S} {v v₁ v₂ : α}
    (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) (hC : C ∈ cuffs S)
    (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (huncov : ∀ j : Fin r, ¬ s_star ⊆ F_star j)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) (hv₁ : v₁ ∉ G.vertexSet)
    (hv₂ : v₂ ∉ G.vertexSet) (hne : v₁ ≠ v₂) :
    IsPseudoPresentation
    (pseudoSplitGraph hpp hC hs_star hs_star_C hv v₁ v₂)
    Γ Γ_sub ιV ιE r F_star
    (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂) q :=
  GM21.theorem_8_2_proof hpp hC hs_star hs_star_C huncov hv hv₁ hv₂ hne

open GraphMinor.GM19 (cuffPoint) in
open Classical GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (8.3)** (page 36 of the preprint):
"With notation as in (8.2), suppose that $\Gamma, F_1^*, \dots, F_r^*, \mu$ is a
pseudo-presentation of depth $\le q$, and surrounds a tangle $\mathcal{T}$ in $G$ of order
$\theta \ge 2q + 3$. Then $\Gamma, F_1^*, \dots, F_r^*, \mu'$ surrounds a tangle in $G'$ of order
$\theta - 1$." -/
theorem theorem_8_3 {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] {G : Hypergraph α β}
    (hG : G.IsGraph) {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β} {r : ℕ}
    {F_star : Fin r → Set S} {μ : BoundaryUnit S → Hypergraph α β} {q_vec : Fin r → ℕ}
    {C s_star : Set S} {u₁ u₂ : S} {v v₁ v₂ : α} {q θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q_vec) (hq : ∀ j : Fin r, q_vec j ≤ q)
    (hθ : 2 * q + 3 ≤ θ) (h𝒯 : IsTangle G θ 𝒯)
    (hsurr : PseudoPresentationSurroundsTangle Γ r F_star μ 𝒯) (hC : C ∈ cuffs S)
    (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (huncov : ∀ j : Fin r, ¬ s_star ⊆ F_star j)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) (hv₁ : v₁ ∉ G.vertexSet)
    (hv₂ : v₂ ∉ G.vertexSet) (hne : v₁ ≠ v₂) :
    ∃ 𝒯' : Set (Hypergraph α β × Hypergraph α β),
    IsTangle (pseudoSplitGraph hpp hC hs_star hs_star_C hv v₁ v₂) (θ - 1) 𝒯' ∧
    PseudoPresentationSurroundsTangle Γ r F_star
      (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂) 𝒯' :=
  GM21.theorem_8_3_proof hG hpp hq hθ h𝒯 hsurr hC hs_star hs_star_C huncov hv hv₁ hv₂ hne

open GraphMinor.GM19 (cuffPoint) in
open Classical GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM17 in
/-- **Graph Minors XXI, (8.4)** (page 36 of the preprint):
"For every surface $\Sigma$ and all integers $p, r \ge 0$ and $q \ge 1$, there exists
$\theta \ge 1$ such that, if a graph $G$ has a pseudo-presentation in $\Sigma$ of depth $\le q$ and
defect $\le r$ which surrounds a tangle of order $\ge \theta$, then $G$ has no vital
$p$-linkage."

The paper's induction splits vertices by (8.2) and (8.3), and each split takes two new vertices.
The type of vertices may be finite, so the proof moves `G` into `α ⊕ ULift ℕ` by `Sum.inl`, where
new vertices exist (`GM21.theorem_8_4_of_infinite`), and moves the conclusion back. -/
theorem theorem_8_4 (S : Type) [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (p r q : ℕ) (hq : 1 ≤ q) :
    ∃ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph →
      ∀ (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α) (ιE : Set S → β)
        (r' : ℕ) (F_star : Fin r' → Set S)
        (μ : BoundaryUnit S → Hypergraph α β)
        (θ_G : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
        r' ≤ r →
        PseudoPresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star μ q →
        θ ≤ θ_G →
        IsTangle G θ_G 𝒯 →
        PseudoPresentationSurroundsTangle Γ r' F_star μ 𝒯 →
        ¬ HasVitalPLinkage G p :=
  GM21.theorem_8_4_proof S hS p r q hq

/-! ## Section 9. Paintings and portraits -/

open GraphMinor.GM19 (cuffPoint) in
open Metric GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM17 Classical in
/-- **Graph Minors XXI, (9.1)** (page 38 of the preprint):
"**9.1** *If $\Gamma, \alpha$ is a portrait in a surface $\Sigma$ of a graph $G$, and $L$ is a vital
linkage in $G$, then for every cell $c$ of $\Gamma$ which is not a border cell, either
$V(\alpha(c)) \setminus \tilde{c}$ contains a terminal of $L$, or $\alpha(c)$ can be drawn in a
disc with the members of $\tilde{c}$ drawn in the boundary.*" -/
theorem theorem_9_1 {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S] {G L : Hypergraph α β}
    (hG : G.IsGraph) {Γ : GM17.Painting S} {ιN : S → α} {α_cell : Set S → Hypergraph α β}
    {α_vert : S → Hypergraph α β} {q_cuff : Set S → ℕ}
    (hport : IsPortrait G Γ ιN α_cell α_vert q_cuff) (hL : IsVitalLinkage G L) {c : Set S}
    (hc : IsInternalCell Γ c) :
    (((α_cell c).vertexSet \ (ιN '' tilde c)) ∩ terminals L).Nonempty ∨
    CanBeDrawnInDiscWithBoundary (α_cell c) (ιN '' tilde c) :=
  GM21.theorem_9_1_proof hG hport hL hc

open GraphMinor.GM19 (cuffPoint) in
open Metric GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM17 Classical in
/-- **Graph Minors XXI, (9.2)** (page 38 of the preprint):
"**9.2** *For every surface $\Sigma$, and all integers $p \ge 0$ and $q \ge 1$, there exists
$\theta \ge 1$ such that, if a graph $G$ has a portrait in $\Sigma$ of depth $\le q$ which
surrounds a tangle of order $\ge \theta$, then $G$ has no vital $p$-linkage.*"

The proof corrects its last step. See the correction to the proof of (9.2) in `corrections/GM21.md`.
-/
theorem theorem_9_2 (S : Type) [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S) (p q : ℕ)
    (hq : 1 ≤ q) :
    ∃ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph →
      ∀ (Γ : GM17.Painting S) (ιN : S → α)
        (α_cell : Set S → Hypergraph α β) (α_vert : S → Hypergraph α β)
        (θ_G : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
        PortraitHasDepthLe G Γ ιN α_cell α_vert q →
        θ ≤ θ_G →
        IsTangle G θ_G 𝒯 →
        PortraitSurroundsTangle Γ α_cell 𝒯 →
        ¬ HasVitalPLinkage G p :=
  GM21.theorem_9_2_proof S hS p q hq

/-! ## Section 10. The main proof -/

open GraphMinor.Surface GraphMinor.GM10 in
/-- **Graph Minors XXI, (10.1)** (page 41 of the preprint):
"**10.1** *For every integer* $n \ge 0$ *there exist* $\rho, \xi \ge 0, q \ge 1$ *and* $\theta >
\xi$
*such that, if a graph* $G$ *has no* $K_n$*-minor, and* $\mathcal{T}$ *is a tangle in* $G$ *of
order*
$\ge \theta$, *then there exists a surface* $\Sigma$ *such that* $c(\Sigma) \le \rho$ *and* $K_n$
*cannot be drawn in* $\Sigma$, *and there exists* $Z \subseteq V(G)$ *with* $|Z| \le \xi$ *such that
there is a portrait of* $G \setminus Z$ *in* $\Sigma$ *with depth* $\le q$, *surrounding*
$\mathcal{T} \setminus Z$." -/
theorem theorem_10_1 (n : ℕ) :
    ∃ (ρ ξ q θ : ℕ),
    1 ≤ q ∧ ξ < θ ∧
    ∀ {α : Type u} {β : Type v} (G : Hypergraph α β) (θ_G : ℕ)
      (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      G.IsGraph →
      ¬ HasCliqueMinor G n →
      θ ≤ θ_G →
      IsTangle G θ_G 𝒯 →
      ∃ (S : Type) (_ : TopologicalSpace S),
        IsSurface S ∧
        ConnectedSpace S ∧
        (cuffs S).ncard ≤ ρ ∧
        ¬ GM17.CanBeDrawn S (completeHypergraph n) ∧
        ∃ (Z : Set α) (Γ : GM17.Painting S) (ιN : S → α)
          (α_cell : Set S → Hypergraph α β) (α_vert : S → Hypergraph α β),
          Z ⊆ G.vertexSet ∧
          Z.ncard ≤ ξ ∧
          PortraitHasDepthLe21 (G.deleteVertices Z) Γ ιN α_cell α_vert q ∧
          PortraitSurroundsTangle21 Γ α_cell (deleteVerticesTangle G Z 𝒯 θ_G) :=
  GM21.theorem_10_1_proof n

open GraphMinor.Surface GraphMinor.GM10 in
/-- **Graph Minors XXI, (10.2)** (page 42 of the preprint):
"**10.2** *For all integers* $n, p \ge 0$ *there exists* $\theta \ge 1$ *such that, if a graph* $G$
*has a tangle of order* $\ge \theta$ *and has no* $K_n$*-minor then* $G$ *has no vital*
$p$*-linkage.*" -/
theorem theorem_10_2 (n p : ℕ) :
    ∃ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v}
      (G : Hypergraph α β) (θ_G : ℕ)
      (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      G.IsGraph →
      ¬ HasCliqueMinor G n →
      θ ≤ θ_G →
      IsTangle G θ_G 𝒯 →
      ¬ HasVitalPLinkage G p :=
  GM21.theorem_10_2_proof n p

open GraphMinor.Surface GraphMinor.GM10 in
/-- **Graph Minors XXI, (10.3)** (page 42 of the preprint):
"**10.3** *For every integer* $p \ge 0$, *no graph with a* $K_n$*-minor has a vital* $p$*-linkage,
where* $n = \lfloor\frac{5}{2}p\rfloor + 1$." -/
theorem theorem_10_3 (p : ℕ) {α : Type u} {β : Type v} (G : Hypergraph α β) (hG : G.IsGraph)
    (hKn : HasCliqueMinor G ((5 * p) / 2 + 1)) :
    ¬ HasVitalPLinkage G p :=
  GM21.theorem_10_3_proof p G hG hKn

open GraphMinor.Surface GraphMinor.GM10 in
/-- **Graph Minors XXI, (10.4)** (page 42 of the preprint):
"**10.4** *For every integer* $p \ge 0$ *there exists* $\theta \ge 1$ *such that, if a graph* $G$
*has a tangle of order* $\ge \theta$ *then* $G$ *has no vital* $p$*-linkage.*" -/
theorem theorem_10_4 (p : ℕ) :
    ∃ θ : ℕ, 1 ≤ θ ∧
    ∀ {α : Type u} {β : Type v}
      (G : Hypergraph α β) (θ_G : ℕ)
      (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      G.IsGraph →
      θ ≤ θ_G →
      IsTangle G θ_G 𝒯 →
      ¬ HasVitalPLinkage G p :=
  GM21.theorem_10_4_proof p

/-! ## Section 11. Intertwinings -/

/-- **Graph Minors XXI, (11.1)** (Section 11, page 43 of the preprint):
"**11.1** *For every integer $p \ge 0$ there exists $r(p)$ such that every intertwining of two
$p$-linkages has rank $\le r(p)$.*"

Proof: the paper's induction on $|V(G)| + |E(G)|$, deleting an isolated vertex or contracting an
edge until both linkages are vital; then (1.1), (2.7), (11.2) and (11.3) bound $|E(G)|$. The Lean
proof fills two gaps. Claim (4) needs $(T, W)$ to have as few vertices as possible (see the
correction to the proof of (11.1) in `corrections/GM21.md`). In steps (2) and (3), the paper gives
no reason why $G/e$ is an intertwining, and the Lean proves it by lifting each linkage of $G/e$ to a
linkage of $G$ (`GM21.exists_lift`). -/
theorem theorem_11_1 (p : ℕ) :
    ∃ r : ℕ, ∀ {α : Type u} {β : Type v} (G L₁ L₂ : Hypergraph α β), G.IsGraph →
      IsPLinkage G L₁ p → IsPLinkage G L₂ p → IsIntertwining G L₁ L₂ → graphRank G ≤ r :=
  GM21.theorem_11_1_proof p

/-- **Graph Minors XXI, (11.2)** (Section 11, page 43 of the preprint):
"**11.2** *Let $G$ be a graph of tree-width $\le w$. Then there is a linked tree-decomposition
$(T, W)$ of $G$, with width $\le w$, such that every vertex of $T$ has degree $\le 3$.*"

The Lean proof starts from a linked tree-decomposition in which no edge is in two bags. See the
correction to the proof of (11.2) in `corrections/GM21.md`. -/
theorem theorem_11_2 {α : Type u} {β : Type v} {G : Hypergraph α β} (hG : G.IsGraph) {w : ℕ}
    (hw : TreeWidthLE21 G w) :
    ∃ (κ : Type) (_ : Fintype κ) (T : SimpleGraph κ) (W : κ → Hypergraph α β),
      IsTreeDecomp21 G T W ∧ IsLinkedTreeDecomp G T W ∧
        (∀ t, (W t).vertexSet.ncard ≤ w + 1) ∧ ∀ t, (T.neighborSet t).ncard ≤ 3 :=
  GM21.theorem_11_2_proof hG hw

/-- **Graph Minors XXI, (11.3)** (Section 11, page 44 of the preprint):
"**11.3** *Let $(T, W)$ be a tree-decomposition of $G$, and let $e_1, e_2 \in E(T)$ be distinct.
Let $T_0, T_1, T_2$ be the three components of $T \setminus e_1, e_2$, where $e_i$ has an end in
$V(T_0)$ and in $V(T_i)$ ($i = 1, 2$). Suppose that $W(T_0) \subseteq W(T_1) \cap W(T_2)$. Let $T'$
be the tree obtained from $T_1 \cup T_2$ by adding an edge joining the end of $e_1$ in $T_1$ to the
end of $e_2$ in $T_2$; and let $W'$ be the restriction of $W$ to $V(T')$. Then $(T', W')$ is a
tree-decomposition of $G$, and if $(T, W)$ is linked then so is $(T', W')$.*"

Here `e₁ = a₁c₁` and `e₂ = c₂a₂`, and `T₀, T₁, T₂` are the components of `c₁, a₁, a₂` in
`T \ e₁, e₂`. The tree `T'` is `joinTree T a₁ c₁ c₂ a₂`, on the vertex set `V(T₁) ∪ V(T₂)`. -/
theorem theorem_11_3 {α : Type u} {β : Type v} {ι : Type w} [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {W : ι → Hypergraph α β} (h : IsTreeDecomp21 G T W) {a₁ c₁ c₂ a₂ : ι}
    (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
    (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)
    (hsub : bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable c₁) ≤
      bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁) ∩
        bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂)) :
    IsTreeDecomp21 G (joinTree T a₁ c₁ c₂ a₂) (fun x ↦ W x.1) ∧
      (IsLinkedTreeDecomp G T W →
        IsLinkedTreeDecomp G (joinTree T a₁ c₁ c₂ a₂) (fun x ↦ W x.1)) :=
  GM21.theorem_11_3_proof h he₁ he₂ hne h0 hsub

/-! ## Section 12. Path-Width -/

/-- **Graph Minors XXI, (12.1)** (Section 12, page 47 of the preprint):
"**12.1** *Let $(A, B), (A', B')$ be separations of a graph, both of order $k$ and with
$A \subseteq A'$ and $B' \subseteq B$. Suppose that in $B \cap A'$ there is a unique set of $k$
mutually vertex-disjoint paths between $V(A \cap B)$ and $V(A' \cap B')$, and every vertex of
$B \cap A'$ belongs to one of these paths. Then there is a path-decomposition $(P, W)$ of $G$ where
$|V(P)| \ge 2$ with the following properties:*

*(i) $P$ has ends $s, s'$ where $W(s) = A, W(P \setminus s) = B, W(P \setminus s') = A'$ and
$W(s') = B'$*

*(ii) $|W(e)| = k$ for every edge $e$ of $P$*

*(iii) for each $t \in V(P)$ with $t \ne s, s'$, $|E(W(t))| = 1$ and if $e, e'$ are the two edges
of $P$ incident with $t$, then either*

*(a) $W(e) = W(e') = V(W(t))$, or*

*(b) $W(e) \cap W(e') = X$ say where $|X| = k - 1$, and the unique edge of $W(t)$ has ends
$v, v'$ say, where $W(e) = X \cup \{v\}$ and $W(e') = X \cup \{v'\}$.*"

The path `P` is `pathGraph (m + 2)`, with ends `s = 0` and `s' = m + 1`. For the edge `e = tu` of
`P`, `W(e)` is `treeEdgeSet (pathGraph (m + 2)) W t u`.

Proof: the paper's induction on $|E(B \cap A')|$. Steps (1) and (2) move one edge from `B` to
`A` and give the first bag after `A`; steps (3) and (4) show that otherwise `B ∩ A'` has no edges,
and then `(A, B) = (A', B')`. -/
theorem theorem_12_1 {α : Type u} {β : Type v} {G : Hypergraph α β} (hG : G.IsGraph) {k : ℕ}
    {A B A' B' : Hypergraph α β} (hs : G.IsSeparation A B) (hs' : G.IsSeparation A' B')
    (hk : separationOrder A B = k) (hk' : separationOrder A' B' = k) (hAA' : A ≤ A')
    (hBB' : B' ≤ B)
    (hU : ∃ M, IsPathSystem (B ∩ A') (A ∩ B).vertexSet (A' ∩ B').vertexSet k M ∧
      (∀ M', IsPathSystem (B ∩ A') (A ∩ B).vertexSet (A' ∩ B').vertexSet k M' → M' = M) ∧
      M.vertexSet = (B ∩ A').vertexSet) :
    ∃ (m : ℕ) (W : Fin (m + 2) → Hypergraph α β),
      IsTreeDecomp21 G (SimpleGraph.pathGraph (m + 2)) W ∧
      -- (i)
      (W 0 = A ∧ bagUnion W (· ≠ 0) = B ∧ bagUnion W (· ≠ Fin.last (m + 1)) = A' ∧
        W (Fin.last (m + 1)) = B') ∧
      -- (ii)
      (∀ t u, (SimpleGraph.pathGraph (m + 2)).Adj t u →
        (treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W t u).ncard = k) ∧
      -- (iii)
      ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∃ g, (W t).edgeSet = {g} ∧
        ∀ u u', (SimpleGraph.pathGraph (m + 2)).Adj t u →
          (SimpleGraph.pathGraph (m + 2)).Adj t u' → u ≠ u' →
          (treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W t u = (W t).vertexSet ∧
            treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W t u' = (W t).vertexSet) ∨
          ∃ X : Set α, ∃ v v' : α,
            treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W t u ∩
              treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W t u' = X ∧
            X.ncard = k - 1 ∧ (W t).ends g = {v, v'} ∧
            treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W t u = insert v X ∧
            treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W t u' = insert v' X :=
  GM21.theorem_12_1_proof hG hs hs' hk hk' hAA' hBB' hU

/-- **Graph Minors XXI, (12.2)** (Section 12, page 49 of the preprint):
"**12.2** *Let $(T, W)$ be a linked tree-decomposition of a graph $G$, with width $\le w$. Let
$f_1, f_2 \in E(T)$ be distinct, and let $T_1, T_2, T_0$ be the three components of
$T \setminus \{f_1, f_2\}$ where $f_i$ has ends in $T_i$ and $T_0$ $(i = 1, 2)$. Let
$|W(f_1)| = |W(f_2)| = k$, and let $(P, W')$ be a path-decomposition of $G$ satisfying statements
(i)–(iii) of (12.1), with $W, A, B, A', B'$ replaced by
$W', W(T_1), W(T_0) \cup W(T_2), W(T_0) \cup W(T_1), W(T_2)$. Let $P$ have ends $s_1, s_2$, where
$s_i$ is the end of $f_i$ in $V(T_i)$ $(i = 1, 2)$, and otherwise let $P$ be disjoint from $T$. Let
$T^*$ be the tree $T_1 \cup T_2 \cup P$, and define $W^*(t) = W(t)$ if $t \in V(T_1) \cup V(T_2)$
and $W^*(t) = W'(t)$ if $t \in V(P) \setminus \{s, s'\}$. Then $(T^*, W^*)$ is a linked
tree-decomposition of $G$, with width $\le w$.*"

The edges are `f₁ = a₁c₁` and `f₂ = c₂a₂`. The three components of `T \ {f₁, f₂}` are those of
`a₁`, `a₂` and `c₁` in `cutTwo T a₁ c₁ c₂ a₂`, and `h0` says that `c₁` and `c₂` are in the same one,
`T₀`. So `W(T₀) ∪ W(T₂)` is the union of the bags not joined to `a₁`. The path `P` is
`pathGraph (m + 2)` with ends `s₁ = 0` and `s₂ = m + 1`, whose bags are `W'`; (i)–(iii) are written as
in `theorem_12_1`. The tree `T*` is `spliceTree T a₁ c₁ c₂ a₂ m`: its vertices are those of `T₁`
and `T₂` (`joinSet`) and the `m` inner vertices of `P`, with `s₁ = a₁` and `s₂ = a₂`. Its bags are
`spliceBag T a₁ c₁ c₂ a₂ m W W'`. "$V(P) \setminus \{s, s'\}$" is read as
"$V(P) \setminus \{s_1, s_2\}$".

The printed statement is false: the width can be $w + 1$ (see the correction to (12.2) in
`corrections/GM21.md`). We add
hypothesis `hiv`: every vertex of an inner bag `W'(t)` is in `W'(e)` for an edge `e` of `P` at `t`.
The path-decomposition that (12.1) builds has this property.

Proof: the paper's. The tree-decomposition is checked bag by bag. Claim (1) goes along `P` one bag
at a time, claim (2) follows from it, claim (3) (the width) uses (2), and linkedness is the paper's
case analysis, pairing paths through the separation at `f₁` or `f₂`. -/
theorem theorem_12_2 {α : Type u} {β : Type v} {ι : Type*} [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {W : ι → Hypergraph α β} (h : IsTreeDecomp21 G T W)
    (hL : IsLinkedTreeDecomp G T W) {w : ℕ} (hw : ∀ t, (W t).vertexSet.ncard ≤ w + 1)
    {a₁ c₁ c₂ a₂ : ι} (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
    (h0 : (GM21.cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂) {k : ℕ}
    (_hk₁ : (treeEdgeSet T W a₁ c₁).ncard = k) (_hk₂ : (treeEdgeSet T W c₂ a₂).ncard = k)
    {m : ℕ} {W' : Fin (m + 2) → Hypergraph α β}
    (hP : IsTreeDecomp21 G (SimpleGraph.pathGraph (m + 2)) W')
    -- (i)
    (hA : W' 0 = bagUnion W ((GM21.cutTwo T a₁ c₁ c₂ a₂).Reachable a₁))
    (hB : bagUnion W' (· ≠ 0) =
      bagUnion W (fun t ↦ ¬ (GM21.cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t))
    (hA' : bagUnion W' (· ≠ Fin.last (m + 1)) =
      bagUnion W (fun t ↦ ¬ (GM21.cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t))
    (hB' : W' (Fin.last (m + 1)) = bagUnion W ((GM21.cutTwo T a₁ c₁ c₂ a₂).Reachable a₂))
    -- (ii)
    (hii : ∀ t u, (SimpleGraph.pathGraph (m + 2)).Adj t u →
      (treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W' t u).ncard = k)
    -- (iii)
    (hiii : ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∃ g, (W' t).edgeSet = {g} ∧
      ∀ u u', (SimpleGraph.pathGraph (m + 2)).Adj t u →
        (SimpleGraph.pathGraph (m + 2)).Adj t u' → u ≠ u' →
        (treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W' t u = (W' t).vertexSet ∧
          treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W' t u' = (W' t).vertexSet) ∨
        ∃ X : Set α, ∃ v v' : α,
          treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W' t u ∩
            treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W' t u' = X ∧
          X.ncard = k - 1 ∧ (W' t).ends g = {v, v'} ∧
          treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W' t u = insert v X ∧
          treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W' t u' = insert v' X)
    -- added: see the correction to (12.2) in `corrections/GM21.md`
    (hiv : ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∀ y ∈ (W' t).vertexSet,
      ∃ u, (SimpleGraph.pathGraph (m + 2)).Adj t u ∧
        y ∈ treeEdgeSet (SimpleGraph.pathGraph (m + 2)) W' t u) :
    IsTreeDecomp21 G (GM21.spliceTree T a₁ c₁ c₂ a₂ m) (GM21.spliceBag T a₁ c₁ c₂ a₂ m W W') ∧
      IsLinkedTreeDecomp G (GM21.spliceTree T a₁ c₁ c₂ a₂ m)
        (GM21.spliceBag T a₁ c₁ c₂ a₂ m W W') ∧
      ∀ t, (GM21.spliceBag T a₁ c₁ c₂ a₂ m W W' t).vertexSet.ncard ≤ w + 1 :=
  GM21.theorem_12_2_proof h hL hw he₁ he₂ hne h0 hP hA hB hA' hB' hii hiii hiv

/-- **Graph Minors XXI, (12.3)** (Section 12, page 50 of the preprint):
"**12.3** *For every integer $p \ge 0$ there exists $w \ge 0$ such that every graph with a vital
$p$-linkage has path-width $\le w$.*"

Proof: the paper's. By (1.1) and (11.2) there is a linked tree-decomposition of width `≤ w'` with
maximum degree `≤ 3`; choose one with the fewest vertices of degree `3`. Claim (1) uses (12.1) and
(12.2) to show that a part of `G` between two edges of `T` that carries a unique set of disjoint
paths holds no such vertex. Claim (2) uses (2.6) and claim (1) to show that every path of `T` has
at most `n` of them. So there are at most `2 ^ n` of them, and step (3) gives a
path-decomposition from the paths between them. Here `w = w' + 2 ^ n (w' + 1)`, the second of the
two values in the paper. See the corrections to the proof of (12.3) in `corrections/GM21.md`. The
paper gives no argument for the bound `2 ^ n`, and the Lean proves it (`GM21.ncard_branchSet_le`).
-/
theorem theorem_12_3 (p : ℕ) :
    ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph →
      HasVitalPLinkage G p → PathWidthLE21 G w :=
  GM21.theorem_12_3_proof p

/-- **Graph Minors XXI, (12.4)** (Section 12, page 52 of the preprint):
"**12.4** *For every integer $p \ge 0$ there exists $p' \ge 0$ such that every graph with a vital
$p$-linkage is a $p'$-chain.*"

Proof: the paper's sketch, written out on the linked tree-decompositions of (11.2) instead of
linked path-decompositions. A vertex of `T` is good if it has two neighbours and its bag looks like
an inner bag of (12.1). Among the decompositions of width `≤ w'` and maximum degree `≤ 3`, choose
one with the fewest bad vertices. As in (12.3), the splice of (12.2) shows that a part with a unique
set of disjoint paths holds no bad vertex, so there are at most `3 · 2 ^ n` bad vertices. Each run
of good vertices between them gives a `(w' + 1)`-chain by the converse of (12.1), and the pieces
are joined into one chain. See the corrections to the converse of (12.1), to the definition of a
$p$-chain and to the proof of (12.4) in `corrections/GM21.md`. -/
theorem theorem_12_4 (p : ℕ) :
    ∃ p' : ℕ, ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph →
      HasVitalPLinkage G p → IsChain G p' :=
  GM21.theorem_12_4_proof p

end GraphMinor.GM21
