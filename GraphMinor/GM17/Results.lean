module

public import GraphMinor.GM17.Basic
public import GraphMinor.GM17.Section10Proved
public import GraphMinor.GM17.Section11Proved
public import GraphMinor.GM17.Section12
public import GraphMinor.GM17.Section12b
public import GraphMinor.GM17.Section12c
public import GraphMinor.GM17.Section12d
public import GraphMinor.GM17.Section13Proved
public import GraphMinor.GM17.Section13a
public import GraphMinor.GM17.Section13b
public import GraphMinor.GM17.Section13c
public import GraphMinor.GM17.Section13d
public import GraphMinor.GM17.Section14
public import GraphMinor.GM17.Section14b
public import GraphMinor.GM17.Section2
public import GraphMinor.GM17.Section4
public import GraphMinor.GM17.Section5
public import GraphMinor.GM17.Section5Proved
public import GraphMinor.GM17.Section6
public import GraphMinor.GM17.Section6Proved
public import GraphMinor.GM17.Section7
public import GraphMinor.GM17.Section7Proved
public import GraphMinor.GM17.Section8Proved
public import GraphMinor.GM17.Section9Proved
public import GraphMinor.GM17.Section9b
public import GraphMinor.GM17.Section9bProved

/-!
# Graph Minors XVII: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XVII. Taming a vortex*, J. Combin. Theory Ser. B
**77** (1999), 162–210.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. The docstrings say where the Lean differs from the print, and
`corrections/GM17.md` lists the corrections to the paper.
-/

public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

universe u v u' v'

/-! ## Section 1. Introduction -/

open scoped Convex in
open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (1.1)** (page 163): "(i) For every non-null connected surface $\Sigma$
there are integers $a$, $b$, $c$ such that $\Sigma \simeq \Sigma(a, b, c)$; (ii) $\Sigma(a, b, c)
\simeq \Sigma(a', b', c')$ if and only if $c = c'$, $a + 2b = a' + 2b'$, and both or neither of $b$,
$b'$ are zero."

Combined statement of (1.1)(i) and (1.1)(ii).

Clause (ii) is stated with `2a + b = 2a' + b'`, as the paper means. See the correction to (1.1)(ii)
in `corrections/GM17.md`. -/
theorem theorem_1_1 :
    (∀ (S : Type u) [TopologicalSpace S], IsSurface S → ConnectedSpace S →
      ∃ a b c : ℕ, Nonempty (S ≃ₜ SurfaceModel a b c)) ∧
    (∀ a b c a' b' c' : ℕ,
      Nonempty (SurfaceModel a b c ≃ₜ SurfaceModel a' b' c') ↔
        c = c' ∧ 2 * a + b = 2 * a' + b' ∧ (b = 0 ↔ b' = 0)) :=
  GM17.theorem_1_1_proof

/-! ## Section 2. Hypergraphs and Their Portrayal -/

open Function Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (2.1)** (page 166): "Given a portrayal $\pi = (\Sigma, \Gamma, \alpha,
\beta, \gamma)$ of $G$, let $(I_1, I_2)$ be a partition of $C(\Gamma)$. For $i = 1, 2$, let $A_i =
\bigcup (\alpha(c) : c \in I_i)$. Then $E(A_1 \cap A_2) = \emptyset$, and $V(A_1 \cap A_2) = \bigcup
(\gamma(\tilde{c}_1) \cap \gamma(\tilde{c}_2) : c_1 \in I_1, c_2 \in I_2) \cup \bigcup (\beta(n) :
\text{there exist border cells } c_1 \in I_1 \text{ and } c_2 \in I_2 \text{ with } n \in
\tilde{c}_1 \cap \tilde{c}_2)$."

Given a portrayal $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ of $G$, let $(I_1, I_2)$ be a
partition of $C(\Gamma)$, and let $A_i = \bigcup (\alpha(c) : c \in I_i)$ for $i = 1, 2$. Then
$E(A_1 \cap A_2) = \emptyset$, and
$$V(A_1 \cap A_2) = \bigcup (\gamma(\tilde{c}_1) \cap \gamma(\tilde{c}_2) : c_1 \in I_1, c_2 \in
I_2)
  \cup \bigcup (\beta(n) : \exists \text{ border cells } c_1 \in I_1, c_2 \in I_2 \text{ with }
  n \in \tilde{c}_1 \cap \tilde{c}_2).$$ -/
theorem theorem_2_1 {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    {I₁ I₂ : Set (Set π.S)} (hcov : I₁ ∪ I₂ = π.Γ.C) (hdisj : Disjoint I₁ I₂) :
    (π.cellsUnion I₁ ∩ π.cellsUnion I₂).edgeSet = ∅ ∧
    (π.cellsUnion I₁ ∩ π.cellsUnion I₂).vertexSet =
      (⋃ c₁ ∈ I₁, ⋃ c₂ ∈ I₂, π.gammaImage (tilde c₁) ∩ π.gammaImage (tilde c₂)) ∪
      (⋃ n ∈ {n : π.S | ∃ c₁ ∈ I₁, (c₁ ∩ bd π.S).Nonempty ∧
        ∃ c₂ ∈ I₂, (c₂ ∩ bd π.S).Nonempty ∧ n ∈ tilde c₁ ∩ tilde c₂}, π.borderSet n) :=
  GM17.theorem_2_1_proof π hcov hdisj

/-! ## Section 3. Warp of a Portrayal -/

/-! ## Section 4. Tangles -/

open Function Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (4.1)** (page 169): "(i) If $A \subseteq G$ is small then $(A, B) \in
\mathscr{T}$ for every $B \subseteq G$ such that $(A, B)$ is a separation of $G$ of order $<
ord(\mathscr{T})$. (ii) If $A_1, A_2 \subseteq G$ are small and $A \subseteq A_1 \cup A_2$ has $<
ord(\mathscr{T})$ attachments in $G$ then $A$ is small."

(i) If $A \subseteq G$ is small then $(A, B) \in \mathcal{T}$ for every $B \subseteq G$ such that
$(A, B)$ is a separation of $G$ of order $< \operatorname{ord}(\mathcal{T})$.
(ii) If $A_1, A_2 \subseteq G$ are small and $A \subseteq A_1 \cup A_2$ has
$< \operatorname{ord}(\mathcal{T})$ attachments in $G$ then $A$ is small. -/
theorem theorem_4_1 {α : Type u} {β : Type v} {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    (∀ A B, IsSmallWrt 𝒯 A → G.IsSeparation A B → separationOrder A B < θ → (A, B) ∈ 𝒯) ∧
    (∀ A A₁ A₂, IsSmallWrt 𝒯 A₁ → IsSmallWrt 𝒯 A₂ → A ≤ A₁ ∪ A₂ →
      (attachments G A).ncard < θ → IsSmallWrt 𝒯 A) :=
  GM17.theorem_4_1_proof h𝒯

open Function Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (4.2)** (page 169): "If $\mathscr{T}$ is a tangle in a hypergraph $G$, and
$Z \subseteq V(G)$ with $|Z| < ord(\mathscr{T})$, then $\mathscr{T}/Z$ is a tangle in $G/Z$ of order
$ord(\mathscr{T}) - |Z|$."

If $\mathcal{T}$ is a tangle in a hypergraph $G$, and $Z \subseteq V(G)$ with
$|Z| < \operatorname{ord}(\mathcal{T})$, then $\mathcal{T} / Z$ is a tangle in $G / Z$ of order
$\operatorname{ord}(\mathcal{T}) - |Z|$.
(Proved in Graph Minors X, Theorem (6.2).) -/
theorem theorem_4_2 {α : Type u} {β : Type v} {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) {Z : Set α}
    (hZ : Z ⊆ G.vertexSet) (hZ_lt : Z.ncard < θ) :
    IsTangle (quotientVertices G Z) (θ - Z.ncard) (quotientTangle G 𝒯 Z) :=
  GM17.theorem_4_2_proof h𝒯 hZ hZ_lt

open Function Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (4.3)** (pages 169–170): "Let $\pi = (\Sigma, \Gamma, \alpha, \beta,
\gamma)$ be a $\mathscr{T}$-central portrayal of a hypergraph $G$, with warp $\le p$, and let
$\mathscr{T}$ have order $\theta$. There is no small subhypergraph $A \subseteq G$ with $< \theta -
2p$ attachments, such that $\gamma(n) \in V(A)$ for all $n \in dom(\gamma)$."

Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $\mathcal{T}$-central portrayal of a
hypergraph $G$, with $\operatorname{warp} \le p$, and let $\mathcal{T}$ have order $\theta$.
There is no small subhypergraph $A \subseteq G$ with $< \theta - 2p$ attachments, such that
$\gamma(n) \in V(A)$ for all $n \in \operatorname{dom}(\gamma)$. -/
theorem theorem_4_3 {α : Type u} {β : Type v} {G : Hypergraph α β} {θ p : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (hcentral : π.IsCentral 𝒯) (hwarp : π.warp ≤ p) :
    ¬ ∃ A : Hypergraph α β,
    IsSmallWrt 𝒯 A ∧
    (attachments G A).ncard < θ - 2 * p ∧
    (∀ n ∈ π.domγ, π.nodeVertex n ∈ A.vertexSet) :=
  GM17.theorem_4_3_proof h𝒯 π hcentral hwarp

/-! ## Section 5. Simplifying a Portrayal -/

open Metric GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (5.1)** (page 171):
"If $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ is a 0-redundant $\mathscr{T}$-central
portrayal of a hypergraph $G$, then for each cuff $\Theta$ of $\Sigma$, $\pi$ has warp $\ge
1$ at $\Theta$."

The warp of a portrayal is at least 1, which the proof needs. See the correction to (5.1) in
`corrections/GM17.md`. -/
theorem theorem_5_1 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (π : Portrayal G) [CompactSpace π.S] [T2Space π.S]
    (hT : π.IsCentral 𝒯) (hred : π.IsZeroRedundant 𝒯) {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) :
    1 ≤ π.warpAt Θ :=
  GM17.theorem_5_1_proof π hT hred hΘ

open Metric GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (5.2)** (page 171):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a hypergraph $G$. Let $c \in C(\Gamma)$ be
internal, and let $n \in \tilde{c} - \operatorname{dom}(\gamma)$. Let $\Gamma'$ be obtained by
shrinking $c$ from $n$; and let $\alpha'$ be defined by $\alpha'(c') = \alpha(c)$, where $c'$ is
the shrunken $c$, and otherwise $\alpha' = \alpha$. Then $\pi' = (\Sigma, \Gamma', \alpha', \beta,
\gamma)$ is a portrayal of $G$." (The paper omits "portrayal of a" before "hypergraph $G$".)

Moreover, if $\pi$ is $\mathcal{T}$-central, then $\pi'$ is $\mathcal{T}$-central, resembles $\pi$,
and is truer than $\pi$ (holding more generally whenever
$n \in \operatorname{dom}(\gamma) \implies \gamma(n) \notin V(\alpha(c))$). -/
theorem theorem_5_2 {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G) [T2Space π.S]
    {c₀ : Set π.S} (hc₀ : π.Γ.IsInternalCell c₀) {n : π.S} (hn : n ∈ tilde c₀)
    (hn_γ : n ∈ π.domγ → π.nodeVertex n ∉ (π.cellGraph c₀).vertexSet) :
    ∃ (Δ : Set π.S) (Γ' : Painting π.S) (hsh : π.Γ.IsShrunkenFrom Γ' c₀ n Δ),
    let π' := π.shrinkCell Γ' c₀ n Δ hsh hn_γ
    (∀ 𝒯, π.IsCentral 𝒯 → π'.IsCentral 𝒯) ∧ π'.Resembles π ∧ π'.IsTruer π :=
  GM17.theorem_5_2_proof π hc₀ hn hn_γ

open Metric GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (5.3)** (page 172):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a 0-redundant $\mathscr{T}$-central
portrayal of a hypergraph $G$. Let $F$ be a $\Gamma$-normal I-arc with ends $n_1, n_2$ such
that $\beta(n_1) = \beta(n_2) = F \cap \operatorname{dom}(\gamma) = \emptyset$. Then there
is a disc $\Delta \subseteq \Sigma$ with $F \subseteq \operatorname{bd}(\Delta) \subseteq F
\cup \operatorname{bd}(\Sigma)$ such that $\alpha(\Delta)$ is small." -/
theorem theorem_5_3 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ} (hTangle : IsTangle G θ 𝒯) (hθ : 1 ≤ θ)
    (π : Portrayal G) [CompactSpace π.S] [T2Space π.S] (hT : π.IsCentral 𝒯)
    (hred : π.IsZeroRedundant 𝒯) {F : Set π.S} {n₁ n₂ : π.S} (hnorm : π.Γ.IsNormal F)
    (hF : IsLineWithEnds F n₁ n₂) (hFbd : F ∩ bd π.S = {n₁, n₂}) (hβ₁ : π.borderSet n₁ = ∅)
    (hβ₂ : π.borderSet n₂ = ∅) (hFγ : F ∩ π.domγ = ∅) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧
    IsSmallWrt 𝒯 (π.areaGraph Δ) :=
  GM17.theorem_5_3_proof hTangle hθ π hT hred hnorm hF hFbd hβ₁ hβ₂ hFγ

open Metric GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (5.4)** (page 173):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a 0-redundant $\mathscr{T}$-central
portrayal of a hypergraph $G$. Let $F \subseteq \Sigma$ be a $\Gamma$-normal O-arc with $F
\cap \operatorname{dom}(\gamma) = \emptyset$. Then there is a disc $\Delta \subseteq \Sigma$
with $\operatorname{bd}(\Delta) = F$ such that $\alpha(\Delta)$ is small." -/
theorem theorem_5_4 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ} (hTangle : IsTangle G θ 𝒯) (hθ : 1 ≤ θ)
    (π : Portrayal G) [CompactSpace π.S] [T2Space π.S] (hT : π.IsCentral 𝒯)
    (hred : π.IsZeroRedundant 𝒯) {F : Set π.S} (hnorm : π.Γ.IsNormal F) (hF : IsOArc F)
    (hFγ : F ∩ π.domγ = ∅) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ discBd Δ = F ∧
    IsSmallWrt 𝒯 (π.areaGraph Δ) :=
  GM17.theorem_5_4_proof hTangle hθ π hT hred hnorm hF hFγ

/-! ## Section 6. Redundancy -/

open Function Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (6.1)** (page 174):
"Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$, and let $Z \subseteq
V(G)$ with $|Z| < \theta$. Let $A \subseteq G$ such that $A/Z'$ has fewer than $\theta -
|Z|$ attachments in $G/Z$, where $Z' = Z \cap V(A)$. Then $A$ is small relative to
$\mathscr{T}$ if and only if $A/Z'$ is small relative to $\mathscr{T}/Z$." -/
theorem theorem_6_1 {α : Type u} {β : Type v} {G A : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) {Z : Set α}
    (hZ : Z ⊆ G.vertexSet) (hZ_lt : Z.ncard < θ) (hA : A ≤ G)
    (hatt : (attachments (quotientVertices G Z) (quotientVertices A (Z ∩ A.vertexSet))).ncard <
      θ - Z.ncard) :
    IsSmallWrt 𝒯 A ↔
    IsSmallWrt (quotientTangle G 𝒯 Z) (quotientVertices A (Z ∩ A.vertexSet)) :=
  GM17.theorem_6_1_proof h𝒯 hZ hZ_lt hA hatt

open Function Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (6.2)** (page 174):
"Let $\mathscr{T}$ be a tangle in a hypergraph $G$ and let $\pi = (\Sigma, \Gamma, \alpha, \beta,
\gamma)$ be a $\mathscr{T}$-central portrayal of $G$ with $warp \le p$. Let $Z \subseteq V(G)$,
with $|Z| < ord(\mathscr{T}) - 2p - 2$. Define
$$ \begin{aligned} \alpha'(c) &= \alpha(c)/(Z \cap V(\alpha(c))) && (c \in C(\Gamma)) \\ \beta'(n)
&= \beta(n) - Z && (n \in N(\Gamma) \cap bd(\Sigma)) \\ \gamma' &= \gamma \mid \{n : n \in
dom(\gamma), \gamma(n) \notin Z\}. \end{aligned} $$
Then $\pi' = (\Sigma, \Gamma, \alpha', \beta', \gamma')$ is a $\mathscr{T}/Z$-central portrayal of
$G/Z$, resembling or simpler than $\pi$."

Note: For an internal cell $c \in C(\Gamma)$ the number of attachments of
$\alpha(c)$ is bounded by $|\tilde{c}| \le 3$, which is $\le 2p + 2$ whenever $p \ge 1$ (in
particular for all 0-redundant portrayals by (5.1)), while for $p = 0$ the bound is
$\max(3, 2p + 2) = 3$. -/
theorem theorem_6_2 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (hT : π.IsCentral 𝒯) (hwarp : π.warp ≤ p) {Z : Set α} (hZ : Z ⊆ G.vertexSet)
    (hZ_lt : Z.ncard + max 3 (2 * p + 2) < θ) :
    (π.quotientBy Z).IsCentral (quotientTangle G 𝒯 Z) ∧
    ((π.quotientBy Z).Resembles π ∨ (π.quotientBy Z).IsSimpler π) :=
  GM17.theorem_6_2_proof h𝒯 π hT hwarp hZ hZ_lt

open Function Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (6.3)** (page 174):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $z$-redundant $\mathscr{T}$-central
portrayal of $G$, with $warp \le p$. Let $ord(\mathscr{T}) > z + 2p + 2$, and let $F
\subseteq \Sigma$ be a $\Gamma$-normal $I$-arc with ends $n_1, n_2$ and with $|F \cap
dom(\gamma)| \le z - 2p$. Then there is a disc $\Delta \subseteq \Sigma$ with $F \subseteq
bd(\Delta) \subseteq F \cup bd(\Sigma)$ such that $\alpha(\Delta)$ is small." -/
theorem theorem_6_3 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (hT : π.IsCentral 𝒯) (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hθ : z + max 3 (2 * p + 2) < θ) {F : Set π.S} {n₁ n₂ : π.S} (hnorm : π.Γ.IsNormal F)
    (hF : IsLineWithEnds F n₁ n₂) (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hFγ_le : 2 * p ≤ z ∧ (F ∩ π.domγ).ncard ≤ z - 2 * p) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧
    IsSmallWrt 𝒯 (π.areaGraph Δ) :=
  GM17.theorem_6_3_proof h𝒯 π hT hwarp hred hθ hnorm hF hFbd hFγ_le

open Function Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (6.4)** (page 175):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $z$-redundant $\mathscr{T}$-central
portrayal of $G$, with $warp \le p$. Let $ord(\mathscr{T}) > z + 2p + 2$, and let $F
\subseteq \Sigma$ be a $\Gamma$-normal $O$-arc with $|F \cap dom(\gamma)| \le z$. Then there
is a disc $\Delta \subseteq \Sigma$ with $bd(\Delta) = F$ such that $\alpha(\Delta)$ is
small." -/
theorem theorem_6_4 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (hT : π.IsCentral 𝒯) (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hθ : z + max 3 (2 * p + 2) < θ) {F : Set π.S} (hO : IsOArc F) (hnorm : π.Γ.IsNormal F)
    (hFγ_le : (F ∩ π.domγ).ncard ≤ z) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ discBd Δ = F ∧
    IsSmallWrt 𝒯 (π.areaGraph Δ) :=
  GM17.theorem_6_4_proof h𝒯 π hT hwarp hred hθ hO hnorm hFγ_le

open Function Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (6.5)** (page 175):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $z$-redundant $\mathscr{T}$-central
portrayal of a hypergraph $G$ with $warp \le q$, let $(A, B) \in \mathscr{T}$ have order
$\le z$, let $\Theta$ be a cuff of $\Sigma$, and let $\pi$ have warp $p$ at $\Theta$. Let
$ord(\mathscr{T}) > z + 2q + 2$. Then there exists either* (i) *a node $n$ bordering
$\Theta$ with $|\beta(n)| = p$ and $\beta(n) \cap V(A) = \emptyset$, or* (ii) *a cell $c$
bordering $\Theta$ with ends $n_1, n_2 \in dom(\gamma)$, such that $\gamma(n_1), \gamma(n_2)
\notin V(A)$, there is no path of $(A \cap \alpha(c))^*$ between $\beta(n_1)$ and
$\beta(n_2)$, and* $$|\beta(n_1) - V(A)| = |\beta(n_2) - V(A)| = p - 1 \ge 1.$$" -/
theorem theorem_6_5 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ q p z : ℕ} (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G) (hT : π.IsCentral 𝒯) (hwarp : π.warp ≤ q) (hred : π.IsRedundant 𝒯 θ z)
    (hθ : z + max 3 (2 * q + 2) < θ) {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯)
    (hord : separationOrder A B ≤ z) {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hp : π.warpAt Θ = p) :
    (∃ n ∈ π.Γ.N ∩ Θ, (π.borderSet n).ncard = p ∧ Disjoint (π.borderSet n) A.vertexSet) ∨
    (∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ ∃ n₁ n₂ : π.S, n₁ ≠ n₂ ∧ tilde c = {n₁, n₂} ∧
      n₁ ∈ π.domγ ∧ n₂ ∈ π.domγ ∧
      π.nodeVertex n₁ ∉ A.vertexSet ∧ π.nodeVertex n₂ ∉ A.vertexSet ∧
      (∀ u ∈ (A ∩ π.cellGraph c).vertexSet ∩ π.borderSet n₁,
       ∀ v ∈ (A ∩ π.cellGraph c).vertexSet ∩ π.borderSet n₂,
       IsEmpty ((A ∩ π.cellGraph c).skeleton.Walk u v)) ∧
      (π.borderSet n₁ \ A.vertexSet).ncard = p - 1 ∧
      (π.borderSet n₂ \ A.vertexSet).ncard = p - 1 ∧ 2 ≤ p) :=
  GM17.theorem_6_5_proof h𝒯 π hT hwarp hred hθ hAB hord hΘ hp

open Function Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (6.6)** (page 176):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $z$-redundant $\mathscr{T}$-central
portrayal of $G$ with $warp \le p$ and $ord(\mathscr{T}) > z + 2p + 2$, and let $\Theta$ be
a cuff. There is no $X \subseteq V(G)$ with $|X| \le z/3$ such that $X \cap \beta(n+) \ne
\emptyset$ for every node $n$ bordering $\Theta$." -/
theorem theorem_6_6 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (hT : π.IsCentral 𝒯) (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hθ : z + max 3 (2 * p + 2) < θ) {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) {X : Set α}
    (hX_sub : X ⊆ G.vertexSet) (hX_card : 3 * X.ncard ≤ z) :
    ¬ (∀ n ∈ π.Γ.N ∩ Θ, (X ∩ π.borderPlus n).Nonempty) :=
  GM17.theorem_6_6_proof h𝒯 π hT hwarp hred hθ hΘ hX_sub hX_card

open Function Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (6.7)** (page 177):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $z$-redundant $\mathscr{T}$-central
portrayal of $G$ with $warp \le p$. Let $ord(\mathscr{T}) > z + 2p + 2$, and let $F$ be a
$\Sigma$-normal $I$-arc with ends $n_1, n_2$ and with $|F \cap dom(\gamma)| \le z - 2p - 1$. Let
$\Delta$ be as in (6.3). Then $\beta(n_1 +) \cap \beta(n_2 +) \subseteq \beta(n+)$ for all $n \in
N(\Gamma) \cap \Delta \cap bd(\Sigma)$." (The paper writes "$\Sigma$-normal" for
"$\Gamma$-normal".) -/
theorem theorem_6_7 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (hT : π.IsCentral 𝒯) (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hθ : z + max 3 (2 * p + 2) < θ) {F Δ : Set π.S} {n₁ n₂ : π.S} (hnorm : π.Γ.IsNormal F)
    (hF : IsLineWithEnds F n₁ n₂) (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hFγ_le : 2 * p + 1 ≤ z ∧ (F ∩ π.domγ).ncard ≤ z - 2 * p - 1) (hΔ : IsClosedDisc Δ)
    (hF_bd : F ⊆ discBd Δ) (hbd_sub : discBd Δ ⊆ F ∪ bd π.S) (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ))
    {n' : π.S} (hn' : n' ∈ π.Γ.N ∩ Δ ∩ bd π.S) :
    π.borderPlus n₁ ∩ π.borderPlus n₂ ⊆ π.borderPlus n' :=
  GM17.theorem_6_7_proof h𝒯 π hT hwarp hred hθ hnorm hF hFbd hFγ_le hΔ hF_bd hbd_sub hsmall hn'

/-! ## Section 7. Some Constructions -/

open Function Metric GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (7.1)** (page 178):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $\mathcal{T}$-central portrayal of a
hypergraph $G$. Let $\Delta \subseteq \Sigma$ be a disc with $bd(\Delta)$ $\Gamma$-normal and
$|bd(\Delta) \cap N(\Gamma)| \le 1$, such that $\alpha(\Delta)$ is small. Let $c' \in C(\Gamma)$
with $c' \subseteq \Sigma - \Delta$, chosen with $\tilde{c}' \cap bd(\Delta) \ne \emptyset$ if
possible. If $\tilde{c}' \cap bd(\Delta) \ne \emptyset$, let $\Gamma' = (U(\Gamma) \cap
\overline{\Sigma - \Delta}, N(\Gamma) \cap \overline{\Sigma - \Delta})$. If $\tilde{c}' \cap
bd(\Delta) = \emptyset$, let $\Gamma' = (U(\Gamma) - \Delta, N(\Gamma) - \Delta)$. Define
$$ \begin{aligned} \alpha'(c') &= \alpha(c') \cup \alpha(\Delta) \\ \alpha'(c) &= \alpha(c) \quad (c
\in C(\Gamma') - \{c'\}) \\ \gamma' &= \gamma \mid N(\Gamma'). \end{aligned} $$
Then $\pi' = (\Sigma, \Gamma', \alpha', \beta, \gamma')$ is a $\mathcal{T}$-central portrayal of
$G$ resembling $\pi$." -/
theorem theorem_7_1 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (hcentral : π.IsCentral 𝒯) {Δ : Set π.S} (hΔ : IsClosedDisc Δ)
    (hnorm : discBd Δ ∩ π.Γ.U ⊆ π.Γ.N) (hcard : (discBd Δ ∩ π.Γ.N).ncard ≤ 1)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ)) {c' : Set π.S} (hc' : c' ∈ π.Γ.C)
    (hc'_out : c' ⊆ Set.univ \ Δ)
    (hchoice : (∃ c ∈ π.Γ.C, c ⊆ Set.univ \ Δ ∧ (tilde c ∩ discBd Δ).Nonempty) →
      (tilde c' ∩ discBd Δ).Nonempty) :
    ∃ π' : Portrayal G,
    π'.S = π.S ∧
    π'.IsCentral 𝒯 ∧
    π'.Resembles π ∧
    ((¬ ((Δ \ discBd Δ) ∩ π.Γ.U).Nonempty) ∨ π'.IsTruer π) :=
  GM17.theorem_7_1_proof h𝒯 π hcentral hΔ hnorm hcard hsmall hc' hc'_out hchoice

open Function Metric GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (7.2)** (page 178):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $\mathcal{T}$-central portrayal of a
hypergraph $G$. Let $\Delta \subseteq \Sigma$ be a disc, with $bd(\Delta)$ $\Gamma$-normal and
$|bd(\Delta) \cap N(\Gamma)| \le 3$, such that $\alpha(\Delta)$ is small. Define $\Gamma' =
(U(\Gamma) \cup \Delta, N(\Gamma) \cap \overline{\Sigma - \Delta})$; thus $c' = \Delta - (bd(\Delta)
\cap N(\Gamma))$ is a cell of $\Gamma'$. Let $A \subseteq G$ be minimal such that $\alpha(\Delta)
\subseteq A$ and $\gamma(N(\Gamma) \cap bd(\Delta)) \subseteq V(A)$. Define
$$ \begin{aligned} \alpha'(c') &= A \\ \alpha'(c) &= \alpha(c) \quad (c \in C(\Gamma') - \{c'\}) \\
\gamma' &= \gamma \mid N(\Gamma'). \end{aligned} $$
Then $\pi' = (\Sigma, \Gamma', \alpha', \beta, \gamma')$ is a $\mathcal{T}$-central portrayal of
$G$ resembling $\pi$."

Moreover, if there is a cell $c_0 \in C(\Gamma)$ with $c_0 \subseteq \Delta$ and
$|\operatorname{bd}(\Delta) \cap N(\Gamma)| \le |\tilde{c}_0|$ (and $\operatorname{ord}(\mathcal{T})
> 3$),
then either $\pi'$ is truer than $\pi$ (`π'.IsTruer π`), or
$\Delta \cap N(\Gamma) \subseteq \operatorname{bd}(\Delta)$ and $\{c \in C(\Gamma) \mid c \subseteq
\Delta\} = \{c_0\}$. -/
theorem theorem_7_2 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ} (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 < θ)
    (π : Portrayal G) (hcentral : π.IsCentral 𝒯) {Δ : Set π.S} (hΔ : IsClosedDisc Δ)
    (hnorm : discBd Δ ∩ π.Γ.U ⊆ π.Γ.N) (hcard : (discBd Δ ∩ π.Γ.N).ncard ≤ 3)
    (hnode : ∀ n ∈ discBd Δ ∩ π.domγ, ∃ d ∈ π.Γ.C, n ∈ tilde d)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ)) :
    ∃ π' : Portrayal G,
    π'.S = π.S ∧
    π'.IsCentral 𝒯 ∧
    π'.Resembles π ∧
    ((∃ c₀ ∈ π.Γ.C, c₀ ⊆ Δ ∧ (discBd Δ ∩ π.Γ.N).ncard ≤ (tilde c₀).ncard) →
      π'.IsTruer π ∨
      (Δ ∩ π.Γ.N ⊆ discBd Δ ∧ ∃ c₀ ∈ π.Γ.C, {c ∈ π.Γ.C | c ⊆ Δ} = {c₀})) :=
  GM17.theorem_7_2_proof h𝒯 hθ π hcentral hΔ hnorm hcard hnode hsmall

open Function Metric GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (7.3)** (pages 178–179):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a portrayal of a hypergraph $G$. Let
$n_1, n_2$ be distinct nodes bordering a cuff $\Theta$, and let $F \subseteq \Sigma$ be a
$\Gamma$-normal $1$-arc with ... ends $n_1, n_2$ and with $F \cap N(\Gamma) = \{n_1, n_2\}$. Let
$\Delta \subseteq \Sigma$ be a disc with $F \subseteq bd(\Delta) \subseteq F \cup \Theta$,
and for each $n \in N(\Gamma) \cap bd(\Delta)$ let
$\beta(n_1+) \cap \beta(n_2+) \subseteq \beta(n+)$. Let $\pi$ have warp $\le p$ at $\Theta$, and
let $|\beta(n_1+)| = |\beta(n_2+)| = p+1$. Then every linkage in $\alpha(\Delta)$ from
$\beta(n_1+)$ to $\beta(n_2+)$ pairs $\gamma(n_1)$ with $\gamma(n_2)$."

 Note: On page 179, the paper defines
$B_h = \bigcap (\beta(n+) : n \in I_h \cap N(\Gamma))$ ($h = 1, 2$), which is a typographical slip
for $B_h = \bigcup (\beta(n+) : n \in I_h \cap N(\Gamma))$, as the later uses of $B_1$ and $B_2$
in the proof on pages 179 and 180 show.

The Lean proof corrects a step of the paper's proof. See the correction to the proof of (7.3) in
`corrections/GM17.md`. -/
theorem theorem_7_3 {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    {Θ F Δ : Set π.S} {n₁ n₂ : π.S} {p : ℕ} (hΘ : Θ ∈ cuffs π.S) (hn₁ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂ : n₂ ∈ π.Γ.N ∩ Θ) (hne : n₁ ≠ n₂) (hnorm : π.Γ.IsNormal F) (hF : IsLineWithEnds F n₁ n₂)
    (hFbd : F ∩ bd π.S = {n₁, n₂}) (hFN : F ∩ π.Γ.N = {n₁, n₂}) (hΔ : IsClosedDisc Δ)
    (hF_bd : F ⊆ discBd Δ) (hbd_sub : discBd Δ ⊆ F ∪ Θ)
    (hinter_sub : ∀ n ∈ π.Γ.N ∩ discBd Δ, π.borderPlus n₁ ∩ π.borderPlus n₂ ⊆ π.borderPlus n)
    (hwarp : π.warpAt Θ ≤ p) (hcard₁ : (π.borderPlus n₁).ncard = p + 1)
    (hcard₂ : (π.borderPlus n₂).ncard = p + 1) :
    Portrayal.LinkagePairs (π.areaGraph Δ).skeleton
    (π.borderPlus n₁) (π.borderPlus n₂) (p + 1)
    (π.nodeVertex n₁) (π.nodeVertex n₂) :=
  GM17.theorem_7_3_proof π hΘ hn₁ hn₂ hne hnorm hF hFbd hFN hΔ hF_bd hbd_sub hinter_sub hwarp hcard₁ hcard₂

open Function Metric GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (7.4)** (page 180):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $(2p+3)$-redundant $\mathcal{T}$-central
portrayal of a hypergraph $G$, with warp $\le p$, and let $ord(\mathcal{T}) > 4p+5$. Let $F
\subseteq \Sigma$ be a $\Gamma$-normal $1$-arc with $|F \cap N(\Gamma)| = 2$. Let $\Delta \subseteq
\Sigma$ be a disc with $F \subseteq bd(\Delta) \subseteq F \cup bd(\Sigma)$, such that
$\alpha(\Delta)$ is small. Define $\Gamma' = (U(\Gamma) \cup \Delta, N(\Gamma) \cap \overline{\Sigma
- \Delta})$ and let $c'$ be the cell $\Delta - (F \cap N(\Gamma))$. Define
$$ \begin{aligned} \alpha'(c') &= \alpha(\Delta) \\ \alpha'(c) &= \alpha(c) \quad (c \in C(\Gamma')
- \{c'\}) \\ \beta' &= \beta \mid (N(\Gamma') \cap bd(\Sigma)) \\ \gamma' &= \gamma \mid N(\Gamma').
\end{aligned} $$
Then $\pi' = (\Sigma, \Gamma', \alpha', \beta', \gamma')$ is a $\mathcal{T}$-central portrayal of
$G$ resembling $\pi$."

Furthermore, either $\pi'$ is truer than $\pi$, or $\Delta \cap N(\Gamma) \subseteq F$ and $\Delta$
includes exactly one cell of $\Gamma$ (used in `(8.3)`). -/
theorem theorem_7_4 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (hc : π.IsCentral 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {F Δ : Set π.S} {n₁ n₂ : π.S} (hnorm : π.Γ.IsNormal F)
    (hF : IsLineWithEnds F n₁ n₂) (hFbd : F ∩ bd π.S = {n₁, n₂}) (hFN : F ∩ π.Γ.N = {n₁, n₂})
    (hΔ : IsClosedDisc Δ) (hF_bd : F ⊆ discBd Δ) (hbd_sub : discBd Δ ⊆ F ∪ bd π.S)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ)) :
    ∃ π' : Portrayal G,
    π'.IsCentral 𝒯 ∧
    π'.Resembles π ∧
    (π'.IsTruer π ∨ (Δ ∩ π.Γ.N ⊆ F ∧ {c ∈ π.Γ.C | c ⊆ Δ}.ncard = 1)) :=
  GM17.theorem_7_4_proof h𝒯 π hc hred hwarp hθ hnorm hF hFbd hFN hΔ hF_bd hbd_sub hsmall

/-! ## Section 8. The Painting of a True Portrayal -/

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (8.1)** (page 181):
"Every region of $\Gamma$ is an open disc." -/
theorem theorem_8_1 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {r : Set π.S} (hr : r ∈ π.Γ.regions) :
    IsOpenDisc r :=
  GM17.theorem_8_1_proof h𝒯 π htrue hred hwarp hθ hr

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (8.2)** (page 181):
"The boundary of every region is an $O$-arc, and in particular, $|\tilde{c}| \ge 2$ for every
cell $c$." -/
theorem theorem_8_2 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) :
    (∀ r ∈ π.Γ.regions, IsOArc (closure r \ r)) ∧
    (∀ c ∈ π.Γ.C, 2 ≤ (tilde c).ncard) ∧
    (∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c) :=
  GM17.theorem_8_2_proof h𝒯 π htrue hred hwarp hθ

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (8.3)** (page 182):
"For every $\Gamma$-normal $I$-arc $F$ with $|F \cap N(\Gamma)| = 2$, there is a disc
$\Delta \subseteq \Sigma$ with $F \subseteq \operatorname{bd}(\Delta) \subseteq F \cup
\operatorname{bd}(\Sigma)$
such that $\Delta \cap N(\Gamma) \subseteq F$ and $\Delta$ includes exactly one cell of $\Gamma$."
-/
theorem theorem_8_3 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {F : Set π.S} (hL : IsLine F) (hnorm : π.Γ.IsNormal F)
    (hFbd_ends : F ∩ bd π.S = lineEnds F) (hcard : (F ∩ π.Γ.N).ncard = 2) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧
    Δ ∩ π.Γ.N ⊆ F ∧ {c ∈ π.Γ.C | c ⊆ Δ}.ncard = 1 :=
  GM17.theorem_8_3_proof h𝒯 π htrue hred hwarp hθ hL hnorm hFbd_ends hcard

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (8.4)** (page 182):
"$\operatorname{dom}(\gamma) = N(\Gamma)$." -/
theorem theorem_8_4 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) :
    π.domγ = π.Γ.N :=
  GM17.theorem_8_4_proof h𝒯 π htrue hred hwarp hθ

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (8.5)** (page 182):
"For every $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with $|F \cap N(\Gamma)| \le 3$, there is
a disc $\Delta \subseteq \Sigma$ with $F = \operatorname{bd}(\Delta)$ such that $\alpha(\Delta)$ is
small, and either
(i) $\Delta \cap N(\Gamma) \subseteq F$ and $\Delta$ includes at most one cell of $\Gamma$, or
(ii) $|F \cap N(\Gamma)| = 3$, and $|\tilde{c}| = 2$ for every cell $c \subseteq \Delta$." -/
theorem theorem_8_5 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {F : Set π.S} (hO : IsOArc F) (hnorm : π.Γ.IsNormal F)
    (hcard : (F ∩ π.Γ.N).ncard ≤ 3) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ discBd Δ = F ∧
    IsSmallWrt 𝒯 (π.areaGraph Δ) ∧
    ((Δ ∩ π.Γ.N ⊆ F ∧ {c ∈ π.Γ.C | c ⊆ Δ}.ncard ≤ 1) ∨
      ((F ∩ π.Γ.N).ncard = 3 ∧ ∀ c ∈ π.Γ.C, c ⊆ Δ → (tilde c).ncard = 2)) :=
  GM17.theorem_8_5_proof h𝒯 π htrue hred hwarp hθ hO hnorm hcard

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (8.6)** (page 182):
"If $c$ is an internal cell, then $|\bar{c} \cap \operatorname{bd}(\Sigma)| \le 2$, and if equality
holds then $|\tilde{c}| = 3$ and the two members of $\bar{c} \cap \operatorname{bd}(\Sigma)$ are
consecutive." -/
theorem theorem_8_6 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {c : Set π.S} (hc : c ∈ π.Γ.C) (hint : ¬ (c ∩ bd π.S).Nonempty) :
    (closure c ∩ bd π.S).ncard ≤ 2 ∧
    ((closure c ∩ bd π.S).ncard = 2 →
      (tilde c).ncard = 3 ∧
      ∀ n₁ ∈ closure c ∩ bd π.S, ∀ n₂ ∈ closure c ∩ bd π.S, n₁ ≠ n₂ →
        ∃ c₀ ∈ π.Γ.C, (c₀ ∩ bd π.S).Nonempty ∧ tilde c₀ = {n₁, n₂}) :=
  GM17.theorem_8_6_proof h𝒯 π htrue hred hwarp hθ hc hint

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (8.7)** (page 182):
"For every node $n$ there are at least two cells $c \in C^*(\Gamma)$ with $n \in \tilde{c}$, and
if there are only two and $|\tilde{c}| = 2$ for one of them, then $c$ is a border cell." -/
theorem theorem_8_7 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {n : π.S} (hn : n ∈ π.Γ.N) :
    2 ≤ {c ∈ π.Γ.CStar | n ∈ tilde c}.ncard ∧
    ({c ∈ π.Γ.CStar | n ∈ tilde c}.ncard = 2 →
      ∀ c ∈ π.Γ.CStar, n ∈ tilde c → (tilde c).ncard = 2 → (c ∩ bd π.S).Nonempty) :=
  GM17.theorem_8_7_proof h𝒯 π htrue hred hwarp hθ hn

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (8.8)** (page 183):
"If $c_1, c_2$ are distinct cells with $\tilde{c}_1 \subseteq \tilde{c}_2$, then $c_1$ is a
border cell, and $|\tilde{c}_2| = 3$." -/
theorem theorem_8_8 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {c₁ c₂ : Set π.S} (hc₁ : c₁ ∈ π.Γ.C) (hc₂ : c₂ ∈ π.Γ.C) (hne : c₁ ≠ c₂)
    (htilde_sub : tilde c₁ ⊆ tilde c₂) :
    (c₁ ∩ bd π.S).Nonempty ∧ (tilde c₂).ncard = 3 :=
  GM17.theorem_8_8_proof h𝒯 π htrue hred hwarp hθ hc₁ hc₂ hne htilde_sub

/-! ## Section 9. Cell Connectivity in a True Portrayal -/

open Function Metric GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (9.1)** (page 183):
"Let $c_0$ be an internal cell, and let $v_1, v_2 \in \gamma(\tilde{c}_0)$. Then there is a path in
$\alpha(c_0)^*$ from $v_1$ to $v_2$ with no other vertex in $\gamma(\tilde{c}_0)$." -/
theorem theorem_9_1 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty)
    {n₁ n₂ : π.S} (hn₁ : n₁ ∈ tilde c₀) (hn₂ : n₂ ∈ tilde c₀) (hne : n₁ ≠ n₂) :
    ∃ L : PathFromTo (π.cellGraph c₀).skeleton {π.nodeVertex n₁} {π.nodeVertex n₂},
    ∀ z ∈ L.walk.support, z ∈ π.nodeVertex '' tilde c₀ →
      z = π.nodeVertex n₁ ∨ z = π.nodeVertex n₂ :=
  GM17.theorem_9_1_proof h𝒯 π htrue hred hwarp hθ hc₀ hint₀ hn₁ hn₂ hne

open Function Metric GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (9.2)** (page 184):
"Let $c_0$ be an internal cell with $|\tilde{c}_0| = 3$, and $\tilde{c}_0 = \{n_1, n_2, n_3\}$. Then
there
do not exist subhypergraphs $A_1, A_2, A_3 \subseteq \alpha(c_0)$ and $v \in V(\alpha(c_0))$ such
that
$\gamma(n_i) \in V(A_i)$ $(i = 1, 2, 3)$, $A_1 \cup A_2 \cup A_3 = \alpha(c_0)$, and for $1 \le i <
j \le 3$,
$E(A_i \cap A_j) = \emptyset$ and $V(A_i \cap A_j) = \{v\}$." -/
theorem theorem_9_2 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hint₀ : ¬ (c₀ ∩ bd π.S).Nonempty)
    {n₁ n₂ n₃ : π.S} (htc₀ : tilde c₀ = {n₁, n₂, n₃}) (hcard3 : (tilde c₀).ncard = 3)
    {A₁ A₂ A₃ : Hypergraph α β} {v : α} (hA₁_le : A₁ ≤ π.cellGraph c₀)
    (hA₂_le : A₂ ≤ π.cellGraph c₀) (hA₃_le : A₃ ≤ π.cellGraph c₀)
    (hv : v ∈ (π.cellGraph c₀).vertexSet) (hn₁_A₁ : π.nodeVertex n₁ ∈ A₁.vertexSet)
    (hn₂_A₂ : π.nodeVertex n₂ ∈ A₂.vertexSet) (hn₃_A₃ : π.nodeVertex n₃ ∈ A₃.vertexSet)
    (hA_union : A₁ ∪ A₂ ∪ A₃ = π.cellGraph c₀) (hE12 : (A₁ ∩ A₂).edgeSet = ∅)
    (hE13 : (A₁ ∩ A₃).edgeSet = ∅) (hE23 : (A₂ ∩ A₃).edgeSet = ∅) (hV12 : (A₁ ∩ A₂).vertexSet = {v})
    (hV13 : (A₁ ∩ A₃).vertexSet = {v}) (hV23 : (A₂ ∩ A₃).vertexSet = {v}) :
    False :=
  GM17.theorem_9_2_proof h𝒯 π htrue hred hwarp hθ hc₀ hint₀ htc₀ hcard3 hA₁_le hA₂_le hA₃_le hv hn₁_A₁ hn₂_A₂ hn₃_A₃ hA_union hE12 hE13 hE23 hV12 hV13 hV23

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (9.3)** (page 184):
"Let $c_0$ be a cell bordering a cuff $\Theta$ with $\tilde{c}_0 = \{n_1, n_2\}$, and let
$\pi$ have warp $q$ at $\Theta$. Suppose that there is no internal cell $c$ with
$\tilde{c}_0 \subseteq \tilde{c}$. Then there are $q + 1$ mutually vertex-disjoint paths of
$\alpha(c_0)$ from $\beta(n_1 +)$ to $\beta(n_2 +)$, and in particular $|\beta(n_i)| = q$
$(i = 1, 2)$." -/
theorem theorem_9_3 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty) {n₁ n₂ : π.S} (hn₁_tc : n₁ ∈ tilde c₀) (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂) (hno_int : ¬ ∃ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty ∧ tilde c₀ ⊆ tilde c) :
    HasDisjointPaths (π.cellGraph c₀).skeleton (π.borderPlus n₁) (π.borderPlus n₂)
      (π.warpAt Θ + 1) ∧
    (π.borderSet n₁).ncard = π.warpAt Θ ∧
    (π.borderSet n₂).ncard = π.warpAt Θ :=
  GM17.theorem_9_3_proof h𝒯 π htrue hred hwarp hθ hΘ hc₀ hc₀_Θ hn₁_tc hn₂_tc hne hno_int

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (9.4)** (page 185):
"Let $\pi$ have warp $q$ at a cuff $\Theta$; then $|\beta(n)| = q$ for all
$n \in N(\Gamma) \cap \Theta$."
Note: in the printed proof on page 185, the displayed definitions of
$\alpha'(c_1)$ and $\alpha'(c_2)$ are swapped relative to $\tilde{c}_1 = \{n_1, n_3\}$,
$\tilde{c}_2 = \{n_2, n_3\}$ and the verification on page 186; we assign the edgeless hypergraph
on $\beta(n_1+) \cup \{\gamma(n_3)\}$ to $c_1$ and $\alpha(c_0) \cup \alpha(c_3)$ to $c_2$, matching
the verification on page 186. -/
theorem theorem_9_4 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) {n₁ : π.S} (hn₁ : n₁ ∈ π.Γ.N ∩ Θ) :
    (π.borderSet n₁).ncard = π.warpAt Θ :=
  GM17.theorem_9_4_proof h𝒯 π htrue hred hwarp hθ hΘ hn₁

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **(9.5)** (Graph Minors XVII, Section 9, page 186):
"Let $H$ be a graph, let $A, B \subseteq V(H)$, and let $X \subseteq A$ and $Y \subseteq B$
with $|X| = |Y| = q$. Suppose that there is a linkage in $H \setminus (A - X)$ from $X$ to a
$q$-subset of $B$, and there is a linkage in $H \setminus (B - Y)$ from a $q$-subset of $A$
to $Y$. Then either there is a linkage in $H \setminus ((A - X) \cup (B - Y))$ from $X$ to
$Y$, or there are $q + 1$ mutually vertex-disjoint paths in $H$ from $A$ to $B$." -/
theorem theorem_9_5 {α : Type u} {β : Type v} (H : Hypergraph α β) {A B X Y : Set α} {q : ℕ}
    (hA : A ⊆ H.vertexSet) (hB : B ⊆ H.vertexSet) (hXA : X ⊆ A) (hYB : Y ⊆ B)
    (hXB : HasDisjointPathsAvoiding H X B (A \ X) q)
    (hAY : HasDisjointPathsAvoiding H A Y (B \ Y) q) :
    HasDisjointPathsAvoiding H X Y ((A \ X) ∪ (B \ Y)) q ∨
    HasDisjointPaths H.skeleton A B (q + 1) :=
  GM17.theorem_9_5_proof H hA hB hXA hYB hXB hAY

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (9.6)** (page 186):
"Let $c_0$ be a cell bordering a cuff $\Theta$ with $\tilde{c}_0 = \{n_1, n_2\}$, and let $\pi$
have warp $q$ at $\Theta$. Then there are $q$ mutually vertex-disjoint paths of $\alpha(c_0)^*$
from $\beta(n_1)$ to $\beta(n_2)$, each containing neither $\gamma(n_1)$ nor $\gamma(n_2)$." -/
theorem theorem_9_6 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty) {n₁ n₂ : π.S} (hn₁_tc : n₁ ∈ tilde c₀) (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂) :
    ∃ L : Fin (π.warpAt Θ) →
      PathFromTo (π.cellGraph c₀).skeleton (π.borderSet n₁) (π.borderSet n₂),
    (Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support}) ∧
    ∀ i, π.nodeVertex n₁ ∉ (L i).walk.support ∧ π.nodeVertex n₂ ∉ (L i).walk.support :=
  GM17.theorem_9_6_proof h𝒯 π htrue hred hwarp hθ hΘ hc₀ hc₀_Θ hn₁_tc hn₂_tc hne

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (9.7)** (page 187):
"For every border node $n$, $\beta(n) \cap \gamma(N(\Gamma)) = \emptyset$." -/
theorem theorem_9_7 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {n : π.S} (hn : n ∈ π.Γ.N ∩ bd π.S) :
    Disjoint (π.borderSet n) (π.nodeVertex '' π.Γ.N) :=
  GM17.theorem_9_7_proof h𝒯 π htrue hred hwarp hθ hn

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (9.8)** (pages 187–188):
"Let $c_0$ be a border cell with $c_0 = \{n_1, n_2\}$. Then
(i) $|\beta(n_1)| = |\beta(n_2)| = q$ and
$\beta(n_1) \cap \gamma(N(\Gamma)), \beta(n_2) \cap \gamma(N(\Gamma)) = \emptyset$; ...
(ii) there is a linkage $\{P_1, \dots, P_q\}$ in $\alpha(c_0) \setminus \{\gamma(n_1),
\gamma(n_2)\}$
from $\beta(n_1)$ to $\beta(n_2)$ such that either there is a path $P_0$ such that
$\{P_0, P_1, \dots, P_q\}$ is a linkage in $\alpha(c_0)$ from $\beta(n_1 +)$ to $\beta(n_2 +)$,
or there is an internal cell $c$ with $|\tilde{c}| = 3$ and $\tilde{c}_0 \subseteq \tilde{c}$."
(The paper writes $c_0 = \{n_1, n_2\}$ for $\tilde{c}_0 = \{n_1, n_2\}$.) -/
theorem theorem_9_8 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty) {n₁ n₂ : π.S} (hn₁_tc : n₁ ∈ tilde c₀) (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂) :
    (π.borderSet n₁).ncard = π.warpAt Θ ∧
    (π.borderSet n₂).ncard = π.warpAt Θ ∧
    Disjoint (π.borderSet n₁) (π.nodeVertex '' π.Γ.N) ∧
    Disjoint (π.borderSet n₂) (π.nodeVertex '' π.Γ.N) ∧
    ∃ L : Fin (π.warpAt Θ) →
        PathFromTo (π.cellGraph c₀).skeleton (π.borderSet n₁) (π.borderSet n₂),
      (Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support}) ∧
      (∀ i, π.nodeVertex n₁ ∉ (L i).walk.support ∧ π.nodeVertex n₂ ∉ (L i).walk.support) ∧
      ((∃ L₀ : PathFromTo (π.cellGraph c₀).skeleton {π.nodeVertex n₁} {π.nodeVertex n₂},
          ∀ i, Disjoint {z | z ∈ L₀.walk.support} {z | z ∈ (L i).walk.support}) ∨
        ∃ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 ∧ tilde c₀ ⊆ tilde c) :=
  GM17.theorem_9_8_proof h𝒯 π htrue hred hwarp hθ hΘ hc₀ hc₀_Θ hn₁_tc hn₂_tc hne

/-! ## Section 10. Circumnavigating a Vortex -/

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (10.1)** (page 188):
"With notation as before, if $v_k \ne v$ then $L(v, n_0)$ is a path, and if $v_k = v$ then
$L(v, n_0)$ is a circuit; and for distinct $v, v' \in \beta(n_0)$, $L(v, n_0)$ and $L(v', n_0)$
are edge-disjoint, and if some vertex $u$ belongs to both of them then both are paths and $u$ is
an initial vertex of one and a terminal vertex of the other." -/
theorem theorem_10_1 {α : Type u} {β : Type v} {G : Hypergraph α β} {π : Portrayal G} {Θ : Set π.S}
    {k q : ℕ} {E : π.Γ.CuffEnumeration Θ k} (SL : CuffStandardLinkages π Θ k q E)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ} (h𝒯 : IsTangle G θ 𝒯)
    (hT : π.IsCentral 𝒯) (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z) (hz : 3 ≤ z)
    (hθ : z + max 3 (2 * p + 2) < θ) (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q)
    (i₀ : Fin k) :
    (∀ v ∈ π.borderSet (E.node i₀),
      {z | z ∈ (SL.circWalk i₀ v k).support} = SL.circumnavigationVertices i₀ v ∧
      (SL.circWalk i₀ v k).support.tail ≠ [] ∧
      (SL.circWalk i₀ v k).support.tail.Nodup ∧
      (SL.traceVertex i₀ v k ≠ v → (SL.circWalk i₀ v k).IsPath) ∧
      (SL.traceVertex i₀ v k = v →
        {z | z ∈ (SL.circWalk i₀ v k).support.tail} = SL.circumnavigationVertices i₀ v)) ∧
    (∀ v ∈ π.borderSet (E.node i₀), ∀ v' ∈ π.borderSet (E.node i₀), v ≠ v' →
      List.Disjoint (SL.circWalk i₀ v k).support.tail (SL.circWalk i₀ v' k).support.tail ∧
      ∀ u ∈ SL.circumnavigationVertices i₀ v ∩ SL.circumnavigationVertices i₀ v',
        (SL.circWalk i₀ v k).IsPath ∧ (SL.circWalk i₀ v' k).IsPath ∧
        SL.traceVertex i₀ v k ≠ v ∧ SL.traceVertex i₀ v' k ≠ v' ∧
        ((u = v ∧ u = SL.traceVertex i₀ v' k) ∨ (u = v' ∧ u = SL.traceVertex i₀ v k))) :=
  GM17.theorem_10_1_proof SL h𝒯 hT hwarp hred hz hθ hcard i₀

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (10.2)** (page 188):
"There is no $(A, B) \in \mathcal{T}$ of order $\le z$ with $V(L(v, n_0)) \subseteq V(A)$."

Note on hypergraph edges: the paper's proof applies [1, Theorem (2.8)] to deduce $L(v, n_0)
\subseteq A$
and hence that each $P_i$ is a path of $(A \cap \alpha(c_i))^*$. In a hypergraph $G$, an edge
$e \in E(\alpha(c_i))$ witnessing an adjacency of $P_i$ may also be incident with a third vertex
outside
$V(A)$, so $e$ may belong to $E(B)$ even when $B$ is minimal. Using `theorem_6_5_walk_subset` (which
is the vertex-support statement proved by the proof of (6.5) on page 176), the contradiction holds
directly from $V(P_i) \subseteq V(L(v, n_0)) \subseteq V(A)$ without assuming edges have size $\le
2$. -/
theorem theorem_10_2 {α : Type u} {β : Type v} {G : Hypergraph α β} {π : Portrayal G} {Θ : Set π.S}
    {k q : ℕ} {E : π.Γ.CuffEnumeration Θ k} (SL : CuffStandardLinkages π Θ k q E)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ} (h𝒯 : IsTangle G θ 𝒯)
    (hT : π.IsCentral 𝒯) (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z) (_hz : 2 * p + 3 ≤ z)
    (hθ : z + 2 * p + 2 < θ) (hq : π.warpAt Θ = q)
    (hcard : ∀ r : Fin k, (π.borderSet (E.node r)).ncard = q) (i₀ : Fin k) {v : α}
    (hv : v ∈ π.borderSet (E.node i₀)) {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯)
    (hord : separationOrder A B ≤ z) :
    ¬ (SL.circumnavigationVertices i₀ v ⊆ A.vertexSet) :=
  GM17.theorem_10_2_proof SL h𝒯 hT hwarp hred _hz hθ hq hcard i₀ hv hAB hord

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (10.3)** (page 189):
"For each cuff $\Theta$, there is no $(A, B) \in \mathcal{T}$ of order $\le z$ with
$\gamma(N(\Gamma) \cap \Theta) \subseteq V(A)$." -/
theorem theorem_10_3 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p z : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (hT : π.IsCentral 𝒯) (htrue : π.IsTrue 𝒯) (hwarp : π.warp ≤ p) (hred : π.IsRedundant 𝒯 θ z)
    (hz : 2 * p + 3 ≤ z) (hθ : z + 2 * p + 2 < θ) {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) (hord : separationOrder A B ≤ z) :
    ¬ (π.gammaImage (π.Γ.N ∩ Θ) ⊆ A.vertexSet) :=
  GM17.theorem_10_3_proof h𝒯 π hT htrue hwarp hred hz hθ hΘ hAB hord

/-! ## Section 11. Surface Separations in a True Portrayal -/

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (11.1)** (page 189):
"Let $I, J$ be a partition of $C(\Gamma)$ with $\gamma(I), \gamma(J) \ne N(\Gamma)$ and
$|\gamma(I) \cap \gamma(J)| \le 3$. Then $|\gamma(I) \cap \gamma(J)| = 3$ and there is a
disc $\Delta \subseteq \Sigma$ such that* (i) *$\{c \in C(\Gamma) \colon c \subseteq
\Delta\}$ is one of $I, J$,* (ii) *$\alpha(\Delta)$ is small, and* (iii) *either
$\operatorname{bd}(\Delta)$ is a $\Gamma$-normal $O$-arc in $\Sigma$ and $N(\Gamma) \cap
\operatorname{bd}(\Delta) = \gamma(I) \cap \gamma(J)$, or $F \subseteq
\operatorname{bd}(\Delta) \subseteq F \cup \operatorname{bd}(\Sigma)$ and $N(\Gamma) \cap F
= \gamma(I) \cap \gamma(J)$ for some $\Gamma$-normal $I$-arc $F$." -/
theorem theorem_11_1 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 4)) (hwarp : π.warp ≤ p)
    (hθ : 6 * p + 8 < θ) {I J : Set (Set π.S)} (hcov : I ∪ J = π.Γ.C) (hdisj : Disjoint I J)
    (hI_ne : π.Γ.tildeOfCells I ≠ π.Γ.N) (hJ_ne : π.Γ.tildeOfCells J ≠ π.Γ.N)
    (hcard_le : (π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J).ncard ≤ 3) :
    (π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J).ncard = 3 ∧
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧
      ({c ∈ π.Γ.C | c ⊆ Δ} = I ∨ {c ∈ π.Γ.C | c ⊆ Δ} = J) ∧
      IsSmallWrt 𝒯 (π.areaGraph Δ) ∧
      ((IsOArc (discBd Δ) ∧ π.Γ.IsNormal (discBd Δ) ∧
          π.Γ.N ∩ discBd Δ = π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J) ∨
       (∃ F : Set π.S, ∃ n₁ n₂ : π.S,
          IsLineWithEnds F n₁ n₂ ∧ π.Γ.IsNormal F ∧ F ∩ bd π.S = {n₁, n₂} ∧
          F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧
          π.Γ.N ∩ F = π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J)) :=
  GM17.theorem_11_1_proof h𝒯 π htrue hred hwarp hθ hcov hdisj hI_ne hJ_ne hcard_le

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (11.2)** (pages 191–192):
"Let $(A, B) \in \mathscr{T}$ have order $< ord(\mathscr{T}) - 4p - 3$, let $c_0 \in C(\Gamma)$
with $\alpha(c_0) \subseteq A$, let $I, J$ be a partition of $C(\Gamma)$ so that $\gamma(I)
\subseteq V(A)$ and $\gamma(J) \subseteq V(B)$ and let
$$|\{n \in N(\Gamma) : \gamma(n) \in V(A \cap B)\}| \le |\tilde{c}_0|.$$
Then equality holds, and either
(i) $\{n \in N(\Gamma) : \gamma(n) \in V(A)\} = \tilde{c}_0$ and $\gamma(n) \in V(B)$ for all $n
\in N(\Gamma)$, or
(ii) $|\tilde{c}_0| = 3$, and there is a $\Gamma$-normal $I$-arc $F$ and a disc $\Delta \subseteq
\Sigma$ with $\alpha(\Delta)$ small and with $F \subseteq bd(\Delta) \subseteq F \cup bd(\Sigma)$,
such that $I = \{c \in C(\Gamma) : c \subseteq \Delta\}$ and for all $n \in N(\Gamma)$, $\gamma(n)
\in V(A)$ if and only if $n \in \Delta$, and $\gamma(n) \in V(B)$ if and only if..."

We also record the equivalent condition $n \in (\Sigma \setminus \Delta) \cup F$ for
$\gamma(n) \in V(B)$ in (ii). -/
theorem theorem_11_2 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 4)) (hwarp : π.warp ≤ p)
    (hθ : 6 * p + 8 < θ) {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯)
    (hord : separationOrder A B + 4 * p + 3 < θ) {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀A : π.cellGraph c₀ ≤ A) {I J : Set (Set π.S)} (hcov : I ∪ J = π.Γ.C) (hdisj : Disjoint I J)
    (hc₀I : c₀ ∈ I) (hI_A : π.gammaOfCells I ⊆ A.vertexSet) (hJ_B : π.gammaOfCells J ⊆ B.vertexSet)
    (hcard_le : {n ∈ π.Γ.N | π.nodeVertex n ∈ (A ∩ B).vertexSet}.ncard ≤ (tilde c₀).ncard) :
    {n ∈ π.Γ.N | π.nodeVertex n ∈ (A ∩ B).vertexSet}.ncard = (tilde c₀).ncard ∧
    (({n ∈ π.Γ.N | π.nodeVertex n ∈ A.vertexSet} = tilde c₀ ∧
        ∀ n ∈ π.Γ.N, π.nodeVertex n ∈ B.vertexSet) ∨
     ((tilde c₀).ncard = 3 ∧
      ∃ F Δ : Set π.S, ∃ n₁ n₂ : π.S,
        IsLineWithEnds F n₁ n₂ ∧ π.Γ.IsNormal F ∧ F ∩ bd π.S = {n₁, n₂} ∧
        IsClosedDisc Δ ∧ IsSmallWrt 𝒯 (π.areaGraph Δ) ∧
        F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧
        I = {c ∈ π.Γ.C | c ⊆ Δ} ∧
        (∀ n ∈ π.Γ.N,
          (π.nodeVertex n ∈ A.vertexSet ↔ n ∈ Δ) ∧
          (π.nodeVertex n ∈ B.vertexSet ↔ n ∈ closure (Set.univ \ Δ)) ∧
          (π.nodeVertex n ∈ B.vertexSet ↔ n ∈ (Set.univ \ Δ) ∪ F)))) :=
  GM17.theorem_11_2_proof h𝒯 π htrue hred hwarp hθ hAB hord hc₀ hc₀A hcov hdisj hc₀I hI_A hJ_B hcard_le

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (11.3)** (pages 192–193):
"Let $F \subseteq \Sigma$ be a $\Gamma$-normal $I$-arc with $F \cap N(\Gamma) = \{n_1, n_2, n_3\}$,
where $F$ has ends $n_1, n_2$, and let $\Delta \subseteq \Sigma$ be the disc with $\alpha(\Delta)$
small and $F \subseteq \operatorname{bd}(\Delta) \subseteq F \cup \operatorname{bd}(\Sigma)$.
Suppose that there is a cell $c_0 \subseteq \Delta$ with $|\tilde{c}_0| = 3$. Then either
(i) $\tilde{c}_0 = \Delta \cap N(\Gamma)$ or
(ii) there is no separation $(A_1, A_2)$ of $\alpha(\Delta)$ with
$V(A_1 \cap A_2) = \{\gamma(n_1), \gamma(n_2)\}$, $\gamma(n_3) \in V(A_1)$, and
$\beta(n_1) \cup \beta(n_2) \subseteq V(A_2)$." -/
theorem theorem_11_3 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 4)) (hwarp : π.warp ≤ p)
    (hθ : 6 * p + 8 < θ) {F Δ c₀ : Set π.S} {n₁ n₂ n₃ : π.S} (hnorm : π.Γ.IsNormal F)
    (hF : IsLineWithEnds F n₁ n₂) (hFbd : F ∩ bd π.S = {n₁, n₂}) (hFN : F ∩ π.Γ.N = {n₁, n₂, n₃})
    (hFN_card : (F ∩ π.Γ.N).ncard = 3) (hΔ : IsClosedDisc Δ) (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ))
    (hF_bd : F ⊆ discBd Δ) (hbd_sub : discBd Δ ⊆ F ∪ bd π.S) (hc₀ : c₀ ∈ π.Γ.C) (hc₀_Δ : c₀ ⊆ Δ)
    (hc₀_card : (tilde c₀).ncard = 3) :
    tilde c₀ = Δ ∩ π.Γ.N ∨
    ¬ ∃ A₁ A₂ : Hypergraph α β,
        (π.areaGraph Δ).IsSeparation A₁ A₂ ∧
        (A₁ ∩ A₂).vertexSet = {π.nodeVertex n₁, π.nodeVertex n₂} ∧
        π.nodeVertex n₃ ∈ A₁.vertexSet ∧
        π.borderSet n₁ ∪ π.borderSet n₂ ⊆ A₂.vertexSet :=
  GM17.theorem_11_3_proof h𝒯 π htrue hred hwarp hθ hnorm hF hFbd hFN hFN_card hΔ hsmall hF_bd hbd_sub hc₀ hc₀_Δ hc₀_card

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (11.4)** (pages 193–194):
"For any separation $(A, B)$ of $G$, if $d \in D(A, B)$ then*
$$
V(A \cap B) \cap (V(\alpha(d)) - (S \cup V(\alpha(-d)))) \ne \emptyset.
$$" -/
theorem theorem_11_4 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) (sys : π.SystemOfStandardLinkages) {A B : Hypergraph α β}
    (hsep : G.IsSeparation A B) {d : Set π.S} (hd : d ∈ π.crossingCells A B) :
    ((A ∩ B).vertexSet ∩ ((π.cellGraph d).vertexSet \ (sys.S ∪ π.otherVertices d))).Nonempty :=
  GM17.theorem_11_4_proof h𝒯 π htrue hred hwarp hθ sys hsep hd

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (11.5)** (page 194):
"For any separation $(A, B)$ of $G$,*
$$|D(A, B)| \le |V(A \cap B) - (S \cup \gamma(N(\Gamma)))|.$$" -/
theorem theorem_11_5 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) (sys : π.SystemOfStandardLinkages) {A B : Hypergraph α β}
    (hsep : G.IsSeparation A B) :
    (π.crossingCells A B).ncard ≤
    ((A ∩ B).vertexSet \ (sys.S ∪ π.gammaImage π.Γ.N)).ncard :=
  GM17.theorem_11_5_proof h𝒯 π htrue hred hwarp hθ sys hsep

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (11.6)** (page 194):
"$|V(A \cap B) - S| \le |\tilde{c}_0|$, and if equality holds then*
$$|V(A \cap B) \cap S| = |V(\alpha(c_0) \cap \alpha(-c_0)) \cap S|.$$" -/
theorem theorem_11_6 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 3)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) (sys : π.SystemOfStandardLinkages) {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) (hc₀A : π.cellGraph c₀ ≤ A)
    (hle : separationOrder A B ≤ ((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀).ncard) :
    ((A ∩ B).vertexSet \ sys.S).ncard ≤ (tilde c₀).ncard ∧
    (((A ∩ B).vertexSet \ sys.S).ncard = (tilde c₀).ncard →
      ((A ∩ B).vertexSet ∩ sys.S).ncard =
        (((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀) ∩ sys.S).ncard) :=
  GM17.theorem_11_6_proof h𝒯 π htrue hred hwarp hθ sys hc₀ hAB hc₀A hle

open Function Metric Classical GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (11.7)** (page 195):
"$|V(A \cap B)| = |V(\alpha(c_0) \cap \alpha(-c_0))|.$" -/
theorem theorem_11_7 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 4)) (hwarp : π.warp ≤ p)
    (hθ : 6 * p + 8 < θ) {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯)
    (hc₀A : π.cellGraph c₀ ≤ A)
    (hle : separationOrder A B ≤ ((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀).ncard) :
    separationOrder A B = ((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀).ncard :=
  GM17.theorem_11_7_proof h𝒯 π htrue hred hwarp hθ hc₀ hAB hc₀A hle

/-! ## Section 12. Filling Out a Portrayal of the 1-Skeleton -/

open Function GraphMinor.GM10 GraphMinor.GM19 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (12.1)** (page 197):
"Let $\mathscr{T}$ be a tangle of order $> 4p+9$ in a hypergraph $G$, let
$\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a true, $(2p+7)$-redundant,
$\mathscr{T}$-central portrayal of $G$ with warp $\le p$, and let $\Theta$ be a cuff of $\Sigma$.
For every clique $K$ of $G$ with
$$K \subseteq \bigcup (V(\alpha(c)) \colon c \in C(\Gamma) \text{ bordering } \Theta)$$
there is a cell $c$ bordering $\Theta$ with $K \subseteq V(\alpha(c))$." -/
theorem theorem_12_1 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 7)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 9 < θ) {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) {K : Set α} (hK : IsClique G K)
    (hK_sub : K ⊆ ⋃ c ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty}, (π.cellGraph c).vertexSet) :
    ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ K ⊆ (π.cellGraph c).vertexSet :=
  GM17.theorem_12_1_proof h𝒯 π htrue hred hwarp hθ hΘ hK hK_sub

open Function GraphMinor.GM10 GraphMinor.GM19 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (12.2)** (page 198):
"Let $\mathscr{T}$ be a tangle of order $>4p+9$ in a hypergraph $G$, and let
$\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a true, $(2p+7)$-redundant,
$\mathscr{T}$-central portrayal of $G$, with warp $\le p$. Then for every clique $K$ of $G$, either
(i) there is a disc $\Delta \subseteq \Sigma$ such that $\alpha(\Delta)$ is small,
$K \subseteq V(\alpha(\Delta))$, and $\operatorname{bd}(\Delta)$ is a $\Gamma$-normal $O$-arc with
$|\operatorname{bd}(\Delta) \cap N(\Gamma)| \le 3$, or
(ii) $K \subseteq V(\alpha(c))$ for some $c \in C(\Gamma)$."

In (i) we prove $K \subseteq V(\alpha(\Delta)) \cup \gamma(\operatorname{bd}(\Delta) \cap
N(\Gamma))$. The paper's proof gives $M \subseteq \Delta(C)$, and a node of
$\operatorname{bd}(\Delta)$ need not lie on a cell inside $\Delta$. This is what (12.4) uses, since
the cell made by (7.2) contains $\gamma(\operatorname{bd}(\Delta) \cap N(\Gamma))$.

In claim (1) of the proof the four discs form a sphere, which is all of `Σ`, as in the paper
(`GM17.four_discs_cover`). -/
theorem theorem_12_2 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ} (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 7)) (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 9 < θ) {K : Set α} (hK : IsClique G K) :
    (∃ Δ : Set π.S, IsClosedDisc Δ ∧ IsSmallWrt 𝒯 (π.areaGraph Δ) ∧
      K ⊆ (π.areaGraph Δ).vertexSet ∪ π.nodeVertex '' (discBd Δ ∩ π.Γ.N) ∧
      IsOArc (discBd Δ) ∧ π.Γ.IsNormal (discBd Δ) ∧
      (discBd Δ ∩ π.Γ.N).ncard ≤ 3) ∨
    (∃ c ∈ π.Γ.C, K ⊆ (π.cellGraph c).vertexSet) :=
  GM17.theorem_12_2_proof h𝒯 π htrue hred hwarp hθ hK

open Function GraphMinor.GM10 GraphMinor.GM19 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (12.3)** (page 199): "Let $e$ be an edge of a hypergraph $G$, and let $K$
be the set of ends of $e$. Let $K$ be a clique of $G \setminus e$. Let $\mathscr{T}$ be a tangle in
$G \setminus e$ of order $> 2p+8$, inducing a tangle $\mathscr{T}'$ in $G$. Let $\pi = (\Sigma,
\Gamma, \alpha, \beta, \gamma)$ be a 6-redundant, $\mathscr{T}$-central portrayal of $G \setminus
e$ with warp $\le p$. Let $c_0 \in C(\Gamma)$ with $K \subseteq V(\alpha(c_0))$. Define $\alpha'$
by $$\begin{aligned} \alpha'(c_0) &= (V(\alpha(c_0)), E(\alpha(c_0)) \cup \{e\}) \\ \alpha'(c) &=
\alpha(c) \qquad (c \in C(\Gamma) - \{c_0\}). \end{aligned}$$ Then $\pi' = (\Sigma, \Gamma,
\alpha', \beta, \gamma)$ is a $\mathscr{T}'$-central portrayal of $G$, resembling $\pi$." Here `π'`
is `addEdgePortrayal`.

The step "Consequently $c$ borders $\Theta$" of the paper's proof needs the conclusion of (9.7) (no
vertex of $\beta(n)$ is $\gamma$ of a node), which the paper does not cite there; (9.7) is proved
for true, $(2p+3)$-redundant portrayals with $\operatorname{ord}(\mathscr{T}) > 4p+5$. So here $\pi$
is assumed true and $\max(6, 2p+3)$-redundant with $\theta > \max(2p+8, 4p+5)$.
`addEdgePortrayal_central_resembles` has the printed hypotheses plus the conclusion of (9.7). -/
theorem theorem_12_3 {α : Type u} {β : Type v} {G : Hypergraph α β} {e : β} (he : e ∈ G.edgeSet)
    (hK : IsClique (G.deleteEdges {e}) (G.ends e)) {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ p : ℕ} (h𝒯 : IsTangle (G.deleteEdges {e}) θ 𝒯) (hθ : max (2 * p + 8) (4 * p + 5) < θ)
    (π : Portrayal (G.deleteEdges {e})) (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (max 6 (2 * p + 3))) (hwarp : π.warp ≤ p) {c₀ : Set π.S}
    (hc₀ : c₀ ∈ π.Γ.C) (hends : G.ends e ⊆ (π.cellGraph c₀).vertexSet) :
    (addEdgePortrayal π hc₀ he hends).IsCentral (inducedSubhypergraphTangle G (G.deleteEdges {e}) 𝒯 θ) ∧
    (addEdgePortrayal π hc₀ he hends).Resembles π :=
  GM17.theorem_12_3_proof he hK h𝒯 hθ π htrue hred hwarp hc₀ hends

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (12.4)** (page 200): "Let $e$ be an edge of a hypergraph $G$, such that the
set of ends of $e$ is a clique of $G \setminus e$. Let $\mathscr{T}$ be a tangle in $G \setminus e$,
of order $>4p+9$, inducing a tangle $\mathscr{T}'$ in $G$. Let $\pi$ be a $(2p+7)$-redundant,
$\mathscr{T}$-central portrayal of $G \setminus e$ with warp $\le p$. Then there is a
$\mathscr{T}'$-central portrayal of $G$ resembling $\pi$." -/
theorem theorem_12_4 {α : Type u} {β : Type v} {G : Hypergraph α β} {e : β} (he : e ∈ G.edgeSet)
    (hK : IsClique (G.deleteEdges {e}) (G.ends e)) {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ p : ℕ} (h𝒯 : IsTangle (G.deleteEdges {e}) θ 𝒯) (hθ : 4 * p + 9 < θ)
    (π : Portrayal (G.deleteEdges {e})) (hc : π.IsCentral 𝒯) (hred : π.IsRedundant 𝒯 θ (2 * p + 7))
    (hwarp : π.warp ≤ p) :
    ∃ π' : Portrayal G, π'.IsCentral (inducedSubhypergraphTangle G (G.deleteEdges {e}) 𝒯 θ) ∧ π'.Resembles π :=
  GM17.theorem_12_4_proof he hK h𝒯 hθ π hc hred hwarp

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (12.5)** (page 200): "Let $G$ be a hypergraph, and let $\mathscr{T}^*$ be a
tangle in $G^*$ of order $\theta$. Let $\mathscr{T}$ be the set of all separations $(A, B)$ of $G$
of order $<\theta$ such that $A^*$ is small relative to $\mathscr{T}^*$. Then $\mathscr{T}$ is a
tangle in $G$ of order $\theta$." -/
theorem theorem_12_5 {α : Type u} {β : Type v} {G : Hypergraph α β} {θ : ℕ}
    {𝒯s : Set (Hypergraph α (Sym2 α) × Hypergraph α (Sym2 α))}
    (h𝒯 : IsTangle (oneSkeletonHypergraph G) θ 𝒯s) : IsTangle G θ (embodimentTangle G 𝒯s θ) :=
  GM17.theorem_12_5_proof h𝒯

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (12.6)** (page 200): "Let $G$ be a hypergraph, and let $\mathscr{T}^*$ be a
tangle in $G^*$ of order $>4p+9$. Let $\mathscr{T}$ be the embodiment of $\mathscr{T}^*$ in $G$. Let
$\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $(2p+7)$-redundant, $\mathscr{T}^*$-central
portrayal of $G^*$ with warp $\le p$. Then there is a $\mathscr{T}$-central portrayal of $G$
resembling $\pi$."

The Lean proof corrects a step of the paper's proof. See the correction to the proof of (12.6) in
`corrections/GM17.md`. -/
theorem theorem_12_6 {α : Type u} {β : Type v} {G : Hypergraph α β} {θ p : ℕ}
    {𝒯s : Set (Hypergraph α (Sym2 α) × Hypergraph α (Sym2 α))}
    (h𝒯 : IsTangle (oneSkeletonHypergraph G) θ 𝒯s) (hθ : 4 * p + 9 < θ)
    (π : Portrayal (oneSkeletonHypergraph G)) (hc : π.IsCentral 𝒯s)
    (hred : π.IsRedundant 𝒯s θ (2 * p + 7)) (hwarp : π.warp ≤ p) :
    ∃ π' : Portrayal G, π'.IsCentral (embodimentTangle G 𝒯s θ) ∧ π'.Resembles π :=
  GM17.theorem_12_6_proof h𝒯 hθ π hc hred hwarp

/-! ## Section 13. Excluding a Minor -/

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (13.1)** (page 202): "For any graph $H$ there are numbers $p$, $q$, $z$ and
$\theta > z$, such that for every hypergraph $G$ and every tangle $\mathcal{T}$ in $G$ of order $\ge
\theta$, either (i) $\mathcal{T}$ controls an $H$-minor of $G^*$, or (ii) there exists $Z \subseteq
V(G)$ with $|Z| \le z$ and a $\mathcal{T} \setminus Z$-central portrayal $\pi = (\Sigma, \Gamma,
\alpha, \beta, \gamma)$ of $G \setminus Z$ with warp $\le p$, such that $\Sigma$ has $\le q$ cuffs
and $H$ cannot be drawn in $\Sigma$."

, from XVI (3.1).

The print fails for hypergraphs, so the Lean states (13.1) for graphs, which is how (13.4) and
(14.2) use it. See the correction to (13.1) in `corrections/GM17.md`. -/
theorem theorem_13_1 {α' β' : Type} (H : Hypergraph α' β') (hH : H.IsGraph) :
    ∃ p q z θ : ℕ, z < θ ∧ ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph →
    ∀ (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯 → θ ≤ θ' →
    ControlsMinor G 𝒯 H ∨ ∃ Z ⊆ G.vertexSet, Z.ncard ≤ z ∧ ∃ π : Portrayal (G.deleteVertices Z),
    π.IsCentral (deleteVerticesTangle G Z 𝒯 θ') ∧ π.warp ≤ p ∧ (cuffs π.S).encard ≤ q ∧
    ¬ CanBeDrawn π.S H :=
  GM17.theorem_13_1_proof H hH

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (13.2)** (page 205): "Let $p \ge 1$, and let $\pi$, $\pi'$ be portrayals of
$G$, $G'$ respectively. If $\pi$ has warp $\le p$, and $\pi'$ is simpler than $\pi$, then $h_p(\pi')
< h_p(\pi)$." -/
theorem theorem_13_2 {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'} {G : Hypergraph α β}
    {G' : Hypergraph α' β'} {p : ℕ} (hp : 1 ≤ p) (π : Portrayal G) (π' : Portrayal G')
    (hw : π.warp ≤ p) (hs : π'.IsSimpler π) :
    π'.hp p < π.hp p :=
  GM17.theorem_13_2_proof hp π π' hw hs

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (13.3)** (page 205): "For any standard $\sigma$ and all $p \ge 1$ and $h$,
$z_0 \ge 0$, there exist $\theta$, $z$ with $\theta > z \ge z_0$ and with the following property.
Let $\mathcal{T}$ be a tangle of order $\ge \theta$ in a graph $G$, let $Z_0 \subseteq V(G)$ with
$|Z_0| \le z_0$, and let $\pi_0$ be a $(\mathcal{T} \setminus Z_0)$-central portrayal of $G
\setminus Z_0$ with warp $\le p$ and with $h_p(\pi_0) \le h$. Then there exist $Z \subseteq V(G)$
with $Z_0 \subseteq Z$ such that $|Z| \le z$, and a $(\mathcal{T} \setminus Z)$-central portrayal
$\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ of $G \setminus Z$, such that $\pi$ is simpler than
or resembles $\pi_0$, and $\pi$ is $\sigma(\Sigma, p, |Z|)$-redundant."

We read a bound on all `σ` from `sigmaBound`, so the paper's reduction to its condition (1) is not
needed. -/
theorem theorem_13_3 (σ : (S : Type) → [TopologicalSpace S] → ℕ → ℕ → ℕ) (hσ : IsStandard σ) {p : ℕ}
    (hp : 1 ≤ p) (h z₀ : ℕ) :
    ∃ θ z : ℕ, z < θ ∧ z₀ ≤ z ∧ ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph → ∀ (θ' : ℕ)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯 → θ ≤ θ' → ∀ Z₀ ⊆ G.vertexSet, Z₀.ncard ≤ z₀ →
    ∀ π₀ : Portrayal (G.deleteVertices Z₀), π₀.IsCentral (deleteVerticesTangle G Z₀ 𝒯 θ') → π₀.warp ≤ p → π₀.hp p ≤ h →
    ∃ Z, Z₀ ⊆ Z ∧ Z ⊆ G.vertexSet ∧ Z.ncard ≤ z ∧ ∃ π : Portrayal (G.deleteVertices Z),
      π.IsCentral (deleteVerticesTangle G Z 𝒯 θ') ∧ (π.IsSimpler π₀ ∨ π.Resembles π₀) ∧
      π.IsRedundant (deleteVerticesTangle G Z 𝒯 θ') (θ' - Z.ncard) (σ π.S p Z.ncard) :=
  GM17.theorem_13_3_proof σ hσ hp h z₀

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (13.4)** (page 206): "For any graph $H$ and standard $\sigma$, there are
numbers $p, q, z$ and $\theta > z$, such that for every graph $G$ and every tangle $\mathscr{T}$ in
$G$ of order $\ge \theta$, either (i) $\mathscr{T}$ controls an $H$-minor of $G$, or (ii) there
exists $Z \subseteq V(G)$ with $|Z| \le z$, and a $(\mathscr{T} \setminus Z)$-central portrayal $\pi
= (\Sigma, \Gamma, \alpha, \beta, \gamma)$ of $G \setminus Z$ with warp $\le p$, such that $\Sigma$
has $\le q$ cuffs, $H$ cannot be drawn in $\Sigma$, and $\pi$ is $\sigma(\Sigma, p, |Z|)$-redundant
and true."

"Simpler than" is defined by the paper's second form. See the correction on page 164 in
`corrections/GM17.md`. -/
theorem theorem_13_4 {α' β' : Type} (H : Hypergraph α' β') (hH : H.IsGraph)
    (σ : (S : Type) → [TopologicalSpace S] → ℕ → ℕ → ℕ) (hσ : IsStandard σ) :
    ∃ p q z θ : ℕ, z < θ ∧ ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph → ∀ (θ' : ℕ)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯 → θ ≤ θ' →
    ControlsMinor G 𝒯 H ∨ ∃ Z ⊆ G.vertexSet, Z.ncard ≤ z ∧ ∃ π : Portrayal (G.deleteVertices Z),
      π.warp ≤ p ∧ (cuffs π.S).encard ≤ q ∧ ¬ CanBeDrawn π.S H ∧ π.IsTrue (deleteVerticesTangle G Z 𝒯 θ') ∧
      π.IsRedundant (deleteVerticesTangle G Z 𝒯 θ') (θ' - Z.ncard) (σ π.S p Z.ncard) :=
  GM17.theorem_13_4_proof H hH σ hσ

/-! ## Section 14. Hypergraph Form of the Excluded Minor Theorem -/

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (14.1)** (page 207):
"Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$. Let $\theta^* \ge 1$ with
$\theta^* < 2/3\theta + 1$, and let $\mathscr{T}^*$ be the set of all separations $(A', B')$ of
$G^*$ of order $< \theta^*$ such that there exists $(A, B) \in \mathscr{T}$ with $V(A) = V(A')$
and $V(B) = V(B')$. Then $\mathscr{T}^*$ is a tangle in $G^*$ of order $\theta^*$." -/
theorem theorem_14_1 {α : Type u} {β : Type v} {G : Hypergraph α β} {θ θstar : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h1 : 1 ≤ θstar) (hlt : 3 * θstar < 2 * θ + 3)
    (h𝒯 : IsTangle G θ 𝒯) :
    IsTangle (oneSkeletonHypergraph G) θstar (oneSkeletonTangle G 𝒯 θstar) :=
  GM17.theorem_14_1_proof h1 hlt h𝒯

open Function GraphMinor.GM10 GraphMinor.Hypergraph in
/-- **Graph Minors XVII, (14.2)** (page 209): "For any graph $H$ there are numbers $p, q, z$ and
$\theta > z$, such that for every hypergraph $G$ and every tangle $\mathscr{T}$ in $G$ of order $\ge
\theta$, either (i) $\mathscr{T}$ controls an $H$-minor of $G^*$, or (ii) there exists $Z \subseteq
V(G)$ with $|Z| \le z$ and a $\mathscr{T}/Z$-central portrayal $\pi = (\Sigma, \Gamma, \alpha,
\beta, \gamma)$ of $G/Z$ with warp $\le p$, such that $\Sigma$ has $\le q$ cuffs and $H$ cannot be
drawn in $\Sigma$, and $\pi$ is true and $(2p + 7)$-redundant." -/
theorem theorem_14_2 {α' β' : Type} (H : Hypergraph α' β') (hH : H.IsGraph) :
    ∃ p q z θ : ℕ, z < θ ∧ ∀ {α : Type u} {β : Type v} (G : Hypergraph α β) (θ' : ℕ)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯 → θ ≤ θ' →
    ControlsMinor G 𝒯 H ∨ ∃ Z ⊆ G.vertexSet, Z.ncard ≤ z ∧
      ∃ π : Portrayal (quotientVertices G Z), π.warp ≤ p ∧ (cuffs π.S).encard ≤ q ∧
        ¬ CanBeDrawn π.S H ∧ π.IsTrue (quotientTangle G 𝒯 Z) ∧
        π.IsRedundant (quotientTangle G 𝒯 Z) (θ' - Z.ncard) (2 * p + 7) :=
  GM17.theorem_14_2_proof H hH

end GraphMinor.GM17
