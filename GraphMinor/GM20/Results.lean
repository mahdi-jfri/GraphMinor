module

public import GraphMinor.GM20.Basic
public import GraphMinor.GM20.Section10a
public import GraphMinor.GM20.Section10b
public import GraphMinor.GM20.Section10c
public import GraphMinor.GM20.Section10cProved
public import GraphMinor.GM20.Section10d
public import GraphMinor.GM20.Section10l
public import GraphMinor.GM20.Section11a
public import GraphMinor.GM20.Section3
public import GraphMinor.GM20.Section4a
public import GraphMinor.GM20.Section4b
public import GraphMinor.GM20.Section4c
public import GraphMinor.GM20.Section4d
public import GraphMinor.GM20.Section4e
public import GraphMinor.GM20.Section4f
public import GraphMinor.GM20.Section4g
public import GraphMinor.GM20.Section5a
public import GraphMinor.GM20.Section5d
public import GraphMinor.GM20.Section5g
public import GraphMinor.GM20.Section5j
public import GraphMinor.GM20.Section5k
public import GraphMinor.GM20.Section6b
public import GraphMinor.GM20.Section6c
public import GraphMinor.GM20.Section6d
public import GraphMinor.GM20.Section7a
public import GraphMinor.GM20.Section7b
public import GraphMinor.GM20.Section8b
public import GraphMinor.GM20.Section9h
public import GraphMinor.GM20.Section9hProved

/-!
# Graph Minors XX: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XX. Wagner's conjecture*, J. Combin. Theory Ser. B
**92** (2004), 325–357.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. The docstrings say where the Lean differs from the print, and
`corrections/GM20.md` lists the corrections to the paper.
-/

public section

namespace GraphMinor.GM20

open Set Hypergraph

universe u v u_1 w

/-! ## Section 1. Introduction -/

/-! ## Section 2. Hypergraphs and tangles -/

/-! ## Section 3. Patchworks -/

open GraphMinor.GM18 GraphMinor.GM10 in
/-- **Graph Minors XX, (3.1)** (page 330), which is (6.7) of Graph Minors XVIII: "Let $\Omega$ be a
well-quasi-order, let $\mathcal{F}$ be a well-behaved set of rootless
partial $\Omega$-patchworks, and let $\theta \ge 1$ be an integer. Let $P_i = (G_i, \mu_i,
\Delta_i, \phi_i)$ ($i = 1, 2, \dots$) be a countable sequence of rootless robust
$\Omega$-patchworks. For each $i \ge 1$ let $\lambda_i$ be a tie-breaker in $G_i$; and
suppose that for every tangle $\mathcal{T}$ in $G_i$ of order $\ge \theta$ there is a rooted
location $\mathcal{L}$ in $G_i$ such that $\mathcal{L}$ $\theta$-isolates $\mathcal{T}$ and
$(P_i, \mathcal{L})$ has a heart in $\mathcal{F}$. Then there exist $j > i \ge 1$ such that
$P_i$ is simulated in $P_j$." -/
theorem theorem_3_1 {α : Type u} {β : Type v} [Infinite β] {Ω : Type (max u v)} [Preorder Ω]
    (hΩ : WellQuasiOrderedLE Ω) {𝓕 : Set (PartialPatchwork Ω α β)} (h𝓕 : GM18.WellBehaved 𝓕)
    (hroot : ∀ P ∈ 𝓕, IsRootless P) {θ : ℕ} (hθ : 1 ≤ θ) (P : ℕ → GM04.Patchwork Ω α β)
    (hP : ∀ i, IsRootless (P i) ∧ (P i).IsRobust) (Λ : ℕ → Type) [∀ i, LinearOrder (Λ i)]
    (lam : ∀ i, Hypergraph α β × Hypergraph α β → Λ i)
    (hlam : ∀ i, IsTieBreaker (P i).G.toHypergraph (lam i))
    (h : ∀ i (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (P i).G.toHypergraph θ' 𝒯 → θ ≤ θ' → ∃ ℒ : Set (RootedHypergraph α β),
      IsOmegaPlace (PartialPatchwork.ofPatchwork (P i)) ℒ ∧
      (∃ Q ∈ 𝓕, HasPlaceHeart (PartialPatchwork.ofPatchwork (P i)) ℒ Q) ∧
      GM18.Isolates (P i).G.toHypergraph (lam i) θ 𝒯 (rootedLocationToLocation (P i).G ℒ)) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) :=
  GM20.theorem_3_1_proof hΩ h𝓕 hroot hθ P hP Λ lam hlam h

/-! ## Section 4. Well-behaved sets of patchworks -/

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 Classical in
/-- **Graph Minors XX, (4.1)** (page 330): "If $\mathcal{F}$ is well-behaved, then there exists $N
\ge 0$ such that if $(G, \mu, \Delta)
\in \mathcal{F}$ and $e \in dom(\mu)$ then $|\bar{\mu}(e)| \le N$." We bound the length of the march
`μ(e)`, which
is `|μ̄(e)|`. -/
theorem theorem_4_1 {α : Type u} {β : Type v} {𝓕 : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕) :
    ∃ N, ∀ P ∈ 𝓕, ∀ e ∈ P.dom, (P.μ e).length ≤ N :=
  GM20.theorem_4_1_proof h

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.2)** (page 331): "Let $\mathcal{F}_1, \mathcal{F}_2$ be sets of patchworks
where $\mathcal{F}_1$ is
well-behaved. Suppose that for every well-quasi-order $\Omega_2$ there is a well-quasi-order
$\Omega_1$ and an encoding of the set of all $\Omega_2$-completions of members of
$\mathcal{F}_2$ in the set of all $\Omega_1$-completions of members of $\mathcal{F}_1$. Then
$\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_2 {α : Type u} {β : Type v} {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)}
    (h₁ : WellBehaved 𝓕₁)
    (h : ∀ (Ω₂ : Type (max u v)) [Preorder Ω₂], WellQuasiOrderedLE Ω₂ →
      ∃ (Ω₁ : Type (max u v)) (_ : Preorder Ω₁) (_ : WellQuasiOrderedLE Ω₁) (γ : Patchwork Ω₂ α β →
        Patchwork Ω₁ α β), IsEncoding (completions Ω₁ 𝓕₁) (completions Ω₂ 𝓕₂) γ) :
    WellBehaved 𝓕₂ :=
  GM20.theorem_4_2_proof h₁ h

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.3)** (page 331): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks.
Let $\mathcal{F}_2$ be the set of
all patchworks $P_2 = (G_2, \mu, \Delta)$ such that there exist $(G_1, \mu, \Delta) \in
\mathcal{F}_1$ and $v \in V(G_1) \setminus \bar{\pi}(G_1)$ such that $G_2^- = G_1^-$ and
$\pi(G_2)$ is the concatenation of $\pi(G_1)$ with a new last term $v$ and $v$ is incident
with some edge $e \in dom(\mu)$. Then $\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_3 {α : Type u} {β : Type v} {𝓕₁ : Set (UnlabeledPatchwork α β)}
    (h : WellBehaved 𝓕₁) :
    WellBehaved {P₂ | ∃ P₁ ∈ 𝓕₁, SameBase P₁ P₂ ∧ ∃ v e, P₂.G.roots = P₁.G.roots ++ [v] ∧
    e ∈ P₁.dom ∧ P₁.G.Inc e v} :=
  GM20.theorem_4_3_proof h

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.4)** (page 332): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks,
and let $\mathcal{F}_2$ be the set
of all rootless patchworks $P_2 = (G_2, \mu, \Delta)$ such that there exists $(G_1, \mu,
\Delta) \in \mathcal{F}_1$ with $G_1^- = G_2^-$. Then $\mathcal{F}_2$ is well-behaved." The paper's
reason: "any realization expansion of one
patchwork in another is a realizable expansion of the corresponding patchworks with roots
forgotten". -/
theorem theorem_4_4 {α : Type u} {β : Type v} {𝓕₁ : Set (UnlabeledPatchwork α β)}
    (h : WellBehaved 𝓕₁) :
    WellBehaved {P₂ | P₂.G.roots = [] ∧ ∃ P₁ ∈ 𝓕₁, SameBase P₁ P₂} :=
  GM20.theorem_4_4_proof h

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.5)** (page 332): "Let $\mathcal{F}_1$ be a well-behaved set of active
patchworks, let $k \ge 0$ and let
$\mathcal{F}_2$ be the set of all patchworks $(G_2, \mu, \Delta)$ such that
$|\bar{\pi}(G_2)| \le k$ and there exists $(G_1, \mu, \Delta) \in \mathcal{F}_1$ with $G_1^-
= G_2^-$. Then $\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_5 {α : Type u} {β : Type v} {𝓕₁ : Set (UnlabeledPatchwork α β)}
    (h : WellBehaved 𝓕₁) (ha : ∀ P ∈ 𝓕₁, IsActive P) (k : ℕ) :
    WellBehaved {P₂ | P₂.G.roots.length ≤ k ∧ ∃ P₁ ∈ 𝓕₁, SameBase P₁ P₂} :=
  GM20.theorem_4_5_proof h ha k

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.6)** (page 332): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks,
and let $\mathcal{F}_2$ be a set of
patchworks such that for each $P_2 = (G_2, \mu_2, \Delta_2) \in \mathcal{F}_2$ there exists
$f \in E(G_2)$ such that $P_2 \setminus \{f\} \in \mathcal{F}_1$ and every end of $f$
belongs to $\bar{\pi}(G_2)$. Then $\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_6 {α : Type u} {β : Type v} {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)}
    (h : WellBehaved 𝓕₁)
    (h₂ : ∀ P₂ ∈ 𝓕₂, ∃ f ∈ P₂.G.edgeSet, P₂.deleteEdges {f} ∈ completions Unit 𝓕₁ ∧ ∀ v,
      P₂.G.Inc f v → v ∈ P₂.G.roots) : WellBehaved 𝓕₂ :=
  GM20.theorem_4_6_proof h h₂

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.7)** (page 332): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks
and let $\mathcal{F}_2$ be a set of
patchworks each of which is a 1-vertex extension of a member of $\mathcal{F}_1$. Then
$\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_7 {α : Type u} {β : Type v} {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)}
    (h : WellBehaved 𝓕₁) (h₂ : ∀ P₂ ∈ 𝓕₂, ∃ P₁ ∈ 𝓕₁, ∃ f v, IsOneVertexExtension P₁ P₂ f v) :
    WellBehaved 𝓕₂ :=
  GM20.theorem_4_7_proof h h₂

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.8)** (page 333): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks,
let $k \ge 0$, and let
$\mathcal{F}_2$ be the set of all patchworks $P_2$ such that there exist $P_1 \in
\mathcal{F}_1$ and a sequence* $$ P_1 = P^0, P^1, \dots, P^{k'} = P_2 $$ *where $k' \le k$
and for $1 \le i \le k'$, $P^i$ is a 1-vertex extension of $P^{i-1}$. Then $\mathcal{F}_2$
is well-behaved." -/
theorem theorem_4_8 {α : Type u} {β : Type v} {𝓕₁ : Set (UnlabeledPatchwork α β)}
    (h : WellBehaved 𝓕₁) (k : ℕ) :
    WellBehaved {P₂ | ∃ s : ℕ → UnlabeledPatchwork α β, ∃ k' ≤ k, s 0 ∈ 𝓕₁ ∧ s k' = P₂ ∧
    ∀ i < k', ∃ f v, IsOneVertexExtension (s i) (s (i + 1)) f v} :=
  GM20.theorem_4_8_proof h k

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.9)** (page 333): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks,
let $\theta \ge 0$, and let
$\mathcal{F}_2$ be the set of all patchworks $P_2 = (G_2, \mu_2, \Delta_2)$ such that
$dom(\mu_2) = E(G_2)$ and there exists $W \subseteq V(G_2)$ with $|W| \le \theta$ and $P_2/W
\in \mathcal{F}_1$. Then $\mathcal{F}_2$ is well-behaved."

The Lean proof corrects a step of the paper's proof. See the correction to the proof of (4.9) in
`corrections/GM20.md`. -/
theorem theorem_4_9 {α : Type u} {β : Type v} {𝓕₁ : Set (UnlabeledPatchwork α β)}
    (h : WellBehaved 𝓕₁) (θ : ℕ) :
    WellBehaved {P₂ | P₂.dom = P₂.G.edgeSet ∧ ∃ W : Set α, W.Finite ∧ W.ncard ≤ θ ∧
    W ⊆ P₂.G.vertexSet ∧ P₂.slash W ∈ completions Unit 𝓕₁} :=
  GM20.theorem_4_9_proof h θ

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.10)** (page 334): "Let $\mathcal{F}_1$ be a well-behaved set of removable
patchworks and let $\mathcal{F}_2$ be
a set of patchworks such that for each $P_2 \in \mathcal{F}_2$ some $P_1 \in \mathcal{F}_1$
is a condensation of $P_2$. Then $\mathcal{F}_2$ is well-behaved."

The proof codes pieces by bags and Higman's lemma. It does not call XVIII (5.7), which does not
apply here: see the correction to the proof of (4.10) in `corrections/GM20.md`. Where the paper says
that a result is "proved in the same way as theorem 8.4 of [1]" and omits the proof, the Lean sorts
the edges of each piece into finitely many classes and applies Higman's lemma to their labels. -/
theorem theorem_4_10 {α : Type u} {β : Type v} {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)}
    (h : WellBehaved 𝓕₁) (hrem : ∀ P ∈ 𝓕₁, P.IsRemovable)
    (h₂ : ∀ P₂ ∈ 𝓕₂, ∃ P₁ ∈ 𝓕₁, IsCondensation P₁ P₂) :
    WellBehaved 𝓕₂ :=
  GM20.theorem_4_10_proof h hrem h₂

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.11)** (page 334): "Let $\mathcal{F}_1$ be a well-behaved set of active
patchworks, and let $\mathcal{F}_2$ be
the set of all patchworks $P_2 = (G_2, \mu_2, \Delta_2)$ such that there exists $P_1 = (G_1,
\mu_1, \Delta_1) \in \mathcal{F}_1$ with $G_2 \subseteq G_1$, $\pi(G_2) = \pi(G_1)$, $G_2$
complemented in $G_1$ and $P_2 = P_1|G_2$. Then $\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_11 {α : Type u} {β : Type v} {𝓕₁ : Set (UnlabeledPatchwork α β)}
    (h : WellBehaved 𝓕₁) (ha : ∀ P ∈ 𝓕₁, IsActive P) :
    WellBehaved {P₂ | ∃ P₁ ∈ 𝓕₁, IsComplemented P₁.G P₂.G ∧ P₂.G.roots = P₁.G.roots ∧
    IsCompletionOf (P₁.restrict P₂.G) P₂} :=
  GM20.theorem_4_11_proof h ha

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.12)** (pages 335–336): "Let $\mathcal{F}_1$ be a well-behaved set of
active patchworks, let $k \ge 0$, and let
$\mathcal{F}_2$ be a set of patchworks such that for each $P_2 = (G_2, \mu_2, \Delta_2) \in
\mathcal{F}_2$ there exists $f \in dom(\mu_2)$ with* ... *$\le k$ ends and $P_1 = (G_1, \mu_1,
\Delta_1) \in \mathcal{F}_1$ so that $G_2 \setminus f = G_1 \setminus A$ and $\pi(A) =
\mu_2(f)$ for some complemented rooted hypergraph $A \subseteq G_1$, and $P_2 \setminus
\{f\} = P_1|(G_2 \setminus \{f\})$. Then $\mathcal{F}_2$ is well-behaved."

The proof is the paper's, with the roots changed as in the correction to the proof of (4.12) in
`corrections/GM20.md`. -/
theorem theorem_4_12 {α : Type u} {β : Type v} {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)}
    (h : WellBehaved 𝓕₁) (ha : ∀ P ∈ 𝓕₁, IsActive P) (k : ℕ)
    (h₂ : ∀ P₂ ∈ 𝓕₂, ∃ f ∈ P₂.dom, (P₂.G.ends f).ncard ≤ k ∧ ∃ P₁ ∈ 𝓕₁,
      ∃ (A : RootedHypergraph α β) (hA : IsComplemented P₁.G A), P₂.G.deleteEdges {f} =
      complement P₁.G A hA ∧ A.roots = P₂.μ f ∧
      IsCompletionOf (P₁.restrict (P₂.G.deleteEdges {f})) (P₂.deleteEdges {f})) :
    WellBehaved 𝓕₂ :=
  GM20.theorem_4_12_proof h ha k h₂

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (4.13)** (page 336), with `π(G₂) = π(G₁)`, see the module docstring: "Let
$\mathcal{F}_1$ be a well-behaved set of active patchworks, let $k, w \ge 0$ and let
$\mathcal{F}_2$ be a set of patchworks such that for each $P_2 = (G_2, \mu_2, \Delta_2) \in
\mathcal{F}_2$ there exists $F \subseteq dom(\mu_2)$ with $|F| \le w$ and $P_1 = (G_1,
\mu_1, \Delta_1) \in \mathcal{F}_1$, and a rooted location $\mathcal{L} = \{A_f : f \in F\}$
in $G_1$, such that* - $G_2^- \setminus F = G_1^- \cap \bigcap((G_1 \setminus A)^- : A \in
\mathcal{L})$, - $P_2 \setminus F = P_1|(G_2 \setminus F)$, and - for each $f \in F$,
$\pi(A_f) = \mu_2(f)$ and $f$ has $\le k$ ends. *Then $\mathcal{F}_2$ is well-behaved."

The Lean assumes `P₂.G.roots = P₁.G.roots`, as in (4.12) and its one use. See the correction to
(4.13) in `corrections/GM20.md`. The proof is the paper's: `w` uses of (4.12), after the new edges
get new names. -/
theorem theorem_4_13 {α : Type u} {β : Type v} {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)}
    (h : WellBehaved 𝓕₁) (ha : ∀ P ∈ 𝓕₁, IsActive P) (k w : ℕ)
    (h₂ : ∀ P₂ ∈ 𝓕₂, ∃ F ⊆ P₂.dom, F.ncard ≤ w ∧ ∃ P₁ ∈ 𝓕₁, ∃ A : β → RootedHypergraph α β,
      IsRootedLocation P₁.G (A '' F) ∧ P₂.G.roots = P₁.G.roots ∧ P₂.G.toHypergraph.deleteEdges F =
      rootedLocationCore P₁.G (A '' F) ∧
      IsCompletionOf (P₁.restrict (P₂.G.deleteEdges F)) (P₂.deleteEdges F) ∧ ∀ f ∈ F, (A f).roots =
      P₂.μ f ∧ (P₂.G.ends f).ncard ≤ k) :
    WellBehaved 𝓕₂ :=
  GM20.theorem_4_13_proof h ha k w h₂

/-! ## Section 5. Isolation modulo a subset -/

open GraphMinor.GM18 GraphMinor.GM10 in
/-- **Graph Minors XX, (5.1)** (page 336), first part: "Let $(C, D) \in \mathcal{M}(\mathcal{T}, W,
\theta)$, and let $(A, B)$ be the $(\mathcal{T},
\mathcal{T}')$-distinction for some tangle $\mathcal{T}'$. Then either $A \subseteq C$ and
$D \subseteq B$, or $A \subseteq D$ and $C \subseteq B$, or $C \subseteq A$ and $B \subseteq
D$" -/
theorem theorem_5_1 {α : Type u} {β : Type v} {Λ : Type u_1} [LinearOrder Λ]
    {lam : Hypergraph α β × Hypergraph α β → Λ} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {W : Set (α ⊕ β)} {θ : ℕ} {θ₀ θ' : ℕ}
    {𝒯' : Set (Hypergraph α β × Hypergraph α β)} (hTB : IsTieBreaker G lam) (h𝒯 : IsTangle G θ₀ 𝒯)
    (h𝒯' : IsTangle G θ' 𝒯') {A B C D : Hypergraph α β} (hM : InM lam G 𝒯 W θ C D)
    (hAB : IsDistinction lam 𝒯 𝒯' A B) :
    (A ≤ C ∧ D ≤ B) ∨ (A ≤ D ∧ C ≤ B) ∨ (C ≤ A ∧ B ≤ D) :=
  GM20.theorem_5_1_proof hTB h𝒯 h𝒯' hM hAB

open GraphMinor.GM18 GraphMinor.GM10 in
/-- **Graph Minors XX, (5.2)** (page 337), first part: "If $(A, B), (A', B') \in
\mathcal{M}(\mathcal{T}, W, \theta)$ are distinct then $A \subseteq
B'$" -/
theorem theorem_5_2 {α : Type u} {β : Type v} {Λ : Type u_1} [LinearOrder Λ]
    {lam : Hypergraph α β × Hypergraph α β → Λ} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {W : Set (α ⊕ β)} {θ : ℕ} {θ₀ : ℕ}
    (hTB : IsTieBreaker G lam) (h𝒯 : IsTangle G θ₀ 𝒯) {A B A' B' : Hypergraph α β}
    (hM : InM lam G 𝒯 W θ A B) (hM' : InM lam G 𝒯 W θ A' B') (hne : (A, B) ≠ (A', B')) : A ≤ B' :=
  GM20.theorem_5_2_proof hTB h𝒯 hM hM' hne

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (5.3)** (page 337): "Let $\mathcal{F}$ be a well-behaved set of patchworks
and let $\theta \ge 1$. Then there is
a well-behaved set of patchworks $\mathcal{F}'$ with the following property. Let $P = (G,
\mu, \Delta)$ be a patchwork, let $\lambda$ be a tie-breaker in $G$, let $\mathcal{T}$ be a
tangle in $G$ of order $\ge \theta^2$, let $W \subseteq Z(G)$ with $|W| \le \theta$, let
$\mathcal{L}$ be a fine rooted location in $G$ that $\theta$-isolates $\mathcal{T}$ modulo
$W$, and let $\mathcal{F}$ contain a heart of $(P, \mathcal{L})$. Then there is a rooted
location $\mathcal{L}'$ in $G$ and $W' \subseteq W$ such that* * *$\mathcal{L}'$ is
$W'$-suitable and $\mathcal{F}'$ contains a heart of $(P, \mathcal{L}')$,* * *for each $(A,
B) \in \mathcal{M}(\mathcal{T}, W', \theta)$,* * *$V(A \cap B) \cap V(C) \subseteq
\bar{\pi}(C)$ for each $C \in \mathcal{L}'$, and* * *there is no $(C, D) \in \mathcal{L}'^-$
with $A \subseteq C$ and $D \subseteq B$." -/
theorem theorem_5_3 {α : Type u} {β : Type v} {𝓕 : Set (UnlabeledPatchwork α β)}
    (h𝓕 : WellBehaved 𝓕) {θ : ℕ} (hθ : 1 ≤ θ) :
    ∃ 𝓕' : Set (UnlabeledPatchwork α β), WellBehaved 𝓕' ∧
    ∀ (P : UnlabeledPatchwork α β) (Λ : Type w) [LinearOrder Λ]
      (lam : Hypergraph α β × Hypergraph α β → Λ) (𝒯 : Set (Hypergraph α β × Hypergraph α β))
      (θ₀ : ℕ) (W : Set (α ⊕ β)) (ℒ : Set (RootedHypergraph α β)),
      IsTieBreaker P.G.toHypergraph lam → IsTangle P.G.toHypergraph θ₀ 𝒯 → θ ^ 2 ≤ θ₀ →
      W ⊆ zSet P.G.toHypergraph → W.ncard ≤ θ → IsFine P.G ℒ →
      IsolatesModulo lam 𝒯 W θ P.G ℒ → (∃ Q ∈ 𝓕, HasPatchworkHeart P ℒ Q) →
      ∃ (ℒ' : Set (RootedHypergraph α β)) (W' : Set (α ⊕ β)), W' ⊆ W ∧
        IsSuitable lam 𝒯 W' θ P.G ℒ' ∧ (∃ Q ∈ 𝓕', HasPatchworkHeart P ℒ' Q) ∧
        ∀ ⦃A B⦄, InM lam P.G.toHypergraph 𝒯 W' θ A B →
          (∀ C ∈ ℒ', (A ∩ B).vertexSet ∩ C.vertexSet ⊆ C.rootSet) ∧
          ∀ C ∈ ℒ', ¬ (A ≤ C.toHypergraph ∧ complementHypergraph P.G C ≤ B) :=
  GM20.theorem_5_3_proof h𝓕 hθ

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (5.4)** (page 339):
"**5.4.** *Let $\mathcal{F}$ be a well-behaved set of patchworks, and let $\theta \ge 1$. Then there
is a well-behaved set of patchworks $\mathcal{F}'$ with the following property. Let $P = (G, \mu,
\Delta)$ be a patchwork, let $\lambda$ be a tie-breaker in $G$, let $\mathcal{T}$ be a tangle in $G$
of order $\ge \theta^2$, and let $W \subseteq Z(G)$ with $|W| \le \theta$. Suppose that:*
* *$P$ is removable,*
* *$\mathcal{L}$ is a $W$-suitable rooted location in $G$, such that $\mathcal{F}$ contains a heart
of $(P, \mathcal{L})$,*
* *for each $(A^*, B^*) \in \mathcal{M}(\mathcal{T}, W, \theta)$,*
  * *$V(A^* \cap B^*) \cap V(C) \subseteq \bar{\pi}(C)$ for each $C \in \mathcal{L}$, and*
  * *there is no $(C, D) \in \mathcal{L}^-$ with $A^* \subseteq C$ and $D \subseteq B^*$.*
*Then there is a $W$-suitable rooted location $\mathcal{L}'$ in $G$ such that $\mathcal{F}'$
contains a heart of $(P, \mathcal{L}')$, and for each $C \in \mathcal{L}'$ and each $(A^*, B^*) \in
\mathcal{M}(\mathcal{T}, W, \theta)$, either $C^- \subseteq A^*$ and $B^* \subseteq (G \setminus
C)^-$, or $C^- \subseteq B^*$ and $A^* \subseteq (G \setminus C)^-$.*" -/
theorem theorem_5_4 {α : Type u} {β : Type v} [Infinite β] {𝓕 : Set (UnlabeledPatchwork α β)}
    (h𝓕 : WellBehaved 𝓕) (θ : ℕ) :
    ∃ 𝓕' : Set (UnlabeledPatchwork α β), WellBehaved 𝓕' ∧
    ∀ (P : UnlabeledPatchwork α β) (Λ : Type w) [LinearOrder Λ]
      (lam : Hypergraph α β × Hypergraph α β → Λ) (𝒯 : Set (Hypergraph α β × Hypergraph α β))
      (θ₀ : ℕ) (W : Set (α ⊕ β)) (ℒ : Set (RootedHypergraph α β)),
      IsTieBreaker P.G.toHypergraph lam → IsTangle P.G.toHypergraph θ₀ 𝒯 → θ ^ 2 ≤ θ₀ →
      P.IsRemovable → IsSuitable lam 𝒯 W θ P.G ℒ → (∃ Q ∈ 𝓕, HasPatchworkHeart P ℒ Q) →
      (∀ ⦃A B⦄, InM lam P.G.toHypergraph 𝒯 W θ A B →
        (∀ C ∈ ℒ, (A ∩ B).vertexSet ∩ C.vertexSet ⊆ C.rootSet) ∧
        ∀ C ∈ ℒ, ¬ (A ≤ C.toHypergraph ∧ complementHypergraph P.G C ≤ B)) →
      ∃ ℒ' : Set (RootedHypergraph α β), IsSuitable lam 𝒯 W θ P.G ℒ' ∧
        (∃ Q ∈ 𝓕', HasPatchworkHeart P ℒ' Q) ∧
        ∀ C ∈ ℒ', ∀ ⦃A B⦄, InM lam P.G.toHypergraph 𝒯 W θ A B →
          (C.toHypergraph ≤ A ∧ B ≤ complementHypergraph P.G C) ∨
          (C.toHypergraph ≤ B ∧ A ≤ complementHypergraph P.G C) :=
  GM20.theorem_5_4_proof h𝓕 θ

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (5.5)** (page 340): "Let $\mathcal{F}$ be a well-behaved set of patchworks
and let $\theta \ge 1$. Then there is
a well-behaved set of patchworks $\mathcal{F}'$ with the following property. Let $P = (G,
\mu, \Delta)$ be a patchwork, let $\lambda$ be a tie-breaker in $G$, let $\mathcal{T}$ be a
tangle in $G$ of order $\ge \theta^2$, and let $W \subseteq Z(G)$ with $|W| \le \theta$.
Suppose that* * *$P$ is rootless,* * *$\mathcal{L}$ is a $W$-suitable rooted location in $G$
such that $\mathcal{F}$ contains a heart of $(P, \mathcal{L})$, and* * *for each $C \in
\mathcal{L}$ and each $(A^*, B^*) \in \mathcal{M}(\mathcal{T}, W, \theta)$, either* * *$C^-
\subseteq A^*$ and $B^* \subseteq (G \setminus C)^-$ or* * *$C^- \subseteq B^*$ and $A^*
\subseteq (G \setminus C)^-$.* *Then there is a fine rooted location $\mathcal{L}'$ such
that $\mathcal{L}'$ $\theta^2$-isolates $\mathcal{T}$ and $\mathcal{F}'$ contains a heart of
$(P, \mathcal{L}')$." -/
theorem theorem_5_5 {α : Type u} {β : Type v} [Infinite β] {𝓕 : Set (UnlabeledPatchwork α β)}
    (h𝓕 : WellBehaved 𝓕) {θ : ℕ} (hθ : 1 ≤ θ) :
    ∃ 𝓕' : Set (UnlabeledPatchwork α β), WellBehaved 𝓕' ∧
    ∀ (P : UnlabeledPatchwork α β) (Λ : Type w) [LinearOrder Λ]
      (lam : Hypergraph α β × Hypergraph α β → Λ) (𝒯 : Set (Hypergraph α β × Hypergraph α β))
      (θ₀ : ℕ) (W : Set (α ⊕ β)) (ℒ : Set (RootedHypergraph α β)),
      IsTieBreaker P.G.toHypergraph lam → IsTangle P.G.toHypergraph θ₀ 𝒯 → θ ^ 2 ≤ θ₀ →
      W ⊆ zSet P.G.toHypergraph → W.ncard ≤ θ → IsRootless P →
      IsSuitable lam 𝒯 W θ P.G ℒ → (∃ Q ∈ 𝓕, HasPatchworkHeart P ℒ Q) →
      (∀ C ∈ ℒ, ∀ ⦃A B⦄, InM lam P.G.toHypergraph 𝒯 W θ A B →
        (C.toHypergraph ≤ A ∧ B ≤ complementHypergraph P.G C) ∨
        (C.toHypergraph ≤ B ∧ A ≤ complementHypergraph P.G C)) →
      ∃ ℒ' : Set (RootedHypergraph α β), IsFine P.G ℒ' ∧ IsRootedLocation P.G ℒ' ∧
        Isolates P.G.toHypergraph lam (θ ^ 2) 𝒯 (rootedLocationToLocation P.G ℒ') ∧
        ∃ Q ∈ 𝓕', HasPatchworkHeart P ℒ' Q :=
  GM20.theorem_5_5_proof h𝓕 hθ

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (5.6)** (page 342):
"**5.6.** *Let $\mathcal{F}$ be a well-behaved set of patchworks, and let $\theta \ge 1$. Then there
is a well-behaved set of patchworks $\mathcal{F}'$ with the following property. Let $P = (G, \mu,
\Delta)$ be a rootless removable patchwork, let $\lambda$ be a tie-breaker in $G$, let $\mathcal{T}$
be a tangle in $G$ of order $\ge \theta^2$, and let $W \subseteq Z(G)$ with $|W| \le \theta$.
Suppose that $\mathcal{L}$ is a fine rooted location in $G$ such that $\mathcal{L}$
$\theta$-isolates $\mathcal{T}$ modulo $W$, and $\mathcal{F}$ contains a heart of $(P,
\mathcal{L})$. Then there is a fine rooted location $\mathcal{L}'$ in $G$ such that $\mathcal{L}$
$\theta^2$-isolates $\mathcal{T}$ and $\mathcal{F}'$ contains a heart of $(P, \mathcal{L}')$.*"
(Here "$\mathcal{L}$ $\theta^2$-isolates $\mathcal{T}$" is a misprint in the paper for
"$\mathcal{L}'$ $\theta^2$-isolates $\mathcal{T}$".) -/
theorem theorem_5_6 {α : Type u} {β : Type v} [Infinite β] {𝓕 : Set (UnlabeledPatchwork α β)}
    (h𝓕 : WellBehaved 𝓕) {θ : ℕ} (hθ : 1 ≤ θ) :
    ∃ 𝓕' : Set (UnlabeledPatchwork α β), WellBehaved 𝓕' ∧
    ∀ (P : UnlabeledPatchwork α β) (Λ : Type w) [LinearOrder Λ]
      (lam : Hypergraph α β × Hypergraph α β → Λ) (𝒯 : Set (Hypergraph α β × Hypergraph α β))
      (θ₀ : ℕ) (W : Set (α ⊕ β)) (ℒ : Set (RootedHypergraph α β)),
      IsTieBreaker P.G.toHypergraph lam → IsTangle P.G.toHypergraph θ₀ 𝒯 → θ ^ 2 ≤ θ₀ →
      W ⊆ zSet P.G.toHypergraph → W.ncard ≤ θ → IsRootless P → P.IsRemovable → IsFine P.G ℒ →
      IsolatesModulo lam 𝒯 W θ P.G ℒ → (∃ Q ∈ 𝓕, HasPatchworkHeart P ℒ Q) →
      ∃ ℒ' : Set (RootedHypergraph α β), IsFine P.G ℒ' ∧ IsRootedLocation P.G ℒ' ∧
        Isolates P.G.toHypergraph lam (θ ^ 2) 𝒯 (rootedLocationToLocation P.G ℒ') ∧
        ∃ Q ∈ 𝓕', HasPatchworkHeart P ℒ' Q :=
  GM20.theorem_5_6_proof h𝓕 hθ

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (5.7)** (page 342): "Let $\Omega$ be a well-quasi-order, let $\mathcal{F}$ be
a well-behaved set of patchworks,
and let $\theta \ge 1$. Let $P_i = (G_i, \mu_i, \Delta_i, \phi_i)$ ($i = 1, 2, \dots$) be a
countable sequence of rootless robust $\Omega$-patchworks. For each $i \ge 1$ let
$\lambda_i$ be a tie-breaker in $G_i$; and suppose that for each tangle $\mathcal{T}$ in
$G_i$ of order $\ge \theta$, there exist $W \subseteq Z(G_i)$ with $|W| \le \theta$ and a
fine rooted location $\mathcal{L}$ in $G_i$, such that $\mathcal{L}$ $\theta$-isolates
$\mathcal{T}$ modulo $W$, and $\mathcal{F}$ contains a heart of $((G_i, \mu_i, \Delta_i),
\mathcal{L})$. Then there exist $j > i \ge 1$ such that $P_i$ is simulated in $P_j$." -/
theorem theorem_5_7 {α : Type u} {β : Type v} [Infinite β] {Ω : Type (max u v)} [Preorder Ω]
    (hΩ : WellQuasiOrderedLE Ω) {𝓕 : Set (UnlabeledPatchwork α β)} (h𝓕 : WellBehaved 𝓕) {θ : ℕ}
    (hθ : 1 ≤ θ) (P : ℕ → GM04.Patchwork Ω α β) (hP : ∀ i, IsRootless (P i) ∧ (P i).IsRobust)
    (Λ : ℕ → Type) [∀ i, LinearOrder (Λ i)] (lam : ∀ i, Hypergraph α β × Hypergraph α β → Λ i)
    (hlam : ∀ i, IsTieBreaker (P i).G.toHypergraph (lam i))
    (h : ∀ i (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (P i).G.toHypergraph θ' 𝒯 → θ ≤ θ' →
      ∃ (W : Set (α ⊕ β)) (ℒ : Set (RootedHypergraph α β)), W ⊆ zSet (P i).G.toHypergraph ∧
      W.ncard ≤ θ ∧ IsFine (P i).G ℒ ∧ IsolatesModulo (lam i) 𝒯 W θ (P i).G ℒ ∧ ∃ Q ∈ 𝓕,
      HasPatchworkHeart ((P i).relabel fun _ ↦ ()) ℒ Q) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) :=
  GM20.theorem_5_7_proof hΩ h𝓕 hθ P hP Λ lam hlam h

/-! ## Section 6. Eliminating the tie-breaker -/

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (6.1)** (page 342): "$\lambda$ is a tie-breaker."

Graph Minors XX, (6.1) (page 342): "`λ` is a tie-breaker." -/
theorem theorem_6_1 {α : Type u} {β : Type v} {G : Hypergraph α β} {v : α ⊕ β → ℝ} {f : β}
    (hf : f ∈ G.edgeSet) (hv : IsIndependentWeight G v) :
    IsTieBreaker G (edgeBasedLam G f v) :=
  GM20.theorem_6_1_proof hf hv

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (6.2)** (page 344): "Let $G$ be a rooted hypergraph, and let $\mathcal{T}$ be
a tangle in $G$ of order $\ge 1$.
Let $\lambda$ be an edge-based tie-breaker in $G$ defined by $f, v$ say. Let $\mathcal{L}$
be a rooted location in $G$ with order $< \theta$, and let $W \subseteq V(G)$ be such that
$W \subseteq \bar{\pi}(A)$ for all $A \in \mathcal{L}$. Let $\mathcal{L}/W$ be linked to
$\mathcal{T}/W$. Then $\mathcal{L}$ $\theta$-isolates $\mathcal{T}$ modulo $W \cup \{f\}$." -/
theorem theorem_6_2 {α : Type u} {β : Type v} {G : RootedHypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {W : Set α} {ℒ : Set (RootedHypergraph α β)}
    {θ₀ θ : ℕ} (h𝒯 : IsTangle G.toHypergraph θ₀ 𝒯)
    {lam : Hypergraph α β × Hypergraph α β → ℝ ×ₗ ℝ ×ₗ ℝ} {f : β} {v : α ⊕ β → ℝ}
    (hlam : IsDefinedBy G.toHypergraph lam f v) (hloc : IsRootedLocation G ℒ)
    (hord : ∀ A ∈ ℒ, A.rootSet.ncard < θ) (hW : ∀ A ∈ ℒ, W ⊆ A.rootSet)
    (hlink : IsLinkedTo (G.slash W) (quotientTangle G.toHypergraph 𝒯 W) (locationSlash ℒ W)) :
    IsolatesModulo lam 𝒯 (Sum.inl '' W ∪ {Sum.inr f}) θ G ℒ :=
  GM20.theorem_6_2_proof h𝒯 hlam hloc hord hW hlink

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (6.3)** (page 345): "Let $\Omega$ be a well-quasi-order, let $\mathcal{F}$ be
a well-behaved set of patchworks,
and let $\theta \ge 1$. Let $P_i = (G_i, \mu_i, \Delta_i, \phi_i)$ ($i = 1, 2, \ldots$) be a
countable sequence of rootless robust $\Omega$-patchworks. Suppose that for each tangle
$\mathcal{T}$ in $G_i$ of order $\ge \theta$, there exist $W \subseteq V(G_i)$ with $|W| <
\theta$ and a fine rooted location $\mathcal{L}$ in $G_i$, such that* - *$W \subseteq
\bar{\pi}(A)$ for all $A \in \mathcal{L}$,* - *$\mathcal{L}/W$ is linked to $\mathcal{T}/W$,
and* - *$\mathcal{F}$ contains a heart of $((G_i, \mu_i, \Delta_i), \mathcal{L})$.* *Then
there exist $j > i \ge 1$ such that $P_i$ is simulated in $P_j$." -/
theorem theorem_6_3 {α : Type u} {β : Type v} [Infinite β] {Ω : Type (max u v)} [Preorder Ω]
    (hΩ : WellQuasiOrderedLE Ω) {𝓕 : Set (UnlabeledPatchwork α β)} (h𝓕 : WellBehaved 𝓕) {θ : ℕ}
    (hθ : 1 ≤ θ) (P : ℕ → GM04.Patchwork Ω α β) (hP : ∀ i, IsRootless (P i) ∧ (P i).IsRobust)
    (h : ∀ i (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (P i).G.toHypergraph θ' 𝒯 → θ ≤ θ' → ∃ (W : Set α) (ℒ : Set (RootedHypergraph α β)),
      W ⊆ (P i).G.vertexSet ∧ W.ncard < θ ∧ IsFine (P i).G ℒ ∧ IsRootedLocation (P i).G ℒ ∧
      (∀ A ∈ ℒ, W ⊆ A.rootSet) ∧
      IsLinkedTo ((P i).G.slash W) (quotientTangle (P i).G.toHypergraph 𝒯 W) (locationSlash ℒ W) ∧
      ∃ Q ∈ 𝓕, HasPatchworkHeart ((P i).relabel fun _ ↦ ()) ℒ Q) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) :=
  GM20.theorem_6_3_proof hΩ h𝓕 hθ P hP h

/-! ## Section 7. Another adjustment -/

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (7.1)** (page 346): "Let $P = (G, \mu, \Delta)$ be a free patchwork and $W
\subseteq \bar{\pi}(G)$. Let $K$ be a
grouping with $V(K) = \bar{\pi}(G) \setminus W$. Then $K$ is feasible in $P/W$ if and only
if $K \cup N_W$ is feasible in $P$." -/
theorem theorem_7_1 {α : Type u} {β : Type v} {Ω : Type u_1} {P : Patchwork Ω α β}
    (hfree : IsFree P) {W : Set α} (hW : W ⊆ P.G.rootSet) {K : (⊤ : SimpleGraph α).Subgraph}
    (hg : IsGrouping (P.G.rootSet \ W) K) (hv : K.verts = P.G.rootSet \ W) :
    IsFeasibleGrouping (P.slash W) K ↔ IsFeasibleGrouping P (K ⊔ emptySubgraph W) :=
  GM20.theorem_7_1_proof hfree hW hg hv

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (7.2)** (page 346): "Let $\mathcal{F}$ be a well-behaved set of patchworks
and let $\theta \ge 1$. Then there is
a well-behaved set of patchworks $\mathcal{F}'$ with the following property. Let $P = (G,
\mu, \Delta)$ be a free patchwork, let $\mathcal{T}$ be a tangle in $G$ of order $\ge
\theta$, let $W \subseteq V(G)$ with $|W| < \theta$, and let $\mathcal{L}$ be a fine rooted
location in $G/W$ such that $\mathcal{L}$ is linked to $\mathcal{T}/W$, and $\mathcal{F}$
contains a heart of $(P/W, \mathcal{L})$. Then there is a fine rooted location
$\mathcal{L}'$ in $G$ such that* - *$W \subseteq \bar{\pi}(A)$ for all $A \in
\mathcal{L}'$,* - *$\mathcal{L}'/W = \mathcal{L}$ and hence is linked to $\mathcal{T}/W$,
and* - *$\mathcal{F}'$ contains a heart of $(P, \mathcal{L}')$." -/
theorem theorem_7_2 {α : Type u} {β : Type v} {𝓕 : Set (UnlabeledPatchwork α β)}
    (h𝓕 : WellBehaved 𝓕) (θ : ℕ) :
    ∃ 𝓕' : Set (UnlabeledPatchwork α β), WellBehaved 𝓕' ∧
    ∀ (P : UnlabeledPatchwork α β), IsFree P →
    ∀ (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle P.G.toHypergraph θ' 𝒯 →
      θ ≤ θ' → ∀ W : Set α, W ⊆ P.G.vertexSet → W.ncard < θ →
      ∀ ℒ : Set (RootedHypergraph α β), IsFine (P.G.slash W) ℒ →
        (∃ Q ∈ 𝓕, HasPatchworkHeart (P.slash W) ℒ Q) →
        ∃ ℒ' : Set (RootedHypergraph α β), IsFine P.G ℒ' ∧ IsRootedLocation P.G ℒ' ∧
          (∀ A ∈ ℒ', W ⊆ A.rootSet) ∧ locationSlash ℒ' W = ℒ ∧
          ∃ Q ∈ 𝓕', HasPatchworkHeart P ℒ' Q :=
  GM20.theorem_7_2_proof h𝓕 θ

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (7.3)** (page 347): "Let $\Omega$ be a well-quasi-order, let $\mathcal{F}$ be
a well-behaved set of patchworks,
and let $\theta \ge 1$. Let $P_i = (G_i, \mu_i, \Delta_i, \phi_i)$ ($i = 1, 2, \ldots$) be a
countable sequence of free rootless $\Omega$-patchworks. Suppose that for each tangle
$\mathcal{T}$ in $G_i$ of order $\ge \theta$, there exist $W \subseteq V(G_i)$ with $|W| <
\theta$ and a fine rooted location $\mathcal{L}$ in $G/W$, such that $\mathcal{L}$ is linked
to $\mathcal{T}/W$, and $\mathcal{F}$ contains a heart of $((G_i, \mu_i, \Delta_i)/W,
\mathcal{L})$. Then there exist $j > i \ge 1$ such that $P_i$ is simulated in $P_j$." -/
theorem theorem_7_3 {α : Type u} {β : Type v} [Infinite β] {Ω : Type (max u v)} [Preorder Ω]
    (hΩ : WellQuasiOrderedLE Ω) {𝓕 : Set (UnlabeledPatchwork α β)} (h𝓕 : WellBehaved 𝓕) {θ : ℕ}
    (hθ : 1 ≤ θ) (P : ℕ → GM04.Patchwork Ω α β) (hfree : ∀ i, IsFree (P i))
    (hroot : ∀ i, IsRootless (P i))
    (h : ∀ i (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (P i).G.toHypergraph θ' 𝒯 → θ ≤ θ' → ∃ (W : Set α) (ℒ : Set (RootedHypergraph α β)),
      W ⊆ (P i).G.vertexSet ∧ W.ncard < θ ∧ IsFine ((P i).G.slash W) ℒ ∧
      IsLinkedTo ((P i).G.slash W) (quotientTangle (P i).G.toHypergraph 𝒯 W) ℒ ∧ ∃ Q ∈ 𝓕,
      HasPatchworkHeart (((P i).relabel fun _ ↦ ()).slash W) ℒ Q) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) :=
  GM20.theorem_7_3_proof hΩ h𝓕 hθ P hfree hroot h

/-! ## Section 8. Surfaces and paintings -/

open Topology GraphMinor.Surface Thin GraphMinor.GM04 GraphMinor.GM18 GraphMinor.GM10 in
/-- **Graph Minors XX, (8.1)** (page 348): "Let $\Sigma$ be a surface and let $\Omega$ be a
well-quasi-order. For each $i \ge 1$ let $\Gamma_i$ be a 3-connected painting in $\Sigma$ and let
$\phi_i : \mathcal{C}(\Gamma_i) \to E(\Omega)$ be a function. Then there exist $j > i \ge 1$ and a
linear inflation $\zeta$ of $\Gamma_i$ in $\Gamma_j$ such that $\phi_i(c) \le \phi_j(\zeta(c))$ for
each $c \in \mathcal{C}(\Gamma_i)$."

Graph Minors XX, (8.1) (page 348), from (2.1) of Graph Minors XIX and `PushOffStatement`. -/
theorem theorem_8_1 (S : Type) [TopologicalSpace S] {Ω : Type w} [Preorder Ω] (hS : IsSurface S)
    (hc : ConnectedSpace S) (hΩ : WellQuasiOrderedLE Ω) (Γ : ℕ → Painting S) (φ : ℕ → Set S → Ω)
    (h3 : ∀ i, (Γ i).IsThreeConnected) :
    ∃ i j, i < j ∧ ∃ (ζn : S → Set S) (ζc : Set S → Set S), IsLinearInflation (Γ i) (Γ j) ζn ζc ∧
    ∀ c ∈ (Γ i).C, φ i c ≤ φ j (ζc c) :=
  GM20.theorem_8_1_proof S hS hc hΩ Γ φ h3

/-! ## Section 9. Patchworks from a surface -/

open Topology GraphMinor.Surface GraphMinor.GM04 GraphMinor.GM18 GraphMinor.GM10 in
/-- **Graph Minors XX, (9.1)** (page 349): "For every graded surface $(\Sigma, \rho)$, the set of
all $(\Sigma, \rho)$-hulled patchworks is well-behaved." -/
theorem theorem_9_1 {α : Type u} {β : Type v} (X : GradedSurface) :
    WellBehaved {P : UnlabeledPatchwork α β | IsHulled X P} :=
  GM20.theorem_9_1_proof X

/-! ## Section 10. Excluding a minor -/

open GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (10.1)** (page 353): "Let* $P = (G, \mu, \Delta)$ *be a free patchwork, and
let* $C$ *be a subgraph of* $sk(G)$.
*Then there is a realization* $H$ *of* $P$ *such that for all* $x, y \in V(C)$, $x$ *and*
$y$ *are connected in* $C$ *if and only if they are connected in* $H$." A vertex of `G` outside
`V(C)` is
here a vertex of `C` with no edges, so the statement covers all of `V(G)`. -/
theorem theorem_10_1 {α : Type u} {β : Type v} {Ω : Type u_1} {P : Patchwork Ω α β}
    (hfree : IsFree P) {C : SimpleGraph α} (hC : C ≤ P.G.toHypergraph.skeleton) :
    ∃ H, P.IsRealization H ∧ ∀ x ∈ P.G.vertexSet, ∀ y ∈ P.G.vertexSet,
    sameComponent H x y ↔ C.Reachable x y :=
  GM20.theorem_10_1_proof hfree hC

open Topology GraphMinor.Surface GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (10.2)** (page 354): "Let* $(P, \mathcal{L})$ *be* $(\Sigma, \rho)$*-shelled.
Then it has a heart which is*
$(\Sigma, \rho)$*-hulled." -/
theorem theorem_10_2 {α : Type u} {β : Type v} {X : GradedSurface} {P : UnlabeledPatchwork α β}
    (hfree : IsFree P) (hroot : P.G.roots = []) {ℒ : Set (RootedHypergraph α β)}
    (hs : IsShelled X P ℒ) :
    ∃ P', HasPatchworkHeart P ℒ P' ∧ IsHulled X P' :=
  GM20.theorem_10_2_proof hfree hroot hs

open Topology GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM20.GM17 GraphMinor.GM04 in
/-- **Graph Minors XX, (10.3)** (page 354): "For every graph* $H$ *there exist* $\theta \ge 1$ *and
a set* $\mathcal{S}$ *of graded
surfaces, finite up to homeomorphism, with the following property. Let* $P = (G, \mu,
\Delta)$ *be a rootless free patchwork, and let* $\mathcal{T}$ *be a tangle in* $G$ *of
order* $\ge \theta$ *controlling no* $H$*-minor of* $sk(G)$. *Then there exist* $W \subseteq
V(G)$ *with* $|W| < \theta$ *and a fine rooted location* $\mathcal{L}$ *in* $G/W$, *such
that* * $(P/W, \mathcal{L})$ *is* $(\Sigma, \rho)$*-shelled for some* $(\Sigma, \rho) \in
\mathcal{S}$, *and* * $\mathcal{L}$ *is linked to* $\mathcal{T}/W$." Here `𝒮` is a finite set of
representatives, and the order `θ` is at least `z + 6p + 9`, so that the standing hypotheses of
Sections
8, 9, 11 of Graph Minors XVII hold. -/
theorem theorem_10_3 {α' β' : Type} (H : Hypergraph α' β') (hH : H.IsGraph) :
    ∃ (θ : ℕ) (𝒮 : Set GradedSurface), 1 ≤ θ ∧ 𝒮.Finite ∧
    ∀ {α : Type u} {β : Type v} [Infinite β] (P : UnlabeledPatchwork α β), IsFree P → P.G.roots =
    [] → ∀ (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle P.G.toHypergraph θ' 𝒯 →
    θ ≤ θ' → ¬ ControlsMinor P.G.toHypergraph 𝒯 H → ∃ W ⊆ P.G.vertexSet, W.ncard < θ ∧
    ∃ ℒ : Set (RootedHypergraph α β), IsFine (P.G.slash W) ℒ ∧
    (∃ X ∈ 𝒮, IsShelled X (P.slash W) ℒ) ∧
    IsLinkedTo (P.G.slash W) (quotientTangle P.G.toHypergraph 𝒯 W) ℒ :=
  GM20.theorem_10_3_proof H hH

open Topology GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (10.4)** (page 355): "Let* $\Omega$ *be a well-quasi-order and let* $p \ge
0$. *Let* $P_i = (G_i, \mu_i, \Delta_i,
\phi_i)$ $(i = 1, 2, \dots)$ *be a countable sequence of free rootless* $\Omega$*-patchworks
such that for all* $i \ge 1$, $sk(G_i^-)$ *has no* $K_p$ *minor. Then there exist* $j > i
\ge 1$ *such that* $P_i$ *is simulated in* $P_j$." -/
theorem theorem_10_4 {α : Type u} {β : Type v} [Infinite β] {Ω : Type (max u v)} [Preorder Ω]
    (hΩ : WellQuasiOrderedLE Ω) (p : ℕ) (P : ℕ → GM04.Patchwork Ω α β) (hfree : ∀ i, IsFree (P i))
    (hroot : ∀ i, IsRootless (P i)) (hmin : ∀ i, ¬ HasCliqueMinor (P i).G.toHypergraph p) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) :=
  GM20.theorem_10_4_proof hΩ p P hfree hroot hmin

open Graph GraphMinor.GM18 GraphMinor.GM04 in
/-- **Graph Minors XX, (10.5)** (page 355):
"**10.5.** *Let* $G_i$ $(i = 1, 2, \dots)$ *be a countable sequence of directed graphs. Then there
exist* $j > i \ge 1$ *such that* $G_i$ *is isomorphic to a minor of* $G_j$."

The Lean proof corrects a step of the paper's proof. See the correction to the proof of (10.5) in
`corrections/GM20.md`. -/
theorem theorem_10_5 {α : Type u} {β : Type v} (G : ℕ → Digraph α β)
    (hV : ∀ n, V((G n).toGraph).Finite) (hE : ∀ n, E((G n).toGraph).Finite) :
    ∃ i j, i < j ∧ (G i).IsIsoMinor (G j) :=
  GM20.theorem_10_5_proof G hV hE

open Graph GraphMinor.GM18 GraphMinor.GM04 in
/-- Graph Minors XX, Section 10 (page 355), the standard form of Wagner's conjecture for undirected
graphs ("As a corollary, we deduce the following form of Wagner’s conjecture for directed graphs
(which immediately implies the standard form of the conjecture for undirected graphs)."):
for every countable sequence `Gᵢ` of finite undirected graphs, there exist `j > i` such that `Gᵢ` is
isomorphic to a minor of `Gⱼ`. -/
theorem wagner_conjecture_undirected {α : Type u} {β : Type v} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) :=
  GM20.wagner_conjecture_undirected_proof G hV hE

/-! ## Section 11. A refinement -/

open Topology GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (11.1)** (page 356): "For every* $p \ge 0$, *there exist* $\theta > 0$ *and a
well-behaved set of patchworks*
$\mathcal{F}$ *with the following property. Let* $P = (G, \mu, \Delta)$ *be a rootless free
patchwork, and let* $\mathcal{T}$ *be a tangle in* $G$ *of order* $\ge \theta$, *controlling
no* $K_p$*-minor of* $sk(G^-)$. *Then there is a fine rooted location* $\mathcal{L}$ *in*
$G$ *such that* * $(P, \mathcal{L})$ *has a heart in* $\mathcal{F}$, *and* * $\mathcal{L}$
$\theta$*-isolates* $\mathcal{T}$ *for every edge-based tie-breaker of* $G$."

The location of the proof depends on the tie-breaker, so here `ℒ` is chosen after `λ`. This is the
form that the proof gives and that (11.2) uses. -/
theorem theorem_11_1 {α : Type u} {β : Type v} [Infinite β] (p : ℕ) :
    ∃ (θ : ℕ) (𝓕 : Set (UnlabeledPatchwork α β)), 0 < θ ∧ WellBehaved 𝓕 ∧
    ∀ P : UnlabeledPatchwork α β, IsFree P → P.G.roots = [] →
    ∀ (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle P.G.toHypergraph θ' 𝒯 →
      θ ≤ θ' → ¬ ControlsMinor P.G.toHypergraph 𝒯 (completeHypergraph p) →
      ∀ lam : Hypergraph α β × Hypergraph α β → ℝ ×ₗ ℝ ×ₗ ℝ, IsEdgeBased P.G.toHypergraph lam →
      ∃ ℒ : Set (RootedHypergraph α β), IsFine P.G ℒ ∧ IsRootedLocation P.G ℒ ∧
        (∃ Q ∈ 𝓕, HasPatchworkHeart P ℒ Q) ∧
        Isolates P.G.toHypergraph lam θ 𝒯 (rootedLocationToLocation P.G ℒ) :=
  GM20.theorem_11_1_proof p

open Topology GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM18 GraphMinor.GM10 GraphMinor.GM04 in
/-- **Graph Minors XX, (11.2)** (pages 356–357): "Let* $\Omega$ *be a well-quasi-order, let*
$\mathcal{F}$ *be a well-behaved set of partial*
$\Omega$*-patchworks, and let* $\theta \ge 1$ *and* $p \ge 0$. *Let* $P_i = (G_i, \mu_i,
\Delta_i, \phi_i)$ $(i = 1, 2, \dots)$ *be a countable sequence of free rootless*
$\Omega$*-patchworks. For each* $i \ge 1$, *let* $\lambda_i$ *be an edge-based tie-breaker
in* $G_i$. ... *Suppose that for each $i \ge 1$ and each tangle $\mathcal{T}$ in $G_i$ of order
$\ge \theta$ which controls a $K_p$-minor of $sk(G_i^-)$, there is a rooted location
$\mathcal{L}$ in $G_i$ which $\theta$-isolates $\mathcal{T}$ such that $(P_i, \mathcal{L})$
has a heart in $\mathcal{F}$. Then there exist $j > i \ge 1$ such that $P_i$ is simulated in
$P_j$." -/
theorem theorem_11_2 {α : Type u} {β : Type v} [Infinite β] {Ω : Type (max u v)} [Preorder Ω]
    (hΩ : WellQuasiOrderedLE Ω) {𝓕 : Set (PartialPatchwork Ω α β)} (h𝓕 : GM18.WellBehaved 𝓕) {θ : ℕ}
    (hθ : 1 ≤ θ) (p : ℕ) (P : ℕ → GM04.Patchwork Ω α β) (hfree : ∀ i, IsFree (P i))
    (hroot : ∀ i, IsRootless (P i)) (lam : ∀ _ : ℕ, Hypergraph α β × Hypergraph α β → ℝ ×ₗ ℝ ×ₗ ℝ)
    (hlam : ∀ i, IsEdgeBased (P i).G.toHypergraph (lam i))
    (h : ∀ i (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (P i).G.toHypergraph θ' 𝒯 → θ ≤ θ' →
      ControlsMinor (P i).G.toHypergraph 𝒯 (completeHypergraph p) →
      ∃ ℒ : Set (RootedHypergraph α β), IsOmegaPlace (PartialPatchwork.ofPatchwork (P i)) ℒ ∧
      (∃ Q ∈ 𝓕, HasPlaceHeart (PartialPatchwork.ofPatchwork (P i)) ℒ Q) ∧
      GM18.Isolates (P i).G.toHypergraph (lam i) θ 𝒯 (rootedLocationToLocation (P i).G ℒ)) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) :=
  GM20.theorem_11_2_proof hΩ h𝓕 hθ p P hfree hroot lam hlam h

end GraphMinor.GM20
