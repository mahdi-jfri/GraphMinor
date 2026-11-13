module

public import GraphMinor.GM18.Section2
public import GraphMinor.GM18.Section3
public import GraphMinor.GM18.Section4
public import GraphMinor.GM18.Section5
public import GraphMinor.GM18.Section5Part1
public import GraphMinor.GM18.Section5Part2
public import GraphMinor.GM18.Section6
public import GraphMinor.GM18.Section6Part1
public import GraphMinor.GM18.Section6Part2
public import GraphMinor.GM18.Section6Stars
public import GraphMinor.GM18.Section7

/-!
# Graph Minors XVIII: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XVIII. Tree-decompositions and well-quasi-ordering*,
J. Combin. Theory Ser. B **89** (2003), 77–108.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. The docstrings say where the Lean differs from the print, and
`corrections/GM18.md` lists the corrections to the paper.
-/

public section

namespace GraphMinor.GM18

open Hypergraph SimpleGraph

universe u v u_1 w u_2 u_3 u_4 u_5 u_6 u_7 w'

/-! ## Section 1. Introduction -/

/-! ## Section 2. Hypergraphs, tangles and tree-decompositions -/

/-- **Graph Minors XVIII, (2.1)** (page 79):
"Let $G$ be a hypergraph, let $G' \subseteq G$, and let $\mathcal{T}'$ be a tangle in $G'$ of
order $\theta$. Let $\mathcal{T}$ be the set of all separations $(A, B)$ of $G$ of order
$<\theta$ such that $(A \cap G', B \cap G') \in \mathcal{T}'$. Then $\mathcal{T}$ is a
tangle in $G$ of order $\theta$." -/
theorem theorem_2_1 {α : Type u} {β : Type v} {G G' : Hypergraph α β} (hG' : G' ≤ G) {θ : ℕ}
    {𝒯' : Set (Hypergraph α β × Hypergraph α β)} (h𝒯' : GM10.IsTangle G' θ 𝒯') :
    GM10.IsTangle G θ
    {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧
      (p.1 ∩ G', p.2 ∩ G') ∈ 𝒯'} :=
  theorem_2_1_proof hG' h𝒯'

/-- **Graph Minors XVIII, (2.2)** (page 79):
"**2.2.** *Let $G$ be a hypergraph with no tangle of order $\ge \theta$, where $\theta \ge 1$.
Then $G$ has tree-width $\le \frac{3}{2}\theta$.*" -/
theorem theorem_2_2 {α : Type u} {β : Type v} (G : Hypergraph α β) {θ : ℕ} (hθ : 1 ≤ θ)
    (hno : ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄, GM10.IsTangle G θ' 𝒯 → θ' < θ) :
    2 * GM10.treeWidth G ≤ 3 * (θ : ℤ) :=
  theorem_2_2_proof G hθ hno

open Classical in
/-- **Graph Minors XVIII, (2.3)** (page 80): "Let $\mathcal{L} = \{(A_1, B_1), \dots, (A_n, B_n)\}$
be a location in a hypergraph $G$. Then"

Combined statement of (2.3.1), (2.3.2), and (2.3.3). -/
theorem theorem_2_3 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ) :
    ((∀ ⦃p₁⦄, p₁ ∈ ℒ → ∀ ⦃p₂⦄, p₂ ∈ ℒ → p₁ ≠ p₂ → Disjoint p₁.1.edgeSet p₂.1.edgeSet) ∧
      (∀ ⦃p⦄, p ∈ ℒ → Disjoint p.1.edgeSet (GM10.locationCore G ℒ).edgeSet) ∧
      GM10.locationCore G ℒ ∪ Hypergraph.biUnion hℒ.finite.toFinset Prod.fst = G) ∧
    (∀ ⦃p⦄, p ∈ ℒ →
      p.2 = GM10.locationCore G ℒ ∪
        Hypergraph.biUnion (hℒ.finite.toFinset.filter (· ≠ p)) Prod.fst ∧
      p.1 ∩ GM10.locationCore G ℒ = p.1 ∩ p.2) ∧
    (∀ ⦃p₁⦄, p₁ ∈ ℒ → ∀ ⦃p₂⦄, p₂ ∈ ℒ → p₁ ≠ p₂ →
      p₁.1 ∩ p₂.1 ≤ GM10.locationCore G ℒ ∧
      (p₁.1 ∩ p₂.1).vertexSet =
        (p₁.1 ∩ p₁.2).vertexSet ∩ (p₂.1 ∩ p₂.2).vertexSet ∩
          (GM10.locationCore G ℒ).vertexSet) :=
  theorem_2_3_proof hℒ

/-- **Graph Minors XVIII, (2.4)** (page 80):
"**2.4.** *Let $(T, \tau)$ be a tree-decomposition of a hypergraph $G$, let $t_0 \in V(T)$ and let
$e_1, \dots, e_k$ be the edges of $T$ incident with $t_0$. For $1 \le i \le k$ let the components
of $T \setminus e_i$ be $T_i, T'_i$, where $t_0 \in V(T'_i)$. Then*
$$\{(\tau \times T_i, \tau \times T'_i): 1 \le i \le k\}$$
*is a location.*" -/
theorem theorem_2_4 {α : Type u} {β : Type v} {ι : Type u_1} [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hD : GM10.IsTreeDecomposition G T τ) (t₀ : ι) :
    GM10.IsLocation G (vertexLocation T τ t₀) :=
  theorem_2_4_proof hD t₀

/-- **Graph Minors XVIII, (2.5)** (page 80):
"Let $(T, \tau)$ be a tree-decomposition of a hypergraph $G$, and let $t \in V(T)$. Let
$\mathcal{L}$ be the location of $t$ in $(T, \tau)$; then $\tau(t) = M(G, \mathcal{L})$." -/
theorem theorem_2_5 {α : Type u} {β : Type v} {ι : Type u_1} [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hD : GM10.IsTreeDecomposition G T τ) (t₀ : ι) :
    τ t₀ = GM10.locationCore G (vertexLocation T τ t₀) :=
  theorem_2_5_proof hD t₀

/-- **Graph Minors XVIII, (2.6)** (page 81):
"Let $\mathscr{T}_1, \dots, \mathscr{T}_n$ be distinct tangles of order $\theta$ in a
hypergraph $G$ with $n \ge 1$, and let $\lambda$ be a tie-breaker. Then there is a
tree-decomposition $(T, \tau)$ of $G$ where $V(T) = \{t_1, \dots, t_n\}$, with the following
properties:* 1. *if $e \in E(T)$ and $T_1, T_2$ are the components of $T \setminus e$ and $1
\le i \le n$ and $t_i \in V(T_2)$ then $(\tau \times T_1, \tau \times T_2) \in
\mathscr{T}_i$,* 2. *for $1 \le i < j \le n$, let $e$ be the edge of the path of $T$ between
$t_i, t_j$ making separations of minimum $\lambda$-order; then these separations are the
$(\mathscr{T}_i, \mathscr{T}_j)$- and $(\mathscr{T}_j, \mathscr{T}_i)$-distinctions." -/
theorem theorem_2_6 {α : Type u} {β : Type v} {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → Λ) (θ : ℕ)
    (𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)) (hn : 1 ≤ n)
    (hlam : GM10.IsTieBreaker G lam) (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i))
    (hdist : Function.Injective 𝒯) :
    ∃ (T : SimpleGraph (Fin n)) (τ : Fin n → Hypergraph α β),
    IsStandardDecomposition G lam 𝒯 T τ :=
  theorem_2_6_proof G lam θ 𝒯 hn hlam h𝒯 hdist

/-- **Graph Minors XVIII, (2.7)** (page 81):
"Let $\mathscr{T}_1, \dots, \mathscr{T}_n$ be distinct tangles of order $\theta$ in a
hypergraph $G$ with $n \ge 1$, and let $\lambda$ be a tie-breaker. Let $(T, \tau)$ be as in
2.6. Then $(T, \tau)$ is proper and rotund, and every separation made by an edge of $T$
under $(T, \tau)$ is robust." -/
theorem theorem_2_7 {α : Type u} {β : Type v} {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ} {θ : ℕ}
    {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)} {T : SimpleGraph (Fin n)}
    {τ : Fin n → Hypergraph α β} (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i)) (hstd : IsStandardDecomposition G lam 𝒯 T τ) :
    IsProper G T τ ∧
    IsRotund G T τ ∧
    (∀ ⦃e : Sym2 (Fin n)⦄, e ∈ T.edgeSet → ∀ ⦃A B : Hypergraph α β⦄,
      GM10.MakesSeparation T τ e A B → GM10.IsRobust G A B) :=
  theorem_2_7_proof hlam h𝒯 hstd

/-! ## Section 3. Tree-width of a location -/

/-- **Graph Minors XVIII, (3.1)** (page 82):
"Let $(A, B)$ be a separation of a hypergraph $G$, and let $(A, B')$ be a separation of a
hypergraph $G'$, with $A \cap B = A \cap B'$. Then $(A, B)$ is titanic if and only if $(A,
B')$ is titanic." -/
theorem theorem_3_1 {α : Type u} {β : Type v} {G G' A B B' : Hypergraph α β}
    (hAB : G.IsSeparation A B) (hAB' : G'.IsSeparation A B') (hinter : A ∩ B = A ∩ B') :
    GM10.IsTitanic G A B ↔ GM10.IsTitanic G' A B' :=
  theorem_3_1_proof hAB hAB' hinter

/-- **Graph Minors XVIII, (3.2)** (page 82):
"Let $(C, D)$ be a separation of a hypergraph $G$, and let $(C', D)$ be a titanic separation
of a hypergraph $G'$, with $V(C \cap D) = V(C' \cap D)$. Let $\mathscr{T}$ be a tangle in
$G$ of order $\theta \ge 2$ with $(C, D) \in \mathscr{T}$. Let $\mathscr{T}'$ be the set of
all separations $(A', B')$ of $G'$ of order $< \theta$ such that there exists $(A, B) \in
\mathscr{T}$ with $E(A \cap D) = E(A' \cap D)$. Then $\mathscr{T}'$ is a tangle in $G'$ of
order $\theta$." -/
theorem theorem_3_2 {α : Type u} {β : Type v} {G G' C C' D : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ} (hCD : G.IsSeparation C D)
    (hC'D : GM10.IsTitanic G' C' D) (hV : (C ∩ D).vertexSet = (C' ∩ D).vertexSet)
    (h𝒯 : GM10.IsTangle G θ 𝒯) (hθ : 2 ≤ θ) (hmem : (C, D) ∈ 𝒯) :
    GM10.IsTangle G' θ (GM10.titanicTransferredTangle G' D 𝒯 θ) :=
  theorem_3_2_proof hCD hC'D hV h𝒯 hθ hmem

/-- **Graph Minors XVIII, (3.3)** (page 82):
"**3.3.** *Let $\mathscr{T}$ be a tangle of order $\ge \theta$ in a hypergraph $G$ and let
$(B, A) \in \mathscr{T}$ be linked to $\mathscr{T}$ and have order $\le \frac{3}{4}\theta$.
Then $(A, B)$ is titanic.*"

The tangle has order `θ' ≥ θ`. Proved from the case `θ' = θ` (`theorem_3_3_proof`), since
`4 * separationOrder B A ≤ 3 * θ ≤ 3 * θ'`. -/
theorem theorem_3_3 {α : Type u} {β : Type v} {G A B : Hypergraph α β} {θ θ' : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : GM10.IsTangle G θ' 𝒯) (hθ : θ ≤ θ')
    (hlink : IsLinkedTo 𝒯 B A) (hord : 4 * separationOrder B A ≤ 3 * θ) :
    GM10.IsTitanic G A B :=
  theorem_3_3_proof h𝒯 hlink (hord.trans (Nat.mul_le_mul_left 3 hθ))

/-- **Graph Minors XVIII, (3.4)** (page 84):
"**3.4.** *Let $\mathscr{L}$ be a location in a hypergraph $G$, such that each
$(A, B) \in \mathscr{L}$ is titanic, and $\mathscr{L}$ has order $< \theta$, where $\theta \ge 2$.
Then either there is a tangle $\mathscr{T}$ in $G$ of order $\theta$ with
$\mathscr{L} \subseteq \mathscr{T}$, or $\mathscr{L}$ has tree-width $\le \frac{3}{2}\theta$.*" -/
theorem theorem_3_4 {α : Type u} {β : Type v} {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    (htitanic : ∀ ⦃p⦄, p ∈ ℒ → GM10.IsTitanic G p.1 p.2) {θ : ℕ} (hθ : 2 ≤ θ)
    (hord : locationOrder ℒ < θ) :
    (∃ 𝒯, GM10.IsTangle G θ 𝒯 ∧ ℒ ⊆ 𝒯) ∨
    2 * locationTreeWidth G ℒ ≤ 3 * (θ : ℤ) :=
  theorem_3_4_proof hℒ htitanic hθ hord

/-! ## Section 4. Isolating locations -/

/-- **Graph Minors XVIII, (4.1)** (page 85, M. Saks):
"Let $T$ be a tree and let $\le$ be some linear order on $E(T)$. For each $t \in V(T)$, let
$T_t$ be a subtree of $T$ such that* - *$t \in V(T_t)$,* - *if $e \in E(T)$ has one end in
$V(T_t)$ and the other end in $V(T) \setminus V(T_t)$ and $f$ is an edge of the path of $T$
with first vertex $t$ and last edge $e$, then $e \le f$.* *Then there exists $I \subseteq
V(T)$ such that the sets $V(T_t)$ ($t \in I$) form a partition of $V(T)$." -/
theorem theorem_4_1 {ι : Type u_1} [Fintype ι] [Nonempty ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {Λ : Type*} [LinearOrder Λ] (μ : Sym2 ι → Λ)
    (he_inj : ∀ ⦃e₁ e₂ : Sym2 ι⦄, e₁ ∈ T.edgeSet → e₂ ∈ T.edgeSet → μ e₁ = μ e₂ → e₁ = e₂)
    (sub : ι → Set ι) (ht_mem : ∀ t : ι, t ∈ sub t) (hsub_conv : ∀ t : ι, IsTreeConvex T (sub t))
    (hsub_ord : ∀ (t u v : ι), u ∈ sub t → v ∉ sub t → T.Adj u v → ∀ x y : ι,
      Thomas.OnTreePathEdge T t v x y → μ s(u, v) ≤ μ s(x, y)) :
    ∃ I : Set ι, (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (sub i) (sub j)) ∧
    (⋃ i ∈ I, sub i) = Set.univ :=
  theorem_4_1_proof hT μ he_inj sub ht_mem hsub_conv hsub_ord

/-- **Graph Minors XVIII, (4.2)** (page 85):
"Let $\mathcal{T}_j$ ($j \in J$) be distinct tangles of order $\theta$ in a hypergraph $G$,
let $\lambda$ be a tie-breaker in $G$, and for each $j \in J$ let $\mathcal{L}_j \subseteq
\mathcal{T}_j$ be a location which $\theta$-isolates $\mathcal{T}_j$ with respect to
$\lambda$. Then there exists $I \subseteq J$ such that for every $j \in J$ there is a unique
$i \in I$ with $\mathcal{L}_i \subseteq \mathcal{T}_j$." -/
theorem theorem_4_2 {α : Type u} {β : Type v} {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ} {θ : ℕ}
    {𝒯 L : Fin n → Set (Hypergraph α β × Hypergraph α β)} (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i)) (hdist : Function.Injective 𝒯)
    (hiso : ∀ i : Fin n, Isolates G lam θ (𝒯 i) (L i)) :
    ∃ I : Set (Fin n), ∀ j : Fin n, ∃! i : Fin n, i ∈ I ∧ L i ⊆ 𝒯 j :=
  theorem_4_2_proof hlam h𝒯 hdist hiso

/-- **Graph Minors XVIII, (4.3)** (page 87):
"4.3. *Let $\lambda$ be a tie-breaker in a hypergraph $G$, let $\theta \ge 2$, and let
$\mathcal{T}_1, \dots, \mathcal{T}_n$ be distinct tangles in $G$, each of order $\theta$, where
$n \ge 1$. For $1 \le i \le n$ let $\mathcal{L}_i \subseteq \mathcal{T}_i$ be a location of order
$\le \frac{3}{4}\theta$ which $\theta$-isolates $\mathcal{T}_i$; and suppose that for every tangle
$\mathcal{T}$ in $G$ of order $\theta$, there is a unique $i$ with $1 \le i \le n$ such that
$\mathcal{L}_i \subseteq \mathcal{T}$. Let $(T, \tau)$ be a standard tree-decomposition of $G$
relative to $\mathcal{T}_1, \dots, \mathcal{T}_n$, where $V(T) = \{t_1, \dots, t_n\}$ and $t_i$
represents $\mathcal{T}_i$ for $1 \le i \le n$. Then for $1 \le i \le n$, the location of $t_i$ in
$(T, \tau)$ is an enlargement of $\mathcal{L}_i$ by tree-width $\le \frac{9}{4}\theta$.*" -/
theorem theorem_4_3 {α : Type u} {β : Type v} {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ} {θ : ℕ} (hθ : 2 ≤ θ)
    {𝒯 L : Fin n → Set (Hypergraph α β × Hypergraph α β)} {T : SimpleGraph (Fin n)}
    {τ : Fin n → Hypergraph α β} (hlam : GM10.IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, GM10.IsTangle G θ (𝒯 i)) (hiso : ∀ i : Fin n, Isolates G lam θ (𝒯 i) (L i))
    (hord_L : ∀ i : Fin n, 4 * locationOrder (L i) ≤ 3 * θ)
    (huniq : ∀ 𝒯' : Set (Hypergraph α β × Hypergraph α β), GM10.IsTangle G θ 𝒯' → ∃! i : Fin n,
      L i ⊆ 𝒯') (hstd : IsStandardDecomposition G lam 𝒯 T τ) (i : Fin n) :
    IsLocationEnlargementByTreeWidth G (L i) (vertexLocation T τ i) ((9 / 4 : ℚ) * θ) :=
  theorem_4_3_proof hθ hlam h𝒯 hiso hord_L huniq hstd i

/-- **Graph Minors XVIII, (4.4)** (page 88):
"4.4. *Let $\lambda$ be a tie-breaker in a hypergraph $G$, and let $\theta \ge 1$ be an integer.
For each tangle $\mathcal{T}$ in $G$ of order $\ge \theta$ let
$\mathcal{L}(\mathcal{T}) \subseteq \mathcal{T}$ be a location which $\theta$-isolates
$\mathcal{T}$, and let $G$ have a tangle of order $\ge \frac{4}{3}\theta$. Then there is a
tree-decomposition $(T, \tau)$ of $G$ with the following properties:*
- *(T, \tau) is proper and rotund,*
- *for each $e \in E(T)$, the separations made by $e$ under $(T, \tau)$ are robust,*
- *for each $t \in V(T)$, let $\mathcal{L}$ be the location of $t$ in $(T, \tau)$; then there is a
  tangle $\mathcal{T}$ in $G$ of order $\ge \frac{4}{3}\theta$ with
  $\mathcal{L} \subseteq \mathcal{T}$, such that $\mathcal{L}$ is an enlargement of
  $\mathcal{L}(\mathcal{T})$ by tree-width $\le 3\theta + 1$.*" -/
theorem theorem_4_4 {α : Type u} {β : Type v} {Λ : Type w} [LinearOrder Λ] (G : Hypergraph α β)
    (lam : Hypergraph α β × Hypergraph α β → Λ) (hlam : GM10.IsTieBreaker G lam) (θ : ℕ)
    (hθ : 1 ≤ θ) (L : Set (Hypergraph α β × Hypergraph α β) → Set (Hypergraph α β × Hypergraph α β))
    (hiso : ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄, θ ≤ θ' → GM10.IsTangle G θ' 𝒯 →
      Isolates G lam θ 𝒯 (L 𝒯))
    (hex_tangle : ∃ (θ₀ : ℕ) (𝒯₀ : Set (Hypergraph α β × Hypergraph α β)), 4 * θ ≤ 3 * θ₀ ∧
      GM10.IsTangle G θ₀ 𝒯₀) :
    ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (τ : Fin n → Hypergraph α β),
    1 ≤ n ∧
    GM10.IsTreeDecomposition G T τ ∧
    IsProper G T τ ∧
    IsRotund G T τ ∧
    (∀ ⦃e : Sym2 (Fin n)⦄, e ∈ T.edgeSet → ∀ ⦃A B : Hypergraph α β⦄,
      GM10.MakesSeparation T τ e A B → GM10.IsRobust G A B) ∧
    (∀ i : Fin n, ∃ (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      4 * θ ≤ 3 * θ' ∧
      GM10.IsTangle G θ' 𝒯 ∧
      vertexLocation T τ i ⊆ 𝒯 ∧
      IsLocationEnlargementByTreeWidth G (L 𝒯) (vertexLocation T τ i) (3 * θ + 1)) :=
  theorem_4_4_proof G lam hlam θ hθ L hiso hex_tangle

/-! ## Section 5. Patchworks -/

/-- **Graph Minors XVIII, (5.1)** (page 91):
"For $i = 1, 2$ let $P_i = (G_i, \mu_i, \Delta_i)$ be a patchwork, and let $(G_i', G_0)$ be a
separation of $G_i$. Let $\pi(G_1') = \pi(G_2')$, and let $P_1|G_0 = P_2|G_0$. For $i = 1,
2$ let $H_i'$ be a realization of $P_i|G_i'$, such that for $x, y \in \bar{\pi}(G_1') =
\bar{\pi}(G_2')$, $x$ and $y$ are connected in $H_1'$ if and only if they are connected in
$H_2'$. Let $H_0$ be a realization of $P_1|G_0 = P_2|G_0$, and let $H_i = H_0 \cup H_i'$ ($i
= 1, 2$). Then for $i = 1, 2, H_i$ is a realization of $P_i$, and for $x, y \in V(G_0)$, $x$
and $y$ are connected in $H_1$ if and only if they are connected in $H_2$." -/
theorem theorem_5_1 {α : Type u} {β : Type v} {Ω : Type w} {P₁ P₂ : GM04.Patchwork Ω α β}
    {G₁' G₂' G₀ : RootedHypergraph α β} (hsep₁ : P₁.G.IsSeparation G₁' G₀)
    (hsep₂ : P₂.G.IsSeparation G₂' G₀) (hroots : G₁'.roots = G₂'.roots)
    (hG₀ : ∀ e ∈ G₀.edgeSet, (P₁.restrict G₀).Δ e = (P₂.restrict G₀).Δ e)
    {H₀ H₁' H₂' : (⊤ : SimpleGraph α).Subgraph} (hH₀ : (P₁.restrict G₀).IsRealization H₀)
    (hH₁' : (P₁.restrict G₁').IsRealization H₁') (hH₂' : (P₂.restrict G₂').IsRealization H₂')
    (hconn' : ∀ x ∈ G₁'.rootSet, ∀ y ∈ G₁'.rootSet, ConnectedIn H₁' x y ↔ ConnectedIn H₂' x y) :
    P₁.IsRealization (H₀ ⊔ H₁') ∧
    P₂.IsRealization (H₀ ⊔ H₂') ∧
    ∀ x ∈ G₀.vertexSet, ∀ y ∈ G₀.vertexSet,
      ConnectedIn (H₀ ⊔ H₁') x y ↔ ConnectedIn (H₀ ⊔ H₂') x y :=
  theorem_5_1_proof hsep₁ hsep₂ hroots hG₀ hH₀ hH₁' hH₂' hconn'

/-- **Graph Minors XVIII, (5.2)** (page 92):
"For $i = 1, 2$ let $P_i = (G_i, \mu_i, \Delta_i)$ be a patchwork, and let $(G_i', G_0)$ be a
separation of $G_i$, such that $\pi(G_1') = \pi(G_2')$, $P_1|G_0 = P_2|G_0$, and
$gr(P_1|G_1') \subseteq gr(P_2|G_2')$. Then for every realization $H_1$ of $P_1$ there is a
realization $H_2$ of $P_2$ such that for $x, y \in V(G_0)$, $x$ and $y$ are connected in
$H_1$ if and only if they are connected in $H_2$." -/
theorem theorem_5_2 {α : Type u} {β : Type v} {Ω : Type w} {P₁ P₂ : GM04.Patchwork Ω α β}
    {G₁' G₂' G₀ : RootedHypergraph α β} (hsep₁ : P₁.G.IsSeparation G₁' G₀)
    (hsep₂ : P₂.G.IsSeparation G₂' G₀) (hroots : G₁'.roots = G₂'.roots)
    (hG₀ : ∀ e ∈ G₀.edgeSet, (P₁.restrict G₀).Δ e = (P₂.restrict G₀).Δ e)
    (hgr : (feasibleGroupings (P₁.restrict G₁')).groupings ⊆
      (feasibleGroupings (P₂.restrict G₂')).groupings) {H₁ : (⊤ : SimpleGraph α).Subgraph}
    (hH₁ : P₁.IsRealization H₁) :
    ∃ H₂ : (⊤ : SimpleGraph α).Subgraph,
    P₂.IsRealization H₂ ∧
    ∀ x ∈ G₀.vertexSet, ∀ y ∈ G₀.vertexSet,
      ConnectedIn H₁ x y ↔ ConnectedIn H₂ x y :=
  theorem_5_2_proof hsep₁ hsep₂ hroots hG₀ hgr hH₁

/-- **Graph Minors XVIII, (5.3)** (page 92):
"For $i = 1, 2$ let $P_i = (G_i, \mu_i, \Delta_i)$ be a patchwork, and let $(G_i', G_0)$ be a
separation of $G_i$, such that $\pi(G_1') = \pi(G_2')$, $P_1|G_0 = P_2|G_0$, and
$gr(P_1|G_1') \subseteq gr(P_2|G_2')$. Let $\eta_1$ be a realizable expansion of some
patchwork $P = (G, \mu, \Delta)$ in $P_1$ such that $\eta_1(e) \in E(G_0)$ for every $e \in
E(G)$ and $\eta_1(v) \cap V(G_0) \ne \emptyset$ for each $v \in V(G)$. Then there is a
realizable expansion $\eta_2$ of $P$ in $P_2$ such that $\eta_2(e) = \eta_1(e)$ for each $e
\in E(G)$, and $\eta_2(v) \cap V(G_0) = \eta_1(v) \cap V(G_0)$ for each $v \in V(G)$." -/
theorem theorem_5_3 {α : Type u} {β : Type v} {Ω : Type w} [Preorder Ω] {α₀ β₀ : Type*}
    {P : GM04.Patchwork Ω α₀ β₀} {P₁ P₂ : GM04.Patchwork Ω α β} {G₁' G₂' G₀ : RootedHypergraph α β}
    (hsep₁ : P₁.G.IsSeparation G₁' G₀) (hsep₂ : P₂.G.IsSeparation G₂' G₀)
    (hroots : G₁'.roots = G₂'.roots) (hG₀_dom : ∀ e ∈ G₀.edgeSet, e ∈ P₁.dom ↔ e ∈ P₂.dom)
    (hG₀_μ : ∀ e ∈ G₀.edgeSet, e ∈ P₁.dom → P₁.μ e = P₂.μ e)
    (hG₀_Δ : ∀ e ∈ G₀.edgeSet, P₁.Δ e = P₂.Δ e) (hG₀_φ : ∀ e ∈ G₀.edgeSet, P₁.φ e ≤ P₂.φ e)
    (hgr : (feasibleGroupings (P₁.restrict G₁')).groupings ⊆
      (feasibleGroupings (P₂.restrict G₂')).groupings) {η₁v : α₀ → Set α} {η₁e : β₀ → β}
    (hη₁ : GM04.IsRealizableExpansion P P₁ η₁v η₁e) (he_G₀ : ∀ e ∈ P.G.edgeSet, η₁e e ∈ G₀.edgeSet)
    (hv_G₀ : ∀ v ∈ P.G.vertexSet, (η₁v v ∩ G₀.vertexSet).Nonempty) :
    ∃ η₂v : α₀ → Set α,
    GM04.IsRealizableExpansion P P₂ η₂v η₁e ∧
    ∀ v ∈ P.G.vertexSet, η₂v v ∩ G₀.vertexSet = η₁v v ∩ G₀.vertexSet :=
  theorem_5_3_proof hsep₁ hsep₂ hroots hG₀_dom hG₀_μ hG₀_Δ hG₀_φ hgr hη₁ he_G₀ hv_G₀

/-- **Graph Minors XVIII, (5.4)** (page 93):
"**5.4.** *Let $P = (G, \mu, \Delta)$ be a patchwork, let $\mathscr{L}$ be a rooted location in
$G$, and let $P' = (G', \mu', \Delta')$ be the heart of $(P, \mathscr{L})$. Then*
$$V(G) \setminus \bar{\pi}(G) = (V(G') \setminus \bar{\pi}(G')) \cup \bigcup_{A \in \mathscr{L}}
(V(A) \setminus \bar{\pi}(A)),$$
*and $gr(P) = gr(P')$.*" -/
theorem theorem_5_4 {α : Type u} {β : Type v} {P P' : UnlabeledPatchwork α β}
    {ℒ : Set (RootedHypergraph α β)} {newEdge : RootedHypergraph α β → β}
    (hP' : IsPatchworkHeart P ℒ newEdge P') :
    P.G.vertexSet \ P.G.rootSet =
      (P'.G.vertexSet \ P'.G.rootSet) ∪ (⋃ A ∈ ℒ, A.vertexSet \ A.rootSet) ∧
    feasibleGroupings P = feasibleGroupings P' :=
  theorem_5_4_proof hP'

/-- **Graph Minors XVIII, (5.5)** (page 95):
"Let $P = (G, \mu, \Delta, \phi)$ be an $\Omega$-patchwork, let $w \ge 0$, and let
$\mathscr{L}, \mathscr{L}^*$ be rooted locations in $G$, such that $\mathscr{L}^{*-}$ is an
enlargement of $\mathscr{L}^-$ by tree-width $\le w$. Then $P | \mathscr{L}^*$ is an
enlargement of $P | \mathscr{L}$ by tree-width $\le w$." -/
theorem theorem_5_5 {α : Type u} {β : Type v} {Ω : Type w} {P P' P_star : PartialPatchwork Ω α β}
    {ℒ ℒ_star : Set (RootedHypergraph α β)} {w : ℕ} (hP' : HasPlaceHeart P ℒ P')
    (hP_star : HasPlaceHeart P ℒ_star P_star)
    (henl : IsLocationEnlargementByTreeWidth P.G.toHypergraph (rootedLocationToLocation P.G ℒ)
      (rootedLocationToLocation P.G ℒ_star) (w : ℚ)) :
    IsPlaceEnlargementByTreeWidth w P' P_star :=
  theorem_5_5_proof hP' hP_star henl

/-- **Graph Minors XVIII, (5.6)** (page 98):
"**5.6.** *Let $P_1, P_2$ be partial $\Omega$-patchworks, and let $(A_1, B_1)$, $(A_2, B_2)$ be
separations of $\|P_1\|, \|P_2\|$ respectively. Let $\eta'$ be a realizable expansion of $P_1|A_1$
in $P_2|A_2$ (whence $|\bar{\pi}(A_1)| = |\bar{\pi}(A_2)| = k$, say) and let $\eta''$ be a
realizable expansion of $P_1|B_1$ in $P_2|B_2$ such that for $1 \le i \le k$, $\eta''(v)$ contains
the $i$th term of $\pi(A_2)$, where $v$ is the $i$th term of $\pi(A_1)$. Define $\eta$ by:*
$$
\eta(v) = \begin{cases}
\eta'(v), & v \in V(A_1) \setminus V(B_1), \\
\eta''(v), & v \in V(B_1) \setminus V(A_1), \\
\eta'(v) \cup \eta''(v), & v \in V(A_1 \cap B_1),
\end{cases}
$$
$$
\eta(e) = \begin{cases}
\eta'(e), & e \in E(A_1), \\
\eta''(e), & e \in E(B_1).
\end{cases}
$$
*Then $\eta$ is a realizable expansion of $P_1$ in $P_2$.*"

In our representation `PartialPatchwork Ω α β = GM04.Patchwork (WithBot Ω) α β`, the adjoined
minimum element `* = ⊥` of the paper's proof is already built into `WithBot Ω`, so (5.6) follows
directly from `GM04.theorem_8_1`. -/
theorem theorem_5_6 {Ω : Type u_3} [Preorder Ω] {α₁ β₁ α₂ β₂ : Type*}
    {P₁ : PartialPatchwork Ω α₁ β₁} {P₂ : PartialPatchwork Ω α₂ β₂} {A₁ B₁ : RootedHypergraph α₁ β₁}
    {A₂ B₂ : RootedHypergraph α₂ β₂} (hsep₁ : P₁.G.IsSeparation A₁ B₁)
    (hsep₂ : P₂.G.IsSeparation A₂ B₂) {η'v η''v : α₁ → Set α₂} {η'e η''e : β₁ → β₂}
    (hη' : GM04.IsRealizableExpansion (P₁.restrict A₁) (P₂.restrict A₂) η'v η'e)
    (hη'' : GM04.IsRealizableExpansion (P₁.restrict B₁) (P₂.restrict B₂) η''v η''e)
    (hroots_mem : ∀ (i : ℕ) (hi₁ : i < A₁.roots.length) (hi₂ : i < A₂.roots.length),
      A₂.roots[i] ∈ η''v A₁.roots[i]) :
    GM04.IsRealizableExpansion P₁ P₂
    (GM04.glueVertex A₁ B₁ η'v η''v) (GM04.glueEdge A₁ η'e η''e) :=
  theorem_5_6_proof hsep₁ hsep₂ hη' hη'' hroots_mem

/-- **Graph Minors XVIII, (5.7)** (page 99):
"For $i = 1, 2$ let $(P_i, \mathcal{L}_i)$ be an $\Omega$-place with heart $Q_i$, using new
elements $e_i(A)$ ($A \in \mathcal{L}_i$). Suppose that $\eta$ is a realizable expansion of
$Q_1$ in $Q_2$ such that* - *if $e \in E(Q_1)$ and $\eta(e) = e_2(A_2)$ for some $A_2 \in
\mathcal{L}_2$ then $e = e_1(A_1)$ for some $A_1 \in \mathcal{L}_1$,* - *for each $A_1 \in
\mathcal{L}_1$ there exists $A_2 \in \mathcal{L}_2$ such that $\eta(e_1(A_1)) = e_2(A_2)$
and $P_1|A_1$ is simulated in $P_2|A_2$.* *Then $P_1$ is simulated in $P_2$." -/
theorem theorem_5_7 {Ω : Type u_3} [Preorder Ω] {α₁ β₁ α₂ β₂ : Type*}
    {P₁ Q₁ : PartialPatchwork Ω α₁ β₁} {P₂ Q₂ : PartialPatchwork Ω α₂ β₂}
    {ℒ₁ : Set (RootedHypergraph α₁ β₁)} {ℒ₂ : Set (RootedHypergraph α₂ β₂)}
    {newEdge₁ : RootedHypergraph α₁ β₁ → β₁} {newEdge₂ : RootedHypergraph α₂ β₂ → β₂}
    (hQ₁ : IsPlaceHeart P₁ ℒ₁ newEdge₁ Q₁) (hQ₂ : IsPlaceHeart P₂ ℒ₂ newEdge₂ Q₂) {ηv : α₁ → Set α₂}
    {ηe : β₁ → β₂} (hη : GM04.IsRealizableExpansion Q₁ Q₂ ηv ηe)
    (hpre : ∀ ⦃e : β₁⦄ ⦃A₂ : RootedHypergraph α₂ β₂⦄, e ∈ Q₁.G.edgeSet → A₂ ∈ ℒ₂ → ηe e =
      newEdge₂ A₂ → ∃ A₁ ∈ ℒ₁, e = newEdge₁ A₁)
    (hsim : ∀ ⦃A₁ : RootedHypergraph α₁ β₁⦄, A₁ ∈ ℒ₁ → ∃ A₂ ∈ ℒ₂, ηe (newEdge₁ A₁) = newEdge₂ A₂ ∧
      GM04.Simulated (P₁.restrict A₁) (P₂.restrict A₂)) :
    GM04.Simulated P₁ P₂ :=
  theorem_5_7_proof hQ₁ hQ₂ hη hpre hsim

/-! ## Section 6. Well-Behavedness -/

/-- **Graph Minors XVIII, (6.1)** (page 100):
"Let $\Omega$ be a well-quasi-order, and let $\mathcal{C}$ be a well-behaved class of partial
$\Omega$-patchworks. Let $\mathcal{C}'$ be the class of all rootings of rootless members of
$\mathcal{C}$. Then $\mathcal{C}'$ is well-behaved." -/
theorem theorem_6_1 {α : Type u} {β : Type v} {Ω : Type w} [Preorder Ω]
    {𝒞 : Set (PartialPatchwork Ω α β)} (h𝒞 : WellBehaved 𝒞) :
    WellBehaved {P' : PartialPatchwork Ω α β | ∃ P ∈ 𝒞, IsRooting P P'} :=
  theorem_6_1_proof h𝒞

/-- **Graph Minors XVIII, (6.2)** (page 101):
"If $\Omega$ is a well-quasi-order and $w \ge 0$, the class of all robust partial
$\Omega$-patchworks of tree-width $\le w$ is well-behaved." -/
theorem theorem_6_2 {α : Type u} {β : Type v} {Ω : Type w} [Preorder Ω] (w : ℕ) :
    WellBehaved {P : PartialPatchwork Ω α β | P.IsRobust ∧ HasPatchworkTreeWidthLE P w} :=
  theorem_6_2_proof w

/-- **Graph Minors XVIII, (6.3)** (page 101):
"Let $\Omega$ be a well-quasi-order, and let $\mathcal{C}_1, \mathcal{C}_2$ be well-behaved
classes of partial $\Omega$-patchworks. Then the class of all enlargements of members of
$\mathcal{C}_1$ by $\mathcal{C}_2$ is well-behaved." -/
theorem theorem_6_3 {α : Type u} {β : Type v} {Ω : Type w} [Preorder Ω]
    {𝒞₁ 𝒞₂ : Set (PartialPatchwork Ω α β)} (h𝒞₁ : WellBehaved 𝒞₁) (h𝒞₂ : WellBehaved 𝒞₂) :
    WellBehaved (enlargementClass 𝒞₁ 𝒞₂) :=
  theorem_6_3_proof h𝒞₁ h𝒞₂

/-- **Graph Minors XVIII, (6.4)** (page 102):
"Let $P = (G, \mu, \Delta, \phi)$ be a rootless, robust $\Omega$-patchwork, and let $(S,
\sigma)$ be a rotund tree-decomposition of $G^-$. Let $T$ be an arborescence with $T^- = S$.
Then there is a rooted decomposition $(T, \tau)$ of $P$ such that $\tau(t)^- = \sigma(t)$
for each $t \in V(T)$." -/
theorem theorem_6_4 {α : Type u} {β : Type v} {Ω : Type w} [Preorder Ω] {ι : Type*} [Fintype ι]
    {P : GM04.Patchwork Ω α β} (hrootless : IsRootless P) (hrob : P.IsRobust) {S : SimpleGraph ι}
    {σ : ι → Hypergraph α β} (htd : GM10.IsTreeDecomposition P.G.toHypergraph S σ)
    (hrot : IsRotund P.G.toHypergraph S σ) (T : GM04.RootedTree ι)
    (hT_verts : T.verts = Finset.univ) (hT_S : arborescenceUnderlying T = S) :
    ∃ τ : ι → RootedHypergraph α β,
    IsRootedDecomposition P T τ ∧ ∀ t, (τ t).toHypergraph = σ t :=
  theorem_6_4_proof hrootless hrob htd hrot T hT_verts hT_S

/-- **Graph Minors XVIII, (6.5)** (page 103): "Let $(T, \tau)$ be a rooted decomposition of a
rootless $\Omega$-patchwork $P = (G, \mu, \Delta, \phi)$."

(combined statement, page 103). -/
theorem theorem_6_5 {α : Type u} {β : Type v} {Ω : Type w} [Preorder Ω] {ι : Type*}
    {P : GM04.Patchwork Ω α β} (hrootless : IsRootless P) {T : GM04.RootedTree ι}
    {τ : ι → RootedHypergraph α β} (hdec : IsRootedDecomposition P T τ) {f : ι} (hf : f ∈ T.edges) :
    (∃ hcomp : IsComplemented P.G (GM04.cross τ (T.subtreeAt f) f),
      complement P.G (GM04.cross τ (T.subtreeAt f) f) hcomp =
        GM04.cross τ (T.rootSide f) T.root) ∧
    (∃ hcomp : IsComplemented P.G (rootedDecompRootSide hdec.isTreeDecomposition hf),
      (complement P.G (rootedDecompRootSide hdec.isTreeDecomposition hf) hcomp).toHypergraph =
        (GM04.cross τ (T.subtreeAt f) f).toHypergraph ∧
      (complement P.G (rootedDecompRootSide hdec.isTreeDecomposition hf) hcomp).rootSet = ∅) ∧
    (let ℒ : Set (RootedHypergraph α β) :=
       {A | ∃ g ∈ T.children f, A = GM04.cross τ (T.subtreeAt g) g}
     let ℒ_star : Set (RootedHypergraph α β) :=
       insert (rootedDecompRootSide hdec.isTreeDecomposition hf) ℒ
     IsRootedLocation (GM04.cross τ (T.subtreeAt f) f) ℒ ∧
       IsRootedLocation P.G ℒ_star ∧
       rootedLocationCore (GM04.cross τ (T.subtreeAt f) f) ℒ =
         rootedLocationCore P.G ℒ_star) :=
  theorem_6_5_proof hrootless hdec hf

/-- **Graph Minors XVIII, (6.6)** (page 104):
"**6.6.** *Let $\Omega$ be a well-quasi-order, and let $\mathcal{C}$ be a well-behaved class of
rootless partial $\Omega$-patchworks. Let $\mathcal{C}'$ be the class of all rootless, robust
$\Omega$-patchworks $P$ such that there is a rotund, proper tree-decomposition of $\|P\|$ under
which all pieces of $P$ belong to $\mathcal{C}$. Then $\mathcal{C}'$ is well-quasi-ordered by
simulation.*"

The Lean proof corrects a step of the paper's proof and, as the paper does, applies Graph Minors IV,
(3.3) to the stars of the arborescences. See the correction to the proof of (6.6) in
`corrections/GM18.md`. -/
theorem theorem_6_6 {α : Type u} {β : Type v} {Ω : Type w} [Infinite β] [Preorder Ω]
    (hΩ : WellQuasiOrderedLE Ω) {ι : ℕ → Type*} [∀ i, Fintype (ι i)]
    {𝒞 : Set (PartialPatchwork Ω α β)} (h𝒞 : WellBehaved 𝒞) (P : ℕ → GM04.Patchwork Ω α β)
    (hrootless : ∀ i, IsRootless (P i)) (hrob : ∀ i, (P i).IsRobust) (S : ∀ i, SimpleGraph (ι i))
    (σ : ∀ i, ι i → Hypergraph α β)
    (htd : ∀ i, GM10.IsTreeDecomposition (P i).G.toHypergraph (S i) (σ i))
    (hrot : ∀ i, IsRotund (P i).G.toHypergraph (S i) (σ i))
    (hprop : ∀ i, IsProper (P i).G.toHypergraph (S i) (σ i))
    (hpieces : ∀ i u (Q : PartialPatchwork Ω α β),
      IsPiece (toPartialPatchwork (P i)) (S i) (σ i) u Q → Q ∈ 𝒞) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) :=
  theorem_6_6_proof hΩ h𝒞 P hrootless hrob S σ htd hrot hprop hpieces

/-- **Graph Minors XVIII, (6.7)** (pages 106–107):
"**6.7.** *Let $\Omega$ be a well-quasi-order, let $\mathscr{C}$ be a well-behaved class of
rootless partial $\Omega$-patchworks, and let $\theta \ge 1$ be an integer. Let $\mathscr{D}$ be
a class of rootless, robust $\Omega$-patchworks and suppose that for each $P \in \mathscr{D}$ there
is a tie-breaker $\lambda$ in $\|P\|^-$ such that for every tangle $\mathscr{T}$ in $G^-$ of order
$\ge \theta$, there is an $\Omega$-place $(P, \mathscr{L})$ with heart in $\mathscr{C}$ such that
$\mathscr{L}^-$ $\theta$-isolates $\mathscr{T}$. Then $\mathscr{D}$ is well-quasi-ordered by
simulation.*" -/
theorem theorem_6_7 {α : Type u} {β : Type v} {Ω : Type w} [Infinite β] [Preorder Ω]
    (hΩ : WellQuasiOrderedLE Ω) {𝒞 : Set (PartialPatchwork Ω α β)} (h𝒞 : WellBehaved 𝒞) {θ : ℕ}
    (hθ : 1 ≤ θ) {𝒟 : Set (GM04.Patchwork Ω α β)}
    (h𝒟 : ∀ ⦃P : GM04.Patchwork Ω α β⦄, P ∈ 𝒟 → IsRootless P ∧ P.IsRobust ∧
      ∃ (Λ : Type w') (_ : LinearOrder Λ) (lam : Hypergraph α β × Hypergraph α β → Λ),
      GM10.IsTieBreaker P.G.toHypergraph lam ∧
      ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄, θ ≤ θ' →
      GM10.IsTangle P.G.toHypergraph θ' 𝒯 →
      ∃ (ℒ : Set (RootedHypergraph α β)) (P' : PartialPatchwork Ω α β),
      IsOmegaPlace (toPartialPatchwork P) ℒ ∧ HasPlaceHeart (toPartialPatchwork P) ℒ P' ∧ P' ∈ 𝒞 ∧
      Isolates P.G.toHypergraph lam θ 𝒯 (rootedLocationToLocation P.G ℒ)) :
    ∀ P : ℕ → GM04.Patchwork Ω α β, (∀ i, P i ∈ 𝒟) →
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) :=
  theorem_6_7_proof hΩ h𝒞 hθ h𝒟

/-! ## Section 7. More on isolation -/

/-- **Graph Minors XVIII, (7.1)** (pages 107–108):
"Let $\mathscr{T}$ be a tangle of order $\ge \theta \ge 1$ in a hypergraph $G$ with a
tie-breaker $\lambda$, and let $\mathscr{L} \subseteq \mathscr{T}$ be a location of order $<
\theta$, every member of which is $\lambda$-linked to $\mathscr{T}$. Then $\mathscr{L}$
$\theta$-isolates $\mathscr{T}$." -/
theorem theorem_7_1 {α : Type u} {β : Type v} {Λ : Type w} [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hlam : GM10.IsTieBreaker G lam) {θ θ_𝒯 : ℕ}
    {𝒯 ℒ : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : GM10.IsTangle G θ_𝒯 𝒯) (_hθ_le : θ ≤ θ_𝒯)
    (hℒ : GM10.IsLocation G ℒ) (hℒ_sub : ℒ ⊆ 𝒯) (hord : locationOrder ℒ < θ)
    (hlink : ∀ ⦃C D : Hypergraph α β⦄, (C, D) ∈ ℒ → IsLambdaLinkedTo lam 𝒯 C D) :
    Isolates G lam θ 𝒯 ℒ :=
  theorem_7_1_proof hlam h𝒯 _hθ_le hℒ hℒ_sub hord hlink

end GraphMinor.GM18
