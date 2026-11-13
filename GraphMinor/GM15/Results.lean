module

public import GraphMinor.GM15.Section2
public import GraphMinor.GM15.Section3
public import GraphMinor.GM15.Section3Crosscap
public import GraphMinor.GM15.Section3Handle
public import GraphMinor.GM15.Section3Parallel
public import GraphMinor.GM15.Section3Given
public import GraphMinor.GM15.Section4
public import GraphMinor.GM15.Section5
public import GraphMinor.GM15.Section6
public import GraphMinor.GM15.Section7
public import GraphMinor.GM15.Section8

/-!
# Graph Minors XV: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XV. Giant steps*, J. Combin. Theory Ser. B **68**
(1996), 112–148.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. The docstrings say where the Lean differs from the print, and
`corrections/GM15.md` lists the corrections to the paper.
-/

public section

namespace GraphMinor.GM15

open Set Function Topology

universe u v w

/-! ## Section 1. Introduction -/

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (1.1)** (pages 115–116): "For any surface $\Sigma$ with $bd(\Sigma) =
\emptyset$, and any integers $\kappa, \phi, \mu \ge 0$, there are integers $\theta, \lambda, \rho \ge
0$ such that the following holds. Let $\mathscr{T}^*$ be a tangle in a graph $G$, such that some
$\Sigma$-span of order $\ge \theta$ is $(\lambda, \mu)$-flat. Then either (i) there is a
$\Sigma$-span of order $\ge \phi$ with $> \kappa$ independent eyes, or (ii) there is a
$\Sigma'$-span of order $\ge \phi$, where $\Sigma'$ is a surface obtained by adding a crosscap to
$\Sigma$, or (iii) there is a $\mathscr{T}^*$-central segregation of $G$ of type $(\rho, \kappa)$ with
an arrangement in $\Sigma$."

Main theorem of Graph Minors XV, proved from `(1.2)` (`GM15Theorem12Statement`), `(5.1)`
(`theorem_5_1_proof`), and `(7.1)` (`theorem_7_1_proof`). -/
theorem theorem_1_1 (S : Type w) [TopologicalSpace S] [T2Space S] (hSurf : IsSurface S)
    (hConn : ConnectedSpace S) (hBd : bd S = ∅) (κ φ μ : ℕ) :
    ∃ (θ lam p : ℕ),
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G)
    (θ₀ : ℕ) (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d₀ : Set S → Set S → ℕ),
    IsFlatSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀ → HasTangleMetric H₀ θ₀ T₀ d₀ → θ ≤ θ₀ →
    (∃ (H' : Drawing S) (η' : SpanEmbedding H' G) (θ' : ℕ)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ),
      IsSigmaSpan G H' η' θ_star θ' T_star T' ∧ HasTangleMetric H' θ' T' d' ∧ φ ≤ θ' ∧
      HasIndependentEyes G H' η' θ' T' d' (κ + 1)) ∨
    (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'), IsObtainedByAddingCrosscap S S' ∧
      ∃ (H' : Drawing S') (η' : SpanEmbedding H' G) (θ' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))), φ ≤ θ' ∧
      IsSigmaSpan G H' η' θ_star θ' T_star T') ∨ Section7S3 S G T_star p κ :=
  GM15.theorem_1_1_proof S hSurf hConn hBd κ φ μ

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (1.2)** (pages 115–116, proved in Section 7, pages 134–145): "For any surface
$\Sigma$ with $bd(\Sigma) = \emptyset$, and any integers $k \ge 0$, $\phi \ge 8$, $\mu \ge 12$ and
even, $\lambda_{k+1} \ge 4$, and $\theta_{k+1} \ge 4\lambda_{k+1} + \mu + 2$, there are integers
$\rho_k, \lambda_k \ge 0$ and $\theta_k \ge 4\lambda_k + \mu + 2$ such that the following holds. Let
$\mathscr{T}^*$ be a tangle in a graph $G$, and suppose that there is a $(\lambda_k, \mu)$-flat
$\Sigma$-span of order $\ge \theta_k$ with $k$ eyes mutually at distance $\ge \theta_k$. Then either
(i) there is a $(\lambda_{k+1}, \mu)$-flat $\Sigma$-span of order $\theta_{k+1}$ with $k+1$ eyes,
mutually at distance $\theta_{k+1}$, or (ii) there is a $\Sigma'$-span of order $\phi$, where
$\Sigma'$ is a surface obtained by adding a crosscap to $\Sigma$, or (iii) there is a
$\mathscr{T}^*$-central segregation of $G$ of type $(\rho_k, k)$ with an arrangement in $\Sigma$."

For any connected surface `Σ` with `bd(Σ) = ∅` and any `k ≥ 0`, `φ ≥ 8`, `μ ≥ 12` even,
`λ_{k+1} ≥ 4`, and `θ_{k+1} ≥ 4λ_{k+1} + μ + 2`, there exist `p_k, λ_k, θ_k` with
`θ_k ≥ 4λ_k + μ + 2` such that every `(λ_k, μ)`-flat `Σ`-span of order `≥ θ_k` with `k` eyes at
distance `≥ θ_k` yields one of `(S1)`, `(S2)`, or `(S3)`.

The Lean takes `τ₂ = 6 + θ' / 2`, so that the numbers of the proof work out. See the correction to
the proof of (1.2) in `corrections/GM15.md`. The definitions of a `Σ`-span and of control of a
clique minor carry the tangle and finiteness conditions with them, so that the lemmas of Sections 3
to 8 need not repeat them. -/
theorem theorem_1_2 (S : Type w) [TopologicalSpace S] [T2Space S] (h1 : IsSurface S)
    (h2 : ConnectedSpace S) (h3 : bd S = ∅) (k φ μ lam_next θ_next : ℕ) (h4 : 8 ≤ φ) (h5 : 12 ≤ μ)
    (h6 : Even μ) (h7 : 4 ≤ lam_next) (h8 : 4 * lam_next + μ + 2 ≤ θ_next) :
    ∃ (p_k lam_k θ_k : ℕ), 4 * lam_k + μ + 2 ≤ θ_k ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G)
    (θ₀ : ℕ) (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d₀ : Set S → Set S → ℕ),
    IsFlatSpan G H₀ η₀ θ_star θ₀ lam_k μ T_star T₀ → HasTangleMetric H₀ θ₀ T₀ d₀ → θ_k ≤ θ₀ →
    HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ k θ_k → Section7S1 S G θ_star T_star k μ lam_next θ_next ∨
    Section7S2 S G θ_star T_star φ ∨ Section7S3 S G T_star p_k k :=
  GM15.theorem_1_2_proof S h1 h2 h3 k φ μ lam_next θ_next h4 h5 h6 h7 h8

/-! ## Section 2. Tangles and Transactions -/

open Graph SimpleGraph Hypergraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 in
/-- **Graph Minors XV, (2.1)** (page 116):
"Let $\mathscr{T}$ be a tangle in a graph $G$, let $\rho \ge 1$ with $ord(\mathscr{T}) \ge 5\rho+2$, and
let $\mathscr{S}$ be a segregation of $G$ of type $(\rho, \kappa)$ for some $\kappa$. Suppose that for
every $(C, \Omega) \in \mathscr{S}$ there is no $(A, B) \in \mathscr{T}$ of order $\le 2\rho+1$ with
$B \subseteq C$. Then $\mathscr{S}$ is $\mathscr{T}$-central."

The Lean proof corrects a step of the paper's proof. See the correction to the proof of (2.1) in
`corrections/GM15.md`. -/
theorem theorem_2_1 {α : Type u} {β : Type v} (G : Graph α β) (θ p κ : ℕ)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (𝒮 : Set (Society α β)) (h𝒯 : IsGraphTangle G θ 𝒯)
    (hp : 1 ≤ p) (hθ : 5 * p + 2 ≤ θ) (h𝒮 : IsSegregationOfType G p κ 𝒮)
    (hno_small : ∀ S₀ ∈ 𝒮, ∀ A B : Hypergraph α β, (A, B) ∈ 𝒯 → separationOrder A B ≤ 2 * p + 1 →
      ¬ SubhypergraphInGraph B S₀.G) :
    IsCentralSegregation G 𝒯 𝒮 :=
  GM15.theorem_2_1_proof G θ p κ 𝒯 𝒮 h𝒯 hp hθ h𝒮 hno_small

/-! ## Section 3. Rigidity -/

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (3.1)** (page 119): "Let $H$ be a rigid drawing in a surface $\Sigma$, and
let $\mathscr{T}$ be a tangle in $H$ of order $\ge 3$. Let $\Delta \subseteq \Sigma$ be a closed
disc with $bd(\Delta) \cap U(H) \subseteq V(H)$ and $|bd(\Delta) \cap V(H)| \le 2$. Then $(H \cap
\Delta, H \cap \overline{\Sigma - \Delta}) \in \mathscr{T}$ if and only if $\Delta$ is a dial for
$bd(\Delta)$."

In a rigid drawing `H` in a connected closed surface `Σ` with a tangle `T` of order `≥ 3`, for any
closed disc `Δ ⊆ Σ` with `bd(Δ) ∩ U(H) ⊆ V(H)` and `|bd(Δ) ∩ V(H)| ≤ 2`,
`(H ∩ Δ, H ∩ closure(Σ - Δ)) ∈ T` if and only if `Δ` is a dial for `bd(Δ)`. -/
theorem theorem_3_1 {S : Type w} [TopologicalSpace S] [T2Space S] (H : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (Δ : Set S) (hS : IsClosedSurface S)
    (hConn : ConnectedSpace S) (hRigid : IsRigid H) (hT : IsTangle H.toHypergraph θ T) (hθ : 3 ≤ θ)
    (hΔ : IsClosedDisc Δ) (hU : subBd Δ ∩ H.U ⊆ H.V) (hV : (subBd Δ ∩ H.V).ncard ≤ 2) :
    (((H.interSet Δ).toHypergraph, (H.interSet (closure (univ \ Δ))).toHypergraph) ∈ T ↔
    IsDial H (subBd Δ) Δ) :=
  GM15.theorem_3_1_proof H θ T Δ hS hConn hRigid hT hθ hΔ hU hV

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (3.2)** (pages 119–120): "Let $\Sigma$ be a surface with $bd(\Sigma) =
\emptyset$, and let $\Sigma_1, \Sigma_2 \subseteq \Sigma$ be surfaces with $\Sigma_1 \cup \Sigma_2 =
\Sigma$ and $\Sigma_1 \cap \Sigma_2 = bd(\Sigma_1) = bd(\Sigma_2)$. Let $H$ be a drawing in $\Sigma$
with $\Sigma_1 \cap \Sigma_2 \subseteq U(H)$, and let $X \subseteq V(H) \cap \Sigma_1 \cap
\Sigma_2$. Let $\hat{\Sigma}_1$ be a surface with $\Sigma_1 \subseteq \hat{\Sigma}_1$ and
$bd(\hat{\Sigma}_1) = \emptyset$, such that each O-arc in $bd(\Sigma_1)$ bounds an open disc in
$\hat{\Sigma}_1$ disjoint from $\Sigma_1$ (thus, $\hat{\Sigma}_1$ is obtained from $\Sigma_1$ by
“pasting” a disc onto each O-arc in $bd(\Sigma_1)$). Suppose that (i) if $r$ is a region of $H$ in
$\Sigma$ and $r \subseteq \Sigma_1$, there is at most one component $F$ of $\Sigma_1 \cap \Sigma_2$
with $\bar{r} \cap F \ne \emptyset$ (ii) for every $O$-arc $F \subseteq \hat{\Sigma}_1$, with $F
\cap U(H) \subseteq V(H)$ and $|F \cap V(H)| \le 2$, there is a dial $\Delta \subseteq
\hat{\Sigma}_1$ for $F, H \cap \Sigma_1$ with $|X \cap \Delta| \le |F \cap V(H)|$ (iii) for every
$O$-arc $F \subseteq \Sigma_2$ with $F \cap U(H) \subseteq V(H)$ and $|F \cap V(H)| \le 2$, there is
a dial $\Delta \subseteq \Sigma_2$ for $F, H$ (iv) if $F \subseteq \Sigma_2$ is a line with ends $u,
v \in \Sigma_1 \cap \Sigma_2 \cap V(H)$ and is otherwise disjoint from $U(H)$, and $P$ is a path of
$H \cap \Sigma_1 \cap \Sigma_2$ with ends $u, v$ and with $|V(P) \cap X| \le 2$, then the $O$-arc
$U(P) \cup F$ bounds an open disc in $\Sigma_2$ disjoint from $U(H)$. Then $H$ is rigid in
$\Sigma$."

Gluing lemma for rigidity of a drawing `H` across a decomposition `Σ = Σ₁ ∪ Σ₂`. -/
theorem theorem_3_2 {S : Type w} [TopologicalSpace S] [T2Space S] {S_hat : Type w}
    [TopologicalSpace S_hat] [T2Space S_hat] {t : ℕ} (C : Fin t → Set S) (P₁ P₂ : Set S)
    (ι : P₁ → S_hat) (D : Fin t → Set S_hat) (H : Drawing S) (H₁ : Drawing S_hat) (X : Set S)
    (h1 : GM12.IsCappedSplit C P₁ P₂ ι D) (h2 : GM12.IsCappedDrawing ι H H₁) (h3 : P₁ ∩ P₂ ⊆ H.U)
    (h4 : X ⊆ H.V ∩ (P₁ ∩ P₂))
    (h5 : ∀ r ∈ H.R, r ⊆ P₁ → ∀ i j : Fin t, (closure r ∩ C i).Nonempty →
      (closure r ∩ C j).Nonempty → i = j)
    (h6 : ∀ F : Set S_hat, IsOArc F → F ∩ H₁.U ⊆ H₁.V → (F ∩ H₁.V).ncard ≤ 2 → ∃ Δ : Set S_hat,
      IsDial H₁ F Δ ∧ ((ι '' ((↑) ⁻¹' X)) ∩ Δ).ncard ≤ (F ∩ H₁.V).ncard)
    (h7 : ∀ F : Set S, F ⊆ P₂ → IsOArc F → F ∩ H.U ⊆ H.V → (F ∩ H.V).ncard ≤ 2 → ∃ Δ : Set S, Δ ⊆
      P₂ ∧ IsDial H F Δ)
    (h8 : ∀ (F : Set S) (u v : S) (P : Drawing S), F ⊆ P₂ → u ∈ (P₁ ∩ P₂) ∩ H.V →
      v ∈ (P₁ ∩ P₂) ∩ H.V → IsLineWithEnds F u v → F ∩ H.U ⊆ {u, v} →
      P.IsSubdrawing (H.interSet (P₁ ∩ P₂)) → P.IsPathBetween u v → (P.V ∩ X).ncard ≤ 2 →
      ∃ U₀ : Set S, IsOpenDisc U₀ ∧ IsClosedDisc (closure U₀) ∧ U₀ ⊆ P₂ ∧ subBd U₀ = P.U ∪ F ∧
      Disjoint U₀ H.U) : IsRigid H :=
  GM15.theorem_3_2_proof C P₁ P₂ ι D H H₁ X h1 h2 h3 h4 h5 h6 h7 h8

open scoped unitInterval in
open Metric Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM12 GM14 in
/-- **Graph Minors XV, (3.3)** (pages 120–121): "Let $\Sigma$ be a surface and let $\phi \ge 3$ be
an integer. Let $\mathscr{T}^*$ be a tangle in a graph $G$, and let $H, \eta, \mathscr{T}$ be a
$\Sigma$-span. Let $\Lambda \subseteq \Sigma$ be a region of $H$ such that $H \cap bd(\Lambda)$ is a
circuit, and let $a_1, \dots, a_\phi, b_1, \dots, b_\phi$ be distinct vertices of this circuit, in
order, such that $\{a_1, \dots, a_\phi, b_1, \dots, b_\phi\}$ is free with respect to $\mathscr{T}$.
For $1 \le i \le \phi$ let $P_i$ be an $\eta(H)$-path with ends $\eta(a_i), \eta(b_i)$, such that
$P_1, \dots, P_\phi$ are mutually disjoint. Then there is a $\Sigma'$-span of order $\phi$, where
$\Sigma'$ is the surface obtained by adding a crosscap to $\Sigma$."

Adding a crosscap to a region `Λ` along `φ` disjoint `η(H)`-paths `P_i` with ends `a_i, b_i` in
circular order `a_1, ..., a_φ, b_1, ..., b_φ` on `subBd Λ` yields a `Σ'`-span `(H', η', T')` of
order `φ`. -/
theorem theorem_3_3 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ φ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (Λ : Set S) (P : Fin φ → Graph α β)
    (a b : Fin φ → S) (h1 : IsSigmaSpan G H η θ_star θ T_star T) (h2 : Λ ∈ H.R)
    (h3 : IsOArc (subBd Λ)) (h4 : (H.interSet (subBd Λ)).IsCircuit) (h5 : 3 ≤ φ) (h6 : φ ≤ θ)
    (h7 : (List.ofFn a ++ List.ofFn b).Nodup)
    (h8 : GM12.IsListedInOrderOn (subBd Λ) (List.ofFn a ++ List.ofFn b))
    (h9 : ∀ i : Fin φ, a i ∈ H.V ∩ subBd Λ ∧ b i ∈ H.V ∩ subBd Λ)
    (h10 : ∀ i : Fin φ, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (a i)) (η.vMap (b i)))
    (h11 : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (h12 : IsFreeSet H.toHypergraph T θ (range a ∪ range b)) :
    ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'), IsObtainedByAddingCrosscap S S' ∧
    ∃ (H' : Drawing S') (η' : SpanEmbedding H' G)
    (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
    IsSigmaSpan G H' η' θ_star φ T_star T' :=
  GM15.theorem_3_3_proof G H η θ_star θ φ T_star T Λ P a b h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

open scoped unitInterval in
open Metric Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM12 GM14 in
/-- **Graph Minors XV, (3.4)** (pages 122–123): "Let $\Sigma$ be a surface and let $k \ge 3$ be an
integer. Let $\mathscr{T}^*$ be a tangle in a graph $G$, and let $H, \mathscr{T}$ be a $\Sigma$-span
of order $\theta$. Let $\Lambda \subseteq \Sigma$ be a region of $H$ such that $H \cap bd(\Lambda)$
is a circuit, and let $v_1, \dots, v_{2k}$ be distinct vertices of this circuit, in order, such that
$\{v_1, \dots, v_{2k}\}$ is free with respect to $\mathscr{T}$. Let $H' \subseteq G$ be a drawing in
$\Sigma$ such that $H' \cap (\Sigma - \Lambda) = H$ and $H' = H \cup P_1 \cup \dots \cup P_{k-1}$,
where $P_i$ is a path with ends $v_i, v_{2k-i}$ for $1 \le i \le k - 1$. Let $\mathscr{T}'$ be a
tangle in $H'$ induced by $\mathscr{T}$; then $H', \mathscr{T}'$ is a $\Sigma$-span of order
$\theta$. Moreover, let $r_1, r_2 \subseteq \Lambda$ be the regions of $H'$ incident with $v_k,
v_{2k}$ respectively; then $d'(r_1, r_2) \ge 2k - 6$, and $d'(v_k, v_{2k}) \ge 2k - 8$, where $d'$
is the metric of $\mathscr{T}'."

Here "$H' \subseteq G$" means that the span embedding `η'` of $H'$ agrees with `η` on $H$. We add
that each $P_i$ meets $H$ only in its ends and that the paths are disjoint, without which the
statement is false. See the correction to (3.4) in `corrections/GM15.md`. -/
theorem theorem_3_4 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (Λ : Set S)
    (v : Fin (2 * k) → S) (H' : Drawing S) (η' : SpanEmbedding H' G)
    (P : Fin (k - 1) → Drawing S) (i_k i_last : Fin (2 * k))
    (h1 : IsSigmaSpan G H η θ_star θ T_star T) (h2 : HasTangleMetric H θ T d) (h3 : Λ ∈ H.R)
    (h4 : IsOArc (subBd Λ)) (h5 : (H.interSet (subBd Λ)).IsCircuit) (h6 : 3 ≤ k)
    (h7 : (List.ofFn v).Nodup) (h8 : GM12.IsListedInOrderOn (subBd Λ) (List.ofFn v))
    (h9 : ∀ i : Fin (2 * k), v i ∈ H.V ∩ subBd Λ) (h10 : IsFreeSet H.toHypergraph T θ (range v))
    (h11 : ∀ x ∈ H.V, η'.vMap x = η.vMap x) (h12 : ∀ e ∈ H.E, η'.eMap e = η.eMap e)
    (h13 : H'.interSet (univ \ Λ) = H)
    (h14 : H'.V = H.V ∪ ⋃ j : Fin (k - 1), (P j).V)
    (h15 : H'.E = H.E ∪ ⋃ j : Fin (k - 1), (P j).E)
    (h16 : ∀ j : Fin (k - 1),
      (P j).IsPathBetween (v ⟨j.1, by omega⟩) (v ⟨2 * k - 2 - j.1, by omega⟩))
    (h17 : ∀ j : Fin (k - 1),
      (P j).U ∩ H.U = {v ⟨j.1, by omega⟩, v ⟨2 * k - 2 - j.1, by omega⟩})
    (h18 : Pairwise (fun j₁ j₂ => Disjoint (P j₁).U (P j₂).U)) (h19 : i_k.1 = k - 1)
    (h20 : i_last.1 = 2 * k - 1) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ)
      (r₁ r₂ : Set S), IsSigmaSpan G H' η' θ_star θ T_star T' ∧ HasTangleMetric H' θ T' d' ∧
    r₁ ∈ H'.R ∧ r₂ ∈ H'.R ∧ r₁ ⊆ Λ ∧ r₂ ⊆ Λ ∧ H'.U \ Λ = H.U ∧ T' =
    GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ ∧ (∀ x ∈ H.A, ∀ y ∈ H.A, d x y ≤ d' x y) ∧
    IsOArc (subBd r₁) ∧ IsOArc (subBd r₂) ∧ (H'.interSet (subBd r₁)).IsCircuit ∧
    (H'.interSet (subBd r₂)).IsCircuit ∧ v i_k ∈ subBd r₁ ∧ v i_last ∈ subBd r₂ ∧
    (∀ w₁ w₂ w₃ w₄ : S, w₁ ∈ H.V ∩ subBd Λ → w₂ ∈ H.V ∩ subBd Λ → w₃ ∈ H.V ∩ subBd Λ →
      w₄ ∈ H.V ∩ subBd Λ →
      (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃,
          w₄] ++ List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)).Nodup →
      GM12.IsListedInOrderOn (subBd Λ) (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁,
          w₂, w₃, w₄] ++ List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)) →
      w₁ ∈ (H'.interSet (subBd r₁)).V ∧ w₂ ∈ (H'.interSet (subBd r₁)).V ∧
      w₃ ∈ (H'.interSet (subBd r₁)).V ∧ w₄ ∈ (H'.interSet (subBd r₁)).V ∧
      OccurInCircuitOrder (H'.interSet (subBd r₁)) w₁ w₂ w₃ w₄) ∧
    (∀ u₁ u₂ u₃ u₄ : S, u₁ ∈ H.V ∩ subBd Λ → u₂ ∈ H.V ∩ subBd Λ → u₃ ∈ H.V ∩ subBd Λ →
      u₄ ∈ H.V ∩ subBd Λ →
      (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]).Nodup →
      GM12.IsListedInOrderOn (subBd Λ) (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1,
            by omega⟩) ++ [u₁, u₂, u₃, u₄]) → u₁ ∈ (H'.interSet (subBd r₂)).V ∧
      u₂ ∈ (H'.interSet (subBd r₂)).V ∧ u₃ ∈ (H'.interSet (subBd r₂)).V ∧
      u₄ ∈ (H'.interSet (subBd r₂)).V ∧ OccurInCircuitOrder (H'.interSet (subBd r₂)) u₁ u₂ u₃ u₄) ∧
    2 * k - 6 ≤ d' r₁ r₂ ∧ 2 * k - 8 ≤ d' {v i_k} {v i_last} :=
  GM15.theorem_3_4_proof G H η θ_star θ k T_star T d Λ v H' η' P i_k i_last h1 h2 h3 h4 h5 h6 h7
    h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (3.5)** (pages 123–124): "Let $\Sigma$ be a surface and let $\phi \ge 3$ be
an integer. Let $\mathscr{T}^*$ be a tangle in a graph $G$, and let $H, \eta, \mathscr{T}$ be a
$\Sigma$-span. Let $\Lambda_1, \Lambda_2 \subseteq \Sigma$ be distinct regions of $H$ so that $H
\cap bd(\Lambda_i)$ is a circuit $C_i$ ($i = 1, 2$), and no region of $H$ is incident with a vertex
in $C_1$ and with a vertex in $C_2$. Let $a_1, \dots, a_\phi$ be distinct vertices of $C_1$ in
order, and let $b_1, \dots, b_\phi$ be distinct vertices of $C_2$ in order (under some orientations
of $C_1$ and $C_2$), such that $\{a_1, \dots, a_\phi\}$ and $\{b_1, \dots, b_\phi\}$ are free with
respect to $\mathscr{T}$. For $1 \le i \le \phi$ let $P_i$ be an $\eta(H)$-path with ends
$\eta(a_i), \eta(b_i)$, such that $P_1, \dots, P_\phi$ are mutually disjoint. Then there is a
$\Sigma'$-span of order $\phi$, where $\Sigma'$ is a surface obtained by adding a handle to
$\Sigma$."

Adding a handle between two distinct regions `Λ₁, Λ₂` along `φ` disjoint `η(H)`-paths `P_i` yields
a `Σ'`-span `(H', η', T')` of order `φ`.

The Lean adds the line condition of Graph Minors XII, (5.1), without which the print fails. See
the correction to (3.5) in `corrections/GM15.md`. -/
theorem theorem_3_5 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ φ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (Λ₁ Λ₂ : Set S) (P : Fin φ → Graph α β)
    (a b : Fin φ → S) (h1 : IsSigmaSpan G H η θ_star θ T_star T) (h2 : Λ₁ ∈ H.R) (h3 : Λ₂ ∈ H.R)
    (h4 : Λ₁ ≠ Λ₂) (h5 : IsOArc (subBd Λ₁)) (h6 : IsOArc (subBd Λ₂))
    (h7 : (H.interSet (subBd Λ₁)).IsCircuit) (h8 : (H.interSet (subBd Λ₂)).IsCircuit)
    (h9 : ∀ r ∈ H.R, (closure r ∩ (H.V ∩ subBd Λ₁)).Nonempty →
      Disjoint (closure r) (H.V ∩ subBd Λ₂))
    (h10 : ∀ F : Set S, IsLine F → H.IsNormal F → F ⊆ univ \ (Λ₁ ∪ Λ₂) → (F ∩ subBd Λ₁).Nonempty →
      (F ∩ subBd Λ₂).Nonempty → φ ≤ (F ∩ H.V).ncard) (h11 : 3 ≤ φ) (h12 : φ ≤ θ)
    (h13 : (List.ofFn a).Nodup) (h14 : (List.ofFn b).Nodup)
    (h15 : GM12.IsListedInOrderOn (subBd Λ₁) (List.ofFn a))
    (h16 : GM12.IsListedInOrderOn (subBd Λ₂) (List.ofFn b))
    (h17 : ∀ i : Fin φ, a i ∈ H.V ∩ subBd Λ₁ ∧ b i ∈ H.V ∩ subBd Λ₂)
    (h18 : ∀ i : Fin φ, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (a i)) (η.vMap (b i)))
    (h19 : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (h20 : IsFreeSet H.toHypergraph T θ (range a)) (h21 : IsFreeSet H.toHypergraph T θ (range b)) :
    ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'), IsObtainedByAddingHandle S S' ∧
    ∃ (H' : Drawing S') (η' : SpanEmbedding H' G)
    (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
    IsSigmaSpan G H' η' θ_star φ T_star T' :=
  GM15.theorem_3_5_proof G H η θ_star θ φ T_star T Λ₁ Λ₂ P a b h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21

/-! ## Section 4. Rearrangement -/

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (4.1)** (pages 124–125): "Let $\mathcal{T}$ be a respectful tangle of order
$\theta$ in a 2-cell drawing $H$ in a surface $\Sigma$. Let $H_1, H_2$ be 2-cell drawings in
$\Sigma$, and for $i = 1, 2$ let $\mathcal{T}_i$ be a $\lambda_i$-compression of $\mathcal{T}$ in
$H_i$. Let $H_1, H_2$ have radial drawings $K_1, K_2$. Then for every $W$ which is a closed walk of
a common subdrawing of $K_1$ and $K_2$, if $ins_1(W)$, $ins_2(W)$ are both defined then they are
equal. In particular, if $H_1 = H_2$ and $\lambda_1 \ge \lambda_2$, then $\mathcal{T}_1 \subseteq
\mathcal{T}_2$."

Slope agreement for compressions `T₁, T₂` of `T`, and `T₁ ⊆ T₂` when `H₁ = H₂` and `λ₁ ≥ λ₂`.
Proved from Graph Minors XI, (8.12) (`exists_atom_dist_eq_theta`). -/
theorem theorem_4_1 {S : Type w} [TopologicalSpace S] [T2Space S] (H H₁ H₂ K₁ K₂ : Drawing S)
    (θ lam₁ lam₂ : ℕ) (T T₁ T₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d d₁ d₂ : Set S → Set S → ℕ) (ins₁ ins₂ : Drawing S → Set S) (h1 : IsClosedSurface S)
    (h2 : IsLambdaCompression H H₁ θ lam₁ T T₁ d d₁)
    (h3 : IsLambdaCompression H H₂ θ lam₂ T T₂ d d₂)
    (h4 : (PaintingOrDrawing.drawing H₁).IsRadialDrawing K₁)
    (h5 : IsDerivedSlope (PaintingOrDrawing.drawing H₁) K₁ (θ - lam₁) T₁ ins₁)
    (h6 : ∀ x ∈ H₁.A, ∀ y ∈ H₁.A, d₁ x y = tangleMetric H₁ K₁ ins₁ (θ - lam₁) x y)
    (h7 : (PaintingOrDrawing.drawing H₂).IsRadialDrawing K₂)
    (h8 : IsDerivedSlope (PaintingOrDrawing.drawing H₂) K₂ (θ - lam₂) T₂ ins₂)
    (h9 : ∀ x ∈ H₂.A, ∀ y ∈ H₂.A, d₂ x y = tangleMetric H₂ K₂ ins₂ (θ - lam₂) x y) :
    (∀ (u₁ u₂ : S) (W₁ : GraphWalk K₁.toGraph u₁ u₁) (W₂ : GraphWalk K₂.toGraph u₂ u₂),
      walkDrawing K₁ W₁ = walkDrawing K₂ W₂ → W₁.length < 2 * (θ - lam₁) → W₂.length <
      2 * (θ - lam₂) → insWalk ins₁ K₁ W₁ = insWalk ins₂ K₂ W₂) ∧
    (H₁ = H₂ → K₁ = K₂ → lam₂ ≤ lam₁ → T₁ ⊆ T₂) :=
  GM15.theorem_4_1_proof H H₁ H₂ K₁ K₂ θ lam₁ lam₂ T T₁ T₂ d d₁ d₂ ins₁ ins₂ h1 h2 h3 h4 h5 h6 h7 h8 h9

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (4.2)** (page 125): "Let $H, H'$ be 2-cell drawings in a surface $\Sigma$,
and let $Z \subseteq \Sigma$ include every atom of $H$ which is not in $A(H')$. (Hence $Z$ includes
every atom of $H'$ not in $A(H)$.) Let $\mathcal{T}, \mathcal{T}'$ be respectful tangles in $H, H'$
respectively, such that, for some $\lambda \ge 0$, one of $\mathcal{T}, \mathcal{T}'$ is a
$\lambda$-compression of the other. Then for all $x, y \in \Sigma$, if $d(x, y) < d(x, \sigma)$ for
all $\sigma \in Z$, and $d(x, y) < ord(\mathcal{T})$, then $d'(x, y) \le d(x, y)$."

Distance bound `d'(x, y) ≤ d(x, y)` away from `Z`.
Proved from `(4.1)` (`theorem_4_1_proof`), Graph Minors XII, `(7.7)` (`GM12Theorem77Statement`), and
Graph Minors XIV, `(3.1)` (`GM14.theorem_3_1_proof`). -/
theorem theorem_4_2 {S : Type w} [TopologicalSpace S] [T2Space S] (H H' : Drawing S) (Z : Set S)
    (θ θ' lam : ℕ) (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d d' : Set S → Set S → ℕ) (x y : S) (h1 : IsClosedSurface S) (h2 : ConnectedSpace S)
    (h3 : HasTangleMetric H θ T d) (h4 : HasTangleMetric H' θ' T' d')
    (h5 : ∀ a ∈ H.A, a ∉ H'.A → a ⊆ Z)
    (h6 : IsLambdaCompression H H' θ lam T T' d d' ∨ IsLambdaCompression H' H θ' lam T' T d' d)
    (h7 : ∀ σ ∈ Z, pointDist H d x y < pointDist H d x σ) (h8 : pointDist H d x y < θ) :
    pointDist H' d' x y ≤ pointDist H d x y :=
  GM15.theorem_4_2_proof H H' Z θ θ' lam T T' d d' x y h1 h2 h3 h4 h5 h6 h7 h8

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (4.3)** (page 125): "If $H, \Sigma, \mathcal{T}, \theta, d, \lambda, z$ are
as above then $H - z^\lambda$ is 2-cell."

For a 2-cell drawing `H` with `E(H) ≠ ∅` in a connected surface `Σ` with a respectful tangle `T`
of order `θ` with metric `d`, `z ∈ A(H)`, `λ < θ`, and `λ ≥ 2` if `z ∈ E(H)`, the subdrawing
`H - z^λ` is 2-cell.
Proved from Graph Minors XII, (7.11) (`GM12.gm12_theorem_7_11`). -/
theorem theorem_4_3 {S : Type w} [TopologicalSpace S] [T2Space S] (H : Drawing S) (θ lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (z : Set S)
    (h1 : IsClosedSurface S) (h2 : ConnectedSpace S) (h3 : HasTangleMetric H θ T d)
    (h4 : H.E.Nonempty) (h5 : z ∈ H.A) (h6 : lam < θ) (h7 : z ∈ H.E → 2 ≤ lam) :
    (PaintingOrDrawing.drawing (deleteAtomNeighborhood H d z lam)).IsTwoCell :=
  GM15.theorem_4_3_proof H θ lam T d z h1 h2 h3 h4 h5 h6 h7

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (4.4)** (page 126): "Let $\mathcal{T}$ be a respectful tangle of order
$\theta$ in a 2-cell drawing $H$ in a surface $\Sigma$. Let $z \in A(H)$, let $\lambda \ge 2$ be an
integer with $\theta > 4\lambda + 2$, and let $H' \subseteq H$ be a 2-cell subdrawing such that $a
\in A(H')$ for every $a \in A(H)$ with $d(z, a) > \lambda$. Then there is a unique respectful tangle
$\mathcal{T}'$ in $H'$ which is a $(4\lambda + 2)$-compression of $\mathcal{T}$, and it includes $(A
\cap H', B \cap H')$ for every $(A, B) \in \mathcal{T}$ of order $< \theta - 4\lambda - 2$."

Unique `(4λ + 2)`-compression of `T` in a 2-cell subdrawing `H' ⊆ H` containing all atoms `a ∈ A(H)`
with `d(z, a) > λ`.
Proved from Graph Minors XII, (7.10) (`GM12Theorem710Statement`). -/
theorem theorem_4_4 {S : Type w} [TopologicalSpace S] [T2Space S] (H H' : Drawing S) (θ lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (z : Set S)
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hMetric : HasTangleMetric H θ T d)
    (hz : z ∈ H.A) (hlam : 2 ≤ lam) (hθ : 4 * lam + 2 < θ) (hSub : H'.IsSubdrawing H)
    (h2cell : (PaintingOrDrawing.drawing H').IsTwoCell) (hAtoms : ∀ a ∈ H.A, lam < d z a → a ∈ H'.A) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ),
    IsLambdaCompression H H' θ (4 * lam + 2) T T' d d' ∧
    (∀ A B : Hypergraph S (Set S), (A, B) ∈ T → separationOrder A B < θ - (4 * lam + 2) →
      (A ∩ H'.toHypergraph, B ∩ H'.toHypergraph) ∈ T') ∧
    (∀ (T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d'' : Set S → Set S → ℕ),
      IsLambdaCompression H H' θ (4 * lam + 2) T T'' d d'' → T'' = T') :=
  GM15.theorem_4_4_proof H H' θ lam T d z hS hConn hMetric hz hlam hθ hSub h2cell hAtoms

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (4.5)** (page 126): "Let $\mathcal{T}$ be a respectful tangle of order
$\theta$ in a 2-cell drawing $H$ in a surface $\Sigma$. Let $z \in A(H)$, let $\lambda \ge 2$ be an
integer with $\theta > 4\lambda + 2$, and let $H'$ be a 2-cell drawing in $\Sigma$ such that $a \in
A(H')$ for every $a \in A(H)$ with $d(z, a) > \lambda$. Then (i) there is a unique $(4\lambda +
2)$-compression $\mathcal{T}'$ of $\mathcal{T}$ in $H'$ (ii) $H - z^\lambda \subseteq H'$, and
$\mathcal{T}'$ is the tangle induced in $H'$ from the unique $(4\lambda + 2)$-compression of
$\mathcal{T}$ in $H - z^\lambda$ (iii) if $H' \subseteq H$ then $(A \cap H', B \cap H') \in
\mathcal{T}'$ for every $(A, B) \in \mathcal{T}$ of order $< \theta - 4\lambda - 2$."

Existence and uniqueness of the `(4λ + 2)`-compression `T'` of `T` in `H'`, with `H - z^λ ⊆ H'` and
`T'` induced in `H'` from the `(4λ + 2)`-compression `T₀` of `T` in `H - z^λ`.
Proved from `(4.1)`, `(4.3)`, Graph Minors XII, `(7.7)`, `(7.10)`, and `(7.11)`. -/
theorem theorem_4_5 {S : Type w} [TopologicalSpace S] [T2Space S] (H H' : Drawing S) (θ lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (z : Set S)
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hMetric : HasTangleMetric H θ T d)
    (hz : z ∈ H.A) (hlam : 2 ≤ lam) (hθ : 4 * lam + 2 < θ)
    (h2cell' : (PaintingOrDrawing.drawing H').IsTwoCell)
    (hAtoms : ∀ a ∈ H.A, lam < d z a → a ∈ H'.A) :
    (deleteAtomNeighborhood H d z lam).IsSubdrawing H' ∧
    ∃ (T₀ T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d₀ d' : Set S → Set S → ℕ),
    IsLambdaCompression H (deleteAtomNeighborhood H d z lam) θ (4 * lam + 2) T T₀ d d₀ ∧
    IsLambdaCompression H H' θ (4 * lam + 2) T T' d d' ∧ T' =
    GM10.inducedTangle H'.toHypergraph (deleteAtomNeighborhood H d z lam).toHypergraph T₀
    (θ - (4 * lam + 2)) ∧
    (∀ (T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d'' : Set S → Set S → ℕ),
      IsLambdaCompression H H' θ (4 * lam + 2) T T'' d d'' → T'' = T') :=
  GM15.theorem_4_5_proof H H' θ lam T d z hS hConn hMetric hz hlam hθ h2cell' hAtoms

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (4.6)** (page 126): "Let $\mathcal{T}, \theta, H, \Sigma, z, \lambda, H',
\mathcal{T}'$ be as in (4.5). Let $\mathcal{T}^*$ be a tangle in a graph $G$, and let $H, \eta,
\mathcal{T}$ be a $\Sigma$-span in $G$ with respect to $\mathcal{T}^*$. Let $H'$ be rigid, and let
$\eta'$ be an isomorphism from $H'$ to a subgraph of $G$, such that $\eta'(x) = \eta(x)$ for every
vertex or edge $x$ of $H$ with $d(z, x) > \lambda$. Then $H', \eta', \mathcal{T}'$ is a
$\Sigma$-span of order $\theta - 4\lambda - 2$, obtained from $H, \eta, \mathcal{T}$ by rearranging
within $\lambda$ of $z$."

If `H, η, T` is a `Σ`-span in `G` with respect to `T*`, `H'` is a rigid 2-cell drawing containing
all atoms `a ∈ A(H)` with `d(z, a) > λ`, `η'` agrees with `η` on vertices and edges with distance
`> λ` from `z`, and `T'` is a `(4λ + 2)`-compression of `T` in `H'`, then `H', η', T'` is a `Σ`-span
obtained from `H, η, T` by rearranging within `λ` of `z`.
Proved from `(4.5)` and Graph Minors XII, `(7.7)`, `(7.10)`, and `(7.11)`. -/
theorem theorem_4_6 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H H' : Drawing S) (η : SpanEmbedding H G) (η' : SpanEmbedding H' G)
    (θ_star θ lam : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d d' : Set S → Set S → ℕ)
    (z : Set S) (h1 : IsSigmaSpan G H η θ_star θ T_star T) (h2 : HasTangleMetric H θ T d)
    (h3 : z ∈ H.A) (h4 : 2 ≤ lam) (h5 : 4 * lam + 2 < θ) (h6 : IsRigid H')
    (h7 : (PaintingOrDrawing.drawing H').IsTwoCell) (h8 : ∀ a ∈ H.A, lam < d z a → a ∈ H'.A)
    (h9 : ∀ v ∈ H.V, lam < d z {v} → v ∈ H'.V ∧ η'.vMap v = η.vMap v)
    (h10 : ∀ e ∈ H.E, lam < d z e → e ∈ H'.E ∧ η'.eMap e = η.eMap e)
    (h11 : IsLambdaCompression H H' θ (4 * lam + 2) T T' d d') :
    IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z :=
  GM15.theorem_4_6_proof G H H' η η' θ_star θ lam T_star T T' d d' z h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (4.7)** (pages 127–128): "Let $\mathcal{T}$ be a respectful tangle of order
$\theta$ in a 2-cell drawing $H$ in a surface $\Sigma$. Let $z \in A(H)$, let $\lambda \ge 2$ be an
integer, and let $X \subseteq V(H)$ be free with respect to $\mathcal{T}$. Suppose that $d(z, v) >
2|X| + 5\lambda + 2$ for all $v \in X$. Now let $H'$ be a 2-cell drawing in $\Sigma$ such that $a
\in A(H')$ for every $a \in A(H)$ with $d(z, a) > \lambda$; and let $\mathcal{T}'$ be a $(4\lambda +
2)$-compression of $\mathcal{T}$ in $H'$. Then $X$ is free with respect to $\mathcal{T}'$."

Preservation of a free set `X ⊆ V(H)` with `d(z, v) > 2|X| + 5λ + 2` for all `v ∈ X` under a
`(4λ + 2)`-compression `T'` of `T` in `H'`.
Proved from `(4.4)`, `(4.5)`, Graph Minors XI, `(9.1)`, and Graph Minors XII, `(4.1)`,
`(7.7)`, `(7.10)`, and `(7.11)`. -/
theorem theorem_4_7 {S : Type w} [TopologicalSpace S] [T2Space S] (H H' : Drawing S) (θ lam : ℕ)
    (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d d' : Set S → Set S → ℕ)
    (z : Set S) (X : Set S) (h1 : IsClosedSurface S) (h2 : ConnectedSpace S)
    (h3 : HasTangleMetric H θ T d) (h4 : z ∈ H.A) (h5 : 2 ≤ lam)
    (h6 : IsFreeSet H.toHypergraph T θ X) (h7 : ∀ v ∈ X, 2 * X.ncard + 5 * lam + 2 < d z {v})
    (h8 : (PaintingOrDrawing.drawing H').IsTwoCell) (h9 : ∀ a ∈ H.A, lam < d z a → a ∈ H'.A)
    (h10 : IsLambdaCompression H H' θ (4 * lam + 2) T T' d d') :
    IsFreeSet H'.toHypergraph T' (θ - (4 * lam + 2)) X :=
  GM15.theorem_4_7_proof H H' θ lam T T' d d' z X h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

/-! ## Section 5. Flatness -/

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (5.1)** (page 129): "Let $\mathscr{T}^*$ be a tangle in $G$, and let $H,
\eta, \mathscr{T}$ be a $(\lambda, \mu)$-flat $\Sigma$-span of order $\theta$. Let $0 \le \lambda_1
\le \lambda$, let $\mu_1 \ge \mu$ and let $1 \le \theta_1 \le \theta$, such that $\theta_1 \ge
4\lambda_1 + \mu_1 + 2$; and let $\mathscr{T}_1$ be the $\theta_1$-truncation of $\mathscr{T}$. Then
$(H, \eta, \mathscr{T}_1)$ is $(\lambda_1, \mu_1)$-flat."

Truncation and monotonicity of `(λ, μ)`-flat `Σ`-spans.
Proved from `(4.1)`, `(4.5)`, `(4.6)`, and Graph Minors XII, `(7.7)`, `(7.10)`, `(7.11)`. -/
theorem theorem_5_1 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ θ₁ lam lam₁ μ μ₁ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (h1 : IsFlatSpan G H η θ_star θ lam μ T_star T) (h2 : lam₁ ≤ lam) (h3 : μ ≤ μ₁) (h4 : 1 ≤ θ₁)
    (h5 : θ₁ ≤ θ) (h6 : 4 * lam₁ + μ₁ + 2 ≤ θ₁) (h7 : lam₁ < lam → 4 * lam + 2 < θ)
    (h8 : θ₁ - (4 * lam₁ + 2) < θ - (4 * lam + 2) → 2 ≤ lam) :
    IsFlatSpan G H η θ_star θ₁ lam₁ μ₁ T_star (GM10.truncation T θ₁) :=
  GM15.theorem_5_1_proof G H η θ_star θ θ₁ lam lam₁ μ μ₁ T_star T h1 h2 h3 h4 h5 h6 h7 h8

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (5.2)** (page 129): "Let $\mathscr{T}^*$ be a tangle in a graph $G$, let
$\Sigma$ be a surface, and let $H, \eta, \mathscr{T}$ be a $(\lambda, \mu)$-flat $\Sigma$-span of
order $\theta$. Let $\lambda_1, \lambda_2 \ge 4$ and $\mu \ge 0$ be integers such that $\lambda \ge
6\lambda_1 + 5\lambda_2 + 3\mu + 4$. Let $z_1 \in A(H)$, and let $H', \eta', \mathscr{T}'$ be a
$\Sigma$-span obtained from $H, \eta, \mathscr{T}$ by rearranging within $\lambda_1$ of $z_1$. Then
$H', \eta', \mathscr{T}'$ is $(\lambda_2, \mu)$-flat."

If `H, η, T` is a `(λ, μ)`-flat `Σ`-span of order `θ`, `λ₁, λ₂ ≥ 4`,
`λ ≥ 6λ₁ + 5λ₂ + 3μ + 4`, and `H', η', T'` is obtained from `H, η, T` by rearranging within `λ₁`
of `z₁ ∈ A(H)`, then `H', η', T'` is `(λ₂, μ)`-flat.
Proved from `(4.1)`, `(4.2)`, `(4.5)`, `(4.6)`, and Graph Minors XII, `(7.7)`, `(7.10)`, `(7.11)`.

The Lean assumes `1 ≤ μ`. See the correction to (5.2) in `corrections/GM15.md`. -/
theorem theorem_5_2 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H H' : Drawing S) (η : SpanEmbedding H G) (η' : SpanEmbedding H' G)
    (θ_star θ lam lam₁ lam₂ μ : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d d' : Set S → Set S → ℕ)
    (z₁ : Set S) (h1 : IsFlatSpan G H η θ_star θ lam μ T_star T) (h2 : μ = 0 → 4 * lam + 2 < θ)
    (h3 : 4 ≤ lam₁) (h4 : 4 ≤ lam₂) (h5 : 6 * lam₁ + 5 * lam₂ + 3 * μ + 4 ≤ lam)
    (h6 : IsRearrangedWithin G H H' η η' θ_star θ lam₁ T_star T T' d d' z₁) :
    IsFlatSpan G H' η' θ_star (θ - (4 * lam₁ + 2)) lam₂ μ T_star T' :=
  GM15.theorem_5_2_proof G H H' η η' θ_star θ lam lam₁ lam₂ μ T_star T T' d d' z₁ h1 h2 h3 h4 h5 h6

/-! ## Section 6. Crooked Transactions -/

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (6.1)** (page 134): "Let $\pi \ge 2$ be an integer, with $\pi \ne 3$, and let
$(G, \Omega)$ be a society with no crooked transaction of cardinality $\pi$. Then there is a
segregation $\mathcal{S}$ of $G$ of type $(3\pi + 9, 1)$ with $\bar{\Omega} \subseteq
V(\mathcal{S})$, and an arrangement $\alpha$ of $\mathcal{S}$ in a closed disc $\Delta$, such that
$\Omega = \alpha^{-1}(bd(\Delta))$."

Every society `(G, Ω)` with no crooked transaction of cardinality `π` (`π ≥ 2`, `π ≠ 3`) admits a
segregation `S_seg` of `G` of type `(3π + 9, 1)` with `Ω̄ ⊆ V(S_seg)` and an arrangement in a closed
disc `Δ` with `Ω = α⁻¹(bd(Δ))`.
Proved from Graph Minors IX, (11.11) (`GM09Theorem1111Statement`). -/
theorem theorem_6_1 {α : Type u} {β : Type v} (S : Society α β) (π : ℕ) (hπ2 : 2 ≤ π) (hπ3 : π ≠ 3)
    (hno_crooked : ∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ π) :
    ∃ (S_seg : Set (Society α β)) (k : ℕ) (A₀ : Society α β) (A : Fin k →
      Society α β) (Δ α₀ : Set EuclideanPlane) (α_disc : Fin k → Set EuclideanPlane) (α_pt : α →
      EuclideanPlane), S_seg = insert A₀ (range A) ∧ IsSegregationOfType S.G (3 * π + 9) 1 S_seg ∧
    S.Ω.bar ⊆ segregationVertices S_seg ∧ IsDiscArrangement S A₀ A Δ α₀ α_disc α_pt :=
  GM15.theorem_6_1_proof S π hπ2 hπ3 hno_crooked

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (6.2)** (page 134): "Let $\phi \ge 2$, $\tau_1 \ge 3$, $\tau_2 \ge 4$ be
integers. Let $\mathcal{P}$ be a crooked transaction in a society $(G, \Omega)$ such that
$|\mathcal{P}| \ge (\phi - 1)(2\tau_i + \tau_2 - 7)$. Then there exists $\mathcal{P}' \subseteq
\mathcal{P}$ such that either (i) $|\mathcal{P}'| = \phi$ and $\mathcal{P}'$ is a crosscap
transaction, or (ii) $|\mathcal{P}'| = \tau_1$ and $\mathcal{P}'$ is a leap transaction, or (iii)
$|\mathcal{P}'| = \tau_2$ and $\mathcal{P}'$ is a doublecross transaction."

Every crooked transaction of cardinality `≥ (φ - 1)(2τ₁ + τ₂ - 7)` contains a crosscap transaction
of cardinality `φ`, a leap transaction of cardinality `τ₁`, or a doublecross transaction of
cardinality `τ₂`.
Proved from Graph Minors IX, (7.1) (`GM09Theorem71Statement`). The print has $2\tau_i$, a
misprint for $2\tau_1$, which the Lean uses. See the correction to (6.2) in `corrections/GM15.md`.
-/
theorem theorem_6_2 {α : Type u} {β : Type v} (S : Society α β) (φ τ₁ τ₂ : ℕ)
    (P_set : Set (Graph α β)) (h1 : 2 ≤ φ) (h2 : 3 ≤ τ₁) (h3 : 4 ≤ τ₂)
    (h4 : S.IsCrookedTransaction P_set) (h5 : (φ - 1) * (2 * τ₁ + τ₂ - 7) ≤ P_set.ncard) :
    ∃ P' ⊆ P_set, (P'.ncard = φ ∧ S.IsCrosscapTransaction P') ∨
    (P'.ncard = τ₁ ∧ S.IsLeapTransaction P') ∨ (P'.ncard = τ₂ ∧ S.IsDoublecrossTransaction P') :=
  GM15.theorem_6_2_proof S φ τ₁ τ₂ P_set h1 h2 h3 h4 h5

/-! ## Section 7. The Main Proof -/

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (7.1)** (page 135): "There is a $(\lambda, \mu)$-flat $\Sigma$-span of order
$\theta$, with $k$ eyes mutually at distance $\theta$."

Truncating a `(λ, μ)`-flat `Σ`-span `H₀, η₀, T₀` of order `θ₀ ≥ θ` with `k` eyes at distance `≥ θ`
to order `θ` yields a `(λ, μ)`-flat `Σ`-span of order `θ` with `k` eyes mutually at distance `θ`.
Proved from `(5.1)` (`theorem_5_1_proof`). -/
theorem theorem_7_1 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ_star θ₀ θ lam μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d₀ : Set S → Set S → ℕ)
    (h1 : IsFlatSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀) (h2 : HasTangleMetric H₀ θ₀ T₀ d₀)
    (h3 : 2 ≤ lam) (h4 : 4 * lam + μ + 2 ≤ θ) (h5 : 4 ≤ θ) (h6 : θ ≤ θ₀)
    (h7 : HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ k θ) :
    ∃ (H : Drawing S) (η : SpanEmbedding H G)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ) (r : Fin k →
      Set S), IsFlatSpan G H η θ_star θ lam μ T_star T ∧ HasTangleMetric H θ T d ∧ Injective r ∧
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) ∧ (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) :=
  GM15.theorem_7_1_proof G H₀ η₀ θ_star θ₀ θ lam μ k T_star T₀ d₀ h1 h2 h3 h4 h5 h6 h7

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (7.2)** (pages 135–136): "For $1 \le i < j \le k$, if $\sigma_1 \in Z_i$ and
$\sigma_2 \in Z_j$ then $d(\sigma_1, \sigma_2) \ge \theta - 2(\theta' + 12\mu + 14)$, and so $Z_i
\cap Z_j = \emptyset$ and $J_i \cap J_j \subseteq H$."

For `i ≠ j`, points in `Z_i` and `Z_j` are at distance `≥ θ - 2(θ' + 12μ + 14)`, `Z_i ∩ Z_j = ∅`,
and `V(J_i) ∩ V(J_j) ⊆ V(η(H))`. -/
theorem theorem_7_2 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ θ' lam μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (r : Fin k → Set S) (h1 : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (h2 : HasTangleMetric H θ T d) (h3 : 1 ≤ μ) (h4 : 2 * (θ' + 12 * μ + 14) + μ ≤ θ)
    (h5 : Injective r) (h6 : ∀ i : Fin k, IsDrawingEye G H η θ T (r i))
    (h7 : ∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) (i j : Fin k) (h8 : i ≠ j) :
    (∀ σ₁ ∈ eyeAtomZone H d θ' μ (r i), ∀ σ₂ ∈ eyeAtomZone H d θ' μ (r j),
      θ - 2 * (θ' + 12 * μ + 14) ≤ pointDist H d σ₁ σ₂) ∧
    Disjoint (eyeAtomZone H d θ' μ (r i)) (eyeAtomZone H d θ' μ (r j)) ∧
    V(eyeBridgeUnion G H η d θ' μ (r i)) ∩ V(eyeBridgeUnion G H η d θ' μ (r j)) ⊆ V(η.imageGraph) :=
  GM15.theorem_7_2_proof G H η θ_star θ θ' lam μ k T_star T d r h1 h2 h3 h4 h5 h6 h7 i j h8

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (7.3)** (pages 136–137): "If there is a $(3\mu + 3)$-zone $\Lambda \subseteq
\Sigma$ for $H$ such that $H \cap (\Sigma - \Lambda)$ is rigid and such that $\Lambda$ is an eye of
$H \cap (\Sigma - \Lambda)$ in $G_0$ with respect to the tangle of order $\theta - 12\mu - 14$
obtained from $\mathcal{T}$ by clearing $\Lambda$, then (S1) holds."

If there is a `(3μ + 3)`-zone `Λ ⊆ Σ` for `H` such that `H ∩ (Σ - Λ)` is rigid and `Λ` is an eye
of `H ∩ (Σ - Λ)` in `G₀` with respect to the tangle `T₁` obtained from `T` by clearing `Λ`, then
`(S1)` holds.
Proved from `(4.6)`, `(4.7)`, `(5.1)`, `(5.2)`, `(7.1)`, and Graph Minors XI, `(9.1)` and XII,
`(7.7)`, `(7.10)`, `(7.11)`. -/
theorem theorem_7_3 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ θ' lam lam' μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (r : Fin k → Set S) (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r)) (z Λ : Set S)
    (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d₁ : Set S → Set S → ℕ)
    (η' : SpanEmbedding (clearedSubdrawing H Λ) (section7G0 G H η d θ' μ r))
    (h1 : IsFlatSpan G H η θ_star θ lam μ T_star T) (h2 : HasTangleMetric H θ T d) (h3 : 12 ≤ μ)
    (h4 : 4 ≤ lam') (h5 : 4 * lam' + μ + 2 ≤ θ') (h6 : 6 * μ + 14 < θ')
    (h7 : 6 * (3 * μ + 3) + 5 * lam' + 3 * μ + 4 ≤ lam) (h8 : θ' + 12 * μ + 14 ≤ θ)
    (h9 : Injective r) (h10 : ∀ i : Fin k, IsDrawingEye G H η θ T (r i))
    (h11 : ∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) (h12 : ∀ v ∈ H.V, η₀.vMap v = η.vMap v)
    (h13 : ∀ e ∈ H.E, η₀.eMap e = η.eMap e) (h14 : IsLambdaZoneAround H d (3 * μ + 3) z Λ)
    (h15 : IsClearedTangle H T d θ (3 * μ + 3) Λ T₁ d₁) (h16 : IsRigid (clearedSubdrawing H Λ))
    (h17 : ∀ v ∈ (clearedSubdrawing H Λ).V, η'.vMap v = η₀.vMap v)
    (h18 : ∀ e ∈ (clearedSubdrawing H Λ).E, η'.eMap e = η₀.eMap e)
    (h19 : IsDrawingEye (section7G0 G H η d θ' μ r) (clearedSubdrawing H Λ) η'
      (θ - 4 * (3 * μ + 3) - 2) T₁ Λ) : Section7S1 S G θ_star T_star k μ lam' θ' :=
  GM15.theorem_7_3_proof G H η θ_star θ θ' lam lam' μ k T_star T d r η₀ z Λ T₁ d₁ η' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (7.4)** (page 137): "If (S1) does not hold, there is a $\mathcal{T}$-local
3-segregation $\mathcal{S}_0$ of $G_0$ and an arrangement $\alpha_0$ of it in $\Sigma$ compatible
with $H$."

If `(S1)` does not hold, there is a `T`-local 3-segregation `S₀` of `G₀` and an arrangement `α₀`
of it in `Σ` compatible with `H`.
Proved from `(7.3)` (`theorem_7_3_proof`) and Graph Minors XIV, `(10.1)`
(`GM14Theorem101Statement`). -/
theorem theorem_7_4 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ θ' lam lam' μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (r : Fin k → Set S) (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (h1 : IsFlatSpan G H η θ_star θ lam μ T_star T) (h2 : HasTangleMetric H θ T d) (h3 : 12 ≤ μ)
    (h4 : Even μ) (h5 : 4 ≤ lam') (h6 : 4 * lam' + μ + 2 ≤ θ') (h7 : 6 * μ + 14 < θ')
    (h8 : 6 * (3 * μ + 3) + 5 * lam' + 3 * μ + 4 ≤ lam) (h9 : θ' + 16 * μ + 17 ≤ θ)
    (h10 : Injective r) (h11 : ∀ i : Fin k, IsDrawingEye G H η θ T (r i))
    (h12 : ∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) (h13 : ∀ v ∈ H.V, η₀.vMap v = η.vMap v)
    (h14 : ∀ e ∈ H.E, η₀.eMap e = η.eMap e)
    (h15 : ¬ IsMuSteppedSpan (section7G0 G H η d θ' μ r) H η₀ d μ)
    (h16 : ¬ Section7S1 S G θ_star T_star k μ lam' θ') :
    ∃ (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S),
    IsThreeSegregation (section7G0 G H η d θ' μ r) S₀ ∧
    IsTangleLocal (section7G0 G H η d θ' μ r) H η₀ T S₀ ∧ IsSurfaceArrangement S₀ α₀_disc α₀_pt ∧
    IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt :=
  GM15.theorem_7_4_proof G H η θ_star θ θ' lam lam' μ k T_star T d r η₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (7.5)** (pages 138–139): "For $1 \le i \le k$ there is a $(3\beta + 3)$-zone
$\Lambda_i$ around $r_i$ and a closed disc $\Delta_i \subseteq \Sigma$ with $\text{bd}(\Delta_i)$
$\alpha_0$-normal, with the following properties: (i) $\Delta_1, \dots, \Delta_k$ are mutually
disjoint, and for $1 \le i \le k$, $V(J_i \cap H) \subseteq \Delta_i$ (ii) $d(r_i, x) \le 3\beta +
6$ for all $x \in A(H)$ with $x \cap \Delta_i \ne \emptyset$ (iii) $x \subseteq \Delta_i -
\text{bd}(\Delta_i)$ for every $x \in A(H)$ with $d(r_i, x) < \beta$ (iv) $H \cap \overline{\Sigma - \Delta_i}$
has a circuit, and $H \cap \overline{\Sigma - \Lambda_i}$ is rigid (v) for $1 \le i \le k$, one of the
following holds: (a) there is a crooked transaction $\mathcal{P}$ of cardinality $\pi$ in $(G_0 \cup
J_i, \Omega_i)$ (where $\Omega_i$ is a natural order of $V(H) \cap \text{bd}(\Lambda_i)$ from
$\text{bd}(\Lambda_i)$) such that $V(\mathcal{P})$ is free with respect to the $(12\beta +
14)$-compression of $\mathcal{T}$ in $H \cap (\Sigma - \Lambda_i)$, and each $P \in \mathcal{P}$
meets $H \cap (\Sigma - \Lambda_i)$ precisely in the ends of $P$ (b) there is no crooked transaction
of cardinality $\pi$ in $(J_i \cup \alpha_0^{-1}(\Delta_i), \alpha_0^{-1}(\text{bd}(\Delta_i)))$."

For `1 ≤ i ≤ k`, there is a `(3β + 3)`-zone `Λ_i` around `r_i` and a closed disc `Δ_i ⊆ Σ` with
`bd(Δ_i)` `α₀`-normal satisfying `(i)`–`(v)` of `(7.5)`.
Proved from Claim `(1)` (`theorem_7_5_claim_1`), `(4.6)` (`theorem_4_6_proof`), and Graph Minors
XIV,
`(9.6)` (`GM14Theorem96Statement`). -/
theorem theorem_7_5 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ θ' lam π beta μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (r : Fin k → Set S) (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r)) (S₀ : Set (Society α β))
    (α₀_disc : Society α β → Set S) (α₀_pt : α → S) (h1 : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (h2 : HasTangleMetric H θ T d) (h3 : 1 ≤ μ) (h4 : 2 ≤ π) (h5 : π ≠ 3) (h6 : beta = 2 * π + 8)
    (h7 : θ' + 13 * μ + 14 ≤ beta) (h8 : 16 * beta + 17 ≤ θ) (h9 : 6 * beta + 12 < θ)
    (h10 : Injective r) (h11 : ∀ i : Fin k, IsDrawingEye G H η θ T (r i))
    (h12 : ∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) (h13 : ∀ v ∈ H.V, η₀.vMap v = η.vMap v)
    (h14 : ∀ e ∈ H.E, η₀.eMap e = η.eMap e)
    (h15 : IsThreeSegregation (section7G0 G H η d θ' μ r) S₀)
    (h16 : IsTangleLocal (section7G0 G H η d θ' μ r) H η₀ T S₀)
    (h17 : IsSurfaceArrangement S₀ α₀_disc α₀_pt)
    (h18 : IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt) :
    ∃ D : ∀ i : Fin k, Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i,
    Pairwise (fun i j : Fin k => Disjoint (D i).Δ (D j).Δ) :=
  GM15.theorem_7_5_proof G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (7.6)** (page 139): "$G^*_1, \dots, G^*_k$ are mutually disjoint."

`G_1*, ..., G_k*` are mutually disjoint.
Proved from `(7.2)` (`theorem_7_2_proof`) and `(7.5)` (`Section75EyeData`). -/
theorem theorem_7_6 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ θ' lam π beta μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (r : Fin k → Set S) (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r)) (S₀ : Set (Society α β))
    (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (D : ∀ i : Fin k, Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (h1 : IsFlatSpan G H η θ_star θ lam μ T_star T) (h2 : HasTangleMetric H θ T d) (h3 : 1 ≤ μ)
    (h4 : 2 * (θ' + 12 * μ + 14) + μ ≤ θ) (h5 : Injective r)
    (h6 : ∀ i : Fin k, IsDrawingEye G H η θ T (r i)) (h7 : ∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ)
    (h8 : ∀ v ∈ H.V, η₀.vMap v = η.vMap v) (h9 : IsThreeSegregation (section7G0 G H η d θ' μ r) S₀)
    (h10 : IsSurfaceArrangement S₀ α₀_disc α₀_pt)
    (h11 : IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt)
    (h12 : Pairwise (fun i j : Fin k => Disjoint (D i).Δ (D j).Δ)) :
    Pairwise (fun i j : Fin k => Disjoint V((D i).soc_star.G) V((D j).soc_star.G)) :=
  GM15.theorem_7_6_proof G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (7.7)** (pages 139–142): "If there is no crooked transaction of cardinality
$\pi$ in $(G_i^*, \Omega_i^*)$ for $1 \le i \le k$, then (S3) holds."

If there is no crooked transaction of cardinality `π` in `(G_i*, Ω_i*)` for `1 ≤ i ≤ k`, then
`(S3)` holds.
Proved from `(2.1)` (`theorem_2_1_proof`), `(6.1)` (`theorem_6_1_proof`), `(7.6)`
(`theorem_7_6_proof`), and Graph
Minors XIV, `(7.3)` (`gm14_theorem_7_3`). -/
theorem theorem_7_7 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ θ' lam π beta μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (r : Fin k → Set S) (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r)) (S₀ : Set (Society α β))
    (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (D : ∀ i : Fin k, Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (h1 : IsFlatSpan G H η θ_star θ lam μ T_star T) (h2 : HasTangleMetric H θ T d) (h3 : 1 ≤ μ)
    (h4 : 2 ≤ π) (h5 : π ≠ 3) (h6 : beta = 2 * π + 8) (h7 : θ' + 13 * μ + 14 ≤ beta)
    (h8 : 100 * beta ≤ θ) (h9 : Injective r) (h10 : ∀ i : Fin k, IsDrawingEye G H η θ T (r i))
    (h11 : ∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) (h12 : ∀ v ∈ H.V, η₀.vMap v = η.vMap v)
    (h13 : ∀ e ∈ H.E, η₀.eMap e = η.eMap e)
    (h14 : IsThreeSegregation (section7G0 G H η d θ' μ r) S₀)
    (h15 : IsTangleLocal (section7G0 G H η d θ' μ r) H η₀ T S₀)
    (h16 : IsSurfaceArrangement S₀ α₀_disc α₀_pt)
    (h17 : IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt)
    (h18 : Pairwise (fun i j : Fin k => Disjoint (D i).Δ (D j).Δ))
    (h19 : ∀ i : Fin k, ∀ P_set : Set (Graph α β), (D i).soc_star.IsCrookedTransaction P_set →
      P_set.ncard ≠ π) : Section7S3 S G T_star (3 * π + 9) k :=
  GM15.theorem_7_7_proof G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (7.8)** (page 142): "There is a transaction $\mathscr{P}$ in $(G_0 \cup J_1,
\Omega_1)$ such that $V(\mathscr{P})$ is free with respect to the $(12\beta + 14)$-compression of
$\mathscr{T}$ in $H \cap (\Sigma - \Lambda_1)$, each $P \in \mathscr{P}$ meets $H \cap (\Sigma -
\Lambda_1)$ precisely in the ends of $P$, and one of the following holds: (i) $|\mathscr{P}| = \phi$
and $\mathscr{P}$ is a crosscap transaction (ii) $|\mathscr{P}| = \tau_1$ and $\mathscr{P}$ is a
leap transaction (iii) $|\mathscr{P}| = \tau_2$ and $\mathscr{P}$ is a doublecross transaction."

If `(G_i*, Ω_i*)` has a crooked transaction of cardinality `π`, then `(G₀ ∪ J_i, Ω_i)` has a
transaction `P` whose ends are free with respect to `T₁` in `H ∩ (Σ - Λ_i)`, each member of `P`
meets `H ∩ (Σ - Λ_i)` precisely in its ends, and `P` is either a crosscap transaction of size `φ`, a
leap transaction of size `τ₁`, or a doublecross transaction of size `τ₂`.
Proved from `(7.5)` (`Section75EyeData.dichotomy`), `(6.2)` (`theorem_6_2_proof`), and Graph Minors
X,
`(12.2)` (`GM10.IsFreeSet.subset`). -/
theorem theorem_7_8 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ θ' π beta μ φ τ₁ τ₂ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (r : Fin k → Set S) (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (i : Fin k) (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P_star : Set (Graph α β)) (h1 : 2 ≤ φ) (h2 : 3 ≤ τ₁) (h3 : 4 ≤ τ₂)
    (h4 : (φ - 1) * (2 * τ₁ + τ₂ - 7) ≤ π) (h5 : D_i.soc_star.IsCrookedTransaction P_star)
    (h6 : P_star.ncard = π) :
    ∃ (P : Set (Graph α β)) (X : Set S), D_i.soc_Λ.IsTransaction P ∧
    (∀ P₀ ∈ P, ∀ a b : α, D_i.soc_Λ.IsOmegaPathWithEnds P₀ a b →
      IsHPathWithEnds G D_i.η_Λ.imageGraph P₀ a b) ∧ X ⊆
    (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ ∧ D_i.soc_Λ.transactionEnds P = D_i.η_Λ.vMap '' X ∧
    IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁ (θ - 4 * (3 * beta + 3) - 2) X ∧
    ((P.ncard = φ ∧ D_i.soc_Λ.IsCrosscapTransaction P) ∨
      (P.ncard = τ₁ ∧ D_i.soc_Λ.IsLeapTransaction P) ∨
      (P.ncard = τ₂ ∧ D_i.soc_Λ.IsDoublecrossTransaction P)) :=
  GM15.theorem_7_8_proof G H η θ_star θ θ' π beta μ φ τ₁ τ₂ k T_star T d r S₀ α₀_disc α₀_pt i D_i P_star h1 h2 h3 h4 h5 h6

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (7.9)** (page 143): "If $\mathscr{P}$ is a crosscap transaction of
cardinality $\phi$ then (S2) is true."

Graph Minors XV, (7.9), page 143: use the established (3.3) in the transaction argument. -/
theorem theorem_7_9 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ θ' π beta μ φ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (r : Fin k → Set S) (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (i : Fin k) (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P : Set (Graph α β)) (X : Set S) (h1 : 3 ≤ φ) (h2 : φ ≤ θ - 4 * (3 * beta + 3) - 2)
    (h3 : D_i.soc_Λ.IsTransaction P)
    (h4 : ∀ P₀ ∈ P, ∀ a b : α, D_i.soc_Λ.IsOmegaPathWithEnds P₀ a b →
      IsHPathWithEnds G D_i.η_Λ.imageGraph P₀ a b)
    (h5 : X ⊆ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ)
    (h6 : D_i.soc_Λ.transactionEnds P = D_i.η_Λ.vMap '' X)
    (h7 : IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁ (θ - 4 * (3 * beta + 3) - 2) X)
    (h8 : P.ncard = φ) (h9 : D_i.soc_Λ.IsCrosscapTransaction P) : Section7S2 S G θ_star T_star φ :=
  GM15.theorem_7_9_proof G H η θ_star θ θ' π beta μ φ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X h1 h2 h3 h4 h5 h6 h7 h8 h9

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (7.10)** (page 143): "$\mathscr{P}$ is not a leap transaction of cardinality
$\tau_1$."

Graph Minors XV, (7.10), page 143: use the established (3.4) in the transaction argument. -/
theorem theorem_7_10 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ θ' lam π beta μ τ₁ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (r : Fin k → Set S) (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (i : Fin k) (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P : Set (Graph α β)) (X : Set S) (h1 : IsFlatSpan G H η θ_star θ lam μ T_star T) (h2 : 12 ≤ μ)
    (h3 : Even μ) (h4 : τ₁ = 4 + μ / 2) (h5 : 3 * beta + 3 ≤ lam)
    (h6 : 2 * τ₁ < θ - 4 * (3 * beta + 3) - 2) (h7 : D_i.soc_Λ.IsTransaction P)
    (h8 : ∀ P₀ ∈ P, ∀ a b : α, D_i.soc_Λ.IsOmegaPathWithEnds P₀ a b →
      IsHPathWithEnds G D_i.η_Λ.imageGraph P₀ a b)
    (h9 : X ⊆ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ)
    (h10 : D_i.soc_Λ.transactionEnds P = D_i.η_Λ.vMap '' X)
    (h11 : IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁ (θ - 4 * (3 * beta + 3) - 2) X)
    (h12 : P.ncard = τ₁) : ¬ D_i.soc_Λ.IsLeapTransaction P :=
  GM15.theorem_7_10_proof G H η θ_star θ θ' lam π beta μ τ₁ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (7.11)** (page 143): "If $\mathscr{P}$ is a doublecross transaction of
cardinality $\tau_2$ then (S1) holds."

Graph Minors XV, (7.11), page 143: use the established (3.4) in the transaction argument.

The Lean takes `τ₂ = 6 + θ' / 2`, so that the numbers of the proof work out. See the correction to
the proof of (7.11) in `corrections/GM15.md`. -/
theorem theorem_7_11 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ θ' lam lam' π beta μ τ₂ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (r : Fin k → Set S) (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (i : Fin k) (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (P : Set (Graph α β)) (X : Set S) (h1 : IsFlatSpan G H η θ_star θ lam μ T_star T)
    (h2 : HasTangleMetric H θ T d) (h3 : 2 ≤ μ) (h4 : 4 ≤ lam') (h5 : 4 * lam' + μ + 2 ≤ θ')
    (h6 : Even θ') (h7 : τ₂ = 6 + θ' / 2) (h8 : 6 * (3 * beta + 3) + 5 * lam' + 3 * μ + 4 ≤ lam)
    (h9 : θ' + 13 * μ + 14 ≤ beta) (h10 : 100 * beta ≤ θ) (h11 : Injective r)
    (h12 : ∀ j : Fin k, IsDrawingEye G H η θ T (r j))
    (h13 : ∀ j₁ j₂ : Fin k, j₁ ≠ j₂ → d (r j₁) (r j₂) = θ) (h14 : D_i.soc_Λ.IsTransaction P)
    (h15 : ∀ P₀ ∈ P, ∀ a b : α, D_i.soc_Λ.IsOmegaPathWithEnds P₀ a b →
      IsHPathWithEnds G D_i.η_Λ.imageGraph P₀ a b)
    (h16 : X ⊆ (clearedSubdrawing H D_i.Λ).V ∩ subBd D_i.Λ)
    (h17 : D_i.soc_Λ.transactionEnds P = D_i.η_Λ.vMap '' X)
    (h18 : IsFreeSet (clearedSubdrawing H D_i.Λ).toHypergraph D_i.T₁ (θ - 4 * (3 * beta + 3) - 2) X)
    (h19 : P.ncard = τ₂) (h20 : D_i.soc_Λ.IsDoublecrossTransaction P) :
    Section7S1 S G θ_star T_star k μ lam' θ' :=
  GM15.theorem_7_11_proof G H η θ_star θ θ' lam lam' π beta μ τ₂ k T_star T d r S₀ α₀_disc α₀_pt i D_i P X h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20

/-! ## Section 8. Some Mild Improvements -/

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (8.1)** (page 145): "For any surface $\Sigma$ with $\text{bd}(\Sigma) =
\emptyset$, and any integer $p \ge 0$ there exists $\kappa, \phi \ge 0$ such that the following is
true. Let $\mathcal{T}^*$ be a tangle in a graph $G$ of order $\ge p$, and let $H, \eta,
\mathcal{T}$ be a $\Sigma$-span of order $\ge \phi$, with $\ge \kappa$ independent eyes. Then
$\mathcal{T}^*$ controls a $K_p$ minor of $G$."

For any connected surface `Σ` with `bd(Σ) = ∅` and any `p ≥ 0`, there exist `κ, φ ≥ 0` such that if
`T*` is a tangle in `G` of order `≥ p` and `H, η, T` is a `Σ`-span of order `≥ φ` with `≥ κ`
independent eyes, then `T*` controls a `K_p` minor of `G`.
Proved from Graph Minors XII, `(4.5)` (`GM12Theorem45Statement`). -/
theorem theorem_8_1 (S : Type w) [TopologicalSpace S] [T2Space S] (hSurf : IsSurface S)
    (hConn : ConnectedSpace S) (hBd : bd S = ∅) (p : ℕ) :
    ∃ κ φ : ℕ,
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (H : Drawing S) (η : SpanEmbedding H G) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ),
    IsSigmaSpan G H η θ_star θ T_star T → HasTangleMetric H θ T d → p ≤ θ_star → φ ≤ θ →
    HasIndependentEyes G H η θ T d κ → ControlsCliqueMinor G p T_star :=
  GM15.theorem_8_1_proof S hSurf hConn hBd p

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (8.2)** (pages 145–146): "For any surface $\Sigma$ with $\text{bd}(\Sigma) =
\emptyset$, and any integers $p, \phi, \mu \ge 0$, there are integers $\kappa, \theta, \lambda, \rho
\ge 0$ such that the following holds. Let $\mathcal{T}^*$ be a tangle in a graph $G$ such that there
is no $\mathcal{T}^*$-central segregation of $G$ of type $(\rho, \kappa)$ with an arrangement in
$\Sigma$. Then either (i) $\mathcal{T}^*$ controls a $K_p$ minor of $G$, or (ii) there is a
$\Sigma'$-span of order $\ge \phi$, where $\Sigma'$ is a surface obtained by adding a crosscap to
$\Sigma$, or (iii) no $\Sigma$-span of order $\ge \theta$ is $(\lambda, \mu)$-flat."

Proved from `(1.1)` (`theorem_1_1_proof`) and `(8.1)` (`theorem_8_1_proof`). -/
theorem theorem_8_2 (S : Type w) [TopologicalSpace S] [T2Space S] (hSurf : IsSurface S)
    (hConn : ConnectedSpace S) (hBd : bd S = ∅) (p φ μ : ℕ) :
    ∃ (κ θ lam ρ : ℕ),
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)), ¬ Section7S3 S G T_star ρ κ →
    ControlsCliqueMinor G p T_star ∨
    (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'), IsObtainedByAddingCrosscap S S' ∧
      ∃ (H' : Drawing S') (η' : SpanEmbedding H' G) (θ' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))), φ ≤ θ' ∧
      IsSigmaSpan G H' η' θ_star θ' T_star T') ∨
    (∀ (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
      (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d₀ : Set S → Set S → ℕ), θ ≤ θ₀ →
      HasTangleMetric H₀ θ₀ T₀ d₀ → ¬ IsFlatSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀) :=
  GM15.theorem_8_2_proof S hSurf hConn hBd p φ μ

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (8.3)** (pages 146–148): "Let $\lambda, \mu \ge 0$ be integers, let
$\mathcal{T}^*$ be a tangle in a graph $G$, and let $\Sigma$ be a surface with $\text{bd}(\Sigma) =
\emptyset$. Then every $\Sigma$-span which is $(\lambda + \mu + 2, \mu)$-level is $(\lambda,
\mu)$-flat."

Every `(λ + μ + 2, μ)`-level `Σ`-span is `(λ, μ)`-flat. -/
theorem theorem_8_3 {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G) (θ_star θ lam μ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d : Set S → Set S → ℕ)
    (hθ_lt : 4 * (lam + μ + 2) + 2 < θ)
    (hLevel : IsLevelSpan G H η θ_star θ (lam + μ + 2) μ T_star T d) :
    IsFlatSpan G H η θ_star θ lam μ T_star T :=
  GM15.theorem_8_3_proof G H η θ_star θ lam μ T_star T d hθ_lt hLevel

open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 in
/-- **Graph Minors XV, (8.4)** (page 148):
"Choose $\kappa, \theta, \lambda', \rho$ to satisfy (8.2). Let $\lambda = \lambda' + \mu +
2$; and we claim that (8.4) holds. For let $\mathscr{T}^*, G$ be as (8.4). By (8.2), we may
assume that no $\Sigma$-span of order $\ge \theta$ is $(\lambda', \mu)$-flat. By (8.3), no
$\Sigma$-span of order $\ge \theta$ is $(\lambda, \mu)$-level, as required." -/
theorem theorem_8_4 (S : Type w) [TopologicalSpace S] [T2Space S] (hSurf : IsSurface S)
    (hConn : ConnectedSpace S) (hBd : bd S = ∅) (p φ μ : ℕ) :
    ∃ (κ θ lam ρ : ℕ),
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)), ¬ Section7S3 S G T_star ρ κ →
    ControlsCliqueMinor G p T_star ∨
    (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'), IsObtainedByAddingCrosscap S S' ∧
      ∃ (H' : Drawing S') (η' : SpanEmbedding H' G) (θ' : ℕ)
      (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))), φ ≤ θ' ∧
      IsSigmaSpan G H' η' θ_star θ' T_star T') ∨
    (∀ (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
      (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d₀ : Set S → Set S → ℕ), θ ≤ θ₀ →
      ¬ IsLevelSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀ d₀) :=
  GM15.theorem_8_4_proof S hSurf hConn hBd p φ μ

end GraphMinor.GM15
