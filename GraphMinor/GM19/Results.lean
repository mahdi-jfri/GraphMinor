module

public import GraphMinor.GM19.Conditional
public import GraphMinor.GM19.Conditional2
public import GraphMinor.GM19.FeatureCount
public import GraphMinor.GM19.Section10Two
public import GraphMinor.GM19.Section10b
public import GraphMinor.GM19.Section10f
public import GraphMinor.GM19.Section10s
public import GraphMinor.GM19.Section10t
public import GraphMinor.GM19.Section11b
public import GraphMinor.GM19.Section11d
public import GraphMinor.GM19.Section11g
public import GraphMinor.GM19.Section12One
public import GraphMinor.GM19.Section12a
public import GraphMinor.GM19.Section12l
public import GraphMinor.GM19.Section13a
public import GraphMinor.GM19.Section13b
public import GraphMinor.GM19.Section13c
public import GraphMinor.GM19.Section13f
public import GraphMinor.GM19.Section13g
public import GraphMinor.GM19.Section13x
public import GraphMinor.GM19.Section13zf
public import GraphMinor.GM19.Section14ah
public import GraphMinor.GM19.Section15b
public import GraphMinor.GM19.Section15c
public import GraphMinor.GM19.Section15q
public import GraphMinor.GM19.Section2Proved
public import GraphMinor.GM19.Section4a
public import GraphMinor.GM19.Section4b
public import GraphMinor.GM19.Section5a
public import GraphMinor.GM19.Section5g
public import GraphMinor.GM19.Section5oProved
public import GraphMinor.GM19.Section5r
public import GraphMinor.GM19.Section6Five
public import GraphMinor.GM19.Section6Minor
public import GraphMinor.GM19.Section6Seven
public import GraphMinor.GM19.Section6Six
public import GraphMinor.GM19.Section6Two
public import GraphMinor.GM19.Section6aProved
public import GraphMinor.GM19.Section6b
public import GraphMinor.GM19.Section7e
public import GraphMinor.GM19.Section8c
public import GraphMinor.GM19.Section8d
public import GraphMinor.GM19.Section8e
public import GraphMinor.GM19.Section8f
public import GraphMinor.GM19.Section8g
public import GraphMinor.GM19.Section8h
public import GraphMinor.GM19.Section8i
public import GraphMinor.GM19.Section9a
public import GraphMinor.GM19.Section9d
public import GraphMinor.GM19.Section9e

/-!
# Graph Minors XIX: the numbered results

N. Robertson and P. D. Seymour, *Graph Minors. XIX. Well-quasi-ordering on a surface*, J. Combin.
Theory Ser. B **90** (2004), 325–385.

This file lists every numbered result of the paper, in the paper's order and under the paper's
section headings. Each result is stated in full and proved in one line by its proof in the other
files of this folder. The docstrings say where the Lean differs from the print, and
`corrections/GM19.md` lists the corrections to the paper.
-/

public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

universe u w

/-! ## Section 1. Introduction -/

/-! ## Section 2. Surfaces -/

open Function in
/-- **Graph Minors XIX, (2.1)** (page 328): "Let $\Sigma$ be a surface, and let $\Omega$ be a
well-quasi-order. Let $\Gamma_i$ ($i = 1, 2, \dots$) be a countable sequence of internally
3-connected paintings in $\Sigma$, and for each $i \ge 1$ let $\phi_i \colon E(\Gamma_i) \to
E(\Omega)$ be some function. Then there exist $j > i \ge 1$ and a linear inflation $\sigma$ of
$\Gamma_i$ in $\Gamma_j$ satisfying $\phi_i \le \phi_j \circ \sigma$."

(3.1) and the topology of its proof. -/
theorem theorem_2_1 (S : Type u) [TopologicalSpace S] {Ω : Type w} [Preorder Ω] (hS : IsSurface S)
    (hc : ConnectedSpace S) (hwqo : WellQuasiOrderedLE Ω) (Γ : ℕ → Painting S) (φ : ℕ → Set S → Ω)
    (h3 : ∀ i, (Γ i).IsInternallyThreeConnected) :
    ∃ i j, i < j ∧ ∃ (σv : S → Set S) (σe : Set S → Set S),
    IsLinearInflation (Γ i) (Γ j) σv σe ∧ ∀ e ∈ (Γ i).E, φ i e ≤ φ j (σe e) :=
  theorem_2_1_proof S hS hc hwqo Γ φ h3

/-! ## Section 3. Frames and colour schemes -/

open Function in
/-- **Graph Minors XIX, (3.1)**, from (4.1) (Graph Minors XIX, Section 4, page 334): no colour
scheme
is bad. The paper's "we may choose it to satisfy `S₁`" is the induction on the capped surface, by
`GraphMinor.Surface.simplerWellFounded`. -/
theorem theorem_3_1 {S Shat : Type u} [TopologicalSpace S] [TopologicalSpace Shat] {α : Type w}
    (cap : IsCappedSurface S Shat) (χ : ColourScheme S α) : ¬ χ.IsBad :=
  theorem_3_1_proof cap χ

/-! ## Section 4. The induction -/

open GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (4.1)** (page 333): "If $\chi$ satisfies $\mathbf{S}_1$--$\mathbf{S}_4$ then
it is not orientedly bad." -/
theorem theorem_4_1 (S Shat : Type u) [TopologicalSpace S] [TopologicalSpace Shat] (β : Type w)
    [Infinite β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (h1 : ConditionS1.{u, w} Shat) (h2 : ConditionS2 χ cap) (h3 : ConditionS3 χ cap)
    (h4 : ConditionS4 χ) : ¬ χ.IsOrientedlyBad :=
  GM19.theorem_4_1_proof S Shat β cap χ h1 h2 h3 h4

open Function in
/-- **Graph Minors XIX, (4.2)** (page 333): "If $\chi$ is a bad colour scheme, there is an
orientedly bad colour scheme $\chi'$ with $\Sigma_{\chi'} = \Sigma_\chi$."

If `χ` is a bad colour scheme, there is an orientedly bad colour
scheme `χ'` with `Σ_{χ'} = Σ_χ`. Here it has the same frame, and its labels are in `α × Bool`. -/
theorem theorem_4_2 {S : Type u} [TopologicalSpace S] {α : Type w} {χ : ColourScheme S α}
    (h : χ.IsBad) :
    ∃ χ' : ColourScheme S (α × Bool), χ'.Φ = χ.Φ ∧ χ'.IsOrientedlyBad :=
  theorem_4_2_proof h

open GraphMinor.GM19.QuasiOrder Function in
/-- **Graph Minors XIX, (4.3)** (page 333): "There is no countable sequence $\Omega_i$ $(i = 1, 2,
\dots)$ of well-quasi-orders such that $\Omega_{i+1} \prec \Omega_i$ for all $i \ge 1$."

A well-quasi-order starts no infinite chain `Ω₁ ≻ Ω₂ ≻ ⋯`. The
paper omits the proof. Choose `x_i ∈ E(Ω_i) \ E(Ω_{i+1})`. Then `x_i ≤ x_j` for some `i < j`, and as
`E(Ω_{i+1})` is closed downward and contains `x_j`, it contains `x_i`, a contradiction. -/
theorem theorem_4_3 {α : Type w} (Ω : ℕ → QuasiOrder α) (hwqo : (Ω 0).IsWQO)
    (hstrict : ∀ i, (Ω (i + 1)).IsStrictSubIdeal (Ω i)) : False :=
  GM19.QuasiOrder.theorem_4_3_proof Ω hwqo hstrict

open Function in
/-- **Graph Minors XIX, (4.4)** (page 334): "There is no countable sequence $\chi_i$ $(i = 1, 2,
\dots)$ of colour schemes such that $\chi_{i+1}$ is a refinement of $\chi_i$ for all $i \ge 1$."

There is no sequence `χ_i` of colour schemes such that `χ_{i+1}` is a
refinement of `χ_i` for all `i`. -/
theorem theorem_4_4 {α : Type w} (S : ℕ → Type u) [∀ i, TopologicalSpace (S i)]
    (χ : ∀ i, ColourScheme (S i) α) (h : ∀ i, (χ (i + 1)).IsRefinement (χ i)) : False :=
  theorem_4_4_proof S χ h

/-! ## Section 5. Surface homeomorphisms -/

/-- **Graph Minors XIX, (5.1)** (page 335): "Let $(\Gamma_1, \phi_1), (\Gamma_2, \phi_2)$ be
$\chi$-coloured paintings, and let $\alpha_1, \alpha_2$ be $\Phi_\chi$-preserving homeomorphisms of
$\Sigma$. For $i = 1, 2$ let $(\Gamma'_i, \phi'_i)$ be the image of $(\Gamma_i, \phi_i)$ under
$\alpha_i$. Then there is a (linear) inflation of $(\Gamma'_1, \phi'_1)$ in $(\Gamma'_2, \phi'_2)$
if and only if there is one of $(\Gamma_1, \phi_1)$ in $(\Gamma_2, \phi_2)$."

For linear inflations. -/
theorem theorem_5_1 {S : Type} [TopologicalSpace S] [T2Space S] {α₀ : Type w}
    {χ : ColourScheme S α₀} {P₁ P₂ P₁' P₂' : ColouredPainting χ} {α₁ α₂ : S ≃ₜ S} (hS : IsSurface S)
    (h₁ : IsFramePreservingHomeo χ.Φ α₁) (h₂ : IsFramePreservingHomeo χ.Φ α₂)
    (I₁ : IsColouredImage α₁ P₁ P₁') (I₂ : IsColouredImage α₂ P₂ P₂') :
    (∃ σv σe, IsColouredLinearInflation χ P₁' P₂' σv σe) ↔
    ∃ σv σe, IsColouredLinearInflation χ P₁ P₂ σv σe :=
  theorem_5_1_proof hS h₁ h₂ I₁ I₂

open Function Metric GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (5.2)** (page 335): "For every surface $\Sigma$, every frame $\Phi$ in
$\Sigma$ and every integer $n \ge 0$, there are only finitely many equivalence classes of features
in $\Phi$ with size $\le n$." -/
theorem theorem_5_2 (S : Type) [TopologicalSpace S] [T2Space S] (hS : IsSurface S)
    (hconn : ConnectedSpace S) (Φ : Frame S) (n : ℕ) :
    ∃ 𝓕 : Set (Drawing S), 𝓕.Finite ∧ ∀ K : Drawing S, IsFeature Φ K → K.V.ncard + K.E.ncard ≤ n →
    ∃ K₀ ∈ 𝓕, FeatureEquiv Φ K₀ K :=
  GM19.theorem_5_2_proof S hS hconn Φ n

open GraphMinor.GM19.FrameData in
/-- **Graph Minors XIX, (5.3)** (page 336): "With $\Gamma, K$, etc. as above, if each component $K'$
of $K$ satisfies $$ |V(K') \cap V(\Gamma)| + |V(K') \cap bd(\Sigma)| \ge 2 $$ then
$\psi^{-1}(\Gamma) \cap \Sigma_1$ fits the frame $\psi^{-1}(\Phi) \cap \Sigma_1$."

With `K` a feature in `Φ` and `Γ` a painting that fits `Φ`, such that each component
of `K` has a vertex of `Γ` in the sense of `IsAnchored`, the painting `ψ⁻¹(Γ) ∩ Σ₁` fits the frame
`ψ⁻¹(Φ) ∩ Σ₁`.
Any choice of `flip` works here, and `exists_flip` gives the one the paper asks for. -/
theorem theorem_5_3 {S S₁ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁]
    [T2Space S₁] {Φ : Frame S} {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S} (D : FrameData Φ Γ K ψ)
    [Nonempty S₁] [ConnectedSpace S] (hF : IsFeature Φ K) (hA : IsAnchored Γ K)
    (flip : Set S₁ → Bool) :
    (pullPainting D.pull (D.borderMarch flip)
    (fun _ hp ↦ (D.nodup_arcMarch _ D.pull.finite_pullV D.pull.two hp).1)
    (fun _ hp ↦ (D.nodup_arcMarch _ D.pull.finite_pullV D.pull.two hp).2)).Fits
    (pullFrame D flip (D.long_disjoint hF)) :=
  GM19.FrameData.theorem_5_3_proof D hF hA flip

open GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (5.4)** (page 337): "Let $\chi$ satisfy S$_3$, and let $(\Gamma_i, \phi_i)$
$(i = 1, 2, \dots)$ be a similarly oriented bad sequence for $\chi$. Then for all $n \ge 0$, there
exists $h \ge 0$ such that $dist(\Gamma_i) > n$ for all $i \ge h$."

, from (5.2) and the facts about orientations and cappings. -/
theorem theorem_5_4 (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (hS3 : ConditionS3 χ cap) (P : ℕ → ColouredPainting χ) (hbad : IsBadSequence χ P)
    (hsim : IsSimilarlyOriented χ P) (rad : ∀ i, RadialDrawing cap (P i).Γ) (n : ℕ) :
    ∃ h, ∀ i ≥ h, (n : ℕ∞) < Painting.dist (rad i) :=
  GM19.theorem_5_4_proof S Shat β cap χ hS3 P hbad hsim rad n

open GraphMinor.GM11 in
/-- **Graph Minors XIX, (5.5)** (page 338): "Let $\chi$ satisfy S$_1$, S$_3$, and let $(\Gamma_i,
\phi_i)$ $(i = 1, 2, \dots)$ be a similarly oriented bad sequence for $\chi$. Then for all $n \ge 0$
there exists $h \ge 1$ such that $rep(\Gamma_i) > n$ for all $i \ge h$."

, from (5.2), (5.4) and the fact that each fragment is simpler. -/
theorem theorem_5_5 (S Shat : Type u) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (h1 : ConditionS1.{u, w} Shat) (h2 : ConditionS3 χ cap) (P : ℕ → ColouredPainting χ)
    (h3 : IsBadSequence χ P) (h4 : IsSimilarlyOriented χ P) (rad : ∀ i, RadialDrawing cap (P i).Γ)
    (n : ℕ) : ∃ h, ∀ i ≥ h, (n : ℕ∞) < Painting.rep (rad i) :=
  GM19.theorem_5_5_proof S Shat β cap χ h1 h2 P h3 h4 rad n

/-! ## Section 6. Inflations and linear inflations -/

/-- **Graph Minors XIX, (6.1)** (page 339): "Let $\chi$ satisfy* **S**$_1$, **S**$_3$, *and let*
$(\Gamma_i, \phi_i)$ $(i = 1, 2, \dots)$
*be a similarly oriented bad sequence for $\chi$. Then there exists $h \ge 1$ such that for
all $j > i \ge h$ there is no inflation of $(\Gamma_i, \phi_i)$ in $(\Gamma_j, \phi_j)$." -/
theorem theorem_6_1 {S Shat : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {β : Type w} [Infinite β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (hS1 : ConditionS1.{u, w} Shat) (hS3 : ConditionS3 χ cap) (P : ℕ → ColouredPainting χ)
    (hbad : IsBadSequence χ P) (hsim : IsSimilarlyOriented χ P)
    (rad : ∀ i, RadialDrawing cap (P i).Γ) :
    ∃ h, ∀ i ≥ h, ∀ j > i, ¬ ∃ σv σe, IsColouredInflation χ (P i) (P j) σv σe :=
  theorem_6_1_proof cap χ hS1 hS3 P hbad hsim rad

open GraphMinor.GM11 in
/-- **Graph Minors XIX, (6.2)** (page 339): "For any surface $\Sigma$ there is a number $n$ with the
following property. Let $\Phi$ be a frame in $\Sigma$, and let $\Gamma_1, \Gamma_2$ be paintings in
$\Sigma$ fitting $\Phi$, with $rep(\Gamma_1) \ge n$. Let $\sigma$ be an inflation of $\Gamma_1$ in
$\Gamma_2$ respecting $\Phi$. Then there is a linear inflation $\sigma'$ of $\Gamma_1$ in $\Gamma_2$
respecting $\Phi$, such that $\sigma(e) = \sigma'(e)$ for all $e \in E(\Gamma_1)$, and $\sigma(v)
\subseteq \sigma'(v)$ for all $v \in V(\Gamma_1)$."

339, by the proof on pages 342-343. -/
theorem theorem_6_2 (S Shat : Type u) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] (cap : IsCappedSurface S Shat) (h1 : IsSurface S) :
    ∃ n : ℕ, ∀ (Φ : Frame S) (Γ₁ Γ₂ : Painting S) (rad : RadialDrawing cap Γ₁), Γ₁.Fits Φ →
    Γ₂.Fits Φ → (n : ℕ∞) ≤ Painting.rep rad → ∀ σv σe, IsInflation Γ₁ Γ₂ σv σe →
    RespectsFrame Φ Γ₁ σe → ∃ σv', IsLinearInflation Γ₁ Γ₂ σv' σe ∧ ∀ v ∈ Γ₁.V, σv v ⊆ σv' v :=
  GM19.theorem_6_2_proof S Shat cap h1

open GraphMinor.GM11 in
/-- **Graph Minors XIX, (6.3)** (page 340): "Let $G, G'$ be drawings in a surface $\Sigma$ with
$bd(\Sigma) = \emptyset$, such that there is an enlargement of $G$ in $G'$. Then $G$ is isomorphic
to a drawing $H$ in $\Sigma$ with $rep(H) \le rep(G')$."

If there is an enlargement of `G` in `G'`, for drawings in a surface with no boundary, then `G` is
isomorphic to a drawing `H` in the surface with `rep(H) ≤ rep(G')`. -/
theorem theorem_6_3 {S : Type} [TopologicalSpace S] (hT : IsClosedSurface S) (hb : bd S = ∅)
    {G G' : Drawing S} (hG : G.IsGM19Drawing) (hG' : G'.IsGM19Drawing) {σv : S → Drawing S}
    {σe : Set S → Set S} (hσ : IsEnlargement G G' σv σe) :
    ∃ H : Drawing S, H.IsGM19Drawing ∧ G.IsIsomorphic H ∧ H.rep ≤ G'.rep :=
  GM19.theorem_6_3_proof hT hb hG hG' hσ

open Metric GraphMinor.GM07 GraphMinor.GM11 in
/-- **Graph Minors XIX, (6.4)** (page 341): "For every surface $\Sigma$ with $bd(\Sigma) =
\emptyset$, not a sphere, and every drawing $H$ in $\Sigma$, there is a number $k$ such that for
every drawing $G$ in $\Sigma$ with $rep(G)\ge k$ there is an enlargement of $H$ in $G$."

The proof uses VII (9.2), VII (5.1), and the proved existence of `α(G)`. -/
theorem theorem_6_4 (S : Type u) [TopologicalSpace S] (hS : IsSurface S) (hconn : ConnectedSpace S)
    (hbd : bd S = ∅) (hsph : ¬ IsSphere S) (H : Drawing S) (h1 : H.IsGM19Drawing) :
    ∃ k : ℕ, ∀ G : Drawing S, G.IsGM19Drawing → (k : ℕ∞) ≤ G.rep →
    ∃ (σv : S → Drawing S) (σe : Set S → Set S), IsEnlargement H G σv σe :=
  GM19.theorem_6_4_proof S hS hconn hbd hsph H h1

/-- **Graph Minors XIX, (6.5)** (page 341): "For every surface $\Sigma$ with $bd(\Sigma) =
\emptyset$, not a sphere, there is a number $k\ge 0$ such that if $G$ is a drawing in $\Sigma$ with
$rep(G)\ge k$ and $G'$ is a drawing in $\Sigma$ such that there is an enlargement of $G$ in $G'$,
then $rep(G')\ge 1$."

(6.4). -/
theorem theorem_6_5 (S : Type) [TopologicalSpace S] (hS : IsSurface S) (hconn : ConnectedSpace S)
    (hb : bd S = ∅) (hsph : ¬ IsSphere S) :
    ∃ k : ℕ, ∀ G : Drawing S, G.IsGM19Drawing → (k : ℕ∞) ≤ G.rep → ∀ G' : Drawing S,
    G'.IsGM19Drawing → ∀ (σv : S → Drawing S) (σe : Set S → Set S), IsEnlargement G G' σv σe → 1 ≤
    G'.rep :=
  theorem_6_5_proof S hS hconn hb hsph

open GM11 in
/-- **Graph Minors XIX, (6.6)** (page 341): "For every surface $\Sigma$ with $bd(\Sigma) =
\emptyset$ there is a number $k\ge 0$ with the following property. Let $G, G'$ be blocks in $\Sigma$
with $rep(G)>k$, and let $\sigma$ be an enlargement of $G$ in $G'$. Then there is an enlargement
$\sigma'$ of $G$ in $G'$ such that"

Follows from (6.5).

The paper states without proof that deleting a vertex lowers representativeness by at most 1. The
Lean proves it (`GM19.lt_rep_delete`): it puts back the edges at the vertex one at a time, and
reroutes each $O$-arc around a thin lens of each edge. -/
theorem theorem_6_6 (S : Type) [TopologicalSpace S] [T2Space S] (hS : IsSurface S)
    (hconn : ConnectedSpace S) (hb : bd S = ∅) :
    ∃ k : ℕ, ∀ G G' : Drawing S, G.IsGM19Drawing → G'.IsGM19Drawing → G.IsBlock → G'.IsBlock →
    (k : ℕ∞) < G.rep → ∀ (σv : S → Drawing S) (σe : Set S → Set S), IsEnlargement G G' σv σe →
    ∃ σv' : S → Drawing S, IsEnlargement G G' σv' σe ∧ (∀ v ∈ G.V, (σv v).IsSubdrawing (σv' v)) ∧
    (⋃ v ∈ G.V, (σv' v).V) = G'.V ∧ (∀ v ∈ G.V, ∀ e ∈ G'.E, tilde e ⊆ (σv' v).V → e ∈ (σv' v).E) ∧
    ∀ r ∈ G'.regions, ∀ v ∈ G.V,
    ((GM19.Drawing.adj ((σv' v).interSet (closure r))).induce
      ((σv' v).interSet (closure r)).V).Preconnected :=
  GM19.theorem_6_6_proof S hS hconn hb

open GraphMinor.GM11 in
/-- **Graph Minors XIX, (6.7)** (page 342): "If $\Gamma$ is an internally 3-connected painting in a
surface $\Sigma$, then $sk(\Gamma)$ is a block and $rep(sk(\Gamma)) = rep(\Gamma)$."

If `Γ` is an internally 3-connected painting in a surface
`Σ`, then `sk(Γ)` is a block and `rep(sk(Γ)) = rep(Γ)`. -/
theorem theorem_6_7 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {cap : IsCappedSurface S Shat} {Γ : Painting S} {D : Drawing Shat}
    [ConnectedSpace Shat] (rad : RadialDrawing cap Γ) (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) : D.IsBlock ∧ D.rep = Painting.rep rad :=
  GM19.theorem_6_7_proof rad hS hD h3

/-! ## Section 7. Tangles -/

open GraphMinor.GM19.TangleDatum GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (7.1).** "**7.1.** *Let $\Gamma$ be a 2-cell painting with
$E(\Gamma)\ne \emptyset$ in a surface $\Sigma$, and let $\mathscr{T}$ be a tangle in $\Gamma$ with
metric $d$. Let $z\in A(\Gamma)$, and let $\kappa$ be an integer with
$4\le \kappa\le rep(\mathscr{T}) - 6$. Then there is a circuit $C$ of $sk(\Gamma)$, bounding an
open disc $\Lambda\subseteq \hat{\Sigma}$ with $z\subseteq \Lambda$, such that*" the four listed
assertions hold.

The print calls the open disc `Λ` throughout, as the Lean does. The bound `d(x, {v}) ≤ 1` in the paper's proof of the third assertion is not needed, since
`d(z, x) < κ` already puts `x` in `ins(W)` for a walk `W` with `ins(W) ⊆ Z(κ)`. -/
theorem theorem_7_1 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    (D : TangleDatum cap χ) {z : Set Shat} (hz : z ∈ D.P.Γ.atoms cap) {κ : ℕ} (h4 : 4 ≤ κ)
    (hκ : κ + 6 ≤ D.rep) {Sk : Drawing Shat} (hSk : IsSkHat cap D.P.Γ Sk) :
    ∃ (C : Drawing Shat) (Λ : Set Shat), C.IsSubdrawing Sk ∧ C.IsCircuit ∧ IsOpenDisc Λ ∧
    IsClosedDisc (closure Λ) ∧ subBd (closure Λ) = C.U ∧ closure Λ \ C.U = Λ ∧ z ⊆ Λ ∧
    (∀ x ∈ D.P.Γ.atoms cap, (x ∩ closure Λ).Nonempty → D.dist z x ≤ κ + 5) ∧
    (∀ x ∈ D.P.Γ.atoms cap, Disjoint x Λ → κ ≤ D.dist z x) ∧
    (∀ x ∈ D.P.Γ.atoms cap, D.dist z x ≤ κ - 2 → x ⊆ Λ) ∧
    ∀ F : Drawing Shat, F.IsCircuitOf D.rad.G → F.U ⊆ closure Λ →
      F.E.ncard + 2 * (κ + 5) < 2 * D.rep → D.ins F ⊆ closure Λ :=
  GM19.TangleDatum.theorem_7_1_proof D hz h4 hκ hSk

/-! ## Section 8. Tie-Breakers -/

open GraphMinor.GM11 in
/-- **Graph Minors XIX, (8.1).** "**8.1.** *Let $(A, B)$ be a separation of $\Gamma$ of order
$< rep(\Gamma)$, with $E(A), E(B) \ne \emptyset$. Then there is a circuit $F$ of $\Gamma^*$ such
that $(A, B)$ splits every edge of $F$ and there is a disc $\Delta \subseteq \hat{\Sigma}$ bounded
by $U(F)$ such that either $\Gamma \cap \Delta \subseteq A$ or $\Gamma \cap \Delta \subseteq B$.*"

The paper counts valencies in the drawing of split edges. We use `N(Z)` of Graph Minors XI for the
regions `Z` of the colouring of this file, which has the same edges. Epstein's theorem gives the
first disc, from `rep(Γ)`. -/
theorem theorem_8_1 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} (hS : IsSurface S)
    (h3 : Γ.IsInternallyThreeConnected) (rad : RadialDrawing cap Γ) {A B : Hypergraph S (Set S)}
    (hAB : Γ.toHypergraph.IsSeparation A B) [T2Space Shat]
    (hlt : (Hypergraph.separationOrder A B : ℕ∞) < Painting.rep rad) (hA : A.edgeSet.Nonempty)
    (hB : B.edgeSet.Nonempty) :
    ∃ (F : Drawing Shat) (Δ : Set Shat), F.IsCircuitOf rad.G ∧ (∀ e ∈ F.E, rad.Splits A B e) ∧
    IsClosedDisc Δ ∧ discBd Δ = F.U ∧
    (Γ.restrict (cap.emb ⁻¹' Δ) ≤ A ∨ Γ.restrict (cap.emb ⁻¹' Δ) ≤ B) :=
  GM19.theorem_8_1_proof hS h3 rad hAB hlt hA hB

open GraphMinor.GM10 in
/-- **Graph Minors XIX, (8.2).** "If $(A, B), (A', B')$ are separations with the same
$\lambda$-order, then $(A, B) = (A',
B')$ or $(B', A')$." -/
theorem theorem_8_2 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} [T2Space Shat] {rad : RadialDrawing cap Γ}
    (tb : TieBreaker rad) (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    {A B A' B' : Hypergraph S (Set S)} (hAB : Γ.toHypergraph.IsSeparation A B)
    (hAB' : Γ.toHypergraph.IsSeparation A' B') (h : tb.lambdaOrder (A, B) = tb.lambdaOrder (A', B')) :
    (A = A' ∧ B = B') ∨ (A = B' ∧ B = A') :=
  GM19.theorem_8_2_proof tb hS h3 hAB hAB' h

open GraphMinor.GM10 in
/-- **Graph Minors XIX, (8.3).** "If $(A, B), (A', B')$ are separations then so are $(A \cup A', B
\cap B')$, $(A \cap A', B
\cup B')$, and either $(A \cup A', B \cap B')$ has smaller $\lambda$-order than $(A, B)$, or
$(A \cap A', B \cup B')$ has $\lambda$-order at most that of $(A', B')$." -/
theorem theorem_8_3 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} [T2Space Shat] {rad : RadialDrawing cap Γ}
    (tb : TieBreaker rad) (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    {A B A' B' : Hypergraph S (Set S)} (hAB : Γ.toHypergraph.IsSeparation A B)
    (hAB' : Γ.toHypergraph.IsSeparation A' B') :
    Γ.toHypergraph.IsSeparation (A ∪ A') (B ∩ B') ∧
    Γ.toHypergraph.IsSeparation (A ∩ A') (B ∪ B') ∧
    (tb.lambdaOrder (A ∪ A', B ∩ B') < tb.lambdaOrder (A, B) ∨
      tb.lambdaOrder (A ∩ A', B ∪ B') ≤ tb.lambdaOrder (A', B')) :=
  GM19.theorem_8_3_proof tb hS h3 hAB hAB'

open GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (8.4).** "Let $\mathscr{T}, \mathscr{T}'$ be tangles in $\Gamma$ and let
$(A, B)$ be the
$(\mathscr{T}, \mathscr{T}')$-distinction. Suppose that $|V(A \cap B)| < rep(\mathscr{T})$.
Then there is a circuit $F$ in $\Gamma^*$ such that $A = \Gamma \cap ins(F)$, $B = \Gamma
\cap out(F)$." -/
theorem theorem_8_4 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}
    (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected) (tb : TieBreaker rad) {ord ord' : ℕ}
    {𝒯 𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯)
    (h𝒯' : IsTangle Γ.toHypergraph ord' 𝒯') {A B : Hypergraph S (Set S)}
    (hd : IsDistinction tb.lambdaOrder 𝒯 𝒯' A B)
    (hlt : Hypergraph.separationOrder A B < tangleRep rad ord 𝒯) :
    ∃ (F : Drawing Shat) (Δ : Set Shat), IsInsOf rad ord 𝒯 F Δ ∧
    A = Γ.restrict (cap.emb ⁻¹' Δ) ∧ B = Γ.restrict (cap.emb ⁻¹' closure Δᶜ) :=
  GM19.theorem_8_4_proof hS h3 tb h𝒯 h𝒯' hd hlt

open GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (8.5).** "Let $\mathscr{T}$ be a tangle in $\Gamma$, and let $F$ be a
$\mathscr{T}$-enclave around
$\mathscr{T}'$, and let $u, v \in V(F)$ be distinct. Let $F_1, F_2$ be the two paths of $F$
between $u$ and $v$, and let $P$ be a path of $\Gamma^*$ between $u$ and $v$ with no other
vertex or edge in common with $F$. Suppose that $|E(P)| \le |E(F_1)|$, and if equality holds
then $\lambda(P) \le \lambda(F_1)$." -/
theorem theorem_8_5 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}
    [ConnectedSpace Shat] {F : Drawing Shat} {Δ : Set Shat} {F₁ F₂ P : Drawing Shat} {u v : Shat}
    {ord ord' : ℕ} {𝒯 𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} (hS : IsSurface S)
    (h3 : Γ.IsInternallyThreeConnected) (tb : TieBreaker rad) (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯)
    (h𝒯' : IsTangle Γ.toHypergraph ord' 𝒯') (hins : IsInsOf rad ord 𝒯 F Δ)
    (hd : IsDistinction tb.lambdaOrder 𝒯 𝒯' (partIn cap Γ Δ) (partIn cap Γ (closure Δᶜ)))
    (ht : TwoPaths rad.G F F₁ F₂ P u v) (hle : P.E.ncard ≤ F₁.E.ncard)
    (heq : P.E.ncard = F₁.E.ncard → tb.weightSub P ≤ tb.weightSub F₁) :
    ∃ Δ₂ : Set Shat, IsInsOf rad ord 𝒯 (rad.G.sup P F₂) Δ₂ ∧
    (partIn cap Γ Δ₂, partIn cap Γ (closure Δ₂ᶜ)) ∈ 𝒯' ∧
    (¬ P.U ⊆ Δ → Δ₂ ∩ Δ = F₂.U) ∧
    F₂.E.ncard ≤ P.E.ncard ∧ (P.E.ncard = F₂.E.ncard → tb.weightSub F₂ < tb.weightSub P) :=
  GM19.theorem_8_5_proof hS h3 tb h𝒯 h𝒯' hins hd ht hle heq

open GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (8.6).** "Let $\mathscr{T}$ be a tangle in $\Gamma$, and let $F_1, F_2$ be
$\mathscr{T}$-enclaves.
Then either $ins(F_1) \subseteq ins(F_2)$, or $ins(F_2) \subseteq ins(F_1)$, or $ins(F_1)
\cap ins(F_2) = U(F_1) \cap U(F_2)$." -/
theorem theorem_8_6 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] [ConnectedSpace Shat] {cap : IsCappedSurface S Shat} {Γ : Painting S}
    {rad : RadialDrawing cap Γ} {ord : ℕ} {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {F₁ F₂ : Drawing Shat} {Δ₁ Δ₂ : Set Shat} (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    (tb : TieBreaker rad) (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯) {ord₁ ord₂ : ℕ}
    {𝒯₁ 𝒯₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯₁ : IsTangle Γ.toHypergraph ord₁ 𝒯₁) (h𝒯₂ : IsTangle Γ.toHypergraph ord₂ 𝒯₂)
    (hins₁ : IsInsOf rad ord 𝒯 F₁ Δ₁) (hins₂ : IsInsOf rad ord 𝒯 F₂ Δ₂)
    (hd₁ : IsDistinction tb.lambdaOrder 𝒯 𝒯₁ (partIn cap Γ Δ₁) (partIn cap Γ (closure Δ₁ᶜ)))
    (hd₂ : IsDistinction tb.lambdaOrder 𝒯 𝒯₂ (partIn cap Γ Δ₂) (partIn cap Γ (closure Δ₂ᶜ))) :
    Δ₁ ⊆ Δ₂ ∨ Δ₂ ⊆ Δ₁ ∨ Δ₁ ∩ Δ₂ = F₁.U ∩ F₂.U :=
  GM19.theorem_8_6_proof hS h3 tb h𝒯 h𝒯₁ h𝒯₂ hins₁ hins₂ hd₁ hd₂

open GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (8.7).** "**8.7.** *Let $\mathscr{T}$ be a tangle in $\Gamma$, let $F$ be a
circuit of $\Gamma^*$ with $\frac{1}{2} |E(F)| < \min(ord(\mathscr{T}), rep(\Gamma))$, and let
$\Sigma_1, \Sigma_2$ be the closures of the two components of $\hat{\Sigma} \setminus U(F)$, where
$(\Gamma \cap \Sigma_1, \Gamma \cap \Sigma_2) \in \mathscr{T}$. Then there is a $\lambda$-linked
circuit $F'$ in $\Gamma^*$ such that*
• *$|E(F')| \le |E(F)|$ and if equality holds then $\lambda(F') \le \lambda(F)$,*
• *$\Sigma_1 \subseteq \Sigma'_1$ and $\Sigma'_2 \subseteq \Sigma_2$, where $\Sigma'_1, \Sigma'_2$
  are the closures of the two components of $\hat{\Sigma} \setminus U(F')$ and
  $(\Gamma \cap \Sigma'_1, \Gamma \cap \Sigma'_2) \in \mathscr{T}$.*" -/
theorem theorem_8_7 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] [ConnectedSpace Shat] {cap : IsCappedSurface S Shat} {Γ : Painting S}
    {rad : RadialDrawing cap Γ} {ord : ℕ} {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {F : Drawing Shat} (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected) (tb : TieBreaker rad)
    (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯) (hF : F.IsCircuitOf rad.G)
    (hlt : (F.E.ncard : ℕ∞) < 2 * min (ord : ℕ∞) (Painting.rep rad)) {S₁ S₂ : Set Shat}
    (hs : IsSidesOf F S₁ S₂) (hm : (partIn cap Γ S₁, partIn cap Γ S₂) ∈ 𝒯) :
    ∃ (F' : Drawing Shat) (S₁' S₂' : Set Shat), IsLambdaLinkedCircuit tb ord 𝒯 F' ∧
    IsSidesOf F' S₁' S₂' ∧
    GM18.IsLambdaLinkedTo tb.lambdaOrder 𝒯 (partIn cap Γ S₁') (partIn cap Γ S₂') ∧
    F'.E.ncard ≤ F.E.ncard ∧ (F'.E.ncard = F.E.ncard → tb.weightSub F' ≤ tb.weightSub F) ∧
    S₁ ⊆ S₁' ∧ S₂' ⊆ S₂ :=
  GM19.theorem_8_7_proof hS h3 tb h𝒯 hF hlt hs hm

open GraphMinor.GM10 in
/-- **Graph Minors XIX, (8.8).** "If $\mathscr{T}$ is a tangle in $\Gamma$, and $\mathscr{L}$ is a
rooted location with
$\mathscr{L}^- \subseteq \mathscr{T}$, and $ord(\mathscr{L}) < \theta \le ord(\mathscr{T})$,
and $\mathscr{L}$ is $\lambda$-linked to $\mathscr{T}$, then $\mathscr{L}$ $\theta$-isolates
$\mathscr{T}$."
The paper applies (7.1) of Graph Minors XVIII to `ℒ⁻`. We apply it to each `(A⁻, Aᶜ)` alone, since
two arms with the same `A⁻` and different `π̄(A)` do not form a location of Graph Minors X. -/
theorem theorem_8_8 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    {cap : IsCappedSurface S Shat} {Γ : Painting S} [T2Space Shat] {rad : RadialDrawing cap Γ}
    (tb : TieBreaker rad) (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected) {ord θ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} (h𝒯 : IsTangle Γ.toHypergraph ord 𝒯)
    {L : RootedLocation Γ} (hlink : L.IsLambdaLinked tb 𝒯) (hlt : L.ord < θ) (hle : θ ≤ ord) :
    L.Isolates tb θ ord 𝒯 :=
  GM19.theorem_8_8_proof tb hS h3 h𝒯 hlink hlt hle

/-! ## Section 9. An application of patchworks -/

open Function in
/-- **Graph Minors XIX, (9.1).** "Let $(\Gamma, \phi), (\Gamma', \phi')$ be $\chi$-coloured
paintings, where $\chi$ is
disjoint. Let $\sigma$ be an inflation of $\Gamma$ in $\Gamma'$, such that $\phi(e) \le
\phi'(\sigma(e))$ (in $\Omega_{\chi}$) for every $e \in E(\Gamma)$. Then $\sigma$ is an
inflation of $(\Gamma, \phi)$ in $(\Gamma', \phi')$." -/
theorem theorem_9_1 {S : Type u} [TopologicalSpace S] {α : Type w} {χ : ColourScheme S α}
    (hd : χ.IsDisjoint) (P P' : ColouredPainting χ) {σv : S → Set S} {σe : Set S → Set S}
    (hσ : IsInflation P.Γ P'.Γ σv σe) (hle : ∀ e ∈ P.Γ.E, (χ.unionWQO hd).le (P.φ e) (P'.φ (σe e))) :
    IsColouredInflation χ P P' σv σe :=
  theorem_9_1_proof hd P P' hσ hle

open GraphMinor.GM04 (Patchwork freePatch IsGrouping IsComponent) in
open Function in
/-- **Graph Minors XIX, (9.2).** "Let $\chi$ be a disjoint colour scheme, let $(\Gamma_i, \phi_i)$
($i = 1, 2, \ldots$) be a
countable sequence of $\chi$-coloured paintings and for each $i \ge 1$ let $\lambda_i$ be a
tie-breaker in $\Gamma_i$. Let $\theta \ge 1$, and for each $i \ge 1$ and every tangle
$\mathscr{T}$ in $\Gamma_i$ of order $\ge \theta$, let $\mathscr{L}(\mathscr{T})$ be a
rooted location in $\Gamma_i$ which $\theta$-isolates $\mathscr{T}$. Let the set of all
these $(\Gamma_i, \phi_i, \mathscr{L}(\mathscr{T}))$ (over all $i$ and $\mathscr{T}$) be
well-behaved. Then there exist $j > i \ge 1$ such that there is an inflation of $(\Gamma_i,
\phi_i)$ in $(\Gamma_j, \phi_j)$." -/
theorem theorem_9_2 {S Shat : Type} {α : Type w} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace Shat] [T2Space Shat] {χ : ColourScheme S α} {cap : IsCappedSurface S Shat}
    (hd : χ.IsDisjoint) (seq : ℕ → ColouredPainting χ) (rad : ∀ i, RadialDrawing cap (seq i).Γ)
    (tb : ∀ i, TieBreaker (rad i)) {θ : ℕ} (hθ : 1 ≤ θ) {Pl : Set (Place χ)}
    (hPl : IsWellBehavedPlaces Pl)
    (hloc : ∀ i ord (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
      GM10.IsTangle (seq i).Γ.toHypergraph ord 𝒯 → θ ≤ ord → ∃ L : RootedLocation (seq i).Γ,
      (⟨hd, seq i, L⟩ : Place χ) ∈ Pl ∧ L.Isolates (tb i) θ ord 𝒯) :
    ∃ i j, i < j ∧ ∃ σv σe, IsColouredInflation χ (seq i) (seq j) σv σe :=
  GM19.theorem_9_2_proof hd seq rad tb hθ hPl hloc

open Function in
/-- **Graph Minors XIX, (9.3).** "**9.3.** *Let $\chi$ be a disjoint colour scheme, and let
$\mathscr{P}$ be a set of $\chi$-places. For each $(\Gamma, \phi, \mathscr{L}) \in \mathscr{P}$ let
$\pi(\mathscr{L})$ be a march with
$\bar{\pi}(\mathscr{L}) = \bigcup (\bar{\pi}(A) : A \in \mathscr{L})$. Suppose that*
• *there exist $m, n$ such that $|\mathscr{L}| \le m$ and $|\bar{\pi}(\mathscr{L})| \le n$ for all
  $(\Gamma, \phi, \mathscr{L}) \in \mathscr{P}$,* ...
• *for every countable sequence $(\Gamma_i, \phi_i, \mathscr{L}_i)$ $(i = 1, 2, \dots)$ of members
  of $\mathscr{P}$ there exist $j > i \ge 1$ and an inflation $\sigma$ of $M(\Gamma_i,
  \mathscr{L}_i)$
  in $\Gamma_j$, such that*
  ◦ *for each $v \in V(M(\Gamma_i, \mathscr{L}_i)), V(\sigma(v)) \subseteq V(M(\Gamma_j,
  \mathscr{L}_j))$,*
  ◦ *for each $e \in E(M(\Gamma_i, \mathscr{L}_i)), \sigma(e) \in E(M(\Gamma_j, \mathscr{L}_j))$ and
    $\phi_i(e) \le \phi_j(\sigma(e))$,*
  ◦ $|\bar{\pi}(\mathscr{L}_i)| = |\bar{\pi}(\mathscr{L}_j)|$, *and for*
    $1 \le h \le |\bar{\pi}(\mathscr{L}_i)|$ *if* $v$ *is the* $h$th *term of* $\pi(\mathscr{L}_i)$
    *then* $\sigma(v)$ *contains the* $h$th *term of* $\pi(\mathscr{L}_j)$.
*Then $\mathscr{P}$ is well-behaved.*" -/
theorem theorem_9_3 {S : Type u} [TopologicalSpace S] {α : Type w} {χ : ColourScheme S α}
    {Pl : Set (Place χ)} (πL : Place χ → List S)
    (hsub : ∀ X ∈ Pl, ∀ A ∈ X.L.arms, ∀ v ∈ A.π, v ∈ πL X) {m n : ℕ}
    (hm : ∀ X ∈ Pl, X.L.arms.ncard ≤ m) (hn : ∀ X ∈ Pl, (πL X).length ≤ n)
    (hseq : ∀ seq : ℕ → Place χ, (∀ i, seq i ∈ Pl) → ∃ i j, i < j ∧ ∃ σv σe,
      IsSubInflationIn (seq i).P.Γ (seq i).L.M (seq j).P.Γ σv σe ∧
      (∀ v ∈ (seq i).L.M.vertexSet, σv v ⊆ (seq j).L.M.vertexSet) ∧
      (∀ e ∈ (seq i).L.M.edgeSet, σe e ∈ (seq j).L.M.edgeSet ∧
        χ.unionLE ((seq i).P.φ e) ((seq j).P.φ (σe e))) ∧ (πL (seq i)).length =
      (πL (seq j)).length ∧ ∀ (h : ℕ) (h₁ : h < (πL (seq i)).length) (h₂ : h < (πL (seq j)).length),
      (πL (seq j))[h] ∈ σv (πL (seq i))[h]) :
    IsWellBehavedPlaces Pl :=
  theorem_9_3_proof πL hsub hm hn hseq

open Function in
/-- **Graph Minors XIX, (9.4).** "Let $\chi$ be a disjoint colour scheme, and let $\mathscr{C}$ be a
well-behaved set of
$\chi$-places. Let $\mathscr{C}'$ be the set of all images of members of $\mathscr{C}$ under
$\Phi_\chi$-preserving homeomorphisms of $\Sigma_\chi$. Then $\mathscr{C}'$ is well-behaved." -/
theorem theorem_9_4 {S : Type} [TopologicalSpace S] [T2Space S] {α : Type w} {χ : ColourScheme S α}
    {C : Set (Place χ)} (h : IsWellBehavedPlaces C) :
    IsWellBehavedPlaces {Y | ∃ X ∈ C, ∃ f, IsPlaceHomeoImage X Y f} :=
  theorem_9_4_proof h

/-! ## Section 10. Tangle flaws -/

open GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (10.1)** (page 353): "With $\Gamma, \phi, \lambda, \mathscr{T}, F, \Sigma_1,
\Sigma_2$ as above,* • *$\Sigma_2$ is
a disc,* • *either $|U(F) \cap bd(\Sigma_\chi)| \le 1$ and $U(F) \subseteq \Sigma_\chi$, or
$|U(F) \cap bd(\Sigma_\chi)| = 2$ and $U(F) \not\subseteq \Sigma_\chi$, or $dist(\Gamma) \le
\frac{1}{4}|E(F)| + 1$,* • *$F$ is $\lambda$-linked to $\mathscr{T}$." -/
theorem theorem_10_1 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {cap : IsCappedSurface S Shat} {α : Type w} {χ : ColourScheme S α}
    {D : TangleDatum cap χ} {F : Drawing Shat} (hS : IsSurface S)
    (h3' : D.P.Γ.IsInternallyThreeConnected) (hFl : D.IsRepFlaw F) {S₁ S₂ : Set Shat}
    (hs : IsSidesOf F S₁ S₂) (hnd : ¬ IsClosedDisc S₁)
    (hm : (partIn cap D.P.Γ S₁, partIn cap D.P.Γ S₂) ∈ D.𝒯) :
    IsClosedDisc S₂ ∧
    (((F.U ∩ cap.emb '' bd S).ncard ≤ 1 ∧ F.U ⊆ range cap.emb) ∨
      ((F.U ∩ cap.emb '' bd S).ncard = 2 ∧ ¬ F.U ⊆ range cap.emb) ∨
      Painting.dist D.rad * 4 ≤ ((F.E.ncard + 4 : ℕ) : ℕ∞)) ∧
    IsLambdaLinkedCircuit D.tb D.ord D.𝒯 F :=
  GM19.theorem_10_1_proof hS h3' hFl hs hnd hm

open GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (10.2)** (page 354):
"**10.2.** *Let $\chi$ satisfy $\mathbf{S}_1$, let $F$ be a circuit in $\hat{\Sigma}_\chi$, with
vertex set $\{v_1, \dots, v_{2n}\}$, numbered in order in $F$, and let $\pi$ be the march
$v_2, v_4, \dots, v_{2n}$. Then there is a well-behaved set $\mathscr{C}(F, \pi)$ of $\chi$-places
with the following property. Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ satisfy*
• *$F \subseteq \Gamma^*$, and $U(F) \cap V(\Gamma) = \bar{\pi}$,*
• *$F$ is a representativeness flaw for $(\Gamma, \phi, \lambda, \mathscr{T})$, and*
• *$dist(\Gamma) > \frac{1}{4}|(E(F)| + 1$.*

*Then there is a rooted location $\mathscr{L}$ with $ord(\mathscr{L}^-) = \frac{1}{2}|E(F)|$, which
$(\frac{1}{2}|E(F)| + 1)$-isolates $\mathscr{T}$ and for which
$(\Gamma, \phi, \mathscr{L}) \in \mathscr{C}(F, \pi)$.*" -/
theorem theorem_10_2 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {β : Type w} [Nonempty β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (hd : χ.IsDisjoint) (𝒮 : Set (ColouredPainting χ)) (hS1 : ConditionS1.{0, w} Shat)
    (F : Drawing Shat) (hFc : F.IsCircuit) (π : List S) (hπ : π.Nodup) :
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧
    ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
      F.IsSubdrawing D.rad.G →
      F.U ∩ cap.emb '' D.P.Γ.V = cap.emb '' {v | v ∈ π} →
      D.IsRepFlaw F →
      ((F.E.ncard + 4 : ℕ) : ℕ∞) < Painting.dist D.rad * 4 →
      ∃ L : RootedLocation D.P.Γ,
        L.ord = F.E.ncard / 2 ∧
        L.Isolates D.tb (F.E.ncard / 2 + 1) D.ord D.𝒯 ∧
        (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞 :=
  GM19.theorem_10_2_proof cap χ hd 𝒮 hS1 F hFc π hπ

open GraphMinor.GM11 GraphMinor.GM10 in
/-- **Graph Minors XIX, (10.3)** (page 355): "Let $\chi$ satisfy $\mathbf{S}_1$, and let $n \ge 1$
be an integer. Then there is a well-behaved set $\mathscr{C}_1(n)$ of $\chi$-places with the
following property. Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ satisfy $rep(\Gamma),
ord(\mathscr{T}) \ge n > rep(\mathscr{T})$, and $dist(\Gamma) \ge \frac{1}{2}n + 1$. Then there is a
rooted location $\mathscr{L}$ which $n$-isolates $\mathscr{T}$ and for which $(\Gamma, \phi,
\mathscr{L}) \in \mathscr{C}_1(n)$."

, from (5.2) and the topological step of (10.2). -/
theorem theorem_10_3 (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (hd : χ.IsDisjoint) (𝒮 : Set (ColouredPainting χ)) (h1 : IsPaintingClass χ 𝒮)
    (hS1 : ConditionS1.{0, w} Shat) (n : ℕ) (h2 : 1 ≤ n) :
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 → (n : ℕ∞) ≤
    Painting.rep D.rad → n ≤ D.ord → D.rep < n → ((n + 2 : ℕ) : ℕ∞) ≤ 2 * Painting.dist D.rad →
    ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb n D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞 :=
  GM19.theorem_10_3_proof S Shat β cap χ hd 𝒮 h1 hS1 n h2

open GraphMinor.GM11 GraphMinor.GM10 in
/-- **Graph Minors XIX, (10.4)** (page 356): "Let $\chi$ satisfy $\mathbf{S}_3$, and let $n \ge 1$
be an integer. Then there is a well-behaved set $\mathscr{C}_2(n)$ of $\chi$-places with the
following property. Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ be $n$-flawed in
distance. Then there is a rooted location $\mathscr{L}$ which $(n + 1)$-isolates $\mathscr{T}$ and
for which $(\Gamma, \phi, \mathscr{L}) \in \mathscr{C}_2(n)$."

, from (5.2), the orientation of a fragment and the fragment outside a distance flaw. -/
theorem theorem_10_4 (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (hd : χ.IsDisjoint) (𝒮 : Set (ColouredPainting χ)) (hcl : IsPaintingClass χ 𝒮)
    (hS3 : ConditionS3 χ cap) (n : ℕ) (hn : 1 ≤ n) :
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
    D.IsFlawedInDistance n → ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (n + 1) D.ord D.𝒯 ∧
    (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞 :=
  GM19.theorem_10_4_proof S Shat β cap χ hd 𝒮 hcl hS3 n hn

open GraphMinor.GM11 GraphMinor.GM10 in
/-- **Graph Minors XIX, (10.5)** (page 357): "Let $\chi$ satisfy $\mathbf{S}_4$, and let $n \ge 0$
be an integer. Then there is a well-behaved set $\mathscr{C}_3(n)$ of $\chi$-places with the
following property. Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ be $n$-flawed in
freedom. Then there is a rooted location $\mathscr{L}$ which $(n + 1)$-isolates $\mathscr{T}$ and
for which $(\Gamma, \phi, \mathscr{L}) \in \mathscr{C}_3(n)$."

, from (5.2) and the orientation of a fragment.

The print fails without condition (S3), so the Lean assumes `ConditionS3 χ cap`, and a distance flaw
is defined as the paper means. See the correction to (10.5) and the correction on page 356 in
`corrections/GM19.md`. -/
theorem theorem_10_5 (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (hd : χ.IsDisjoint) (𝒮 : Set (ColouredPainting χ)) (hcl : IsPaintingClass χ 𝒮)
    (hS3 : ConditionS3 χ cap) (hS4 : ConditionS4 χ) (n : ℕ) :
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
    D.IsFlawedInFreedom n → ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (n + 1) D.ord D.𝒯 ∧
    (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞 :=
  GM19.theorem_10_5_proof S Shat β cap χ hd 𝒮 hcl hS3 hS4 n

/-! ## Section 11. Border label flaws -/

open GraphMinor.GM11 GraphMinor.GM10 in
/-- **Graph Minors XIX, (11.1)** (page 358):
"**11.1.** *Let $\chi$ satisfy $S_4$, let $S$ be a long side of $\Phi_\chi$, let
$\omega_1, \dots, \omega_m \in E(\Omega_\chi(S))$ with $m \ge 1$, and let $n \ge 4$. Then there is
a well-behaved set $\mathscr{C}_4(S, (\omega_1, \dots, \omega_m), n)$ of $\chi$-places with the
following property. Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ be
$(n, (\omega_1, \dots, \omega_m))$-flawed on $S$. Then there is a rooted location $\mathscr{L}$
which $(m + 1)n$-isolates $\mathscr{T}$, and for which
$(\Gamma, \phi, \mathscr{L}) \in \mathscr{C}_4(S, (\omega_1, \dots, \omega_m), n)$.*"

Flawed on a side uses strict inequalities, which the proof of (11.2) needs. See the correction on
pages 357 and 362 in `corrections/GM19.md`. -/
theorem theorem_11_1 :
    ∀ (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat)
    (χ : ColourScheme S β) (hd : χ.IsDisjoint)
    (𝒮 : Set (ColouredPainting χ)), IsPaintingClass χ 𝒮 → ConditionS4 χ →
    ∀ side ∈ χ.Φ.longSides, ∀ ω : List β, ω ≠ [] → (∀ x ∈ ω, x ∈ (χ.ΩS side).E) → ∀ n : ℕ, 4 ≤ n →
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
      D.IsFlawedOnSide side n ω →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb ((ω.length + 1) * n) D.ord D.𝒯 ∧
        (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞 :=
  GM19.theorem_11_1_proof

open GraphMinor.GM19.TangleDatum GraphMinor.GM11 GraphMinor.GM10 in
/-- **Graph Minors XIX, (11.2)** (page 358): "If $(\Gamma, \phi, \lambda, \mathscr{T}) \in
\mathscr{D}$ is $(n, (\omega_1, \dots,
\omega_m))$-flawed on $S$, then there is a feast of order $\le (m + 1)n$." We also say which pole,
and that
each bite has `½|E(F)| ≤ n`. -/
theorem theorem_11_2 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}
    {D : TangleDatum cap χ} (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
    {side : Set S} (hside : side ∈ χ.Φ.longSides) {n : ℕ} (hn : 4 ≤ n) {ω : List β} (hω : ω ≠ [])
    (hfl : D.IsFlawedOnSide side n ω) :
    ∃ (r : Shat) (Θ : Set S), Θ ∈ cuffs S ∧ side ⊆ Θ ∧ r ∈ D.rad.poles ∧ D.rad.regionOf r = cap.cuffDisc Θ ∧ ∃ ℱ, D.IsFeast r side ω ℱ ∧ feastOrder ℱ ≤ (ω.length + 1) * n ∧
    ∀ F ∈ ℱ, F.E.ncard ≤ 2 * n :=
  GM19.TangleDatum.theorem_11_2_proof hS h3 hside hn hω hfl

open GraphMinor.GM19.TangleDatum GraphMinor.GM11 GraphMinor.GM10 in
/-- **Graph Minors XIX, (11.3)** (page 360): "Every feast of minimum order with order $\le (m + 1)n$
is disjoint." -/
theorem theorem_11_3 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}
    {D : TangleDatum cap χ} (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
    {side : Set S} (hside : side ∈ χ.Φ.longSides) {n : ℕ} (hn : 4 ≤ n) {ω : List β} (hω : ω ≠ [])
    (hfl : D.IsFlawedOnSide side n ω) {Θ : Set S} {r : Shat} (hsΘ : side ⊆ Θ) (hΘ : Θ ∈ cuffs S)
    (hr : r ∈ D.rad.poles) (hreg : D.rad.regionOf r = cap.cuffDisc Θ) {ℱ : Set (Drawing Shat)}
    (hfe : D.IsFeast r side ω ℱ) (hord : feastOrder ℱ ≤ (ω.length + 1) * n)
    (hmin : ∀ ℱ', D.IsFeast r side ω ℱ' → feastOrder ℱ ≤ feastOrder ℱ') :
    D.IsDisjointFeast r side ω ℱ :=
  GM19.TangleDatum.theorem_11_3_proof hS h3 hside hn hω hfl hsΘ hΘ hr hreg hfe hord hmin

open GraphMinor.GM19.TangleDatum GraphMinor.GM11 GraphMinor.GM10 in
/-- **Graph Minors XIX, (11.4)** (page 361): "Let $\mathcal{F}$ be a feast of minimum order $\le
(m+1)n$ and subject to that with
$\Sigma(\lambda(F) : F \in \mathcal{F})$ minimum. Then each $F \in \mathcal{F}$ is
$\lambda$-linked to $\mathcal{T}$." -/
theorem theorem_11_4 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}
    {D : TangleDatum cap χ} (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
    {side : Set S} (hside : side ∈ χ.Φ.longSides) {n : ℕ} (hn : 4 ≤ n) {ω : List β} (hω : ω ≠ [])
    (hfl : D.IsFlawedOnSide side n ω) {Θ : Set S} {r : Shat} (hsΘ : side ⊆ Θ) (hΘ : Θ ∈ cuffs S)
    (hr : r ∈ D.rad.poles) (hreg : D.rad.regionOf r = cap.cuffDisc Θ) {ℱ : Set (Drawing Shat)}
    (hfe : D.IsFeast r side ω ℱ) (hord : feastOrder ℱ ≤ (ω.length + 1) * n)
    (hmin : ∀ ℱ', D.IsFeast r side ω ℱ' → feastOrder ℱ ≤ feastOrder ℱ')
    (hw : ∀ ℱ', D.IsFeast r side ω ℱ' → feastOrder ℱ' = feastOrder ℱ → D.feastWeight ℱ ≤
      D.feastWeight ℱ') {F : Drawing Shat} (hF : F ∈ ℱ) :
    IsLambdaLinkedCircuit D.tb D.ord D.𝒯 F :=
  GM19.TangleDatum.theorem_11_4_proof hS h3 hside hn hω hfl hsΘ hΘ hr hreg hfe hord hmin hw hF

/-! ## Section 12. Internal label flaws -/

open GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (12.1)** (page 362):
"**12.1.** *Let $\rho \ge 2$, even, let $rep(\mathcal{T}) \ge 5\rho + 12$, and let $H$ be a
subdrawing of $\Gamma^*$, satisfying the third condition in the definition of a wheel above. Then
there is a wheel $W$ such that $H$ is a $W$-hub of radius $\rho$.*"

Formalized with the corrected hypotheses: $\rho \ge 3$,
$\operatorname{rep}(\mathscr{T}) \ge 5\rho + 14$, and 3-vertex edges of $\Gamma$ disjoint from
$\operatorname{bd}(\Sigma_\chi)$ (for the version with an additional closed zone set $Y$ near cuffs
used in (12.4), see `TangleDatum.exists_wheel` in `Section12e.lean`).

The print fails for small `ρ`, so the Lean proves it for `ρ = k + 3` with a larger
representativeness. See the correction to (12.1) in `corrections/GM19.md`. -/
theorem theorem_12_1 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    (D : TangleDatum cap χ) {H : Drawing Shat} {ρ : ℕ} (hρ : 3 ≤ ρ) (hrep : 5 * ρ + 14 ≤ D.rep)
    (hH : H.IsSubdrawing D.rad.G)
    (hhub : (H.V.ncard = 1 ∧ H.E = ∅ ∧ ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' →
        H'.E.ncard ≤ 4 * ρ + 4 → ¬ (H.V ⊆ D.ins H' \ H'.U)) ∨
      (IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * ρ + 4 ∧ ∀ H' : Drawing Shat,
        IsEnclave D.tb D.ord D.𝒯 H' → H' ≠ H → H'.E.ncard ≤ 4 * ρ + 4 → ¬ (H.U ⊆ D.ins H')))
    (hcuff : ∀ e ∈ D.P.Γ.E, (tilde e).ncard = 3 → Disjoint (closure e) (bd S)) :
    ∃ W : Set Shat, D.IsWheel W ∧ D.IsWheelHubOfRadius W H ρ :=
  GM19.theorem_12_1_proof D hρ hrep hH hhub hcuff

open GraphMinor.GM19.TangleDatum GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (12.2)** (page 364): "There exists $X_1 \subseteq V(\Gamma^*)$ with $|X_1|
\le m + c(\Sigma_\chi)$ and $P^*
\subseteq X_1$, such that for every $e \in Z$ there exists $x \in X_1$ with $d(e, x) \le n$." -/
theorem theorem_12_2 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    (D : TangleDatum cap χ) {m n k : ℕ} {ω₀ : α} (hn : 4 ≤ n) (hrep : n < D.rep)
    (hno : D.NoInternalMatch m n k ω₀) :
    ∃ X₁ ⊆ D.rad.G.V, X₁.ncard ≤ m + numCuffs S ∧ D.rad.poles ⊆ X₁ ∧
    ∀ e ∈ D.largeEdges k ω₀, ∃ x ∈ X₁, D.edgeVertDist e x ≤ n :=
  GM19.TangleDatum.theorem_12_2_proof D hn hrep hno

open GraphMinor.GM19.TangleDatum GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (12.3)** (page 364): "There exists $X_2 \subseteq V(\Gamma^*)$ with $|X_2|
\le m + c(\Sigma_\chi)$ and $P^*
\subseteq X_2$ and an integer $t$ with $n \le t \le 5^{2m}n$, such that" `d(x₁, x₂) > 24t` for all
distinct
`x₁, x₂ ∈ X₂`, and for every `e ∈ Z` there exists `x ∈ X₂` with `d(e, x) ≤ t`. -/
theorem theorem_12_3 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    (D : TangleDatum cap χ) {m n k : ℕ} {ω₀ : α} (hn : 4 ≤ n) (hfl : D.IsFlawedInternally m n k ω₀) :
    ∃ X₂ ⊆ D.rad.G.V, X₂.ncard ≤ m + numCuffs S ∧ D.rad.poles ⊆ X₂ ∧ ∃ t, n ≤ t ∧
    t ≤ 5 ^ (2 * m) * n ∧ (∀ x₁ ∈ X₂, ∀ x₂ ∈ X₂, x₁ ≠ x₂ → 24 * t < D.vDist x₁ x₂) ∧
    ∀ e ∈ D.largeEdges k ω₀, ∃ x ∈ X₂, D.edgeVertDist e x ≤ t :=
  GM19.TangleDatum.theorem_12_3_proof D hn hfl

open GraphMinor.GM19.TangleDatum GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (12.4)** (page 364): "There is a cover $\mathcal{W}$ with $|\mathcal{W}| \le
m + c(\Sigma_\chi)$, each member of
which has radius $\le 2n \cdot 5^{2m}$." Uses the proved VII (11.10) through (7.1). -/
theorem theorem_12_4 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    (D : TangleDatum cap χ) (hd : χ.IsDisjoint) {m n k : ℕ} {ω₀ : α}
    (hk : (k = 2 ∧ ω₀ ∈ χ.Ω2.E) ∨ (k = 3 ∧ ω₀ ∈ χ.Ω3.E)) (hn : 4 ≤ n)
    (hfl : D.IsFlawedInternally m n k ω₀) :
    ∃ 𝒲, D.IsWheelCover ω₀ 𝒲 ∧ 𝒲.ncard ≤ m + numCuffs S ∧ ∀ W ∈ 𝒲, D.wheelRadius W ≤ 2 * n * 5 ^ (2 * m) :=
  GM19.TangleDatum.theorem_12_4_proof D hd hk hn hfl

/-! ## Section 13. The spokes of a wheel -/

open GraphMinor.GM19.TangleDatum GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (13.1)** (page 366): "There is no path in $\Gamma^*$ from $R^* \cap bd(W)$
to $V(H)$ with $\le \rho - 1$ edges."
The paper's "fourth condition" is the condition that `W` contains the vertices of `Γ` near `H`. -/
theorem theorem_13_1 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ}
    (h : D.IsWheelHubOfRadius W H ρ) (hbd : discBd W ⊆ cap.emb '' (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) {r : Shat} (hr : r ∈ D.rad.Rstar)
    (hrb : r ∈ discBd W) :
    ¬ ∃ P : Drawing Shat, ∃ z ∈ H.V, P.IsPathOf D.rad.G r z ∧ P.E.ncard + 1 ≤ ρ :=
  GM19.TangleDatum.theorem_13_1_proof h hbd hin hr hrb

open GraphMinor.GM19.TangleDatum GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (13.2)** (page 366): "**13.2.** *Let $v_1, v_2 \in V(\Gamma) \cap
bd(\Sigma)$.
If $S_{v_1}$ meets $S_{v_2}$ then they have the same inner end, and $S_{v_1} \cap S_{v_2}$ is a
path.*" The paper prints `bd(Σ)` for `bd(W)`. The path `Q` also ends at the inner end. -/
theorem theorem_13_2 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {v₁ v₂ h₁ h₂ : Shat}
    {S₁ S₂ : Drawing Shat} (hS₁ : D.IsSpoke W H v₁ h₁ S₁) (hS₂ : D.IsSpoke W H v₂ h₂ S₂)
    (hm : (S₁.V ∩ S₂.V).Nonempty) :
    h₁ = h₂ ∧ ∃ u, ∃ Q : Drawing Shat, Q.IsPathOf D.rad.G u h₁ ∧
    S₁.V ∩ S₂.V = Q.V ∧ S₁.E ∩ S₂.E = Q.E :=
  GM19.TangleDatum.theorem_13_2_proof hS₁ hS₂ hm

open GraphMinor.GM19.TangleDatum GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (13.3)** (page 367): "Let $S_v$ be a spoke with inner end $h$, and let $F$
be a $\mathscr{T}$-enclave. If $U(S_v)
\cap ins(F) \ne \emptyset$ then $S_v \cap ins(F)$ is a path, and if $U(S_v) \cap ins(F)
\nsubseteq U(F)$ then one of $v, h \in ins(F) \setminus U(F)$." -/
theorem theorem_13_3 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    {D : TangleDatum cap χ} {W : Set Shat} {H F P : Drawing Shat} {v h : Shat}
    (hS : D.IsSpoke W H v h P) (hF : IsEnclave D.tb D.ord D.𝒯 F) :
    ((P.U ∩ D.ins F).Nonempty → ∃ (a b : Shat) (Q : Drawing Shat), Drawing.IsPathOf Q D.rad.G a b ∧
      Q.V = P.V ∩ D.ins F ∧ Q.E = {e ∈ P.E | e ⊆ D.ins F}) ∧
    (¬ P.U ∩ D.ins F ⊆ F.U → v ∈ D.ins F \ F.U ∨ h ∈ D.ins F \ F.U) :=
  GM19.TangleDatum.theorem_13_3_proof hS hF

open GraphMinor.GM19.TangleDatum GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (13.4)** (page 367), for an optimal hub `H`: "**13.4.** *Let
$r^* \in R^* \cap bd(W)$ with neighbours $v_1, v_2$ in $\Gamma^* \cap bd(W)$. Let $S_{v_1}$ meet
$S_{v_2}$, and let $S_{v_1} \cap S_{v_2}$ have ends $u, h$ where $h \in V(H)$. Let
$\Delta \subseteq W$ be the disc bounded by*
$$(U(S_{v_1} \cup S_{v_2}) \setminus U(S_{v_1} \cap S_{v_2})) \cup \{u\} \cup \bar{f}_1 \cup
\bar{f}_2,$$
*where $f_i$ is the edge of $\Gamma^* \cap bd(W)$ with ends $r^*, v_i$ ($i = 1, 2$). Then
$\Delta \cap U(H) = \emptyset$ unless $u = h$, in which case $\Delta \cap U(H) = \{h\}$; and
$\Delta \cap U(S_v) \subseteq bd(\Delta)$ for every $v \in V(\Gamma) \cap bd(W)$.*" The hypotheses
on `W` are those of (13.1). -/
theorem theorem_13_4 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r v₁ v₂ u : Shat}
    {f₁ f₂ : Set Shat} (hopt : D.IsOptimalWheelHub W H ρ)
    (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) (hr : r ∈ D.rad.Rstar ∩ discBd W)
    (hne : v₁ ≠ v₂) (hf₁ : f₁ ∈ D.rad.G.E) (hf₁' : tilde f₁ = {r, v₁}) (hf₂ : f₂ ∈ D.rad.G.E)
    (hf₂' : tilde f₂ = {r, v₂}) {h₁ h₂ : Shat} {S₁ S₂ Q : Drawing Shat}
    (hS₁ : D.IsSpoke W H v₁ h₁ S₁) (hS₂ : D.IsSpoke W H v₂ h₂ S₂)
    (hQ : Drawing.IsPathOf Q D.rad.G u h₁) (hQV : Q.V = S₁.V ∩ S₂.V) (hQE : Q.E = S₁.E ∩ S₂.E)
    (hm : (S₁.V ∩ S₂.V).Nonempty) {Δ : Set Shat} (hΔ : IsClosedDisc Δ) (hΔW : Δ ⊆ W)
    (hbd : discBd Δ = (S₁.U ∪ S₂.U) \ (S₁.U ∩ S₂.U) ∪ {u} ∪ closure f₁ ∪ closure f₂) :
    (u ≠ h₁ → Δ ∩ H.U = ∅) ∧ (u = h₁ → Δ ∩ H.U = {h₁}) ∧
    ∀ (v h : Shat) (P : Drawing Shat), D.IsSpoke W H v h P → Δ ∩ P.U ⊆ discBd Δ :=
  GM19.TangleDatum.theorem_13_4_proof hopt hbdS hin hr hne hf₁ hf₁' hf₂ hf₂' hS₁ hS₂ hQ hQV hQE hm hΔ hΔW hbd

open GraphMinor.GM19.TangleDatum GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (13.5)** (page 368): "With notation as above, $|E(D_v)| \le 4\rho + 4$, and
$ins(D_v) = \Delta_v$." The hypotheses on `W` are those of
(13.1). -/
theorem theorem_13_5 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat}
    (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) {Δv : Set Shat} {Dv : Drawing Shat}
    (hs : D.IsBoundarySector W H r Δv Dv) :
    Dv.E.ncard ≤ 4 * ρ + 4 ∧ D.ins Dv = Δv :=
  GM19.TangleDatum.theorem_13_5_proof hW hbdS hin hs

open GraphMinor.GM19.TangleDatum GraphMinor.GM10 GraphMinor.GM11 in
/-- **Graph Minors XIX, (13.6)** (page 368): "With notation as above, let $\mathscr{T}'$ be a tangle
with $(\Gamma \cap out(D_v), \Gamma \cap ins(D_v)) \in \mathscr{T}'$, and let $F$ be a
$\mathscr{T}$-enclave around $\mathscr{T}'$. Then $ins(F) \subseteq \Delta_v$."

(13.6): the choice of the enclave `F` puts its inside in `Δ_v`.

The paper states in one sentence that some circuit $C \subseteq F \cup D_v$ bounds a disc that
includes $ins(F) \cup \Delta_v$. The Lean proves it (`GM19.exists_enclosing_circuit`): it takes a
largest such disc, and shows that an edge of $F$ outside it would give an ear and a larger disc. -/
theorem theorem_13_6 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set Shat}
    {Dv F : Drawing Shat} {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hx : D.IsSectorEnclave W H ρ r Δv Dv ord' 𝒯' F) : D.ins F ⊆ Δv :=
  GM19.TangleDatum.theorem_13_6_proof hx

open GraphMinor.GM19.TangleDatum GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM06 in
/-- **Graph Minors XIX, (13.7)** (page 374): "With notation as in 13.6, let $S_{v_1}, S_{v_2}$ have
the same inner end. Let the vertices of $S_{v_i}$ in $V(\Gamma)$ be $v_i^1, \dots, v_i^k$ in order,
where $v_i^1 = v_i$ $(i = 1, 2)$. Then there are $k$ paths $P_1, \dots, P_k$ of $sk(\Gamma)$,
mutually vertex-disjoint, such that $P_j$ has ends $v_1^j$ and $v_2^j$ $(1 \le j \le k)$, and such
that for $1 \le j \le k$, either - $v_1^j = v_2^j \in V(S_{v_1} \cap S_{v_2})$ and $V(P_j) =
\{v_1^j\}$, or - $v_1^j, v_2^j \notin V(S_{v_1} \cap S_{v_2})$ and $U(P_j) \subseteq \Delta_v$."

Let the spokes of `v₁, v₂` meet. The vertices of `Γ` on a spoke are those at even position. There
are mutually disjoint vertex sets `P j`, one for each even position `2 * j` on the spokes, such
that either the two vertices at that position are the same vertex, on both spokes, and `P j` is this
vertex, or neither is on the other spoke, and `P j` holds a path between them of
`sk(Γ)` in `Δ_v`. -/
theorem theorem_13_7 {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r u h v₁ v₂ : Shat}
    {f₁ f₂ Δv : Set Shat} {Dv : Drawing Shat} {A₁ : GraphWalk (Drawing.toGraph D.rad.G) v₁ u}
    {A₂ : GraphWalk (Drawing.toGraph D.rad.G) v₂ u} {T : GraphWalk (Drawing.toGraph D.rad.G) u h}
    (hopt : D.IsOptimalWheelHub W H ρ) (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T)
    (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv) (hs : D.IsBoundarySector W H r Δv Dv) :
    ∃ (Sk : Drawing Shat) (G : Drawing Δv), D.IsSkPart Δv Sk G ∧ ∃ P : ℕ → Set Shat,
    (∀ j k, 2 * j ≤ (A₁.append T).length → 2 * k ≤ (A₁.append T).length → j ≠ k → Disjoint (P j) (P k)) ∧
    ∀ j, 2 * j ≤ (A₁.append T).length →
      (GraphWalk.vertexAt (A₁.append T) (2 * j) = GraphWalk.vertexAt (A₂.append T) (2 * j) ∧ GraphWalk.vertexAt (A₁.append T) (2 * j) ∈ (A₁.append T).support ∧
        GraphWalk.vertexAt (A₁.append T) (2 * j) ∈ (A₂.append T).support ∧ P j = {GraphWalk.vertexAt (A₁.append T) (2 * j)}) ∨
      (GraphWalk.vertexAt (A₁.append T) (2 * j) ∉ (A₂.append T).support ∧ GraphWalk.vertexAt (A₂.append T) (2 * j) ∉ (A₁.append T).support ∧ P j ⊆ Δv ∧
        ∃ a b : Δv, a.1 = GraphWalk.vertexAt (A₁.append T) (2 * j) ∧ b.1 = GraphWalk.vertexAt (A₂.append T) (2 * j) ∧
          ∃ K : GraphWalk G.toGraph a b, K.IsSimple ∧ ∀ z ∈ K.support, z.1 ∈ P j) :=
  GM19.TangleDatum.IsFan.theorem_13_7_proof hopt hbdS hin hf hC hs

/-! ## Section 14. Removing wheel covers -/

open GraphMinor.GM10 GraphMinor.GM11 TangleDatum in
/-- **Graph Minors XIX, (14.1)** (page 375): "Let $\chi, \mathscr{S}, \mathscr{D}$ be as in Section
10, and let $\chi$ satisfy $\mathbf{S_2}$; let $\omega_0 \in E(\Omega_\chi(2)) \cup
E(\Omega_\chi(3))$, and let $m \ge 1, n \ge 4$. Then there is a well-behaved set $\mathscr{C}_5(m,
n, q_0)$ of $\chi$-places with the following property. Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in
\mathscr{D}$ be $(m, n, \omega_0)$-flawed internally. Then there is a rooted location $\mathscr{L}$
which $(4n \cdot 5^{2m} + 3)$-isolates $\mathscr{T}$, and for which $(\Gamma, \phi, \mathscr{L}) \in
\mathscr{C}_5(m, n, \omega_0)$."

The well-behaved set is quantified existentially, as the paper means, and flawed internally uses
strict inequalities. See the correction to (14.1) and the correction on pages 357 and 362 in
`corrections/GM19.md`. Where the paper says that deleting the insides of the wheels gives a surface
$\Sigma'$ with $\hat\Sigma' \cong \hat\Sigma_\chi$, the Lean builds the homeomorphism
(`GM19.IsCutData`). -/
theorem theorem_14_1 (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] (β : Type w) [Infinite β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (hd : χ.IsDisjoint) (𝒮 : Set (ColouredPainting χ)) (hcl : IsPaintingClass χ 𝒮)
    (hS2 : ConditionS2 χ cap) (k : ℕ) (ω₀ : β) (hk : (k = 2 ∧ ω₀ ∈ χ.Ω2.E) ∨ (k = 3 ∧ ω₀ ∈ χ.Ω3.E))
    (m n : ℕ) (h1 : 1 ≤ m) (hn : 4 ≤ n) :
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
    D.IsFlawedInternally m n k ω₀ → ∃ L : RootedLocation D.P.Γ,
    L.Isolates D.tb (4 * n * 5 ^ (2 * m) + 3) D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞 :=
  GM19.theorem_14_1_proof S Shat β cap χ hd 𝒮 hcl hS2 k ω₀ hk m n h1 hn

/-! ## Section 15. Conclusion -/

open GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph in
/-- **Graph Minors XIX, (15.1)** (page 379): "Let $\Gamma$ be a 2-cell drawing with $E(\Gamma) \ne
\emptyset$ in a surface $\Sigma$ with
$\text{bd}(\Sigma) = \emptyset$, and let $\mathscr{T}$ be a tangle in $\Gamma$ with
$\text{rep}(\mathscr{T}) \ge \theta$. Let $r$ be a region of $\Gamma$, and let $X \subseteq
V(\Gamma) \cap \bar{r}$ with $|X| \le \theta$. Then the following are equivalent:" the existence of
`(A, B) ∈ 𝒯` of order `< |X|` with `X ⊆ V(A)`, and the existence of a circuit `C` of `Γ*` of length
`< 2θ` such that `|X ∩ ins(C)| > ½|E(C)|` and `r* ∈ ins(C)`. -/
theorem theorem_15_1 {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    [ConnectedSpace S] {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hE : H.E.Nonempty) (hResp : IsRespectfulDrawingTangle H θ T)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins) {r : Set S} (hr : r ∈ H.R) {w : S}
    (hw : w ∈ r) (hwV : w ∈ K.V) {X : Set S} (hXV : X ⊆ H.V) (hXr : X ⊆ closure r)
    (hXθ : X.ncard ≤ θ) :
    (∃ A B, (A, B) ∈ T ∧ separationOrder A B < X.ncard ∧ X ⊆ A.vertexSet) ↔
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ ∧
      C.length < 2 * (X ∩ ins C).ncard ∧ w ∈ ins C :=
  GM19.theorem_15_1_proof hS hE hResp hK hd hr hw hwV hXV hXr hXθ

open GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph in
/-- **Graph Minors XIX, (15.2)** (page 380): "Let $\chi$ be a colour scheme, and let $(\Gamma_0,
\phi_0)$ be a $\chi$-coloured painting. Then there exist $n \ge 0$ with the following property. Let
$(\Gamma, \phi)$ be a $\chi$-coloured painting, such that $(\Gamma_0, \phi_0)$ and $(\Gamma, \phi)$
are similarly oriented, and there is no inflation of $(\Gamma_0, \phi_0)$ in $(\Gamma, \phi)$. Let
$\mathscr{T}$ be a tangle in $\Gamma$ with metric $d$, with $\text{rep}(\mathscr{T}) >
\frac{3}{2}n$. Then either" $d(r^*_1, r^*_2) \le n$ for two distinct poles, or there is a short
circuit $F$ of $\Gamma^*$ whose inside includes a long side or many vertices of $\Phi_\chi$, or
the edges of $\Gamma_0$ along some long side have no matching edges of $\Gamma$ far apart, or some
internal edge of $\Gamma_0$ has no $|E(\Gamma_0)|$ matching edges of $\Gamma$ far apart and far
from the poles.

The paper says that the discs $S_v$ of step (3) of the proof (page 382) clearly exist. The Lean
proves steps (2) and (3) in the form of closed discs that (3.2) of Graph Minors XII uses
(`GraphMinor.GM19.theorem152Feasibility` in `Feasibility.lean`), building the homeomorphism of step
(2) with `GraphMinor.GM19.exists_realizing_discs` (`DiscRealize.lean`). -/
theorem theorem_15_2 (S Shat : Type) [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
    [T2Space Shat] (β : Type w) (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (P₀ : ColouredPainting χ) :
    ∃ n : ℕ, 8 ≤ n ∧ Even n ∧ ∃ ω : Set S → List β,
    (∀ side ∈ χ.Φ.longSides, IsBorderLabels P₀ side (ω side)) ∧ ∀ D : TangleDatum cap χ,
    (¬ IsOrientableSurface S ∨ ∃ o : SurfaceOrientation S, ∀ P ∈ ({P₀, D.P} : Set _), ∀ e ∈ P.Γ.E,
      (tilde e).ncard = 3 → ∀ a b c : S, P.Γ.γ e = [a, b, c] → o.pos (closure e) a b c) →
    (¬ ∃ σv σe, IsColouredInflation χ P₀ D.P σv σe) → 3 * n < 2 * D.rep →
    (∃ r₁ ∈ D.rad.poles, ∃ r₂ ∈ D.rad.poles, r₁ ≠ r₂ ∧ D.vDist r₁ r₂ ≤ n) ∨
    (∃ F : Drawing Shat, F.IsCircuitOf D.rad.G ∧ F.E.ncard ≤ 2 * n ∧
      ((∃ side ∈ χ.Φ.longSides, cap.emb '' side ⊆ D.ins F) ∨ F.E.ncard <
        2 * ((cap.emb '' χ.Φ.V) ∩ D.ins F).ncard)) ∨
    (∃ side ∈ χ.Φ.longSides, D.NoSideMatch side (n / 2) (ω side)) ∨
    (∃ f ∈ P₀.Γ.E, Painting.IsInternal f ∧
      D.NoInternalMatch P₀.Γ.E.ncard n (tilde f).ncard (P₀.φ f)) :=
  GM19.theorem_15_2_proof S Shat β cap χ P₀

end GraphMinor.GM19
