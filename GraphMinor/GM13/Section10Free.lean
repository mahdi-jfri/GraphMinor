module

public import GraphMinor.GM13.Section10
public import GraphMinor.GM21.Final
public import GraphMinor.GM22.Join21
public import GraphMinor.GM22.Section8To13

/-!
# Graph Minors XIII, Section 10: Hypothesis-Free Forms of (10.2), (10.3), (10.4), and (10.5)

This file combines `GraphMinor.GM13.Section10`, `GM22.gm13_theorem_10_2`
(`GraphMinor.GM22.Section8To13`), `GM22.gm21Theorem11Statement_iff_gm21`
(`GraphMinor.GM22.Join21`), and `GM21.theorem_1_1_proof` (`GraphMinor.GM21.Final`) to prove:
- `theorem_10_2` / `theorem_10_2_free` (**Graph Minors XIII, (10.2)**, page 107) with no hypotheses;
- `theorem_10_3` (**Graph Minors XIII, (10.3)**, pages 107–108) with no hypotheses;
- `algorithm_10_4_correct_free` and `theorem_10_4` (**Graph Minors XIII, Algorithm (10.4)**,
  page 107) with no hypotheses;
- `algorithm_10_5_correct_free` and `theorem_10_5` (**Graph Minors XIII, Algorithm (10.5)**,
  pages 108–109) with no hypotheses.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM05 GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-- Hypothesis-free alias for **Graph Minors XIII, (10.2)** (Section 10, page 107):
“(10.2) *For any $q$, $\delta \ge 0$ and $h \ge 2$, even, there exists $f(h) \ge h$, even, such
that under Hypothesis C, if $H' \subseteq H$ is an $h$-homogeneous subwall of height $f(h)$ then
both middle vertices of $H'$ are irrelevant to the $\delta$-folio of $G$ relative to $X$.*” -/
theorem theorem_10_2_free : GM13Theorem102Statement.{u, v} :=
  theorem_10_2_proof.{u, v}

/-- **Graph Minors XIII, (10.3)** (Section 10, pages 107–108):
"(10.3) *For all $q$, $\delta \ge 0$ there exists $h \ge 0$, even, such that for all $\omega \ge 0$
there is an algorithm as in (10.4) with running time $O(\varepsilon^2)$.*"

Mathematical content of the proof of (10.3) (pages 107–108): given
`h = sec10WallHeight theorem_10_2_proof q δ` and input `G, X, H, S_H, 𝒜` satisfying Hypothesis C with
`h ≤ H.height` (in particular when `H.height = h`) and branch-width `≤ ω` for each interior member
`A ∈ 𝒜`, Algorithm (10.1) finds a vision `vis`, and the subwall recursion maintaining invariants
(i)–(iii) terminates at some step `i` (`1 ≤ i ≤ |𝒯_1| + 1`) at an `h_{i+1}`-homogeneous subwall
`H_i` of `H` of height `h_i`, both of whose middle vertices are irrelevant to the `δ`-folio of `G`
relative to `X` by `(10.2)`.

The Word RAM program `GM13.algorithm_10_3` follows the paper (pages 107–108):
an `O(ε²)` Word RAM implementation calling Algorithm (10.1) (`O(ε²)`) to find a vision and then
running at most `|𝒯_1| + 1` iterations (`O(v)` per iteration, checking the bounded number of
subwalls of `H_i` of height `h_{i+1}`) to output a middle vertex of `H_i`. -/
theorem theorem_10_3_proof
    (q δ ω : ℕ)
    (G : Digraph α β) (X : Set α) (H : Wall α β)
    (S_H : Society α β) (𝒜 : Set (Graph α β))
    (hC : HypothesisC G q X H S_H 𝒜)
    (hH_height : sec10WallHeight theorem_10_2_proof.{u, v} q δ ≤ H.height)
    (hbw : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω) :
    let n := (folioClassT1 q δ).ncard
    let h_seq := sec10HeightSeq theorem_10_2_proof.{u, v} q δ
    ∃ (vis : Vision G X H S_H 𝒜) (i : ℕ) (H_i : Wall α β)
      (𝒯_i : Set (Σ j : Fin (q + 4), Set (RootedDigraph ℕ ℕ j.val))),
      1 ≤ i ∧ i ≤ n + 1 ∧
      H_i.IsSubwallOf H ∧ H_i.height = h_seq i ∧
      𝒯_i ⊆ folioClassT1 q δ ∧ 𝒯_i.ncard = n + 1 - i ∧
      (∀ ⦃A : Graph α β⦄ (hInt : IsInteriorMember H 𝒜 A),
        vis.vOf A ∈ H_i.insideVerts →
        sigmaDeltaFolio q δ (Nat.lt_succ_of_le (vis.pi_properties hC hInt).2.1)
          (rootedDigraphOfList (vis.tildeA A) (vis.pi A) (vis.pi_properties hC hInt).2.2) ∈ 𝒯_i) ∧
      IsHomogeneousSubwall vis δ (h_seq (i + 1)) H_i ∧
      IsIrrelevantVertex G δ X H_i.middleVertex₁ ∧
      IsIrrelevantVertex G δ X H_i.middleVertex₂ :=
  theorem_10_3_of_theorem_10_2 q δ ω G X H S_H 𝒜 hC hH_height hbw

/-- **Graph Minors XIII, Algorithm (10.4)** (Section 10, page 107):
"(10.4) Algorithm.
*Input:* $G$, $X$, $H$, $\mathcal{A}$ satisfying Hypothesis C, where $H$ has height $h$, and for
each interior $A \in \mathcal{A}$ a branch-decomposition of $A$ of width $\le \omega$.
*Output:* A vertex irrelevant to the $\delta$-folio of $G$ relative to $X$."

The Word RAM program `GM13.algorithm_10_4` follows the paper (pages 107–108):
an `O(ε²)` Word RAM implementation calling Algorithm (10.1) and the subwall homogeneity recursion
of `(10.3)` to return a middle vertex of `H_i`. -/
theorem algorithm_10_4_correct_free
    (q δ ω : ℕ)
    (G : Digraph α β) (X : Set α) (H : Wall α β)
    (S_H : Society α β) (𝒜 : Set (Graph α β))
    (hC : HypothesisC G q X H S_H 𝒜)
    (hH_height : sec10WallHeight theorem_10_2_proof.{u, v} q δ ≤ H.height)
    (hbw : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω) :
    ∃ v ∈ G.vertexSet \ X, IsIrrelevantVertex G δ X v :=
  algorithm_10_4_correct q δ ω G X H S_H 𝒜 hC hH_height hbw

/-- **Graph Minors XIII, (10.4)** (Section 10, page 107):
"(10.4) Algorithm.
*Input:* $G$, $X$, $H$, $\mathcal{A}$ satisfying Hypothesis C, where $H$ has height $h$, and for
each interior $A \in \mathcal{A}$ a branch-decomposition of $A$ of width $\le \omega$.
*Output:* A vertex irrelevant to the $\delta$-folio of $G$ relative to $X$." -/
theorem theorem_10_4_proof
    (q δ ω : ℕ)
    (G : Digraph α β) (X : Set α) (H : Wall α β)
    (S_H : Society α β) (𝒜 : Set (Graph α β))
    (hC : HypothesisC G q X H S_H 𝒜)
    (hH_height : sec10WallHeight theorem_10_2_proof.{u, v} q δ ≤ H.height)
    (hbw : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω) :
    ∃ v ∈ G.vertexSet \ X, IsIrrelevantVertex G δ X v :=
  theorem_10_4_of_theorem_10_2 q δ ω G X H S_H 𝒜 hC hH_height hbw

/-- **Graph Minors XIII, Algorithm (10.5)** (Section 10, pages 108–109):
"(10.5) Algorithm.
*Input:* A digraph $G$ and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$.
*Output:* The $\delta$-folio of $G$ relative to $Z$.
*Running time:* $O(v^3)$."

Mathematical correctness of Steps (1)–(4) (pages 108–109):
1. Step (1) applies `(6.5)` (`algorithm_6_5_correct`) to obtain a sparse subdigraph `G' ⊆ G` with
   `Z ⊆ V(G')`, `|E(G')| ≤ C |V(G')|`, and the same `δ`-folio relative to `Z` as `G`.
2. In each iteration of the recursion starting from `G_1 = G'`, applying `(9.8)`/`(9.9)`
   (`GM13Theorem98Statement`) to `G_i \ Z` either:
   - Step (2): yields `GraphBranchWidthLE (G_i \ Z).toGraph ω`, hence
     `GraphBranchWidthLE G_i.toGraph (max ω 2 + ξ)`, so `(4.1)` (`algorithm_4_1_correct`) computes
     the `δ`-folio of `G_i` (and hence of `G`) relative to `Z` together with a modelling of it; or
   - Step (3): yields a `K_p`-model in `G_i`, so `(6.2)`
     (`exists_irrelevantVertex_of_completeGraph_minor`) finds an irrelevant vertex `v ∈ V(G_i) \ Z`;
     or
   - Step (4): yields `X, H, S_H, 𝒜` satisfying Hypothesis C in `G_i \ Z`, so `X' = X ∪ Z`
     satisfies Hypothesis C in `G_i`, `(10.4)` (`algorithm_10_4_correct`) finds a vertex `v`
     irrelevant to the `δ`-folio of `G_i` relative to `X'`, and `(2.1)` (`IsIrrelevantVertex.mono`)
     shows `v` is irrelevant relative to `Z`.
   Thus the recursion terminates in at most `|V(G')|` deletions at a subdigraph `G_i ⊆ G'` with
   `Z ⊆ V(G_i)`, `GraphBranchWidthLE G_i.toGraph (max ω 2 + ξ)`, and the same `δ`-folio relative to
   `Z` as `G`.

The Word RAM program `GM13.algorithm_10_5` follows the paper (pages 108–109):
an `O(v³)` Word RAM implementation of Step (1) calling Algorithm (6.5) (`O(v³)`) to obtain `G' ⊆ G`
with `|E(G')| ≤ C |V(G')|`, followed by at most `v(G)` iterations (`O(ε(G')²) = O(v²)` per
iteration) invoking Algorithm (9.9) on `G_i \ Z`, Algorithm (4.1) in Step (2), Algorithm (6.2) in
Step (3), and Algorithm (10.4) in Step (4). -/
theorem algorithm_10_5_correct_free
    [Nonempty β] (ξ δ : ℕ) :
    let p := 5 * ξ / 2 + 3 * δ + 1
    let C := δ + 2 * (δ + 1) * 2 ^ (p - 3)
    let q := p.choose 2 + ξ - 1
    let h := sec10MaxWallHeight theorem_10_2_proof.{u, v} q δ
    2 ≤ h ∧ Even h ∧
    ∃ (ω : ℕ),
      ∀ (G : Digraph α β) (Z : Set α),
        G.IsFinite → Z ⊆ G.vertexSet → Z.ncard ≤ ξ →
        ∃ (G' G_final : Digraph α β),
          G'.IsSubdigraph G ∧ Z ⊆ G'.vertexSet ∧
          HasSameDeltaFolioRel G G' δ Z ∧
          G'.edgeSet.ncard ≤ C * G'.vertexSet.ncard ∧
          G_final.IsSubdigraph G' ∧ Z ⊆ G_final.vertexSet ∧
          GraphBranchWidthLE G_final.toGraph (max ω 2 + ξ) ∧
          HasSameDeltaFolioRel G G_final δ Z ∧
          (∀ {k : ℕ} (r : Fin k → α) (hr : ∀ j, r j ∈ G_final.vertexSet)
            (hrG : ∀ j, r j ∈ G.vertexSet),
            Injective r → range r ⊆ Z →
            HasSameDeltaFolio (RootedDigraph.mk G r hrG) (RootedDigraph.mk G_final r hr) δ ∧
            (Nonempty α → ∃ (vMod : RootedDigraph ℕ ℕ k → ℕ → Digraph α β)
              (eMod : RootedDigraph ℕ ℕ k → ℕ → β),
              IsDeltaFolioModelling (RootedDigraph.mk G_final r hr) δ vMod eMod)) :=
  algorithm_10_5_correct (α := α) (β := β) ξ δ

/-- **Graph Minors XIII, (10.5)** (Section 10, pages 108–109):
"(10.5) Algorithm.
*Input:* A digraph $G$ and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$.
*Output:* The $\delta$-folio of $G$ relative to $Z$.
*Running time:* $O(v^3)$." -/
theorem theorem_10_5_proof
    [Nonempty β] (ξ δ : ℕ) :
    let p := 5 * ξ / 2 + 3 * δ + 1
    let C := δ + 2 * (δ + 1) * 2 ^ (p - 3)
    let q := p.choose 2 + ξ - 1
    let h := sec10MaxWallHeight theorem_10_2_proof.{u, v} q δ
    2 ≤ h ∧ Even h ∧
    ∃ (ω : ℕ),
      ∀ (G : Digraph α β) (Z : Set α),
        G.IsFinite → Z ⊆ G.vertexSet → Z.ncard ≤ ξ →
        ∃ (G' G_final : Digraph α β),
          G'.IsSubdigraph G ∧ Z ⊆ G'.vertexSet ∧
          HasSameDeltaFolioRel G G' δ Z ∧
          G'.edgeSet.ncard ≤ C * G'.vertexSet.ncard ∧
          G_final.IsSubdigraph G' ∧ Z ⊆ G_final.vertexSet ∧
          GraphBranchWidthLE G_final.toGraph (max ω 2 + ξ) ∧
          HasSameDeltaFolioRel G G_final δ Z ∧
          (∀ {k : ℕ} (r : Fin k → α) (hr : ∀ j, r j ∈ G_final.vertexSet)
            (hrG : ∀ j, r j ∈ G.vertexSet),
            Injective r → range r ⊆ Z →
            HasSameDeltaFolio (RootedDigraph.mk G r hrG) (RootedDigraph.mk G_final r hr) δ ∧
            (Nonempty α → ∃ (vMod : RootedDigraph ℕ ℕ k → ℕ → Digraph α β)
              (eMod : RootedDigraph ℕ ℕ k → ℕ → β),
              IsDeltaFolioModelling (RootedDigraph.mk G_final r hr) δ vMod eMod)) :=
  theorem_10_5_of_theorem_10_2 (α := α) (β := β) ξ δ

end GraphMinor.GM13
