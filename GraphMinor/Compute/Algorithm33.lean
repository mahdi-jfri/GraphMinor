module

public import GraphMinor.Compute.BranchDecomp
public import GraphMinor.Compute.Algorithm64
public import GraphMinor.Compute.Bridge3
public import Mathlib.Tactic.Linarith

/-!
# GM XIII Algorithm (3.3): Branch-Decomposition Approximation in Time `O(v²)`

This file formalizes Algorithm (3.3) of Robertson and Seymour, *Graph Minors. XIII. The Disjoint
Paths Problem*, pages 72–75, on the Word RAM:

> **(3.3) Algorithm.**
> *Input:* A graph `G` with `|E(G)| ≥ 2`.
> *Output:* A subgraph `G'` of `G` and a branch-decomposition of `G'` of width `≤ 3ω`, such that
> either `G' = G` or `G'` has branch-width `≥ ω`.
> *Running time:* `O(v² + ε)`.

Here `ω ≥ 2` is a fixed integer parameter, and the input is taken as the underlying simple graph
`H₁ : SimpleGraph (Fin n)` with `|E(H₁)| ≥ 2` encoded in `encGraph` format. (The linear-time step
from a multigraph `G` to `H₁` and the conversion of a branch-decomposition of `H₁` back to `G` at
the end wait for `ram`'s multigraph format.)

Following the paper's description (pages 72–75):
1. We construct a subgraph `H₂ ≤ H₁` with `|E(H₂)| = min(|E(H₁)|, ⌊(3ω/2 - 1)|V(H₁)|⌋ + 1)`, so
   that `|E(H₂)| ≤ (3ω/2 - 1)|V(H₁)| + 1`, and either `H₂ = H₁` or `|E(H₂)| > (3ω/2 - 1)|V(H₁)|`.
2. We initialize `G₁ = H₂`, `T₁` a 2-vertex tree, and `τ₁` mapping one edge of `G₁` to leaf `0` and
   all other edges of `G₁` to leaf `1`.
3. In each iteration of the recursion (1)–(6):
   - **(1)** If `τ_i` is a bijection from `E(G_i)` to the leaves of `T_i`, we set `H₃ = G_i` and
     stop.
   - **(2)** Otherwise, we find a leaf `v` of `T_i` with at least two edges of `G_i` mapped to `v`,
     compute `Z = V(R ∩ R') = leafCutVerts G_i τ_i v` of size `≤ 3ω`, and select an edge `g ∈ E(R)`
     (incident with `Z` when `Z ≠ ∅`).
   - **(3)** If `|Z| < 3ω`, we split leaf `v` into two new leaves `v₁, v₂`, assigning `g` to `v₁`
     and `E(R) \ {g}` to `v₂`.
   - **(4)–(5)** If `|Z| = 3ω`, we enumerate all valid partitions `(Z₁, Z₂, Z₃)` of `Z` with
     `|Z₁|, |Z₂| ≤ 2ω - |Z₃|/2` and `|Z₃| ≤ ω`, and test via Menger's disjoint paths algorithm
     (`mengerLoopRegProg`) whether `R \ Z` has `< ω - |Z₃| + 1` vertex-disjoint paths between
     `N_R(Z₁) \ Z` and `N_R(Z₂) \ Z` (with no edge of `R` directly joining `Z₁` to `Z₂`). If a
     residual cut is found, we split leaf `v` according to the cut (`isPartialBranchDecomp_step5`).
   - **(6)** If no partition yields a cut, we delete `g` from `G_i` (`G_{i+1} = G_i \ g`) and
     record the certificate `(G_i, g, Z)`, proving via `no_balanced_separation_of_step6` that `G_i`
     has no separation `(A, B)` of order `≤ ω` satisfying
     `|Z - V(A)|, |Z - V(B)| ≤ (2/3)|Z| - (1/2)|Z ∩ V(A ∩ B)|`.
-/

@[expose] public section

namespace GraphMinor.Compute

open scoped BigOperators
open SimpleGraph

/-! ### Section 1: Input/Output Types, Subgraph `H₂`, and Edge-Array Graph Representation -/

/-- Input to Algorithm (3.3): a simple graph `H₁` on `Fin n` with at least 2 edges. -/
structure Alg33Input where
  /-- Number of vertices `n = |V(H₁)|`. -/
  n : ℕ
  /-- The input simple graph `H₁` on `Fin n`. -/
  H₁ : SimpleGraph (Fin n)
  /-- Decidability of adjacency in `H₁`. -/
  [decAdj : DecidableRel H₁.Adj]
  /-- Precondition `|E(H₁)| ≥ 2` (page 72). -/
  h_edges : 2 ≤ H₁.edgeFinset.card

attribute [instance] Alg33Input.decAdj

/-- Flat word-list encoding of `Alg33Input` using `encGraph`. -/
def encAlg33In (x : Alg33Input) : List ℕ :=
  encGraph x.H₁

/-- Size parameter `v = |V(H₁)|` of `Alg33Input`. -/
def alg33Size (x : Alg33Input) : ℕ := x.n

/-- Output of Algorithm (3.3) on input `x : Alg33Input`:
- `G'`: a subgraph of `x.H₁`
- `(T, τ)`: a branch-decomposition of `G'` on `Fin t` of width `≤ 3ω`
- `(G_step6, g, Z)`: certificate when Step (6) occurred, consisting of the graph `G_i` at the last
  Step (6) iteration, the edge `g` deleted at that step, and the cut set `Z` of size `3ω`. -/
structure Alg33Output (x : Alg33Input) where
  /-- The output subgraph `G'` of `x.H₁`. -/
  G' : SimpleGraph (Fin x.n)
  /-- Number of vertices of the branch-decomposition tree `T`. -/
  t : ℕ
  /-- The branch-decomposition tree `T` on `Fin t`. -/
  T : SimpleGraph (Fin t)
  /-- Map sending edges of `G'` to leaves of `T`. -/
  τ : Sym2 (Fin x.n) → Fin t
  /-- When Step (6) occurred, the graph `G_i` at the last Step (6) iteration. -/
  G_step6 : SimpleGraph (Fin x.n)
  /-- When Step (6) occurred, the last edge `g` deleted in Step (6). -/
  g : Sym2 (Fin x.n)
  /-- When Step (6) occurred, the vertex set `Z = V(R ∩ R')` at that Step (6) iteration. -/
  Z : Finset (Fin x.n)

/-- Three-case certificate predicate for the output of Algorithm (3.3) with parameter `ω`:
1. `(out.T, out.τ)` is a branch-decomposition of `out.G'` of width `≤ 3ω`
   (`IsBranchDecompOfWidthLe (3 * ω) out.G' out.T out.τ`).
2. `out.G'` is a subgraph of `x.H₁` (`out.G' ≤ x.H₁`).
3. One of three cases holds:
   - `out.G' = x.H₁`; or
   - `out.G' ≠ x.H₁`, `(|E(out.G')| : ℚ) ≤ ((3/2)ω - 1)|V(H₁)| + 1`, and
     `(|E(out.G')| : ℚ) > ((3/2)ω - 1)|V(H₁)|`; or
   - Step (6) happened: `out.G_step6 ≤ x.H₁`, `out.g ∈ out.G_step6.edgeFinset`,
     `|out.Z| = 3ω`, `out.G' ≤ out.G_step6 \ {out.g}`, `out.G' = out.G_step6 \ {out.g}`
     (every iteration after the last Step (6) kept `G_i` unchanged), and `out.G_step6` has no
     separation `(A, B)` of order `≤ ω` with
     `|Z - V(A)|, |Z - V(B)| ≤ (2/3)|Z| - (1/2)|Z ∩ V(A ∩ B)|` (`sep.IsBalancedQ out.Z`). -/
def IsValidAlg33OutputCases (ω : ℕ) (x : Alg33Input) (out : Alg33Output x) : Prop :=
  haveI := Classical.decRel out.G'.Adj
  haveI := Classical.decRel out.T.Adj
  haveI := Classical.decRel out.G_step6.Adj
  IsBranchDecompOfWidthLe (3 * ω) out.G' out.T out.τ ∧
  out.G' ≤ x.H₁ ∧
  (out.G' = x.H₁ ∨
   (out.G' ≠ x.H₁ ∧
    (out.G'.edgeFinset.card : ℚ) ≤ ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (x.n : ℚ) + 1 ∧
    (out.G'.edgeFinset.card : ℚ) > ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (x.n : ℚ)) ∨
   (out.G_step6 ≤ x.H₁ ∧
    out.g ∈ out.G_step6.edgeFinset ∧
    out.Z.card = 3 * ω ∧
    out.G' ≤ out.G_step6.deleteEdges {out.g} ∧
    out.G' = out.G_step6.deleteEdges {out.g} ∧
    ∀ sep : GraphSeparation out.G_step6, sep.order ≤ ω → ¬ sep.IsBalancedQ out.Z))

/-- Validity predicate for the output of Algorithm (3.3) with parameter `ω` (GM XIII (3.3),
page 72):
- `out.G'` is a subgraph of `x.H₁` (`out.G' ≤ x.H₁`);
- `(out.T, out.τ)` is a branch-decomposition of `out.G'` of width `≤ 3ω`
  (`IsBranchDecompOfWidthLe (3 * ω) out.G' out.T out.τ`, which by `isBranchDecompOfWidthLe_iff_gm13`
  is equivalent to `GM13.IsGraphBranchDecomposition out.G'.toGMGraph out.T out.τ ∧
  GM13.graphBranchDecompWidth out.G'.toGMGraph out.T out.τ ≤ 3 * ω`);
- either `out.G' = x.H₁`, or `out.G'` has branch-width `≥ ω` in `GM13`'s terms
  (`¬ GM13.GraphBranchWidthLE out.G'.toGMGraph (ω - 1)`). -/
def IsValidAlg33Output (ω : ℕ) (x : Alg33Input) (out : Alg33Output x) : Prop :=
  haveI := Classical.decRel out.G'.Adj
  haveI := Classical.decRel out.T.Adj
  out.G' ≤ x.H₁ ∧
  IsBranchDecompOfWidthLe (3 * ω) out.G' out.T out.τ ∧
  (out.G' = x.H₁ ∨ ¬ GM13.GraphBranchWidthLE out.G'.toGMGraph (ω - 1))

/-- Deduction of `IsValidAlg33Output` from `IsValidAlg33OutputCases` using `GM13.theorem_3_2_proof`,
`GM13.theorem_3_1_proof`, and `GM13.algorithm_3_3_step_6_deleteEdge` (via
`eq_or_not_graphBranchWidthLE_of_alg33_cases`). -/
theorem IsValidAlg33OutputCases.to_isValidAlg33Output {ω : ℕ} (hω : 2 ≤ ω)
    {x : Alg33Input} {out : Alg33Output x}
    (h : IsValidAlg33OutputCases ω x out) :
    IsValidAlg33Output ω x out := by
  let _ := Classical.decRel out.G'.Adj
  let _ := Classical.decRel out.T.Adj
  let _ := Classical.decRel out.G_step6.Adj
  rcases h with ⟨hbd, hle, hcases⟩
  exact ⟨hle, hbd,
    eq_or_not_graphBranchWidthLE_of_alg33_cases hω x.H₁ out.G' out.G_step6 out.g out.Z hcases⟩

/-- Maximum number of edges `⌊(3ω/2 - 1)n⌋ + 1 = ((3ω - 2)n) / 2 + 1` in the subgraph `H₂`
of `H₁` (page 72). -/
def maxEdgesH2 (ω n : ℕ) : ℕ :=
  ((3 * ω - 2) * n) / 2 + 1

theorem two_le_maxEdgesH2 {ω n : ℕ} (hω : 2 ≤ ω) (hn : 1 ≤ n) :
    2 ≤ maxEdgesH2 ω n := by
  unfold maxEdgesH2
  have h1 : 4 ≤ 3 * ω - 2 := by omega
  have h2 : 4 ≤ (3 * ω - 2) * n := by
    calc 4 = 4 * 1 := rfl
      _ ≤ (3 * ω - 2) * n := Nat.mul_le_mul h1 hn
  omega

theorem maxEdgesH2_le_rat {ω n : ℕ} (hω : 1 ≤ ω) :
    (maxEdgesH2 ω n : ℚ) ≤ ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ) + 1 := by
  unfold maxEdgesH2
  have hdiv : 2 * (((3 * ω - 2) * n) / 2) ≤ (3 * ω - 2) * n := Nat.mul_div_le _ 2
  have hcast : (2 : ℚ) * ((((3 * ω - 2) * n) / 2 : ℕ) : ℚ) ≤ ((3 * ω - 2 : ℕ) : ℚ) * (n : ℚ) := by
    exact_mod_cast hdiv
  have hsub : ((3 * ω - 2 : ℕ) : ℚ) = 3 * (ω : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [hsub] at hcast
  push_cast
  linarith

theorem maxEdgesH2_gt_rat {ω n : ℕ} (hω : 1 ≤ ω) :
    (maxEdgesH2 ω n : ℚ) > ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ) := by
  unfold maxEdgesH2
  have hdiv : (3 * ω - 2) * n < 2 * (((3 * ω - 2) * n) / 2 + 1) := by omega
  have hcast : ((3 * ω - 2 : ℕ) : ℚ) * (n : ℚ) <
      (2 : ℚ) * (((((3 * ω - 2) * n) / 2 + 1 : ℕ) : ℚ)) := by
    exact_mod_cast hdiv
  have hsub : ((3 * ω - 2 : ℕ) : ℚ) = 3 * (ω : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [hsub] at hcast
  push_cast at hcast ⊢
  linarith

theorem length_allPairs (n : ℕ) : (allPairs n).length = n * n := by
  unfold allPairs
  rw [List.length_flatMap]
  simp [List.map_const', List.sum_replicate]

theorem length_edgeListOf_le_sq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (edgeListOf G).length ≤ n * n := by
  unfold edgeListOf
  exact (List.length_filter_le _ (allPairs n)).trans (by rw [length_allPairs])

theorem one_le_n_of_two_le_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : 2 ≤ G.edgeFinset.card) : 1 ≤ n := by
  have hlen : 2 ≤ (edgeListOf G).length := by
    rw [length_edgeListOf_eq_card_edgeFinset]
    exact h
  have hsq : 2 ≤ n * n := hlen.trans (length_edgeListOf_le_sq G)
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp at hsq
  · exact hpos

/-- Unordered edge `s(u, v) : Sym2 (Fin n)` at index `k` of `edges`. -/
def symEdgeAt {n : ℕ} (edges : List (Fin n × Fin n)) (k : Fin edges.length) : Sym2 (Fin n) :=
  s((edges[k.1]'k.2).1, (edges[k.1]'k.2).2)

theorem symEdgeAt_injective {n : ℕ} {G : SimpleGraph (Fin n)} {edges : List (Fin n × Fin n)}
    (hedges : IsSimpleEdgeList G edges) :
    Function.Injective (symEdgeAt edges) := by
  intro i j hij
  ext
  by_contra hne
  unfold symEdgeAt at hij
  rw [Sym2.eq_iff] at hij
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hedges.2.1 i.1 j.1 hlt j.2 hij
  · have hij' :
        ((edges[j.1]'j.2).1 = (edges[i.1]'i.2).1 ∧ (edges[j.1]'j.2).2 = (edges[i.1]'i.2).2) ∨
        ((edges[j.1]'j.2).1 = (edges[i.1]'i.2).2 ∧ (edges[j.1]'j.2).2 = (edges[i.1]'i.2).1) := by
      rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    exact hedges.2.1 j.1 i.1 hgt i.2 hij'

/-- Adjacency relation on `Fin n` induced by a subset of active edge indices
`aliveSet : Finset (Fin edges.length)` in an edge list `edges`. -/
def aliveEdgeAdj {n : ℕ} (edges : List (Fin n × Fin n)) (aliveSet : Finset (Fin edges.length))
    (u v : Fin n) : Prop :=
  ∃ k ∈ aliveSet,
    (((edges[k.1]'k.2).1 = u ∧ (edges[k.1]'k.2).2 = v) ∨
     ((edges[k.1]'k.2).1 = v ∧ (edges[k.1]'k.2).2 = u))

instance instDecidableAliveEdgeAdj {n : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (u v : Fin n) :
    Decidable (aliveEdgeAdj edges aliveSet u v) := by
  unfold aliveEdgeAdj
  infer_instance

/-- The simple graph on `Fin n` formed by the edges at indices `k ∈ aliveSet`. -/
def graphOfAlive {n : ℕ} (edges : List (Fin n × Fin n))
    (hloop : ∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2)
    (aliveSet : Finset (Fin edges.length)) : SimpleGraph (Fin n) where
  Adj := aliveEdgeAdj edges aliveSet
  symm := ⟨fun _ _ ⟨k, hal, h⟩ => ⟨k, hal, h.symm⟩⟩
  loopless := ⟨fun _ ⟨k, _, h⟩ => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hloop k.1 k.2 (h1.trans h2.symm)⟩

instance instDecidableRelGraphOfAlive {n : ℕ} (edges : List (Fin n × Fin n))
    (hloop : ∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2)
    (aliveSet : Finset (Fin edges.length)) :
    DecidableRel (graphOfAlive edges hloop aliveSet).Adj :=
  fun u v => instDecidableAliveEdgeAdj edges aliveSet u v

theorem graphOfAlive_le_graphOfEdgeList {n : ℕ} (edges : List (Fin n × Fin n))
    (hloop : ∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2)
    (aliveSet : Finset (Fin edges.length)) :
    graphOfAlive edges hloop aliveSet ≤ graphOfEdgeList edges hloop := by
  intro u v ⟨k, _, hmatch⟩
  exact ⟨k.1, k.2, hmatch⟩

theorem graphOfAlive_univ {n : ℕ} (edges : List (Fin n × Fin n))
    (hloop : ∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2) :
    graphOfAlive edges hloop Finset.univ = graphOfEdgeList edges hloop := by
  ext u v
  constructor
  · rintro ⟨k, _, h⟩
    exact ⟨k.1, k.2, h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, h⟩

theorem graphOfAlive_adj_at_iff {n : ℕ} {G : SimpleGraph (Fin n)} {edges : List (Fin n × Fin n)}
    (hedges : IsSimpleEdgeList G edges)
    (aliveSet : Finset (Fin edges.length)) (k : Fin edges.length) :
    (graphOfAlive edges hedges.1 aliveSet).Adj (edges[k.1]'k.2).1 (edges[k.1]'k.2).2 ↔
      k ∈ aliveSet := by
  constructor
  · rintro ⟨j, hj_al, hmatch⟩
    have heq : symEdgeAt edges j = symEdgeAt edges k := by
      unfold symEdgeAt
      rw [Sym2.eq_iff]
      exact hmatch
    have hjk : j = k := symEdgeAt_injective hedges heq
    rwa [← hjk]
  · intro hal
    exact ⟨k, hal, Or.inl ⟨rfl, rfl⟩⟩

theorem mem_edgeFinset_graphOfAlive_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList G edges)
    (aliveSet : Finset (Fin edges.length)) (e : Sym2 (Fin n)) :
    e ∈ (graphOfAlive edges hedges.1 aliveSet).edgeFinset ↔
      ∃ k ∈ aliveSet, symEdgeAt edges k = e := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeFinset, mem_edgeSet]
    constructor
    · rintro ⟨k, hal, hmatch⟩
      refine ⟨k, hal, ?_⟩
      unfold symEdgeAt
      rw [Sym2.eq_iff]
      exact hmatch
    · rintro ⟨k, hal, heq⟩
      unfold symEdgeAt at heq
      rw [Sym2.eq_iff] at heq
      exact ⟨k, hal, heq⟩

theorem edgeFinset_graphOfAlive_eq_image {n : ℕ} {G : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList G edges)
    (aliveSet : Finset (Fin edges.length)) :
    (graphOfAlive edges hedges.1 aliveSet).edgeFinset =
      aliveSet.image (symEdgeAt edges) := by
  ext e
  rw [mem_edgeFinset_graphOfAlive_iff hedges, Finset.mem_image]

theorem card_edgeFinset_graphOfAlive {n : ℕ} {G : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList G edges)
    (aliveSet : Finset (Fin edges.length)) :
    (graphOfAlive edges hedges.1 aliveSet).edgeFinset.card = aliveSet.card := by
  rw [edgeFinset_graphOfAlive_eq_image hedges,
    Finset.card_image_of_injective _ (symEdgeAt_injective hedges)]

theorem graphOfAlive_erase_eq_deleteEdges {n : ℕ} {G : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList G edges)
    (aliveSet : Finset (Fin edges.length)) (g_idx : Fin edges.length) :
    graphOfAlive edges hedges.1 (aliveSet.erase g_idx) =
      (graphOfAlive edges hedges.1 aliveSet).deleteEdges {symEdgeAt edges g_idx} := by
  ext u v
  rw [deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hal, hmatch⟩
    obtain ⟨hk_ne, hk_al⟩ := Finset.mem_erase.mp hal
    refine ⟨⟨k, hk_al, hmatch⟩, ?_⟩
    intro heq
    have hsym : symEdgeAt edges k = symEdgeAt edges g_idx := by
      rw [← heq]
      unfold symEdgeAt
      rw [Sym2.eq_iff]
      exact hmatch
    exact hk_ne (symEdgeAt_injective hedges hsym)
  · rintro ⟨⟨k, hal, hmatch⟩, hne⟩
    have hk_ne : k ≠ g_idx := by
      intro h
      subst h
      apply hne
      unfold symEdgeAt
      rw [Sym2.eq_iff]
      rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    exact ⟨k, Finset.mem_erase.mpr ⟨hk_ne, hal⟩, hmatch⟩

/-- Canonical extension of an edge-index leaf assignment `f_tau : Fin edges.length → Fin t` to
`Sym2 (Fin n) → Fin t`. -/
def tauOfArr {n : ℕ} (edges : List (Fin n × Fin n)) (t : ℕ) (ht : 0 < t)
    (f_tau : Fin edges.length → Fin t) (e : Sym2 (Fin n)) : Fin t :=
  match (List.finRange edges.length).find? (fun k => decide (symEdgeAt edges k = e)) with
  | some k => f_tau k
  | none => ⟨0, ht⟩

@[simp]
theorem tauOfArr_symEdgeAt {n : ℕ} {G : SimpleGraph (Fin n)} {edges : List (Fin n × Fin n)}
    (hedges : IsSimpleEdgeList G edges) (t : ℕ) (ht : 0 < t)
    (f_tau : Fin edges.length → Fin t) (k : Fin edges.length) :
    tauOfArr edges t ht f_tau (symEdgeAt edges k) = f_tau k := by
  unfold tauOfArr
  have hmem : k ∈ List.finRange edges.length := List.mem_finRange k
  have hpred : decide (symEdgeAt edges k = symEdgeAt edges k) = true := decide_eq_true rfl
  generalize hj : List.find? (fun x => decide (symEdgeAt edges x = symEdgeAt edges k))
    (List.finRange edges.length) = res
  cases res with
  | none =>
    exfalso
    exact (List.find?_eq_none.mp hj) k hmem hpred
  | some j =>
    have hj_pred := List.find?_some hj
    have hj_eq : symEdgeAt edges j = symEdgeAt edges k := of_decide_eq_true hj_pred
    have hjk : j = k := symEdgeAt_injective hedges hj_eq
    rw [hjk]

/-! ### Section 2: Array State Predicates, Output Decoder, and Initialization (`initAlg33Prog`) -/

/-- Arrays `a_eu` and `a_ev` store the endpoints `(u_k, v_k)` of `edges`. -/
def IsEndpointArrs {n : ℕ} (edges : List (Fin n × Fin n)) (a_eu a_ev : Arr) (s : State) : Prop :=
  ∃ (heu : (s.arrs a_eu).length = edges.length) (hev : (s.arrs a_ev).length = edges.length),
    ∀ k : Fin edges.length,
      (s.arrs a_eu)[k.1]'(by rw [heu]; exact k.2) = (edges[k.1]'k.2).1.1 ∧
      (s.arrs a_ev)[k.1]'(by rw [hev]; exact k.2) = (edges[k.1]'k.2).2.1

theorem IsEndpointArrs.of_arrs_eq {n : ℕ} {edges : List (Fin n × Fin n)} {a_eu a_ev : Arr}
    {s s' : State} (h : IsEndpointArrs edges a_eu a_ev s)
    (heu : s'.arrs a_eu = s.arrs a_eu) (hev : s'.arrs a_ev = s.arrs a_ev) :
    IsEndpointArrs edges a_eu a_ev s' := by
  rcases h with ⟨h1, h2, hall⟩
  exact ⟨by rw [heu, h1], by rw [hev, h2], fun k => by simp only [heu, hev]; exact hall k⟩

/-- Array `a_tau` stores the leaf index `(f_tau k).1 < t` for each `k : Fin m₂`. -/
def IsTauArr {m₂ t : ℕ} (f_tau : Fin m₂ → Fin t) (a_tau : Arr) (s : State) : Prop :=
  ∃ (hlen : (s.arrs a_tau).length = m₂),
    ∀ k : Fin m₂, (s.arrs a_tau)[k.1]'(by rw [hlen]; exact k.2) = (f_tau k).1

theorem IsTauArr.of_arr_eq {m₂ t : ℕ} {f_tau : Fin m₂ → Fin t} {a_tau : Arr}
    {s s' : State} (h : IsTauArr f_tau a_tau s) (heq : s'.arrs a_tau = s.arrs a_tau) :
    IsTauArr f_tau a_tau s' := by
  rcases h with ⟨hlen, hall⟩
  exact ⟨by rw [heq, hlen], fun k => by simp only [heq]; exact hall k⟩

/-- Array `a_parent` of length `2 * m₂` stores the parent pointers `p z < z` for `0 < z < t`. -/
def IsParentArr (m₂ t : ℕ) (p : ℕ → ℕ) (a_parent : Arr) (s : State) : Prop :=
  ∃ (hlen : (s.arrs a_parent).length = 2 * m₂) (ht_le : t ≤ 2 * m₂),
    (∀ z (hz : z < t), (s.arrs a_parent)[z]'(by omega) = p z) ∧
    (∀ z, 0 < z → z < t → p z < z)

theorem IsParentArr.of_arr_eq {m₂ t : ℕ} {p : ℕ → ℕ} {a_parent : Arr}
    {s s' : State} (h : IsParentArr m₂ t p a_parent s) (heq : s'.arrs a_parent = s.arrs a_parent) :
    IsParentArr m₂ t p a_parent s' := by
  rcases h with ⟨hlen, hle, hall, hp⟩
  exact ⟨by rw [heq, hlen], hle, fun z hz => by simp only [heq]; exact hall z hz, hp⟩

/-- Initial leaf assignment `f_tau` on `Fin m₂` mapping index `0` to `0` and all `k ≥ 1` to `1`. -/
def initFTau (m₂ : ℕ) (k : Fin m₂) : Fin 2 :=
  if k.1 = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩

theorem isPartialBranchDecomp_init_edges {n : ℕ} {ω : ℕ} (hω : 2 ≤ ω)
    {H₂ : SimpleGraph (Fin n)}
    {edges₂ : List (Fin n × Fin n)} (hedges₂ : IsSimpleEdgeList H₂ edges₂)
    (hm₂ : 2 ≤ edges₂.length) :
    IsPartialBranchDecomp ω (graphOfAlive edges₂ hedges₂.1 Finset.univ)
      (parentTree 2 (fun _ => 0)) (tauOfArr edges₂ 2 (by decide) (initFTau edges₂.length)) := by
  let k₀ : Fin edges₂.length := ⟨0, by omega⟩
  let k₁ : Fin edges₂.length := ⟨1, by omega⟩
  have hk₀_mem : symEdgeAt edges₂ k₀ ∈ (graphOfAlive edges₂ hedges₂.1 Finset.univ).edgeFinset := by
    rw [mem_edgeFinset_graphOfAlive_iff hedges₂]
    exact ⟨k₀, Finset.mem_univ k₀, rfl⟩
  have hk₁_mem : symEdgeAt edges₂ k₁ ∈ (graphOfAlive edges₂ hedges₂.1 Finset.univ).edgeFinset := by
    rw [mem_edgeFinset_graphOfAlive_iff hedges₂]
    exact ⟨k₁, Finset.mem_univ k₁, rfl⟩
  have hne01 : symEdgeAt edges₂ k₁ ≠ symEdgeAt edges₂ k₀ := by
    intro heq
    have hval : (1 : ℕ) = 0 := congrArg Fin.val (symEdgeAt_injective hedges₂ heq)
    omega
  apply isPartialBranchDecomp_init hω (graphOfAlive edges₂ hedges₂.1 Finset.univ)
    hk₀_mem hk₁_mem hne01 (tauOfArr edges₂ 2 (by decide) (initFTau edges₂.length))
  · rw [tauOfArr_symEdgeAt hedges₂]
    rfl
  · intro e he hne
    rw [mem_edgeFinset_graphOfAlive_iff hedges₂] at he
    rcases he with ⟨k, _, rfl⟩
    rw [tauOfArr_symEdgeAt hedges₂]
    have hk_ne0 : k.1 ≠ 0 := by
      intro h0
      apply hne
      congr 1
      exact Fin.ext h0
    simp [initFTau, hk_ne0]

/-- Step (6) certificate invariant maintained across iterations of Algorithm (3.3). -/
def Step6CertInv (ω : ℕ) {n : ℕ} (H₁ : SimpleGraph (Fin n)) [DecidableRel H₁.Adj]
    (edges₂ : List (Fin n × Fin n))
    (hloop₂ : ∀ k (hk : k < edges₂.length), (edges₂[k]).1 ≠ (edges₂[k]).2)
    (aliveSet lastAliveSet : Finset (Fin edges₂.length))
    (Z_step6 : Finset (Fin n)) (step6_flag last_g : ℕ) : Prop :=
  (step6_flag = 0 ∧ aliveSet = Finset.univ ∧ last_g = 0) ∨
  (step6_flag = 1 ∧
   ∃ (hg : last_g < edges₂.length),
     let g_idx : Fin edges₂.length := ⟨last_g, hg⟩
     let G_step6 := graphOfAlive edges₂ hloop₂ lastAliveSet
     let g := symEdgeAt edges₂ g_idx
     G_step6 ≤ H₁ ∧
     g ∈ G_step6.edgeFinset ∧
     Z_step6.card = 3 * ω ∧
     aliveSet = lastAliveSet.erase g_idx ∧
     (∀ sep : GraphSeparation G_step6, sep.order ≤ ω → ¬ sep.IsBalancedQ Z_step6))

/-- Body of the initialization loop over `k < m₂`: reads `(u_k, v_k)` from `inArr` into `r_12, r_13`
and writes `a_eu[k] := u_k`, `a_ev[k] := v_k`, `a_alive[k] := 1`, `a_tau[k] := 1`. -/
def initEdgesBody : Cmd :=
  .seq (readEdgeEndpoints 11 12 13 14)
    (.seq (.write 2 (.reg 11) (.reg 12))
      (.seq (.write 3 (.reg 11) (.reg 13))
        (.seq (.write 4 (.reg 11) (.const 1))
          (.write 5 (.reg 11) (.const 1)))))

/-- Preamble register setup for `initAlg33Prog`:
reads `r_0 := n`, `r_1 := m₁`, computes `r_14 := maxEdgesH2 ω n`, sets `r_2 := min m₁ r_14`,
`r_3 := 2 * m₂`, `r_4 := 2`, `r_5 := 0`, `r_6 := 0`. -/
def initAlg33RegsCmd (ω : ℕ) : Cmd :=
  .seq (.assign 0 (.read inArr (.const 0)))
    (.seq (.assign 1 (.read inArr (.const 1)))
      (.seq (.assign 14 (.op .add
          (.op .div (.op .mul (.const (3 * ω - 2)) (.reg 0)) (.const 2)) (.const 1)))
        (.seq (.ite (.op .lt (.reg 1) (.reg 14))
            (.assign 2 (.reg 1))
            (.assign 2 (.reg 14)))
          (.seq (.assign 3 (.op .mul (.const 2) (.reg 2)))
            (.seq (.assign 4 (.const 2))
              (.seq (.assign 5 (.const 0))
                (.assign 6 (.const 0))))))))

/-- Preamble array allocations for `initAlg33Prog`:
allocates `2..8` and initializes loop counter `r_11 := 0`. -/
def initAlg33AllocsCmd : Cmd :=
  .seq (.alloc 2 (.reg 2))
    (.seq (.alloc 3 (.reg 2))
      (.seq (.alloc 4 (.reg 2))
        (.seq (.alloc 5 (.reg 2))
          (.seq (.alloc 6 (.reg 3))
            (.seq (.alloc 7 (.reg 2))
              (.seq (.alloc 8 (.reg 0))
                (.assign 11 (.const 0))))))))

/-- Initialization program for Algorithm (3.3):
1. Executes `initAlg33RegsCmd ω` and `initAlg33AllocsCmd`.
2. Loops `r_11` from `0` to `m₂` executing `initEdgesBody`, then sets `a_tau[0] := 0`. -/
def initAlg33Prog (ω : ℕ) : Cmd :=
  .seq (initAlg33RegsCmd ω)
    (.seq initAlg33AllocsCmd
      (.seq (forUp 11 (.reg 2) initEdgesBody)
        (.write 5 (.const 0) (.const 0))))

theorem initEdgesLoop_exec {w n : ℕ} (edges₁ : List (Fin n × Fin n)) (m₂ : ℕ)
    (hm₂_le : m₂ ≤ edges₁.length)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm1_w : 2 + 2 * edges₁.length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = m₂) {s : State}
    (hin : s.arrs inArr = [n, edges₁.length] ++ flatEdges edges₁ ++ [])
    (hr2 : s.regs 2 = m₂)
    (hr11 : s.regs 11 = k)
    (heu_len : (s.arrs 2).length = m₂)
    (hev_len : (s.arrs 3).length = m₂)
    (heu_prev : ∀ j : Fin m₂, j.1 < k →
      (s.arrs 2)[j.1]'(by rw [heu_len]; exact j.2) = ((edges₁.take m₂)[j.1]'(by simp [hm₂_le])).1.1)
    (hev_prev : ∀ j : Fin m₂, j.1 < k →
      (s.arrs 3)[j.1]'(by rw [hev_len]; exact j.2) = ((edges₁.take m₂)[j.1]'(by simp [hm₂_le])).2.1)
    (halive : s.arrs 4 = List.replicate k 1 ++ List.replicate (m₂ - k) 0)
    (htau : s.arrs 5 = List.replicate k 1 ++ List.replicate (m₂ - k) 0) :
    ∃ s' t_steps,
      Exec w (forUp 11 (.reg 2) initEdgesBody) s s' t_steps ∧
      t_steps ≤ 3 + 33 * rem ∧
      IsEndpointArrs (edges₁.take m₂) 2 3 s' ∧
      s'.arrs 4 = List.replicate m₂ 1 ∧
      s'.arrs 5 = List.replicate m₂ 1 ∧
      (∀ a : Arr, a ≠ 2 → a ≠ 3 → a ≠ 4 → a ≠ 5 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 11 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm2_w : m₂ < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = m₂ := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hm2_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, ?_, ?_,
      fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
    · have hlen_take : (edges₁.take k).length = k := List.length_take_of_le hm₂_le
      refine ⟨by rw [heu_len, hlen_take], by rw [hev_len, hlen_take], fun j => ?_⟩
      have hj_lt : j.1 < k := by have := j.2; omega
      exact ⟨heu_prev ⟨j.1, hj_lt⟩ hj_lt, hev_prev ⟨j.1, hj_lt⟩ hj_lt⟩
    · simpa using halive
    · simpa using htau
  | succ rem ih =>
    have hk_lt : k < m₂ := by omega
    have hk_lt1 : k < edges₁.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hk_w, hm2_w, hk_lt, hw]
    -- 1. readEdgeEndpoints 11 12 13 14
    rcases readEdgeEndpoints_exec edges₁ [] 11 12 13 14 k s (by decide) (by decide)
        hw2 hn_w hm1_w hk_lt1 hin hr11 with
      ⟨s₁, t₁, hex₁, ht₁, hr12_1, hr13_1, harr₁, hreg₁⟩
    have hr11_1 : s₁.regs 11 = k := by rw [hreg₁ 11 (by decide) (by decide) (by decide), hr11]
    have hu_w : (edges₁[k]).1.1 < 2 ^ w := by have := (edges₁[k]).1.2; omega
    have hv_w : (edges₁[k]).2.1 < 2 ^ w := by have := (edges₁[k]).2.2; omega
    -- 2. write 2[k] := r_12
    have heu₁ : (s₁.arrs 2).length = m₂ := by rw [harr₁ 2, heu_len]
    let s₂ := s₁.writeArr 2 k (edges₁[k]).1.1
    have hex₂ : Exec w (.write 2 (.reg 11) (.reg 12)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, hr11_1, hk_w])
        (by simp [Expr.eval, checkWord, hr12_1, hu_w]) (by rw [heu₁]; exact hk_lt)
    -- 3. write 3[k] := r_13
    have hev₂ : (s₂.arrs 3).length = m₂ := by simp [s₂, harr₁ 3, hev_len]
    let s₃ := s₂.writeArr 3 k (edges₁[k]).2.1
    have hex₃ : Exec w (.write 3 (.reg 11) (.reg 13)) s₂ s₃ 3 :=
      .write (by simp [s₂, Expr.eval, checkWord, hr11_1, hk_w])
        (by simp [s₂, Expr.eval, checkWord, hr13_1, hv_w]) (by rw [hev₂]; exact hk_lt)
    -- 4. write 4[k] := 1
    have hal₃ : (s₃.arrs 4).length = m₂ := by
      simp [s₃, s₂, harr₁ 4, halive]; omega
    let s₄ := s₃.writeArr 4 k 1
    have hex₄ : Exec w (.write 4 (.reg 11) (.const 1)) s₃ s₄ 3 :=
      .write (by simp [s₃, s₂, Expr.eval, checkWord, hr11_1, hk_w])
        (by simp [Expr.eval, checkWord, hw]) (by rw [hal₃]; exact hk_lt)
    -- 5. write 5[k] := 1
    have htau₄ : (s₄.arrs 5).length = m₂ := by
      simp [s₄, s₃, s₂, harr₁ 5, htau]; omega
    let s₅ := s₄.writeArr 5 k 1
    have hex₅ : Exec w (.write 5 (.reg 11) (.const 1)) s₄ s₅ 3 :=
      .write (by simp [s₄, s₃, s₂, Expr.eval, checkWord, hr11_1, hk_w])
        (by simp [Expr.eval, checkWord, hw]) (by rw [htau₄]; exact hk_lt)
    -- 6. r_11 := k + 1
    let s₆ := s₅.setReg 11 (k + 1)
    have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₅ s₆ 4 :=
      .assign (by
        simp [s₅, s₄, s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11_1, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have hrep_step : (List.replicate k 1 ++ List.replicate (m₂ - k) 0).set k 1 =
        List.replicate (k + 1) 1 ++ List.replicate (m₂ - (k + 1)) 0 := by
      rw [List.set_append_right _ _ (by simp)]
      have hsub0 : k - (List.replicate k 1).length = 0 := by simp
      have hrep : m₂ - k = (m₂ - (k + 1)) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      rw [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]
    have hal₆ : s₆.arrs 4 = List.replicate (k + 1) 1 ++ List.replicate (m₂ - (k + 1)) 0 := by
      simp [s₆, s₅, s₄, s₃, s₂, harr₁ 4, halive, hrep_step]
    have htau₆ : s₆.arrs 5 = List.replicate (k + 1) 1 ++ List.replicate (m₂ - (k + 1)) 0 := by
      simp [s₆, s₅, s₄, s₃, s₂, harr₁ 5, htau, hrep_step]
    have heu_len₆ : (s₆.arrs 2).length = m₂ := by simp [s₆, s₅, s₄, s₃, s₂, heu₁]
    have hev_len₆ : (s₆.arrs 3).length = m₂ := by simp [s₆, s₅, s₄, s₃, hev₂]
    have heu_prev₆ : ∀ j : Fin m₂, j.1 < k + 1 →
        (s₆.arrs 2)[j.1]'(by rw [heu_len₆]; exact j.2) =
          ((edges₁.take m₂)[j.1]'(by simp [hm₂_le])).1.1 := by
      intro j hj
      have h2_eq : s₆.arrs 2 = (s.arrs 2).set k (edges₁[k]).1.1 := by
        simp [s₆, s₅, s₄, s₃, s₂, harr₁ 2]
      by_cases hjk : j.1 = k
      · subst hjk
        simp only [h2_eq, List.getElem_set_self, List.getElem_take]
      · simp only [h2_eq, List.getElem_set_ne (Ne.symm hjk)]
        exact heu_prev j (by omega)
    have hev_prev₆ : ∀ j : Fin m₂, j.1 < k + 1 →
        (s₆.arrs 3)[j.1]'(by rw [hev_len₆]; exact j.2) =
          ((edges₁.take m₂)[j.1]'(by simp [hm₂_le])).2.1 := by
      intro j hj
      have h3_eq : s₆.arrs 3 = (s.arrs 3).set k (edges₁[k]).2.1 := by
        simp [s₆, s₅, s₄, s₃, s₂, harr₁ 3]
      by_cases hjk : j.1 = k
      · subst hjk
        simp only [h3_eq, List.getElem_set_self, List.getElem_take]
      · simp only [h3_eq, List.getElem_set_ne (Ne.symm hjk)]
        exact hev_prev j (by omega)
    have hin₆ : s₆.arrs inArr = [n, edges₁.length] ++ flatEdges edges₁ ++ [] := by
      simp [s₆, s₅, s₄, s₃, s₂, harr₁ inArr, hin]
    have hr2_6 : s₆.regs 2 = m₂ := by
      simp [s₆, s₅, s₄, s₃, s₂, State.setReg, hreg₁ 2 (by decide) (by decide) (by decide), hr2]
    rcases ih (k + 1) (by omega) hin₆ hr2_6 (by simp [s₆]) heu_len₆ hev_len₆
        heu_prev₆ hev_prev₆ hal₆ htau₆ with
      ⟨s₇, t₇, hex₇, ht₇, hend₇, hal₇, htau₇, harr₇, hreg₇⟩
    refine ⟨s₇, 3 + ((t₁ + (3 + (3 + (3 + 3)))) + 4) + t₇,
      .while_true hcond (by omega)
        (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))) hex_inc) hex₇,
      by omega, hend₇, hal₇, htau₇,
      fun a ha2 ha3 ha4 ha5 => by
        rw [harr₇ a ha2 ha3 ha4 ha5]
        simp [s₆, s₅, s₄, s₃, s₂, harr₁ a, ha2, ha3, ha4, ha5],
      fun r hr => by
        have hr11 : r ≠ 11 := ne_of_lt hr
        have hr12 : r ≠ 12 := ne_of_lt (Nat.lt_trans hr (by decide))
        have hr13 : r ≠ 13 := ne_of_lt (Nat.lt_trans hr (by decide))
        have hr14 : r ≠ 14 := ne_of_lt (Nat.lt_trans hr (by decide))
        rw [hreg₇ r hr]
        simp [s₆, s₅, s₄, s₃, s₂, hr11, hreg₁ r hr12 hr13 hr14]⟩

theorem initAlg33Prog_exec {w n ω : ℕ} (hω : 2 ≤ ω)
    (H₁ : SimpleGraph (Fin n)) [DecidableRel H₁.Adj]
    (edges₁ : List (Fin n × Fin n)) (hedges₁ : IsSimpleEdgeList H₁ edges₁)
    (hm₁_ge2 : 2 ≤ edges₁.length) (hn_pos : 1 ≤ n)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm1_w : 2 + 2 * edges₁.length < 2 ^ w)
    (hB_w : (3 * ω - 2) * n + 2 < 2 ^ w)
    {s₀ : State}
    (hs₀ : s₀.arrs inArr = [n, edges₁.length] ++ flatEdges edges₁) :
    let m₂ := min edges₁.length (maxEdgesH2 ω n)
    let edges₂ := edges₁.take m₂
    let hloop₂ := take_loopless_of_isSimpleEdgeList hedges₁ m₂
    ∃ s' t_steps,
      Exec w (initAlg33Prog ω) s₀ s' t_steps ∧
      t_steps ≤ 45 * m₂ + n + 60 ∧
      s'.regs 0 = n ∧
      s'.regs 1 = edges₁.length ∧
      s'.regs 2 = m₂ ∧
      s'.regs 3 = 2 * m₂ ∧
      s'.regs 4 = 2 ∧
      s'.regs 5 = 0 ∧
      s'.regs 6 = 0 ∧
      IsEndpointArrs edges₂ 2 3 s' ∧
      IsBitSet (Finset.univ : Finset (Fin edges₂.length)) 4 s' ∧
      IsTauArr (initFTau edges₂.length) 5 s' ∧
      IsParentArr m₂ 2 (fun _ => 0) 6 s' ∧
      IsBitSet (∅ : Finset (Fin edges₂.length)) 7 s' ∧
      IsBitSet (∅ : Finset (Fin n)) 8 s' ∧
      IsPartialBranchDecomp ω
        (graphOfAlive edges₂ hloop₂ Finset.univ)
        (parentTree 2 (fun _ => 0))
        (tauOfArr edges₂ 2 (by decide) (initFTau edges₂.length)) := by
  intro m₂ edges₂ hloop₂
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm₁_w : edges₁.length < 2 ^ w := by omega
  have hB_ge2 : 2 ≤ maxEdgesH2 ω n := two_le_maxEdgesH2 hω hn_pos
  have hm₂_ge2 : 2 ≤ m₂ := Nat.le_min.mpr ⟨hm₁_ge2, hB_ge2⟩
  have hm₂_le1 : m₂ ≤ edges₁.length := Nat.min_le_left _ _
  have hm₂_leB : m₂ ≤ maxEdgesH2 ω n := Nat.min_le_right _ _
  have hlen_e2 : edges₂.length = m₂ := List.length_take_of_le hm₂_le1
  have h3w_w : 3 * ω - 2 < 2 ^ w := by
    have : (3 * ω - 2) * 1 ≤ (3 * ω - 2) * n := Nat.mul_le_mul_left _ hn_pos
    omega
  have hmul_w : (3 * ω - 2) * n < 2 ^ w := by omega
  have hdiv_w : ((3 * ω - 2) * n) / 2 < 2 ^ w := by omega
  have hadd_w : ((3 * ω - 2) * n) / 2 + 1 < 2 ^ w := by omega
  have hmaxB_w : maxEdgesH2 ω n < 2 ^ w := hadd_w
  have hm₂_w : m₂ < 2 ^ w := by omega
  have h2m₂_w : 2 * m₂ < 2 ^ w := by omega
  have hin₀ : s₀.arrs inArr = [n, edges₁.length] ++ flatEdges edges₁ ++ [] := by simp [hs₀]
  -- 1..5. Preamble register assignments (depth 8, then abstract `s₈`)
  have hpre_regs : ∃ s₈,
      Exec w (.seq (.assign 0 (.read inArr (.const 0)))
        (.seq (.assign 1 (.read inArr (.const 1)))
          (.seq (.assign 14 (.op .add
              (.op .div (.op .mul (.const (3 * ω - 2)) (.reg 0)) (.const 2)) (.const 1)))
            (.seq (.ite (.op .lt (.reg 1) (.reg 14))
                (.assign 2 (.reg 1))
                (.assign 2 (.reg 14)))
              (.seq (.assign 3 (.op .mul (.const 2) (.reg 2)))
                (.seq (.assign 4 (.const 2))
                  (.seq (.assign 5 (.const 0))
                    (.assign 6 (.const 0))))))))) s₀ s₈ 29 ∧
      s₈.regs 0 = n ∧ s₈.regs 1 = edges₁.length ∧ s₈.regs 2 = m₂ ∧
      s₈.regs 3 = 2 * m₂ ∧ s₈.regs 4 = 2 ∧ s₈.regs 5 = 0 ∧ s₈.regs 6 = 0 ∧
      s₈.arrs = s₀.arrs := by
    obtain ⟨h0_len, h0_val⟩ := inArr_getElem_zero edges₁ [] hin₀
    let s₁ := s₀.setReg 0 n
    have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s₀ s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
    obtain ⟨h1_len, h1_val⟩ := inArr_getElem_one edges₁ [] hin₀
    let s₂ := s₁.setReg 1 edges₁.length
    have hex₂ : Exec w (.assign 1 (.read inArr (.const 1))) s₁ s₂ 3 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hw, h1_len, h1_val, hm₁_w])
    let s₃ := s₂.setReg 14 (maxEdgesH2 ω n)
    have hex₃ : Exec w (.assign 14 (.op .add
        (.op .div (.op .mul (.const (3 * ω - 2)) (.reg 0)) (.const 2)) (.const 1))) s₂ s₃ 8 :=
      .assign (by
        simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          h3w_w, hn_w, hmul_w, hw2, hdiv_w, hw, hadd_w, maxEdgesH2])
    let s₄ := s₃.setReg 2 m₂
    have hex₄ : Exec w (.ite (.op .lt (.reg 1) (.reg 14))
        (.assign 2 (.reg 1)) (.assign 2 (.reg 14))) s₃ s₄ 5 := by
      by_cases hlt : edges₁.length < maxEdgesH2 ω n
      · have hm₂_eq : m₂ = edges₁.length := Nat.min_eq_left (by omega)
        have hcond : (Expr.op .lt (.reg 1) (.reg 14)).eval w s₃ = some 1 := by
          simp [s₃, s₂, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hm₁_w, hmaxB_w, hlt, hw]
        have hex_br : Exec w (.assign 2 (.reg 1)) s₃ s₄ 2 := by
          rw [show s₄ = s₃.setReg 2 edges₁.length by rw [← hm₂_eq]]
          exact .assign (by simp [s₃, s₂, State.setReg, Expr.eval, checkWord, hm₁_w])
        exact .ite_true hcond (by omega) hex_br
      · have hm₂_eq : m₂ = maxEdgesH2 ω n := Nat.min_eq_right (by omega)
        have hcond : (Expr.op .lt (.reg 1) (.reg 14)).eval w s₃ = some 0 := by
          simp [s₃, s₂, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hm₁_w, hmaxB_w, hlt, h0_w]
        have hex_br : Exec w (.assign 2 (.reg 14)) s₃ s₄ 2 := by
          rw [show s₄ = s₃.setReg 2 (maxEdgesH2 ω n) by rw [← hm₂_eq]]
          exact .assign (by simp [s₃, State.setReg, Expr.eval, checkWord, hmaxB_w])
        exact .ite_false hcond hex_br
    let s₅ := s₄.setReg 3 (2 * m₂)
    have hex₅ : Exec w (.assign 3 (.op .mul (.const 2) (.reg 2))) s₄ s₅ 4 :=
      .assign (by simp [s₄, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hm₂_w, h2m₂_w])
    let s₆ := s₅.setReg 4 2
    have hex₆ : Exec w (.assign 4 (.const 2)) s₅ s₆ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw2])
    let s₇ := s₆.setReg 5 0
    have hex₇ : Exec w (.assign 5 (.const 0)) s₆ s₇ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    let s₈ := s₇.setReg 6 0
    have hex₈ : Exec w (.assign 6 (.const 0)) s₇ s₈ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    refine ⟨s₈, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
      by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁],
      by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂],
      by simp [s₈, s₇, s₆, s₅, s₄],
      by simp [s₈, s₇, s₆, s₅],
      by simp [s₈, s₇, s₆],
      by simp [s₈, s₇],
      by simp [s₈],
      by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg]⟩
  rcases hpre_regs with ⟨s₈, hex₁_₈, hr0_8, hr1_8, hr2_8, hr3_8, hr4_8, hr5_8, hr6_8, harr_8⟩
  -- 6. Allocations for 2, 3, 4, 5, 6, 7, 8 and r_11 := 0 (abstract `s₁₆`)
  have hpre_allocs : ∃ s₁₆,
      Exec w (.seq (.alloc 2 (.reg 2))
        (.seq (.alloc 3 (.reg 2))
          (.seq (.alloc 4 (.reg 2))
            (.seq (.alloc 5 (.reg 2))
              (.seq (.alloc 6 (.reg 3))
                (.seq (.alloc 7 (.reg 2))
                  (.seq (.alloc 8 (.reg 0))
                    (.assign 11 (.const 0))))))))) s₈ s₁₆ (9 + 7 * m₂ + n) ∧
      (∀ r : Reg, r ≠ 11 → s₁₆.regs r = s₈.regs r) ∧
      s₁₆.regs 11 = 0 ∧
      s₁₆.arrs inArr = s₀.arrs inArr ∧
      s₁₆.arrs 2 = List.replicate m₂ 0 ∧
      s₁₆.arrs 3 = List.replicate m₂ 0 ∧
      s₁₆.arrs 4 = List.replicate m₂ 0 ∧
      s₁₆.arrs 5 = List.replicate m₂ 0 ∧
      s₁₆.arrs 6 = List.replicate (2 * m₂) 0 ∧
      s₁₆.arrs 7 = List.replicate m₂ 0 ∧
      s₁₆.arrs 8 = List.replicate n 0 := by
    let s₉ := s₈.setArr 2 (List.replicate m₂ 0)
    have hex₉ : Exec w (.alloc 2 (.reg 2)) s₈ s₉ (1 + m₂) :=
      .alloc (by simp [Expr.eval, checkWord, hr2_8, hm₂_w])
    let s₁₀ := s₉.setArr 3 (List.replicate m₂ 0)
    have hex₁₀ : Exec w (.alloc 3 (.reg 2)) s₉ s₁₀ (1 + m₂) :=
      .alloc (by simp [s₉, Expr.eval, checkWord, hr2_8, hm₂_w])
    let s₁₁ := s₁₀.setArr 4 (List.replicate m₂ 0)
    have hex₁₁ : Exec w (.alloc 4 (.reg 2)) s₁₀ s₁₁ (1 + m₂) :=
      .alloc (by simp [s₁₀, s₉, Expr.eval, checkWord, hr2_8, hm₂_w])
    let s₁₂ := s₁₁.setArr 5 (List.replicate m₂ 0)
    have hex₁₂ : Exec w (.alloc 5 (.reg 2)) s₁₁ s₁₂ (1 + m₂) :=
      .alloc (by simp [s₁₁, s₁₀, s₉, Expr.eval, checkWord, hr2_8, hm₂_w])
    let s₁₃ := s₁₂.setArr 6 (List.replicate (2 * m₂) 0)
    have hex₁₃ : Exec w (.alloc 6 (.reg 3)) s₁₂ s₁₃ (1 + 2 * m₂) :=
      .alloc (by simp [s₁₂, s₁₁, s₁₀, s₉, Expr.eval, checkWord, hr3_8, h2m₂_w])
    let s₁₄ := s₁₃.setArr 7 (List.replicate m₂ 0)
    have hex₁₄ : Exec w (.alloc 7 (.reg 2)) s₁₃ s₁₄ (1 + m₂) :=
      .alloc (by simp [s₁₃, s₁₂, s₁₁, s₁₀, s₉, Expr.eval, checkWord, hr2_8, hm₂_w])
    let s₁₅ := s₁₄.setArr 8 (List.replicate n 0)
    have hex₁₅ : Exec w (.alloc 8 (.reg 0)) s₁₄ s₁₅ (1 + n) :=
      .alloc (by simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, Expr.eval, checkWord, hr0_8, hn_w])
    let s₁₆ := s₁₅.setReg 11 0
    have hex₁₆ : Exec w (.assign 11 (.const 0)) s₁₅ s₁₆ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    have ht_eq : (1 + m₂) + ((1 + m₂) + ((1 + m₂) + ((1 + m₂) + ((1 + 2 * m₂) + ((1 + m₂) + ((1 + n) + 2)))))) =
        9 + 7 * m₂ + n := by omega
    refine ⟨s₁₆, ht_eq ▸ .seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ (.seq hex₁₃ (.seq hex₁₄ (.seq hex₁₅ hex₁₆)))))),
      fun r hr => by simp [s₁₆, s₁₅, s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, hr],
      by simp [s₁₆],
      by simp [s₁₆, s₁₅, s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, harr_8],
      by simp [s₁₆, s₁₅, s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉],
      by simp [s₁₆, s₁₅, s₁₄, s₁₃, s₁₂, s₁₁, s₁₀],
      by simp [s₁₆, s₁₅, s₁₄, s₁₃, s₁₂, s₁₁],
      by simp [s₁₆, s₁₅, s₁₄, s₁₃, s₁₂],
      by simp [s₁₆, s₁₅, s₁₄, s₁₃],
      by simp [s₁₆, s₁₅, s₁₄],
      by simp [s₁₆, s₁₅]⟩
  rcases hpre_allocs with
    ⟨s₁₆, hex₉_₁₆, hreg_16, hr11_16, hin_16, h2_16, h3_16, h4_16, h5_16, h6_16, h7_16, h8_16⟩
  -- 7. Loop `forUp 11 (.reg 2) initEdgesBody`
  rcases initEdgesLoop_exec edges₁ m₂ hm₂_le1 hw2 hn_w hm1_w m₂ 0 (by omega)
      (s := s₁₆)
      (by rw [hin_16]; exact hin₀)
      (by rw [hreg_16 2 (by decide)]; exact hr2_8)
      hr11_16
      (by simp [h2_16])
      (by simp [h3_16])
      (fun _ hj => absurd hj (by omega))
      (fun _ hj => absurd hj (by omega))
      (by simp [h4_16])
      (by simp [h5_16]) with
    ⟨s₁₇, t₁₇, hex₁₇, ht₁₇, hend₁₇, hal₁₇, htau₁₇, harr₁₇, hreg₁₇⟩
  -- 8. write 5[0] := 0
  have h5_len : 0 < (s₁₇.arrs 5).length := by rw [htau₁₇, List.length_replicate]; omega
  let s₁₈ := s₁₇.writeArr 5 0 0
  have hex₁₈ : Exec w (.write 5 (.const 0) (.const 0)) s₁₇ s₁₈ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w]) (by simp [Expr.eval, checkWord, h0_w]) h5_len
  have hr0_18 : s₁₈.regs 0 = n := by
    simp [s₁₈, hreg₁₇ 0 (by decide), hreg_16 0 (by decide), hr0_8]
  have hr1_18 : s₁₈.regs 1 = edges₁.length := by
    simp [s₁₈, hreg₁₇ 1 (by decide), hreg_16 1 (by decide), hr1_8]
  have hr2_18 : s₁₈.regs 2 = m₂ := by
    simp [s₁₈, hreg₁₇ 2 (by decide), hreg_16 2 (by decide), hr2_8]
  have hr3_18 : s₁₈.regs 3 = 2 * m₂ := by
    simp [s₁₈, hreg₁₇ 3 (by decide), hreg_16 3 (by decide), hr3_8]
  have hr4_18 : s₁₈.regs 4 = 2 := by
    simp [s₁₈, hreg₁₇ 4 (by decide), hreg_16 4 (by decide), hr4_8]
  have hr5_18 : s₁₈.regs 5 = 0 := by
    simp [s₁₈, hreg₁₇ 5 (by decide), hreg_16 5 (by decide), hr5_8]
  have hr6_18 : s₁₈.regs 6 = 0 := by
    simp [s₁₈, hreg₁₇ 6 (by decide), hreg_16 6 (by decide), hr6_8]
  have hend₁₈ : IsEndpointArrs edges₂ 2 3 s₁₈ :=
    hend₁₇.of_arrs_eq (by simp [s₁₈]) (by simp [s₁₈])
  have hal₁₈ : IsBitSet (Finset.univ : Finset (Fin edges₂.length)) 4 s₁₈ := by
    apply IsBitSet.univ_of_replicate
    simp [s₁₈, hal₁₇, hlen_e2]
  have htau₁₈ : IsTauArr (initFTau edges₂.length) 5 s₁₈ := by
    refine ⟨by simp [s₁₈, htau₁₇, hlen_e2], fun k => ?_⟩
    simp only [s₁₈, State.writeArr_arrs_self, htau₁₇, initFTau]
    by_cases hk0 : k.1 = 0
    · simp [hk0]
    · rw [List.getElem_set_ne (Ne.symm hk0)]
      simp [hk0]
  have hpar₁₈ : IsParentArr m₂ 2 (fun _ => 0) 6 s₁₈ := by
    have h6 : s₁₈.arrs 6 = List.replicate (2 * m₂) 0 := by
      simp [s₁₈, harr₁₇ 6 (by decide) (by decide) (by decide) (by decide), h6_16]
    refine ⟨by simp [h6], by omega, fun z _ => by simp [h6], fun z hz _ => hz⟩
  have hlast_al₁₈ : IsBitSet (∅ : Finset (Fin edges₂.length)) 7 s₁₈ := by
    apply IsBitSet.empty_of_replicate
    simp [s₁₈, harr₁₇ 7 (by decide) (by decide) (by decide) (by decide), h7_16, hlen_e2]
  have hlast_Z₁₈ : IsBitSet (∅ : Finset (Fin n)) 8 s₁₈ := by
    apply IsBitSet.empty_of_replicate
    simp [s₁₈, harr₁₇ 8 (by decide) (by decide) (by decide) (by decide), h8_16]
  have hedges₂ : IsSimpleEdgeList (graphOfEdgeList edges₂ hloop₂) edges₂ :=
    isSimpleEdgeList_take hedges₁ m₂
  have hpart₁₈ := isPartialBranchDecomp_init_edges hω hedges₂ (by omega)
  refine ⟨s₁₈, 29 + ((9 + 7 * m₂ + n) + (t₁₇ + 3)),
    .seq hex₁_₈ (.seq hex₉_₁₆ (.seq hex₁₇ hex₁₈)),
    by omega, hr0_18, hr1_18, hr2_18, hr3_18, hr4_18, hr5_18, hr6_18,
    hend₁₈, hal₁₈, htau₁₈, hpar₁₈, hlast_al₁₈, hlast_Z₁₈, hpart₁₈⟩

/-! ### Section 3: Step (1) and Step (2), Leaf Search (`findDupLeafProg`), Cut Set `Z`
(`computeZProg`), and Candidate Edge (`selectCandEdgeProg`) -/

/-- Set of leaves of `Fin t` assigned to active edges with index `< k`. -/
def seenLeavesUpTo {m₂ t : ℕ} (aliveSet : Finset (Fin m₂)) (f_tau : Fin m₂ → Fin t) :
    ℕ → Finset (Fin t)
  | 0 => ∅
  | k + 1 =>
    if hk : k < m₂ then
      if (⟨k, hk⟩ : Fin m₂) ∈ aliveSet then
        insert (f_tau ⟨k, hk⟩) (seenLeavesUpTo aliveSet f_tau k)
      else
        seenLeavesUpTo aliveSet f_tau k
    else
      seenLeavesUpTo aliveSet f_tau k

theorem mem_seenLeavesUpTo {m₂ t : ℕ} (aliveSet : Finset (Fin m₂)) (f_tau : Fin m₂ → Fin t)
    (k : ℕ) (w : Fin t) :
    w ∈ seenLeavesUpTo aliveSet f_tau k ↔
      ∃ j : Fin m₂, j.1 < k ∧ j ∈ aliveSet ∧ f_tau j = w := by
  induction k with
  | zero => simp [seenLeavesUpTo]
  | succ k ih =>
    simp only [seenLeavesUpTo]
    split_ifs with hk hmem
    · simp only [Finset.mem_insert, ih]
      constructor
      · rintro (rfl | ⟨j, hj, hjal, hjw⟩)
        · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hmem, rfl⟩
        · exact ⟨j, by omega, hjal, hjw⟩
      · rintro ⟨j, hj, hjal, hjw⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
        · exact Or.inr ⟨j, hlt, hjal, hjw⟩
        · left
          have hjk : j = ⟨k, hk⟩ := Fin.ext heq
          subst hjk
          exact hjw.symm
    · rw [ih]
      constructor
      · rintro ⟨j, hj, hjal, hjw⟩
        exact ⟨j, by omega, hjal, hjw⟩
      · rintro ⟨j, hj, hjal, hjw⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
        · exact ⟨j, hlt, hjal, hjw⟩
        · exfalso
          have hjk : j = ⟨k, hk⟩ := Fin.ext heq
          subst hjk
          exact hmem hjal
    · rw [ih]
      constructor <;> rintro ⟨j, hj, hjal, hjw⟩
      · exact ⟨j, by omega, hjal, hjw⟩
      · exact ⟨j, by omega, hjal, hjw⟩

/-- Body of `findDupLeafProg`: if `a_alive[r_11] != 0`, let `w = a_tau[r_11]`; if `a_seen[w] != 0`,
record `r_7 := w`, else mark `a_seen[w] := 1`. -/
def findDupLeafBody : Cmd :=
  .seq (.assign 14 (.read 4 (.reg 11)))
    (.ite (.reg 14)
      (.seq (.assign 15 (.read 5 (.reg 11)))
        (.seq (.assign 16 (.read 9 (.reg 15)))
          (.ite (.reg 16)
            (.assign 7 (.reg 15))
            (.write 9 (.reg 15) (.const 1)))))
      .skip)

/-- Step (1)–(2) leaf search: allocates `a_seen = 9` of size `t` (`r_4`), sets `r_7 := t`, and
scans `r_11` from `0` to `m₂` (`r_2`). -/
def findDupLeafProg : Cmd :=
  .seq (.alloc 9 (.reg 4))
    (.seq (.assign 7 (.reg 4))
      (.seq (.assign 11 (.const 0))
        (forUp 11 (.reg 2) findDupLeafBody)))

theorem findDupLeafLoop_exec {w m₂ t : ℕ} (aliveSet : Finset (Fin m₂)) (f_tau : Fin m₂ → Fin t)
    (hw : 1 < 2 ^ w) (hm2_w : m₂ < 2 ^ w) (ht_w : t < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = m₂) {s : State}
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hseen : IsBitSet (seenLeavesUpTo aliveSet f_tau k) 9 s)
    (hr2 : s.regs 2 = m₂)
    (hr4 : s.regs 4 = t)
    (hr11 : s.regs 11 = k)
    (hr7_inv :
      (s.regs 7 = t ∧
        ∀ i j : Fin m₂, i.1 < j.1 → j.1 < k → i ∈ aliveSet → j ∈ aliveSet → f_tau i ≠ f_tau j) ∨
      (∃ (v : Fin t) (i j : Fin m₂),
        s.regs 7 = v.1 ∧ i.1 < j.1 ∧ j.1 < k ∧ i ∈ aliveSet ∧ j ∈ aliveSet ∧
        f_tau i = v ∧ f_tau j = v)) :
    ∃ s' t_steps,
      Exec w (forUp 11 (.reg 2) findDupLeafBody) s s' t_steps ∧
      t_steps ≤ 3 + 22 * rem ∧
      ((s'.regs 7 = t ∧
        ∀ i j : Fin m₂, i.1 < j.1 → i ∈ aliveSet → j ∈ aliveSet → f_tau i ≠ f_tau j) ∨
       (∃ (v : Fin t) (i j : Fin m₂),
        s'.regs 7 = v.1 ∧ i.1 < j.1 ∧ i ∈ aliveSet ∧ j ∈ aliveSet ∧
        f_tau i = v ∧ f_tau j = v)) ∧
      (∀ a : Arr, a ≠ 9 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 11 → r ≠ 14 → r ≠ 15 → r ≠ 16 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = m₂ := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hm2_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
    rcases hr7_inv with ⟨hr7, hinj⟩ | ⟨v, i, j, hr7, hij, _, hi, hj, hfi, hfj⟩
    · exact Or.inl ⟨hr7, fun i j hij hi hj => hinj i j hij j.2 hi hj⟩
    · exact Or.inr ⟨v, i, j, hr7, hij, hi, hj, hfi, hfj⟩
  | succ rem ih =>
    have hk_lt : k < m₂ := by omega
    have hk_w : k < 2 ^ w := by omega
    let jk : Fin m₂ := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hk_w, hm2_w, hk_lt, hw]
    have hal_len : k < (s.arrs 4).length := by rw [hal.1]; exact hk_lt
    let al_k := (s.arrs 4)[k]'hal_len
    have hal_k_le : al_k ≤ 1 := hal.2.1 jk
    have hal_k_w : al_k < 2 ^ w := by omega
    let s₁ := s.setReg 14 al_k
    have hex_rd4 : Exec w (.assign 14 (.read 4 (.reg 11))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr11, hk_w, hal_len, al_k, hal_k_w])
    by_cases hmem_k : jk ∈ aliveSet
    · have hal_k_ne0 : al_k ≠ 0 := (hal.2.2 jk).mpr hmem_k
      have hcond14 : (Expr.reg 14).eval w s₁ = some al_k := by
        simp [s₁, Expr.eval, checkWord, hal_k_w]
      have htau_len : k < (s.arrs 5).length := by rw [htau.1]; exact hk_lt
      have htau_k : (s.arrs 5)[k]'htau_len = (f_tau jk).1 := htau.2 jk
      let wk := f_tau jk
      have hwk_w : wk.1 < 2 ^ w := by have := wk.2; omega
      let s₂ := s₁.setReg 15 wk.1
      have hex_rd5 : Exec w (.assign 15 (.read 5 (.reg 11))) s₁ s₂ 3 :=
        .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w, htau_len, htau_k, wk, hwk_w])
      have hseen_len : wk.1 < (s.arrs 9).length := by rw [hseen.1]; exact wk.2
      let sn_w := (s.arrs 9)[wk.1]'hseen_len
      have hsn_le : sn_w ≤ 1 := hseen.2.1 wk
      have hsn_w : sn_w < 2 ^ w := by omega
      let s₃ := s₂.setReg 16 sn_w
      have hex_rd9 : Exec w (.assign 16 (.read 9 (.reg 15))) s₂ s₃ 3 :=
        .assign (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hwk_w, hseen_len, sn_w, hsn_w])
      by_cases hwk_seen : wk ∈ seenLeavesUpTo aliveSet f_tau k
      · have hsn_ne0 : sn_w ≠ 0 := (hseen.2.2 wk).mpr hwk_seen
        have hcond16 : (Expr.reg 16).eval w s₃ = some sn_w := by
          simp [s₃, Expr.eval, checkWord, hsn_w]
        let s₄ := s₃.setReg 7 wk.1
        have hex_set7 : Exec w (.assign 7 (.reg 15)) s₃ s₄ 2 :=
          .assign (by simp [s₃, s₂, State.setReg, Expr.eval, checkWord, hwk_w])
        have hex_ite16 : Exec w (.ite (.reg 16) (.assign 7 (.reg 15)) (.write 9 (.reg 15) (.const 1)))
            s₃ s₄ 3 := .ite_true hcond16 hsn_ne0 hex_set7
        have hex_ite14 : Exec w (findDupLeafBody) s s₄ 13 :=
          .seq hex_rd4 (.ite_true hcond14 hal_k_ne0 (.seq hex_rd5 (.seq hex_rd9 hex_ite16)))
        let s₅ := s₄.setReg 11 (k + 1)
        have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₄ s₅ 4 :=
          .assign (by
            simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
        have hseen_step : seenLeavesUpTo aliveSet f_tau (k + 1) = seenLeavesUpTo aliveSet f_tau k := by
          simp only [seenLeavesUpTo, hk_lt, ↓reduceDIte,
            show (⟨k, hk_lt⟩ : Fin m₂) ∈ aliveSet from hmem_k, ↓reduceIte]
          exact Finset.insert_eq_of_mem hwk_seen
        have hseen₅ : IsBitSet (seenLeavesUpTo aliveSet f_tau (k + 1)) 9 s₅ := by
          rw [hseen_step]
          exact hseen.of_arr_eq rfl
        rcases (mem_seenLeavesUpTo aliveSet f_tau k wk).mp hwk_seen with ⟨i₀, hi₀_lt, hi₀_al, hi₀_eq⟩
        have hr7_inv₅ :
            (s₅.regs 7 = t ∧
              ∀ i j : Fin m₂, i.1 < j.1 → j.1 < k + 1 → i ∈ aliveSet → j ∈ aliveSet → f_tau i ≠ f_tau j) ∨
            (∃ (v : Fin t) (i j : Fin m₂),
              s₅.regs 7 = v.1 ∧ i.1 < j.1 ∧ j.1 < k + 1 ∧ i ∈ aliveSet ∧ j ∈ aliveSet ∧
              f_tau i = v ∧ f_tau j = v) :=
          Or.inr ⟨wk, i₀, jk, by simp [s₅, s₄, State.setReg], hi₀_lt, by simp [jk],
            hi₀_al, hmem_k, hi₀_eq, rfl⟩
        rcases ih (k + 1) (by omega) (s := s₅) (hal.of_arr_eq rfl) (htau.of_arr_eq rfl) hseen₅
            (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, hr2])
            (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, hr4])
            (by simp [s₅]) hr7_inv₅ with
          ⟨s₆, t₆, hex₆, ht₆, hres₆, harr₆, hreg₆⟩
        refine ⟨s₆, 3 + (13 + 4) + t₆,
          .while_true hcond (by omega) (.seq hex_ite14 hex_inc) hex₆,
          by omega, hres₆,
          fun a ha9 => by rw [harr₆ a ha9]; rfl,
          fun r hr7 hr11' hr14 hr15 hr16 => by
            rw [hreg₆ r hr7 hr11' hr14 hr15 hr16]
            simp [s₅, s₄, s₃, s₂, s₁, State.setReg, hr11', hr7, hr16, hr15, hr14]⟩
      · have hsn_eq0 : sn_w = 0 := by
          by_contra hne
          exact hwk_seen ((hseen.2.2 wk).mp hne)
        have hcond16 : (Expr.reg 16).eval w s₃ = some 0 := by
          simp [s₃, Expr.eval, checkWord, hsn_eq0, h0_w]
        let s₄ := s₃.writeArr 9 wk.1 1
        have hex_wr9 : Exec w (.write 9 (.reg 15) (.const 1)) s₃ s₄ 3 :=
          .write (by simp [s₃, s₂, State.setReg, Expr.eval, checkWord, hwk_w])
            (by simp [Expr.eval, checkWord, hw]) (by simp [s₃, s₂, s₁, hseen_len])
        have hex_ite16 : Exec w (.ite (.reg 16) (.assign 7 (.reg 15)) (.write 9 (.reg 15) (.const 1)))
            s₃ s₄ 4 := .ite_false hcond16 hex_wr9
        have hex_ite14 : Exec w (findDupLeafBody) s s₄ 14 :=
          .seq hex_rd4 (.ite_true hcond14 hal_k_ne0 (.seq hex_rd5 (.seq hex_rd9 hex_ite16)))
        let s₅ := s₄.setReg 11 (k + 1)
        have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₄ s₅ 4 :=
          .assign (by
            simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
        have hseen_step : seenLeavesUpTo aliveSet f_tau (k + 1) =
            insert wk (seenLeavesUpTo aliveSet f_tau k) := by
          simp only [seenLeavesUpTo, hk_lt, ↓reduceDIte,
            show (⟨k, hk_lt⟩ : Fin m₂) ∈ aliveSet from hmem_k, ↓reduceIte]
          rfl
        have hseen₅ : IsBitSet (seenLeavesUpTo aliveSet f_tau (k + 1)) 9 s₅ := by
          rw [hseen_step]
          exact (hseen.of_arr_eq (rfl : s₃.arrs 9 = s.arrs 9)).write_one wk
        have hr7_5 : s₅.regs 7 = s.regs 7 := by
          simp [s₅, s₄, s₃, s₂, s₁, State.setReg]
        have hr7_inv₅ :
            (s₅.regs 7 = t ∧
              ∀ i j : Fin m₂, i.1 < j.1 → j.1 < k + 1 → i ∈ aliveSet → j ∈ aliveSet → f_tau i ≠ f_tau j) ∨
            (∃ (v : Fin t) (i j : Fin m₂),
              s₅.regs 7 = v.1 ∧ i.1 < j.1 ∧ j.1 < k + 1 ∧ i ∈ aliveSet ∧ j ∈ aliveSet ∧
              f_tau i = v ∧ f_tau j = v) := by
          rcases hr7_inv with ⟨hr7, hinj⟩ | ⟨v, i, j, hr7, hij, hj_lt, hi, hj, hfi, hfj⟩
          · refine Or.inl ⟨by rw [hr7_5, hr7], fun i j hij hj_lt hi hj => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj_lt with hlt | heq
            · exact hinj i j hij hlt hi hj
            · intro hfeq
              have hjk : j = jk := Fin.ext heq
              subst hjk
              apply hwk_seen
              rw [mem_seenLeavesUpTo]
              exact ⟨i, hij, hi, hfeq⟩
          · exact Or.inr ⟨v, i, j, by rw [hr7_5, hr7], hij, by omega, hi, hj, hfi, hfj⟩
        rcases ih (k + 1) (by omega) (s := s₅)
            (hal.of_arr_eq (by simp [s₅, s₄, s₃, s₂, s₁]))
            (htau.of_arr_eq (by simp [s₅, s₄, s₃, s₂, s₁])) hseen₅
            (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, hr2])
            (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, hr4])
            (by simp [s₅]) hr7_inv₅ with
          ⟨s₆, t₆, hex₆, ht₆, hres₆, harr₆, hreg₆⟩
        refine ⟨s₆, 3 + (14 + 4) + t₆,
          .while_true hcond (by omega) (.seq hex_ite14 hex_inc) hex₆,
          by omega, hres₆,
          fun a ha9 => by rw [harr₆ a ha9]; simp [s₅, s₄, s₃, s₂, s₁, ha9],
          fun r hr7 hr11' hr14 hr15 hr16 => by
            rw [hreg₆ r hr7 hr11' hr14 hr15 hr16]
            simp [s₅, s₄, s₃, s₂, s₁, State.setReg, hr11', hr16, hr15, hr14]⟩
    · have hal_k_eq0 : al_k = 0 := by
        by_contra hne
        exact hmem_k ((hal.2.2 jk).mp hne)
      have hcond14 : (Expr.reg 14).eval w s₁ = some 0 := by
        simp [s₁, Expr.eval, checkWord, hal_k_eq0, h0_w]
      have hex_ite14 : Exec w (findDupLeafBody) s s₁ 5 :=
        .seq hex_rd4 (.ite_false hcond14 (.skip s₁))
      let s₂ := s₁.setReg 11 (k + 1)
      have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₁ s₂ 4 :=
        .assign (by
          simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
      have hseen_step : seenLeavesUpTo aliveSet f_tau (k + 1) = seenLeavesUpTo aliveSet f_tau k := by
        simp only [seenLeavesUpTo, hk_lt, ↓reduceDIte,
          show (⟨k, hk_lt⟩ : Fin m₂) ∉ aliveSet from hmem_k, ↓reduceIte]
      have hseen₂ : IsBitSet (seenLeavesUpTo aliveSet f_tau (k + 1)) 9 s₂ := by
        rw [hseen_step]
        exact hseen.of_arr_eq rfl
      have hr7_inv₂ :
          (s₂.regs 7 = t ∧
            ∀ i j : Fin m₂, i.1 < j.1 → j.1 < k + 1 → i ∈ aliveSet → j ∈ aliveSet → f_tau i ≠ f_tau j) ∨
          (∃ (v : Fin t) (i j : Fin m₂),
            s₂.regs 7 = v.1 ∧ i.1 < j.1 ∧ j.1 < k + 1 ∧ i ∈ aliveSet ∧ j ∈ aliveSet ∧
            f_tau i = v ∧ f_tau j = v) := by
        rcases hr7_inv with ⟨hr7, hinj⟩ | ⟨v, i, j, hr7, hij, hj_lt, hi, hj, hfi, hfj⟩
        · refine Or.inl ⟨by simp [s₂, s₁, State.setReg, hr7], fun i j hij hj_lt hi hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj_lt with hlt | heq
          · exact hinj i j hij hlt hi hj
          · exfalso
            have hjk : j = jk := Fin.ext heq
            subst hjk
            exact hmem_k hj
        · exact Or.inr ⟨v, i, j, by simp [s₂, s₁, State.setReg, hr7], hij, by omega, hi, hj, hfi, hfj⟩
      rcases ih (k + 1) (by omega) (s := s₂) (hal.of_arr_eq rfl) (htau.of_arr_eq rfl) hseen₂
          (by simp [s₂, s₁, State.setReg, hr2])
          (by simp [s₂, s₁, State.setReg, hr4])
          (by simp [s₂]) hr7_inv₂ with
        ⟨s₃, t₃, hex₃, ht₃, hres₃, harr₃, hreg₃⟩
      refine ⟨s₃, 3 + (5 + 4) + t₃,
        .while_true hcond (by omega) (.seq hex_ite14 hex_inc) hex₃,
        by omega, hres₃,
        fun a ha9 => by rw [harr₃ a ha9]; rfl,
        fun r hr7 hr11' hr14 hr15 hr16 => by
          rw [hreg₃ r hr7 hr11' hr14 hr15 hr16]
          simp [s₂, s₁, State.setReg, hr11', hr14]⟩

theorem findDupLeafProg_exec {w m₂ t : ℕ} (aliveSet : Finset (Fin m₂)) (f_tau : Fin m₂ → Fin t)
    (hw : 1 < 2 ^ w) (hm2_w : m₂ < 2 ^ w) (ht_w : t < 2 ^ w)
    {s : State}
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hr2 : s.regs 2 = m₂)
    (hr4 : s.regs 4 = t) :
    ∃ s' t_steps,
      Exec w findDupLeafProg s s' t_steps ∧
      t_steps ≤ 22 * m₂ + t + 10 ∧
      ((s'.regs 7 = t ∧
        ∀ i j : Fin m₂, i.1 < j.1 → i ∈ aliveSet → j ∈ aliveSet → f_tau i ≠ f_tau j) ∨
       (∃ (v : Fin t) (i j : Fin m₂),
        s'.regs 7 = v.1 ∧ i.1 < j.1 ∧ i ∈ aliveSet ∧ j ∈ aliveSet ∧
        f_tau i = v ∧ f_tau j = v)) ∧
      (∀ a : Arr, a ≠ 9 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 11 → r ≠ 14 → r ≠ 15 → r ≠ 16 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 9 (List.replicate t 0)
  have hex₁ : Exec w (.alloc 9 (.reg 4)) s s₁ (1 + t) :=
    .alloc (by simp [Expr.eval, checkWord, hr4, ht_w])
  let s₂ := s₁.setReg 7 t
  have hex₂ : Exec w (.assign 7 (.reg 4)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hr4, ht_w])
  let s₃ := s₂.setReg 11 0
  have hex₃ : Exec w (.assign 11 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hseen₃ : IsBitSet (seenLeavesUpTo aliveSet f_tau 0) 9 s₃ := by
    unfold seenLeavesUpTo
    exact IsBitSet.empty_of_replicate (by simp [s₃, s₂, s₁])
  rcases findDupLeafLoop_exec aliveSet f_tau hw hm2_w ht_w m₂ 0 (by omega)
      (s := s₃)
      (hal.of_arr_eq (by simp [s₃, s₂, s₁]))
      (htau.of_arr_eq (by simp [s₃, s₂, s₁]))
      hseen₃
      (by simp [s₃, s₂, s₁, State.setReg, hr2])
      (by simp [s₃, s₂, s₁, State.setReg, hr4])
      (by simp [s₃])
      (Or.inl ⟨by simp [s₃, s₂, State.setReg], fun _ _ _ hj => absurd hj (by omega)⟩) with
    ⟨s₄, t₄, hex₄, ht₄, hres₄, harr₄, hreg₄⟩
  refine ⟨s₄, (1 + t) + (2 + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hres₄,
    fun a ha9 => by rw [harr₄ a ha9]; simp [s₃, s₂, s₁, ha9],
    fun r hr7 hr11 hr14 hr15 hr16 => by
      rw [hreg₄ r hr7 hr11 hr14 hr15 hr16]
      simp [s₃, s₂, s₁, State.setReg, hr11, hr7]⟩

/-- Vertices of `Fin n` incident to some active edge with index `< k` mapped to `v`. -/
def incRUpTo {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t) (v : Fin t) :
    ℕ → Finset (Fin n)
  | 0 => ∅
  | k + 1 =>
    if hk : k < edges.length then
      if (⟨k, hk⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk⟩ = v then
        insert (edges[k]'hk).2 (insert (edges[k]'hk).1 (incRUpTo edges aliveSet f_tau v k))
      else
        incRUpTo edges aliveSet f_tau v k
    else
      incRUpTo edges aliveSet f_tau v k

/-- Vertices of `Fin n` incident to some active edge with index `< k` mapped to a leaf `≠ v`. -/
def incRprimeUpTo {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t) (v : Fin t) :
    ℕ → Finset (Fin n)
  | 0 => ∅
  | k + 1 =>
    if hk : k < edges.length then
      if (⟨k, hk⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk⟩ ≠ v then
        insert (edges[k]'hk).2 (insert (edges[k]'hk).1 (incRprimeUpTo edges aliveSet f_tau v k))
      else
        incRprimeUpTo edges aliveSet f_tau v k
    else
      incRprimeUpTo edges aliveSet f_tau v k

theorem mem_incRUpTo {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t) (v : Fin t)
    (k : ℕ) (x : Fin n) :
    x ∈ incRUpTo edges aliveSet f_tau v k ↔
      ∃ j : Fin edges.length, j.1 < k ∧ j ∈ aliveSet ∧ f_tau j = v ∧
        (x = (edges[j.1]'j.2).1 ∨ x = (edges[j.1]'j.2).2) := by
  induction k with
  | zero => simp [incRUpTo]
  | succ k ih =>
    simp only [incRUpTo]
    split_ifs with hk hcond
    · simp only [Finset.mem_insert, ih]
      constructor
      · rintro (rfl | rfl | ⟨j, hj, hjal, hjv, hx⟩)
        · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hcond.1, hcond.2, Or.inr rfl⟩
        · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hcond.1, hcond.2, Or.inl rfl⟩
        · exact ⟨j, by omega, hjal, hjv, hx⟩
      · rintro ⟨j, hj, hjal, hjv, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
        · exact Or.inr (Or.inr ⟨j, hlt, hjal, hjv, hx⟩)
        · have hjk : j = ⟨k, hk⟩ := Fin.ext heq
          subst hjk
          rcases hx with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
    · rw [ih]
      constructor
      · rintro ⟨j, hj, hjal, hjv, hx⟩
        exact ⟨j, by omega, hjal, hjv, hx⟩
      · rintro ⟨j, hj, hjal, hjv, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
        · exact ⟨j, hlt, hjal, hjv, hx⟩
        · exfalso
          have hjk : j = ⟨k, hk⟩ := Fin.ext heq
          subst hjk
          exact hcond ⟨hjal, hjv⟩
    · rw [ih]
      constructor <;> rintro ⟨j, hj, hjal, hjv, hx⟩
      · exact ⟨j, by omega, hjal, hjv, hx⟩
      · exact ⟨j, by omega, hjal, hjv, hx⟩

theorem mem_incRprimeUpTo {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t) (v : Fin t)
    (k : ℕ) (x : Fin n) :
    x ∈ incRprimeUpTo edges aliveSet f_tau v k ↔
      ∃ j : Fin edges.length, j.1 < k ∧ j ∈ aliveSet ∧ f_tau j ≠ v ∧
        (x = (edges[j.1]'j.2).1 ∨ x = (edges[j.1]'j.2).2) := by
  induction k with
  | zero => simp [incRprimeUpTo]
  | succ k ih =>
    simp only [incRprimeUpTo]
    split_ifs with hk hcond
    · simp only [Finset.mem_insert, ih]
      constructor
      · rintro (rfl | rfl | ⟨j, hj, hjal, hjv, hx⟩)
        · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hcond.1, hcond.2, Or.inr rfl⟩
        · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hcond.1, hcond.2, Or.inl rfl⟩
        · exact ⟨j, by omega, hjal, hjv, hx⟩
      · rintro ⟨j, hj, hjal, hjv, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
        · exact Or.inr (Or.inr ⟨j, hlt, hjal, hjv, hx⟩)
        · have hjk : j = ⟨k, hk⟩ := Fin.ext heq
          subst hjk
          rcases hx with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
    · rw [ih]
      constructor
      · rintro ⟨j, hj, hjal, hjv, hx⟩
        exact ⟨j, by omega, hjal, hjv, hx⟩
      · rintro ⟨j, hj, hjal, hjv, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
        · exact ⟨j, hlt, hjal, hjv, hx⟩
        · exfalso
          have hjk : j = ⟨k, hk⟩ := Fin.ext heq
          subst hjk
          exact hcond ⟨hjal, hjv⟩
    · rw [ih]
      constructor <;> rintro ⟨j, hj, hjal, hjv, hx⟩
      · exact ⟨j, by omega, hjal, hjv, hx⟩
      · exact ⟨j, by omega, hjal, hjv, hx⟩

theorem incRUpTo_inter_incRprimeUpTo_eq_leafCutVerts {n t : ℕ} (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t) (v : Fin t) :
    incRUpTo edges aliveSet f_tau v edges.length ∩
      incRprimeUpTo edges aliveSet f_tau v edges.length =
      leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v := by
  ext x
  simp only [Finset.mem_inter, mem_incRUpTo, mem_incRprimeUpTo, mem_leafCutVerts,
    mem_edgeFinset_graphOfAlive_iff hedges]
  constructor
  · rintro ⟨⟨j₁, _, hj₁_al, hj₁_v, hx₁⟩, ⟨j₂, _, hj₂_al, hj₂_v, hx₂⟩⟩
    refine ⟨⟨symEdgeAt edges j₁, ⟨j₁, hj₁_al, rfl⟩, ?_, by rw [tauOfArr_symEdgeAt hedges, hj₁_v]⟩,
      ⟨symEdgeAt edges j₂, ⟨j₂, hj₂_al, rfl⟩, ?_, by rw [tauOfArr_symEdgeAt hedges]; exact hj₂_v⟩⟩
    · unfold symEdgeAt; rw [Sym2.mem_iff]; exact hx₁
    · unfold symEdgeAt; rw [Sym2.mem_iff]; exact hx₂
  · rintro ⟨⟨_, ⟨j₁, hj₁_al, rfl⟩, hx₁, hj₁_v⟩, ⟨_, ⟨j₂, hj₂_al, rfl⟩, hx₂, hj₂_v⟩⟩
    rw [tauOfArr_symEdgeAt hedges] at hj₁_v hj₂_v
    unfold symEdgeAt at hx₁ hx₂
    rw [Sym2.mem_iff] at hx₁ hx₂
    exact ⟨⟨j₁, j₁.2, hj₁_al, hj₁_v, hx₁⟩, ⟨j₂, j₂.2, hj₂_al, hj₂_v, hx₂⟩⟩

/-- Body of the first loop of `computeZProg`: marks endpoints of active edges in `a_inc_R = 10`
(if mapped to `v = r_7`) or `a_inc_Rprime = 11` (if mapped to a leaf `≠ v`). -/
def markIncEdgesBody : Cmd :=
  .seq (.assign 14 (.read 4 (.reg 11)))
    (.ite (.reg 14)
      (.seq (.assign 12 (.read 2 (.reg 11)))
        (.seq (.assign 13 (.read 3 (.reg 11)))
          (.seq (.assign 15 (.read 5 (.reg 11)))
            (.ite (.op .eq (.reg 15) (.reg 7))
              (.seq (.write 10 (.reg 12) (.const 1))
                (.write 10 (.reg 13) (.const 1)))
              (.seq (.write 11 (.reg 12) (.const 1))
                (.write 11 (.reg 13) (.const 1)))))))
      .skip)

theorem markIncEdgesLoop_exec {w n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t) (v : Fin t)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : edges.length < 2 ^ w) (ht_w : t < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = edges.length) {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hincR : IsBitSet (incRUpTo edges aliveSet f_tau v k) 10 s)
    (hincRp : IsBitSet (incRprimeUpTo edges aliveSet f_tau v k) 11 s)
    (hr2 : s.regs 2 = edges.length)
    (hr7 : s.regs 7 = v.1)
    (hr11 : s.regs 11 = k) :
    ∃ s' t_steps,
      Exec w (forUp 11 (.reg 2) markIncEdgesBody) s s' t_steps ∧
      t_steps ≤ 3 + 30 * rem ∧
      IsBitSet (incRUpTo edges aliveSet f_tau v edges.length) 10 s' ∧
      IsBitSet (incRprimeUpTo edges aliveSet f_tau v edges.length) 11 s' ∧
      (∀ a : Arr, a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = edges.length := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hm2_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hincR, hincRp,
      fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < edges.length := by omega
    have hk_w : k < 2 ^ w := by omega
    let jk : Fin edges.length := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hk_w, hm2_w, hk_lt, hw]
    have hal_len : k < (s.arrs 4).length := by rw [hal.1]; exact hk_lt
    let al_k := (s.arrs 4)[k]'hal_len
    have hal_k_le : al_k ≤ 1 := hal.2.1 jk
    have hal_k_w : al_k < 2 ^ w := by omega
    let s₁ := s.setReg 14 al_k
    have hex_rd4 : Exec w (.assign 14 (.read 4 (.reg 11))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr11, hk_w, hal_len, al_k, hal_k_w])
    by_cases hmem_k : jk ∈ aliveSet
    · have hal_k_ne0 : al_k ≠ 0 := (hal.2.2 jk).mpr hmem_k
      have hcond14 : (Expr.reg 14).eval w s₁ = some al_k := by
        simp [s₁, Expr.eval, checkWord, hal_k_w]
      rcases hend with ⟨heu_len, hev_len, hend_all⟩
      have heu_k : (s.arrs 2)[k]'(by rw [heu_len]; exact hk_lt) = (edges[k]'hk_lt).1.1 :=
        (hend_all jk).1
      have hev_k : (s.arrs 3)[k]'(by rw [hev_len]; exact hk_lt) = (edges[k]'hk_lt).2.1 :=
        (hend_all jk).2
      let uk := (edges[k]'hk_lt).1
      let vk := (edges[k]'hk_lt).2
      have huk_w : uk.1 < 2 ^ w := by have := uk.2; omega
      have hvk_w : vk.1 < 2 ^ w := by have := vk.2; omega
      let s₂ := s₁.setReg 12 uk.1
      have hex_rd2 : Exec w (.assign 12 (.read 2 (.reg 11))) s₁ s₂ 3 :=
        .assign (by
          simp [s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w,
            show k < (s.arrs 2).length by rw [heu_len]; exact hk_lt, heu_k, uk, huk_w])
      let s₃ := s₂.setReg 13 vk.1
      have hex_rd3 : Exec w (.assign 13 (.read 3 (.reg 11))) s₂ s₃ 3 :=
        .assign (by
          simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w,
            show k < (s.arrs 3).length by rw [hev_len]; exact hk_lt, hev_k, vk, hvk_w])
      have htau_len : k < (s.arrs 5).length := by rw [htau.1]; exact hk_lt
      have htau_k : (s.arrs 5)[k]'htau_len = (f_tau jk).1 := htau.2 jk
      let wk := f_tau jk
      have hwk_w : wk.1 < 2 ^ w := by have := wk.2; omega
      let s₄ := s₃.setReg 15 wk.1
      have hex_rd5 : Exec w (.assign 15 (.read 5 (.reg 11))) s₃ s₄ 3 :=
        .assign (by
          simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w,
            htau_len, htau_k, wk, hwk_w])
      by_cases hwk_eq : wk = v
      · have hwk_val : wk.1 = v.1 := congrArg Fin.val hwk_eq
        have hcond15 : (Expr.op .eq (.reg 15) (.reg 7)).eval w s₄ = some 1 := by
          simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr7, hwk_val, hv_w, hw]
        let s₅ := s₄.writeArr 10 uk.1 1
        have hex_wr10a : Exec w (.write 10 (.reg 12) (.const 1)) s₄ s₅ 3 :=
          .write (by simp [s₄, s₃, s₂, State.setReg, Expr.eval, checkWord, huk_w])
            (by simp [Expr.eval, checkWord, hw])
            (by simp [s₄, s₃, s₂, s₁, hincR.1, uk.2])
        let s₆ := s₅.writeArr 10 vk.1 1
        have hex_wr10b : Exec w (.write 10 (.reg 13) (.const 1)) s₅ s₆ 3 :=
          .write (by simp [s₅, s₄, s₃, State.setReg, Expr.eval, checkWord, hvk_w])
            (by simp [Expr.eval, checkWord, hw])
            (by simp [s₅, s₄, s₃, s₂, s₁, hincR.1, vk.2])
        have hex_ite15 : Exec w (.ite (.op .eq (.reg 15) (.reg 7))
            (.seq (.write 10 (.reg 12) (.const 1)) (.write 10 (.reg 13) (.const 1)))
            (.seq (.write 11 (.reg 12) (.const 1)) (.write 11 (.reg 13) (.const 1)))) s₄ s₆ 9 :=
          .ite_true hcond15 (by omega) (.seq hex_wr10a hex_wr10b)
        have hex_body : Exec w markIncEdgesBody s s₆ 22 :=
          .seq hex_rd4 (.ite_true hcond14 hal_k_ne0
            (.seq hex_rd2 (.seq hex_rd3 (.seq hex_rd5 hex_ite15))))
        let s₇ := s₆.setReg 11 (k + 1)
        have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₆ s₇ 4 :=
          .assign (by
            simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
        have hincR_step : incRUpTo edges aliveSet f_tau v (k + 1) =
            insert vk (insert uk (incRUpTo edges aliveSet f_tau v k)) := by
          have hmem' : (⟨k, hk_lt⟩ : Fin edges.length) ∈ aliveSet := hmem_k
          have heq' : f_tau ⟨k, hk_lt⟩ = v := hwk_eq
          simp [incRUpTo, hk_lt, hmem', heq', uk, vk]
        have hincRp_step : incRprimeUpTo edges aliveSet f_tau v (k + 1) =
            incRprimeUpTo edges aliveSet f_tau v k := by
          simp only [incRprimeUpTo, hk_lt, ↓reduceDIte,
            show ¬ ((⟨k, hk_lt⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk_lt⟩ ≠ v) from
              fun h => h.2 hwk_eq, ↓reduceIte]
        have hincR₇ : IsBitSet (incRUpTo edges aliveSet f_tau v (k + 1)) 10 s₇ := by
          rw [hincR_step]
          exact (((hincR.of_arr_eq (rfl : s₄.arrs 10 = s.arrs 10)).write_one uk).write_one vk).of_arr_eq rfl
        have hincRp₇ : IsBitSet (incRprimeUpTo edges aliveSet f_tau v (k + 1)) 11 s₇ := by
          rw [hincRp_step]
          exact hincRp.of_arr_eq (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁])
        rcases ih (k + 1) (by omega) (s := s₇)
            (IsEndpointArrs.of_arrs_eq ⟨heu_len, hev_len, hend_all⟩
              (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]) (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]))
            (hal.of_arr_eq (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]))
            (htau.of_arr_eq (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]))
            hincR₇ hincRp₇
            (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr2])
            (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr7])
            (by simp [s₇]) with
          ⟨s₈, t₈, hex₈, ht₈, hR₈, hRp₈, harr₈, hreg₈⟩
        refine ⟨s₈, 3 + (22 + 4) + t₈,
          .while_true hcond (by omega) (.seq hex_body hex_inc) hex₈,
          by omega, hR₈, hRp₈,
          fun a ha10 ha11 => by rw [harr₈ a ha10 ha11]; simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha10],
          fun r hr11' hr12 hr13 hr14 hr15 => by
            rw [hreg₈ r hr11' hr12 hr13 hr14 hr15]
            simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr11', hr15, hr13, hr12, hr14]⟩
      · have hwk_ne_val : wk.1 ≠ v.1 := fun h => hwk_eq (Fin.ext h)
        have hcond15 : (Expr.op .eq (.reg 15) (.reg 7)).eval w s₄ = some 0 := by
          simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr7, hwk_ne_val, hwk_w, hv_w, h0_w]
        let s₅ := s₄.writeArr 11 uk.1 1
        have hex_wr11a : Exec w (.write 11 (.reg 12) (.const 1)) s₄ s₅ 3 :=
          .write (by simp [s₄, s₃, s₂, State.setReg, Expr.eval, checkWord, huk_w])
            (by simp [Expr.eval, checkWord, hw])
            (by simp [s₄, s₃, s₂, s₁, hincRp.1, uk.2])
        let s₆ := s₅.writeArr 11 vk.1 1
        have hex_wr11b : Exec w (.write 11 (.reg 13) (.const 1)) s₅ s₆ 3 :=
          .write (by simp [s₅, s₄, s₃, State.setReg, Expr.eval, checkWord, hvk_w])
            (by simp [Expr.eval, checkWord, hw])
            (by simp [s₅, s₄, s₃, s₂, s₁, hincRp.1, vk.2])
        have hex_ite15 : Exec w (.ite (.op .eq (.reg 15) (.reg 7))
            (.seq (.write 10 (.reg 12) (.const 1)) (.write 10 (.reg 13) (.const 1)))
            (.seq (.write 11 (.reg 12) (.const 1)) (.write 11 (.reg 13) (.const 1)))) s₄ s₆ 9 :=
          .ite_false hcond15 (.seq hex_wr11a hex_wr11b)
        have hex_body : Exec w markIncEdgesBody s s₆ 22 :=
          .seq hex_rd4 (.ite_true hcond14 hal_k_ne0
            (.seq hex_rd2 (.seq hex_rd3 (.seq hex_rd5 hex_ite15))))
        let s₇ := s₆.setReg 11 (k + 1)
        have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₆ s₇ 4 :=
          .assign (by
            simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
        have hincR_step : incRUpTo edges aliveSet f_tau v (k + 1) =
            incRUpTo edges aliveSet f_tau v k := by
          simp only [incRUpTo, hk_lt, ↓reduceDIte,
            show ¬ ((⟨k, hk_lt⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk_lt⟩ = v) from
              fun h => hwk_eq h.2, ↓reduceIte]
        have hincRp_step : incRprimeUpTo edges aliveSet f_tau v (k + 1) =
            insert vk (insert uk (incRprimeUpTo edges aliveSet f_tau v k)) := by
          have hmem' : (⟨k, hk_lt⟩ : Fin edges.length) ∈ aliveSet := hmem_k
          have hne' : f_tau ⟨k, hk_lt⟩ ≠ v := hwk_eq
          simp [incRprimeUpTo, hk_lt, hmem', hne', uk, vk]
        have hincR₇ : IsBitSet (incRUpTo edges aliveSet f_tau v (k + 1)) 10 s₇ := by
          rw [hincR_step]
          exact hincR.of_arr_eq (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁])
        have hincRp₇ : IsBitSet (incRprimeUpTo edges aliveSet f_tau v (k + 1)) 11 s₇ := by
          rw [hincRp_step]
          exact (((hincRp.of_arr_eq (rfl : s₄.arrs 11 = s.arrs 11)).write_one uk).write_one vk).of_arr_eq rfl
        rcases ih (k + 1) (by omega) (s := s₇)
            (IsEndpointArrs.of_arrs_eq ⟨heu_len, hev_len, hend_all⟩
              (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]) (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]))
            (hal.of_arr_eq (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]))
            (htau.of_arr_eq (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]))
            hincR₇ hincRp₇
            (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr2])
            (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr7])
            (by simp [s₇]) with
          ⟨s₈, t₈, hex₈, ht₈, hR₈, hRp₈, harr₈, hreg₈⟩
        refine ⟨s₈, 3 + (22 + 4) + t₈,
          .while_true hcond (by omega) (.seq hex_body hex_inc) hex₈,
          by omega, hR₈, hRp₈,
          fun a ha10 ha11 => by rw [harr₈ a ha10 ha11]; simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha11],
          fun r hr11' hr12 hr13 hr14 hr15 => by
            rw [hreg₈ r hr11' hr12 hr13 hr14 hr15]
            simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr11', hr15, hr13, hr12, hr14]⟩
    · have hal_k_eq0 : al_k = 0 := by
        by_contra hne
        exact hmem_k ((hal.2.2 jk).mp hne)
      have hcond14 : (Expr.reg 14).eval w s₁ = some 0 := by
        simp [s₁, Expr.eval, checkWord, hal_k_eq0, h0_w]
      have hex_body : Exec w markIncEdgesBody s s₁ 5 :=
        .seq hex_rd4 (.ite_false hcond14 (.skip s₁))
      let s₂ := s₁.setReg 11 (k + 1)
      have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₁ s₂ 4 :=
        .assign (by
          simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
      have hincR_step : incRUpTo edges aliveSet f_tau v (k + 1) =
          incRUpTo edges aliveSet f_tau v k := by
        simp only [incRUpTo, hk_lt, ↓reduceDIte,
          show ¬ ((⟨k, hk_lt⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk_lt⟩ = v) from
            fun h => hmem_k h.1, ↓reduceIte]
      have hincRp_step : incRprimeUpTo edges aliveSet f_tau v (k + 1) =
          incRprimeUpTo edges aliveSet f_tau v k := by
        simp only [incRprimeUpTo, hk_lt, ↓reduceDIte,
          show ¬ ((⟨k, hk_lt⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk_lt⟩ ≠ v) from
            fun h => hmem_k h.1, ↓reduceIte]
      have hincR₂ : IsBitSet (incRUpTo edges aliveSet f_tau v (k + 1)) 10 s₂ := by
        rw [hincR_step]; exact hincR.of_arr_eq rfl
      have hincRp₂ : IsBitSet (incRprimeUpTo edges aliveSet f_tau v (k + 1)) 11 s₂ := by
        rw [hincRp_step]; exact hincRp.of_arr_eq rfl
      rcases ih (k + 1) (by omega) (s := s₂)
          (hend.of_arrs_eq rfl rfl) (hal.of_arr_eq rfl) (htau.of_arr_eq rfl)
          hincR₂ hincRp₂
          (by simp [s₂, s₁, hr2])
          (by simp [s₂, s₁, hr7])
          (by simp [s₂]) with
        ⟨s₃, t₃, hex₃, ht₃, hR₃, hRp₃, harr₃, hreg₃⟩
      refine ⟨s₃, 3 + (5 + 4) + t₃,
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₃,
        by omega, hR₃, hRp₃,
        fun a ha10 ha11 => by rw [harr₃ a ha10 ha11]; rfl,
        fun r hr11' hr12 hr13 hr14 hr15 => by
          rw [hreg₃ r hr11' hr12 hr13 hr14 hr15]
          simp [s₂, s₁, hr11', hr14]⟩

/-- Ordered list of vertices in `Z` with index `< x`. -/
def zListUpTo {n : ℕ} (Z : Finset (Fin n)) : ℕ → List (Fin n)
  | 0 => []
  | x + 1 =>
    if hx : x < n then
      if (⟨x, hx⟩ : Fin n) ∈ Z then
        zListUpTo Z x ++ [⟨x, hx⟩]
      else
        zListUpTo Z x
    else
      zListUpTo Z x

theorem mem_zListUpTo {n : ℕ} (Z : Finset (Fin n)) (x : ℕ) (u : Fin n) :
    u ∈ zListUpTo Z x ↔ u.1 < x ∧ u ∈ Z := by
  induction x with
  | zero => simp [zListUpTo]
  | succ x ih =>
    simp only [zListUpTo]
    split_ifs with hx hmem
    · simp only [List.mem_append, List.mem_singleton, ih]
      constructor
      · rintro (⟨hlt, hu⟩ | rfl)
        · exact ⟨by omega, hu⟩
        · exact ⟨Nat.lt_succ_self x, hmem⟩
      · rintro ⟨hlt, hu⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
        · exact Or.inl ⟨hlt', hu⟩
        · exact Or.inr (Fin.ext heq)
    · rw [ih]
      constructor
      · rintro ⟨hlt, hu⟩
        exact ⟨by omega, hu⟩
      · rintro ⟨hlt, hu⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
        · exact ⟨hlt', hu⟩
        · exfalso
          have hux : u = ⟨x, hx⟩ := Fin.ext heq
          subst hux
          exact hmem hu
    · rw [ih]
      constructor <;> rintro ⟨hlt, hu⟩ <;> exact ⟨by omega, hu⟩

theorem nodup_zListUpTo {n : ℕ} (Z : Finset (Fin n)) (x : ℕ) :
    (zListUpTo Z x).Nodup := by
  induction x with
  | zero => simp [zListUpTo]
  | succ x ih =>
    simp only [zListUpTo]
    split_ifs with hx hmem
    · rw [List.nodup_append]
      refine ⟨ih, List.nodup_singleton _, fun u hu v hv huv => ?_⟩
      rw [List.mem_singleton] at hv
      subst hv
      rw [mem_zListUpTo] at hu
      have hval : u.1 = x := congrArg Fin.val huv
      omega
    · exact ih
    · exact ih

theorem toFinset_zListUpTo {n : ℕ} (Z : Finset (Fin n)) (x : ℕ) :
    (zListUpTo Z x).toFinset = Z.filter (fun u => u.1 < x) := by
  ext u
  rw [List.mem_toFinset, mem_zListUpTo, Finset.mem_filter, and_comm]

theorem length_zListUpTo {n : ℕ} (Z : Finset (Fin n)) (x : ℕ) :
    (zListUpTo Z x).length = (Z.filter (fun u => u.1 < x)).card := by
  rw [← toFinset_zListUpTo, List.toFinset_card_of_nodup (nodup_zListUpTo Z x)]

theorem toFinset_zListUpTo_self {n : ℕ} (Z : Finset (Fin n)) :
    (zListUpTo Z n).toFinset = Z := by
  rw [toFinset_zListUpTo]
  ext u
  simp

theorem length_zListUpTo_self {n : ℕ} (Z : Finset (Fin n)) :
    (zListUpTo Z n).length = Z.card := by
  rw [← List.toFinset_card_of_nodup (nodup_zListUpTo Z n), toFinset_zListUpTo_self]

/-- Array `a_Z_list` of length `n` stores the elements of `L : List (Fin n)` in its prefix. -/
def IsZListArr {n : ℕ} (L : List (Fin n)) (a_Z_list : Arr) (s : State) : Prop :=
  ∃ (hlen : (s.arrs a_Z_list).length = n) (hL : L.length ≤ n),
    ∀ i (hi : i < L.length), (s.arrs a_Z_list)[i]'(by omega) = (L[i]'hi).1

theorem IsZListArr.of_arr_eq {n : ℕ} {L : List (Fin n)} {a_Z_list : Arr} {s s' : State}
    (h : IsZListArr L a_Z_list s) (heq : s'.arrs a_Z_list = s.arrs a_Z_list) :
    IsZListArr L a_Z_list s' := by
  rcases h with ⟨hlen, hL, hall⟩
  exact ⟨by rw [heq, hlen], hL, fun i hi => by simp only [heq]; exact hall i hi⟩

/-- Body of the second loop of `computeZProg`: intersects `a_inc_R = 10` and `a_inc_Rprime = 11`
into `a_Z_bit = 12`, appends members of `Z` to `a_Z_list = 13`, and increments `r_8` (`Z_cnt`). -/
def collectZBody : Cmd :=
  .seq (.assign 14 (.read 10 (.reg 11)))
    (.seq (.assign 15 (.read 11 (.reg 11)))
      (.seq (.assign 16 (.op .mul (.reg 14) (.reg 15)))
        (.ite (.reg 16)
          (.seq (.write 12 (.reg 11) (.const 1))
            (.seq (.write 13 (.reg 8) (.reg 11))
              (.assign 8 (.op .add (.reg 8) (.const 1)))))
          .skip)))

theorem collectZLoop_exec {w n : ℕ} (S_R S_Rp : Finset (Fin n))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem x : ℕ) (hrem : x + rem = n) {s : State}
    (hincR : IsBitSet S_R 10 s)
    (hincRp : IsBitSet S_Rp 11 s)
    (hZbit : IsBitSet ((S_R ∩ S_Rp).filter (fun u => u.1 < x)) 12 s)
    (hZlist : IsZListArr (zListUpTo (S_R ∩ S_Rp) x) 13 s)
    (hr0 : s.regs 0 = n)
    (hr8 : s.regs 8 = (zListUpTo (S_R ∩ S_Rp) x).length)
    (hr11 : s.regs 11 = x) :
    ∃ s' t_steps,
      Exec w (forUp 11 (.reg 0) collectZBody) s s' t_steps ∧
      t_steps ≤ 3 + 28 * rem ∧
      IsBitSet (S_R ∩ S_Rp) 12 s' ∧
      IsZListArr (zListUpTo (S_R ∩ S_Rp) n) 13 s' ∧
      s'.regs 8 = (S_R ∩ S_Rp).card ∧
      (∀ a : Arr, a ≠ 12 → a ≠ 13 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 11 → r ≠ 14 → r ≠ 15 → r ≠ 16 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let Z := S_R ∩ S_Rp
  induction rem generalizing x s with
  | zero =>
    have hx_eq : x = n := by omega
    rw [hx_eq] at hr11 hZbit hZlist hr8
    have hcond : (Expr.op .lt (.reg 11) (.reg 0)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr0, hn_w, h0_w]
    have hfilter_self : (S_R ∩ S_Rp).filter (fun u : Fin n => u.1 < n) = S_R ∩ S_Rp := by
      ext u; simp
    rw [hfilter_self] at hZbit
    rw [length_zListUpTo_self] at hr8
    exact ⟨s, 3, .while_false hcond, by omega, hZbit, hZlist, hr8,
      fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hx_lt : x < n := by omega
    have hx_w : x < 2 ^ w := by omega
    let ux : Fin n := ⟨x, hx_lt⟩
    have hcond : (Expr.op .lt (.reg 11) (.reg 0)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr0, hx_w, hn_w, hx_lt, hw]
    have hR_len : x < (s.arrs 10).length := by rw [hincR.1]; exact hx_lt
    have hRp_len : x < (s.arrs 11).length := by rw [hincRp.1]; exact hx_lt
    let vR := (s.arrs 10)[x]'hR_len
    let vRp := (s.arrs 11)[x]'hRp_len
    have hvR_le : vR ≤ 1 := hincR.2.1 ux
    have hvRp_le : vRp ≤ 1 := hincRp.2.1 ux
    have hvR_w : vR < 2 ^ w := by omega
    have hvRp_w : vRp < 2 ^ w := by omega
    have hmul_le : vR * vRp ≤ 1 := by
      have := Nat.mul_le_mul hvR_le hvRp_le; omega
    have hmul_w : vR * vRp < 2 ^ w := by omega
    let s₁ := s.setReg 14 vR
    have hex_rd10 : Exec w (.assign 14 (.read 10 (.reg 11))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr11, hx_w, hR_len, vR, hvR_w])
    let s₂ := s₁.setReg 15 vRp
    have hex_rd11 : Exec w (.assign 15 (.read 11 (.reg 11))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hr11, hx_w, hRp_len, vRp, hvRp_w])
    let s₃ := s₂.setReg 16 (vR * vRp)
    have hex_mul : Exec w (.assign 16 (.op .mul (.reg 14) (.reg 15))) s₂ s₃ 4 :=
      .assign (by
        simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hvR_w, hvRp_w, hmul_w])
    by_cases hmem_Z : ux ∈ Z
    · have hmem_R : ux ∈ S_R := (Finset.mem_inter.mp hmem_Z).1
      have hmem_Rp : ux ∈ S_Rp := (Finset.mem_inter.mp hmem_Z).2
      have hvR_ne0 : vR ≠ 0 := (hincR.2.2 ux).mpr hmem_R
      have hvRp_ne0 : vRp ≠ 0 := (hincRp.2.2 ux).mpr hmem_Rp
      have hmul_ne0 : vR * vRp ≠ 0 := Nat.mul_ne_zero hvR_ne0 hvRp_ne0
      have hcond16 : (Expr.reg 16).eval w s₃ = some (vR * vRp) := by
        simp [s₃, Expr.eval, checkWord, hmul_w]
      let s₄ := s₃.writeArr 12 x 1
      have hex_wr12 : Exec w (.write 12 (.reg 11) (.const 1)) s₃ s₄ 3 :=
        .write (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hr11, hx_w])
          (by simp [Expr.eval, checkWord, hw])
          (by simp [s₃, s₂, s₁, hZbit.1, hx_lt])
      let Lx := zListUpTo (S_R ∩ S_Rp) x
      have hr8_Lx : s.regs 8 = Lx.length := hr8
      have hLx_lt : Lx.length < n := by
        dsimp only [Lx]
        rw [length_zListUpTo]
        have hsub : Z.filter (fun u : Fin n => u.1 < x) ⊂ Finset.univ := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.subset_univ _, fun heq => ?_⟩
          have hux_mem : ux ∈ Z.filter (fun u : Fin n => u.1 < x) := by
            rw [heq]; exact Finset.mem_univ ux
          rw [Finset.mem_filter] at hux_mem
          exact Nat.lt_irrefl x hux_mem.2
        have hcard := Finset.card_lt_card hsub
        simpa [Z] using hcard
      have hLx_w : Lx.length < 2 ^ w := by omega
      let s₅ := s₄.writeArr 13 Lx.length x
      have hex_wr13 : Exec w (.write 13 (.reg 8) (.reg 11)) s₄ s₅ 3 :=
        .write (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hr8_Lx, hLx_w])
          (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hr11, hx_w])
          (by simp [s₄, s₃, s₂, s₁, hZlist.1, hLx_lt])
      let s₆ := s₅.setReg 8 (Lx.length + 1)
      have hex_inc8 : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₅ s₆ 4 :=
        .assign (by
          simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr8_Lx, hLx_w, hw, show Lx.length + 1 < 2 ^ w by omega])
      have hex_ite16 : Exec w (.ite (.reg 16)
          (.seq (.write 12 (.reg 11) (.const 1))
            (.seq (.write 13 (.reg 8) (.reg 11))
              (.assign 8 (.op .add (.reg 8) (.const 1))))) .skip) s₃ s₆ 11 :=
        .ite_true hcond16 hmul_ne0 (.seq hex_wr12 (.seq hex_wr13 hex_inc8))
      have hex_body : Exec w collectZBody s s₆ 21 :=
        .seq hex_rd10 (.seq hex_rd11 (.seq hex_mul hex_ite16))
      let s₇ := s₆.setReg 11 (x + 1)
      have hex_inc11 : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₆ s₇ 4 :=
        .assign (by
          simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr11, hx_w, hw, show x + 1 < 2 ^ w by omega])
      have hfilter_step : Z.filter (fun u : Fin n => u.1 < x + 1) =
          insert ux (Z.filter (fun u : Fin n => u.1 < x)) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hu, hlt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
          · exact Or.inr ⟨hu, hlt'⟩
          · exact Or.inl (Fin.ext heq)
        · rintro (rfl | ⟨hu, hlt⟩)
          · exact ⟨hmem_Z, Nat.lt_succ_self x⟩
          · exact ⟨hu, by omega⟩
      have hZbit₇ : IsBitSet ((S_R ∩ S_Rp).filter (fun u : Fin n => u.1 < x + 1)) 12 s₇ := by
        change IsBitSet (Z.filter (fun u : Fin n => u.1 < x + 1)) 12 s₇
        rw [hfilter_step]
        exact ((hZbit.of_arr_eq (rfl : s₃.arrs 12 = s.arrs 12)).write_one ux).of_arr_eq
          (by simp [s₇, s₆, s₅, s₄, ux])
      have hzList_step : zListUpTo (S_R ∩ S_Rp) (x + 1) = Lx ++ [ux] := by
        simp only [zListUpTo, hx_lt, ↓reduceDIte,
          show (⟨x, hx_lt⟩ : Fin n) ∈ S_R ∩ S_Rp from hmem_Z,
          ↓reduceIte, Lx, ux]
      have hZlist₇ : IsZListArr (zListUpTo (S_R ∩ S_Rp) (x + 1)) 13 s₇ := by
        rw [hzList_step]
        have hZlist' : IsZListArr Lx 13 s := hZlist
        rcases hZlist' with ⟨hlen13, _, hall13⟩
        have h13_eq : s₇.arrs 13 = (s.arrs 13).set Lx.length x := by
          simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]
        refine ⟨by simp [h13_eq, hlen13], by simp; omega, fun i hi => ?_⟩
        simp only [h13_eq]
        rw [List.length_append, List.length_singleton] at hi
        by_cases hi_eq : i = Lx.length
        · subst hi_eq
          simp [List.getElem_set_self, ux]
        · rw [List.getElem_set_ne (Ne.symm hi_eq), List.getElem_append_left (by omega)]
          exact hall13 i (by omega)
      have hr8_7 : s₇.regs 8 = (zListUpTo (S_R ∩ S_Rp) (x + 1)).length := by
        rw [hzList_step, List.length_append, List.length_singleton]
        simp [s₇, s₆]
      rcases ih (x + 1) (by omega) (s := s₇)
          (hincR.of_arr_eq (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]))
          (hincRp.of_arr_eq (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]))
          hZbit₇ hZlist₇
          (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr0])
          hr8_7
          (by simp [s₇]) with
        ⟨s₈, t₈, hex₈, ht₈, hZb₈, hZl₈, hr8_8, harr₈, hreg₈⟩
      refine ⟨s₈, 3 + (21 + 4) + t₈,
        .while_true hcond (by omega) (.seq hex_body hex_inc11) hex₈,
        by omega, hZb₈, hZl₈, hr8_8,
        fun a ha12 ha13 => by
          rw [harr₈ a ha12 ha13]; simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha12, ha13],
        fun r hr8' hr11' hr14 hr15 hr16 => by
          rw [hreg₈ r hr8' hr11' hr14 hr15 hr16]
          simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr11', hr8', hr16, hr15, hr14]⟩
    · have hmul_eq0 : vR * vRp = 0 := by
        by_contra hne
        have hvR_ne0 : vR ≠ 0 := fun h0 => by simp [h0] at hne
        have hvRp_ne0 : vRp ≠ 0 := fun h0 => by simp [h0] at hne
        exact hmem_Z (Finset.mem_inter.mpr ⟨(hincR.2.2 ux).mp hvR_ne0, (hincRp.2.2 ux).mp hvRp_ne0⟩)
      have hcond16 : (Expr.reg 16).eval w s₃ = some 0 := by
        simp [s₃, Expr.eval, checkWord, hmul_eq0, h0_w]
      have hex_ite16 : Exec w (.ite (.reg 16)
          (.seq (.write 12 (.reg 11) (.const 1))
            (.seq (.write 13 (.reg 8) (.reg 11))
              (.assign 8 (.op .add (.reg 8) (.const 1))))) .skip) s₃ s₃ 2 :=
        .ite_false hcond16 (.skip s₃)
      have hex_body : Exec w collectZBody s s₃ 12 :=
        .seq hex_rd10 (.seq hex_rd11 (.seq hex_mul hex_ite16))
      let s₄ := s₃.setReg 11 (x + 1)
      have hex_inc11 : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₃ s₄ 4 :=
        .assign (by
          simp [s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr11, hx_w, hw, show x + 1 < 2 ^ w by omega])
      have hfilter_step : (S_R ∩ S_Rp).filter (fun u : Fin n => u.1 < x + 1) =
          (S_R ∩ S_Rp).filter (fun u : Fin n => u.1 < x) := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hu, hlt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
          · exact ⟨hu, hlt'⟩
          · exfalso
            have hux : u = ux := Fin.ext heq
            subst hux
            exact hmem_Z hu
        · rintro ⟨hu, hlt⟩
          exact ⟨hu, by omega⟩
      have hzList_step : zListUpTo (S_R ∩ S_Rp) (x + 1) = zListUpTo (S_R ∩ S_Rp) x := by
        simp only [zListUpTo, hx_lt, ↓reduceDIte,
          show (⟨x, hx_lt⟩ : Fin n) ∉ S_R ∩ S_Rp from hmem_Z,
          ↓reduceIte]
      have hZbit₄ : IsBitSet ((S_R ∩ S_Rp).filter (fun u : Fin n => u.1 < x + 1)) 12 s₄ := by
        rw [hfilter_step]; exact hZbit.of_arr_eq rfl
      have hZlist₄ : IsZListArr (zListUpTo (S_R ∩ S_Rp) (x + 1)) 13 s₄ := by
        rw [hzList_step]; exact hZlist.of_arr_eq rfl
      have hr8_4 : s₄.regs 8 = (zListUpTo (S_R ∩ S_Rp) (x + 1)).length := by
        rw [hzList_step]; simp [s₄, s₃, s₂, s₁, hr8]
      rcases ih (x + 1) (by omega) (s := s₄)
          (hincR.of_arr_eq rfl) (hincRp.of_arr_eq rfl)
          hZbit₄ hZlist₄
          (by simp [s₄, s₃, s₂, s₁, hr0])
          hr8_4
          (by simp [s₄]) with
        ⟨s₅, t₅, hex₅, ht₅, hZb₅, hZl₅, hr8_5, harr₅, hreg₅⟩
      refine ⟨s₅, 3 + (12 + 4) + t₅,
        .while_true hcond (by omega) (.seq hex_body hex_inc11) hex₅,
        by omega, hZb₅, hZl₅, hr8_5,
        fun a ha12 ha13 => by rw [harr₅ a ha12 ha13]; rfl,
        fun r hr8' hr11' hr14 hr15 hr16 => by
          rw [hreg₅ r hr8' hr11' hr14 hr15 hr16]
          simp [s₄, s₃, s₂, s₁, hr11', hr16, hr15, hr14]⟩

/-- Preamble allocations for `computeZProg`: allocates `10..13` of size `n` (`r_0`) and sets
`r_11 := 0`. -/
def computeZAllocsCmd : Cmd :=
  .seq (.alloc 10 (.reg 0))
    (.seq (.alloc 11 (.reg 0))
      (.seq (.alloc 12 (.reg 0))
        (.seq (.alloc 13 (.reg 0))
          (.assign 11 (.const 0)))))

/-- Program computing the cut vertex set `Z = leafCutVerts G τ v`:
1. Allocates `a_inc_R = 10`, `a_inc_Rprime = 11`, `a_Z_bit = 12`, `a_Z_list = 13` of size `n`.
2. Loops `r_11` from `0` to `m₂` (`r_2`) executing `markIncEdgesBody`.
3. Sets `r_8 := 0`, `r_11 := 0`, and loops `r_11` from `0` to `n` (`r_0`) executing `collectZBody`. -/
def computeZProg : Cmd :=
  .seq computeZAllocsCmd
    (.seq (forUp 11 (.reg 2) markIncEdgesBody)
      (.seq (.assign 8 (.const 0))
        (.seq (.assign 11 (.const 0))
          (forUp 11 (.reg 0) collectZBody))))

theorem computeZProg_exec {w n t : ℕ} (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t) (v : Fin t)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : edges.length < 2 ^ w) (ht_w : t < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = edges.length)
    (hr7 : s.regs 7 = v.1) :
    let Z := leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v
    ∃ s' t_steps,
      Exec w computeZProg s s' t_steps ∧
      t_steps ≤ 30 * edges.length + 32 * n + 20 ∧
      IsBitSet Z 12 s' ∧
      IsZListArr (zListUpTo Z n) 13 s' ∧
      s'.regs 8 = Z.card ∧
      (∀ a : Arr, a ≠ 10 → a ≠ 11 → a ≠ 12 → a ≠ 13 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 →
        s'.regs r = s.regs r) := by
  intro Z
  have h0_w : 0 < 2 ^ w := by omega
  have hallocs : ∃ s₅,
      Exec w computeZAllocsCmd s s₅ (6 + 4 * n) ∧
      (∀ r : Reg, r ≠ 11 → s₅.regs r = s.regs r) ∧
      s₅.regs 11 = 0 ∧
      (∀ a : Arr, a ≠ 10 → a ≠ 11 → a ≠ 12 → a ≠ 13 → s₅.arrs a = s.arrs a) ∧
      s₅.arrs 10 = List.replicate n 0 ∧
      s₅.arrs 11 = List.replicate n 0 ∧
      s₅.arrs 12 = List.replicate n 0 ∧
      s₅.arrs 13 = List.replicate n 0 := by
    let s₁ := s.setArr 10 (List.replicate n 0)
    have hex₁ : Exec w (.alloc 10 (.reg 0)) s s₁ (1 + n) :=
      .alloc (by simp [Expr.eval, checkWord, hr0, hn_w])
    let s₂ := s₁.setArr 11 (List.replicate n 0)
    have hex₂ : Exec w (.alloc 11 (.reg 0)) s₁ s₂ (1 + n) :=
      .alloc (by simp [s₁, Expr.eval, checkWord, hr0, hn_w])
    let s₃ := s₂.setArr 12 (List.replicate n 0)
    have hex₃ : Exec w (.alloc 12 (.reg 0)) s₂ s₃ (1 + n) :=
      .alloc (by simp [s₂, s₁, Expr.eval, checkWord, hr0, hn_w])
    let s₄ := s₃.setArr 13 (List.replicate n 0)
    have hex₄ : Exec w (.alloc 13 (.reg 0)) s₃ s₄ (1 + n) :=
      .alloc (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hr0, hn_w])
    let s₅ := s₄.setReg 11 0
    have hex₅ : Exec w (.assign 11 (.const 0)) s₄ s₅ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    have ht_eq : (1 + n) + ((1 + n) + ((1 + n) + ((1 + n) + 2))) = 6 + 4 * n := by omega
    refine ⟨s₅, ht_eq ▸ .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
      fun r hr => by simp [s₅, s₄, s₃, s₂, s₁, hr],
      by simp [s₅],
      fun a h10 h11 h12 h13 => by simp [s₅, s₄, s₃, s₂, s₁, h10, h11, h12, h13],
      by simp [s₅, s₄, s₃, s₂, s₁],
      by simp [s₅, s₄, s₃, s₂],
      by simp [s₅, s₄, s₃],
      by simp [s₅, s₄]⟩
  rcases hallocs with ⟨s₅, hex_alloc, hreg₅, hr11_5, harr₅, h10_5, h11_5, h12_5, h13_5⟩
  have hincR₅ : IsBitSet (incRUpTo edges aliveSet f_tau v 0) 10 s₅ := by
    simp only [incRUpTo]; exact IsBitSet.empty_of_replicate h10_5
  have hincRp₅ : IsBitSet (incRprimeUpTo edges aliveSet f_tau v 0) 11 s₅ := by
    simp only [incRprimeUpTo]; exact IsBitSet.empty_of_replicate h11_5
  rcases markIncEdgesLoop_exec edges aliveSet f_tau v hw hn_w hm2_w ht_w edges.length 0 (by omega)
      (s := s₅)
      (hend.of_arrs_eq (harr₅ 2 (by decide) (by decide) (by decide) (by decide))
        (harr₅ 3 (by decide) (by decide) (by decide) (by decide)))
      (hal.of_arr_eq (harr₅ 4 (by decide) (by decide) (by decide) (by decide)))
      (htau.of_arr_eq (harr₅ 5 (by decide) (by decide) (by decide) (by decide)))
      hincR₅ hincRp₅
      (by rw [hreg₅ 2 (by decide), hr2])
      (by rw [hreg₅ 7 (by decide), hr7])
      hr11_5 with
    ⟨s₆, t₆, hex₆, ht₆, hincR₆, hincRp₆, harr₆, hreg₆⟩
  let s₇ := s₆.setReg 8 0
  have hex₇ : Exec w (.assign 8 (.const 0)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₈ := s₇.setReg 11 0
  have hex₈ : Exec w (.assign 11 (.const 0)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let S_R := incRUpTo edges aliveSet f_tau v edges.length
  let S_Rp := incRprimeUpTo edges aliveSet f_tau v edges.length
  have hSR_inter : S_R ∩ S_Rp = Z :=
    incRUpTo_inter_incRprimeUpTo_eq_leafCutVerts ht_pos hedges aliveSet f_tau v
  have hZbit₈ : IsBitSet ((S_R ∩ S_Rp).filter (fun u : Fin n => u.1 < 0)) 12 s₈ := by
    have hempty : (S_R ∩ S_Rp).filter (fun u : Fin n => u.1 < 0) = ∅ := by ext u; simp
    rw [hempty]
    apply IsBitSet.empty_of_replicate
    simp [s₈, s₇, harr₆ 12 (by decide) (by decide), h12_5]
  have hZlist₈ : IsZListArr (zListUpTo (S_R ∩ S_Rp) 0) 13 s₈ := by
    simp only [zListUpTo]
    refine ⟨by simp [s₈, s₇, harr₆ 13 (by decide) (by decide), h13_5], by simp,
      fun _ hi => absurd hi (by simp)⟩
  rcases collectZLoop_exec S_R S_Rp hw hn_w n 0 (by omega)
      (s := s₈)
      (hincR₆.of_arr_eq rfl)
      (hincRp₆.of_arr_eq rfl)
      hZbit₈ hZlist₈
      (by simp [s₈, s₇, hreg₆ 0 (by decide) (by decide) (by decide) (by decide) (by decide),
        hreg₅ 0 (by decide), hr0])
      (by simp [s₈, s₇, zListUpTo])
      (by simp [s₈]) with
    ⟨s₉, t₉, hex₉, ht₉, hZb₉, hZl₉, hr8_9, harr₉, hreg₉⟩
  rw [hSR_inter] at hZb₉ hZl₉ hr8_9
  refine ⟨s₉, (6 + 4 * n) + (t₆ + (2 + (2 + t₉))),
    .seq hex_alloc (.seq hex₆ (.seq hex₇ (.seq hex₈ hex₉))),
    by omega, hZb₉, hZl₉, hr8_9,
    fun a ha10 ha11 ha12 ha13 => by
      rw [harr₉ a ha12 ha13]
      simp [s₈, s₇, harr₆ a ha10 ha11, harr₅ a ha10 ha11 ha12 ha13],
    fun r hr8 hr11 hr12 hr13 hr14 hr15 hr16 => by
      rw [hreg₉ r hr8 hr11 hr14 hr15 hr16]
      simp [s₈, s₇, hr11, hr8, hreg₆ r hr11 hr12 hr13 hr14 hr15, hreg₅ r hr11]⟩

/-- Pass 1 body of `selectCandEdgeProg`: if `a_alive[r_11] != 0` and `a_tau[r_11] == r_7`,
set `r_9 := r_11`. -/
def selectCandPass1Body : Cmd :=
  .seq (.assign 14 (.read 4 (.reg 11)))
    (.ite (.reg 14)
      (.seq (.assign 15 (.read 5 (.reg 11)))
        (.ite (.op .eq (.reg 15) (.reg 7))
          (.assign 9 (.reg 11))
          .skip))
      .skip)

/-- Pass 2 body of `selectCandEdgeProg`: if `a_alive[r_11] != 0` and `a_tau[r_11] == r_7`,
read endpoints `u, w` and if `a_Z_bit[u] + a_Z_bit[w] != 0`, set `r_9 := r_11`. -/
def selectCandPass2Body : Cmd :=
  .seq (.assign 14 (.read 4 (.reg 11)))
    (.ite (.reg 14)
      (.seq (.assign 15 (.read 5 (.reg 11)))
        (.ite (.op .eq (.reg 15) (.reg 7))
          (.seq (.assign 12 (.read 2 (.reg 11)))
            (.seq (.assign 13 (.read 3 (.reg 11)))
              (.seq (.assign 16 (.read 12 (.reg 12)))
                (.seq (.assign 17 (.read 12 (.reg 13)))
                  (.ite (.op .add (.reg 16) (.reg 17))
                    (.assign 9 (.reg 11))
                    .skip)))))
          .skip))
      .skip)

/-- Program selecting a candidate active edge `g_idx` mapped to `v = r_7` (stored in `r_9`),
preferring an edge incident with `Z` whenever one exists. -/
def selectCandEdgeProg : Cmd :=
  .seq (.assign 11 (.const 0))
    (.seq (forUp 11 (.reg 2) selectCandPass1Body)
      (.seq (.assign 11 (.const 0))
        (forUp 11 (.reg 2) selectCandPass2Body)))

theorem selectCandPass1Loop_exec {w m₂ t : ℕ} (aliveSet : Finset (Fin m₂)) (f_tau : Fin m₂ → Fin t)
    (v : Fin t) (hw : 1 < 2 ^ w) (hm2_w : m₂ < 2 ^ w) (ht_w : t < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = m₂) {s : State}
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hr2 : s.regs 2 = m₂)
    (hr7 : s.regs 7 = v.1)
    (hr11 : s.regs 11 = k)
    (hinv :
      (∃ g_idx : Fin m₂, s.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v) ∨
      (∀ j : Fin m₂, j.1 < k → j ∈ aliveSet → f_tau j ≠ v)) :
    ∃ s' t_steps,
      Exec w (forUp 11 (.reg 2) selectCandPass1Body) s s' t_steps ∧
      t_steps ≤ 3 + 19 * rem ∧
      ((∃ g_idx : Fin m₂, s'.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v) ∨
       (∀ j : Fin m₂, j ∈ aliveSet → f_tau j ≠ v)) ∧
      s'.arrs = s.arrs ∧
      (∀ r : Reg, r ≠ 9 → r ≠ 11 → r ≠ 14 → r ≠ 15 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = m₂ := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hm2_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, rfl, fun _ _ _ _ _ => rfl⟩
    rcases hinv with hfound | hnone
    · exact Or.inl hfound
    · exact Or.inr (fun j hj => hnone j j.2 hj)
  | succ rem ih =>
    have hk_lt : k < m₂ := by omega
    have hk_w : k < 2 ^ w := by omega
    let jk : Fin m₂ := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hk_w, hm2_w, hk_lt, hw]
    have hal_len : k < (s.arrs 4).length := by rw [hal.1]; exact hk_lt
    let al_k := (s.arrs 4)[k]'hal_len
    have hal_k_le : al_k ≤ 1 := hal.2.1 jk
    have hal_k_w : al_k < 2 ^ w := by omega
    let s₁ := s.setReg 14 al_k
    have hex_rd4 : Exec w (.assign 14 (.read 4 (.reg 11))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr11, hk_w, hal_len, al_k, hal_k_w])
    by_cases hmem_k : jk ∈ aliveSet
    · have hal_k_ne0 : al_k ≠ 0 := (hal.2.2 jk).mpr hmem_k
      have hcond14 : (Expr.reg 14).eval w s₁ = some al_k := by
        simp [s₁, Expr.eval, checkWord, hal_k_w]
      have htau_len : k < (s.arrs 5).length := by rw [htau.1]; exact hk_lt
      have htau_k : (s.arrs 5)[k]'htau_len = (f_tau jk).1 := htau.2 jk
      let wk := f_tau jk
      have hwk_w : wk.1 < 2 ^ w := by have := wk.2; omega
      let s₂ := s₁.setReg 15 wk.1
      have hex_rd5 : Exec w (.assign 15 (.read 5 (.reg 11))) s₁ s₂ 3 :=
        .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w, htau_len, htau_k, wk, hwk_w])
      by_cases hwk_eq : wk = v
      · have hwk_val : wk.1 = v.1 := congrArg Fin.val hwk_eq
        have hcond15 : (Expr.op .eq (.reg 15) (.reg 7)).eval w s₂ = some 1 := by
          simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr7, hwk_val, hv_w, hw]
        let s₃ := s₂.setReg 9 k
        have hex_set9 : Exec w (.assign 9 (.reg 11)) s₂ s₃ 2 :=
          .assign (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w])
        have hex_body : Exec w selectCandPass1Body s s₃ 12 :=
          .seq hex_rd4 (.ite_true hcond14 hal_k_ne0
            (.seq hex_rd5 (.ite_true hcond15 (by omega) hex_set9)))
        let s₄ := s₃.setReg 11 (k + 1)
        have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₃ s₄ 4 :=
          .assign (by
            simp [s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
        have hinv₄ :
            (∃ g_idx : Fin m₂, s₄.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v) ∨
            (∀ j : Fin m₂, j.1 < k + 1 → j ∈ aliveSet → f_tau j ≠ v) :=
          Or.inl ⟨jk, by simp [s₄, s₃, jk], hmem_k, hwk_eq⟩
        rcases ih (k + 1) (by omega) (s := s₄)
            (hal.of_arr_eq rfl) (htau.of_arr_eq rfl)
            (by simp [s₄, s₃, s₂, s₁, hr2])
            (by simp [s₄, s₃, s₂, s₁, hr7])
            (by simp [s₄]) hinv₄ with
          ⟨s₅, t₅, hex₅, ht₅, hres₅, harr₅, hreg₅⟩
        refine ⟨s₅, 3 + (12 + 4) + t₅,
          .while_true hcond (by omega) (.seq hex_body hex_inc) hex₅,
          by omega, hres₅, harr₅,
          fun r hr9 hr11' hr14 hr15 => by
            rw [hreg₅ r hr9 hr11' hr14 hr15]
            simp [s₄, s₃, s₂, s₁, hr11', hr9, hr15, hr14]⟩
      · have hwk_ne_val : wk.1 ≠ v.1 := fun h => hwk_eq (Fin.ext h)
        have hcond15 : (Expr.op .eq (.reg 15) (.reg 7)).eval w s₂ = some 0 := by
          simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr7, hwk_ne_val, hwk_w, hv_w, h0_w]
        have hex_body : Exec w selectCandPass1Body s s₂ 11 :=
          .seq hex_rd4 (.ite_true hcond14 hal_k_ne0
            (.seq hex_rd5 (.ite_false hcond15 (.skip s₂))))
        let s₃ := s₂.setReg 11 (k + 1)
        have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₂ s₃ 4 :=
          .assign (by
            simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
        have hinv₃ :
            (∃ g_idx : Fin m₂, s₃.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v) ∨
            (∀ j : Fin m₂, j.1 < k + 1 → j ∈ aliveSet → f_tau j ≠ v) := by
          rcases hinv with ⟨g_idx, hr9, hg_al, hg_v⟩ | hnone
          · exact Or.inl ⟨g_idx, by simp [s₃, s₂, s₁, hr9], hg_al, hg_v⟩
          · refine Or.inr (fun j hj hj_al => ?_)
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
            · exact hnone j hlt hj_al
            · have hjk : j = jk := Fin.ext heq
              subst hjk
              exact hwk_eq
        rcases ih (k + 1) (by omega) (s := s₃)
            (hal.of_arr_eq rfl) (htau.of_arr_eq rfl)
            (by simp [s₃, s₂, s₁, hr2])
            (by simp [s₃, s₂, s₁, hr7])
            (by simp [s₃]) hinv₃ with
          ⟨s₄, t₄, hex₄, ht₄, hres₄, harr₄, hreg₄⟩
        refine ⟨s₄, 3 + (11 + 4) + t₄,
          .while_true hcond (by omega) (.seq hex_body hex_inc) hex₄,
          by omega, hres₄, harr₄,
          fun r hr9 hr11' hr14 hr15 => by
            rw [hreg₄ r hr9 hr11' hr14 hr15]
            simp [s₃, s₂, s₁, hr11', hr15, hr14]⟩
    · have hal_k_eq0 : al_k = 0 := by
        by_contra hne
        exact hmem_k ((hal.2.2 jk).mp hne)
      have hcond14 : (Expr.reg 14).eval w s₁ = some 0 := by
        simp [s₁, Expr.eval, checkWord, hal_k_eq0, h0_w]
      have hex_body : Exec w selectCandPass1Body s s₁ 5 :=
        .seq hex_rd4 (.ite_false hcond14 (.skip s₁))
      let s₂ := s₁.setReg 11 (k + 1)
      have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₁ s₂ 4 :=
        .assign (by
          simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
      have hinv₂ :
          (∃ g_idx : Fin m₂, s₂.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v) ∨
          (∀ j : Fin m₂, j.1 < k + 1 → j ∈ aliveSet → f_tau j ≠ v) := by
        rcases hinv with ⟨g_idx, hr9, hg_al, hg_v⟩ | hnone
        · exact Or.inl ⟨g_idx, by simp [s₂, s₁, hr9], hg_al, hg_v⟩
        · refine Or.inr (fun j hj hj_al => ?_)
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
          · exact hnone j hlt hj_al
          · exfalso
            have hjk : j = jk := Fin.ext heq
            subst hjk
            exact hmem_k hj_al
      rcases ih (k + 1) (by omega) (s := s₂)
          (hal.of_arr_eq rfl) (htau.of_arr_eq rfl)
          (by simp [s₂, s₁, hr2])
          (by simp [s₂, s₁, hr7])
          (by simp [s₂]) hinv₂ with
        ⟨s₃, t₃, hex₃, ht₃, hres₃, harr₃, hreg₃⟩
      refine ⟨s₃, 3 + (5 + 4) + t₃,
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₃,
        by omega, hres₃, harr₃,
        fun r hr9 hr11' hr14 hr15 => by
          rw [hreg₃ r hr9 hr11' hr14 hr15]
          simp [s₂, s₁, hr11', hr14]⟩

theorem selectCandPass2Loop_exec {w n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t) (v : Fin t)
    (Z : Finset (Fin n))
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : edges.length < 2 ^ w) (ht_w : t < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = edges.length) {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hZbit : IsBitSet Z 12 s)
    (hr2 : s.regs 2 = edges.length)
    (hr7 : s.regs 7 = v.1)
    (hr11 : s.regs 11 = k)
    (hinv : ∃ g_idx : Fin edges.length,
      s.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v ∧
      ((∃ z ∈ Z, z ∈ symEdgeAt edges g_idx) ∨
       (∀ j : Fin edges.length, j.1 < k → j ∈ aliveSet → f_tau j = v →
         ∀ z ∈ Z, z ∉ symEdgeAt edges j))) :
    ∃ s' t_steps,
      Exec w (forUp 11 (.reg 2) selectCandPass2Body) s s' t_steps ∧
      t_steps ≤ 3 + 34 * rem ∧
      (∃ g_idx : Fin edges.length,
        s'.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v ∧
        ((∃ z ∈ Z, z ∈ symEdgeAt edges g_idx) ∨
         (∀ j : Fin edges.length, j ∈ aliveSet → f_tau j = v →
           ∀ z ∈ Z, z ∉ symEdgeAt edges j))) ∧
      s'.arrs = s.arrs ∧
      (∀ r : Reg, r ≠ 9 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
        s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = edges.length := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hm2_w, h0_w]
    rcases hinv with ⟨g_idx, hr9, hg_al, hg_v, hinc | hnone⟩
    · exact ⟨s, 3, .while_false hcond, by omega,
        ⟨g_idx, hr9, hg_al, hg_v, Or.inl hinc⟩, rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩
    · exact ⟨s, 3, .while_false hcond, by omega,
        ⟨g_idx, hr9, hg_al, hg_v, Or.inr (fun j hj hfv => hnone j j.2 hj hfv)⟩,
        rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < edges.length := by omega
    have hk_w : k < 2 ^ w := by omega
    let jk : Fin edges.length := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hk_w, hm2_w, hk_lt, hw]
    have hal_len : k < (s.arrs 4).length := by rw [hal.1]; exact hk_lt
    let al_k := (s.arrs 4)[k]'hal_len
    have hal_k_le : al_k ≤ 1 := hal.2.1 jk
    have hal_k_w : al_k < 2 ^ w := by omega
    let s₁ := s.setReg 14 al_k
    have hex_rd4 : Exec w (.assign 14 (.read 4 (.reg 11))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr11, hk_w, hal_len, al_k, hal_k_w])
    by_cases hmem_k : jk ∈ aliveSet
    · have hal_k_ne0 : al_k ≠ 0 := (hal.2.2 jk).mpr hmem_k
      have hcond14 : (Expr.reg 14).eval w s₁ = some al_k := by
        simp [s₁, Expr.eval, checkWord, hal_k_w]
      have htau_len : k < (s.arrs 5).length := by rw [htau.1]; exact hk_lt
      have htau_k : (s.arrs 5)[k]'htau_len = (f_tau jk).1 := htau.2 jk
      let wk := f_tau jk
      have hwk_w : wk.1 < 2 ^ w := by have := wk.2; omega
      let s₂ := s₁.setReg 15 wk.1
      have hex_rd5 : Exec w (.assign 15 (.read 5 (.reg 11))) s₁ s₂ 3 :=
        .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w, htau_len, htau_k, wk, hwk_w])
      by_cases hwk_eq : wk = v
      · have hwk_val : wk.1 = v.1 := congrArg Fin.val hwk_eq
        have hcond15 : (Expr.op .eq (.reg 15) (.reg 7)).eval w s₂ = some 1 := by
          simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr7, hwk_val, hv_w, hw]
        rcases hend with ⟨heu_len, hev_len, hend_all⟩
        have heu_k : (s.arrs 2)[k]'(by rw [heu_len]; exact hk_lt) = (edges[k]'hk_lt).1.1 :=
          (hend_all jk).1
        have hev_k : (s.arrs 3)[k]'(by rw [hev_len]; exact hk_lt) = (edges[k]'hk_lt).2.1 :=
          (hend_all jk).2
        let uk := (edges[k]'hk_lt).1
        let vk := (edges[k]'hk_lt).2
        have huk_w : uk.1 < 2 ^ w := by have := uk.2; omega
        have hvk_w : vk.1 < 2 ^ w := by have := vk.2; omega
        let s₃ := s₂.setReg 12 uk.1
        have hex_rd2 : Exec w (.assign 12 (.read 2 (.reg 11))) s₂ s₃ 3 :=
          .assign (by
            simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w,
              show k < (s.arrs 2).length by rw [heu_len]; exact hk_lt, heu_k, uk, huk_w])
        let s₄ := s₃.setReg 13 vk.1
        have hex_rd3 : Exec w (.assign 13 (.read 3 (.reg 11))) s₃ s₄ 3 :=
          .assign (by
            simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w,
              show k < (s.arrs 3).length by rw [hev_len]; exact hk_lt, hev_k, vk, hvk_w])
        have hZu_len : uk.1 < (s.arrs 12).length := by rw [hZbit.1]; exact uk.2
        have hZv_len : vk.1 < (s.arrs 12).length := by rw [hZbit.1]; exact vk.2
        let zu := (s.arrs 12)[uk.1]'hZu_len
        let zv := (s.arrs 12)[vk.1]'hZv_len
        have hzu_le : zu ≤ 1 := hZbit.2.1 uk
        have hzv_le : zv ≤ 1 := hZbit.2.1 vk
        have hzu_w : zu < 2 ^ w := by omega
        have hzv_w : zv < 2 ^ w := by omega
        have hsum_w : zu + zv < 2 ^ w := by omega
        let s₅ := s₄.setReg 16 zu
        have hex_rd12a : Exec w (.assign 16 (.read 12 (.reg 12))) s₄ s₅ 3 :=
          .assign (by
            simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, huk_w, hZu_len, zu, hzu_w])
        let s₆ := s₅.setReg 17 zv
        have hex_rd12b : Exec w (.assign 17 (.read 12 (.reg 13))) s₅ s₆ 3 :=
          .assign (by
            simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hvk_w, hZv_len, zv, hzv_w])
        by_cases hinc_k : uk ∈ Z ∨ vk ∈ Z
        · have hsum_ne0 : zu + zv ≠ 0 := by
            rcases hinc_k with hu | hv
            · have := (hZbit.2.2 uk).mpr hu; omega
            · have := (hZbit.2.2 vk).mpr hv; omega
          have hcond_sum : (Expr.op .add (.reg 16) (.reg 17)).eval w s₆ = some (zu + zv) := by
            simp [s₆, s₅, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hzu_w, hzv_w, hsum_w]
          let s₇ := s₆.setReg 9 k
          have hex_set9 : Exec w (.assign 9 (.reg 11)) s₆ s₇ 2 :=
            .assign (by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w])
          have hex_ite_sum : Exec w (.ite (.op .add (.reg 16) (.reg 17)) (.assign 9 (.reg 11)) .skip)
              s₆ s₇ 5 := .ite_true hcond_sum hsum_ne0 hex_set9
          have hex_body : Exec w selectCandPass2Body s s₇ 27 :=
            .seq hex_rd4 (.ite_true hcond14 hal_k_ne0
              (.seq hex_rd5 (.ite_true hcond15 (by omega)
                (.seq hex_rd2 (.seq hex_rd3 (.seq hex_rd12a (.seq hex_rd12b hex_ite_sum)))))))
          let s₈ := s₇.setReg 11 (k + 1)
          have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₇ s₈ 4 :=
            .assign (by
              simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw,
                checkWord, hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
          have hjk_inc : ∃ z ∈ Z, z ∈ symEdgeAt edges jk := by
            rcases hinc_k with hu | hv
            · refine ⟨uk, hu, ?_⟩
              unfold symEdgeAt; rw [Sym2.mem_iff]; exact Or.inl rfl
            · refine ⟨vk, hv, ?_⟩
              unfold symEdgeAt; rw [Sym2.mem_iff]; exact Or.inr rfl
          have hinv₈ : ∃ g_idx : Fin edges.length,
              s₈.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v ∧
              ((∃ z ∈ Z, z ∈ symEdgeAt edges g_idx) ∨
               (∀ j : Fin edges.length, j.1 < k + 1 → j ∈ aliveSet → f_tau j = v →
                 ∀ z ∈ Z, z ∉ symEdgeAt edges j)) :=
            ⟨jk, by simp [s₈, s₇, jk], hmem_k, hwk_eq, Or.inl hjk_inc⟩
          rcases ih (k + 1) (by omega) (s := s₈)
              ⟨heu_len, hev_len, hend_all⟩
              (hal.of_arr_eq rfl) (htau.of_arr_eq rfl) (hZbit.of_arr_eq rfl)
              (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr2])
              (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr7])
              (by simp [s₈]) hinv₈ with
            ⟨s₉, t₉, hex₉, ht₉, hres₉, harr₉, hreg₉⟩
          refine ⟨s₉, 3 + (27 + 4) + t₉,
            .while_true hcond (by omega) (.seq hex_body hex_inc) hex₉,
            by omega, hres₉, harr₉,
            fun r hr9 hr11' hr12 hr13 hr14 hr15 hr16 hr17 => by
              rw [hreg₉ r hr9 hr11' hr12 hr13 hr14 hr15 hr16 hr17]
              simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
                hr11', hr9, hr17, hr16, hr13, hr12, hr15, hr14]⟩
        · have hsum_eq0 : zu + zv = 0 := by
            have hzu0 : zu = 0 := by
              by_contra hne
              exact hinc_k (Or.inl ((hZbit.2.2 uk).mp hne))
            have hzv0 : zv = 0 := by
              by_contra hne
              exact hinc_k (Or.inr ((hZbit.2.2 vk).mp hne))
            omega
          have hcond_sum : (Expr.op .add (.reg 16) (.reg 17)).eval w s₆ = some 0 := by
            simp [s₆, s₅, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hzu_w, hzv_w, hsum_eq0, h0_w]
          have hex_ite_sum : Exec w (.ite (.op .add (.reg 16) (.reg 17)) (.assign 9 (.reg 11)) .skip)
              s₆ s₆ 4 := .ite_false hcond_sum (.skip s₆)
          have hex_body : Exec w selectCandPass2Body s s₆ 26 :=
            .seq hex_rd4 (.ite_true hcond14 hal_k_ne0
              (.seq hex_rd5 (.ite_true hcond15 (by omega)
                (.seq hex_rd2 (.seq hex_rd3 (.seq hex_rd12a (.seq hex_rd12b hex_ite_sum)))))))
          let s₇ := s₆.setReg 11 (k + 1)
          have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₆ s₇ 4 :=
            .assign (by
              simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw,
                checkWord, hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
          have hinv₇ : ∃ g_idx : Fin edges.length,
              s₇.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v ∧
              ((∃ z ∈ Z, z ∈ symEdgeAt edges g_idx) ∨
               (∀ j : Fin edges.length, j.1 < k + 1 → j ∈ aliveSet → f_tau j = v →
                 ∀ z ∈ Z, z ∉ symEdgeAt edges j)) := by
            rcases hinv with ⟨g_idx, hr9, hg_al, hg_v, hinc | hnone⟩
            · exact ⟨g_idx, by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr9], hg_al, hg_v, Or.inl hinc⟩
            · refine ⟨g_idx, by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr9], hg_al, hg_v,
                Or.inr (fun j hj hj_al hfv z hz hz_mem => ?_)⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
              · exact hnone j hlt hj_al hfv z hz hz_mem
              · have hjk : j = jk := Fin.ext heq
                subst hjk
                unfold symEdgeAt at hz_mem
                rw [Sym2.mem_iff] at hz_mem
                rcases hz_mem with rfl | rfl
                · exact hinc_k (Or.inl hz)
                · exact hinc_k (Or.inr hz)
          rcases ih (k + 1) (by omega) (s := s₇)
              ⟨heu_len, hev_len, hend_all⟩
              (hal.of_arr_eq rfl) (htau.of_arr_eq rfl) (hZbit.of_arr_eq rfl)
              (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr2])
              (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr7])
              (by simp [s₇]) hinv₇ with
            ⟨s₈, t₈, hex₈, ht₈, hres₈, harr₈, hreg₈⟩
          refine ⟨s₈, 3 + (26 + 4) + t₈,
            .while_true hcond (by omega) (.seq hex_body hex_inc) hex₈,
            by omega, hres₈, harr₈,
            fun r hr9 hr11' hr12 hr13 hr14 hr15 hr16 hr17 => by
              rw [hreg₈ r hr9 hr11' hr12 hr13 hr14 hr15 hr16 hr17]
              simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁,
                hr11', hr17, hr16, hr13, hr12, hr15, hr14]⟩
      · have hwk_ne_val : wk.1 ≠ v.1 := fun h => hwk_eq (Fin.ext h)
        have hcond15 : (Expr.op .eq (.reg 15) (.reg 7)).eval w s₂ = some 0 := by
          simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr7, hwk_ne_val, hwk_w, hv_w, h0_w]
        have hex_body : Exec w selectCandPass2Body s s₂ 11 :=
          .seq hex_rd4 (.ite_true hcond14 hal_k_ne0
            (.seq hex_rd5 (.ite_false hcond15 (.skip s₂))))
        let s₃ := s₂.setReg 11 (k + 1)
        have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₂ s₃ 4 :=
          .assign (by
            simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
        have hinv₃ : ∃ g_idx : Fin edges.length,
            s₃.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v ∧
            ((∃ z ∈ Z, z ∈ symEdgeAt edges g_idx) ∨
             (∀ j : Fin edges.length, j.1 < k + 1 → j ∈ aliveSet → f_tau j = v →
               ∀ z ∈ Z, z ∉ symEdgeAt edges j)) := by
          rcases hinv with ⟨g_idx, hr9, hg_al, hg_v, hinc | hnone⟩
          · exact ⟨g_idx, by simp [s₃, s₂, s₁, hr9], hg_al, hg_v, Or.inl hinc⟩
          · refine ⟨g_idx, by simp [s₃, s₂, s₁, hr9], hg_al, hg_v,
              Or.inr (fun j hj hj_al hfv => ?_)⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
            · exact hnone j hlt hj_al hfv
            · exfalso
              have hjk : j = jk := Fin.ext heq
              subst hjk
              exact hwk_eq hfv
        rcases ih (k + 1) (by omega) (s := s₃)
            (hend.of_arrs_eq rfl rfl) (hal.of_arr_eq rfl) (htau.of_arr_eq rfl) (hZbit.of_arr_eq rfl)
            (by simp [s₃, s₂, s₁, hr2])
            (by simp [s₃, s₂, s₁, hr7])
            (by simp [s₃]) hinv₃ with
          ⟨s₄, t₄, hex₄, ht₄, hres₄, harr₄, hreg₄⟩
        refine ⟨s₄, 3 + (11 + 4) + t₄,
          .while_true hcond (by omega) (.seq hex_body hex_inc) hex₄,
          by omega, hres₄, harr₄,
          fun r hr9 hr11' hr12 hr13 hr14 hr15 hr16 hr17 => by
            rw [hreg₄ r hr9 hr11' hr12 hr13 hr14 hr15 hr16 hr17]
            simp [s₃, s₂, s₁, hr11', hr15, hr14]⟩
    · have hal_k_eq0 : al_k = 0 := by
        by_contra hne
        exact hmem_k ((hal.2.2 jk).mp hne)
      have hcond14 : (Expr.reg 14).eval w s₁ = some 0 := by
        simp [s₁, Expr.eval, checkWord, hal_k_eq0, h0_w]
      have hex_body : Exec w selectCandPass2Body s s₁ 5 :=
        .seq hex_rd4 (.ite_false hcond14 (.skip s₁))
      let s₂ := s₁.setReg 11 (k + 1)
      have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₁ s₂ 4 :=
        .assign (by
          simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
      have hinv₂ : ∃ g_idx : Fin edges.length,
          s₂.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v ∧
          ((∃ z ∈ Z, z ∈ symEdgeAt edges g_idx) ∨
           (∀ j : Fin edges.length, j.1 < k + 1 → j ∈ aliveSet → f_tau j = v →
             ∀ z ∈ Z, z ∉ symEdgeAt edges j)) := by
        rcases hinv with ⟨g_idx, hr9, hg_al, hg_v, hinc | hnone⟩
        · exact ⟨g_idx, by simp [s₂, s₁, hr9], hg_al, hg_v, Or.inl hinc⟩
        · refine ⟨g_idx, by simp [s₂, s₁, hr9], hg_al, hg_v,
            Or.inr (fun j hj hj_al hfv => ?_)⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
          · exact hnone j hlt hj_al hfv
          · exfalso
            have hjk : j = jk := Fin.ext heq
            subst hjk
            exact hmem_k hj_al
      rcases ih (k + 1) (by omega) (s := s₂)
          (hend.of_arrs_eq rfl rfl) (hal.of_arr_eq rfl) (htau.of_arr_eq rfl) (hZbit.of_arr_eq rfl)
          (by simp [s₂, s₁, hr2])
          (by simp [s₂, s₁, hr7])
          (by simp [s₂]) hinv₂ with
        ⟨s₃, t₃, hex₃, ht₃, hres₃, harr₃, hreg₃⟩
      refine ⟨s₃, 3 + (5 + 4) + t₃,
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₃,
        by omega, hres₃, harr₃,
        fun r hr9 hr11' hr12 hr13 hr14 hr15 hr16 hr17 => by
          rw [hreg₃ r hr9 hr11' hr12 hr13 hr14 hr15 hr16 hr17]
          simp [s₂, s₁, hr11', hr14]⟩

theorem selectCandEdgeProg_exec {w n t : ℕ} (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t) (v : Fin t)
    (hex_v : ∃ i₀ ∈ aliveSet, f_tau i₀ = v)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : edges.length < 2 ^ w) (ht_w : t < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hZbit : IsBitSet (leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
      (tauOfArr edges t ht_pos f_tau) v) 12 s)
    (hr2 : s.regs 2 = edges.length)
    (hr7 : s.regs 7 = v.1) :
    let Z := leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v
    ∃ s' t_steps,
      Exec w selectCandEdgeProg s s' t_steps ∧
      t_steps ≤ 53 * edges.length + 12 ∧
      (∃ g_idx : Fin edges.length,
        s'.regs 9 = g_idx.1 ∧ g_idx ∈ aliveSet ∧ f_tau g_idx = v ∧
        (Z.Nonempty → ∃ z ∈ Z, z ∈ symEdgeAt edges g_idx)) ∧
      s'.arrs = s.arrs ∧
      (∀ r : Reg, r ≠ 9 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
        s'.regs r = s.regs r) := by
  intro Z
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 11 0
  have hex₁ : Exec w (.assign 11 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases selectCandPass1Loop_exec aliveSet f_tau v hw hm2_w ht_w edges.length 0 (by omega)
      (s := s₁)
      (hal.of_arr_eq rfl) (htau.of_arr_eq rfl)
      (by simp [s₁, hr2]) (by simp [s₁, hr7]) (by simp [s₁])
      (Or.inr (fun _ hj => absurd hj (by omega))) with
    ⟨s₂, t₂, hex₂, ht₂, hres₂, harr₂, hreg₂⟩
  have hg₀ : ∃ g₀ : Fin edges.length, s₂.regs 9 = g₀.1 ∧ g₀ ∈ aliveSet ∧ f_tau g₀ = v := by
    rcases hres₂ with hfound | hnone
    · exact hfound
    · rcases hex_v with ⟨i₀, hi₀_al, hi₀_v⟩
      exact absurd hi₀_v (hnone i₀ hi₀_al)
  let s₃ := s₂.setReg 11 0
  have hex₃ : Exec w (.assign 11 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases hg₀ with ⟨g₀, hr9_2, hg₀_al, hg₀_v⟩
  rcases selectCandPass2Loop_exec edges aliveSet f_tau v Z hw2 hn_w hm2_w ht_w
      edges.length 0 (by omega)
      (s := s₃)
      (hend.of_arrs_eq (by simp [s₃, harr₂, s₁]) (by simp [s₃, harr₂, s₁]))
      (hal.of_arr_eq (by simp [s₃, harr₂, s₁]))
      (htau.of_arr_eq (by simp [s₃, harr₂, s₁]))
      (hZbit.of_arr_eq (by simp [s₃, harr₂, s₁]))
      (by simp [s₃, hreg₂ 2 (by decide) (by decide) (by decide) (by decide), s₁, hr2])
      (by simp [s₃, hreg₂ 7 (by decide) (by decide) (by decide) (by decide), s₁, hr7])
      (by simp [s₃])
      ⟨g₀, by simp [s₃, hr9_2], hg₀_al, hg₀_v,
        Or.inr (fun _ hj => absurd hj (by omega))⟩ with
    ⟨s₄, t₄, hex₄, ht₄, ⟨g_idx, hr9_4, hg_al, hg_v, hinc_or⟩, harr₄, hreg₄⟩
  have hg_inc : Z.Nonempty → ∃ z ∈ Z, z ∈ symEdgeAt edges g_idx := by
    intro ⟨z, hz⟩
    rcases hinc_or with hinc | hnone
    · exact hinc
    · exfalso
      have hz_filt : z ∈ leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
          (tauOfArr edges t ht_pos f_tau) v := hz
      rw [mem_leafCutVerts] at hz_filt
      rcases hz_filt.1 with ⟨e, he_mem, hz_mem, hj_tau⟩
      rw [mem_edgeFinset_graphOfAlive_iff hedges] at he_mem
      rcases he_mem with ⟨j, hj_al, rfl⟩
      rw [tauOfArr_symEdgeAt hedges] at hj_tau
      exact hnone j hj_al hj_tau z hz hz_mem
  refine ⟨s₄, 2 + (t₂ + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, ⟨g_idx, hr9_4, hg_al, hg_v, hg_inc⟩,
    by simp [harr₄, s₃, harr₂, s₁],
    fun r hr9 hr11 hr12 hr13 hr14 hr15 hr16 hr17 => by
      rw [hreg₄ r hr9 hr11 hr12 hr13 hr14 hr15 hr16 hr17]
      simp [s₃, hr11, hreg₂ r hr9 hr11 hr14 hr15, s₁]⟩

/-! ### Section 4: Step (3) (`|Z| < 3ω`), Leaf Splitting Program (`step3Prog`) -/

/-- Command splitting leaf `v = r_7` in `a_parent = 6` into `t = r_4` and `t + 1 = r_4 + 1`,
then advancing `r_4 := r_4 + 2`. Used in both Step (3) and Step (5). -/
def splitParentCmd : Cmd :=
  .seq (.write 6 (.reg 4) (.reg 7))
    (.seq (.write 6 (.op .add (.reg 4) (.const 1)) (.reg 7))
      (.assign 4 (.op .add (.reg 4) (.const 2))))

theorem splitParentCmd_exec {w m₂ t : ℕ} (p : ℕ → ℕ) (v : Fin t)
    (ht_le : t + 2 ≤ 2 * m₂)
    (hw2 : 2 < 2 ^ w) (ht2_w : t + 2 < 2 ^ w)
    {s : State}
    (hpar : IsParentArr m₂ t p 6 s)
    (hr4 : s.regs 4 = t)
    (hr7 : s.regs 7 = v.1) :
    ∃ s',
      Exec w splitParentCmd s s' 12 ∧
      IsParentArr m₂ (t + 2) (splitLeafParent p t v.1) 6 s' ∧
      s'.regs 4 = t + 2 ∧
      (∀ a : Arr, a ≠ 6 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 4 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have ht_w : t < 2 ^ w := by omega
  have ht1_w : t + 1 < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  rcases hpar with ⟨hlen6, _, hall6, hp6⟩
  let s₁ := s.writeArr 6 t v.1
  have hex₁ : Exec w (.write 6 (.reg 4) (.reg 7)) s s₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hr4, ht_w])
      (by simp [Expr.eval, checkWord, hr7, hv_w])
      (by omega)
  let s₂ := s₁.writeArr 6 (t + 1) v.1
  have hex₂ : Exec w (.write 6 (.op .add (.reg 4) (.const 1)) (.reg 7)) s₁ s₂ 5 :=
    .write (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, ht_w, hw, ht1_w])
      (by simp [s₁, Expr.eval, checkWord, hr7, hv_w])
      (by simp [s₁]; omega)
  let s₃ := s₂.setReg 4 (t + 2)
  have hex₃ : Exec w (.assign 4 (.op .add (.reg 4) (.const 2))) s₂ s₃ 4 :=
    .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, ht_w, hw2, ht2_w])
  refine ⟨s₃, .seq hex₁ (.seq hex₂ hex₃), ?_, by simp [s₃],
    fun a ha6 => by simp [s₃, s₂, s₁, ha6],
    fun r hr4' => by simp [s₃, s₂, s₁, hr4']⟩
  have h6_eq : s₃.arrs 6 = ((s.arrs 6).set t v.1).set (t + 1) v.1 := by simp [s₃, s₂, s₁]
  refine ⟨by simp [h6_eq, hlen6], ht_le, fun z hz => ?_, splitLeafParent_lt hp6 v.2⟩
  simp only [h6_eq, splitLeafParent]
  by_cases hzt1 : z = t + 1
  · subst hzt1
    rw [List.getElem_set_self]
    simp
  · rw [List.getElem_set_ne (Ne.symm hzt1)]
    by_cases hzt : z = t
    · subst hzt
      rw [List.getElem_set_self]
      simp
    · rw [List.getElem_set_ne (Ne.symm hzt)]
      have hz_lt : z < t := by omega
      simp [hzt, hzt1, hall6 z hz_lt]

/-- Updated leaf assignment `f_tau` in Step (3): maps `g_idx` to `t`, all other `k` with
`f_tau k = v` to `t + 1`, and leaves all `k` with `f_tau k ≠ v` unchanged. -/
def step3FTau {m₂ t : ℕ} (f_tau : Fin m₂ → Fin t) (v : Fin t) (g_idx : Fin m₂)
    (k : Fin m₂) : Fin (t + 2) :=
  if f_tau k = v then
    if k = g_idx then ⟨t, by omega⟩ else ⟨t + 1, by omega⟩
  else
    ⟨(f_tau k).1, by have := (f_tau k).2; omega⟩

/-- Partial update of `f_tau` up to index `idx` in `step3Loop`. -/
def step3FTauUpTo {m₂ t : ℕ} (f_tau : Fin m₂ → Fin t) (v : Fin t) (g_idx : Fin m₂)
    (idx : ℕ) (k : Fin m₂) : Fin (t + 2) :=
  if k.1 < idx then
    step3FTau f_tau v g_idx k
  else
    ⟨(f_tau k).1, by have := (f_tau k).2; omega⟩

/-- Loop body of `step3Prog`: if `a_tau[r_11] == r_7`, sets `a_tau[r_11] := r_4` when `r_11 == r_9`
and `a_tau[r_11] := r_4 + 1` otherwise. -/
def step3LoopBody : Cmd :=
  .seq (.assign 15 (.read 5 (.reg 11)))
    (.ite (.op .eq (.reg 15) (.reg 7))
      (.ite (.op .eq (.reg 11) (.reg 9))
        (.write 5 (.reg 11) (.reg 4))
        (.write 5 (.reg 11) (.op .add (.reg 4) (.const 1))))
      .skip)

/-- Step (3) program (`|Z| < 3ω`): updates `a_tau = 5` via `step3LoopBody` and splits `v = r_7`
in `a_parent = 6` via `splitParentCmd`. -/
def step3Prog : Cmd :=
  .seq (.assign 11 (.const 0))
    (.seq (forUp 11 (.reg 2) step3LoopBody)
      splitParentCmd)

theorem step3Loop_exec {w m₂ t : ℕ} (f_tau : Fin m₂ → Fin t) (v : Fin t) (g_idx : Fin m₂)
    (hw : 1 < 2 ^ w) (hm2_w : m₂ < 2 ^ w) (ht1_w : t + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = m₂) {s : State}
    (htau : IsTauArr (step3FTauUpTo f_tau v g_idx k) 5 s)
    (hr2 : s.regs 2 = m₂)
    (hr4 : s.regs 4 = t)
    (hr7 : s.regs 7 = v.1)
    (hr9 : s.regs 9 = g_idx.1)
    (hr11 : s.regs 11 = k) :
    ∃ s' t_steps,
      Exec w (forUp 11 (.reg 2) step3LoopBody) s s' t_steps ∧
      t_steps ≤ 3 + 21 * rem ∧
      IsTauArr (step3FTau f_tau v g_idx) 5 s' ∧
      (∀ a : Arr, a ≠ 5 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 15 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have ht_w : t < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  have hg_w : g_idx.1 < 2 ^ w := by have := g_idx.2; omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = m₂ := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hm2_w, h0_w]
    have htau_eq : step3FTauUpTo f_tau v g_idx k = step3FTau f_tau v g_idx := by
      ext j; simp [step3FTauUpTo, j.2]
    rw [htau_eq] at htau
    exact ⟨s, 3, .while_false hcond, by omega, htau, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < m₂ := by omega
    have hk_w : k < 2 ^ w := by omega
    let jk : Fin m₂ := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hk_w, hm2_w, hk_lt, hw]
    rcases htau with ⟨htau_len, htau_all⟩
    have htau_k : (s.arrs 5)[k]'(by rw [htau_len]; exact hk_lt) = (f_tau jk).1 := by
      have := htau_all jk
      simpa [step3FTauUpTo, jk] using this
    let wk := f_tau jk
    have hwk_w : wk.1 < 2 ^ w := by have := wk.2; omega
    let s₁ := s.setReg 15 wk.1
    have hex_rd5 : Exec w (.assign 15 (.read 5 (.reg 11))) s s₁ 3 :=
      .assign (by
        simp [Expr.eval, checkWord, hr11, hk_w,
          show k < (s.arrs 5).length by rw [htau_len]; exact hk_lt, htau_k, wk, hwk_w])
    by_cases hwk_eq : wk = v
    · have hwk_val : wk.1 = v.1 := congrArg Fin.val hwk_eq
      have hcond15 : (Expr.op .eq (.reg 15) (.reg 7)).eval w s₁ = some 1 := by
        simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr7, hwk_val, hv_w, hw]
      by_cases hkg : jk = g_idx
      · have hkg_val : k = g_idx.1 := congrArg Fin.val hkg
        have hcond9 : (Expr.op .eq (.reg 11) (.reg 9)).eval w s₁ = some 1 := by
          simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr11, hr9, hkg_val, hg_w, hw]
        let s₂ := s₁.writeArr 5 k t
        have hex_wr5 : Exec w (.write 5 (.reg 11) (.reg 4)) s₁ s₂ 3 :=
          .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w])
            (by simp [s₁, State.setReg, Expr.eval, checkWord, hr4, ht_w])
            (by simp [s₁, htau_len, hk_lt])
        have hex_ite9 : Exec w (.ite (.op .eq (.reg 11) (.reg 9))
            (.write 5 (.reg 11) (.reg 4))
            (.write 5 (.reg 11) (.op .add (.reg 4) (.const 1)))) s₁ s₂ 6 :=
          .ite_true hcond9 (by omega) hex_wr5
        have hex_body : Exec w step3LoopBody s s₂ 12 :=
          .seq hex_rd5 (.ite_true hcond15 (by omega) hex_ite9)
        let s₃ := s₂.setReg 11 (k + 1)
        have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₂ s₃ 4 :=
          .assign (by
            simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
        have htau₃ : IsTauArr (step3FTauUpTo f_tau v g_idx (k + 1)) 5 s₃ := by
          have h5_eq : s₃.arrs 5 = (s.arrs 5).set k t := by simp [s₃, s₂, s₁]
          refine ⟨by simp [h5_eq, htau_len], fun j => ?_⟩
          simp only [h5_eq, step3FTauUpTo]
          by_cases hjk : j.1 = k
          · have hj_eq : j = jk := Fin.ext hjk
            subst hj_eq
            have hfg : f_tau g_idx = v := hkg ▸ hwk_eq
            simp [jk, step3FTau, hfg, hkg]
          · rw [List.getElem_set_ne (Ne.symm hjk)]
            have hprev := htau_all j
            simp only [step3FTauUpTo] at hprev
            by_cases hj_lt : j.1 < k
            · have hj_lt1 : j.1 < k + 1 := by omega
              simpa [hj_lt, hj_lt1] using hprev
            · have hj_nlt1 : ¬ j.1 < k + 1 := by omega
              simpa [hj_lt, hj_nlt1] using hprev
        rcases ih (k + 1) (by omega) (s := s₃) htau₃
            (by simp [s₃, s₂, s₁, hr2])
            (by simp [s₃, s₂, s₁, hr4])
            (by simp [s₃, s₂, s₁, hr7])
            (by simp [s₃, s₂, s₁, hr9])
            (by simp [s₃]) with
          ⟨s₄, t₄, hex₄, ht₄, htau₄, harr₄, hreg₄⟩
        refine ⟨s₄, 3 + (12 + 4) + t₄,
          .while_true hcond (by omega) (.seq hex_body hex_inc) hex₄,
          by omega, htau₄,
          fun a ha5 => by rw [harr₄ a ha5]; simp [s₃, s₂, s₁, ha5],
          fun r hr11' hr15 => by
            rw [hreg₄ r hr11' hr15]
            simp [s₃, s₂, s₁, hr11', hr15]⟩
      · have hkg_ne_val : k ≠ g_idx.1 := fun h => hkg (Fin.ext h)
        have hcond9 : (Expr.op .eq (.reg 11) (.reg 9)).eval w s₁ = some 0 := by
          simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr11, hr9, hkg_ne_val, hk_w, hg_w, h0_w]
        let s₂ := s₁.writeArr 5 k (t + 1)
        have hex_wr5 : Exec w (.write 5 (.reg 11) (.op .add (.reg 4) (.const 1))) s₁ s₂ 5 :=
          .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hr11, hk_w])
            (by simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr4, ht_w, hw, ht1_w])
            (by simp [s₁, htau_len, hk_lt])
        have hex_ite9 : Exec w (.ite (.op .eq (.reg 11) (.reg 9))
            (.write 5 (.reg 11) (.reg 4))
            (.write 5 (.reg 11) (.op .add (.reg 4) (.const 1)))) s₁ s₂ 8 :=
          .ite_false hcond9 hex_wr5
        have hex_body : Exec w step3LoopBody s s₂ 14 :=
          .seq hex_rd5 (.ite_true hcond15 (by omega) hex_ite9)
        let s₃ := s₂.setReg 11 (k + 1)
        have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₂ s₃ 4 :=
          .assign (by
            simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
        have htau₃ : IsTauArr (step3FTauUpTo f_tau v g_idx (k + 1)) 5 s₃ := by
          have h5_eq : s₃.arrs 5 = (s.arrs 5).set k (t + 1) := by simp [s₃, s₂, s₁]
          refine ⟨by simp [h5_eq, htau_len], fun j => ?_⟩
          simp only [h5_eq, step3FTauUpTo]
          by_cases hjk : j.1 = k
          · have hj_eq : j = jk := Fin.ext hjk
            subst hj_eq
            have hfk : f_tau jk = v := hwk_eq
            simp [jk, step3FTau, hfk, hkg]
          · rw [List.getElem_set_ne (Ne.symm hjk)]
            have hprev := htau_all j
            simp only [step3FTauUpTo] at hprev
            by_cases hj_lt : j.1 < k
            · have hj_lt1 : j.1 < k + 1 := by omega
              simpa [hj_lt, hj_lt1] using hprev
            · have hj_nlt1 : ¬ j.1 < k + 1 := by omega
              simpa [hj_lt, hj_nlt1] using hprev
        rcases ih (k + 1) (by omega) (s := s₃) htau₃
            (by simp [s₃, s₂, s₁, hr2])
            (by simp [s₃, s₂, s₁, hr4])
            (by simp [s₃, s₂, s₁, hr7])
            (by simp [s₃, s₂, s₁, hr9])
            (by simp [s₃]) with
          ⟨s₄, t₄, hex₄, ht₄, htau₄, harr₄, hreg₄⟩
        refine ⟨s₄, 3 + (14 + 4) + t₄,
          .while_true hcond (by omega) (.seq hex_body hex_inc) hex₄,
          by omega, htau₄,
          fun a ha5 => by rw [harr₄ a ha5]; simp [s₃, s₂, s₁, ha5],
          fun r hr11' hr15 => by
            rw [hreg₄ r hr11' hr15]
            simp [s₃, s₂, s₁, hr11', hr15]⟩
    · have hwk_ne_val : wk.1 ≠ v.1 := fun h => hwk_eq (Fin.ext h)
      have hcond15 : (Expr.op .eq (.reg 15) (.reg 7)).eval w s₁ = some 0 := by
        simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr7, hwk_ne_val, hwk_w, hv_w, h0_w]
      have hex_body : Exec w step3LoopBody s s₁ 7 :=
        .seq hex_rd5 (.ite_false hcond15 (.skip s₁))
      let s₂ := s₁.setReg 11 (k + 1)
      have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₁ s₂ 4 :=
        .assign (by
          simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
      have htau₂ : IsTauArr (step3FTauUpTo f_tau v g_idx (k + 1)) 5 s₂ := by
        refine ⟨by simp [s₂, s₁, htau_len], fun j => ?_⟩
        have hprev := htau_all j
        simp only [s₂, s₁, State.setReg_arrs, step3FTauUpTo] at hprev ⊢
        by_cases hjk : j.1 = k
        · have hj_eq : j = jk := Fin.ext hjk
          subst hj_eq
          have hfk : f_tau jk ≠ v := hwk_eq
          simpa [jk, step3FTau, hfk] using hprev
        · by_cases hj_lt : j.1 < k
          · have hj_lt1 : j.1 < k + 1 := by omega
            simpa [hj_lt, hj_lt1] using hprev
          · have hj_nlt1 : ¬ j.1 < k + 1 := by omega
            simpa [hj_lt, hj_nlt1] using hprev
      rcases ih (k + 1) (by omega) (s := s₂) htau₂
          (by simp [s₂, s₁, hr2])
          (by simp [s₂, s₁, hr4])
          (by simp [s₂, s₁, hr7])
          (by simp [s₂, s₁, hr9])
          (by simp [s₂]) with
        ⟨s₃, t₃, hex₃, ht₃, htau₃, harr₃, hreg₃⟩
      refine ⟨s₃, 3 + (7 + 4) + t₃,
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₃,
        by omega, htau₃,
        fun a ha5 => by rw [harr₃ a ha5]; rfl,
        fun r hr11' hr15 => by
          rw [hreg₃ r hr11' hr15]
          simp [s₂, s₁, hr11', hr15]⟩

theorem step3Prog_exec {w n t ω : ℕ} (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (p : ℕ → ℕ) (v : Fin t) (g_idx : Fin edges.length)
    (hpart : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
      (parentTree t p) (tauOfArr edges t ht_pos f_tau))
    (hv_leaf : v ∈ treeLeaves (parentTree t p))
    (hZ_lt : (leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
      (tauOfArr edges t ht_pos f_tau) v).card < 3 * ω)
    (hg_al : g_idx ∈ aliveSet) (hg_v : f_tau g_idx = v)
    (hother : ∃ j₀ ∈ aliveSet, j₀ ≠ g_idx ∧ f_tau j₀ = v)
    (hg_inc : (leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
      (tauOfArr edges t ht_pos f_tau) v).Nonempty →
      ∃ z ∈ leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
        (tauOfArr edges t ht_pos f_tau) v, z ∈ symEdgeAt edges g_idx)
    (ht_le : t + 2 ≤ 2 * edges.length)
    (hw2 : 2 < 2 ^ w) (hm2_w : edges.length < 2 ^ w) (ht2_w : t + 2 < 2 ^ w)
    {s : State}
    (htau : IsTauArr f_tau 5 s)
    (hpar : IsParentArr edges.length t p 6 s)
    (hr2 : s.regs 2 = edges.length)
    (hr4 : s.regs 4 = t)
    (hr7 : s.regs 7 = v.1)
    (hr9 : s.regs 9 = g_idx.1) :
    ∃ s' t_steps,
      Exec w step3Prog s s' t_steps ∧
      t_steps ≤ 21 * edges.length + 20 ∧
      IsTauArr (step3FTau f_tau v g_idx) 5 s' ∧
      IsParentArr edges.length (t + 2) (splitLeafParent p t v.1) 6 s' ∧
      IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
        (parentTree (t + 2) (splitLeafParent p t v.1))
        (tauOfArr edges (t + 2) (by omega) (step3FTau f_tau v g_idx)) ∧
      s'.regs 4 = t + 2 ∧
      (∀ a : Arr, a ≠ 5 → a ≠ 6 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 4 → r ≠ 11 → r ≠ 15 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have ht1_w : t + 1 < 2 ^ w := by omega
  let s₁ := s.setReg 11 0
  have hex₁ : Exec w (.assign 11 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have htau₁ : IsTauArr (step3FTauUpTo f_tau v g_idx 0) 5 s₁ := by
    rcases htau with ⟨hlen, hall⟩
    exact ⟨hlen, fun k => by simp [s₁, step3FTauUpTo, hall k]⟩
  rcases step3Loop_exec f_tau v g_idx hw hm2_w ht1_w edges.length 0 (by omega)
      (s := s₁) htau₁
      (by simp [s₁, hr2]) (by simp [s₁, hr4]) (by simp [s₁, hr7]) (by simp [s₁, hr9])
      (by simp [s₁]) with
    ⟨s₂, t₂, hex₂, ht₂, htau₂, harr₂, hreg₂⟩
  rcases splitParentCmd_exec p v ht_le hw2 ht2_w
      (s := s₂)
      (hpar.of_arr_eq (by rw [harr₂ 6 (by decide)]; rfl))
      (by rw [hreg₂ 4 (by decide) (by decide)]; simp [s₁, hr4])
      (by rw [hreg₂ 7 (by decide) (by decide)]; simp [s₁, hr7]) with
    ⟨s₃, hex₃, hpar₃, hr4_3, harr₃, hreg₃⟩
  have hp : ∀ z, 0 < z → z < t → p z < z := hpar.2.2.2
  have hg_mem : symEdgeAt edges g_idx ∈ (graphOfAlive edges hedges.1 aliveSet).edgeFinset := by
    rw [mem_edgeFinset_graphOfAlive_iff hedges]
    exact ⟨g_idx, hg_al, rfl⟩
  have hτ_g : tauOfArr edges t ht_pos f_tau (symEdgeAt edges g_idx) = v := by
    rw [tauOfArr_symEdgeAt hedges, hg_v]
  rcases hother with ⟨j₀, hj₀_al, hj₀_ne, hj₀_v⟩
  have hother_edge : ∃ e' ∈ (graphOfAlive edges hedges.1 aliveSet).edgeFinset,
      tauOfArr edges t ht_pos f_tau e' = v ∧ e' ≠ symEdgeAt edges g_idx := by
    refine ⟨symEdgeAt edges j₀, ?_, ?_, ?_⟩
    · rw [mem_edgeFinset_graphOfAlive_iff hedges]; exact ⟨j₀, hj₀_al, rfl⟩
    · rw [tauOfArr_symEdgeAt hedges, hj₀_v]
    · intro heq; exact hj₀_ne (symEdgeAt_injective hedges heq)
  have hpart' : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
      (parentTree (t + 2) (splitLeafParent p t v.1))
      (tauOfArr edges (t + 2) (by omega) (step3FTau f_tau v g_idx)) := by
    apply isPartialBranchDecomp_step3 ht_pos hp hpart hv_leaf hZ_lt hg_mem hτ_g
      hother_edge hg_inc
    · intro e he hne_v
      rw [mem_edgeFinset_graphOfAlive_iff hedges] at he
      rcases he with ⟨k, _, rfl⟩
      rw [tauOfArr_symEdgeAt hedges] at hne_v ⊢
      rw [tauOfArr_symEdgeAt hedges]
      simp [step3FTau, hne_v]
    · rw [tauOfArr_symEdgeAt hedges]
      simp [step3FTau, hg_v]
    · intro e he he_v he_ne
      rw [mem_edgeFinset_graphOfAlive_iff hedges] at he
      rcases he with ⟨k, _, rfl⟩
      rw [tauOfArr_symEdgeAt hedges] at he_v ⊢
      have hk_ne : k ≠ g_idx := fun h => he_ne (congrArg (symEdgeAt edges) h)
      simp [step3FTau, he_v, hk_ne]
  refine ⟨s₃, 2 + (t₂ + 12),
    .seq hex₁ (.seq hex₂ hex₃),
    by omega,
    htau₂.of_arr_eq (harr₃ 5 (by decide)),
    hpar₃, hpart', hr4_3,
    fun a ha5 ha6 => by rw [harr₃ a ha6, harr₂ a ha5]; rfl,
    fun r hr4' hr11 hr15 => by
      rw [hreg₃ r hr4', hreg₂ r hr11 hr15]
      simp [s₁, hr11]⟩

/-! ### Section 5: Steps (4)–(6), Subgraph CSR, Partition Search, Menger Calls, Split/Delete -/

/-! #### Subpart 5.1: Subgraph Edge List `subEdgesUpTo` and `buildSubgraphCsrProg` -/

/-- Whether edge `k : Fin edges.length` belongs to the restricted leaf graph `R \ Z`, that is,
`k ∈ aliveSet`, `f_tau k = v`, and neither endpoint of `edges[k]` lies in `Z`. -/
def isSubEdge {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z : Finset (Fin n)) (k : Fin edges.length) : Prop :=
  k ∈ aliveSet ∧ f_tau k = v ∧ (edges[k.1]).1 ∉ Z ∧ (edges[k.1]).2 ∉ Z

instance instDecidableIsSubEdge {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z : Finset (Fin n)) (k : Fin edges.length) :
    Decidable (isSubEdge edges aliveSet f_tau v Z k) := by
  unfold isSubEdge
  infer_instance

/-- List of edges of `R \ Z` accumulated from the first `m` entries of `edges`. -/
def subEdgesUpTo {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z : Finset (Fin n)) : ℕ → List (Fin n × Fin n)
  | 0 => []
  | m + 1 =>
    if hm : m < edges.length then
      if isSubEdge edges aliveSet f_tau v Z ⟨m, hm⟩ then
        subEdgesUpTo edges aliveSet f_tau v Z m ++ [edges[m]]
      else
        subEdgesUpTo edges aliveSet f_tau v Z m
    else
      subEdgesUpTo edges aliveSet f_tau v Z m

theorem length_subEdgesUpTo_le {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z : Finset (Fin n)) (m : ℕ) :
    (subEdgesUpTo edges aliveSet f_tau v Z m).length ≤ m := by
  induction m with
  | zero => simp [subEdgesUpTo]
  | succ m ih =>
    unfold subEdgesUpTo
    by_cases hm : m < edges.length
    · by_cases hsub : isSubEdge edges aliveSet f_tau v Z ⟨m, hm⟩
      · simp [hm, hsub]; omega
      · simp [hm, hsub]; omega
    · simp [hm]; omega

theorem getElem_subEdgesUpTo_origin {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z : Finset (Fin n)) (m : ℕ) :
    ∀ (i : ℕ) (hi : i < (subEdgesUpTo edges aliveSet f_tau v Z m).length),
      ∃ (k : ℕ) (hk : k < edges.length), k < m ∧
        isSubEdge edges aliveSet f_tau v Z ⟨k, hk⟩ ∧
        (subEdgesUpTo edges aliveSet f_tau v Z m)[i]'hi = edges[k] := by
  induction m with
  | zero => intro i hi; simp [subEdgesUpTo] at hi
  | succ m ih =>
    intro i hi
    unfold subEdgesUpTo at hi ⊢
    by_cases hm : m < edges.length
    · simp only [hm, ↓reduceDIte] at hi ⊢
      by_cases hsub : isSubEdge edges aliveSet f_tau v Z ⟨m, hm⟩
      · simp only [hsub, ↓reduceIte] at hi ⊢
        let L := subEdgesUpTo edges aliveSet f_tau v Z m
        have hi_len : i < L.length + 1 := by simpa [L] using hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi_len with hlt | rfl
        · rw [List.getElem_append_left hlt]
          rcases ih i hlt with ⟨k, hk, hkm, hk_sub, hget⟩
          exact ⟨k, hk, by omega, hk_sub, hget⟩
        · refine ⟨m, hm, by omega, hsub, ?_⟩
          rw [List.getElem_append_right (by rfl)]
          simp [L]
      · simp only [hsub, ↓reduceIte] at hi ⊢
        rcases ih i hi with ⟨k, hk, hkm, hk_sub, hget⟩
        exact ⟨k, hk, by omega, hk_sub, hget⟩
    · simp only [hm, ↓reduceDIte] at hi ⊢
      rcases ih i hi with ⟨k, hk, hkm, hk_sub, hget⟩
      exact ⟨k, hk, by omega, hk_sub, hget⟩

theorem getElem_subEdgesUpTo_lt_origin {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z : Finset (Fin n)) (m : ℕ) :
    ∀ (i j : ℕ) (hij : i < j) (hj : j < (subEdgesUpTo edges aliveSet f_tau v Z m).length),
      ∃ (k₁ k₂ : ℕ) (hk₁ : k₁ < edges.length) (hk₂ : k₂ < edges.length),
        k₁ < k₂ ∧ k₂ < m ∧
        (subEdgesUpTo edges aliveSet f_tau v Z m)[i]'(Nat.lt_trans hij hj) = edges[k₁] ∧
        (subEdgesUpTo edges aliveSet f_tau v Z m)[j]'hj = edges[k₂] := by
  induction m with
  | zero => intro i j _ hj; simp [subEdgesUpTo] at hj
  | succ m ih =>
    intro i j hij hj
    unfold subEdgesUpTo at hj ⊢
    by_cases hm : m < edges.length
    · simp only [hm, ↓reduceDIte] at hj ⊢
      by_cases hsub : isSubEdge edges aliveSet f_tau v Z ⟨m, hm⟩
      · simp only [hsub, ↓reduceIte] at hj ⊢
        let L := subEdgesUpTo edges aliveSet f_tau v Z m
        have hj_len : j < L.length + 1 := by simpa [L] using hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj_len with hj_lt | rfl
        · have hi_lt : i < L.length := Nat.lt_trans hij hj_lt
          rw [List.getElem_append_left hi_lt, List.getElem_append_left hj_lt]
          rcases ih i j hij hj_lt with ⟨k₁, k₂, hk₁, hk₂, h12, hk₂_m, hget1, hget2⟩
          exact ⟨k₁, k₂, hk₁, hk₂, h12, by omega, hget1, hget2⟩
        · rw [List.getElem_append_left hij, List.getElem_append_right (by rfl)]
          rcases getElem_subEdgesUpTo_origin edges aliveSet f_tau v Z m i hij with
            ⟨k₁, hk₁, hk₁_m, _, hget1⟩
          refine ⟨k₁, m, hk₁, hm, hk₁_m, by omega, hget1, ?_⟩
          simp [L]
      · simp only [hsub, ↓reduceIte] at hj ⊢
        rcases ih i j hij hj with ⟨k₁, k₂, hk₁, hk₂, h12, hk₂_m, hget1, hget2⟩
        exact ⟨k₁, k₂, hk₁, hk₂, h12, by omega, hget1, hget2⟩
    · simp only [hm, ↓reduceDIte] at hj ⊢
      rcases ih i j hij hj with ⟨k₁, k₂, hk₁, hk₂, h12, hk₂_m, hget1, hget2⟩
      exact ⟨k₁, k₂, hk₁, hk₂, h12, by omega, hget1, hget2⟩

theorem exists_getElem_subEdgesUpTo_of_isSubEdge {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z : Finset (Fin n)) (m : ℕ) :
    ∀ (k : ℕ) (hk : k < edges.length), k < m →
      isSubEdge edges aliveSet f_tau v Z ⟨k, hk⟩ →
      ∃ (i : ℕ) (hi : i < (subEdgesUpTo edges aliveSet f_tau v Z m).length),
        (subEdgesUpTo edges aliveSet f_tau v Z m)[i]'hi = edges[k] := by
  induction m with
  | zero => intro k _ hkm _; omega
  | succ m ih =>
    intro k hk hkm hk_sub
    unfold subEdgesUpTo
    by_cases hm : m < edges.length
    · simp only [hm, ↓reduceDIte]
      let L := subEdgesUpTo edges aliveSet f_tau v Z m
      rcases Nat.lt_succ_iff_lt_or_eq.mp hkm with hlt | rfl
      · rcases ih k hk hlt hk_sub with ⟨i, hi, hget⟩
        by_cases hsub : isSubEdge edges aliveSet f_tau v Z ⟨m, hm⟩
        · simp only [hsub, ↓reduceIte]
          refine ⟨i, by simp; omega, ?_⟩
          rw [List.getElem_append_left hi]
          exact hget
        · simp only [hsub, ↓reduceIte]
          exact ⟨i, hi, hget⟩
      · simp only [hk_sub, ↓reduceIte]
        refine ⟨L.length, by simp [L], ?_⟩
        rw [List.getElem_append_right (by rfl)]
        simp
    · simp only [hm, ↓reduceDIte]
      exact ih k hk (by omega) hk_sub

theorem isSimpleEdgeList_subEdgesUpTo {n t : ℕ} (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z : Finset (Fin n)) :
    IsSimpleEdgeList
      (restrictGraph
        (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        (Finset.univ \ Z))
      (subEdgesUpTo edges aliveSet f_tau v Z edges.length) := by
  let sub_edges := subEdgesUpTo edges aliveSet f_tau v Z edges.length
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rcases getElem_subEdgesUpTo_origin edges aliveSet f_tau v Z edges.length i hi with
      ⟨k, hk, _, _, hget⟩
    rw [hget]
    exact hedges.1 k hk
  · intro i j hij hj
    rcases getElem_subEdgesUpTo_lt_origin edges aliveSet f_tau v Z edges.length i j hij hj with
      ⟨k₁, k₂, hk₁, hk₂, h12, _, hget1, hget2⟩
    rw [hget1, hget2]
    exact hedges.2.1 k₁ k₂ h12 hk₂
  · intro x y
    simp only [restrictGraph_adj, Finset.mem_sdiff, Finset.mem_univ, true_and]
    change (_ ∧ _ ∧ (graphOfAlive edges hedges.1 aliveSet).Adj x y ∧
      tauOfArr edges t ht_pos f_tau s(x, y) = v) ↔ _
    constructor
    · rintro ⟨hxZ, hyZ, ⟨k, hk_al, hmatch⟩, htau_xy⟩
      have hsym_eq : symEdgeAt edges k = s(x, y) := by
        unfold symEdgeAt
        rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2, Sym2.eq_swap]
      have hfk_v : f_tau k = v := by
        rw [← hsym_eq, tauOfArr_symEdgeAt hedges] at htau_xy
        exact htau_xy
      have hk_sub : isSubEdge edges aliveSet f_tau v Z k := by
        refine ⟨hk_al, hfk_v, ?_, ?_⟩
        · rcases hmatch with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rwa [h1]
        · rcases hmatch with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rwa [h2]
      rcases exists_getElem_subEdgesUpTo_of_isSubEdge edges aliveSet f_tau v Z edges.length
          k.1 k.2 k.2 hk_sub with ⟨i, hi, hget⟩
      refine ⟨i, hi, ?_⟩
      simpa [sub_edges, hget] using hmatch
    · rintro ⟨i, hi, hmatch⟩
      rcases getElem_subEdgesUpTo_origin edges aliveSet f_tau v Z edges.length i hi with
        ⟨k, hk, _, ⟨hk_al, hfk_v, hk1_Z, hk2_Z⟩, hget⟩
      change (sub_edges[i]).1 = _ ∧ _ ∨ _ at hmatch
      rw [hget] at hmatch
      have hxZ : x ∉ Z := by
        rcases hmatch with ⟨rfl, _⟩ | ⟨_, rfl⟩
        · exact hk1_Z
        · exact hk2_Z
      have hyZ : y ∉ Z := by
        rcases hmatch with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact hk2_Z
        · exact hk1_Z
      have hsym_eq : s(x, y) = symEdgeAt edges ⟨k, hk⟩ := by
        unfold symEdgeAt
        rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      refine ⟨hxZ, hyZ, ⟨⟨k, hk⟩, hk_al, hmatch⟩, ?_⟩
      rw [hsym_eq, tauOfArr_symEdgeAt hedges]
      exact hfk_v

/-- Write endpoints `(r_12, r_13)` at offset `2 + 2 * r_19` in `inArr` and increment `r_19`. -/
def writeSubEdgeCmd : Cmd :=
  .seq (.assign 14 (.op .add (.const 2) (.op .mul (.const 2) (.reg 19))))
    (.seq (.write inArr (.reg 14) (.reg 12))
      (.seq (.write inArr (.op .add (.reg 14) (.const 1)) (.reg 13))
        (.assign 19 (.op .add (.reg 19) (.const 1)))))

theorem writeSubEdgeCmd_exec {w n : ℕ} (m₂ : ℕ) (sub_k : List (Fin n × Fin n))
    (e : Fin n × Fin n) (hsub_lt : sub_k.length < m₂)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (h2m2_w : 2 + 2 * m₂ < 2 ^ w)
    {s : State}
    (hin : s.arrs inArr =
      [0, 0] ++ flatEdges sub_k ++ List.replicate (2 * m₂ - 2 * sub_k.length) 0)
    (hr12 : s.regs 12 = e.1.1)
    (hr13 : s.regs 13 = e.2.1)
    (hr19 : s.regs 19 = sub_k.length) :
    ∃ s',
      Exec w writeSubEdgeCmd s s' 18 ∧
      s'.arrs inArr =
        [0, 0] ++ flatEdges (sub_k ++ [e]) ++
          List.replicate (2 * m₂ - 2 * (sub_k ++ [e]).length) 0 ∧
      s'.regs 19 = (sub_k ++ [e]).length ∧
      (∀ a : Arr, a ≠ inArr → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 14 → r ≠ 19 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hsub_w : sub_k.length < 2 ^ w := by omega
  have h2sub_w : 2 * sub_k.length < 2 ^ w := by omega
  have hoff_w : 2 + 2 * sub_k.length < 2 ^ w := by omega
  have hoff1_w : 2 + 2 * sub_k.length + 1 < 2 ^ w := by omega
  have hsub1_w : sub_k.length + 1 < 2 ^ w := by omega
  have he1_w : e.1.1 < 2 ^ w := by have := e.1.2; omega
  have he2_w : e.2.1 < 2 ^ w := by have := e.2.2; omega
  let s₁ := s.setReg 14 (2 + 2 * sub_k.length)
  have hex₁ : Exec w (.assign 14 (.op .add (.const 2) (.op .mul (.const 2) (.reg 19)))) s s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr19, hw2, hsub_w, h2sub_w, hoff_w])
  have hlen_in : (s.arrs inArr).length = 2 + 2 * m₂ := by
    rw [hin, List.length_append, List.length_append, length_flatEdges, List.length_replicate]
    simp; omega
  let s₂ := s₁.writeArr inArr (2 + 2 * sub_k.length) e.1.1
  have hex₂ : Exec w (.write inArr (.reg 14) (.reg 12)) s₁ s₂ 3 :=
    .write (by simp [s₁, Expr.eval, checkWord, hoff_w])
      (by simp [s₁, Expr.eval, checkWord, hr12, he1_w])
      (by simp [s₁, hlen_in]; omega)
  let s₃ := s₂.writeArr inArr (2 + 2 * sub_k.length + 1) e.2.1
  have hex₃ : Exec w (.write inArr (.op .add (.reg 14) (.const 1)) (.reg 13)) s₂ s₃ 5 :=
    .write (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hoff_w, hw, hoff1_w])
      (by simp [s₂, s₁, Expr.eval, checkWord, hr13, he2_w])
      (by simp [s₂, s₁, hlen_in]; omega)
  let s₄ := s₃.setReg 19 (sub_k.length + 1)
  have hex₄ : Exec w (.assign 19 (.op .add (.reg 19) (.const 1))) s₃ s₄ 4 :=
    .assign (by simp [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr19, hsub_w, hw, hsub1_w])
  have hin₄ : s₄.arrs inArr =
      [0, 0] ++ flatEdges (sub_k ++ [e]) ++
        List.replicate (2 * m₂ - 2 * (sub_k ++ [e]).length) 0 := by
    have hs4_in : s₄.arrs inArr =
        ((s.arrs inArr).set (2 + 2 * sub_k.length) e.1.1).set
          (2 + 2 * sub_k.length + 1) e.2.1 := rfl
    rw [hs4_in, hin]
    have hpre_len : ([0, 0] ++ flatEdges sub_k).length = 2 + 2 * sub_k.length := by
      simp [length_flatEdges]; omega
    have hrem_split : 2 * m₂ - 2 * sub_k.length =
        (2 * m₂ - 2 * (sub_k.length + 1) + 1) + 1 := by omega
    rw [hrem_split, List.replicate_succ, List.replicate_succ]
    rw [List.set_append_right _ _ (by omega)]
    have hsub0 : 2 + 2 * sub_k.length - ([0, 0] ++ flatEdges sub_k).length = 0 := by omega
    rw [hsub0, List.set_cons_zero]
    rw [List.set_append_right _ _ (by omega)]
    have hsub1 : 2 + 2 * sub_k.length + 1 - ([0, 0] ++ flatEdges sub_k).length = 1 := by omega
    rw [hsub1, List.set_cons_succ, List.set_cons_zero]
    have hflat_app : flatEdges (sub_k ++ [e]) = flatEdges sub_k ++ [e.1.1, e.2.1] := by
      rw [flatEdges_append]; rfl
    rw [hflat_app]
    simp [List.append_assoc]
  refine ⟨s₄, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), hin₄,
    by simp [s₄],
    fun a ha => by simp [s₄, s₃, s₂, s₁, ha],
    fun r hr14 hr19' => by simp [s₄, s₃, s₂, s₁, hr14, hr19']⟩

/-- Loop body for `buildSubgraphEdgesProg`: checks whether edge `r_11` belongs to `R \ Z`, and if
so appends its endpoints to `inArr` via `writeSubEdgeCmd`. -/
def buildSubgraphEdgesBody : Cmd :=
  .ite (.read 4 (.reg 11))
    (.ite (.op .eq (.read 5 (.reg 11)) (.reg 7))
      (.seq (.assign 12 (.read 2 (.reg 11)))
        (.seq (.assign 13 (.read 3 (.reg 11)))
          (.ite (.read 12 (.reg 12))
            .skip
            (.ite (.read 12 (.reg 13))
              .skip
              writeSubEdgeCmd))))
      .skip)
    .skip

theorem buildSubgraphEdgesBody_exec {w n t : ℕ}
    (edges : List (Fin n × Fin n)) (aliveSet : Finset (Fin edges.length))
    (f_tau : Fin edges.length → Fin t) (v : Fin t) (Z : Finset (Fin n))
    (k : ℕ) (hk : k < edges.length)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (ht_w : t < 2 ^ w) (h2m2_w : 2 + 2 * edges.length < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hZbit : IsBitSet Z 12 s)
    (hin : s.arrs inArr =
      [0, 0] ++ flatEdges (subEdgesUpTo edges aliveSet f_tau v Z k) ++
        List.replicate (2 * edges.length - 2 * (subEdgesUpTo edges aliveSet f_tau v Z k).length) 0)
    (hr7 : s.regs 7 = v.1)
    (hr11 : s.regs 11 = k)
    (hr19 : s.regs 19 = (subEdgesUpTo edges aliveSet f_tau v Z k).length) :
    ∃ s' t_body,
      Exec w buildSubgraphEdgesBody s s' t_body ∧
      t_body ≤ 34 ∧
      s'.arrs inArr =
        [0, 0] ++ flatEdges (subEdgesUpTo edges aliveSet f_tau v Z (k + 1)) ++
          List.replicate
            (2 * edges.length - 2 * (subEdgesUpTo edges aliveSet f_tau v Z (k + 1)).length) 0 ∧
      s'.regs 19 = (subEdgesUpTo edges aliveSet f_tau v Z (k + 1)).length ∧
      (∀ a : Arr, a ≠ inArr → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 19 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  let k_fin : Fin edges.length := ⟨k, hk⟩
  have hal_len : k < (s.arrs 4).length := by rw [hal.1]; exact hk
  let al_k := (s.arrs 4)[k]'hal_len
  have hal_le : al_k ≤ 1 := hal.2.1 k_fin
  have hal_w : al_k < 2 ^ w := by omega
  have hread_al : (Expr.read 4 (.reg 11)).eval w s = some al_k := by
    simp [Expr.eval, checkWord, hr11, hk_w, hal_len, al_k, hal_w]
  by_cases h_al : k_fin ∈ aliveSet
  · have hal_ne0 : al_k ≠ 0 := (hal.2.2 k_fin).mpr h_al
    have htau_k_w : (f_tau k_fin).1 < 2 ^ w := by have := (f_tau k_fin).2; omega
    rcases htau with ⟨hlen5, hall5⟩
    have hk_len5 : k < (s.arrs 5).length := by rw [hlen5]; exact hk
    have hval5 : (s.arrs 5)[k]'hk_len5 = (f_tau k_fin).1 := hall5 k_fin
    by_cases h_v : f_tau k_fin = v
    · have hval_eq : (f_tau k_fin).1 = v.1 := congrArg Fin.val h_v
      have hcond_v : (Expr.op .eq (.read 5 (.reg 11)) (.reg 7)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hk_w, hk_len5, hval5,
          hr7, hv_w, hval_eq, hw]
      rcases hend with ⟨hlen2, hlen3, hall23⟩
      let u := (edges[k]).1
      let y := (edges[k]).2
      have hu_w : u.1 < 2 ^ w := by have := u.2; omega
      have hy_w : y.1 < 2 ^ w := by have := y.2; omega
      have hk_len2 : k < (s.arrs 2).length := by rw [hlen2]; exact hk
      have hval2 : (s.arrs 2)[k]'hk_len2 = u.1 := (hall23 k_fin).1
      let s₁ := s.setReg 12 u.1
      have hex₁ : Exec w (.assign 12 (.read 2 (.reg 11))) s s₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, hr11, hk_w, hk_len2, hval2, hu_w])
      have hk_len3 : k < (s.arrs 3).length := by rw [hlen3]; exact hk
      have hval3 : (s.arrs 3)[k]'hk_len3 = y.1 := (hall23 k_fin).2
      let s₂ := s₁.setReg 13 y.1
      have hex₂ : Exec w (.assign 13 (.read 3 (.reg 11))) s₁ s₂ 3 :=
        .assign (by simp [s₁, Expr.eval, checkWord, hr11, hk_w, hk_len3, hval3, hy_w])
      have hZ_len_u : u.1 < (s.arrs 12).length := by rw [hZbit.1]; exact u.2
      let zu := (s.arrs 12)[u.1]'hZ_len_u
      have hzu_le : zu ≤ 1 := hZbit.2.1 u
      have hzu_w : zu < 2 ^ w := by omega
      have hread_uZ : (Expr.read 12 (.reg 12)).eval w s₂ = some zu := by
        simp [s₂, s₁, Expr.eval, checkWord, hu_w, hZ_len_u, zu, hzu_w]
      by_cases hu_Z : u ∈ Z
      · have hzu_ne0 : zu ≠ 0 := (hZbit.2.2 u).mpr hu_Z
        have hex_ite_u : Exec w (.ite (.read 12 (.reg 12)) .skip
            (.ite (.read 12 (.reg 13)) .skip writeSubEdgeCmd)) s₂ s₂ 3 :=
          .ite_true hread_uZ hzu_ne0 (.skip s₂)
        have hnot_sub : ¬ isSubEdge edges aliveSet f_tau v Z k_fin :=
          fun h => h.2.2.1 hu_Z
        have hsub_eq : subEdgesUpTo edges aliveSet f_tau v Z (k + 1) =
            subEdgesUpTo edges aliveSet f_tau v Z k := by
          simp [subEdgesUpTo, hk, k_fin, hnot_sub]
        refine ⟨s₂, 2 + (4 + (3 + (3 + 3))),
          .ite_true hread_al hal_ne0
            (.ite_true hcond_v (by omega) (.seq hex₁ (.seq hex₂ hex_ite_u))),
          by omega, by simp [s₂, s₁, hsub_eq, hin], by simp [s₂, s₁, hsub_eq, hr19],
          fun _ _ => rfl,
          fun r hr12 hr13 _ _ => by simp [s₂, s₁, hr12, hr13]⟩
      · have hzu_eq0 : zu = 0 := by
          by_contra hne
          exact hu_Z ((hZbit.2.2 u).mp hne)
        have hread_uZ0 : (Expr.read 12 (.reg 12)).eval w s₂ = some 0 := by
          rw [hread_uZ, hzu_eq0]
        have hZ_len_y : y.1 < (s.arrs 12).length := by rw [hZbit.1]; exact y.2
        let zy := (s.arrs 12)[y.1]'hZ_len_y
        have hzy_le : zy ≤ 1 := hZbit.2.1 y
        have hzy_w : zy < 2 ^ w := by omega
        have hread_yZ : (Expr.read 12 (.reg 13)).eval w s₂ = some zy := by
          simp [s₂, s₁, Expr.eval, checkWord, hy_w, hZ_len_y, zy, hzy_w]
        by_cases hy_Z : y ∈ Z
        · have hzy_ne0 : zy ≠ 0 := (hZbit.2.2 y).mpr hy_Z
          have hex_ite_y : Exec w (.ite (.read 12 (.reg 13)) .skip writeSubEdgeCmd) s₂ s₂ 3 :=
            .ite_true hread_yZ hzy_ne0 (.skip s₂)
          have hnot_sub : ¬ isSubEdge edges aliveSet f_tau v Z k_fin :=
            fun h => h.2.2.2 hy_Z
          have hsub_eq : subEdgesUpTo edges aliveSet f_tau v Z (k + 1) =
              subEdgesUpTo edges aliveSet f_tau v Z k := by
            simp [subEdgesUpTo, hk, k_fin, hnot_sub]
          refine ⟨s₂, 2 + (4 + (3 + (3 + (2 + 3)))),
            .ite_true hread_al hal_ne0
              (.ite_true hcond_v (by omega)
                (.seq hex₁ (.seq hex₂ (.ite_false hread_uZ0 hex_ite_y)))),
            by omega, by simp [s₂, s₁, hsub_eq, hin], by simp [s₂, s₁, hsub_eq, hr19],
            fun _ _ => rfl,
            fun r hr12 hr13 _ _ => by simp [s₂, s₁, hr12, hr13]⟩
        · have hzy_eq0 : zy = 0 := by
            by_contra hne
            exact hy_Z ((hZbit.2.2 y).mp hne)
          have hread_yZ0 : (Expr.read 12 (.reg 13)).eval w s₂ = some 0 := by
            rw [hread_yZ, hzy_eq0]
          have hsub : isSubEdge edges aliveSet f_tau v Z k_fin := ⟨h_al, h_v, hu_Z, hy_Z⟩
          have hsub_eq : subEdgesUpTo edges aliveSet f_tau v Z (k + 1) =
              subEdgesUpTo edges aliveSet f_tau v Z k ++ [edges[k]] := by
            simp [subEdgesUpTo, hk, k_fin, hsub]
          have hlen_lt : (subEdgesUpTo edges aliveSet f_tau v Z k).length < edges.length :=
            Nat.lt_of_le_of_lt (length_subEdgesUpTo_le edges aliveSet f_tau v Z k) hk
          rcases writeSubEdgeCmd_exec edges.length
              (subEdgesUpTo edges aliveSet f_tau v Z k) (edges[k]) hlen_lt
              hw2 hn_w h2m2_w (s := s₂) (by simpa [s₂, s₁] using hin)
              (by simp [s₂, s₁, u]) (by simp [s₂, y]) (by simp [s₂, s₁, hr19]) with
            ⟨s₃, hex_w, hin₃, hr19_3, harr₃, hreg₃⟩
          refine ⟨s₃, 2 + (4 + (3 + (3 + (2 + (2 + 18))))),
            .ite_true hread_al hal_ne0
              (.ite_true hcond_v (by omega)
                (.seq hex₁ (.seq hex₂ (.ite_false hread_uZ0 (.ite_false hread_yZ0 hex_w))))),
            by omega, by simpa [hsub_eq] using hin₃, by simpa [hsub_eq] using hr19_3,
            fun a ha => by rw [harr₃ a ha]; rfl,
            fun r hr12 hr13 hr14 hr19' => by
              rw [hreg₃ r hr14 hr19']
              simp [s₂, s₁, hr12, hr13]⟩
    · have hval_ne : (f_tau k_fin).1 ≠ v.1 := fun h => h_v (Fin.ext h)
      have hcond_v : (Expr.op .eq (.read 5 (.reg 11)) (.reg 7)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hk_w, hk_len5, hval5,
          htau_k_w, hr7, hv_w, hval_ne, h0_w]
      have hnot_sub : ¬ isSubEdge edges aliveSet f_tau v Z k_fin := fun h => h_v h.2.1
      have hsub_eq : subEdgesUpTo edges aliveSet f_tau v Z (k + 1) =
          subEdgesUpTo edges aliveSet f_tau v Z k := by
        simp [subEdgesUpTo, hk, k_fin, hnot_sub]
      refine ⟨s, 2 + (4 + 1),
        .ite_true hread_al hal_ne0 (.ite_false hcond_v (.skip s)),
        by omega, by simp [hsub_eq, hin], by simp [hsub_eq, hr19],
        fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · have hal_eq0 : al_k = 0 := by
      by_contra hne
      exact h_al ((hal.2.2 k_fin).mp hne)
    have hread_al0 : (Expr.read 4 (.reg 11)).eval w s = some 0 := by
      rw [hread_al, hal_eq0]
    have hnot_sub : ¬ isSubEdge edges aliveSet f_tau v Z k_fin := fun h => h_al h.1
    have hsub_eq : subEdgesUpTo edges aliveSet f_tau v Z (k + 1) =
        subEdgesUpTo edges aliveSet f_tau v Z k := by
      simp [subEdgesUpTo, hk, k_fin, hnot_sub]
    refine ⟨s, 2 + 1, .ite_false hread_al0 (.skip s),
      by omega, by simp [hsub_eq, hin], by simp [hsub_eq, hr19],
      fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem buildSubgraphEdgesLoop_exec {w n t : ℕ}
    (edges : List (Fin n × Fin n)) (aliveSet : Finset (Fin edges.length))
    (f_tau : Fin edges.length → Fin t) (v : Fin t) (Z : Finset (Fin n))
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (ht_w : t < 2 ^ w) (h2m2_w : 2 + 2 * edges.length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = edges.length)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hZbit : IsBitSet Z 12 s)
    (hin : s.arrs inArr =
      [0, 0] ++ flatEdges (subEdgesUpTo edges aliveSet f_tau v Z k) ++
        List.replicate (2 * edges.length - 2 * (subEdgesUpTo edges aliveSet f_tau v Z k).length) 0)
    (hr2 : s.regs 2 = edges.length)
    (hr7 : s.regs 7 = v.1)
    (hr11 : s.regs 11 = k)
    (hr19 : s.regs 19 = (subEdgesUpTo edges aliveSet f_tau v Z k).length) :
    ∃ s' t_loop,
      Exec w (forUp 11 (.reg 2) buildSubgraphEdgesBody) s s' t_loop ∧
      t_loop ≤ 3 + 41 * rem ∧
      s'.arrs inArr =
        [0, 0] ++ flatEdges (subEdgesUpTo edges aliveSet f_tau v Z edges.length) ++
          List.replicate
            (2 * edges.length - 2 * (subEdgesUpTo edges aliveSet f_tau v Z edges.length).length) 0 ∧
      s'.regs 19 = (subEdgesUpTo edges aliveSet f_tau v Z edges.length).length ∧
      (∀ a : Arr, a ≠ inArr → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 19 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm2_w : edges.length < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = edges.length := by omega
    rw [hk_eq] at hr11 hin hr19
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hm2_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hin, hr19,
      fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < edges.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hk_w, hm2_w, hk_lt, hw]
    rcases buildSubgraphEdgesBody_exec edges aliveSet f_tau v Z k hk_lt
        hw2 hn_w ht_w h2m2_w hend hal htau hZbit hin hr7 hr11 hr19 with
      ⟨s₁, t₁, hex₁, ht₁, hin₁, hr19_1, harr₁, hreg₁⟩
    have hr11_1 : s₁.regs 11 = k := by
      rw [hreg₁ 11 (by decide) (by decide) (by decide) (by decide), hr11]
    let s₂ := s₁.setReg 11 (k + 1)
    have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11_1, hk_w, hw, hk1_w])
    rcases ih (k + 1) (by omega) (s := s₂)
        (hend.of_arrs_eq (harr₁ 2 (by decide)) (harr₁ 3 (by decide)))
        (hal.of_arr_eq (harr₁ 4 (by decide)))
        (htau.of_arr_eq (harr₁ 5 (by decide)))
        (hZbit.of_arr_eq (harr₁ 12 (by decide)))
        (by simpa [s₂] using hin₁)
        (by simp [s₂, hreg₁ 2 (by decide) (by decide) (by decide) (by decide), hr2])
        (by simp [s₂, hreg₁ 7 (by decide) (by decide) (by decide) (by decide), hr7])
        (by simp [s₂])
        (by simp [s₂, hr19_1]) with
      ⟨s₃, t₃, hex₃, ht₃, hin₃, hr19_3, harr₃, hreg₃⟩
    refine ⟨s₃, 3 + (t₁ + 4) + t₃,
      .while_true hcond (by omega) (.seq hex₁ hex_inc) hex₃,
      by omega, hin₃, hr19_3,
      fun a ha => by rw [harr₃ a ha]; exact harr₁ a ha,
      fun r hr11' hr12 hr13 hr14 hr19' => by
        rw [hreg₃ r hr11' hr12 hr13 hr14 hr19']
        simp [s₂, hr11', hreg₁ r hr12 hr13 hr14 hr19']⟩

/-- Build the CSR representation of `restrictGraph (leafGraph G τ v) (Finset.univ \ Z)` in arrays
`15, 16, 17` (using degree array `14` and register block `30..36`):
1. Allocates `inArr = 0` of size `2 + r_3` (`2 + 2 * m₂`), sets `r_19 := 0` and `r_11 := 0`,
   and runs `buildSubgraphEdgesBody` for `r_11 < r_2`.
2. Writes `inArr[0] := r_0` (`n`) and `inArr[1] := r_19` (`sub_edges.length`).
3. Runs `parseGraphProg 14 15 16 17 30`. -/
def buildSubgraphCsrProg : Cmd :=
  .seq (.alloc inArr (.op .add (.const 2) (.reg 3)))
    (.seq (.assign 19 (.const 0))
      (.seq (.assign 11 (.const 0))
        (.seq (forUp 11 (.reg 2) buildSubgraphEdgesBody)
          (.seq (.write inArr (.const 0) (.reg 0))
            (.seq (.write inArr (.const 1) (.reg 19))
              (parseGraphProg 14 15 16 17 30))))))

theorem parseGraphProg_writtenArrs_subset :
    ∀ a ∈ (parseGraphProg 14 15 16 17 30).writtenArrs,
      a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 := by decide

theorem parseGraphProg_writtenRegs_ge :
    ∀ r ∈ (parseGraphProg 14 15 16 17 30).writtenRegs, 30 ≤ r := by decide

theorem buildSubgraphCsrProg_exec {w n t : ℕ} (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z : Finset (Fin n))
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (ht_w : t < 2 ^ w) (h2m2_w : 2 + 2 * edges.length < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hZbit : IsBitSet Z 12 s)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = edges.length)
    (hr3 : s.regs 3 = 2 * edges.length)
    (hr7 : s.regs 7 = v.1) :
    let sub_edges := subEdgesUpTo edges aliveSet f_tau v Z edges.length
    let G_sub := restrictGraph
      (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
      (Finset.univ \ Z)
    ∃ s' t_csr,
      Exec w buildSubgraphCsrProg s s' t_csr ∧
      t_csr ≤ 23 * n + 131 * edges.length + 45 ∧
      IsAdjList G_sub 15 16 17 (edgeNeighbors sub_edges) s' ∧
      (s'.arrs 17).length = 2 * sub_edges.length ∧
      totalAdjEntries (edgeNeighbors sub_edges) = 2 * sub_edges.length ∧
      sub_edges.length ≤ edges.length ∧
      (∀ a : Arr, a ≠ inArr → a ≠ 14 → a ≠ 15 → a ≠ 16 → a ≠ 17 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 30 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 19 → s'.regs r = s.regs r) := by
  intro sub_edges G_sub
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have h2m_w : 2 * edges.length < 2 ^ w := by omega
  have hsub_le : sub_edges.length ≤ edges.length :=
    length_subEdgesUpTo_le edges aliveSet f_tau v Z edges.length
  have hsub_w : sub_edges.length < 2 ^ w := by omega
  have h2sub2_w : 2 + 2 * sub_edges.length < 2 ^ w := by omega
  let s₁ := s.setArr inArr (List.replicate (2 + 2 * edges.length) 0)
  have hex₁ : Exec w (.alloc inArr (.op .add (.const 2) (.reg 3))) s s₁
      (3 + (2 + 2 * edges.length)) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hw2, h2m_w, h2m2_w])
  let s₂ := s₁.setReg 19 0
  have hex₂ : Exec w (.assign 19 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg 11 0
  have hex₃ : Exec w (.assign 11 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hin₃ : s₃.arrs inArr =
      [0, 0] ++ flatEdges (subEdgesUpTo edges aliveSet f_tau v Z 0) ++
        List.replicate (2 * edges.length - 2 * (subEdgesUpTo edges aliveSet f_tau v Z 0).length) 0 := by
    have hrep : List.replicate (2 + 2 * edges.length) 0 =
        [0, 0] ++ List.replicate (2 * edges.length) 0 := by
      rw [List.replicate_add]; rfl
    simp [s₃, s₂, s₁, subEdgesUpTo, flatEdges, hrep]
  rcases buildSubgraphEdgesLoop_exec edges aliveSet f_tau v Z
      hw2 hn_w ht_w h2m2_w edges.length 0 (by omega) (s := s₃)
      (hend.of_arrs_eq (by simp [s₃, s₂, s₁]) (by simp [s₃, s₂, s₁]))
      (hal.of_arr_eq (by simp [s₃, s₂, s₁]))
      (htau.of_arr_eq (by simp [s₃, s₂, s₁]))
      (hZbit.of_arr_eq (by simp [s₃, s₂, s₁]))
      hin₃ (by simp [s₃, s₂, s₁, hr2]) (by simp [s₃, s₂, s₁, hr7])
      (by simp [s₃]) (by simp [s₃, s₂, subEdgesUpTo]) with
    ⟨s₄, t₄, hex₄, ht₄, hin₄, hr19_4, harr₄, hreg₄⟩
  change s₄.regs 19 = sub_edges.length at hr19_4
  change s₄.arrs inArr =
    [0, 0] ++ flatEdges sub_edges ++ List.replicate (2 * edges.length - 2 * sub_edges.length) 0 at hin₄
  have hr0_4 : s₄.regs 0 = n := by
    rw [hreg₄ 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s₃, s₂, s₁, hr0]
  have hlen_in₄ : 1 < (s₄.arrs inArr).length := by simp [hin₄]
  let s₅ := s₄.writeArr inArr 0 n
  have hex₅ : Exec w (.write inArr (.const 0) (.reg 0)) s₄ s₅ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, hr0_4, hn_w])
      (by omega)
  let s₆ := s₅.writeArr inArr 1 sub_edges.length
  have hex₆ : Exec w (.write inArr (.const 1) (.reg 19)) s₅ s₆ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [s₅, Expr.eval, checkWord, hr19_4, hsub_w])
      (by simp [s₅, hlen_in₄])
  let extra := List.replicate (2 * edges.length - 2 * sub_edges.length) 0
  have hin₆ : s₆.arrs inArr = [n, sub_edges.length] ++ flatEdges sub_edges ++ extra := by
    simp only [s₆, s₅, State.writeArr_arrs_self, hin₄, extra]
    rfl
  have hedges_sub : IsSimpleEdgeList G_sub sub_edges :=
    isSimpleEdgeList_subEdgesUpTo ht_pos hedges aliveSet f_tau v Z
  rcases Triple.parseGraphProg_spec G_sub sub_edges extra 14 15 16 17 30 hedges_sub
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw2 hn_w h2sub2_w s₆ hin₆ with
    ⟨s₇, t₇, hex₇, ht₇, _, _, _, hadj₇, hent₇, _⟩
  dsimp only at ht₇
  have h88 : 88 * sub_edges.length ≤ 88 * edges.length := Nat.mul_le_mul_left 88 hsub_le
  have htot : totalAdjEntries (edgeNeighbors sub_edges) = 2 * sub_edges.length :=
    totalAdjEntries_edgeNeighbors sub_edges hedges_sub.1
  refine ⟨s₇, (3 + (2 + 2 * edges.length)) + (2 + (2 + (t₄ + (3 + (3 + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by omega, hadj₇, hent₇, htot, hsub_le,
    fun a ha0 ha14 ha15 ha16 ha17 => ?_,
    fun r hr30 hr11 hr12 hr13 hr14 hr19 => ?_⟩
  · have hnot_mem : a ∉ (parseGraphProg 14 15 16 17 30).writtenArrs := by
      intro hmem
      rcases parseGraphProg_writtenArrs_subset a hmem with rfl | rfl | rfl | rfl
      · exact ha14 rfl
      · exact ha15 rfl
      · exact ha16 rfl
      · exact ha17 rfl
    rw [hex₇.arrs_eq_of_not_mem_writtenArrs hnot_mem]
    simp [s₆, s₅, ha0, harr₄ a ha0, s₃, s₂, s₁]
  · have hnot_mem : r ∉ (parseGraphProg 14 15 16 17 30).writtenRegs := by
      intro hmem
      exact absurd (parseGraphProg_writtenRegs_ge r hmem) (not_le_of_gt hr30)
    rw [hex₇.regs_eq_of_not_mem_writtenRegs hnot_mem]
    simp only [s₆, s₅, State.writeArr_regs]
    rw [hreg₄ r hr11 hr12 hr13 hr14 hr19]
    simp [s₃, s₂, s₁, hr11, hr19]

/-! #### Subpart 5.2: Valid Ternary Templates `validTernaryLists` and `buildZ12Prog` -/

/-- All ternary lists `List (Fin 3)` of length `k`. -/
def ternaryLists : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | k + 1 =>
    (ternaryLists k).map (0 :: ·) ++
      (ternaryLists k).map (1 :: ·) ++
      (ternaryLists k).map (2 :: ·)

theorem mem_ternaryLists_iff (k : ℕ) (l : List (Fin 3)) :
    l ∈ ternaryLists k ↔ l.length = k := by
  induction k generalizing l with
  | zero =>
    simp [ternaryLists]
  | succ k ih =>
    unfold ternaryLists
    simp only [List.mem_append, List.mem_map]
    constructor
    · rintro ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩) <;>
        simp [(ih t).mp ht]
    · intro hlen
      cases l with
      | nil => simp at hlen
      | cons a t =>
        have ht_len : t.length = k := by simpa using hlen
        have ht_mem : t ∈ ternaryLists k := (ih t).mpr ht_len
        rcases a with ⟨val, hval⟩
        rcases val with _ | _ | _ | val
        · exact Or.inl (Or.inl ⟨t, ht_mem, rfl⟩)
        · exact Or.inl (Or.inr ⟨t, ht_mem, rfl⟩)
        · exact Or.inr ⟨t, ht_mem, rfl⟩
        · omega

/-- Count of occurrences of `c : Fin 3` in `l : List (Fin 3)`. -/
def countVal (c : Fin 3) (l : List (Fin 3)) : ℕ :=
  (l.filter (· == c)).length

theorem countVal_append (c : Fin 3) (l₁ l₂ : List (Fin 3)) :
    countVal c (l₁ ++ l₂) = countVal c l₁ + countVal c l₂ := by
  simp [countVal, List.filter_append]

theorem countVal_singleton (c a : Fin 3) :
    countVal c [a] = if a = c then 1 else 0 := by
  unfold countVal
  by_cases h : a = c <;> simp [h]

/-- Whether a ternary template `l : List (Fin 3)` of length `3 * ω` satisfies the cardinality
conditions of Step (4) of Algorithm (3.3):
`2 * |Z₁| + |Z₃| ≤ 4 * ω`, `2 * |Z₂| + |Z₃| ≤ 4 * ω`, and `|Z₃| ≤ ω`. -/
def validTemplate (ω : ℕ) (l : List (Fin 3)) : Prop :=
  l.length = 3 * ω ∧
  2 * countVal 0 l + countVal 2 l ≤ 4 * ω ∧
  2 * countVal 1 l + countVal 2 l ≤ 4 * ω ∧
  countVal 2 l ≤ ω

instance instDecidableValidTemplate (ω : ℕ) (l : List (Fin 3)) :
    Decidable (validTemplate ω l) := by
  unfold validTemplate
  infer_instance

/-- All valid ternary templates of length `3 * ω`. -/
def validTernaryLists (ω : ℕ) : List (List (Fin 3)) :=
  (ternaryLists (3 * ω)).filter (fun l => decide (validTemplate ω l))

theorem mem_validTernaryLists_iff (ω : ℕ) (l : List (Fin 3)) :
    l ∈ validTernaryLists ω ↔ validTemplate ω l := by
  simp only [validTernaryLists, List.mem_filter, mem_ternaryLists_iff, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- Prefix of the vertex subset for part `c : Fin 3` reconstructed from `L : List (Fin n)` and
template `l : List (Fin 3)` up to index `k`. -/
def partOfTemplateUpTo {n : ℕ} (L : List (Fin n)) (l : List (Fin 3)) (c : Fin 3) :
    ℕ → Finset (Fin n)
  | 0 => ∅
  | k + 1 =>
    let prev := partOfTemplateUpTo L l c k
    if hkL : k < L.length then
      if hkl : k < l.length then
        if l[k] = c then insert L[k] prev else prev
      else prev
    else prev

/-- Full vertex subset for part `c : Fin 3` reconstructed from `L : List (Fin n)` and template `l`. -/
def partOfTemplate {n : ℕ} (L : List (Fin n)) (l : List (Fin 3)) (c : Fin 3) : Finset (Fin n) :=
  partOfTemplateUpTo L l c l.length

theorem mem_partOfTemplateUpTo_iff {n : ℕ} (L : List (Fin n)) (l : List (Fin 3)) (c : Fin 3)
    (hlL : l.length = L.length)
    (k : ℕ) (hk : k ≤ l.length) (u : Fin n) :
    u ∈ partOfTemplateUpTo L l c k ↔
      ∃ (i : ℕ) (hi : i < k),
        L[i]'(by omega) = u ∧ l[i]'(by omega) = c := by
  induction k with
  | zero => simp [partOfTemplateUpTo]
  | succ k ih =>
    have hkL : k < L.length := by omega
    have hkl : k < l.length := by omega
    unfold partOfTemplateUpTo
    simp only [hkL, hkl, ↓reduceDIte]
    by_cases hlc : l[k] = c
    · simp only [hlc, ↓reduceIte, Finset.mem_insert, ih (by omega)]
      constructor
      · rintro (rfl | ⟨i, hi, hLi, hli⟩)
        · exact ⟨k, Nat.lt_succ_self k, rfl, hlc⟩
        · exact ⟨i, Nat.lt_succ_of_lt hi, hLi, hli⟩
      · rintro ⟨i, hi, hLi, hli⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt_i | rfl
        · exact Or.inr ⟨i, hlt_i, hLi, hli⟩
        · exact Or.inl hLi.symm
    · simp only [hlc, ↓reduceIte, ih (by omega)]
      constructor
      · rintro ⟨i, hi, hLi, hli⟩
        exact ⟨i, Nat.lt_succ_of_lt hi, hLi, hli⟩
      · rintro ⟨i, hi, hLi, hli⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt_i | rfl
        · exact ⟨i, hlt_i, hLi, hli⟩
        · exact False.elim (hlc hli)

theorem card_partOfTemplateUpTo_eq {n : ℕ} (L : List (Fin n)) (l : List (Fin 3)) (c : Fin 3)
    (hlL : l.length = L.length) (hL_nodup : L.Nodup)
    (k : ℕ) (hk : k ≤ l.length) :
    (partOfTemplateUpTo L l c k).card = countVal c (l.take k) := by
  induction k with
  | zero => simp [partOfTemplateUpTo, countVal]
  | succ k ih =>
    have hkL : k < L.length := by omega
    have hkl : k < l.length := by omega
    unfold partOfTemplateUpTo
    simp only [hkL, hkl, ↓reduceDIte]
    rw [take_add_one_eq_append_getElem l k hkl, countVal_append, countVal_singleton]
    by_cases hlc : l[k] = c
    · simp only [hlc, ↓reduceIte]
      have hnot_mem : L[k] ∉ partOfTemplateUpTo L l c k := by
        rw [mem_partOfTemplateUpTo_iff L l c hlL k (by omega)]
        rintro ⟨i, hi, hLi, _⟩
        have hnodup := List.nodup_iff_injective_getElem.mp hL_nodup
        have heq : (⟨i, by omega⟩ : Fin L.length) = ⟨k, hkL⟩ := hnodup hLi
        have : i = k := congrArg Fin.val heq
        omega
      rw [Finset.card_insert_of_notMem hnot_mem, ih (by omega)]
    · simp only [hlc, ↓reduceIte, Nat.add_zero]
      exact ih (by omega)

theorem card_partOfTemplate_eq {n : ℕ} (L : List (Fin n)) (l : List (Fin 3)) (c : Fin 3)
    (hlL : l.length = L.length) (hL_nodup : L.Nodup) :
    (partOfTemplate L l c).card = countVal c l := by
  unfold partOfTemplate
  rw [card_partOfTemplateUpTo_eq L l c hlL hL_nodup l.length le_rfl, List.take_length]

theorem disjoint_partOfTemplate {n : ℕ} (L : List (Fin n)) (l : List (Fin 3)) {c₁ c₂ : Fin 3}
    (hne : c₁ ≠ c₂) (hlL : l.length = L.length) (hL_nodup : L.Nodup) :
    Disjoint (partOfTemplate L l c₁) (partOfTemplate L l c₂) := by
  rw [Finset.disjoint_left]
  intro u hu1 hu2
  unfold partOfTemplate at hu1 hu2
  rw [mem_partOfTemplateUpTo_iff L l c₁ hlL l.length le_rfl] at hu1
  rw [mem_partOfTemplateUpTo_iff L l c₂ hlL l.length le_rfl] at hu2
  rcases hu1 with ⟨i₁, hi₁, hL1, hl1⟩
  rcases hu2 with ⟨i₂, hi₂, hL2, hl2⟩
  have hnodup := List.nodup_iff_injective_getElem.mp hL_nodup
  have heq : (⟨i₁, by omega⟩ : Fin L.length) = ⟨i₂, by omega⟩ :=
    hnodup (hL1.trans hL2.symm)
  have hi_eq : i₁ = i₂ := congrArg Fin.val heq
  subst hi_eq
  exact hne (hl1.symm.trans hl2)

theorem isValidZPartition_partOfTemplate {n ω : ℕ} (Z : Finset (Fin n))
    (hZ_card : Z.card = 3 * ω) {l : List (Fin 3)} (hval : validTemplate ω l) :
    let L := zListUpTo Z n
    IsValidZPartition ω Z
      (partOfTemplate L l 0)
      (partOfTemplate L l 1)
      (partOfTemplate L l 2) := by
  intro L
  have hL_len : L.length = 3 * ω := by
    rw [length_zListUpTo_self, hZ_card]
  have hlL : l.length = L.length := by rw [hval.1, hL_len]
  have hL_nodup : L.Nodup := nodup_zListUpTo Z n
  have hcard0 := card_partOfTemplate_eq L l 0 hlL hL_nodup
  have hcard1 := card_partOfTemplate_eq L l 1 hlL hL_nodup
  have hcard2 := card_partOfTemplate_eq L l 2 hlL hL_nodup
  rcases hval with ⟨_, hv1, hv2, hv3⟩
  refine ⟨disjoint_partOfTemplate L l (by decide) hlL hL_nodup,
    disjoint_partOfTemplate L l (by decide) hlL hL_nodup,
    disjoint_partOfTemplate L l (by decide) hlL hL_nodup,
    ?_, hZ_card,
    by omega, by omega, by omega⟩
  ext u
  simp only [Finset.mem_union, partOfTemplate,
    mem_partOfTemplateUpTo_iff L l _ hlL l.length le_rfl]
  constructor
  · rintro ((⟨i, hi, rfl, _⟩ | ⟨i, hi, rfl, _⟩) | ⟨i, hi, rfl, _⟩) <;>
    · have hu_mem : L[i]'(by omega) ∈ L := List.getElem_mem (by omega)
      exact ((mem_zListUpTo Z n _).mp hu_mem).2
  · intro huZ
    have hu_mem : u ∈ L := (mem_zListUpTo Z n u).mpr ⟨u.2, huZ⟩
    rcases List.mem_iff_getElem.mp hu_mem with ⟨i, hiL, hLi⟩
    have hil : i < l.length := by omega
    rcases hli : l[i]'hil with ⟨val, hval_lt⟩
    rcases val with _ | _ | _ | val
    · exact Or.inl (Or.inl ⟨i, hil, hLi, hli⟩)
    · exact Or.inl (Or.inr ⟨i, hil, hLi, hli⟩)
    · exact Or.inr ⟨i, hil, hLi, hli⟩
    · omega

/-- Template encoding a given partition `(Z₁, Z₂, Z₃)` of `Z` along `L = zListUpTo Z n`. -/
def templateOfPartition {n : ℕ} (Z₁ Z₂ : Finset (Fin n)) (L : List (Fin n)) : List (Fin 3) :=
  L.map (fun u =>
    if u ∈ Z₁ then 0
    else if u ∈ Z₂ then 1
    else 2)

theorem exists_validTernaryLists_of_isValidZPartition {n ω : ℕ}
    {Z Z₁ Z₂ Z₃ : Finset (Fin n)} (hpart : IsValidZPartition ω Z Z₁ Z₂ Z₃) :
    let L := zListUpTo Z n
    ∃ l ∈ validTernaryLists ω,
      partOfTemplate L l 0 = Z₁ ∧
      partOfTemplate L l 1 = Z₂ ∧
      partOfTemplate L l 2 = Z₃ := by
  intro L
  let l := templateOfPartition Z₁ Z₂ L
  have hZ_card : Z.card = 3 * ω := hpart.card_Z
  have hL_len : L.length = 3 * ω := by rw [length_zListUpTo_self, hZ_card]
  have hl_len : l.length = 3 * ω := by simp [l, templateOfPartition, hL_len]
  have hlL : l.length = L.length := by rw [hl_len, hL_len]
  have hL_nodup : L.Nodup := nodup_zListUpTo Z n
  have hZ1_sub : Z₁ ⊆ Z := by
    intro u hu
    rw [← hpart.union_eq]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)
  have hZ2_sub : Z₂ ⊆ Z := by
    intro u hu
    rw [← hpart.union_eq]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hu)
  have hZ3_sub : Z₃ ⊆ Z := by
    intro u hu
    rw [← hpart.union_eq]
    exact Finset.mem_union_right _ hu
  have hp0 : partOfTemplate L l 0 = Z₁ := by
    ext u
    rw [partOfTemplate, mem_partOfTemplateUpTo_iff L l 0 hlL l.length le_rfl]
    constructor
    · rintro ⟨i, hi, rfl, hli⟩
      have hget : l[i] = (if L[i]'(by omega) ∈ Z₁ then 0 else if L[i]'(by omega) ∈ Z₂ then 1 else 2) := by
        simp [l, templateOfPartition]
      rw [hget] at hli
      by_cases hu1 : L[i]'(by omega) ∈ Z₁
      · exact hu1
      · simp only [hu1, ↓reduceIte] at hli
        by_cases hu2 : L[i]'(by omega) ∈ Z₂ <;> simp [hu2] at hli
    · intro hu1
      have huZ : u ∈ Z := hZ1_sub hu1
      have huL : u ∈ L := (mem_zListUpTo Z n u).mpr ⟨u.2, huZ⟩
      rcases List.mem_iff_getElem.mp huL with ⟨i, hiL, hLi⟩
      refine ⟨i, by omega, hLi, ?_⟩
      simp [l, templateOfPartition, hLi, hu1]
  have hp1 : partOfTemplate L l 1 = Z₂ := by
    ext u
    rw [partOfTemplate, mem_partOfTemplateUpTo_iff L l 1 hlL l.length le_rfl]
    constructor
    · rintro ⟨i, hi, rfl, hli⟩
      have hget : l[i] = (if L[i]'(by omega) ∈ Z₁ then 0 else if L[i]'(by omega) ∈ Z₂ then 1 else 2) := by
        simp [l, templateOfPartition]
      rw [hget] at hli
      by_cases hu1 : L[i]'(by omega) ∈ Z₁
      · simp [hu1] at hli
      · simp only [hu1, ↓reduceIte] at hli
        by_cases hu2 : L[i]'(by omega) ∈ Z₂
        · exact hu2
        · simp [hu2] at hli
    · intro hu2
      have hu1 : u ∉ Z₁ := Finset.disjoint_right.mp hpart.disj12 hu2
      have huZ : u ∈ Z := hZ2_sub hu2
      have huL : u ∈ L := (mem_zListUpTo Z n u).mpr ⟨u.2, huZ⟩
      rcases List.mem_iff_getElem.mp huL with ⟨i, hiL, hLi⟩
      refine ⟨i, by omega, hLi, ?_⟩
      simp [l, templateOfPartition, hLi, hu1, hu2]
  have hp2 : partOfTemplate L l 2 = Z₃ := by
    ext u
    rw [partOfTemplate, mem_partOfTemplateUpTo_iff L l 2 hlL l.length le_rfl]
    constructor
    · rintro ⟨i, hi, rfl, hli⟩
      have hiL : i < L.length := by omega
      have huL : L[i] ∈ L := List.getElem_mem hiL
      have huZ : L[i] ∈ Z := ((mem_zListUpTo Z n _).mp huL).2
      have hget : l[i] = (if L[i] ∈ Z₁ then 0 else if L[i] ∈ Z₂ then 1 else 2) := by
        simp [l, templateOfPartition]
      rw [hget] at hli
      by_cases hu1 : L[i] ∈ Z₁
      · simp [hu1] at hli
      · simp only [hu1, ↓reduceIte] at hli
        by_cases hu2 : L[i] ∈ Z₂
        · simp [hu2] at hli
        · rw [← hpart.union_eq, Finset.mem_union, Finset.mem_union] at huZ
          rcases huZ with (h1 | h2) | h3
          · exact False.elim (hu1 h1)
          · exact False.elim (hu2 h2)
          · exact h3
    · intro hu3
      have hu1 : u ∉ Z₁ := Finset.disjoint_right.mp hpart.disj13 hu3
      have hu2 : u ∉ Z₂ := Finset.disjoint_right.mp hpart.disj23 hu3
      have huZ : u ∈ Z := hZ3_sub hu3
      have huL : u ∈ L := (mem_zListUpTo Z n u).mpr ⟨u.2, huZ⟩
      rcases List.mem_iff_getElem.mp huL with ⟨i, hiL, hLi⟩
      refine ⟨i, by omega, hLi, ?_⟩
      simp [l, templateOfPartition, hLi, hu1, hu2]
  have hc0 : countVal 0 l = Z₁.card := by
    rw [← card_partOfTemplate_eq L l 0 hlL hL_nodup, hp0]
  have hc1 : countVal 1 l = Z₂.card := by
    rw [← card_partOfTemplate_eq L l 1 hlL hL_nodup, hp1]
  have hc2 : countVal 2 l = Z₃.card := by
    rw [← card_partOfTemplate_eq L l 2 hlL hL_nodup, hp2]
  have hval : validTemplate ω l := by
    refine ⟨hl_len, ?_, ?_, ?_⟩
    · rw [hc0, hc2]; exact hpart.card_Z1
    · rw [hc1, hc2]; exact hpart.card_Z2
    · rw [hc2]; exact hpart.card_Z3
  exact ⟨l, (mem_validTernaryLists_iff ω l).mpr hval, hp0, hp1, hp2⟩

/-- Unrolled command populating `a_Z1 = 10` (`partOfTemplateUpTo L l 0 k`) and `a_Z2 = 11`
(`partOfTemplateUpTo L l 1 k`) from `a_Z_list = 13` for the first `k` entries of `l`. -/
def buildZ12Steps (l : List (Fin 3)) : ℕ → Cmd
  | 0 => .skip
  | k + 1 =>
    .seq (buildZ12Steps l k)
      (if hk : k < l.length then
        if l[k] = 0 then
          .seq (.assign 14 (.read 13 (.const k)))
            (.write 10 (.reg 14) (.const 1))
        else if l[k] = 1 then
          .seq (.assign 14 (.read 13 (.const k)))
            (.write 11 (.reg 14) (.const 1))
        else .skip
      else .skip)

/-- Allocate `a_Z1 = 10` and `a_Z2 = 11` of size `n = r_0` and populate them according to `l`. -/
def buildZ12Prog (l : List (Fin 3)) : Cmd :=
  .seq (.alloc 10 (.reg 0))
    (.seq (.alloc 11 (.reg 0))
      (buildZ12Steps l l.length))

theorem buildZ12Steps_exec {w n : ℕ} (Z : Finset (Fin n)) (l : List (Fin 3))
    (hlL : l.length = (zListUpTo Z n).length)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hl_w : l.length < 2 ^ w)
    (k : ℕ) (hk : k ≤ l.length) {s : State}
    (hZlist : IsZListArr (zListUpTo Z n) 13 s)
    (hZ1_0 : IsBitSet (∅ : Finset (Fin n)) 10 s)
    (hZ2_0 : IsBitSet (∅ : Finset (Fin n)) 11 s) :
    let L := zListUpTo Z n
    ∃ s' t_steps,
      Exec w (buildZ12Steps l k) s s' t_steps ∧
      t_steps ≤ 1 + 6 * k ∧
      IsBitSet (partOfTemplateUpTo L l 0 k) 10 s' ∧
      IsBitSet (partOfTemplateUpTo L l 1 k) 11 s' ∧
      (∀ a : Arr, a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 14 → s'.regs r = s.regs r) := by
  intro L
  induction k with
  | zero =>
    refine ⟨s, 1, .skip s, by omega, ?_, ?_, fun _ _ _ => rfl, fun _ _ => rfl⟩
    · simpa [partOfTemplateUpTo] using hZ1_0
    · simpa [partOfTemplateUpTo] using hZ2_0
  | succ k ih =>
    rcases ih (by omega) with ⟨s₁, t₁, hex₁, ht₁, hZ1_1, hZ2_1, harr₁, hreg₁⟩
    have hkl : k < l.length := by omega
    have hkL : k < L.length := by dsimp [L]; omega
    have hk_w : k < 2 ^ w := by omega
    let uk : Fin n := L[k]'hkL
    have huk_w : uk.1 < 2 ^ w := by have := uk.2; omega
    have hZlist₁ : IsZListArr L 13 s₁ := hZlist.of_arr_eq (harr₁ 13 (by decide) (by decide))
    rcases hZlist₁ with ⟨hlen13, hL_le_n, hall13⟩
    have hk_len13 : k < (s₁.arrs 13).length := by omega
    have hval13 : (s₁.arrs 13)[k]'hk_len13 = uk.1 := hall13 k hkL
    unfold buildZ12Steps
    simp only [hkl, ↓reduceDIte]
    by_cases hc0 : l[k] = 0
    · simp only [hc0, ↓reduceIte]
      let s₂ := s₁.setReg 14 uk.1
      have hex₂ : Exec w (.assign 14 (.read 13 (.const k))) s₁ s₂ 3 :=
        .assign (by simp [Expr.eval, checkWord, hk_w, hk_len13, hval13, huk_w])
      let s₃ := s₂.writeArr 10 uk.1 1
      have hex₃ : Exec w (.write 10 (.reg 14) (.const 1)) s₂ s₃ 3 :=
        .write (by simp [s₂, Expr.eval, checkWord, huk_w])
          (by simp [Expr.eval, checkWord, hw])
          (by simp [s₂, hZ1_1.1, uk.2])
      have hZ1_3 : IsBitSet (partOfTemplateUpTo L l 0 (k + 1)) 10 s₃ := by
        unfold partOfTemplateUpTo
        simp only [hkL, hkl, hc0, ↓reduceDIte, ↓reduceIte]
        exact (hZ1_1.of_arr_eq rfl).write_one uk
      have hZ2_3 : IsBitSet (partOfTemplateUpTo L l 1 (k + 1)) 11 s₃ := by
        have hc1 : l[k] ≠ 1 := by rw [hc0]; decide
        unfold partOfTemplateUpTo
        simp only [hkL, hkl, hc1, ↓reduceDIte, ↓reduceIte]
        exact hZ2_1.of_arr_eq (by simp [s₃, s₂])
      refine ⟨s₃, t₁ + (3 + 3), .seq hex₁ (.seq hex₂ hex₃), by omega, hZ1_3, hZ2_3,
        fun a ha10 ha11 => by simp [s₃, s₂, ha10, harr₁ a ha10 ha11],
        fun r hr14 => by simp [s₃, s₂, hr14, hreg₁ r hr14]⟩
    · simp only [hc0, ↓reduceIte]
      by_cases hc1 : l[k] = 1
      · simp only [hc1, ↓reduceIte]
        let s₂ := s₁.setReg 14 uk.1
        have hex₂ : Exec w (.assign 14 (.read 13 (.const k))) s₁ s₂ 3 :=
          .assign (by simp [Expr.eval, checkWord, hk_w, hk_len13, hval13, huk_w])
        let s₃ := s₂.writeArr 11 uk.1 1
        have hex₃ : Exec w (.write 11 (.reg 14) (.const 1)) s₂ s₃ 3 :=
          .write (by simp [s₂, Expr.eval, checkWord, huk_w])
            (by simp [Expr.eval, checkWord, hw])
            (by simp [s₂, hZ2_1.1, uk.2])
        have hZ1_3 : IsBitSet (partOfTemplateUpTo L l 0 (k + 1)) 10 s₃ := by
          unfold partOfTemplateUpTo
          simp only [hkL, hkl, hc0, ↓reduceDIte, ↓reduceIte]
          exact hZ1_1.of_arr_eq (by simp [s₃, s₂])
        have hZ2_3 : IsBitSet (partOfTemplateUpTo L l 1 (k + 1)) 11 s₃ := by
          unfold partOfTemplateUpTo
          simp only [hkL, hkl, hc1, ↓reduceDIte, ↓reduceIte]
          exact (hZ2_1.of_arr_eq rfl).write_one uk
        refine ⟨s₃, t₁ + (3 + 3), .seq hex₁ (.seq hex₂ hex₃), by omega, hZ1_3, hZ2_3,
          fun a ha10 ha11 => by simp [s₃, s₂, ha11, harr₁ a ha10 ha11],
          fun r hr14 => by simp [s₃, s₂, hr14, hreg₁ r hr14]⟩
      · simp only [hc1, ↓reduceIte]
        have hZ1_2 : IsBitSet (partOfTemplateUpTo L l 0 (k + 1)) 10 s₁ := by
          unfold partOfTemplateUpTo
          simp only [hkL, hkl, hc0, ↓reduceDIte, ↓reduceIte]
          exact hZ1_1
        have hZ2_2 : IsBitSet (partOfTemplateUpTo L l 1 (k + 1)) 11 s₁ := by
          unfold partOfTemplateUpTo
          simp only [hkL, hkl, hc1, ↓reduceDIte, ↓reduceIte]
          exact hZ2_1
        refine ⟨s₁, t₁ + 1, .seq hex₁ (.skip s₁), by omega, hZ1_2, hZ2_2, harr₁, hreg₁⟩

theorem buildZ12Prog_exec {w n : ℕ} (Z : Finset (Fin n)) (l : List (Fin 3))
    (hlL : l.length = (zListUpTo Z n).length)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hl_w : l.length < 2 ^ w)
    {s : State}
    (hZlist : IsZListArr (zListUpTo Z n) 13 s)
    (hr0 : s.regs 0 = n) :
    let L := zListUpTo Z n
    ∃ s' t_steps,
      Exec w (buildZ12Prog l) s s' t_steps ∧
      t_steps ≤ 2 * n + 6 * l.length + 3 ∧
      IsBitSet (partOfTemplate L l 0) 10 s' ∧
      IsBitSet (partOfTemplate L l 1) 11 s' ∧
      (∀ a : Arr, a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 14 → s'.regs r = s.regs r) := by
  intro L
  let s₁ := s.setArr 10 (List.replicate n 0)
  have hex₁ : Exec w (.alloc 10 (.reg 0)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hr0, hn_w])
  let s₂ := s₁.setArr 11 (List.replicate n 0)
  have hex₂ : Exec w (.alloc 11 (.reg 0)) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hr0, hn_w])
  have hZ1_0 : IsBitSet (∅ : Finset (Fin n)) 10 s₂ :=
    IsBitSet.empty_of_replicate (by simp [s₂, s₁])
  have hZ2_0 : IsBitSet (∅ : Finset (Fin n)) 11 s₂ :=
    IsBitSet.empty_of_replicate (by simp [s₂])
  have hZlist₂ : IsZListArr (zListUpTo Z n) 13 s₂ :=
    hZlist.of_arr_eq (by simp [s₂, s₁])
  rcases buildZ12Steps_exec Z l hlL hw hn_w hl_w l.length le_rfl
      (s := s₂) hZlist₂ hZ1_0 hZ2_0 with
    ⟨s₃, t₃, hex₃, ht₃, hZ1_3, hZ2_3, harr₃, hreg₃⟩
  refine ⟨s₃, (1 + n) + ((1 + n) + t₃), .seq hex₁ (.seq hex₂ hex₃),
    by omega, hZ1_3, hZ2_3,
    fun a ha10 ha11 => by rw [harr₃ a ha10 ha11]; simp [s₂, s₁, ha10, ha11],
    fun r hr14 => by rw [hreg₃ r hr14]; rfl⟩

/-! #### Subpart 5.3: External Neighborhoods `N₁, N₂` and Bad-Edge Check (`buildExtNeighborsProg`) -/

/-- If `a_A[r_x] != 0` and `a_B[r_y] != 0`, set `r_18 := 1` (`bad_edge := 1`). -/
def checkBadPairCmd (a_A a_B : Arr) (r_x r_y : Reg) : Cmd :=
  .ite (.read a_A (.reg r_x))
    (.ite (.read a_B (.reg r_y))
      (.assign 18 (.const 1))
      .skip)
    .skip

theorem checkBadPairCmd_exec {w n : ℕ} (A B : Finset (Fin n))
    (a_A a_B : Arr) (r_x r_y : Reg) (x y : Fin n) (P : Prop)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hA : IsBitSet A a_A s) (hB : IsBitSet B a_B s)
    (hrx : s.regs r_x = x.1) (hry : s.regs r_y = y.1)
    (hr18 : (s.regs 18 ≠ 0 ↔ P) ∧ s.regs 18 ≤ 1) :
    ∃ s' t_cmd,
      Exec w (checkBadPairCmd a_A a_B r_x r_y) s s' t_cmd ∧
      t_cmd ≤ 6 ∧
      ((s'.regs 18 ≠ 0 ↔ P ∨ (x ∈ A ∧ y ∈ B)) ∧ s'.regs 18 ≤ 1) ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 18 → s'.regs r = s.regs r) := by
  have hx_w : x.1 < 2 ^ w := by have := x.2; omega
  have hy_w : y.1 < 2 ^ w := by have := y.2; omega
  have hA_len : x.1 < (s.arrs a_A).length := by rw [hA.1]; exact x.2
  let vx := (s.arrs a_A)[x.1]'hA_len
  have hvx_le : vx ≤ 1 := hA.2.1 x
  have hvx_w : vx < 2 ^ w := by omega
  have hread_x : (Expr.read a_A (.reg r_x)).eval w s = some vx := by
    simp [Expr.eval, checkWord, hrx, hx_w, hA_len, vx, hvx_w]
  by_cases hxA : x ∈ A
  · have hvx_ne0 : vx ≠ 0 := (hA.2.2 x).mpr hxA
    have hB_len : y.1 < (s.arrs a_B).length := by rw [hB.1]; exact y.2
    let vy := (s.arrs a_B)[y.1]'hB_len
    have hvy_le : vy ≤ 1 := hB.2.1 y
    have hvy_w : vy < 2 ^ w := by omega
    have hread_y : (Expr.read a_B (.reg r_y)).eval w s = some vy := by
      simp [Expr.eval, checkWord, hry, hy_w, hB_len, vy, hvy_w]
    by_cases hyB : y ∈ B
    · have hvy_ne0 : vy ≠ 0 := (hB.2.2 y).mpr hyB
      let s₁ := s.setReg 18 1
      have hex_set : Exec w (.assign 18 (.const 1)) s s₁ 2 :=
        .assign (by simp [Expr.eval, checkWord, hw])
      refine ⟨s₁, 2 + (2 + 2),
        .ite_true hread_x hvx_ne0 (.ite_true hread_y hvy_ne0 hex_set),
        by omega,
        ⟨by simp [s₁, hxA, hyB], by simp [s₁]⟩,
        fun _ => rfl,
        fun r hr => by simp [s₁, hr]⟩
    · have hvy_eq0 : vy = 0 := by
        by_contra hne; exact hyB ((hB.2.2 y).mp hne)
      have hread_y0 : (Expr.read a_B (.reg r_y)).eval w s = some 0 := by
        rw [hread_y, hvy_eq0]
      refine ⟨s, 2 + (2 + 1),
        .ite_true hread_x hvx_ne0 (.ite_false hread_y0 (.skip s)),
        by omega,
        ⟨by simp [hr18.1, hyB], hr18.2⟩,
        fun _ => rfl, fun _ _ => rfl⟩
  · have hvx_eq0 : vx = 0 := by
      by_contra hne; exact hxA ((hA.2.2 x).mp hne)
    have hread_x0 : (Expr.read a_A (.reg r_x)).eval w s = some 0 := by
      rw [hread_x, hvx_eq0]
    refine ⟨s, 2 + 1, .ite_false hread_x0 (.skip s),
      by omega,
      ⟨by simp [hr18.1, hxA], hr18.2⟩,
      fun _ => rfl, fun _ _ => rfl⟩

/-- If `a_S[r_x] != 0` and `a_Z_bit[r_y] == 0` (`a_12[r_y] == 0`), mark `a_N[r_y] := 1`. -/
def markExtStepCmd (a_S a_N : Arr) (r_x r_y : Reg) : Cmd :=
  .ite (.read a_S (.reg r_x))
    (.ite (.read 12 (.reg r_y))
      .skip
      (.write a_N (.reg r_y) (.const 1)))
    .skip

theorem markExtStepCmd_exec {w n : ℕ} (Z S prev : Finset (Fin n))
    (a_S a_N : Arr) (r_x r_y : Reg) (x y : Fin n)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hZ : IsBitSet Z 12 s) (hS : IsBitSet S a_S s) (hN : IsBitSet prev a_N s)
    (hrx : s.regs r_x = x.1) (hry : s.regs r_y = y.1) :
    ∃ s' t_cmd,
      Exec w (markExtStepCmd a_S a_N r_x r_y) s s' t_cmd ∧
      t_cmd ≤ 7 ∧
      IsBitSet (if x ∈ S ∧ y ∉ Z then insert y prev else prev) a_N s' ∧
      (∀ a : Arr, a ≠ a_N → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, s'.regs r = s.regs r) := by
  have hx_w : x.1 < 2 ^ w := by have := x.2; omega
  have hy_w : y.1 < 2 ^ w := by have := y.2; omega
  have hS_len : x.1 < (s.arrs a_S).length := by rw [hS.1]; exact x.2
  let vx := (s.arrs a_S)[x.1]'hS_len
  have hvx_le : vx ≤ 1 := hS.2.1 x
  have hvx_w : vx < 2 ^ w := by omega
  have hread_x : (Expr.read a_S (.reg r_x)).eval w s = some vx := by
    simp [Expr.eval, checkWord, hrx, hx_w, hS_len, vx, hvx_w]
  by_cases hxS : x ∈ S
  · have hvx_ne0 : vx ≠ 0 := (hS.2.2 x).mpr hxS
    have hZ_len : y.1 < (s.arrs 12).length := by rw [hZ.1]; exact y.2
    let vy := (s.arrs 12)[y.1]'hZ_len
    have hvy_le : vy ≤ 1 := hZ.2.1 y
    have hvy_w : vy < 2 ^ w := by omega
    have hread_y : (Expr.read 12 (.reg r_y)).eval w s = some vy := by
      simp [Expr.eval, checkWord, hry, hy_w, hZ_len, vy, hvy_w]
    by_cases hyZ : y ∈ Z
    · have hvy_ne0 : vy ≠ 0 := (hZ.2.2 y).mpr hyZ
      refine ⟨s, 2 + (2 + 1),
        .ite_true hread_x hvx_ne0 (.ite_true hread_y hvy_ne0 (.skip s)),
        by omega,
        by simp [hxS, hyZ, hN],
        fun _ _ => rfl, fun _ => rfl⟩
    · have hvy_eq0 : vy = 0 := by
        by_contra hne; exact hyZ ((hZ.2.2 y).mp hne)
      have hread_y0 : (Expr.read 12 (.reg r_y)).eval w s = some 0 := by
        rw [hread_y, hvy_eq0]
      let s₁ := s.writeArr a_N y.1 1
      have hex_w : Exec w (.write a_N (.reg r_y) (.const 1)) s s₁ 3 :=
        .write (by simp [Expr.eval, checkWord, hry, hy_w])
          (by simp [Expr.eval, checkWord, hw])
          (by rw [hN.1]; exact y.2)
      refine ⟨s₁, 2 + (2 + 3),
        .ite_true hread_x hvx_ne0 (.ite_false hread_y0 hex_w),
        by omega,
        by simp [hxS, hyZ]; exact hN.write_one y,
        fun a ha => by simp [s₁, ha],
        fun _ => rfl⟩
  · have hvx_eq0 : vx = 0 := by
      by_contra hne; exact hxS ((hS.2.2 x).mp hne)
    have hread_x0 : (Expr.read a_S (.reg r_x)).eval w s = some 0 := by
      rw [hread_x, hvx_eq0]
    refine ⟨s, 2 + 1, .ite_false hread_x0 (.skip s),
      by omega,
      by simp [hxS, hN],
      fun _ _ => rfl, fun _ => rfl⟩

/-- Whether any active edge mapped to `v` among the first `m` entries of `edges` has one endpoint
in `Z₁` and the other in `Z₂`. -/
def hasBadEdgeUpTo {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z₁ Z₂ : Finset (Fin n)) : ℕ → Prop
  | 0 => False
  | m + 1 =>
    hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ m ∨
      ∃ hm : m < edges.length,
        (⟨m, hm⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨m, hm⟩ = v ∧
        (((edges[m]).1 ∈ Z₁ ∧ (edges[m]).2 ∈ Z₂) ∨
         ((edges[m]).1 ∈ Z₂ ∧ (edges[m]).2 ∈ Z₁))

/-- External neighbors of `S` outside `Z` in `leafGraph G τ v` accumulated over the first `m`
entries of `edges`. -/
def extNeighborsUpTo {n t : ℕ} (edges : List (Fin n × Fin n))
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z S : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => ∅
  | m + 1 =>
    let prev := extNeighborsUpTo edges aliveSet f_tau v Z S m
    if hm : m < edges.length then
      if (⟨m, hm⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨m, hm⟩ = v then
        let p1 := if (edges[m]).1 ∈ S ∧ (edges[m]).2 ∉ Z then insert (edges[m]).2 prev else prev
        if (edges[m]).2 ∈ S ∧ (edges[m]).1 ∉ Z then insert (edges[m]).1 p1 else p1
      else prev
    else prev

theorem hasBadEdgeUpTo_iff {n t : ℕ} (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z₁ Z₂ : Finset (Fin n)) :
    hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ edges.length ↔
      ∃ z₁ ∈ Z₁, ∃ z₂ ∈ Z₂,
        (leafGraph (graphOfAlive edges hedges.1 aliveSet)
          (tauOfArr edges t ht_pos f_tau) v).Adj z₁ z₂ := by
  have haux : ∀ m ≤ edges.length,
      hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ m ↔
        ∃ (k : ℕ) (hk : k < edges.length), k < m ∧
          (⟨k, hk⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk⟩ = v ∧
          (((edges[k]).1 ∈ Z₁ ∧ (edges[k]).2 ∈ Z₂) ∨
           ((edges[k]).1 ∈ Z₂ ∧ (edges[k]).2 ∈ Z₁)) := by
    intro m hm
    induction m with
    | zero => simp [hasBadEdgeUpTo]
    | succ m ih =>
      unfold hasBadEdgeUpTo
      rw [ih (by omega)]
      constructor
      · rintro (⟨k, hk, hkm, hrest⟩ | ⟨hm_lt, hrest⟩)
        · exact ⟨k, hk, by omega, hrest⟩
        · exact ⟨m, hm_lt, Nat.lt_succ_self m, hrest⟩
      · rintro ⟨k, hk, hkm, hrest⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hkm with hlt | rfl
        · exact Or.inl ⟨k, hk, hlt, hrest⟩
        · exact Or.inr ⟨hk, hrest⟩
  rw [haux edges.length le_rfl]
  constructor
  · rintro ⟨k, hk, _, hk_al, hfk_v, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · refine ⟨(edges[k]).1, h1, (edges[k]).2, h2, ⟨⟨k, hk⟩, hk_al, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
      change tauOfArr edges t ht_pos f_tau (symEdgeAt edges ⟨k, hk⟩) = v
      rw [tauOfArr_symEdgeAt hedges, hfk_v]
    · refine ⟨(edges[k]).2, h2, (edges[k]).1, h1, ⟨⟨k, hk⟩, hk_al, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
      have hsym : s((edges[k]).2, (edges[k]).1) = symEdgeAt edges ⟨k, hk⟩ := Sym2.eq_swap
      rw [hsym, tauOfArr_symEdgeAt hedges, hfk_v]
  · rintro ⟨z₁, hz₁, z₂, hz₂, ⟨k, hk_al, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩, htau_v⟩
    · have hsym : s(z₁, z₂) = symEdgeAt edges k := by
        unfold symEdgeAt; rw [h1, h2]
      rw [hsym, tauOfArr_symEdgeAt hedges] at htau_v
      exact ⟨k.1, k.2, k.2, hk_al, htau_v, Or.inl ⟨h1 ▸ hz₁, h2 ▸ hz₂⟩⟩
    · have hsym : s(z₁, z₂) = symEdgeAt edges k := by
        unfold symEdgeAt; rw [h1, h2, Sym2.eq_swap]
      rw [hsym, tauOfArr_symEdgeAt hedges] at htau_v
      exact ⟨k.1, k.2, k.2, hk_al, htau_v, Or.inr ⟨h1 ▸ hz₂, h2 ▸ hz₁⟩⟩

theorem extNeighborsUpTo_eq_extNeighbors {n t : ℕ} (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z S : Finset (Fin n)) :
    extNeighborsUpTo edges aliveSet f_tau v Z S edges.length =
      extNeighbors
        (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        Z S := by
  have haux : ∀ m ≤ edges.length, ∀ u : Fin n,
      u ∈ extNeighborsUpTo edges aliveSet f_tau v Z S m ↔
        ∃ (k : ℕ) (hk : k < edges.length), k < m ∧
          (⟨k, hk⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk⟩ = v ∧ u ∉ Z ∧
          (((edges[k]).1 ∈ S ∧ (edges[k]).2 = u) ∨
           ((edges[k]).2 ∈ S ∧ (edges[k]).1 = u)) := by
    intro m hm u
    induction m with
    | zero => simp [extNeighborsUpTo]
    | succ m ih =>
      have hm_lt : m < edges.length := by omega
      unfold extNeighborsUpTo
      simp only [hm_lt, ↓reduceDIte]
      by_cases hcond : (⟨m, hm_lt⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨m, hm_lt⟩ = v
      · simp only [hcond, and_self, ↓reduceIte]
        have hmem_p1 : ∀ (prev : Finset (Fin n)) (c : Prop) [Decidable c] (w : Fin n),
            u ∈ (if c then insert w prev else prev) ↔ (c ∧ u = w) ∨ u ∈ prev := by
          intro prev c _ w
          split_ifs with hc <;> simp [hc]
        rw [hmem_p1, hmem_p1, ih (by omega)]
        constructor
        · rintro (⟨⟨h2S, h1Z⟩, rfl⟩ | ⟨⟨h1S, h2Z⟩, rfl⟩ | ⟨k, hk, hkm, hrest⟩)
          · exact ⟨m, hm_lt, Nat.lt_succ_self m, hcond.1, hcond.2, h1Z, Or.inr ⟨h2S, rfl⟩⟩
          · exact ⟨m, hm_lt, Nat.lt_succ_self m, hcond.1, hcond.2, h2Z, Or.inl ⟨h1S, rfl⟩⟩
          · exact ⟨k, hk, Nat.lt_succ_of_lt hkm, hrest⟩
        · rintro ⟨k, hk, hkm, hk_al, hfk_v, huZ, hmatch⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hkm with hlt | rfl
          · exact Or.inr (Or.inr ⟨k, hk, hlt, hk_al, hfk_v, huZ, hmatch⟩)
          · rcases hmatch with ⟨h1S, rfl⟩ | ⟨h2S, rfl⟩
            · exact Or.inr (Or.inl ⟨⟨h1S, huZ⟩, rfl⟩)
            · exact Or.inl ⟨⟨h2S, huZ⟩, rfl⟩
      · simp only [hcond, ↓reduceIte, ih (by omega)]
        constructor
        · rintro ⟨k, hk, hkm, hrest⟩
          exact ⟨k, hk, Nat.lt_succ_of_lt hkm, hrest⟩
        · rintro ⟨k, hk, hkm, hk_al, hfk_v, hrest⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hkm with hlt | rfl
          · exact ⟨k, hk, hlt, hk_al, hfk_v, hrest⟩
          · exact False.elim (hcond ⟨hk_al, hfk_v⟩)
  ext u
  rw [haux edges.length le_rfl u, mem_extNeighbors]
  constructor
  · rintro ⟨k, hk, _, hk_al, hfk_v, huZ, ⟨h1S, rfl⟩ | ⟨h2S, rfl⟩⟩
    · refine ⟨huZ, (edges[k]).1, h1S, ⟨⟨k, hk⟩, hk_al, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
      change tauOfArr edges t ht_pos f_tau (symEdgeAt edges ⟨k, hk⟩) = v
      rw [tauOfArr_symEdgeAt hedges, hfk_v]
    · refine ⟨huZ, (edges[k]).2, h2S, ⟨⟨k, hk⟩, hk_al, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
      have hsym : s((edges[k]).2, (edges[k]).1) = symEdgeAt edges ⟨k, hk⟩ := Sym2.eq_swap
      rw [hsym, tauOfArr_symEdgeAt hedges, hfk_v]
  · rintro ⟨huZ, z, hzS, ⟨k, hk_al, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩, htau_v⟩
    · have hsym : s(z, u) = symEdgeAt edges k := by
        unfold symEdgeAt; rw [h1, h2]
      rw [hsym, tauOfArr_symEdgeAt hedges] at htau_v
      exact ⟨k.1, k.2, k.2, hk_al, htau_v, huZ, Or.inl ⟨h1 ▸ hzS, h2⟩⟩
    · have hsym : s(z, u) = symEdgeAt edges k := by
        unfold symEdgeAt; rw [h1, h2, Sym2.eq_swap]
      rw [hsym, tauOfArr_symEdgeAt hedges] at htau_v
      exact ⟨k.1, k.2, k.2, hk_al, htau_v, huZ, Or.inr ⟨h2 ▸ hzS, h1⟩⟩

/-- Inner update of `r_18` (`bad_edge`), `a_18` (`N₁`), and `a_19` (`N₂`) for endpoints
`(r_12, r_13)` of an active edge mapped to `v`. -/
def updateExtAndBadCmd : Cmd :=
  .seq (checkBadPairCmd 10 11 12 13)
    (.seq (checkBadPairCmd 11 10 12 13)
      (.seq (markExtStepCmd 10 18 12 13)
        (.seq (markExtStepCmd 10 18 13 12)
          (.seq (markExtStepCmd 11 19 12 13)
            (markExtStepCmd 11 19 13 12)))))

/-- Loop body for `buildExtNeighborsProg` over edge index `r_11 < r_2`. -/
def buildExtNeighborsBody : Cmd :=
  .ite (.read 4 (.reg 11))
    (.ite (.op .eq (.read 5 (.reg 11)) (.reg 7))
      (.seq (.assign 12 (.read 2 (.reg 11)))
        (.seq (.assign 13 (.read 3 (.reg 11)))
          updateExtAndBadCmd))
      .skip)
    .skip

theorem buildExtNeighborsBody_exec {w n t : ℕ}
    (edges : List (Fin n × Fin n)) (aliveSet : Finset (Fin edges.length))
    (f_tau : Fin edges.length → Fin t) (v : Fin t)
    (Z Z₁ Z₂ : Finset (Fin n)) (k : ℕ) (hk : k < edges.length)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : edges.length < 2 ^ w) (ht_w : t < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hZ1 : IsBitSet Z₁ 10 s)
    (hZ2 : IsBitSet Z₂ 11 s)
    (hZ : IsBitSet Z 12 s)
    (hN1 : IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₁ k) 18 s)
    (hN2 : IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₂ k) 19 s)
    (hbad : (s.regs 18 ≠ 0 ↔ hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ k) ∧ s.regs 18 ≤ 1)
    (hr7 : s.regs 7 = v.1)
    (hr11 : s.regs 11 = k) :
    ∃ s' t_body,
      Exec w buildExtNeighborsBody s s' t_body ∧
      t_body ≤ 52 ∧
      IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₁ (k + 1)) 18 s' ∧
      IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₂ (k + 1)) 19 s' ∧
      ((s'.regs 18 ≠ 0 ↔ hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ (k + 1)) ∧ s'.regs 18 ≤ 1) ∧
      (∀ a : Arr, a ≠ 18 → a ≠ 19 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 12 → r ≠ 13 → r ≠ 18 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  let k_fin : Fin edges.length := ⟨k, hk⟩
  have hal_len : k < (s.arrs 4).length := by rw [hal.1]; exact hk
  let al_k := (s.arrs 4)[k]'hal_len
  have hal_le : al_k ≤ 1 := hal.2.1 k_fin
  have hal_w : al_k < 2 ^ w := by omega
  have hread_al : (Expr.read 4 (.reg 11)).eval w s = some al_k := by
    simp [Expr.eval, checkWord, hr11, hk_w, hal_len, al_k, hal_w]
  by_cases h_al : k_fin ∈ aliveSet
  · have hal_ne0 : al_k ≠ 0 := (hal.2.2 k_fin).mpr h_al
    have htau_k_w : (f_tau k_fin).1 < 2 ^ w := by have := (f_tau k_fin).2; omega
    rcases htau with ⟨hlen5, hall5⟩
    have hk_len5 : k < (s.arrs 5).length := by rw [hlen5]; exact hk
    have hval5 : (s.arrs 5)[k]'hk_len5 = (f_tau k_fin).1 := hall5 k_fin
    by_cases h_v : f_tau k_fin = v
    · have hval_eq : (f_tau k_fin).1 = v.1 := congrArg Fin.val h_v
      have hcond_v : (Expr.op .eq (.read 5 (.reg 11)) (.reg 7)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hk_w, hk_len5, hval5,
          hr7, hv_w, hval_eq, hw]
      rcases hend with ⟨hlen2, hlen3, hall23⟩
      let u := (edges[k]).1
      let y := (edges[k]).2
      have hu_w : u.1 < 2 ^ w := by have := u.2; omega
      have hy_w : y.1 < 2 ^ w := by have := y.2; omega
      have hk_len2 : k < (s.arrs 2).length := by rw [hlen2]; exact hk
      have hval2 : (s.arrs 2)[k]'hk_len2 = u.1 := (hall23 k_fin).1
      let s₁ := s.setReg 12 u.1
      have hex₁ : Exec w (.assign 12 (.read 2 (.reg 11))) s s₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, hr11, hk_w, hk_len2, hval2, hu_w])
      have hk_len3 : k < (s.arrs 3).length := by rw [hlen3]; exact hk
      have hval3 : (s.arrs 3)[k]'hk_len3 = y.1 := (hall23 k_fin).2
      let s₂ := s₁.setReg 13 y.1
      have hex₂ : Exec w (.assign 13 (.read 3 (.reg 11))) s₁ s₂ 3 :=
        .assign (by simp [s₁, Expr.eval, checkWord, hr11, hk_w, hk_len3, hval3, hy_w])
      rcases checkBadPairCmd_exec Z₁ Z₂ 10 11 12 13 u y
          (hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ k) hw hn_w (s := s₂)
          (hZ1.of_arr_eq rfl) (hZ2.of_arr_eq rfl)
          (by simp [s₂, s₁, u]) (by simp [s₂, y])
          ⟨by simpa [s₂, s₁] using hbad.1, by simpa [s₂, s₁] using hbad.2⟩ with
        ⟨s₃, t₃, hex₃, ht₃, hbad₃, harr₃, hreg₃⟩
      rcases checkBadPairCmd_exec Z₂ Z₁ 11 10 12 13 u y
          (hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ k ∨ (u ∈ Z₁ ∧ y ∈ Z₂))
          hw hn_w (s := s₃)
          (hZ2.of_arr_eq (harr₃ 11)) (hZ1.of_arr_eq (harr₃ 10))
          (by rw [hreg₃ 12 (by decide)]; simp [s₂, s₁, u])
          (by rw [hreg₃ 13 (by decide)]; simp [s₂, y])
          hbad₃ with
        ⟨s₄, t₄, hex₄, ht₄, hbad₄, harr₄, hreg₄⟩
      have hru₄ : s₄.regs 12 = u.1 := by
        rw [hreg₄ 12 (by decide), hreg₃ 12 (by decide)]; simp [s₂, s₁, u]
      have hry₄ : s₄.regs 13 = y.1 := by
        rw [hreg₄ 13 (by decide), hreg₃ 13 (by decide)]; simp [s₂, y]
      rcases markExtStepCmd_exec Z Z₁ (extNeighborsUpTo edges aliveSet f_tau v Z Z₁ k)
          10 18 12 13 u y hw hn_w (s := s₄)
          (hZ.of_arr_eq (by rw [harr₄ 12, harr₃ 12]; rfl))
          (hZ1.of_arr_eq (by rw [harr₄ 10, harr₃ 10]; rfl))
          (hN1.of_arr_eq (by rw [harr₄ 18, harr₃ 18]; rfl))
          hru₄ hry₄ with
        ⟨s₅, t₅, hex₅, ht₅, hN1_5, harr₅, hreg₅⟩
      rcases markExtStepCmd_exec Z Z₁ _ 10 18 13 12 y u hw hn_w (s := s₅)
          (hZ.of_arr_eq (by rw [harr₅ 12 (by decide), harr₄ 12, harr₃ 12]; rfl))
          (hZ1.of_arr_eq (by rw [harr₅ 10 (by decide), harr₄ 10, harr₃ 10]; rfl))
          hN1_5
          (by rw [hreg₅ 13, hry₄]) (by rw [hreg₅ 12, hru₄]) with
        ⟨s₆, t₆, hex₆, ht₆, hN1_6, harr₆, hreg₆⟩
      rcases markExtStepCmd_exec Z Z₂ (extNeighborsUpTo edges aliveSet f_tau v Z Z₂ k)
          11 19 12 13 u y hw hn_w (s := s₆)
          (hZ.of_arr_eq (by rw [harr₆ 12 (by decide), harr₅ 12 (by decide), harr₄ 12, harr₃ 12]; rfl))
          (hZ2.of_arr_eq (by rw [harr₆ 11 (by decide), harr₅ 11 (by decide), harr₄ 11, harr₃ 11]; rfl))
          (hN2.of_arr_eq (by rw [harr₆ 19 (by decide), harr₅ 19 (by decide), harr₄ 19, harr₃ 19]; rfl))
          (by rw [hreg₆ 12, hreg₅ 12, hru₄]) (by rw [hreg₆ 13, hreg₅ 13, hry₄]) with
        ⟨s₇, t₇, hex₇, ht₇, hN2_7, harr₇, hreg₇⟩
      rcases markExtStepCmd_exec Z Z₂ _ 11 19 13 12 y u hw hn_w (s := s₇)
          (hZ.of_arr_eq (by
            rw [harr₇ 12 (by decide), harr₆ 12 (by decide), harr₅ 12 (by decide), harr₄ 12, harr₃ 12]; rfl))
          (hZ2.of_arr_eq (by
            rw [harr₇ 11 (by decide), harr₆ 11 (by decide), harr₅ 11 (by decide), harr₄ 11, harr₃ 11]; rfl))
          hN2_7
          (by rw [hreg₇ 13, hreg₆ 13, hreg₅ 13, hry₄])
          (by rw [hreg₇ 12, hreg₆ 12, hreg₅ 12, hru₄]) with
        ⟨s₈, t₈, hex₈, ht₈, hN2_8, harr₈, hreg₈⟩
      have hN1_8 : IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₁ (k + 1)) 18 s₈ := by
        have hcond_k : (⟨k, hk⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk⟩ = v := ⟨h_al, h_v⟩
        unfold extNeighborsUpTo
        simp only [hk, hcond_k, and_self, ↓reduceDIte, ↓reduceIte]
        exact hN1_6.of_arr_eq (by rw [harr₈ 18 (by decide), harr₇ 18 (by decide)])
      have hN2_8' : IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₂ (k + 1)) 19 s₈ := by
        have hcond_k : (⟨k, hk⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk⟩ = v := ⟨h_al, h_v⟩
        unfold extNeighborsUpTo
        simp only [hk, hcond_k, and_self, ↓reduceDIte, ↓reduceIte]
        exact hN2_8
      have hbad₈ : (s₈.regs 18 ≠ 0 ↔ hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ (k + 1)) ∧
          s₈.regs 18 ≤ 1 := by
        have hr18_eq : s₈.regs 18 = s₄.regs 18 := by
          rw [hreg₈ 18, hreg₇ 18, hreg₆ 18, hreg₅ 18]
        rw [hr18_eq]
        refine ⟨?_, hbad₄.2⟩
        rw [hbad₄.1]
        simp only [hasBadEdgeUpTo]
        constructor
        · rintro ((hprev | h1) | h2)
          · exact Or.inl hprev
          · exact Or.inr ⟨hk, h_al, h_v, Or.inl h1⟩
          · exact Or.inr ⟨hk, h_al, h_v, Or.inr ⟨h2.1, h2.2⟩⟩
        · rintro (hprev | ⟨_, _, _, h1 | h2⟩)
          · exact Or.inl (Or.inl hprev)
          · exact Or.inl (Or.inr h1)
          · exact Or.inr ⟨h2.1, h2.2⟩
      refine ⟨s₈, 2 + (4 + (3 + (3 + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + t₈)))))))),
        .ite_true hread_al hal_ne0
          (.ite_true hcond_v (by omega)
            (.seq hex₁ (.seq hex₂
              (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))))),
        by omega, hN1_8, hN2_8', hbad₈,
        fun a ha18 ha19 => by
          rw [harr₈ a ha19, harr₇ a ha19, harr₆ a ha18, harr₅ a ha18, harr₄ a, harr₃ a]
          rfl,
        fun r hr12 hr13 hr18 => by
          rw [hreg₈ r, hreg₇ r, hreg₆ r, hreg₅ r, hreg₄ r hr18, hreg₃ r hr18]
          simp [s₂, s₁, hr12, hr13]⟩
    · have hval_ne : (f_tau k_fin).1 ≠ v.1 := fun h => h_v (Fin.ext h)
      have hcond_v : (Expr.op .eq (.read 5 (.reg 11)) (.reg 7)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hk_w, hk_len5, hval5,
          htau_k_w, hr7, hv_w, hval_ne, h0_w]
      have hnot_cond : ¬ ((⟨k, hk⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk⟩ = v) :=
        fun h => h_v h.2
      have hbad_eq : hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ (k + 1) ↔
          hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ k := by
        simp only [hasBadEdgeUpTo]
        exact ⟨fun h => h.resolve_right (fun ⟨_, _, hv, _⟩ => h_v hv), Or.inl⟩
      refine ⟨s, 2 + (4 + 1),
        .ite_true hread_al hal_ne0 (.ite_false hcond_v (.skip s)),
        by omega,
        by simpa [extNeighborsUpTo, hk, hnot_cond] using hN1,
        by simpa [extNeighborsUpTo, hk, hnot_cond] using hN2,
        ⟨hbad.1.trans hbad_eq.symm, hbad.2⟩,
        fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  · have hal_eq0 : al_k = 0 := by
      by_contra hne; exact h_al ((hal.2.2 k_fin).mp hne)
    have hread_al0 : (Expr.read 4 (.reg 11)).eval w s = some 0 := by
      rw [hread_al, hal_eq0]
    have hnot_cond : ¬ ((⟨k, hk⟩ : Fin edges.length) ∈ aliveSet ∧ f_tau ⟨k, hk⟩ = v) :=
      fun h => h_al h.1
    have hbad_eq : hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ (k + 1) ↔
        hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ k := by
      simp only [hasBadEdgeUpTo]
      exact ⟨fun h => h.resolve_right (fun ⟨_, ha, _, _⟩ => h_al ha), Or.inl⟩
    refine ⟨s, 2 + 1, .ite_false hread_al0 (.skip s),
      by omega,
      by simpa [extNeighborsUpTo, hk, hnot_cond] using hN1,
      by simpa [extNeighborsUpTo, hk, hnot_cond] using hN2,
      ⟨hbad.1.trans hbad_eq.symm, hbad.2⟩,
      fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem buildExtNeighborsLoop_exec {w n t : ℕ}
    (edges : List (Fin n × Fin n)) (aliveSet : Finset (Fin edges.length))
    (f_tau : Fin edges.length → Fin t) (v : Fin t)
    (Z Z₁ Z₂ : Finset (Fin n))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : edges.length < 2 ^ w) (ht_w : t < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = edges.length)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hZ1 : IsBitSet Z₁ 10 s)
    (hZ2 : IsBitSet Z₂ 11 s)
    (hZ : IsBitSet Z 12 s)
    (hN1 : IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₁ k) 18 s)
    (hN2 : IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₂ k) 19 s)
    (hbad : (s.regs 18 ≠ 0 ↔ hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ k) ∧ s.regs 18 ≤ 1)
    (hr2 : s.regs 2 = edges.length)
    (hr7 : s.regs 7 = v.1)
    (hr11 : s.regs 11 = k) :
    ∃ s' t_loop,
      Exec w (forUp 11 (.reg 2) buildExtNeighborsBody) s s' t_loop ∧
      t_loop ≤ 3 + 59 * rem ∧
      IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₁ edges.length) 18 s' ∧
      IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₂ edges.length) 19 s' ∧
      ((s'.regs 18 ≠ 0 ↔ hasBadEdgeUpTo edges aliveSet f_tau v Z₁ Z₂ edges.length) ∧
        s'.regs 18 ≤ 1) ∧
      (∀ a : Arr, a ≠ 18 → a ≠ 19 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 18 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = edges.length := by omega
    rw [hk_eq] at hr11 hN1 hN2 hbad
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hm2_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hN1, hN2, hbad,
      fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < edges.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hk_w, hm2_w, hk_lt, hw]
    rcases buildExtNeighborsBody_exec edges aliveSet f_tau v Z Z₁ Z₂ k hk_lt
        hw hn_w hm2_w ht_w hend hal htau hZ1 hZ2 hZ hN1 hN2 hbad hr7 hr11 with
      ⟨s₁, t₁, hex₁, ht₁, hN1_1, hN2_1, hbad₁, harr₁, hreg₁⟩
    have hr11_1 : s₁.regs 11 = k := by
      rw [hreg₁ 11 (by decide) (by decide) (by decide), hr11]
    let s₂ := s₁.setReg 11 (k + 1)
    have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11_1, hk_w, hw, hk1_w])
    rcases ih (k + 1) (by omega) (s := s₂)
        (hend.of_arrs_eq (harr₁ 2 (by decide) (by decide)) (harr₁ 3 (by decide) (by decide)))
        (hal.of_arr_eq (harr₁ 4 (by decide) (by decide)))
        (htau.of_arr_eq (harr₁ 5 (by decide) (by decide)))
        (hZ1.of_arr_eq (harr₁ 10 (by decide) (by decide)))
        (hZ2.of_arr_eq (harr₁ 11 (by decide) (by decide)))
        (hZ.of_arr_eq (harr₁ 12 (by decide) (by decide)))
        (hN1_1.of_arr_eq rfl)
        (hN2_1.of_arr_eq rfl)
        ⟨by simpa [s₂] using hbad₁.1, by simpa [s₂] using hbad₁.2⟩
        (by simp [s₂, hreg₁ 2 (by decide) (by decide) (by decide), hr2])
        (by simp [s₂, hreg₁ 7 (by decide) (by decide) (by decide), hr7])
        (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, hN1_3, hN2_3, hbad₃, harr₃, hreg₃⟩
    refine ⟨s₃, 3 + (t₁ + 4) + t₃,
      .while_true hcond (by omega) (.seq hex₁ hex_inc) hex₃,
      by omega, hN1_3, hN2_3, hbad₃,
      fun a ha18 ha19 => by rw [harr₃ a ha18 ha19]; exact harr₁ a ha18 ha19,
      fun r hr11' hr12 hr13 hr18 => by
        rw [hreg₃ r hr11' hr12 hr13 hr18]
        simp [s₂, hr11', hreg₁ r hr12 hr13 hr18]⟩

/-- Allocate `a_A = 18` and `a_B = 19` of size `n = r_0`, set `r_18 := 0` (`bad_edge := 0`) and
`r_11 := 0`, and scan `r_11 < r_2` to compute `extNeighbors R Z Z₁`, `extNeighbors R Z Z₂`, and
the `bad_edge` flag in `r_18`. -/
def buildExtNeighborsProg : Cmd :=
  .seq (.alloc 18 (.reg 0))
    (.seq (.alloc 19 (.reg 0))
      (.seq (.assign 18 (.const 0))
        (.seq (.assign 11 (.const 0))
          (forUp 11 (.reg 2) buildExtNeighborsBody))))

theorem buildExtNeighborsProg_exec {w n t : ℕ} (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z Z₁ Z₂ : Finset (Fin n))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : edges.length < 2 ^ w) (ht_w : t < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hZ1 : IsBitSet Z₁ 10 s)
    (hZ2 : IsBitSet Z₂ 11 s)
    (hZ : IsBitSet Z 12 s)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = edges.length)
    (hr7 : s.regs 7 = v.1) :
    let R := leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v
    ∃ s' t_ext,
      Exec w buildExtNeighborsProg s s' t_ext ∧
      t_ext ≤ 2 * n + 59 * edges.length + 9 ∧
      IsBitSet (extNeighbors R Z Z₁) 18 s' ∧
      IsBitSet (extNeighbors R Z Z₂) 19 s' ∧
      ((s'.regs 18 ≠ 0 ↔ ∃ z₁ ∈ Z₁, ∃ z₂ ∈ Z₂, R.Adj z₁ z₂) ∧ s'.regs 18 ≤ 1) ∧
      (∀ a : Arr, a ≠ 18 → a ≠ 19 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 18 → s'.regs r = s.regs r) := by
  intro R
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 18 (List.replicate n 0)
  have hex₁ : Exec w (.alloc 18 (.reg 0)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hr0, hn_w])
  let s₂ := s₁.setArr 19 (List.replicate n 0)
  have hex₂ : Exec w (.alloc 19 (.reg 0)) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hr0, hn_w])
  let s₃ := s₂.setReg 18 0
  have hex₃ : Exec w (.assign 18 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg 11 0
  have hex₄ : Exec w (.assign 11 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hN1_0 : IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₁ 0) 18 s₄ :=
    IsBitSet.empty_of_replicate (by simp [s₄, s₃, s₂, s₁])
  have hN2_0 : IsBitSet (extNeighborsUpTo edges aliveSet f_tau v Z Z₂ 0) 19 s₄ :=
    IsBitSet.empty_of_replicate (by simp [s₄, s₃, s₂])
  rcases buildExtNeighborsLoop_exec edges aliveSet f_tau v Z Z₁ Z₂
      hw hn_w hm2_w ht_w edges.length 0 (by omega) (s := s₄)
      (hend.of_arrs_eq (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁]))
      (hal.of_arr_eq (by simp [s₄, s₃, s₂, s₁]))
      (htau.of_arr_eq (by simp [s₄, s₃, s₂, s₁]))
      (hZ1.of_arr_eq (by simp [s₄, s₃, s₂, s₁]))
      (hZ2.of_arr_eq (by simp [s₄, s₃, s₂, s₁]))
      (hZ.of_arr_eq (by simp [s₄, s₃, s₂, s₁]))
      hN1_0 hN2_0
      ⟨by simp [s₄, s₃, hasBadEdgeUpTo], by simp [s₄, s₃]⟩
      (by simp [s₄, s₃, s₂, s₁, hr2])
      (by simp [s₄, s₃, s₂, s₁, hr7])
      (by simp [s₄]) with
    ⟨s₅, t₅, hex₅, ht₅, hN1_5, hN2_5, hbad₅, harr₅, hreg₅⟩
  rw [extNeighborsUpTo_eq_extNeighbors ht_pos hedges] at hN1_5 hN2_5
  rw [hasBadEdgeUpTo_iff ht_pos hedges] at hbad₅
  refine ⟨s₅, (1 + n) + ((1 + n) + (2 + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hN1_5, hN2_5, hbad₅,
    fun a ha18 ha19 => by rw [harr₅ a ha18 ha19]; simp [s₄, s₃, s₂, s₁, ha18, ha19],
    fun r hr11 hr12 hr13 hr18 => by
      rw [hreg₅ r hr11 hr12 hr13 hr18]
      simp [s₄, s₃, s₂, s₁, hr11, hr18]⟩

/-! #### Subpart 5.4: Step (5) Leaf-Splitting and Single-Template Check (`checkOneTemplateProg`) -/

/-- Whether a vertex `u : Fin n` belongs to the left side of the Step (5) split:
`u ∈ Z₁ ∨ (u ∉ Z ∧ u.1 + n ∈ items)`. -/
def inLeftSide {n : ℕ} (Z Z₁ : Finset (Fin n)) (items : List ℕ) (u : Fin n) : Prop :=
  u ∈ Z₁ ∨ (u ∉ Z ∧ u.1 + n ∈ items)

instance instDecidableInLeftSide {n : ℕ} (Z Z₁ : Finset (Fin n)) (items : List ℕ) (u : Fin n) :
    Decidable (inLeftSide Z Z₁ items u) := by
  unfold inLeftSide
  infer_instance

/-- Updated leaf assignment `f_tau` in Step (5): for `k` with `f_tau k = v`, maps `k` to `t` if
either endpoint of `edges[k]` satisfies `inLeftSide Z Z₁ items`, and to `t + 1` otherwise; leaves
all `k` with `f_tau k ≠ v` unchanged. -/
def step5FTau {n t : ℕ} (edges : List (Fin n × Fin n)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z Z₁ : Finset (Fin n)) (items : List ℕ)
    (k : Fin edges.length) : Fin (t + 2) :=
  if f_tau k = v then
    if inLeftSide Z Z₁ items (edges[k.1]).1 ∨ inLeftSide Z Z₁ items (edges[k.1]).2 then
      ⟨t, by omega⟩
    else
      ⟨t + 1, by omega⟩
  else
    ⟨(f_tau k).1, by have := (f_tau k).2; omega⟩

/-- Partial update of `f_tau` up to index `idx` in `step5Loop`. -/
def step5FTauUpTo {n t : ℕ} (edges : List (Fin n × Fin n)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z Z₁ : Finset (Fin n)) (items : List ℕ)
    (idx : ℕ) (k : Fin edges.length) : Fin (t + 2) :=
  if k.1 < idx then
    step5FTau edges f_tau v Z Z₁ items k
  else
    ⟨(f_tau k).1, by have := (f_tau k).2; omega⟩

/-- Check whether vertex `r_x` satisfies `inLeftSide Z Z₁ items`; if so, set `r_14 := 1`. -/
def checkInLeftCmd (r_x : Reg) : Cmd :=
  .ite (.read 10 (.reg r_x))
    (.assign 14 (.const 1))
    (.ite (.read 12 (.reg r_x))
      .skip
      (.ite (.read 23 (.op .add (.reg r_x) (.reg 0)))
        (.assign 14 (.const 1))
        .skip))

theorem checkInLeftCmd_exec {w n : ℕ} (Z Z₁ : Finset (Fin n)) (items : List ℕ)
    (r_x : Reg) (x : Fin n) (prev : Prop)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {s : State}
    (hZ1 : IsBitSet Z₁ 10 s)
    (hZ : IsBitSet Z 12 s)
    (hvis : IsResVisArr n 23 items s)
    (hr0 : s.regs 0 = n)
    (hrx : s.regs r_x = x.1)
    (hr14 : (s.regs 14 ≠ 0 ↔ prev) ∧ s.regs 14 ≤ 1) :
    ∃ s' t_chk,
      Exec w (checkInLeftCmd r_x) s s' t_chk ∧
      t_chk ≤ 10 ∧
      ((s'.regs 14 ≠ 0 ↔ (prev ∨ inLeftSide Z Z₁ items x)) ∧ s'.regs 14 ≤ 1) ∧
      s'.arrs = s.arrs ∧
      (∀ r : Reg, r ≠ 14 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hx_w : x.1 < 2 ^ w := by have := x.2; omega
  have hxn_lt : x.1 + n < 2 * n := by have := x.2; omega
  have hxn_w : x.1 + n < 2 ^ w := by omega
  have hZ1_len : x.1 < (s.arrs 10).length := by rw [hZ1.1]; exact x.2
  let v1 := (s.arrs 10)[x.1]'hZ1_len
  have hv1_le : v1 ≤ 1 := hZ1.2.1 x
  have hv1_w : v1 < 2 ^ w := by omega
  have hread10 : (Expr.read 10 (.reg r_x)).eval w s = some v1 := by
    simp [Expr.eval, checkWord, hrx, hx_w, hZ1_len, v1, hv1_w]
  by_cases hx1 : x ∈ Z₁
  · have hv1_ne0 : v1 ≠ 0 := (hZ1.2.2 x).mpr hx1
    let s₁ := s.setReg 14 1
    have hex₁ : Exec w (.assign 14 (.const 1)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    have hx_left : inLeftSide Z Z₁ items x := Or.inl hx1
    refine ⟨s₁, 2 + 2, .ite_true hread10 hv1_ne0 hex₁, by omega,
      ⟨by simp [s₁, hx_left], by simp [s₁]⟩, rfl,
      fun r hr14' => by simp [s₁, hr14']⟩
  · have hv1_eq0 : v1 = 0 := by
      by_contra hne; exact hx1 ((hZ1.2.2 x).mp hne)
    have hread10_0 : (Expr.read 10 (.reg r_x)).eval w s = some 0 := by
      rw [hread10, hv1_eq0]
    have hZ_len : x.1 < (s.arrs 12).length := by rw [hZ.1]; exact x.2
    let vz := (s.arrs 12)[x.1]'hZ_len
    have hvz_le : vz ≤ 1 := hZ.2.1 x
    have hvz_w : vz < 2 ^ w := by omega
    have hread12 : (Expr.read 12 (.reg r_x)).eval w s = some vz := by
      simp [Expr.eval, checkWord, hrx, hx_w, hZ_len, vz, hvz_w]
    by_cases hxZ : x ∈ Z
    · have hvz_ne0 : vz ≠ 0 := (hZ.2.2 x).mpr hxZ
      have hx_not_left : ¬ inLeftSide Z Z₁ items x := by
        rintro (h1 | ⟨h2, _⟩)
        · exact hx1 h1
        · exact h2 hxZ
      refine ⟨s, 2 + (2 + 1),
        .ite_false hread10_0 (.ite_true hread12 hvz_ne0 (.skip s)),
        by omega,
        ⟨by simp [hr14.1, hx_not_left], hr14.2⟩, rfl, fun _ _ => rfl⟩
    · have hvz_eq0 : vz = 0 := by
        by_contra hne; exact hxZ ((hZ.2.2 x).mp hne)
      have hread12_0 : (Expr.read 12 (.reg r_x)).eval w s = some 0 := by
        rw [hread12, hvz_eq0]
      rcases hvis with ⟨hvis_len, hvis_iff⟩
      have hxn_len : x.1 + n < (s.arrs 23).length := by rw [hvis_len]; exact hxn_lt
      let vvis := (s.arrs 23)[x.1 + n]'hxn_len
      have hvvis_props := hvis_iff (x.1 + n) hxn_lt
      have hvvis_le : vvis ≤ 1 := hvvis_props.2
      have hvvis_w : vvis < 2 ^ w := by omega
      have hread23 : (Expr.read 23 (.op .add (.reg r_x) (.reg 0))).eval w s = some vvis := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx, hr0, hx_w, hn_w, hxn_w,
          hxn_len, vvis, hvvis_w]
      by_cases hx_it : x.1 + n ∈ items
      · have hvvis_ne0 : vvis ≠ 0 := hvvis_props.1.mpr hx_it
        let s₁ := s.setReg 14 1
        have hex₁ : Exec w (.assign 14 (.const 1)) s s₁ 2 :=
          .assign (by simp [Expr.eval, checkWord, hw])
        have hx_left : inLeftSide Z Z₁ items x := Or.inr ⟨hxZ, hx_it⟩
        refine ⟨s₁, 2 + (2 + (4 + 2)),
          .ite_false hread10_0 (.ite_false hread12_0 (.ite_true hread23 hvvis_ne0 hex₁)),
          by omega,
          ⟨by simp [s₁, hx_left], by simp [s₁]⟩, rfl,
          fun r hr14' => by simp [s₁, hr14']⟩
      · have hvvis_eq0 : vvis = 0 := by
          by_contra hne; exact hx_it (hvvis_props.1.mp hne)
        have hread23_0 : (Expr.read 23 (.op .add (.reg r_x) (.reg 0))).eval w s = some 0 := by
          rw [hread23, hvvis_eq0]
        have hx_not_left : ¬ inLeftSide Z Z₁ items x := by
          rintro (h1 | ⟨_, h3⟩)
          · exact hx1 h1
          · exact hx_it h3
        refine ⟨s, 2 + (2 + (4 + 1)),
          .ite_false hread10_0 (.ite_false hread12_0 (.ite_false hread23_0 (.skip s))),
          by omega,
          ⟨by simp [hr14.1, hx_not_left], hr14.2⟩, rfl, fun _ _ => rfl⟩

/-- Reassign edge `r_11` (currently mapped to `v`) to `t = r_4` if either endpoint is in
`inLeftSide Z Z₁ items`, or to `t + 1 = r_4 + 1` otherwise. -/
def step5EdgeSplitCmd : Cmd :=
  .seq (.assign 12 (.read 2 (.reg 11)))
    (.seq (.assign 13 (.read 3 (.reg 11)))
      (.seq (.assign 14 (.const 0))
        (.seq (checkInLeftCmd 12)
          (.seq (checkInLeftCmd 13)
            (.ite (.reg 14)
              (.write 5 (.reg 11) (.reg 4))
              (.write 5 (.reg 11) (.op .add (.reg 4) (.const 1))))))))

/-- Loop body of `step5SplitProg`: if `a_tau[r_11] == r_7`, runs `step5EdgeSplitCmd`. -/
def step5LoopBody : Cmd :=
  .seq (.assign 15 (.read 5 (.reg 11)))
    (.ite (.op .eq (.reg 15) (.reg 7))
      step5EdgeSplitCmd
      .skip)

theorem step5LoopBody_exec {w n t : ℕ}
    (edges : List (Fin n × Fin n)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z Z₁ : Finset (Fin n)) (items : List ℕ)
    (k : ℕ) (hk : k < edges.length)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w) (hm2_w : edges.length < 2 ^ w) (ht1_w : t + 1 < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (htau : IsTauArr (step5FTauUpTo edges f_tau v Z Z₁ items k) 5 s)
    (hZ1 : IsBitSet Z₁ 10 s)
    (hZ : IsBitSet Z 12 s)
    (hvis : IsResVisArr n 23 items s)
    (hr0 : s.regs 0 = n)
    (hr4 : s.regs 4 = t)
    (hr7 : s.regs 7 = v.1)
    (hr11 : s.regs 11 = k) :
    ∃ s' t_body,
      Exec w step5LoopBody s s' t_body ∧
      t_body ≤ 41 ∧
      IsTauArr (step5FTauUpTo edges f_tau v Z Z₁ items (k + 1)) 5 s' ∧
      (∀ a : Arr, a ≠ 5 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have ht_w : t < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  let jk : Fin edges.length := ⟨k, hk⟩
  rcases htau with ⟨htau_len, htau_all⟩
  have htau_k : (s.arrs 5)[k]'(by rw [htau_len]; exact hk) = (f_tau jk).1 := by
    have := htau_all jk
    simpa [step5FTauUpTo, jk] using this
  let wk := f_tau jk
  have hwk_w : wk.1 < 2 ^ w := by have := wk.2; omega
  let s₁ := s.setReg 15 wk.1
  have hex_rd5 : Exec w (.assign 15 (.read 5 (.reg 11))) s s₁ 3 :=
    .assign (by
      simp [Expr.eval, checkWord, hr11, hk_w,
        show k < (s.arrs 5).length by rw [htau_len]; exact hk, htau_k, wk, hwk_w])
  by_cases hwk_eq : wk = v
  · have hwk_val : wk.1 = v.1 := congrArg Fin.val hwk_eq
    have hcond15 : (Expr.op .eq (.reg 15) (.reg 7)).eval w s₁ = some 1 := by
      simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr7, hwk_val, hv_w, hw]
    rcases hend with ⟨hlen2, hlen3, hall23⟩
    let u := (edges[k]).1
    let y := (edges[k]).2
    have hu_w : u.1 < 2 ^ w := by have := u.2; omega
    have hy_w : y.1 < 2 ^ w := by have := y.2; omega
    have hk_len2 : k < (s.arrs 2).length := by rw [hlen2]; exact hk
    have hval2 : (s.arrs 2)[k]'hk_len2 = u.1 := (hall23 jk).1
    let s₂ := s₁.setReg 12 u.1
    have hex₂ : Exec w (.assign 12 (.read 2 (.reg 11))) s₁ s₂ 3 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hr11, hk_w, hk_len2, hval2, hu_w])
    have hk_len3 : k < (s.arrs 3).length := by rw [hlen3]; exact hk
    have hval3 : (s.arrs 3)[k]'hk_len3 = y.1 := (hall23 jk).2
    let s₃ := s₂.setReg 13 y.1
    have hex₃ : Exec w (.assign 13 (.read 3 (.reg 11))) s₂ s₃ 3 :=
      .assign (by simp [s₂, s₁, Expr.eval, checkWord, hr11, hk_w, hk_len3, hval3, hy_w])
    let s₄ := s₃.setReg 14 0
    have hex₄ : Exec w (.assign 14 (.const 0)) s₃ s₄ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    rcases checkInLeftCmd_exec Z Z₁ items 12 u False hw h2n_w (s := s₄)
        (hZ1.of_arr_eq rfl) (hZ.of_arr_eq rfl) (hvis.of_arr_eq rfl)
        (by simp [s₄, s₃, s₂, s₁, hr0])
        (by simp [s₄, s₃, s₂, u])
        ⟨by simp [s₄], by simp [s₄]⟩ with
      ⟨s₅, t₅, hex₅, ht₅, h14_5, harr₅, hreg₅⟩
    rcases checkInLeftCmd_exec Z Z₁ items 13 y (False ∨ inLeftSide Z Z₁ items u)
        hw h2n_w (s := s₅)
        (hZ1.of_arr_eq (by rw [harr₅]; rfl))
        (hZ.of_arr_eq (by rw [harr₅]; rfl))
        (hvis.of_arr_eq (by rw [harr₅]; rfl))
        (by rw [hreg₅ 0 (by decide)]; simp [s₄, s₃, s₂, s₁, hr0])
        (by rw [hreg₅ 13 (by decide)]; simp [s₄, s₃, y])
        h14_5 with
      ⟨s₆, t₆, hex₆, ht₆, h14_6, harr₆, hreg₆⟩
    have harr_s₆ : s₆.arrs = s.arrs := by rw [harr₆, harr₅]; rfl
    have hr11_6 : s₆.regs 11 = k := by
      rw [hreg₆ 11 (by decide), hreg₅ 11 (by decide)]; simp [s₄, s₃, s₂, s₁, hr11]
    have hr4_6 : s₆.regs 4 = t := by
      rw [hreg₆ 4 (by decide), hreg₅ 4 (by decide)]; simp [s₄, s₃, s₂, s₁, hr4]
    by_cases hleft : inLeftSide Z Z₁ items u ∨ inLeftSide Z Z₁ items y
    · have hr14_ne0 : s₆.regs 14 ≠ 0 := h14_6.1.mpr (by simpa using hleft)
      have hr14_w : s₆.regs 14 < 2 ^ w := by have := h14_6.2; omega
      have hcond14 : (Expr.reg 14).eval w s₆ = some (s₆.regs 14) := by
        simp [Expr.eval, checkWord, hr14_w]
      let s₇ := s₆.writeArr 5 k t
      have hex_wr : Exec w (.write 5 (.reg 11) (.reg 4)) s₆ s₇ 3 :=
        .write (by simp [Expr.eval, checkWord, hr11_6, hk_w])
          (by simp [Expr.eval, checkWord, hr4_6, ht_w])
          (by rw [harr_s₆, htau_len]; exact hk)
      have htau₇ : IsTauArr (step5FTauUpTo edges f_tau v Z Z₁ items (k + 1)) 5 s₇ := by
        have h5_eq : s₇.arrs 5 = (s.arrs 5).set k t := by simp [s₇, harr_s₆]
        refine ⟨by simp [h5_eq, htau_len], fun j => ?_⟩
        simp only [h5_eq, step5FTauUpTo]
        by_cases hjk : j.1 = k
        · have hj_eq : j = jk := Fin.ext hjk
          subst hj_eq
          have hfk : f_tau jk = v := hwk_eq
          have hleft' : inLeftSide Z Z₁ items (edges[jk.1]).1 ∨
              inLeftSide Z Z₁ items (edges[jk.1]).2 := hleft
          simp [jk, step5FTau, hfk, hleft']
        · rw [List.getElem_set_ne (Ne.symm hjk)]
          have hprev := htau_all j
          simp only [step5FTauUpTo] at hprev
          by_cases hj_lt : j.1 < k
          · have hj_lt1 : j.1 < k + 1 := by omega
            simpa [hj_lt, hj_lt1] using hprev
          · have hj_nlt1 : ¬ j.1 < k + 1 := by omega
            simpa [hj_lt, hj_nlt1] using hprev
      refine ⟨s₇, 3 + (3 + (3 + (3 + (2 + (t₅ + (t₆ + (1 + 3))))))),
        .seq hex_rd5 (.ite_true hcond15 (by omega)
          (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
            (.ite_true hcond14 hr14_ne0 hex_wr))))))),
        by omega, htau₇,
        fun a ha5 => by simp [s₇, ha5, harr_s₆],
        fun r hr12 hr13 hr14 hr15 => by
          simp [s₇, hreg₆ r hr14, hreg₅ r hr14, s₄, s₃, s₂, s₁, hr14, hr13, hr12, hr15]⟩
    · have hr14_eq0 : s₆.regs 14 = 0 := by
        by_contra hne
        have := h14_6.1.mp hne
        simp [hleft] at this
      have hcond14 : (Expr.reg 14).eval w s₆ = some 0 := by
        simp [Expr.eval, checkWord, hr14_eq0, h0_w]
      let s₇ := s₆.writeArr 5 k (t + 1)
      have hex_wr : Exec w (.write 5 (.reg 11) (.op .add (.reg 4) (.const 1))) s₆ s₇ 5 :=
        .write (by simp [Expr.eval, checkWord, hr11_6, hk_w])
          (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_6, ht_w, hw, ht1_w])
          (by rw [harr_s₆, htau_len]; exact hk)
      have htau₇ : IsTauArr (step5FTauUpTo edges f_tau v Z Z₁ items (k + 1)) 5 s₇ := by
        have h5_eq : s₇.arrs 5 = (s.arrs 5).set k (t + 1) := by simp [s₇, harr_s₆]
        refine ⟨by simp [h5_eq, htau_len], fun j => ?_⟩
        simp only [h5_eq, step5FTauUpTo]
        by_cases hjk : j.1 = k
        · have hj_eq : j = jk := Fin.ext hjk
          subst hj_eq
          have hfk : f_tau jk = v := hwk_eq
          have hleft' : ¬ (inLeftSide Z Z₁ items (edges[jk.1]).1 ∨
              inLeftSide Z Z₁ items (edges[jk.1]).2) := hleft
          simp [jk, step5FTau, hfk, hleft']
        · rw [List.getElem_set_ne (Ne.symm hjk)]
          have hprev := htau_all j
          simp only [step5FTauUpTo] at hprev
          by_cases hj_lt : j.1 < k
          · have hj_lt1 : j.1 < k + 1 := by omega
            simpa [hj_lt, hj_lt1] using hprev
          · have hj_nlt1 : ¬ j.1 < k + 1 := by omega
            simpa [hj_lt, hj_nlt1] using hprev
      refine ⟨s₇, 3 + (3 + (3 + (3 + (2 + (t₅ + (t₆ + (1 + 5))))))),
        .seq hex_rd5 (.ite_true hcond15 (by omega)
          (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
            (.ite_false hcond14 hex_wr))))))),
        by omega, htau₇,
        fun a ha5 => by simp [s₇, ha5, harr_s₆],
        fun r hr12 hr13 hr14 hr15 => by
          simp [s₇, hreg₆ r hr14, hreg₅ r hr14, s₄, s₃, s₂, s₁, hr14, hr13, hr12, hr15]⟩
  · have hwk_ne_val : wk.1 ≠ v.1 := fun h => hwk_eq (Fin.ext h)
    have hcond15 : (Expr.op .eq (.reg 15) (.reg 7)).eval w s₁ = some 0 := by
      simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr7, hwk_ne_val, hwk_w, hv_w, h0_w]
    have htau₁ : IsTauArr (step5FTauUpTo edges f_tau v Z Z₁ items (k + 1)) 5 s₁ := by
      refine ⟨by simp [s₁, htau_len], fun j => ?_⟩
      have hprev := htau_all j
      simp only [s₁, State.setReg_arrs, step5FTauUpTo] at hprev ⊢
      by_cases hjk : j.1 = k
      · have hj_eq : j = jk := Fin.ext hjk
        subst hj_eq
        have hfk : f_tau jk ≠ v := hwk_eq
        simpa [jk, step5FTau, hfk] using hprev
      · by_cases hj_lt : j.1 < k
        · have hj_lt1 : j.1 < k + 1 := by omega
          simpa [hj_lt, hj_lt1] using hprev
        · have hj_nlt1 : ¬ j.1 < k + 1 := by omega
          simpa [hj_lt, hj_nlt1] using hprev
    refine ⟨s₁, 3 + (3 + 1),
      .seq hex_rd5 (.ite_false hcond15 (.skip s₁)),
      by omega, htau₁,
      fun _ _ => rfl,
      fun r _ _ _ hr15 => by simp [s₁, hr15]⟩

theorem step5Loop_exec {w n t : ℕ}
    (edges : List (Fin n × Fin n)) (f_tau : Fin edges.length → Fin t)
    (v : Fin t) (Z Z₁ : Finset (Fin n)) (items : List ℕ)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w) (hm2_w : edges.length < 2 ^ w) (ht1_w : t + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = edges.length)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (htau : IsTauArr (step5FTauUpTo edges f_tau v Z Z₁ items k) 5 s)
    (hZ1 : IsBitSet Z₁ 10 s)
    (hZ : IsBitSet Z 12 s)
    (hvis : IsResVisArr n 23 items s)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = edges.length)
    (hr4 : s.regs 4 = t)
    (hr7 : s.regs 7 = v.1)
    (hr11 : s.regs 11 = k) :
    ∃ s' t_loop,
      Exec w (forUp 11 (.reg 2) step5LoopBody) s s' t_loop ∧
      t_loop ≤ 3 + 48 * rem ∧
      IsTauArr (step5FTau edges f_tau v Z Z₁ items) 5 s' ∧
      (∀ a : Arr, a ≠ 5 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = edges.length := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hm2_w, h0_w]
    have htau_eq : step5FTauUpTo edges f_tau v Z Z₁ items edges.length =
        step5FTau edges f_tau v Z Z₁ items := by
      ext j; simp [step5FTauUpTo]
    rw [htau_eq] at htau
    exact ⟨s, 3, .while_false hcond, by omega, htau,
      fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < edges.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 11) (.reg 2)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr2, hk_w, hm2_w, hk_lt, hw]
    rcases step5LoopBody_exec edges f_tau v Z Z₁ items k hk_lt
        hw h2n_w hm2_w ht1_w hend htau hZ1 hZ hvis hr0 hr4 hr7 hr11 with
      ⟨s₁, t₁, hex₁, ht₁, htau₁, harr₁, hreg₁⟩
    have hr11_1 : s₁.regs 11 = k := by
      rw [hreg₁ 11 (by decide) (by decide) (by decide) (by decide), hr11]
    let s₂ := s₁.setReg 11 (k + 1)
    have hex_inc : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11_1, hk_w, hw, hk1_w])
    rcases ih (k + 1) (by omega) (s := s₂)
        (hend.of_arrs_eq (harr₁ 2 (by decide)) (harr₁ 3 (by decide)))
        (htau₁.of_arr_eq rfl)
        (hZ1.of_arr_eq (harr₁ 10 (by decide)))
        (hZ.of_arr_eq (harr₁ 12 (by decide)))
        (hvis.of_arr_eq (harr₁ 23 (by decide)))
        (by simp [s₂, hreg₁ 0 (by decide) (by decide) (by decide) (by decide), hr0])
        (by simp [s₂, hreg₁ 2 (by decide) (by decide) (by decide) (by decide), hr2])
        (by simp [s₂, hreg₁ 4 (by decide) (by decide) (by decide) (by decide), hr4])
        (by simp [s₂, hreg₁ 7 (by decide) (by decide) (by decide) (by decide), hr7])
        (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, htau₃, harr₃, hreg₃⟩
    refine ⟨s₃, 3 + (t₁ + 4) + t₃,
      .while_true hcond (by omega) (.seq hex₁ hex_inc) hex₃,
      by omega, htau₃,
      fun a ha5 => by rw [harr₃ a ha5]; exact harr₁ a ha5,
      fun r hr11' hr12 hr13 hr14 hr15 => by
        rw [hreg₃ r hr11' hr12 hr13 hr14 hr15]
        simp [s₂, hr11', hreg₁ r hr12 hr13 hr14 hr15]⟩

/-- Step (5) leaf-splitting program: updates `a_tau = 5`, splits `v = r_7` in `a_parent = 6`, and
sets `r_10 := 1` (`found_flag := 1`). -/
def step5SplitProg : Cmd :=
  .seq (.assign 11 (.const 0))
    (.seq (forUp 11 (.reg 2) step5LoopBody)
      (.seq splitParentCmd
        (.assign 10 (.const 1))))

theorem step5SplitProg_exec {w n t ω : ℕ} (hω : 1 ≤ ω) (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (p : ℕ → ℕ) (v : Fin t) (hv_leaf : v ∈ treeLeaves (parentTree t p))
    (Z₁ Z₂ Z₃ : Finset (Fin n))
    (hpart : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
      (parentTree t p) (tauOfArr edges t ht_pos f_tau))
    (hZ_part : IsValidZPartition ω
      (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
      Z₁ Z₂ Z₃)
    (hno_edge : ∀ z₁ ∈ Z₁, ∀ z₂ ∈ Z₂,
      ¬ (leafGraph (graphOfAlive edges hedges.1 aliveSet)
          (tauOfArr edges t ht_pos f_tau) v).Adj z₁ z₂)
    {used pred succ : Fin n → ℕ} {items : List ℕ}
    (hsys : IsValidPathSystem
      (restrictGraph
        (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        (Finset.univ \ leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
          (tauOfArr edges t ht_pos f_tau) v))
      (extNeighbors
        (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v) Z₁)
      (extNeighbors
        (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v) Z₂)
      used pred succ)
    (hcard_lt : (pathStarts used pred).card < ω - Z₃.card + 1)
    (hclosed : IsResPopClosed
      (restrictGraph
        (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        (Finset.univ \ leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
          (tauOfArr edges t ht_pos f_tau) v))
      used pred succ items items.length)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable
        (ResidualAdj
          (restrictGraph
            (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
            (Finset.univ \ leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
              (tauOfArr edges t ht_pos f_tau) v))
          used pred succ)
        {z | ∃ a ∈ extNeighbors
          (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
          (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v) Z₁,
          z = inNode a} z)
    (hinit : ∀ a ∈ extNeighbors
      (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
      (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v) Z₁,
      a.1 ∈ items)
    (hnoB : ∀ b ∈ extNeighbors
      (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
      (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v) Z₂,
      b.1 + n ∉ items)
    (ht_le : t + 2 ≤ 2 * edges.length)
    (hw2 : 2 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (hm2_w : edges.length < 2 ^ w) (ht2_w : t + 2 < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (htau : IsTauArr f_tau 5 s)
    (hpar : IsParentArr edges.length t p 6 s)
    (hZ1 : IsBitSet Z₁ 10 s)
    (hZ : IsBitSet
      (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v) 12 s)
    (hvis : IsResVisArr n 23 items s)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = edges.length)
    (hr4 : s.regs 4 = t)
    (hr7 : s.regs 7 = v.1) :
    let Z := leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v
    let f_tau' := step5FTau edges f_tau v Z Z₁ items
    let p' := splitLeafParent p t v.1
    ∃ s' t_sp,
      Exec w step5SplitProg s s' t_sp ∧
      t_sp ≤ 48 * edges.length + 19 ∧
      IsTauArr f_tau' 5 s' ∧
      IsParentArr edges.length (t + 2) p' 6 s' ∧
      IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
        (parentTree (t + 2) p') (tauOfArr edges (t + 2) (by omega) f_tau') ∧
      s'.regs 4 = t + 2 ∧
      s'.regs 10 = 1 ∧
      (∀ a : Arr, a ≠ 5 → a ≠ 6 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 4 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
        s'.regs r = s.regs r) := by
  intro Z f_tau' p'
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have ht1_w : t + 1 < 2 ^ w := by omega
  let s₁ := s.setReg 11 0
  have hex₁ : Exec w (.assign 11 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have htau₀ : IsTauArr (step5FTauUpTo edges f_tau v Z Z₁ items 0) 5 s₁ := by
    rcases htau with ⟨hlen, hall⟩
    exact ⟨hlen, fun j => by simpa [s₁, step5FTauUpTo] using hall j⟩
  rcases step5Loop_exec edges f_tau v Z Z₁ items hw h2n_w hm2_w ht1_w
      edges.length 0 (by omega) (s := s₁)
      (hend.of_arrs_eq rfl rfl) htau₀
      (hZ1.of_arr_eq rfl) (hZ.of_arr_eq rfl) (hvis.of_arr_eq rfl)
      (by simp [s₁, hr0]) (by simp [s₁, hr2]) (by simp [s₁, hr4])
      (by simp [s₁, hr7]) (by simp [s₁]) with
    ⟨s₂, t₂, hex₂, ht₂, htau₂, harr₂, hreg₂⟩
  rcases splitParentCmd_exec p v ht_le hw2 ht2_w (s := s₂)
      (hpar.of_arr_eq (harr₂ 6 (by decide)))
      (by rw [hreg₂ 4 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s₁, hr4])
      (by rw [hreg₂ 7 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s₁, hr7]) with
    ⟨s₃, hex₃, hpar₃, hr4_3, harr₃, hreg₃⟩
  let s₄ := s₃.setReg 10 1
  have hex₄ : Exec w (.assign 10 (.const 1)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hpart' : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
      (parentTree (t + 2) p') (tauOfArr edges (t + 2) (by omega) f_tau') := by
    apply isPartialBranchDecomp_step5 hω ht_pos hpar.2.2.2 hpart hv_leaf hZ_part hno_edge
      hsys hcard_lt hclosed hreach hinit hnoB
    · intro e he hne_v
      rw [mem_edgeFinset_graphOfAlive_iff hedges] at he
      rcases he with ⟨k, _, rfl⟩
      rw [tauOfArr_symEdgeAt hedges] at hne_v
      rw [tauOfArr_symEdgeAt hedges, tauOfArr_symEdgeAt hedges]
      simp [f_tau', step5FTau, hne_v]
    · intro x y hadj hxy
      rcases hadj with ⟨⟨k, _, hmatch⟩, htau_xy⟩
      have hsym : s(x, y) = symEdgeAt edges k := by
        unfold symEdgeAt
        rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      rw [hsym, tauOfArr_symEdgeAt hedges] at htau_xy ⊢
      have hxy' : inLeftSide Z Z₁ items (edges[k.1]).1 ∨ inLeftSide Z Z₁ items (edges[k.1]).2 := by
        rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hxy
        · rw [h1, h2, or_comm]; exact hxy
      simp [f_tau', step5FTau, htau_xy, hxy']
    · intro x y hadj hxy
      rcases hadj with ⟨⟨k, _, hmatch⟩, htau_xy⟩
      have hsym : s(x, y) = symEdgeAt edges k := by
        unfold symEdgeAt
        rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      rw [hsym, tauOfArr_symEdgeAt hedges] at htau_xy ⊢
      have hxy' : ¬ (inLeftSide Z Z₁ items (edges[k.1]).1 ∨
          inLeftSide Z Z₁ items (edges[k.1]).2) := by
        rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hxy
        · rw [h1, h2, or_comm]; exact hxy
      simp [f_tau', step5FTau, htau_xy, hxy']
  refine ⟨s₄, 2 + (t₂ + (12 + 2)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega,
    htau₂.of_arr_eq (by simp [s₄, harr₃ 5 (by decide)]),
    hpar₃.of_arr_eq rfl,
    hpart',
    by simp [s₄, hr4_3],
    by simp [s₄],
    fun a ha5 ha6 => by simp [s₄, harr₃ a ha6, harr₂ a ha5, s₁],
    fun r hr4' hr10 hr11 hr12 hr13 hr14 hr15 => by
      simp [s₄, hr10, hreg₃ r hr4', hreg₂ r hr11 hr12 hr13 hr14 hr15, s₁, hr11]⟩

theorem initPathSystemRegProg_writtenRegs_ge :
    ∀ r ∈ (initPathSystemRegProg 20 30).writtenRegs, 30 ≤ r := by
  decide

theorem mengerLoopRegProg_writtenRegs_ge :
    ∀ r ∈ (mengerLoopRegProg 15 16 17 18 19 20 30).writtenRegs, 30 ≤ r := by
  decide

/-- Set up `ConstRegs n k_goal 30` (`r_42 := r_0`, `r_43 := 2 * r_0`, `r_44 := k_goal`),
initialize `r_45 := 0` (`round := 0`) and `r_46 := 1` (`ok := 1`), run `initPathSystemRegProg 20 30`
and `mengerLoopRegProg 15 16 17 18 19 20 30`, and if `r_46 == 0` execute `step5SplitProg`. -/
def runMengerForTemplateProg (k_goal : ℕ) : Cmd :=
  .seq (.assign 42 (.reg 0))
    (.seq (.assign 43 (.op .mul (.const 2) (.reg 0)))
      (.seq (.assign 44 (.const k_goal))
        (.seq (.assign 45 (.const 0))
          (.seq (.assign 46 (.const 1))
            (.seq (initPathSystemRegProg 20 30)
              (.seq (mengerLoopRegProg 15 16 17 18 19 20 30)
                (.ite (.reg 46)
                  .skip
                  step5SplitProg)))))))

/-- For a single valid template `l : List (Fin 3)`, if `r_10 == 0` (`found_flag == 0`), builds
`Z₁, Z₂` via `buildZ12Prog l`, builds `N₁, N₂` and `bad_edge` (`r_18`) via `buildExtNeighborsProg`,
and if `r_18 == 0` runs `runMengerForTemplateProg (ω - countVal 2 l + 1)`. -/
def checkOneTemplateProg (ω : ℕ) (l : List (Fin 3)) : Cmd :=
  .ite (.reg 10)
    .skip
    (.seq (buildZ12Prog l)
      (.seq buildExtNeighborsProg
        (.ite (.reg 18)
          .skip
          (runMengerForTemplateProg (ω - countVal 2 l + 1)))))

theorem checkOneTemplateProg_exec {w n t ω : ℕ} (hω : 1 ≤ ω) (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (p : ℕ → ℕ) (v : Fin t) (hv_leaf : v ∈ treeLeaves (parentTree t p))
    (hpart : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
      (parentTree t p) (tauOfArr edges t ht_pos f_tau))
    (hZ_card : (leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
      (tauOfArr edges t ht_pos f_tau) v).card = 3 * ω)
    (l : List (Fin 3)) (hval : validTemplate ω l)
    (ht_le : t + 2 ≤ 2 * edges.length)
    (hw2 : 2 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (h2m2_w : 2 + 2 * edges.length < 2 ^ w) (ht2_w : t + 2 < 2 ^ w)
    (h3w_w : 3 * ω < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hpar : IsParentArr edges.length t p 6 s)
    (hZ : IsBitSet
      (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v) 12 s)
    (hZlist : IsZListArr
      (zListUpTo (leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
        (tauOfArr edges t ht_pos f_tau) v) n) 13 s)
    (hadj_sub : IsAdjList
      (restrictGraph
        (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        (Finset.univ \ leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
          (tauOfArr edges t ht_pos f_tau) v))
      15 16 17
      (edgeNeighbors (subEdgesUpTo edges aliveSet f_tau v
        (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        edges.length)) s)
    (hent_sub : (s.arrs 17).length =
      2 * (subEdgesUpTo edges aliveSet f_tau v
        (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        edges.length).length)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = edges.length)
    (hr4 : s.regs 4 = t)
    (hr7 : s.regs 7 = v.1)
    (hr10 : s.regs 10 = 0) :
    let G := graphOfAlive edges hedges.1 aliveSet
    let τ := tauOfArr edges t ht_pos f_tau
    let R := leafGraph G τ v
    let Z := leafCutVerts G τ v
    let L := zListUpTo Z n
    let Z₁ := partOfTemplate L l 0
    let Z₂ := partOfTemplate L l 1
    let Z₃ := partOfTemplate L l 2
    ∃ s' t_one,
      Exec w (checkOneTemplateProg ω l) s s' t_one ∧
      t_one ≤ (ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω ∧
      (∀ a : Arr, a < 10 → a ≠ 5 → a ≠ 6 → s'.arrs a = s.arrs a) ∧
      (∀ a : Arr, a = 12 ∨ a = 13 ∨ a = 15 ∨ a = 16 ∨ a = 17 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 10 → r ≠ 4 → s'.regs r = s.regs r) ∧
      ((s'.regs 10 = 1 ∧
        ∃ f_tau' : Fin edges.length → Fin (t + 2),
          IsTauArr f_tau' 5 s' ∧
          IsParentArr edges.length (t + 2) (splitLeafParent p t v.1) 6 s' ∧
          IsPartialBranchDecomp ω G
            (parentTree (t + 2) (splitLeafParent p t v.1))
            (tauOfArr edges (t + 2) (by omega) f_tau') ∧
          s'.regs 4 = t + 2) ∨
       (s'.regs 10 = 0 ∧
        s'.arrs 5 = s.arrs 5 ∧
        s'.arrs 6 = s.arrs 6 ∧
        s'.regs 4 = t ∧
        ((∃ z₁ ∈ Z₁, ∃ z₂ ∈ Z₂, R.Adj z₁ z₂) ∨
         (∃ P : Fin (ω - Z₃.card + 1) →
            ABWalk (restrictGraph R (Finset.univ \ Z))
              (extNeighbors R Z Z₁) (extNeighbors R Z Z₂),
            PairwiseVertexDisjoint P)))) := by
  intro G τ R Z L Z₁ Z₂ Z₃
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm2_w : edges.length < 2 ^ w := by omega
  have ht_w : t < 2 ^ w := by omega
  have hlL : l.length = L.length := by
    rw [hval.1, length_zListUpTo_self, hZ_card]
  have hl_w : l.length < 2 ^ w := by rw [hval.1]; exact h3w_w
  have hcond10 : (Expr.reg 10).eval w s = some 0 := by
    simp [Expr.eval, checkWord, hr10, h0_w]
  -- 1. buildZ12Prog l
  rcases buildZ12Prog_exec Z l hlL hw hn_w hl_w hZlist hr0 with
    ⟨s₁, t₁, hex₁, ht₁, hZ1_1, hZ2_1, harr₁, hreg₁⟩
  -- 2. buildExtNeighborsProg
  rcases buildExtNeighborsProg_exec ht_pos hedges aliveSet f_tau v Z Z₁ Z₂
      hw hn_w hm2_w ht_w (s := s₁)
      (hend.of_arrs_eq (harr₁ 2 (by decide) (by decide)) (harr₁ 3 (by decide) (by decide)))
      (hal.of_arr_eq (harr₁ 4 (by decide) (by decide)))
      (htau.of_arr_eq (harr₁ 5 (by decide) (by decide)))
      hZ1_1 hZ2_1
      (hZ.of_arr_eq (harr₁ 12 (by decide) (by decide)))
      (by rw [hreg₁ 0 (by decide), hr0])
      (by rw [hreg₁ 2 (by decide), hr2])
      (by rw [hreg₁ 7 (by decide), hr7]) with
    ⟨s₂, t₂, hex₂, ht₂, hN1_2, hN2_2, hbad₂, harr₂, hreg₂⟩
  have harr₂_keep : ∀ a : Arr, a ≠ 10 → a ≠ 11 → a ≠ 18 → a ≠ 19 → s₂.arrs a = s.arrs a := by
    intro a ha10 ha11 ha18 ha19
    rw [harr₂ a ha18 ha19, harr₁ a ha10 ha11]
  have hreg₂_keep : ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 18 →
      s₂.regs r = s.regs r := by
    intro r hr11 hr12 hr13 hr14 hr18
    rw [hreg₂ r hr11 hr12 hr13 hr18, hreg₁ r hr14]
  have harr₂_lt10 : ∀ a : Arr, a < 10 → s₂.arrs a = s.arrs a := by
    intro a ha10; dsimp [Arr] at ha10
    exact harr₂_keep a (by dsimp [Arr]; omega) (by dsimp [Arr]; omega)
      (by dsimp [Arr]; omega) (by dsimp [Arr]; omega)
  have hreg₂_lt10 : ∀ r : Reg, r < 10 → s₂.regs r = s.regs r := by
    intro r hr10'; dsimp [Reg] at hr10'
    exact hreg₂_keep r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
  by_cases hbad : s₂.regs 18 ≠ 0
  · -- Bad edge exists between Z₁ and Z₂ in R
    have hbad_edge : ∃ z₁ ∈ Z₁, ∃ z₂ ∈ Z₂, R.Adj z₁ z₂ := hbad₂.1.mp hbad
    have hr18_w : s₂.regs 18 < 2 ^ w := by have := hbad₂.2; omega
    have hcond18 : (Expr.reg 18).eval w s₂ = some (s₂.regs 18) := by
      simp [Expr.eval, checkWord, hr18_w]
    have htime : 1 + (t₁ + (t₂ + 2)) ≤
        (ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω := by
      have hl_eq : l.length = 3 * ω := hval.1
      have h1 : 350 * n + 170 * edges.length + 100 ≤
          (ω + 2) * (350 * n + 170 * edges.length + 100) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    refine ⟨s₂, 1 + (t₁ + (t₂ + 2)),
      .ite_false hcond10 (.seq hex₁ (.seq hex₂ (.ite_true hcond18 hbad (.skip s₂)))),
      htime,
      fun a ha10 _ _ => harr₂_lt10 a ha10,
      fun a ha => by rcases ha with rfl | rfl | rfl | rfl | rfl <;>
        exact harr₂_keep _ (by decide) (by decide) (by decide) (by decide),
      fun r hr10' _ => hreg₂_lt10 r hr10',
      Or.inr ⟨by rw [hreg₂_keep 10 (by decide) (by decide) (by decide) (by decide) (by decide), hr10],
        harr₂_keep 5 (by decide) (by decide) (by decide) (by decide),
        harr₂_keep 6 (by decide) (by decide) (by decide) (by decide),
        by rw [hreg₂_keep 4 (by decide) (by decide) (by decide) (by decide) (by decide), hr4],
        Or.inl hbad_edge⟩⟩
  · -- No bad edge between Z₁ and Z₂ in R: run Menger
    have hr18_eq0 : s₂.regs 18 = 0 := by omega
    have hno_edge : ∀ z₁ ∈ Z₁, ∀ z₂ ∈ Z₂, ¬ R.Adj z₁ z₂ := by
      intro z₁ hz₁ z₂ hz₂ hadj
      exact hbad (hbad₂.1.mpr ⟨z₁, hz₁, z₂, hz₂, hadj⟩)
    have hcond18 : (Expr.reg 18).eval w s₂ = some 0 := by
      simp [Expr.eval, checkWord, hr18_eq0, h0_w]
    let k_goal := ω - countVal 2 l + 1
    have hZ3_card : Z₃.card = countVal 2 l :=
      card_partOfTemplate_eq L l 2 hlL (nodup_zListUpTo Z n)
    have hk_eq : k_goal = ω - Z₃.card + 1 := by rw [hZ3_card]
    have hk_le : k_goal ≤ ω + 1 := by omega
    have hk_w : k_goal < 2 ^ w := by omega
    have hr0_2 : s₂.regs 0 = n := by
      rw [hreg₂_keep 0 (by decide) (by decide) (by decide) (by decide) (by decide), hr0]
    let s₃ := s₂.setReg 42 n
    have hex₃ : Exec w (.assign 42 (.reg 0)) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, hr0_2, hn_w])
    let s₄ := s₃.setReg 43 (2 * n)
    have hex₄ : Exec w (.assign 43 (.op .mul (.const 2) (.reg 0))) s₃ s₄ 4 :=
      .assign (by simp [s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0_2, hw2, hn_w, h2n_w])
    let s₅ := s₄.setReg 44 k_goal
    have hex₅ : Exec w (.assign 44 (.const k_goal)) s₄ s₅ 2 :=
      .assign (by simp [Expr.eval, checkWord, hk_w])
    let s₆ := s₅.setReg 45 0
    have hex₆ : Exec w (.assign 45 (.const 0)) s₅ s₆ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    let s₇ := s₆.setReg 46 1
    have hex₇ : Exec w (.assign 46 (.const 1)) s₆ s₇ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    have hconst₇ : ConstRegs n k_goal 30 s₇ :=
      ⟨by simp [s₇, s₆, s₅, s₄, s₃], by simp [s₇, s₆, s₅, s₄], by simp [s₇, s₆, s₅]⟩
    -- initPathSystemRegProg 20 30
    rcases initPathSystemRegProg_exec
        (restrictGraph R (Finset.univ \ Z)) (extNeighbors R Z Z₁) (extNeighbors R Z Z₂)
        20 30 hw hn_w hconst₇ with
      ⟨s₈, t₈, hex₈, ht₈, hconst₈, hsys₈, hcard₈, harr₈, hreg₈⟩
    have hreg₈_lt30 : ∀ r : Reg, r < 30 → s₈.regs r = s₂.regs r := by
      intro r hr30
      dsimp [Reg] at hr30
      rw [Exec.regs_eq_of_not_mem_writtenRegs hex₈
        (fun hmem => absurd (initPathSystemRegProg_writtenRegs_ge r hmem) (not_le_of_gt hr30))]
      simp [s₇, s₆, s₅, s₄, s₃,
        show (r : Reg) ≠ 46 by dsimp [Reg]; omega,
        show (r : Reg) ≠ 45 by dsimp [Reg]; omega,
        show (r : Reg) ≠ 44 by dsimp [Reg]; omega,
        show (r : Reg) ≠ 43 by dsimp [Reg]; omega,
        show (r : Reg) ≠ 42 by dsimp [Reg]; omega]
    have harr₈_lt20 : ∀ a < 20, s₈.arrs a = s₂.arrs a := harr₈
    have hadj₈ : IsAdjList (restrictGraph R (Finset.univ \ Z)) 15 16 17
        (edgeNeighbors (subEdgesUpTo edges aliveSet f_tau v Z edges.length)) s₈ :=
      hadj_sub.of_arrs_eq
        (by rw [harr₈_lt20 15 (by decide), harr₂_keep 15 (by decide) (by decide) (by decide) (by decide)])
        (by rw [harr₈_lt20 16 (by decide), harr₂_keep 16 (by decide) (by decide) (by decide) (by decide)])
        (by rw [harr₈_lt20 17 (by decide), harr₂_keep 17 (by decide) (by decide) (by decide) (by decide)])
    have hsub_len_le : (subEdgesUpTo edges aliveSet f_tau v Z edges.length).length ≤ edges.length :=
      length_subEdgesUpTo_le edges aliveSet f_tau v Z edges.length
    have hent₈_w : (s₈.arrs 17).length < 2 ^ w := by
      rw [harr₈_lt20 17 (by decide), harr₂_keep 17 (by decide) (by decide) (by decide) (by decide),
        hent_sub]
      dsimp only [Z, G, τ] at hsub_len_le
      omega
    have hN1_8 : IsBitSet (extNeighbors R Z Z₁) 18 s₈ :=
      hN1_2.of_arr_eq (harr₈_lt20 18 (by decide))
    have hN2_8 : IsBitSet (extNeighbors R Z Z₂) 19 s₈ :=
      hN2_2.of_arr_eq (harr₈_lt20 19 (by decide))
    have hr45_8 : s₈.regs 45 = 0 := by rw [hreg₈ 45 (by decide)]; simp [s₇, s₆]
    have hr46_8 : s₈.regs 46 = 1 := by rw [hreg₈ 46 (by decide)]; simp [s₇]
    -- mengerLoopRegProg 15 16 17 18 19 20 30
    rcases mengerLoopRegProg_exec
        (restrictGraph R (Finset.univ \ Z))
        (edgeNeighbors (subEdgesUpTo edges aliveSet f_tau v Z edges.length))
        (extNeighbors R Z Z₁) (extNeighbors R Z Z₂)
        15 16 17 18 19 20 30
        (by omega) (by omega) (by omega) (by omega) (by omega)
        hw h2n_w hk_w k_goal 0 (by omega)
        hconst₈ hadj₈ hent₈_w hN1_8 hN2_8 hsys₈ hcard₈ hr45_8 hr46_8 with
      ⟨s₉, t₉, hex₉, ht₉, _, harr₉, _, hres₉⟩
    have hreg₉_lt30 : ∀ r : Reg, r < 30 → s₉.regs r = s₂.regs r := by
      intro r hr30
      rw [Exec.regs_eq_of_not_mem_writtenRegs hex₉
        (fun hmem => absurd (mengerLoopRegProg_writtenRegs_ge r hmem) (not_le_of_gt hr30))]
      exact hreg₈_lt30 r hr30
    have harr₉_lt20 : ∀ a < 20, s₉.arrs a = s₂.arrs a := by
      intro a ha20; rw [harr₉ a ha20, harr₈_lt20 a ha20]
    have htot_sub : totalAdjEntries
        (edgeNeighbors (subEdgesUpTo edges aliveSet f_tau v Z edges.length)) ≤ 2 * edges.length := by
      have hsub_simple := isSimpleEdgeList_subEdgesUpTo ht_pos hedges aliveSet f_tau v Z
      rw [totalAdjEntries_edgeNeighbors _ hsub_simple.1]
      omega
    have ht₉_bound : t₉ ≤ 3 + (ω + 1) * (264 * n + 62 * edges.length + 65) := by
      have h1 : 65 + 264 * n + 31 * totalAdjEntries
          (edgeNeighbors (subEdgesUpTo edges aliveSet f_tau v Z edges.length)) ≤
          264 * n + 62 * edges.length + 65 := by omega
      have h2 : k_goal * (65 + 264 * n + 31 * totalAdjEntries
          (edgeNeighbors (subEdgesUpTo edges aliveSet f_tau v Z edges.length))) ≤
          (ω + 1) * (264 * n + 62 * edges.length + 65) :=
        Nat.mul_le_mul hk_le h1
      omega
    rcases hres₉ with ⟨hok1, used', pred', succ', hsys₉, hcard₉⟩ |
        ⟨hok0, used', pred', succ', items, hsys₉, hcard_lt₉, hvis₉, hpar₉, hclosed₉, hinit₉, hnoB₉⟩
    · -- Menger found k_goal disjoint paths: r_46 = 1 -> .skip
      have hcond46 : (Expr.reg 46).eval w s₉ = some 1 := by
        simp [Expr.eval, checkWord, hok1, hw]
      have hex_menger : Exec w (runMengerForTemplateProg k_goal) s₂ s₉
          (2 + (4 + (2 + (2 + (2 + (t₈ + (t₉ + 2))))))) :=
        .seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
          (.seq hex₈ (.seq hex₉ (.ite_true hcond46 (by omega) (.skip s₉))))))))
      rw [hk_eq] at hcard₉
      have hpaths : ∃ P : Fin (ω - Z₃.card + 1) →
          ABWalk (restrictGraph R (Finset.univ \ Z))
            (extNeighbors R Z Z₁) (extNeighbors R Z Z₂),
          PairwiseVertexDisjoint P :=
        ⟨extractDisjointPaths hsys₉.1 hcard₉, (extractDisjointPaths_sound hsys₉.1 hcard₉).1⟩
      have htime : 1 + (t₁ + (t₂ + (1 + (2 + (4 + (2 + (2 + (2 + (t₈ + (t₉ + 2)))))))))) ≤
          (ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω := by
        have hl_eq : l.length = 3 * ω := hval.1
        have hmul : (ω + 2) * (350 * n + 170 * edges.length + 100) =
            (ω + 1) * (350 * n + 170 * edges.length + 100) +
              (350 * n + 170 * edges.length + 100) := by
          rw [show ω + 2 = (ω + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
        have hle_mul : (ω + 1) * (264 * n + 62 * edges.length + 65) ≤
            (ω + 1) * (350 * n + 170 * edges.length + 100) := by
          apply Nat.mul_le_mul_left; omega
        omega
      refine ⟨s₉, 1 + (t₁ + (t₂ + (1 + (2 + (4 + (2 + (2 + (2 + (t₈ + (t₉ + 2)))))))))),
        .ite_false hcond10 (.seq hex₁ (.seq hex₂ (.ite_false hcond18 hex_menger))),
        htime,
        fun a ha10 _ _ => by
          dsimp [Arr] at ha10
          rw [harr₉_lt20 a (by dsimp [Arr]; omega)]
          exact harr₂_lt10 a ha10,
        fun a ha => by
          rcases ha with rfl | rfl | rfl | rfl | rfl <;>
          · rw [harr₉_lt20 _ (by decide)]
            exact harr₂_keep _ (by decide) (by decide) (by decide) (by decide),
        fun r hr10' _ => by
          dsimp [Reg] at hr10'
          rw [hreg₉_lt30 r (by dsimp [Reg]; omega)]
          exact hreg₂_lt10 r hr10',
        Or.inr ⟨by
            rw [hreg₉_lt30 10 (by decide),
              hreg₂_keep 10 (by decide) (by decide) (by decide) (by decide) (by decide), hr10],
          by rw [harr₉_lt20 5 (by decide), harr₂_keep 5 (by decide) (by decide) (by decide) (by decide)],
          by rw [harr₉_lt20 6 (by decide), harr₂_keep 6 (by decide) (by decide) (by decide) (by decide)],
          by rw [hreg₉_lt30 4 (by decide),
              hreg₂_keep 4 (by decide) (by decide) (by decide) (by decide) (by decide), hr4],
          Or.inr hpaths⟩⟩
    · -- Menger stopped with cut: r_46 = 0 -> step5SplitProg
      have hcond46 : (Expr.reg 46).eval w s₉ = some 0 := by
        simp [Expr.eval, checkWord, hok0, h0_w]
      rw [hk_eq] at hcard_lt₉
      have hZ_part : IsValidZPartition ω Z Z₁ Z₂ Z₃ :=
        isValidZPartition_partOfTemplate Z hZ_card hval
      rcases step5SplitProg_exec hω ht_pos hedges aliveSet f_tau p v hv_leaf Z₁ Z₂ Z₃
          hpart hZ_part hno_edge hsys₉.1 hcard_lt₉ hclosed₉ hpar₉.2.1 hinit₉ hnoB₉
          ht_le hw2 h2n_w hm2_w ht2_w (s := s₉)
          (hend.of_arrs_eq
            (by rw [harr₉_lt20 2 (by decide), harr₂_keep 2 (by decide) (by decide) (by decide) (by decide)])
            (by rw [harr₉_lt20 3 (by decide), harr₂_keep 3 (by decide) (by decide) (by decide) (by decide)]))
          (htau.of_arr_eq
            (by rw [harr₉_lt20 5 (by decide), harr₂_keep 5 (by decide) (by decide) (by decide) (by decide)]))
          (hpar.of_arr_eq
            (by rw [harr₉_lt20 6 (by decide), harr₂_keep 6 (by decide) (by decide) (by decide) (by decide)]))
          (hZ1_1.of_arr_eq (by rw [harr₉_lt20 10 (by decide), harr₂ 10 (by decide) (by decide)]))
          (hZ.of_arr_eq
            (by rw [harr₉_lt20 12 (by decide), harr₂_keep 12 (by decide) (by decide) (by decide) (by decide)]))
          hvis₉
          (by rw [hreg₉_lt30 0 (by decide), hr0_2])
          (by rw [hreg₉_lt30 2 (by decide),
              hreg₂_keep 2 (by decide) (by decide) (by decide) (by decide) (by decide), hr2])
          (by rw [hreg₉_lt30 4 (by decide),
              hreg₂_keep 4 (by decide) (by decide) (by decide) (by decide) (by decide), hr4])
          (by rw [hreg₉_lt30 7 (by decide),
              hreg₂_keep 7 (by decide) (by decide) (by decide) (by decide) (by decide), hr7]) with
        ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, htau₁₀, hpar₁₀, hpart₁₀, hr4_10, hr10_10, harr₁₀, hreg₁₀⟩
      have hex_menger : Exec w (runMengerForTemplateProg k_goal) s₂ s₁₀
          (2 + (4 + (2 + (2 + (2 + (t₈ + (t₉ + (1 + t₁₀)))))))) :=
        .seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
          (.seq hex₈ (.seq hex₉ (.ite_false hcond46 hex₁₀)))))))
      have htime : 1 + (t₁ + (t₂ + (1 + (2 + (4 + (2 + (2 + (2 + (t₈ + (t₉ + (1 + t₁₀))))))))))) ≤
          (ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω := by
        have hl_eq : l.length = 3 * ω := hval.1
        have hmul : (ω + 2) * (350 * n + 170 * edges.length + 100) =
            (ω + 1) * (350 * n + 170 * edges.length + 100) +
              (350 * n + 170 * edges.length + 100) := by
          rw [show ω + 2 = (ω + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
        have hle_mul : (ω + 1) * (264 * n + 62 * edges.length + 65) ≤
            (ω + 1) * (350 * n + 170 * edges.length + 100) := by
          apply Nat.mul_le_mul_left; omega
        omega
      refine ⟨s₁₀, 1 + (t₁ + (t₂ + (1 + (2 + (4 + (2 + (2 + (2 + (t₈ + (t₉ + (1 + t₁₀))))))))))),
        .ite_false hcond10 (.seq hex₁ (.seq hex₂ (.ite_false hcond18 hex_menger))),
        htime,
        fun a ha10 ha5 ha6 => by
          dsimp [Arr] at ha10
          rw [harr₁₀ a ha5 ha6, harr₉_lt20 a (by dsimp [Arr]; omega)]
          exact harr₂_lt10 a ha10,
        fun a ha => by
          rcases ha with rfl | rfl | rfl | rfl | rfl <;>
          · rw [harr₁₀ _ (by decide) (by decide), harr₉_lt20 _ (by decide)]
            exact harr₂_keep _ (by decide) (by decide) (by decide) (by decide),
        fun r hr10' hr4' => by
          dsimp [Reg] at hr10'
          rw [hreg₁₀ r hr4' (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
              (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
            hreg₉_lt30 r (by dsimp [Reg]; omega)]
          exact hreg₂_lt10 r hr10',
        Or.inl ⟨hr10_10, _, htau₁₀, hpar₁₀, hpart₁₀, hr4_10⟩⟩

/-! #### Subpart 5.5: Template-List Search, Step (6) Deletion, and `step456Prog` -/

/-- Run `checkOneTemplateProg ω l` sequentially over a list of templates `ls`. -/
def checkTemplatesListProg (ω : ℕ) : List (List (Fin 3)) → Cmd
  | [] => .skip
  | l :: ls => .seq (checkOneTemplateProg ω l) (checkTemplatesListProg ω ls)

theorem checkTemplatesListProg_skip_of_found {w : ℕ} (ω : ℕ) (ls : List (List (Fin 3)))
    (hw : 1 < 2 ^ w) {s : State} (hr10 : s.regs 10 = 1) :
    ∃ t_skip,
      Exec w (checkTemplatesListProg ω ls) s s t_skip ∧
      t_skip ≤ 1 + 2 * ls.length := by
  induction ls with
  | nil => exact ⟨1, .skip s, by omega⟩
  | cons l ls ih =>
    have hcond10 : (Expr.reg 10).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hr10, hw]
    have hex_one : Exec w (checkOneTemplateProg ω l) s s 2 :=
      .ite_true hcond10 (by omega) (.skip s)
    rcases ih with ⟨t_rest, hex_rest, ht_rest⟩
    exact ⟨2 + t_rest, .seq hex_one hex_rest, by simp; omega⟩

theorem checkTemplatesListProg_exec {w n t ω : ℕ} (hω : 1 ≤ ω) (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (p : ℕ → ℕ) (v : Fin t) (hv_leaf : v ∈ treeLeaves (parentTree t p))
    (hpart : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
      (parentTree t p) (tauOfArr edges t ht_pos f_tau))
    (hZ_card : (leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
      (tauOfArr edges t ht_pos f_tau) v).card = 3 * ω)
    (ls : List (List (Fin 3))) (hls_val : ∀ l ∈ ls, validTemplate ω l)
    (ht_le : t + 2 ≤ 2 * edges.length)
    (hw2 : 2 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (h2m2_w : 2 + 2 * edges.length < 2 ^ w) (ht2_w : t + 2 < 2 ^ w)
    (h3w_w : 3 * ω < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hpar : IsParentArr edges.length t p 6 s)
    (hZ : IsBitSet
      (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v) 12 s)
    (hZlist : IsZListArr
      (zListUpTo (leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
        (tauOfArr edges t ht_pos f_tau) v) n) 13 s)
    (hadj_sub : IsAdjList
      (restrictGraph
        (leafGraph (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        (Finset.univ \ leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
          (tauOfArr edges t ht_pos f_tau) v))
      15 16 17
      (edgeNeighbors (subEdgesUpTo edges aliveSet f_tau v
        (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        edges.length)) s)
    (hent_sub : (s.arrs 17).length =
      2 * (subEdgesUpTo edges aliveSet f_tau v
        (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v)
        edges.length).length)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = edges.length)
    (hr4 : s.regs 4 = t)
    (hr7 : s.regs 7 = v.1)
    (hr10 : s.regs 10 = 0) :
    let G := graphOfAlive edges hedges.1 aliveSet
    let τ := tauOfArr edges t ht_pos f_tau
    let R := leafGraph G τ v
    let Z := leafCutVerts G τ v
    let L := zListUpTo Z n
    ∃ s' t_ls,
      Exec w (checkTemplatesListProg ω ls) s s' t_ls ∧
      t_ls ≤ 1 + ls.length * ((ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω + 2) ∧
      (∀ a : Arr, a < 10 → a ≠ 5 → a ≠ 6 → s'.arrs a = s.arrs a) ∧
      (∀ a : Arr, a = 12 ∨ a = 13 ∨ a = 15 ∨ a = 16 ∨ a = 17 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 10 → r ≠ 4 → s'.regs r = s.regs r) ∧
      ((s'.regs 10 = 1 ∧
        ∃ f_tau' : Fin edges.length → Fin (t + 2),
          IsTauArr f_tau' 5 s' ∧
          IsParentArr edges.length (t + 2) (splitLeafParent p t v.1) 6 s' ∧
          IsPartialBranchDecomp ω G
            (parentTree (t + 2) (splitLeafParent p t v.1))
            (tauOfArr edges (t + 2) (by omega) f_tau') ∧
          s'.regs 4 = t + 2) ∨
       (s'.regs 10 = 0 ∧
        s'.arrs 5 = s.arrs 5 ∧
        s'.arrs 6 = s.arrs 6 ∧
        s'.regs 4 = t ∧
        (∀ l ∈ ls,
          let Z₁ := partOfTemplate L l 0
          let Z₂ := partOfTemplate L l 1
          let Z₃ := partOfTemplate L l 2
          (∃ z₁ ∈ Z₁, ∃ z₂ ∈ Z₂, R.Adj z₁ z₂) ∨
          (∃ P : Fin (ω - Z₃.card + 1) →
             ABWalk (restrictGraph R (Finset.univ \ Z))
               (extNeighbors R Z Z₁) (extNeighbors R Z Z₂),
             PairwiseVertexDisjoint P)))) := by
  intro G τ R Z L
  have hw : 1 < 2 ^ w := by omega
  induction ls generalizing s with
  | nil =>
    refine ⟨s, 1, .skip s, by omega,
      fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
      Or.inr ⟨hr10, rfl, rfl, hr4, fun _ h => False.elim (List.not_mem_nil h)⟩⟩
  | cons l ls ih =>
    have hl_val : validTemplate ω l := hls_val l List.mem_cons_self
    have hls_val' : ∀ l' ∈ ls, validTemplate ω l' :=
      fun l' hl' => hls_val l' (List.mem_cons_of_mem l hl')
    rcases checkOneTemplateProg_exec hω ht_pos hedges aliveSet f_tau p v hv_leaf hpart hZ_card
        l hl_val ht_le hw2 h2n_w h2m2_w ht2_w h3w_w
        hend hal htau hpar hZ hZlist hadj_sub hent_sub hr0 hr2 hr4 hr7 hr10 with
      ⟨s₁, t₁, hex₁, ht₁, harr₁_lt10, harr₁_keep, hreg₁_lt10, hres₁⟩
    have hstep_bound : (ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω + 2 ≥ 2 := by omega
    have hcons_mul :
        (l :: ls).length * ((ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω + 2) =
        ls.length * ((ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω + 2) +
          ((ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω + 2) := by
      rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    rcases hres₁ with ⟨hr10_1, f_tau', htau₁, hpar₁, hpart₁, hr4_1⟩ |
        ⟨hr10_0, harr5_1, harr6_1, hr4_1, hobs_l⟩
    · rcases checkTemplatesListProg_skip_of_found ω ls hw hr10_1 with ⟨t₂, hex₂, ht₂⟩
      have hmul_ge : 2 * ls.length ≤
          ls.length * ((ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω + 2) := by
        rw [Nat.mul_comm 2]
        exact Nat.mul_le_mul_left ls.length hstep_bound
      have htime : t₁ + t₂ ≤
          1 + (l :: ls).length * ((ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω + 2) := by
        rw [hcons_mul]
        omega
      exact ⟨s₁, t₁ + t₂, .seq hex₁ hex₂, htime,
        harr₁_lt10, harr₁_keep, hreg₁_lt10,
        Or.inl ⟨hr10_1, f_tau', htau₁, hpar₁, hpart₁, hr4_1⟩⟩
    · rcases ih hls_val' (s := s₁)
          (hend.of_arrs_eq
            (harr₁_lt10 2 (by decide) (by decide) (by decide))
            (harr₁_lt10 3 (by decide) (by decide) (by decide)))
          (hal.of_arr_eq (harr₁_lt10 4 (by decide) (by decide) (by decide)))
          (htau.of_arr_eq harr5_1)
          (hpar.of_arr_eq harr6_1)
          (hZ.of_arr_eq (harr₁_keep 12 (Or.inl rfl)))
          (hZlist.of_arr_eq (harr₁_keep 13 (Or.inr (Or.inl rfl))))
          (hadj_sub.of_arrs_eq
            (harr₁_keep 15 (Or.inr (Or.inr (Or.inl rfl))))
            (harr₁_keep 16 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
            (harr₁_keep 17 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
          (by rw [harr₁_keep 17 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), hent_sub])
          (by rw [hreg₁_lt10 0 (by decide) (by decide), hr0])
          (by rw [hreg₁_lt10 2 (by decide) (by decide), hr2])
          hr4_1
          (by rw [hreg₁_lt10 7 (by decide) (by decide), hr7])
          hr10_0 with
        ⟨s₂, t₂, hex₂, ht₂, harr₂_lt10, harr₂_keep, hreg₂_lt10, hres₂⟩
      have htime : t₁ + t₂ ≤
          1 + (l :: ls).length * ((ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω + 2) := by
        rw [hcons_mul]
        omega
      refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, htime,
        fun a ha10 ha5 ha6 => by rw [harr₂_lt10 a ha10 ha5 ha6, harr₁_lt10 a ha10 ha5 ha6],
        fun a ha => by rw [harr₂_keep a ha, harr₁_keep a ha],
        fun r hr10' hr4' => by rw [hreg₂_lt10 r hr10' hr4', hreg₁_lt10 r hr10' hr4'],
        ?_⟩
      rcases hres₂ with ⟨hr10_2, f_tau', htau₂, hpar₂, hpart₂, hr4_2⟩ |
          ⟨hr10_2, harr5_2, harr6_2, hr4_2, hobs_ls⟩
      · exact Or.inl ⟨hr10_2, f_tau', htau₂, hpar₂, hpart₂, hr4_2⟩
      · refine Or.inr ⟨hr10_2, by rw [harr5_2, harr5_1], by rw [harr6_2, harr6_1], hr4_2, ?_⟩
        intro l' hl'
        rcases List.mem_cons.mp hl' with rfl | hl'_ls
        · exact hobs_l
        · exact hobs_ls l' hl'_ls

/-- Copy a bitset array `a_src` of length `N = r_n` into `a_dst` using `readSliceProg` with
scratch registers `20..22`. -/
theorem copyBitSet_exec {w N : ℕ} (X : Finset (Fin N)) (a_src a_dst : Arr) (r_n : Reg)
    (hne : a_src ≠ a_dst) (hr_n : r_n < 20)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w)
    {s : State}
    (hsrc : IsBitSet X a_src s)
    (hrn_val : s.regs r_n = N) :
    ∃ s' t,
      Exec w (readSliceProg a_src (.const 0) a_dst (.reg r_n) 20) s s' t ∧
      t ≤ 16 * N + 9 ∧
      IsBitSet X a_dst s' ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < 20, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hmid_w : ∀ v ∈ bitSetList X, v < 2 ^ w := by
    intro v hv
    rcases List.mem_iff_getElem.mp hv with ⟨i, hi, rfl⟩
    have := getElem_bitSetList_le_one X i hi
    omega
  rcases readSliceProg_exec (w := w) (off := 0) a_src a_dst (.const 0) r_n 20
      hne hr_n [] (bitSetList X) [] rfl (length_bitSetList X) hmid_w hw (by omega)
      (by simp [Expr.eval, checkWord, h0_w])
      (by simp [hsrc.arr_eq_bitSetList])
      hrn_val with
    ⟨s', t, hex, ht, hdst, harr, hreg⟩
  exact ⟨s', t, hex, by simpa [Expr.cost] using ht,
    IsBitSet.of_bitSetList X a_dst s' hdst, harr, hreg⟩

/-- Step (6) deletion program:
1. Copies `a_alive = 4` (length `m₂ = r_2`) into `a_last_alive = 7`.
2. Copies `a_Z_bit = 12` (length `n = r_0`) into `a_last_Z = 8`.
3. Deletes `g_cand = r_9` from `a_alive = 4` (`a_4[r_9] := 0`).
4. Records `r_5 := 1` (`step6_flag := 1`) and `r_6 := r_9` (`last_g := r_9`). -/
def step6DeleteProg : Cmd :=
  .seq (readSliceProg 4 (.const 0) 7 (.reg 2) 20)
    (.seq (readSliceProg 12 (.const 0) 8 (.reg 0) 20)
      (.seq (.write 4 (.reg 9) (.const 0))
        (.seq (.assign 5 (.const 1))
          (.assign 6 (.reg 9)))))

theorem step6DeleteProg_exec {w n t ω : ℕ} (ht_pos : 0 < t)
    {H₁ H₂ : SimpleGraph (Fin n)} [DecidableRel H₁.Adj]
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (p : ℕ → ℕ) (v : Fin t) (g_idx : Fin edges.length)
    (hG_le : graphOfAlive edges hedges.1 aliveSet ≤ H₁)
    (hg_al : g_idx ∈ aliveSet) (hg_v : f_tau g_idx = v)
    (hother : ∃ j ∈ aliveSet, f_tau j = v ∧ j ≠ g_idx)
    (hpart : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
      (parentTree t p) (tauOfArr edges t ht_pos f_tau))
    (hZ_card : (leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
      (tauOfArr edges t ht_pos f_tau) v).card = 3 * ω)
    (hno_sep : ∀ sep : GraphSeparation (graphOfAlive edges hedges.1 aliveSet),
      sep.order ≤ ω → ¬ sep.IsBalancedQ
        (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : edges.length < 2 ^ w)
    {s : State}
    (hal : IsBitSet aliveSet 4 s)
    (hZ : IsBitSet
      (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v) 12 s)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = edges.length)
    (hr9 : s.regs 9 = g_idx.1) :
    let Z := leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v
    ∃ s' t_del,
      Exec w step6DeleteProg s s' t_del ∧
      t_del ≤ 16 * edges.length + 16 * n + 25 ∧
      IsBitSet (aliveSet.erase g_idx) 4 s' ∧
      IsBitSet aliveSet 7 s' ∧
      IsBitSet Z 8 s' ∧
      IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 (aliveSet.erase g_idx))
        (parentTree t p) (tauOfArr edges t ht_pos f_tau) ∧
      Step6CertInv ω H₁ edges hedges.1 (aliveSet.erase g_idx) aliveSet Z 1 g_idx.1 ∧
      s'.regs 5 = 1 ∧
      s'.regs 6 = g_idx.1 ∧
      (∀ a : Arr, a ≠ 4 → a ≠ 7 → a ≠ 8 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 20 → r ≠ 5 → r ≠ 6 → s'.regs r = s.regs r) := by
  intro Z
  have h0_w : 0 < 2 ^ w := by omega
  have hg_w : g_idx.1 < 2 ^ w := by have := g_idx.2; omega
  -- 1. copy a_alive = 4 to a_last_alive = 7
  rcases copyBitSet_exec aliveSet 4 7 2 (by decide) (by decide) hw hm2_w hal hr2 with
    ⟨s₁, t₁, hex₁, ht₁, hlast_al₁, harr₁, hreg₁⟩
  -- 2. copy a_Z_bit = 12 to a_last_Z = 8
  rcases copyBitSet_exec Z 12 8 0 (by decide) (by decide) hw hn_w (s := s₁)
      (hZ.of_arr_eq (harr₁ 12 (by decide)))
      (by rw [hreg₁ 0 (by decide), hr0]) with
    ⟨s₂, t₂, hex₂, ht₂, hlast_Z₂, harr₂, hreg₂⟩
  have hal₂ : IsBitSet aliveSet 4 s₂ :=
    hal.of_arr_eq (by rw [harr₂ 4 (by decide), harr₁ 4 (by decide)])
  have hr9_2 : s₂.regs 9 = g_idx.1 := by
    rw [hreg₂ 9 (by decide), hreg₁ 9 (by decide), hr9]
  -- 3. write 4[r_9] := 0
  let s₃ := s₂.writeArr 4 g_idx.1 0
  have hex₃ : Exec w (.write 4 (.reg 9) (.const 0)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, hr9_2, hg_w])
      (by simp [Expr.eval, checkWord, h0_w])
      (by rw [hal₂.1]; exact g_idx.2)
  have hal₃ : IsBitSet (aliveSet.erase g_idx) 4 s₃ := hal₂.write_zero g_idx
  -- 4. r_5 := 1, r_6 := r_9
  let s₄ := s₃.setReg 5 1
  have hex₄ : Exec w (.assign 5 (.const 1)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₅ := s₄.setReg 6 g_idx.1
  have hex₅ : Exec w (.assign 6 (.reg 9)) s₄ s₅ 2 :=
    .assign (by simp [s₄, s₃, Expr.eval, checkWord, hr9_2, hg_w])
  have hpart' : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 (aliveSet.erase g_idx))
      (parentTree t p) (tauOfArr edges t ht_pos f_tau) := by
    simp only [graphOfAlive_erase_eq_deleteEdges hedges]
    apply isPartialBranchDecomp_step6 (v := v) hpart
    · rw [tauOfArr_symEdgeAt hedges]; exact hg_v
    · rcases hother with ⟨j, hj_al, hj_v, hj_ne⟩
      refine ⟨symEdgeAt edges j, ?_, ?_, ?_⟩
      · rw [mem_edgeFinset_graphOfAlive_iff hedges]; exact ⟨j, hj_al, rfl⟩
      · rw [tauOfArr_symEdgeAt hedges]; exact hj_v
      · intro heq; exact hj_ne (symEdgeAt_injective hedges heq)
  have hcert' : Step6CertInv ω H₁ edges hedges.1 (aliveSet.erase g_idx) aliveSet Z 1 g_idx.1 := by
    refine Or.inr ⟨rfl, g_idx.2, hG_le, ?_, hZ_card, rfl, hno_sep⟩
    rw [mem_edgeFinset_graphOfAlive_iff hedges]
    exact ⟨g_idx, hg_al, rfl⟩
  refine ⟨s₅, t₁ + (t₂ + (3 + (2 + 2))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega,
    hal₃.of_arr_eq rfl,
    hlast_al₁.of_arr_eq (by simp [s₅, s₄, s₃, harr₂ 7 (by decide)]),
    hlast_Z₂.of_arr_eq rfl,
    hpart', hcert',
    by simp [s₅, s₄],
    by simp [s₅],
    fun a ha4 ha7 ha8 => by
      simp [s₅, s₄, s₃, ha4, harr₂ a ha8, harr₁ a ha7],
    fun r hr20 hr5 hr6 => by
      simp [s₅, s₄, s₃, hr5, hr6, hreg₂ r hr20, hreg₁ r hr20]⟩

/-- Combined Steps (4), (5), and (6) when `|Z| = 3ω`:
1. Builds the CSR representation of `R \ Z` (`buildSubgraphCsrProg`).
2. Initializes `r_10 := 0` (`found_flag := 0`) and searches all valid partitions
   `validTernaryLists ω` via `checkTemplatesListProg`.
3. If `r_10 == 0` (no template split `v` in Step (5)), deletes `g_cand = r_9` in Step (6)
   (`step6DeleteProg`). -/
def step456Prog (ω : ℕ) : Cmd :=
  .seq buildSubgraphCsrProg
    (.seq (.assign 10 (.const 0))
      (.seq (checkTemplatesListProg ω (validTernaryLists ω))
        (.ite (.reg 10)
          .skip
          step6DeleteProg)))

theorem length_validTernaryLists_le (ω : ℕ) :
    (validTernaryLists ω).length ≤ 3 ^ (3 * ω) := by
  have hsub : (validTernaryLists ω).length ≤ (ternaryLists (3 * ω)).length :=
    List.length_filter_le _ _
  have hlen : ∀ k, (ternaryLists k).length = 3 ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [ternaryLists, List.length_append, List.length_map, ih, Nat.pow_succ]
      omega
  rw [hlen] at hsub
  exact hsub

theorem step456Prog_exec {w n t ω : ℕ} (hω : 1 ≤ ω) (ht_pos : 0 < t)
    {H₁ H₂ : SimpleGraph (Fin n)} [DecidableRel H₁.Adj]
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet lastAliveSet : Finset (Fin edges.length))
    (Z_step6 : Finset (Fin n)) (step6_flag last_g : ℕ)
    (f_tau : Fin edges.length → Fin t)
    (p : ℕ → ℕ) (v : Fin t) (hv_leaf : v ∈ treeLeaves (parentTree t p))
    (g_idx : Fin edges.length)
    (hG_le : graphOfAlive edges hedges.1 aliveSet ≤ H₁)
    (hg_al : g_idx ∈ aliveSet) (hg_v : f_tau g_idx = v)
    (hother : ∃ j ∈ aliveSet, f_tau j = v ∧ j ≠ g_idx)
    (hpart : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
      (parentTree t p) (tauOfArr edges t ht_pos f_tau))
    (hcert : Step6CertInv ω H₁ edges hedges.1 aliveSet lastAliveSet Z_step6 step6_flag last_g)
    (hZ_card : (leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
      (tauOfArr edges t ht_pos f_tau) v).card = 3 * ω)
    (ht_le : t + 2 ≤ 2 * edges.length)
    (hw2 : 2 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (h2m2_w : 2 + 2 * edges.length < 2 ^ w) (ht2_w : t + 2 < 2 ^ w)
    (h3w_w : 3 * ω < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hpar : IsParentArr edges.length t p 6 s)
    (hlast_al : IsBitSet lastAliveSet 7 s)
    (hlast_Z : IsBitSet Z_step6 8 s)
    (hZ : IsBitSet
      (leafCutVerts (graphOfAlive edges hedges.1 aliveSet) (tauOfArr edges t ht_pos f_tau) v) 12 s)
    (hZlist : IsZListArr
      (zListUpTo (leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
        (tauOfArr edges t ht_pos f_tau) v) n) 13 s)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = edges.length)
    (hr3 : s.regs 3 = 2 * edges.length)
    (hr4 : s.regs 4 = t)
    (hr5 : s.regs 5 = step6_flag)
    (hr6 : s.regs 6 = last_g)
    (hr7 : s.regs 7 = v.1)
    (hr9 : s.regs 9 = g_idx.1) :
    ∃ s' t_456,
      Exec w (step456Prog ω) s s' t_456 ∧
      t_456 ≤
        3 ^ (3 * ω) * ((ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω + 2) +
          40 * n + 150 * edges.length + 80 ∧
      IsEndpointArrs edges 2 3 s' ∧
      s'.regs 0 = n ∧
      s'.regs 1 = s.regs 1 ∧
      s'.regs 2 = edges.length ∧
      s'.regs 3 = s.regs 3 ∧
      ((∃ f_tau' : Fin edges.length → Fin (t + 2),
          let p' := splitLeafParent p t v.1
          IsBitSet aliveSet 4 s' ∧
          IsTauArr f_tau' 5 s' ∧
          IsParentArr edges.length (t + 2) p' 6 s' ∧
          IsBitSet lastAliveSet 7 s' ∧
          IsBitSet Z_step6 8 s' ∧
          IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
            (parentTree (t + 2) p') (tauOfArr edges (t + 2) (by omega) f_tau') ∧
          Step6CertInv ω H₁ edges hedges.1 aliveSet lastAliveSet Z_step6 step6_flag last_g ∧
          s'.regs 4 = t + 2 ∧
          s'.regs 5 = step6_flag ∧
          s'.regs 6 = last_g) ∨
       (let aliveSet' := aliveSet.erase g_idx
        let Z := leafCutVerts (graphOfAlive edges hedges.1 aliveSet)
          (tauOfArr edges t ht_pos f_tau) v
        IsBitSet aliveSet' 4 s' ∧
        IsTauArr f_tau 5 s' ∧
        IsParentArr edges.length t p 6 s' ∧
        IsBitSet aliveSet 7 s' ∧
        IsBitSet Z 8 s' ∧
        IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet')
          (parentTree t p) (tauOfArr edges t ht_pos f_tau) ∧
        Step6CertInv ω H₁ edges hedges.1 aliveSet' aliveSet Z 1 g_idx.1 ∧
        s'.regs 4 = t ∧
        s'.regs 5 = 1 ∧
        s'.regs 6 = g_idx.1)) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm2_w : edges.length < 2 ^ w := by omega
  have ht_w : t < 2 ^ w := by omega
  let G := graphOfAlive edges hedges.1 aliveSet
  let τ := tauOfArr edges t ht_pos f_tau
  let R := leafGraph G τ v
  let Z := leafCutVerts G τ v
  -- 1. buildSubgraphCsrProg
  rcases buildSubgraphCsrProg_exec ht_pos hedges aliveSet f_tau v Z
      hw2 hn_w ht_w h2m2_w hend hal htau hZ hr0 hr2 hr3 hr7 with
    ⟨s₁, t₁, hex₁, ht₁, hadj_sub₁, hent_sub₁, _, _, harr₁, hreg₁⟩
  -- 2. r_10 := 0
  let s₂ := s₁.setReg 10 0
  have hex₂ : Exec w (.assign 10 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have harr₂_lt14 : ∀ a : Arr, a < 14 → a ≠ inArr → s₂.arrs a = s.arrs a := by
    intro a ha14 hain
    dsimp [Arr] at ha14
    exact harr₁ a hain (by dsimp [Arr]; omega) (by dsimp [Arr]; omega)
      (by dsimp [Arr]; omega) (by dsimp [Arr]; omega)
  have hreg₂_lt10 : ∀ r : Reg, r < 10 → s₂.regs r = s.regs r := by
    intro r hr10
    dsimp [Reg] at hr10
    simp [s₂, show (r : Reg) ≠ 10 by dsimp [Reg]; omega]
    exact hreg₁ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
  -- 3. checkTemplatesListProg ω (validTernaryLists ω)
  have hls_val : ∀ l ∈ validTernaryLists ω, validTemplate ω l :=
    fun l hl => (mem_validTernaryLists_iff ω l).mp hl
  rcases checkTemplatesListProg_exec hω ht_pos hedges aliveSet f_tau p v hv_leaf hpart hZ_card
      (validTernaryLists ω) hls_val ht_le hw2 h2n_w h2m2_w ht2_w h3w_w (s := s₂)
      (hend.of_arrs_eq
        (harr₂_lt14 2 (by decide) (by decide))
        (harr₂_lt14 3 (by decide) (by decide)))
      (hal.of_arr_eq (harr₂_lt14 4 (by decide) (by decide)))
      (htau.of_arr_eq (harr₂_lt14 5 (by decide) (by decide)))
      (hpar.of_arr_eq (harr₂_lt14 6 (by decide) (by decide)))
      (hZ.of_arr_eq (harr₂_lt14 12 (by decide) (by decide)))
      (hZlist.of_arr_eq (harr₂_lt14 13 (by decide) (by decide)))
      (hadj_sub₁.of_arrs_eq rfl rfl rfl)
      hent_sub₁
      (by rw [hreg₂_lt10 0 (by decide), hr0])
      (by rw [hreg₂_lt10 2 (by decide), hr2])
      (by rw [hreg₂_lt10 4 (by decide), hr4])
      (by rw [hreg₂_lt10 7 (by decide), hr7])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, harr₃_lt10, harr₃_keep, hreg₃_lt10, hres₃⟩
  have hlen_vtl : (validTernaryLists ω).length ≤ 3 ^ (3 * ω) := length_validTernaryLists_le ω
  have ht₃_bound : t₃ ≤
      1 + 3 ^ (3 * ω) * ((ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω + 2) := by
    have hmul := Nat.mul_le_mul_right
      ((ω + 2) * (350 * n + 170 * edges.length + 100) + 18 * ω + 2) hlen_vtl
    omega
  rcases hres₃ with ⟨hr10_3, f_tau', htau₃, hpar₃, hpart₃, hr4_3⟩ |
      ⟨hr10_3, harr5_3, harr6_3, hr4_3, hobs_all⟩
  · -- Step (5) succeeded: r_10 = 1 -> .skip
    have hcond10 : (Expr.reg 10).eval w s₃ = some 1 := by
      simp [Expr.eval, checkWord, hr10_3, hw]
    have hex_ite : Exec w (.ite (.reg 10) .skip step6DeleteProg) s₃ s₃ 2 :=
      .ite_true hcond10 (by omega) (.skip s₃)
    refine ⟨s₃, t₁ + (2 + (t₃ + 2)),
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex_ite)),
      by omega,
      hend.of_arrs_eq
        (by rw [harr₃_lt10 2 (by decide) (by decide) (by decide), harr₂_lt14 2 (by decide) (by decide)])
        (by rw [harr₃_lt10 3 (by decide) (by decide) (by decide), harr₂_lt14 3 (by decide) (by decide)]),
      by rw [hreg₃_lt10 0 (by decide) (by decide), hreg₂_lt10 0 (by decide), hr0],
      by rw [hreg₃_lt10 1 (by decide) (by decide), hreg₂_lt10 1 (by decide)],
      by rw [hreg₃_lt10 2 (by decide) (by decide), hreg₂_lt10 2 (by decide), hr2],
      by rw [hreg₃_lt10 3 (by decide) (by decide), hreg₂_lt10 3 (by decide)],
      Or.inl ⟨f_tau',
        hal.of_arr_eq
          (by rw [harr₃_lt10 4 (by decide) (by decide) (by decide), harr₂_lt14 4 (by decide) (by decide)]),
        htau₃, hpar₃,
        hlast_al.of_arr_eq
          (by rw [harr₃_lt10 7 (by decide) (by decide) (by decide), harr₂_lt14 7 (by decide) (by decide)]),
        hlast_Z.of_arr_eq
          (by rw [harr₃_lt10 8 (by decide) (by decide) (by decide), harr₂_lt14 8 (by decide) (by decide)]),
        hpart₃, hcert, hr4_3,
        by rw [hreg₃_lt10 5 (by decide) (by decide), hreg₂_lt10 5 (by decide), hr5],
        by rw [hreg₃_lt10 6 (by decide) (by decide), hreg₂_lt10 6 (by decide), hr6]⟩⟩
  · -- Step (5) did not split: r_10 = 0 -> Step (6) deletion
    have hcond10 : (Expr.reg 10).eval w s₃ = some 0 := by
      simp [Expr.eval, checkWord, hr10_3, h0_w]
    have hno_sep : ∀ sep : GraphSeparation G, sep.order ≤ ω → ¬ sep.IsBalancedQ Z := by
      apply no_balanced_separation_of_step6 hZ_card
      intro Z₁ Z₂ Z₃ hvalid
      rcases exists_validTernaryLists_of_isValidZPartition hvalid with ⟨l, hl_mem, hp0, hp1, hp2⟩
      have hobs := hobs_all l hl_mem
      dsimp only at hobs
      rwa [hp0, hp1, hp2] at hobs
    rcases step6DeleteProg_exec ht_pos hedges aliveSet f_tau p v g_idx
        hG_le hg_al hg_v hother hpart hZ_card hno_sep hw hn_w hm2_w (s := s₃)
        (hal.of_arr_eq
          (by rw [harr₃_lt10 4 (by decide) (by decide) (by decide), harr₂_lt14 4 (by decide) (by decide)]))
        (hZ.of_arr_eq
          (by rw [harr₃_keep 12 (Or.inl rfl), harr₂_lt14 12 (by decide) (by decide)]))
        (by rw [hreg₃_lt10 0 (by decide) (by decide), hreg₂_lt10 0 (by decide), hr0])
        (by rw [hreg₃_lt10 2 (by decide) (by decide), hreg₂_lt10 2 (by decide), hr2])
        (by rw [hreg₃_lt10 9 (by decide) (by decide), hreg₂_lt10 9 (by decide), hr9]) with
      ⟨s₄, t₄, hex₄, ht₄, hal₄, hlast_al₄, hlast_Z₄, hpart₄, hcert₄, hr5_4, hr6_4, harr₄, hreg₄⟩
    have hex_ite : Exec w (.ite (.reg 10) .skip step6DeleteProg) s₃ s₄ (1 + t₄) :=
      .ite_false hcond10 hex₄
    refine ⟨s₄, t₁ + (2 + (t₃ + (1 + t₄))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex_ite)),
      by omega,
      hend.of_arrs_eq
        (by rw [harr₄ 2 (by decide) (by decide) (by decide),
            harr₃_lt10 2 (by decide) (by decide) (by decide), harr₂_lt14 2 (by decide) (by decide)])
        (by rw [harr₄ 3 (by decide) (by decide) (by decide),
            harr₃_lt10 3 (by decide) (by decide) (by decide), harr₂_lt14 3 (by decide) (by decide)]),
      by rw [hreg₄ 0 (by decide) (by decide) (by decide),
          hreg₃_lt10 0 (by decide) (by decide), hreg₂_lt10 0 (by decide), hr0],
      by rw [hreg₄ 1 (by decide) (by decide) (by decide),
          hreg₃_lt10 1 (by decide) (by decide), hreg₂_lt10 1 (by decide)],
      by rw [hreg₄ 2 (by decide) (by decide) (by decide),
          hreg₃_lt10 2 (by decide) (by decide), hreg₂_lt10 2 (by decide), hr2],
      by rw [hreg₄ 3 (by decide) (by decide) (by decide),
          hreg₃_lt10 3 (by decide) (by decide), hreg₂_lt10 3 (by decide)],
      Or.inr ⟨hal₄,
        htau.of_arr_eq
          (by rw [harr₄ 5 (by decide) (by decide) (by decide), harr5_3,
              harr₂_lt14 5 (by decide) (by decide)]),
        hpar.of_arr_eq
          (by rw [harr₄ 6 (by decide) (by decide) (by decide), harr6_3,
              harr₂_lt14 6 (by decide) (by decide)]),
        hlast_al₄, hlast_Z₄, hpart₄, hcert₄,
        by rw [hreg₄ 4 (by decide) (by decide) (by decide), hr4_3],
        hr5_4, hr6_4⟩⟩

/-! ### Section 6: Outer Loop, Output Serialization, and Main Theorem (`gm13_algorithm_3_3`)

#### Subpart 6.1: Leaf-Cardinality Invariant, Single Iteration (`alg33IterStep`), and Outer Loop (`alg33LoopProg`)
-/

/-- Whenever `2 * (treeLeaves (parentTree t p)).card = t + 2` and a leaf `v : Fin t` has two
distinct active edges `i₁, i₂ ∈ aliveSet` mapped to `v`:
1. `v ∈ treeLeaves (parentTree t p)`.
2. `t + 2 ≤ 2 * (aliveSet.card - 1)` (by surjectivity of `f_tau` from `aliveSet.erase i₁` onto
   `treeLeaves (parentTree t p)`).
3. `1 ≤ aliveSet.card` and `t + 2 ≤ 2 * edges.length`. -/
theorem two_add_t_le_two_mul_card_erase {n t ω : ℕ} (ht_pos : 0 < t)
    {H₂ : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet : Finset (Fin edges.length)) (f_tau : Fin edges.length → Fin t)
    (p : ℕ → ℕ)
    (hpart : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
      (parentTree t p) (tauOfArr edges t ht_pos f_tau))
    (hleaves_card : 2 * (treeLeaves (parentTree t p)).card = t + 2)
    {v : Fin t} {i₁ i₂ : Fin edges.length}
    (hij : i₁.1 < i₂.1) (hi₁ : i₁ ∈ aliveSet) (hi₂ : i₂ ∈ aliveSet)
    (hfi₁ : f_tau i₁ = v) (hfi₂ : f_tau i₂ = v) :
    v ∈ treeLeaves (parentTree t p) ∧
    t + 2 ≤ 2 * (aliveSet.card - 1) ∧
    1 ≤ aliveSet.card ∧
    t + 2 ≤ 2 * edges.length := by
  have he₁ : symEdgeAt edges i₁ ∈ (graphOfAlive edges hedges.1 aliveSet).edgeFinset := by
    rw [mem_edgeFinset_graphOfAlive_iff hedges]
    exact ⟨i₁, hi₁, rfl⟩
  have hτ_i₁ : tauOfArr edges t ht_pos f_tau (symEdgeAt edges i₁) = v := by
    rw [tauOfArr_symEdgeAt hedges]; exact hfi₁
  have hv_leaf : v ∈ treeLeaves (parentTree t p) := by
    rw [← hτ_i₁]; exact hpart.2.1 _ he₁
  have hsub : treeLeaves (parentTree t p) ⊆ (aliveSet.erase i₁).image f_tau := by
    intro w hw
    rw [Finset.mem_image]
    by_cases hwv : w = v
    · subst hwv
      refine ⟨i₂, Finset.mem_erase.mpr ⟨by intro h; subst h; omega, hi₂⟩, hfi₂⟩
    · rcases hpart.2.2.1 w hw with ⟨e, he, hτe⟩
      rw [mem_edgeFinset_graphOfAlive_iff hedges] at he
      rcases he with ⟨j, hj_al, rfl⟩
      rw [tauOfArr_symEdgeAt hedges] at hτe
      have hj_ne : j ≠ i₁ := by
        intro h; subst h; exact hwv (hτe.symm.trans hfi₁)
      exact ⟨j, Finset.mem_erase.mpr ⟨hj_ne, hj_al⟩, hτe⟩
  have hcard_le : (treeLeaves (parentTree t p)).card ≤ aliveSet.card - 1 := by
    calc (treeLeaves (parentTree t p)).card
      _ ≤ ((aliveSet.erase i₁).image f_tau).card := Finset.card_le_card hsub
      _ ≤ (aliveSet.erase i₁).card := Finset.card_image_le
      _ = aliveSet.card - 1 := Finset.card_erase_of_mem hi₁
  have hal_pos : 1 ≤ aliveSet.card := Finset.card_pos.mpr ⟨i₁, hi₁⟩
  have hal_le_m2 : aliveSet.card ≤ edges.length := by
    calc aliveSet.card
      _ ≤ (Finset.univ : Finset (Fin edges.length)).card := Finset.card_le_univ _
      _ = edges.length := Fintype.card_fin edges.length
  refine ⟨hv_leaf, by omega, hal_pos, by omega⟩

/-- One step of the main loop of Algorithm (3.3) when `r_7 = v.1 < r_4 = t`:
1. Computes `Z = leafCutVerts G τ v` (`computeZProg`), setting `r_8 = |Z|`.
2. Selects a candidate edge `g_cand = r_9` mapped to `v` (`selectCandEdgeProg`).
3. If `r_8 < 3 * ω`, executes Step (3) (`step3Prog`); otherwise (`r_8 = 3 * ω`), executes
   Steps (4)–(6) (`step456Prog ω`). -/
def alg33IterStep (ω : ℕ) : Cmd :=
  .seq computeZProg
    (.seq selectCandEdgeProg
      (.ite (.op .lt (.reg 8) (.const (3 * ω)))
        step3Prog
        (step456Prog ω)))

/-- Step-count bound for one iteration of `alg33IterStep ω`. -/
def iterStepMax (ω n m₂ : ℕ) : ℕ :=
  3 ^ (3 * ω) * ((ω + 2) * (350 * n + 170 * m₂ + 100) + 18 * ω + 2) +
    80 * n + 240 * m₂ + 120

theorem iterStepMax_le_mul (ω n m₂ X : ℕ) (hn : n ≤ X) (hm : m₂ ≤ X) (h1 : 1 ≤ X) :
    iterStepMax ω n m₂ + 30 * m₂ + 12 ≤ (iterStepMax ω 1 1 + 50) * X := by
  have h1' : 350 * n + 170 * m₂ + 100 ≤ 620 * X := by omega
  have ha : (ω + 2) * (350 * n + 170 * m₂ + 100) ≤ ((ω + 2) * 620) * X := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left (ω + 2) h1'
  have hb : 18 * ω + 2 ≤ (18 * ω + 2) * X := by
    calc 18 * ω + 2 = (18 * ω + 2) * 1 := (Nat.mul_one _).symm
      _ ≤ (18 * ω + 2) * X := Nat.mul_le_mul_left _ h1
  have h2' : (ω + 2) * (350 * n + 170 * m₂ + 100) + 18 * ω + 2 ≤
      ((ω + 2) * 620 + 18 * ω + 2) * X := by
    have h := Nat.add_le_add ha hb
    rw [← Nat.add_mul, ← Nat.add_assoc, ← Nat.add_assoc] at h
    exact h
  have h3' : 3 ^ (3 * ω) * ((ω + 2) * (350 * n + 170 * m₂ + 100) + 18 * ω + 2) ≤
      (3 ^ (3 * ω) * ((ω + 2) * 620 + 18 * ω + 2)) * X := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left (3 ^ (3 * ω)) h2'
  have h4' : 80 * n + 240 * m₂ + 120 + 30 * m₂ + 12 ≤ 490 * X := by omega
  have htot : 3 ^ (3 * ω) * ((ω + 2) * (350 * n + 170 * m₂ + 100) + 18 * ω + 2) +
      (80 * n + 240 * m₂ + 120 + 30 * m₂ + 12) ≤
      (3 ^ (3 * ω) * ((ω + 2) * 620 + 18 * ω + 2)) * X + 490 * X :=
    Nat.add_le_add h3' h4'
  have hrhs : (iterStepMax ω 1 1 + 50) * X =
      (3 ^ (3 * ω) * ((ω + 2) * 620 + 18 * ω + 2)) * X + 490 * X := by
    change (3 ^ (3 * ω) * ((ω + 2) * 620 + 18 * ω + 2) + 490) * X = _
    exact Nat.add_mul _ 490 X
  rw [hrhs]
  unfold iterStepMax
  omega

theorem alg33IterStep_exec {w n t ω : ℕ} (hω : 1 ≤ ω) (ht_pos : 0 < t)
    {H₁ H₂ : SimpleGraph (Fin n)} [DecidableRel H₁.Adj]
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (aliveSet lastAliveSet : Finset (Fin edges.length))
    (Z_step6 : Finset (Fin n)) (step6_flag last_g : ℕ)
    (f_tau : Fin edges.length → Fin t)
    (p : ℕ → ℕ) (v : Fin t) {i₁ i₂ : Fin edges.length}
    (hij : i₁.1 < i₂.1) (hi₁ : i₁ ∈ aliveSet) (hi₂ : i₂ ∈ aliveSet)
    (hfi₁ : f_tau i₁ = v) (hfi₂ : f_tau i₂ = v)
    (hG2_le : H₂ ≤ H₁)
    (hpart : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
      (parentTree t p) (tauOfArr edges t ht_pos f_tau))
    (hcert : Step6CertInv ω H₁ edges hedges.1 aliveSet lastAliveSet Z_step6 step6_flag last_g)
    (hleaves_card : 2 * (treeLeaves (parentTree t p)).card = t + 2)
    (hw2 : 2 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (h2m2_w : 2 + 2 * edges.length < 2 ^ w) (h3w_w : 3 * ω < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges 2 3 s)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hpar : IsParentArr edges.length t p 6 s)
    (hlast_al : IsBitSet lastAliveSet 7 s)
    (hlast_Z : IsBitSet Z_step6 8 s)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = edges.length)
    (hr3 : s.regs 3 = 2 * edges.length)
    (hr4 : s.regs 4 = t)
    (hr5 : s.regs 5 = step6_flag)
    (hr6 : s.regs 6 = last_g)
    (hr7 : s.regs 7 = v.1) :
    ∃ (s' : State) (t_step t' : ℕ) (ht'_pos : 0 < t')
      (aliveSet' lastAliveSet' : Finset (Fin edges.length))
      (Z_step6' : Finset (Fin n)) (step6_flag' last_g' : ℕ)
      (f_tau' : Fin edges.length → Fin t') (p' : ℕ → ℕ),
      Exec w (alg33IterStep ω) s s' t_step ∧
      t_step ≤ iterStepMax ω n edges.length ∧
      IsEndpointArrs edges 2 3 s' ∧
      IsBitSet aliveSet' 4 s' ∧
      IsTauArr f_tau' 5 s' ∧
      IsParentArr edges.length t' p' 6 s' ∧
      IsBitSet lastAliveSet' 7 s' ∧
      IsBitSet Z_step6' 8 s' ∧
      IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet')
        (parentTree t' p') (tauOfArr edges t' ht'_pos f_tau') ∧
      Step6CertInv ω H₁ edges hedges.1 aliveSet' lastAliveSet' Z_step6' step6_flag' last_g' ∧
      2 * (treeLeaves (parentTree t' p')).card = t' + 2 ∧
      ((t' = t + 2 ∧ aliveSet' = aliveSet) ∨
       (t' = t ∧ aliveSet'.card + 1 = aliveSet.card)) ∧
      s'.regs 0 = n ∧
      s'.regs 1 = s.regs 1 ∧
      s'.regs 2 = edges.length ∧
      s'.regs 3 = 2 * edges.length ∧
      s'.regs 4 = t' ∧
      s'.regs 5 = step6_flag' ∧
      s'.regs 6 = last_g' := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm2_w : edges.length < 2 ^ w := by omega
  obtain ⟨hv_leaf, ht_le_erase, hal_pos, ht_le⟩ :=
    two_add_t_le_two_mul_card_erase ht_pos hedges aliveSet f_tau p
      hpart hleaves_card hij hi₁ hi₂ hfi₁ hfi₂
  have ht2_w : t + 2 < 2 ^ w := by omega
  have ht_w : t < 2 ^ w := by omega
  -- 1. computeZProg
  rcases computeZProg_exec ht_pos hedges aliveSet f_tau v hw hn_w hm2_w ht_w
      hend hal htau hr0 hr2 hr7 with
    ⟨s₁, t₁, hex₁, ht₁, hZ₁, hZlist₁, hr8_1, harr₁, hreg₁⟩
  -- 2. selectCandEdgeProg
  rcases selectCandEdgeProg_exec ht_pos hedges aliveSet f_tau v ⟨i₁, hi₁, hfi₁⟩
      hw2 hn_w hm2_w ht_w (s := s₁)
      (hend.of_arrs_eq
        (harr₁ 2 (by decide) (by decide) (by decide) (by decide))
        (harr₁ 3 (by decide) (by decide) (by decide) (by decide)))
      (hal.of_arr_eq (harr₁ 4 (by decide) (by decide) (by decide) (by decide)))
      (htau.of_arr_eq (harr₁ 5 (by decide) (by decide) (by decide) (by decide)))
      hZ₁
      (by rw [hreg₁ 2 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide), hr2])
      (by rw [hreg₁ 7 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide), hr7]) with
    ⟨s₂, t₂, hex₂, ht₂, ⟨g_idx, hr9_2, hg_al, hg_v, hg_inc⟩, harr₂, hreg₂⟩
  have harr₂_lt9 : ∀ a : Arr, a < 9 → s₂.arrs a = s.arrs a := by
    intro a ha9
    dsimp [Arr] at ha9
    rw [harr₂]
    exact harr₁ a (by dsimp [Arr]; omega) (by dsimp [Arr]; omega)
      (by dsimp [Arr]; omega) (by dsimp [Arr]; omega)
  have hreg₂_lt8 : ∀ r : Reg, r < 8 → s₂.regs r = s.regs r := by
    intro r hr8
    dsimp [Reg] at hr8
    rw [hreg₂ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
    exact hreg₁ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega)
  have hother3 : ∃ j₀ ∈ aliveSet, j₀ ≠ g_idx ∧ f_tau j₀ = v := by
    by_cases hg1 : i₁ = g_idx
    · exact ⟨i₂, hi₂, fun h => by subst hg1 h; omega, hfi₂⟩
    · exact ⟨i₁, hi₁, hg1, hfi₁⟩
  have hother456 : ∃ j ∈ aliveSet, f_tau j = v ∧ j ≠ g_idx := by
    rcases hother3 with ⟨j₀, hj₀, hne, hfv⟩
    exact ⟨j₀, hj₀, hfv, hne⟩
  let G := graphOfAlive edges hedges.1 aliveSet
  let τ := tauOfArr edges t ht_pos f_tau
  let Z := leafCutVerts G τ v
  have hr8_2 : s₂.regs 8 = Z.card := by
    rw [hreg₂ 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hr8_1]
  have hZ_le_3w : Z.card ≤ 3 * ω := card_leafCutVerts_le_three_mul_omega hpart hv_leaf
  have hZ_w : Z.card < 2 ^ w := by omega
  by_cases hZ_lt : Z.card < 3 * ω
  · -- Case `|Z| < 3ω`: execute `step3Prog`
    have hcond8 : (Expr.op .lt (.reg 8) (.const (3 * ω))).eval w s₂ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_2, hZ_w, h3w_w, hZ_lt, hw]
    rcases step3Prog_exec ht_pos hedges aliveSet f_tau p v g_idx
        hpart hv_leaf hZ_lt hg_al hg_v hother3 hg_inc ht_le hw2 hm2_w ht2_w (s := s₂)
        (htau.of_arr_eq (harr₂_lt9 5 (by decide)))
        (hpar.of_arr_eq (harr₂_lt9 6 (by decide)))
        (by rw [hreg₂_lt8 2 (by decide), hr2])
        (by rw [hreg₂_lt8 4 (by decide), hr4])
        (by rw [hreg₂_lt8 7 (by decide), hr7])
        hr9_2 with
      ⟨s₃, t₃, hex₃, ht₃, htau₃, hpar₃, hpart₃, hr4_3, harr₃, hreg₃⟩
    have hex_ite : Exec w (.ite (.op .lt (.reg 8) (.const (3 * ω))) step3Prog (step456Prog ω))
        s₂ s₃ (3 + t₃) := .ite_true hcond8 (by omega) hex₃
    have hleaves' : 2 * (treeLeaves (parentTree (t + 2) (splitLeafParent p t v.1))).card =
        (t + 2) + 2 := by
      rw [card_treeLeaves_splitLeafParent hpar.2.2.2 ht_pos hv_leaf]
      omega
    have htime : t₁ + (t₂ + (3 + t₃)) ≤ iterStepMax ω n edges.length := by
      unfold iterStepMax
      omega
    refine ⟨s₃, t₁ + (t₂ + (3 + t₃)), t + 2, by omega,
      aliveSet, lastAliveSet, Z_step6, step6_flag, last_g,
      step3FTau f_tau v g_idx, splitLeafParent p t v.1,
      .seq hex₁ (.seq hex₂ hex_ite), htime,
      hend.of_arrs_eq
        (by rw [harr₃ 2 (by decide) (by decide), harr₂_lt9 2 (by decide)])
        (by rw [harr₃ 3 (by decide) (by decide), harr₂_lt9 3 (by decide)]),
      hal.of_arr_eq (by rw [harr₃ 4 (by decide) (by decide), harr₂_lt9 4 (by decide)]),
      htau₃, hpar₃,
      hlast_al.of_arr_eq (by rw [harr₃ 7 (by decide) (by decide), harr₂_lt9 7 (by decide)]),
      hlast_Z.of_arr_eq (by rw [harr₃ 8 (by decide) (by decide), harr₂_lt9 8 (by decide)]),
      hpart₃, hcert, hleaves', Or.inl ⟨rfl, rfl⟩,
      by rw [hreg₃ 0 (by decide) (by decide) (by decide), hreg₂_lt8 0 (by decide), hr0],
      by rw [hreg₃ 1 (by decide) (by decide) (by decide), hreg₂_lt8 1 (by decide)],
      by rw [hreg₃ 2 (by decide) (by decide) (by decide), hreg₂_lt8 2 (by decide), hr2],
      by rw [hreg₃ 3 (by decide) (by decide) (by decide), hreg₂_lt8 3 (by decide), hr3],
      hr4_3,
      by rw [hreg₃ 5 (by decide) (by decide) (by decide), hreg₂_lt8 5 (by decide), hr5],
      by rw [hreg₃ 6 (by decide) (by decide) (by decide), hreg₂_lt8 6 (by decide), hr6]⟩
  · -- Case `|Z| = 3ω`: execute `step456Prog ω`
    have hZ_card : Z.card = 3 * ω := by omega
    have hcond8 : (Expr.op .lt (.reg 8) (.const (3 * ω))).eval w s₂ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_2, hZ_card, h3w_w, h0_w]
    have hG_le : G ≤ H₁ := by
      refine (?_ : G ≤ H₂).trans hG2_le
      intro u w ⟨k, _, hmatch⟩
      exact (hedges.2.2 u w).mpr ⟨k.1, k.2, hmatch⟩
    rcases step456Prog_exec hω ht_pos hedges aliveSet lastAliveSet Z_step6 step6_flag last_g
        f_tau p v hv_leaf g_idx hG_le hg_al hg_v hother456 hpart hcert hZ_card
        ht_le hw2 h2n_w h2m2_w ht2_w h3w_w (s := s₂)
        (hend.of_arrs_eq (harr₂_lt9 2 (by decide)) (harr₂_lt9 3 (by decide)))
        (hal.of_arr_eq (harr₂_lt9 4 (by decide)))
        (htau.of_arr_eq (harr₂_lt9 5 (by decide)))
        (hpar.of_arr_eq (harr₂_lt9 6 (by decide)))
        (hlast_al.of_arr_eq (harr₂_lt9 7 (by decide)))
        (hlast_Z.of_arr_eq (harr₂_lt9 8 (by decide)))
        (hZ₁.of_arr_eq (congrFun harr₂ 12))
        (hZlist₁.of_arr_eq (congrFun harr₂ 13))
        (by rw [hreg₂_lt8 0 (by decide), hr0])
        (by rw [hreg₂_lt8 2 (by decide), hr2])
        (by rw [hreg₂_lt8 3 (by decide), hr3])
        (by rw [hreg₂_lt8 4 (by decide), hr4])
        (by rw [hreg₂_lt8 5 (by decide), hr5])
        (by rw [hreg₂_lt8 6 (by decide), hr6])
        (by rw [hreg₂_lt8 7 (by decide), hr7])
        hr9_2 with
      ⟨s₃, t₃, hex₃, ht₃, hend₃, hr0_3, hr1_3, hr2_3, hr3_3, hres₃⟩
    have hex_ite : Exec w (.ite (.op .lt (.reg 8) (.const (3 * ω))) step3Prog (step456Prog ω))
        s₂ s₃ (3 + t₃) := .ite_false hcond8 hex₃
    have htime : t₁ + (t₂ + (3 + t₃)) ≤ iterStepMax ω n edges.length := by
      unfold iterStepMax
      omega
    rcases hres₃ with
      ⟨f_tau', hal₃, htau₃, hpar₃, hlast_al₃, hlast_Z₃, hpart₃, hcert₃, hr4_3, hr5_3, hr6_3⟩ |
      ⟨hal₃, htau₃, hpar₃, hlast_al₃, hlast_Z₃, hpart₃, hcert₃, hr4_3, hr5_3, hr6_3⟩
    · -- Step (5) occurred
      have hleaves' : 2 * (treeLeaves (parentTree (t + 2) (splitLeafParent p t v.1))).card =
          (t + 2) + 2 := by
        rw [card_treeLeaves_splitLeafParent hpar.2.2.2 ht_pos hv_leaf]
        omega
      refine ⟨s₃, t₁ + (t₂ + (3 + t₃)), t + 2, by omega,
        aliveSet, lastAliveSet, Z_step6, step6_flag, last_g,
        f_tau', splitLeafParent p t v.1,
        .seq hex₁ (.seq hex₂ hex_ite), htime,
        hend₃, hal₃, htau₃, hpar₃, hlast_al₃, hlast_Z₃,
        hpart₃, hcert₃, hleaves', Or.inl ⟨rfl, rfl⟩,
        hr0_3, by rw [hr1_3, hreg₂_lt8 1 (by decide)], hr2_3,
        by rw [hr3_3, hreg₂_lt8 3 (by decide), hr3],
        hr4_3, hr5_3, hr6_3⟩
    · -- Step (6) occurred
      have hcard_erase : (aliveSet.erase g_idx).card + 1 = aliveSet.card :=
        Finset.card_erase_add_one hg_al
      refine ⟨s₃, t₁ + (t₂ + (3 + t₃)), t, ht_pos,
        aliveSet.erase g_idx, aliveSet, Z, 1, g_idx.1,
        f_tau, p,
        .seq hex₁ (.seq hex₂ hex_ite), htime,
        hend₃, hal₃, htau₃, hpar₃, hlast_al₃, hlast_Z₃,
        hpart₃, hcert₃, hleaves_card, Or.inr ⟨rfl, hcard_erase⟩,
        hr0_3, by rw [hr1_3, hreg₂_lt8 1 (by decide)], hr2_3,
        by rw [hr3_3, hreg₂_lt8 3 (by decide), hr3],
        hr4_3, hr5_3, hr6_3⟩

/-- Body of the main `while` loop of Algorithm (3.3): runs `alg33IterStep ω`, then re-runs
`findDupLeafProg` to update `r_7` (`v` or `t`). -/
def alg33WhileBody (ω : ℕ) : Cmd :=
  .seq (alg33IterStep ω) findDupLeafProg

/-- Main loop of Algorithm (3.3): initializes `r_7` via `findDupLeafProg`, then repeats
`alg33WhileBody ω` while `r_7 < r_4`. -/
def alg33LoopProg (ω : ℕ) : Cmd :=
  .seq findDupLeafProg
    (.while (.op .lt (.reg 7) (.reg 4)) (alg33WhileBody ω))

theorem alg33While_exec {w n ω : ℕ} (hω : 1 ≤ ω)
    {H₁ H₂ : SimpleGraph (Fin n)} [DecidableRel H₁.Adj]
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H₂ edges)
    (hG2_le : H₂ ≤ H₁)
    (hw2 : 2 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (h2m2_w : 2 + 2 * edges.length < 2 ^ w) (h3w_w : 3 * ω < 2 ^ w)
    (k_rem : ℕ) :
    ∀ {t : ℕ} (ht_pos : 0 < t)
      (aliveSet lastAliveSet : Finset (Fin edges.length))
      (Z_step6 : Finset (Fin n)) (step6_flag last_g : ℕ)
      (f_tau : Fin edges.length → Fin t) (p : ℕ → ℕ)
      (_hpart : IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet)
        (parentTree t p) (tauOfArr edges t ht_pos f_tau))
      (_hcert : Step6CertInv ω H₁ edges hedges.1 aliveSet lastAliveSet Z_step6 step6_flag last_g)
      (_hleaves_card : 2 * (treeLeaves (parentTree t p)).card = t + 2)
      (_hpot : 2 * aliveSet.card ≤ t + 2 * k_rem)
      {s : State}
      (_hend : IsEndpointArrs edges 2 3 s)
      (_hal : IsBitSet aliveSet 4 s)
      (_htau : IsTauArr f_tau 5 s)
      (_hpar : IsParentArr edges.length t p 6 s)
      (_hlast_al : IsBitSet lastAliveSet 7 s)
      (_hlast_Z : IsBitSet Z_step6 8 s)
      (_hr0 : s.regs 0 = n)
      (_hr2 : s.regs 2 = edges.length)
      (_hr3 : s.regs 3 = 2 * edges.length)
      (_hr4 : s.regs 4 = t)
      (_hr5 : s.regs 5 = step6_flag)
      (_hr6 : s.regs 6 = last_g)
      (_hr7_inv :
        (s.regs 7 = t ∧
          ∀ i j : Fin edges.length, i.1 < j.1 → i ∈ aliveSet → j ∈ aliveSet → f_tau i ≠ f_tau j) ∨
        (∃ (v : Fin t) (i j : Fin edges.length),
          s.regs 7 = v.1 ∧ i.1 < j.1 ∧ i ∈ aliveSet ∧ j ∈ aliveSet ∧
          f_tau i = v ∧ f_tau j = v)),
      ∃ (s' : State) (t_loop t' : ℕ) (ht'_pos : 0 < t')
        (aliveSet' lastAliveSet' : Finset (Fin edges.length))
        (Z_step6' : Finset (Fin n)) (step6_flag' last_g' : ℕ)
        (f_tau' : Fin edges.length → Fin t') (p' : ℕ → ℕ),
        Exec w (.while (.op .lt (.reg 7) (.reg 4)) (alg33WhileBody ω)) s s' t_loop ∧
        t_loop ≤ 3 + k_rem * (iterStepMax ω n edges.length + 30 * edges.length + 12) ∧
        IsEndpointArrs edges 2 3 s' ∧
        IsBitSet aliveSet' 4 s' ∧
        IsTauArr f_tau' 5 s' ∧
        IsParentArr edges.length t' p' 6 s' ∧
        IsBitSet lastAliveSet' 7 s' ∧
        IsBitSet Z_step6' 8 s' ∧
        IsPartialBranchDecomp ω (graphOfAlive edges hedges.1 aliveSet')
          (parentTree t' p') (tauOfArr edges t' ht'_pos f_tau') ∧
        Step6CertInv ω H₁ edges hedges.1 aliveSet' lastAliveSet' Z_step6' step6_flag' last_g' ∧
        2 * (treeLeaves (parentTree t' p')).card = t' + 2 ∧
        (∀ i j : Fin edges.length, i.1 < j.1 → i ∈ aliveSet' → j ∈ aliveSet' →
          f_tau' i ≠ f_tau' j) ∧
        s'.regs 0 = n ∧
        s'.regs 2 = edges.length ∧
        s'.regs 3 = 2 * edges.length ∧
        s'.regs 4 = t' ∧
        s'.regs 5 = step6_flag' ∧
        s'.regs 6 = last_g' := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm2_w : edges.length < 2 ^ w := by omega
  induction k_rem with
  | zero =>
    intro t ht_pos aliveSet lastAliveSet Z_step6 step6_flag last_g f_tau p
      hpart hcert hleaves_card hpot s hend hal htau hpar hlast_al hlast_Z
      hr0 hr2 hr3 hr4 hr5 hr6 hr7_inv
    have ht_le_2m2 : t ≤ 2 * edges.length := hpar.2.1
    have ht_w : t < 2 ^ w := by omega
    rcases hr7_inv with ⟨hr7, hinj⟩ | ⟨v, i₁, i₂, hr7, hij, hi₁, hi₂, hfi₁, hfi₂⟩
    · have hcond : (Expr.op .lt (.reg 7) (.reg 4)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7, hr4, ht_w, h0_w]
      exact ⟨s, 3, t, ht_pos, aliveSet, lastAliveSet, Z_step6, step6_flag, last_g, f_tau, p,
        .while_false hcond, by omega,
        hend, hal, htau, hpar, hlast_al, hlast_Z, hpart, hcert, hleaves_card, hinj,
        hr0, hr2, hr3, hr4, hr5, hr6⟩
    · obtain ⟨_, ht_le_erase, hal_pos, _⟩ :=
        two_add_t_le_two_mul_card_erase ht_pos hedges aliveSet f_tau p
          hpart hleaves_card hij hi₁ hi₂ hfi₁ hfi₂
      omega
  | succ k_rem ih =>
    intro t ht_pos aliveSet lastAliveSet Z_step6 step6_flag last_g f_tau p
      hpart hcert hleaves_card hpot s hend hal htau hpar hlast_al hlast_Z
      hr0 hr2 hr3 hr4 hr5 hr6 hr7_inv
    have ht_le_2m2 : t ≤ 2 * edges.length := hpar.2.1
    have ht_w : t < 2 ^ w := by omega
    rcases hr7_inv with ⟨hr7, hinj⟩ | ⟨v, i₁, i₂, hr7, hij, hi₁, hi₂, hfi₁, hfi₂⟩
    · have hcond : (Expr.op .lt (.reg 7) (.reg 4)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7, hr4, ht_w, h0_w]
      exact ⟨s, 3, t, ht_pos, aliveSet, lastAliveSet, Z_step6, step6_flag, last_g, f_tau, p,
        .while_false hcond, by omega,
        hend, hal, htau, hpar, hlast_al, hlast_Z, hpart, hcert, hleaves_card, hinj,
        hr0, hr2, hr3, hr4, hr5, hr6⟩
    · have hv_w : v.1 < 2 ^ w := by have := v.2; omega
      have hcond : (Expr.op .lt (.reg 7) (.reg 4)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7, hr4, hv_w, ht_w, v.2, hw]
      rcases alg33IterStep_exec hω ht_pos hedges aliveSet lastAliveSet Z_step6 step6_flag last_g
          f_tau p v hij hi₁ hi₂ hfi₁ hfi₂ hG2_le hpart hcert hleaves_card
          hw2 h2n_w h2m2_w h3w_w
          hend hal htau hpar hlast_al hlast_Z hr0 hr2 hr3 hr4 hr5 hr6 hr7 with
        ⟨s₁, t₁, t', ht'_pos, aliveSet', lastAliveSet', Z_step6', step6_flag', last_g',
          f_tau', p', hex₁, ht₁, hend₁, hal₁, htau₁, hpar₁, hlast_al₁, hlast_Z₁,
          hpart₁, hcert₁, hleaves_card₁, hpot_step,
          hr0_1, _, hr2_1, hr3_1, hr4_1, hr5_1, hr6_1⟩
      have ht'_le_2m2 : t' ≤ 2 * edges.length := hpar₁.2.1
      have ht'_w : t' < 2 ^ w := by omega
      rcases findDupLeafProg_exec aliveSet' f_tau' hw hm2_w ht'_w
          hal₁ htau₁ hr2_1 hr4_1 with
        ⟨s₂, t₂, hex₂, ht₂, hr7_inv₂, harr₂, hreg₂⟩
      have hpot' : 2 * aliveSet'.card ≤ t' + 2 * k_rem := by
        rcases hpot_step with ⟨rfl, rfl⟩ | ⟨rfl, hcard'⟩ <;> omega
      rcases ih ht'_pos aliveSet' lastAliveSet' Z_step6' step6_flag' last_g' f_tau' p'
          hpart₁ hcert₁ hleaves_card₁ hpot' (s := s₂)
          (hend₁.of_arrs_eq (harr₂ 2 (by decide)) (harr₂ 3 (by decide)))
          (hal₁.of_arr_eq (harr₂ 4 (by decide)))
          (htau₁.of_arr_eq (harr₂ 5 (by decide)))
          (hpar₁.of_arr_eq (harr₂ 6 (by decide)))
          (hlast_al₁.of_arr_eq (harr₂ 7 (by decide)))
          (hlast_Z₁.of_arr_eq (harr₂ 8 (by decide)))
          (by rw [hreg₂ 0 (by decide) (by decide) (by decide) (by decide) (by decide), hr0_1])
          (by rw [hreg₂ 2 (by decide) (by decide) (by decide) (by decide) (by decide), hr2_1])
          (by rw [hreg₂ 3 (by decide) (by decide) (by decide) (by decide) (by decide), hr3_1])
          (by rw [hreg₂ 4 (by decide) (by decide) (by decide) (by decide) (by decide), hr4_1])
          (by rw [hreg₂ 5 (by decide) (by decide) (by decide) (by decide) (by decide), hr5_1])
          (by rw [hreg₂ 6 (by decide) (by decide) (by decide) (by decide) (by decide), hr6_1])
          hr7_inv₂ with
        ⟨s₃, t₃, t'', ht''_pos, aliveSet'', lastAliveSet'', Z_step6'', step6_flag'', last_g'',
          f_tau'', p'', hex₃, ht₃, hend₃, hal₃, htau₃, hpar₃, hlast_al₃, hlast_Z₃,
          hpart₃, hcert₃, hleaves_card₃, hinj₃, hr0_3, hr2_3, hr3_3, hr4_3, hr5_3, hr6_3⟩
      have hsucc_mul :
          (k_rem + 1) * (iterStepMax ω n edges.length + 30 * edges.length + 12) =
          k_rem * (iterStepMax ω n edges.length + 30 * edges.length + 12) +
            (iterStepMax ω n edges.length + 30 * edges.length + 12) := by
        rw [Nat.add_mul, Nat.one_mul]
      refine ⟨s₃, 3 + (t₁ + t₂) + t₃, t'', ht''_pos,
        aliveSet'', lastAliveSet'', Z_step6'', step6_flag'', last_g'', f_tau'', p'',
        .while_true hcond (by omega) (.seq hex₁ hex₂) hex₃,
        by rw [hsucc_mul]; omega,
        hend₃, hal₃, htau₃, hpar₃, hlast_al₃, hlast_Z₃,
        hpart₃, hcert₃, hleaves_card₃, hinj₃, hr0_3, hr2_3, hr3_3, hr4_3, hr5_3, hr6_3⟩

/-! #### Subpart 6.2: Output Serialization (`appendArrToOutProg`, `writeAlg33OutProg`, `decAlg33Out`) -/

/-- Loop body of `appendArrToOutProg`: writes `a_src[r_11]` to `outArr[r_12]` and increments `r_12`. -/
def appendArrToOutBody (a_src : Arr) : Cmd :=
  .seq (.write outArr (.reg 12) (.read a_src (.reg 11)))
    (.assign 12 (.op .add (.reg 12) (.const 1)))

/-- Appends `a_src[0..r_len)` into `outArr[r_12 .. r_12 + r_len)` using loop index `r_11`, leaving
`r_12 := r_12 + r_len`. -/
def appendArrToOutProg (a_src : Arr) (r_len : Reg) : Cmd :=
  .seq (.assign 11 (.const 0))
    (forUp 11 (.reg r_len) (appendArrToOutBody a_src))

theorem appendArrToOutLoop_exec {w len rem_out : ℕ} (a_src : Arr) (r_len : Reg)
    (hne_out : a_src ≠ outArr) (hr_len : r_len < 11)
    (pre mid : List ℕ) (hmid : mid.length = len)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hout_w : pre.length + len + rem_out < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = len) {s : State}
    (hsrc : (s.arrs a_src).take len = mid)
    (hdst : s.arrs outArr = pre ++ mid.take k ++ List.replicate (rem + rem_out) 0)
    (hrlen_val : s.regs r_len = len)
    (hr11 : s.regs 11 = k)
    (hr12 : s.regs 12 = pre.length + k) :
    ∃ s' t_copy,
      Exec w (forUp 11 (.reg r_len) (appendArrToOutBody a_src)) s s' t_copy ∧
      t_copy ≤ 3 + 16 * rem ∧
      s'.arrs outArr = (pre ++ mid) ++ List.replicate rem_out 0 ∧
      s'.regs 12 = (pre ++ mid).length ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r < 11, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : len < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = len := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 11) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hrlen_val, hlen_w, h0_w]
    have htake : mid.take k = mid := List.take_of_length_le (by omega)
    refine ⟨s, 3, .while_false hcond, by omega, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · simpa [htake] using hdst
    · simp [hr12, hmid]
  | succ rem ih =>
    have hk_lt : k < len := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk_mid : k < mid.length := by omega
    have hpos_w : pre.length + k < 2 ^ w := by omega
    have hpos1_w : pre.length + k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 11) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hrlen_val, hk_w, hlen_w, hk_lt, hw]
    let val := mid[k]'hk_mid
    have hval_w : val < 2 ^ w := hmid_w val (List.getElem_mem hk_mid)
    have hsrc_len_le : len ≤ (s.arrs a_src).length := by
      have h := congrArg List.length hsrc
      rw [List.length_take, hmid] at h
      omega
    have hsrc_len : k < (s.arrs a_src).length := by omega
    have hsrc_get : (s.arrs a_src)[k]'hsrc_len = val := by
      dsimp [val]
      have htake_k : ((s.arrs a_src).take len)[k]'(by rw [hsrc]; exact hk_mid) =
          (s.arrs a_src)[k]'hsrc_len := List.getElem_take
      rw [← htake_k]
      congr 1
    have hdst_len : pre.length + k < (s.arrs outArr).length := by
      rw [hdst, List.length_append, List.length_append, List.length_take, List.length_replicate]
      omega
    let s₁ := s.writeArr outArr (pre.length + k) val
    have hex₁ : Exec w (.write outArr (.reg 12) (.read a_src (.reg 11))) s s₁ 4 :=
      .write (by simp [Expr.eval, checkWord, hr12, hpos_w])
        (by simp [Expr.eval, checkWord, hr11, hk_w, hsrc_len, hsrc_get, hval_w])
        hdst_len
    let s₂ := s₁.setReg 12 (pre.length + k + 1)
    have hex₂ : Exec w (.assign 12 (.op .add (.reg 12) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr12, hpos_w, hw, hpos1_w])
    let s₃ := s₂.setReg 11 (k + 1)
    have hex₃ : Exec w (.assign 11 (.op .add (.reg 11) (.const 1))) s₂ s₃ 4 :=
      .assign (by
        simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr11, hk_w, hw, show k + 1 < 2 ^ w by omega])
    have hdst₃ : s₃.arrs outArr = pre ++ mid.take (k + 1) ++ List.replicate (rem + rem_out) 0 := by
      simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hdst, List.append_assoc]
      have hlen_take : (mid.take k).length = k := by rw [List.length_take]; omega
      rw [List.set_append_right _ _ (by omega)]
      rw [List.set_append_right _ _ (by omega)]
      have hsub0 : pre.length + k - pre.length - (mid.take k).length = 0 := by omega
      have hrep : rem + 1 + rem_out = (rem + rem_out) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      rw [take_add_one_eq_append_getElem mid k hk_mid, List.append_assoc, List.singleton_append]
    rcases ih (k + 1) (by omega) (s := s₃)
        (by simp [s₃, s₂, s₁, hne_out, hsrc])
        hdst₃
        (by
          dsimp [Reg] at hr_len
          simp [s₃, s₂, s₁, State.setReg,
            show (r_len : Reg) ≠ 11 by dsimp [Reg]; omega,
            show (r_len : Reg) ≠ 12 by dsimp [Reg]; omega, hrlen_val])
        (by simp [s₃])
        (by simp [s₃, s₂]; omega) with
      ⟨s₄, t₄, hex₄, ht₄, hdst₄, hr12_4, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((4 + 4) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by omega, hdst₄, hr12_4,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, ha],
      fun r hr11' => by
        dsimp [Reg] at hr11'
        rw [hreg₄ r hr11']
        simp [s₃, s₂, s₁, State.setReg,
          show (r : Reg) ≠ 11 by dsimp [Reg]; omega,
          show (r : Reg) ≠ 12 by dsimp [Reg]; omega]⟩

theorem appendArrToOutProg_exec {w len rem_out : ℕ} (a_src : Arr) (r_len : Reg)
    (hne_out : a_src ≠ outArr) (hr_len : r_len < 11)
    (pre mid : List ℕ) (hmid : mid.length = len)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hout_w : pre.length + len + rem_out < 2 ^ w)
    {s : State}
    (hsrc : (s.arrs a_src).take len = mid)
    (hdst : s.arrs outArr = pre ++ List.replicate (len + rem_out) 0)
    (hrlen_val : s.regs r_len = len)
    (hr12 : s.regs 12 = pre.length) :
    ∃ s' t_copy,
      Exec w (appendArrToOutProg a_src r_len) s s' t_copy ∧
      t_copy ≤ 5 + 16 * len ∧
      s'.arrs outArr = (pre ++ mid) ++ List.replicate rem_out 0 ∧
      s'.regs 12 = (pre ++ mid).length ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r < 11, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 11 0
  have hex₁ : Exec w (.assign 11 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases appendArrToOutLoop_exec a_src r_len hne_out hr_len pre mid hmid hmid_w
      hw hout_w len 0 (by omega) (s := s₁)
      hsrc (by simpa [s₁] using hdst)
      (by
        dsimp [Reg] at hr_len
        simp [s₁, State.setReg, show (r_len : Reg) ≠ 11 by dsimp [Reg]; omega, hrlen_val])
      (by simp [s₁])
      (by simp [s₁, hr12]) with
    ⟨s₂, t₂, hex₂, ht₂, hdst₂, hr12_2, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hdst₂, hr12_2, harr₂,
    fun r hr11' => by
      dsimp [Reg] at hr11'
      rw [hreg₂ r hr11']
      simp [s₁, State.setReg, show (r : Reg) ≠ 11 by dsimp [Reg]; omega]⟩

/-- Preamble of `writeAlg33OutProg`: sets `a_6[0] := 0`, allocates `outArr` of size
`3 + 3 * m₂ + t + n`, writes `outArr[0] := r_4` (`t`), `outArr[1] := r_5` (`step6_flag`),
`outArr[2] := r_6` (`last_g`), and sets `r_12 := 3`. -/
def initAlg33OutCmd : Cmd :=
  .seq (.write 6 (.const 0) (.const 0))
    (.seq (.alloc outArr (.op .add (.const 3)
        (.op .add (.op .mul (.const 3) (.reg 2)) (.op .add (.reg 4) (.reg 0)))))
      (.seq (.write outArr (.const 0) (.reg 4))
        (.seq (.write outArr (.const 1) (.reg 5))
          (.seq (.write outArr (.const 2) (.reg 6))
            (.assign 12 (.const 3))))))

/-- Full output-serialization program for Algorithm (3.3): writes
`[t, step6_flag, last_g] ++ s.arrs 4 ++ s.arrs 5 ++ (a_6).take t ++ s.arrs 7 ++ s.arrs 8`
to `outArr`. -/
def writeAlg33OutProg : Cmd :=
  .seq initAlg33OutCmd
    (.seq (appendArrToOutProg 4 2)
      (.seq (appendArrToOutProg 5 2)
        (.seq (appendArrToOutProg 6 4)
          (.seq (appendArrToOutProg 7 2)
            (appendArrToOutProg 8 0)))))

theorem writeAlg33OutProg_exec {w n m₂ t step6_flag last_g : ℕ}
    (ht_pos : 0 < t)
    (aliveSet lastAliveSet : Finset (Fin m₂))
    (Z_step6 : Finset (Fin n))
    (f_tau : Fin m₂ → Fin t) (p : ℕ → ℕ)
    (hw3 : 3 < 2 ^ w) (hout_w : 3 + 3 * m₂ + t + n < 2 ^ w)
    (hflag_le : step6_flag ≤ 1) (hg_le : last_g ≤ m₂)
    {s : State}
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (hpar : IsParentArr m₂ t p 6 s)
    (hlast_al : IsBitSet lastAliveSet 7 s)
    (hlast_Z : IsBitSet Z_step6 8 s)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = m₂)
    (hr4 : s.regs 4 = t)
    (hr5 : s.regs 5 = step6_flag)
    (hr6 : s.regs 6 = last_g) :
    ∃ (s' : State) (t_out : ℕ) (arr6_out : List ℕ),
      Exec w writeAlg33OutProg s s' t_out ∧
      t_out ≤ 85 * m₂ + 17 * n + 51 ∧
      arr6_out.length = t ∧
      (∀ z (hz : z < arr6_out.length), 0 < z → arr6_out[z]'hz = p z) ∧
      s'.arrs outArr =
        [t, step6_flag, last_g] ++
          s.arrs 4 ++ s.arrs 5 ++ arr6_out ++ s.arrs 7 ++ s.arrs 8 := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm2_w : m₂ < 2 ^ w := by omega
  have h3m2_w : 3 * m₂ < 2 ^ w := by omega
  have ht_le : t ≤ 2 * m₂ := hpar.2.1
  have ht_w : t < 2 ^ w := by omega
  have htn_w : t + n < 2 ^ w := by omega
  have h3m2_tn_w : 3 * m₂ + (t + n) < 2 ^ w := by omega
  have hout_w' : 3 + (3 * m₂ + (t + n)) < 2 ^ w := by omega
  have hflag_w : step6_flag < 2 ^ w := by omega
  have hg_w : last_g < 2 ^ w := by omega
  have hpar_len0 : 0 < (s.arrs 6).length := by rw [hpar.1]; omega
  -- 1. initAlg33OutCmd
  have hinit : ∃ s₁,
      Exec w initAlg33OutCmd s s₁ (26 + 3 * m₂ + t + n) ∧
      s₁.arrs outArr = [t, step6_flag, last_g] ++ List.replicate (3 * m₂ + t + n) 0 ∧
      s₁.arrs 6 = (s.arrs 6).set 0 0 ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 6 → s₁.arrs a = s.arrs a) ∧
      s₁.regs 12 = 3 ∧
      (∀ r < 11, s₁.regs r = s.regs r) := by
    let s_0 := s.writeArr 6 0 0
    have hex_0 : Exec w (.write 6 (.const 0) (.const 0)) s s_0 3 :=
      .write (by simp [Expr.eval, checkWord, h0_w])
        (by simp [Expr.eval, checkWord, h0_w])
        hpar_len0
    let s_a := s_0.setArr outArr (List.replicate (3 + (3 * m₂ + (t + n))) 0)
    have hex_a : Exec w (.alloc outArr (.op .add (.const 3)
        (.op .add (.op .mul (.const 3) (.reg 2)) (.op .add (.reg 4) (.reg 0)))))
        s_0 s_a (9 + (3 + (3 * m₂ + (t + n)))) :=
      .alloc (by
        simp [s_0, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hw3, hr2, hm2_w, h3m2_w, hr4, ht_w, hr0, hn_w, htn_w, h3m2_tn_w, hout_w'])
    let s_b := s_a.writeArr outArr 0 t
    have hex_b : Exec w (.write outArr (.const 0) (.reg 4)) s_a s_b 3 :=
      .write (by simp [Expr.eval, checkWord, h0_w])
        (by simp [s_a, s_0, Expr.eval, checkWord, hr4, ht_w])
        (by simp [s_a])
    let s_c := s_b.writeArr outArr 1 step6_flag
    have hex_c : Exec w (.write outArr (.const 1) (.reg 5)) s_b s_c 3 :=
      .write (by simp [Expr.eval, checkWord, hw])
        (by simp [s_b, s_a, s_0, Expr.eval, checkWord, hr5, hflag_w])
        (by simp [s_b, s_a]; omega)
    let s_d := s_c.writeArr outArr 2 last_g
    have hex_d : Exec w (.write outArr (.const 2) (.reg 6)) s_c s_d 3 :=
      .write (by simp [Expr.eval, checkWord, hw2])
        (by simp [s_c, s_b, s_a, s_0, Expr.eval, checkWord, hr6, hg_w])
        (by simp [s_c, s_b, s_a]; omega)
    let s₁ := s_d.setReg 12 3
    have hex_e : Exec w (.assign 12 (.const 3)) s_d s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw3])
    have ht_eq : 3 + ((9 + (3 + (3 * m₂ + (t + n)))) + (3 + (3 + (3 + 2)))) =
        26 + 3 * m₂ + t + n := by omega
    have hrep_eq : 3 * m₂ + (t + n) = 3 * m₂ + t + n := by omega
    have hout_eq : s₁.arrs outArr =
        [t, step6_flag, last_g] ++ List.replicate (3 * m₂ + t + n) 0 := by
      simp only [s₁, s_d, s_c, s_b, s_a, State.setReg_arrs, State.writeArr_arrs_self,
        State.setArr_arrs_self, hrep_eq]
      rw [Nat.add_comm 3 (3 * m₂ + t + n),
        List.replicate_succ, List.replicate_succ, List.replicate_succ]
      rfl
    exact ⟨s₁, ht_eq ▸ .seq hex_0 (.seq hex_a (.seq hex_b (.seq hex_c (.seq hex_d hex_e)))),
      hout_eq,
      by simp [s₁, s_d, s_c, s_b, s_a, s_0, show (6 : Arr) ≠ outArr by decide],
      fun a ha ha6 => by simp [s₁, s_d, s_c, s_b, s_a, s_0, ha, ha6],
      by simp [s₁],
      fun r hr11 => by
        dsimp [Reg] at hr11
        simp [s₁, s_d, s_c, s_b, s_a, s_0, State.setReg,
          show (r : Reg) ≠ 12 by dsimp [Reg]; omega]⟩
  rcases hinit with ⟨s₁, hex₁, hout₁, harr₁_6, harr₁, hr12_1, hreg₁⟩
  -- Word bounds on arrays 4..8 and `arr6_out := (s₁.arrs 6).take t`
  let arr6_out := (s₁.arrs 6).take t
  have harr6_len : arr6_out.length = t := by
    dsimp [arr6_out]
    rw [List.length_take, harr₁_6, List.length_set, hpar.1]
    omega
  have harr6_eq : ∀ z (hz : z < arr6_out.length), 0 < z → arr6_out[z]'hz = p z := by
    intro z hz hz_pos
    have hz_t : z < t := by omega
    dsimp [arr6_out]
    rw [List.getElem_take]
    simp only [harr₁_6]
    rw [List.getElem_set_ne (by omega : 0 ≠ z)]
    exact hpar.2.2.1 z hz_t
  have hw_arr4 : ∀ x ∈ s.arrs 4, x < 2 ^ w := by
    intro x hx; rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    have := hal.2.1 ⟨i, by rw [← hal.1]; exact hi⟩
    dsimp only at this; omega
  have hw_arr5 : ∀ x ∈ s.arrs 5, x < 2 ^ w := by
    intro x hx; rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    have h := htau.2 ⟨i, by rw [← htau.1]; exact hi⟩
    dsimp only at h
    have := (f_tau ⟨i, by rw [← htau.1]; exact hi⟩).2; omega
  have hw_arr6 : ∀ x ∈ arr6_out, x < 2 ^ w := by
    intro x hx; rcases List.mem_iff_getElem.mp hx with ⟨z, hz, rfl⟩
    have hz_lt : z < t := by omega
    by_cases hz_pos : 0 < z
    · rw [harr6_eq z hz hz_pos]
      have := hpar.2.2.2 z hz_pos hz_lt; omega
    · have hz0 : z = 0 := by omega
      subst hz0
      dsimp [arr6_out]
      rw [List.getElem_take]
      simp [harr₁_6, h0_w]
  have hw_arr7 : ∀ x ∈ s.arrs 7, x < 2 ^ w := by
    intro x hx; rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    have := hlast_al.2.1 ⟨i, by rw [← hlast_al.1]; exact hi⟩
    dsimp only at this; omega
  have hw_arr8 : ∀ x ∈ s.arrs 8, x < 2 ^ w := by
    intro x hx; rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    have := hlast_Z.2.1 ⟨i, by rw [← hlast_Z.1]; exact hi⟩
    dsimp only at this; omega
  -- 2. appendArrToOutProg 4 2
  let pre₁ : List ℕ := [t, step6_flag, last_g]
  rcases appendArrToOutProg_exec 4 2 (by decide) (by decide)
      pre₁ (s.arrs 4) hal.1 hw_arr4 hw
      (rem_out := 2 * m₂ + t + n) (by simp [pre₁]; omega) (s := s₁)
      (by rw [harr₁ 4 (by decide) (by decide), List.take_of_length_le (by rw [hal.1])])
      (by rw [hout₁, show 3 * m₂ + t + n = m₂ + (2 * m₂ + t + n) by omega])
      (by rw [hreg₁ 2 (by decide), hr2])
      hr12_1 with
    ⟨s₂, t₂, hex₂, ht₂, hout₂, hr12_2, harr₂, hreg₂⟩
  -- 3. appendArrToOutProg 5 2
  let pre₂ := pre₁ ++ s.arrs 4
  rcases appendArrToOutProg_exec 5 2 (by decide) (by decide)
      pre₂ (s.arrs 5) htau.1 hw_arr5 hw
      (rem_out := m₂ + t + n) (by simp [pre₂, pre₁, hal.1]; omega) (s := s₂)
      (by rw [harr₂ 5 (by decide), harr₁ 5 (by decide) (by decide),
            List.take_of_length_le (by rw [htau.1])])
      (by rw [hout₂, show 2 * m₂ + t + n = m₂ + (m₂ + t + n) by omega])
      (by rw [hreg₂ 2 (by decide), hreg₁ 2 (by decide), hr2])
      hr12_2 with
    ⟨s₃, t₃, hex₃, ht₃, hout₃, hr12_3, harr₃, hreg₃⟩
  -- 4. appendArrToOutProg 6 4
  let pre₃ := pre₂ ++ s.arrs 5
  rcases appendArrToOutProg_exec 6 4 (by decide) (by decide)
      pre₃ arr6_out harr6_len hw_arr6 hw
      (rem_out := m₂ + n) (by simp [pre₃, pre₂, pre₁, hal.1, htau.1]; omega) (s := s₃)
      (by rw [harr₃ 6 (by decide), harr₂ 6 (by decide)])
      (by rw [hout₃, show m₂ + t + n = t + (m₂ + n) by omega])
      (by rw [hreg₃ 4 (by decide), hreg₂ 4 (by decide), hreg₁ 4 (by decide), hr4])
      hr12_3 with
    ⟨s₄, t₄, hex₄, ht₄, hout₄, hr12_4, harr₄, hreg₄⟩
  -- 5. appendArrToOutProg 7 2
  let pre₄ := pre₃ ++ arr6_out
  rcases appendArrToOutProg_exec 7 2 (by decide) (by decide)
      pre₄ (s.arrs 7) hlast_al.1 hw_arr7 hw
      (rem_out := n) (by simp [pre₄, pre₃, pre₂, pre₁, hal.1, htau.1, harr6_len]; omega) (s := s₄)
      (by rw [harr₄ 7 (by decide), harr₃ 7 (by decide), harr₂ 7 (by decide),
            harr₁ 7 (by decide) (by decide), List.take_of_length_le (by rw [hlast_al.1])])
      hout₄
      (by rw [hreg₄ 2 (by decide), hreg₃ 2 (by decide), hreg₂ 2 (by decide),
            hreg₁ 2 (by decide), hr2])
      hr12_4 with
    ⟨s₅, t₅, hex₅, ht₅, hout₅, hr12_5, harr₅, hreg₅⟩
  -- 6. appendArrToOutProg 8 0
  let pre₅ := pre₄ ++ s.arrs 7
  rcases appendArrToOutProg_exec 8 0 (by decide) (by decide)
      pre₅ (s.arrs 8) hlast_Z.1 hw_arr8 hw
      (rem_out := 0)
      (by simp [pre₅, pre₄, pre₃, pre₂, pre₁, hal.1, htau.1, harr6_len, hlast_al.1]; omega)
      (s := s₅)
      (by rw [harr₅ 8 (by decide), harr₄ 8 (by decide), harr₃ 8 (by decide),
            harr₂ 8 (by decide), harr₁ 8 (by decide) (by decide),
            List.take_of_length_le (by rw [hlast_Z.1])])
      (by rw [Nat.add_zero]; exact hout₅)
      (by rw [hreg₅ 0 (by decide), hreg₄ 0 (by decide), hreg₃ 0 (by decide),
            hreg₂ 0 (by decide), hreg₁ 0 (by decide), hr0])
      hr12_5 with
    ⟨s₆, t₆, hex₆, ht₆, hout₆, _, _, _⟩
  refine ⟨s₆, (26 + 3 * m₂ + t + n) + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))), arr6_out,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, harr6_len, harr6_eq, ?_⟩
  simpa [pre₅, pre₄, pre₃, pre₂, pre₁, List.append_assoc] using hout₆

/-! #### Subpart 6.3: Output Decoder (`decAlg33Out`) and Top-Level Theorem (`gm13_algorithm_3_3`) -/

theorem graphOfEdgeList_take_eq_of_le {n : ℕ} {G : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList G edges) {m_H : ℕ}
    (hle : edges.length ≤ m_H) :
    graphOfEdgeList (edges.take m_H) (take_loopless_of_isSimpleEdgeList hedges m_H) = G := by
  ext u v
  rw [hedges.2.2 u v]
  unfold graphOfEdgeList edgeListAdj
  dsimp only
  simp only [List.take_of_length_le hle]

theorem drop_take_append (a b c : List ℕ) :
    ((a ++ b ++ c).drop a.length).take b.length = b := by
  rw [List.append_assoc, List.drop_left, List.take_left]

theorem drop_take_append_end (a b : List ℕ) :
    ((a ++ b).drop a.length).take b.length = b := by
  rw [List.drop_left, List.take_of_length_le (le_refl _)]

/-- Helper constructor building `Alg33Output x` from decoded header words and array slices. -/
def mkAlg33Out (ω : ℕ) (x : Alg33Input)
    (last_g : ℕ) (s_alive s_tau s_par s_last_al s_last_Z : List ℕ)
    (t : ℕ) (ht_pos : 0 < t) : Alg33Output x :=
  let edges₁ := edgeListOf x.H₁
  let m₂ := min edges₁.length (maxEdgesH2 ω x.n)
  let edges₂ := edges₁.take m₂
  let hloop₂ := take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf x.H₁) m₂
  let aliveSet : Finset (Fin edges₂.length) :=
    Finset.univ.filter (fun k => s_alive.getD k.1 0 == 1)
  let lastAliveSet : Finset (Fin edges₂.length) :=
    Finset.univ.filter (fun k => s_last_al.getD k.1 0 == 1)
  let Z_step6 : Finset (Fin x.n) :=
    Finset.univ.filter (fun u => s_last_Z.getD u.1 0 == 1)
  let f_tau : Fin edges₂.length → Fin t := fun k =>
    if h : s_tau.getD k.1 0 < t then ⟨s_tau.getD k.1 0, h⟩ else ⟨0, ht_pos⟩
  let p : ℕ → ℕ := fun z => s_par.getD z 0
  have hn_pos : 1 ≤ x.n := one_le_n_of_two_le_edges x.H₁ x.h_edges
  { G' := graphOfAlive edges₂ hloop₂ aliveSet
    t := t
    T := parentTree t p
    τ := tauOfArr edges₂ t ht_pos f_tau
    G_step6 := graphOfAlive edges₂ hloop₂ lastAliveSet
    g := if hg : last_g < edges₂.length then symEdgeAt edges₂ ⟨last_g, hg⟩
         else s(⟨0, hn_pos⟩, ⟨0, hn_pos⟩)
    Z := Z_step6 }

/-- Output decoder for Algorithm (3.3): reconstructs `Alg33Output x` from the flat `outArr` word
list produced by `writeAlg33OutProg`. -/
def decAlg33Out (ω : ℕ) (x : Alg33Input) (out : List ℕ) : Alg33Output x :=
  let m₂ := min (edgeListOf x.H₁).length (maxEdgesH2 ω x.n)
  let t := if 0 < out.getD 0 2 then out.getD 0 2 else 2
  mkAlg33Out ω x (out.getD 2 0)
    ((out.drop 3).take m₂)
    ((out.drop (3 + m₂)).take m₂)
    ((out.drop (3 + 2 * m₂)).take t)
    ((out.drop (3 + 2 * m₂ + t)).take m₂)
    ((out.drop (3 + 3 * m₂ + t)).take x.n)
    t (by dsimp [t]; split_ifs with h; exact h; decide)

theorem filter_getD_eq_of_isBitSet {m : ℕ} {S : Finset (Fin m)} {a : Arr} {s : State}
    (hS : IsBitSet S a s) :
    Finset.univ.filter (fun k : Fin m => (s.arrs a).getD k.1 0 == 1) = S := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, beq_iff_eq]
  have hk_len : k.1 < (s.arrs a).length := by rw [hS.1]; exact k.2
  rw [list_getD_eq_getElem _ _ _ hk_len]
  constructor
  · intro h1
    exact (hS.2.2 k).mp (by omega)
  · intro hk
    have hle := hS.2.1 k
    have hne := (hS.2.2 k).mpr hk
    omega

theorem isValidAlg33OutputCases_decAlg33Out {ω : ℕ} (hω : 2 ≤ ω) (x : Alg33Input)
    {t step6_flag last_g : ℕ} (ht_pos : 0 < t)
    {s : State} {arr6_out : List ℕ}
    (aliveSet lastAliveSet : Finset (Fin ((edgeListOf x.H₁).take
      (min (edgeListOf x.H₁).length (maxEdgesH2 ω x.n))).length))
    (Z_step6 : Finset (Fin x.n))
    (f_tau : Fin ((edgeListOf x.H₁).take
      (min (edgeListOf x.H₁).length (maxEdgesH2 ω x.n))).length → Fin t)
    (p : ℕ → ℕ)
    (hal : IsBitSet aliveSet 4 s)
    (htau : IsTauArr f_tau 5 s)
    (harr6_len : arr6_out.length = t)
    (harr6_eq : ∀ z (hz : z < arr6_out.length), 0 < z → arr6_out[z]'hz = p z)
    (hlast_al : IsBitSet lastAliveSet 7 s)
    (hlast_Z : IsBitSet Z_step6 8 s)
    (hpart : IsPartialBranchDecomp ω
      (graphOfAlive ((edgeListOf x.H₁).take (min (edgeListOf x.H₁).length (maxEdgesH2 ω x.n)))
        (take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf x.H₁)
          (min (edgeListOf x.H₁).length (maxEdgesH2 ω x.n))) aliveSet)
      (parentTree t p)
      (tauOfArr ((edgeListOf x.H₁).take (min (edgeListOf x.H₁).length (maxEdgesH2 ω x.n)))
        t ht_pos f_tau))
    (hcert : Step6CertInv ω x.H₁
      ((edgeListOf x.H₁).take (min (edgeListOf x.H₁).length (maxEdgesH2 ω x.n)))
      (take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf x.H₁)
        (min (edgeListOf x.H₁).length (maxEdgesH2 ω x.n)))
      aliveSet lastAliveSet Z_step6 step6_flag last_g)
    (hinj : ∀ i j, i.1 < j.1 → i ∈ aliveSet → j ∈ aliveSet → f_tau i ≠ f_tau j)
    {out : List ℕ}
    (hout : out = [t, step6_flag, last_g] ++
      s.arrs 4 ++ s.arrs 5 ++ arr6_out ++ s.arrs 7 ++ s.arrs 8) :
    IsValidAlg33OutputCases ω x (decAlg33Out ω x out) := by
  let edges₁ := edgeListOf x.H₁
  have hedges₁ : IsSimpleEdgeList x.H₁ edges₁ := isSimpleEdgeList_edgeListOf x.H₁
  let m₂ := min edges₁.length (maxEdgesH2 ω x.n)
  let edges₂ := edges₁.take m₂
  let hloop₂ := take_loopless_of_isSimpleEdgeList hedges₁ m₂
  have hedges₂ : IsSimpleEdgeList (graphOfEdgeList edges₂ hloop₂) edges₂ :=
    isSimpleEdgeList_take hedges₁ m₂
  have hm₂_le : m₂ ≤ edges₁.length := Nat.min_le_left _ _
  have hlen_e2 : edges₂.length = m₂ := List.length_take_of_le hm₂_le
  have h4_len : (s.arrs 4).length = m₂ := hal.1.trans hlen_e2
  have h5_len : (s.arrs 5).length = m₂ := htau.1.trans hlen_e2
  have h7_len : (s.arrs 7).length = m₂ := hlast_al.1.trans hlen_e2
  have h8_len : (s.arrs 8).length = x.n := hlast_Z.1
  -- Unpack slices of `out`
  have ht_get : out.getD 0 2 = t := by simp [hout]
  have htd_eq : (if 0 < out.getD 0 2 then out.getD 0 2 else 2) = t := by
    rw [ht_get]
    simp [ht_pos]
  have hg_get : out.getD 2 0 = last_g := by simp [hout]
  have hs4 : (out.drop 3).take m₂ = s.arrs 4 := by
    have hpre : ([t, step6_flag, last_g] : List ℕ).length = 3 := rfl
    have h := drop_take_append [t, step6_flag, last_g] (s.arrs 4)
      (s.arrs 5 ++ arr6_out ++ s.arrs 7 ++ s.arrs 8)
    rw [hpre, h4_len] at h
    simpa [hout, List.append_assoc] using h
  have hs5 : (out.drop (3 + m₂)).take m₂ = s.arrs 5 := by
    have hpre : ([t, step6_flag, last_g] ++ s.arrs 4).length = 3 + m₂ := by
      simp [h4_len]; omega
    have h := drop_take_append ([t, step6_flag, last_g] ++ s.arrs 4) (s.arrs 5)
      (arr6_out ++ s.arrs 7 ++ s.arrs 8)
    rw [hpre, h5_len] at h
    simpa [hout, List.append_assoc] using h
  have hs6 : (out.drop (3 + 2 * m₂)).take t = arr6_out := by
    have hpre : ([t, step6_flag, last_g] ++ s.arrs 4 ++ s.arrs 5).length = 3 + 2 * m₂ := by
      simp [h4_len, h5_len]; omega
    have h := drop_take_append ([t, step6_flag, last_g] ++ s.arrs 4 ++ s.arrs 5) arr6_out
      (s.arrs 7 ++ s.arrs 8)
    rw [hpre, harr6_len] at h
    simpa [hout, List.append_assoc] using h
  have hs7 : (out.drop (3 + 2 * m₂ + t)).take m₂ = s.arrs 7 := by
    have hpre : ([t, step6_flag, last_g] ++ s.arrs 4 ++ s.arrs 5 ++ arr6_out).length =
        3 + 2 * m₂ + t := by
      simp [h4_len, h5_len, harr6_len]; omega
    have h := drop_take_append
      ([t, step6_flag, last_g] ++ s.arrs 4 ++ s.arrs 5 ++ arr6_out) (s.arrs 7) (s.arrs 8)
    rw [hpre, h7_len] at h
    simpa [hout, List.append_assoc] using h
  have hs8 : (out.drop (3 + 3 * m₂ + t)).take x.n = s.arrs 8 := by
    have hpre : ([t, step6_flag, last_g] ++ s.arrs 4 ++ s.arrs 5 ++ arr6_out ++ s.arrs 7).length =
        3 + 3 * m₂ + t := by
      simp [h4_len, h5_len, harr6_len, h7_len]; omega
    have h := drop_take_append_end
      ([t, step6_flag, last_g] ++ s.arrs 4 ++ s.arrs 5 ++ arr6_out ++ s.arrs 7) (s.arrs 8)
    rw [hpre, h8_len] at h
    simpa [hout, List.append_assoc] using h
  have hdec_eq : decAlg33Out ω x out =
      mkAlg33Out ω x last_g (s.arrs 4) (s.arrs 5) arr6_out (s.arrs 7) (s.arrs 8)
        t ht_pos := by
    unfold decAlg33Out
    dsimp only
    generalize_proofs ht_dec
    revert ht_dec
    rw [htd_eq, hg_get, hs4, hs5, hs6, hs7, hs8]
    intro _
    rfl
  -- Simplify the decoded fields of `mkAlg33Out`
  have hal_eq : Finset.univ.filter (fun k : Fin edges₂.length => (s.arrs 4).getD k.1 0 == 1) =
      aliveSet := filter_getD_eq_of_isBitSet hal
  have hlast_al_eq : Finset.univ.filter (fun k : Fin edges₂.length => (s.arrs 7).getD k.1 0 == 1) =
      lastAliveSet := filter_getD_eq_of_isBitSet hlast_al
  have hlast_Z_eq : Finset.univ.filter (fun u : Fin x.n => (s.arrs 8).getD u.1 0 == 1) =
      Z_step6 := filter_getD_eq_of_isBitSet hlast_Z
  have hftau_eq : (fun k : Fin edges₂.length =>
      if h : (s.arrs 5).getD k.1 0 < t then ⟨(s.arrs 5).getD k.1 0, h⟩ else ⟨0, ht_pos⟩) =
      f_tau := by
    funext k
    have hk_len : k.1 < (s.arrs 5).length := by rw [htau.1]; exact k.2
    have hget : (s.arrs 5).getD k.1 0 = (f_tau k).1 := by
      rw [list_getD_eq_getElem _ _ _ hk_len]
      exact htau.2 k
    have hlt : (s.arrs 5).getD k.1 0 < t := by rw [hget]; exact (f_tau k).2
    simp only [hlt, ↓reduceDIte]
    exact Fin.ext hget
  have htree_eq : parentTree t (fun z => arr6_out.getD z 0) = parentTree t p := by
    apply parentTree_congr
    intro z hz_pos hz_lt
    have hz_len : z < arr6_out.length := by rw [harr6_len]; exact hz_lt
    rw [list_getD_eq_getElem _ _ _ hz_len]
    exact harr6_eq z hz_len hz_pos
  have hmk_eq :
      mkAlg33Out ω x last_g (s.arrs 4) (s.arrs 5) arr6_out (s.arrs 7) (s.arrs 8) t ht_pos =
      { G' := graphOfAlive edges₂ hloop₂ aliveSet
        t := t
        T := parentTree t p
        τ := tauOfArr edges₂ t ht_pos f_tau
        G_step6 := graphOfAlive edges₂ hloop₂ lastAliveSet
        g := if hg : last_g < edges₂.length then symEdgeAt edges₂ ⟨last_g, hg⟩
             else s(⟨0, one_le_n_of_two_le_edges x.H₁ x.h_edges⟩,
                    ⟨0, one_le_n_of_two_le_edges x.H₁ x.h_edges⟩)
        Z := Z_step6 } := by
    unfold mkAlg33Out
    dsimp only
    rw [hal_eq, hlast_al_eq, hlast_Z_eq, hftau_eq, htree_eq]
  rw [hdec_eq, hmk_eq]
  unfold IsValidAlg33OutputCases
  dsimp only
  -- 1. Branch-decomposition of width ≤ 3ω
  have hbd : IsBranchDecompOfWidthLe (3 * ω)
      (graphOfAlive edges₂ hloop₂ aliveSet)
      (parentTree t p)
      (tauOfArr edges₂ t ht_pos f_tau) := by
    classical
    rcases hpart with ⟨htree, hmaps, hsurj, hord⟩
    refine ⟨htree, ⟨fun e he => hmaps e he, ?_, fun v hv => hsurj v hv⟩, hord⟩
    intro e₁ he₁ e₂ he₂ heq
    rw [Finset.mem_coe] at he₁ he₂
    rw [mem_edgeFinset_graphOfAlive_iff hedges₂] at he₁ he₂
    rcases he₁ with ⟨i, hi_al, rfl⟩
    rcases he₂ with ⟨j, hj_al, rfl⟩
    rw [tauOfArr_symEdgeAt hedges₂, tauOfArr_symEdgeAt hedges₂] at heq
    by_contra hne
    have hij_ne : i ≠ j := fun h => hne (congrArg (symEdgeAt edges₂) h)
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij_ne) with hlt | hgt
    · exact hinj i j hlt hi_al hj_al heq
    · exact hinj j i hgt hj_al hi_al heq.symm
  -- 2. Subgraph of H₁
  have hsub_H1 : graphOfAlive edges₂ hloop₂ aliveSet ≤ x.H₁ :=
    (graphOfAlive_le_graphOfEdgeList edges₂ hloop₂ aliveSet).trans
      (graphOfEdgeList_take_le hedges₁ m₂)
  refine ⟨by convert hbd, hsub_H1, ?_⟩
  -- 3. Three-case disjunction from `hcert`
  rcases hcert with ⟨_, rfl, rfl⟩ |
    ⟨_, hg_lt, hG6_le, hg_mem, hZ_card, hal_erase, hno_sep⟩
  · -- Step (6) never occurred: `aliveSet = Finset.univ`
    rw [graphOfAlive_univ]
    by_cases hle : edges₁.length ≤ maxEdgesH2 ω x.n
    · -- Case 3a: `G' = H₁`
      left
      have hm₂_eq : m₂ = edges₁.length := Nat.min_eq_left hle
      exact graphOfEdgeList_take_eq_of_le hedges₁ (by omega)
    · -- Case 3b: `G' = H₂ ≠ H₁` with `|E(H₂)| = maxEdgesH2 ω x.n`
      right; left
      have hm₂_eq : m₂ = maxEdgesH2 ω x.n := Nat.min_eq_right (by omega)
      have hcard_H2 : (graphOfEdgeList edges₂ hloop₂).edgeFinset.card = maxEdgesH2 ω x.n := by
        have h1 := card_edgeFinset_of_isSimpleEdgeList (graphOfEdgeList edges₂ hloop₂) hedges₂
        omega
      have hcard_H1 : x.H₁.edgeFinset.card = edges₁.length :=
        length_edgeListOf_eq_card_edgeFinset x.H₁ |>.symm
      have hne_H1 : graphOfEdgeList edges₂ hloop₂ ≠ x.H₁ := by
        intro heq
        have hcards : (graphOfEdgeList edges₂ hloop₂).edgeFinset.card = x.H₁.edgeFinset.card := by
          congr 1
          ext e
          simp [heq]
        omega
      refine ⟨hne_H1, ?_, ?_⟩
      · convert maxEdgesH2_le_rat (by omega : 1 ≤ ω) using 2
        rw [← hcard_H2]
        congr 1
        ext e
        simp [SimpleGraph.mem_edgeFinset]
      · convert maxEdgesH2_gt_rat (by omega : 1 ≤ ω) using 2
        rw [← hcard_H2]
        congr 1
        ext e
        simp [SimpleGraph.mem_edgeFinset]
  · -- Case 3c: Step (6) occurred
    right; right
    have hg_eq : (if hg : last_g < edges₂.length then symEdgeAt edges₂ ⟨last_g, hg⟩
        else s(⟨0, one_le_n_of_two_le_edges x.H₁ x.h_edges⟩,
               ⟨0, one_le_n_of_two_le_edges x.H₁ x.h_edges⟩)) =
        symEdgeAt edges₂ ⟨last_g, hg_lt⟩ := by
      split_ifs with hg_c
      · rfl
      · exact False.elim (hg_c hg_lt)
    rw [hg_eq]
    have herase_eq :
        graphOfAlive edges₂ hloop₂ aliveSet =
          (graphOfAlive edges₂ hloop₂ lastAliveSet).deleteEdges {symEdgeAt edges₂ ⟨last_g, hg_lt⟩} := by
      rw [hal_erase]
      exact graphOfAlive_erase_eq_deleteEdges hedges₂ lastAliveSet ⟨last_g, hg_lt⟩
    refine ⟨hG6_le, by convert hg_mem, hZ_card, ?_, herase_eq, hno_sep⟩
    rw [herase_eq]

/-- Complete Word-RAM program for Algorithm (3.3) of Graph Minors XIII:
1. `initAlg33Prog ω`: parses `n` and `m₁`, constructs the subgraph `H₂` of at most
   `maxEdgesH2 ω n` edges, and initializes `(G₁, T₁, τ₁)`.
2. `alg33LoopProg ω`: runs the recursion (1)–(6) using `mengerLoopRegProg` in Step (4).
3. `writeAlg33OutProg`: serializes the final branch-decomposition and Step (6) certificate to
   `outArr`. -/
def alg33Prog (ω : ℕ) : Cmd :=
  .seq (initAlg33Prog ω)
    (.seq (alg33LoopProg ω)
      writeAlg33OutProg)

/--Three-case certificate lemma for `alg33Prog ω` (`IsValidAlg33OutputCases`). -/
theorem algorithm_3_3_cases (ω : ℕ) (hω : 2 ≤ ω) :
    ComputesArrRelInTime alg33Size encAlg33In
      (fun x out => IsValidAlg33OutputCases ω x (decAlg33Out ω x out))
      (alg33Prog ω) (fun v => (v + 1) ^ 2) := by
  let B_fac := 3 * ω
  let K_iter := iterStepMax ω 1 1 + 50
  let C_step := 500 * B_fac + 10 * B_fac * K_iter * B_fac + 500
  let c_word := 16 * ω + 4
  have hK_pos : 1 ≤ K_iter := by dsimp [K_iter, iterStepMax]; omega
  refine ⟨C_step, c_word, by dsimp [C_step, B_fac]; omega, by dsimp [c_word]; omega,
    fun x s₀ hs₀ => ?_⟩
  let edges₁ := edgeListOf x.H₁
  have hedges₁ : IsSimpleEdgeList x.H₁ edges₁ := isSimpleEdgeList_edgeListOf x.H₁
  have hm₁_eq : edges₁.length = x.H₁.edgeFinset.card :=
    length_edgeListOf_eq_card_edgeFinset x.H₁
  have hm₁_ge2 : 2 ≤ edges₁.length := by rw [hm₁_eq]; exact x.h_edges
  have hn_pos : 1 ≤ x.n := one_le_n_of_two_le_edges x.H₁ x.h_edges
  let m₂ := min edges₁.length (maxEdgesH2 ω x.n)
  let edges₂ := edges₁.take m₂
  let hloop₂ := take_loopless_of_isSimpleEdgeList hedges₁ m₂
  have hedges₂ : IsSimpleEdgeList (graphOfEdgeList edges₂ hloop₂) edges₂ :=
    isSimpleEdgeList_take hedges₁ m₂
  have hm₂_ge2 : 2 ≤ m₂ := Nat.le_min.mpr ⟨hm₁_ge2, two_le_maxEdgesH2 hω hn_pos⟩
  have hm₂_le1 : m₂ ≤ edges₁.length := Nat.min_le_left _ _
  have hm₂_leB : m₂ ≤ maxEdgesH2 ω x.n := Nat.min_le_right _ _
  have hlen_e2 : edges₂.length = m₂ := List.length_take_of_le hm₂_le1
  have hm₂_le_lin : m₂ ≤ 3 * ω * x.n := by
    have hmax : maxEdgesH2 ω x.n ≤ 3 * ω * x.n := by
      unfold maxEdgesH2
      have h1 : (3 * ω - 2) * x.n = 3 * ω * x.n - 2 * x.n := Nat.sub_mul (3 * ω) 2 x.n
      have h2 : 2 * x.n ≤ 3 * ω * x.n := Nat.mul_le_mul_right x.n (by omega)
      omega
    exact hm₂_leB.trans hmax
  -- Word-size bounds from `(x.n + 2) ^ c_word < 2 ^ w`
  let w := wordSize c_word (alg33Size x)
  have hpow_w : (x.n + 2) ^ c_word < 2 ^ w :=
    pow_lt_two_pow_wordSize (c := c_word) (by dsimp [c_word]; omega) (alg33Size x)
  have hpow3_le : (x.n + 2) ^ 3 ≤ (x.n + 2) ^ c_word :=
    Nat.pow_le_pow_right (by omega) (by dsimp [c_word]; omega)
  have hpow3_expand : 2 + 2 * (x.n * x.n) < (x.n + 2) ^ 3 := by
    have hcube : (x.n + 2) ^ 3 = (x.n + 2) * ((x.n + 2) * (x.n + 2)) := by
      rw [show (3 : ℕ) = 2 + 1 by rfl, Nat.pow_succ, Nat.pow_two, Nat.mul_comm]
    have hge3 : 3 * ((x.n + 2) * (x.n + 2)) ≤ (x.n + 2) * ((x.n + 2) * (x.n + 2)) :=
      Nat.mul_le_mul_right _ (by omega : 3 ≤ x.n + 2)
    have hsq : x.n * x.n + 4 ≤ (x.n + 2) * (x.n + 2) := by
      rw [Nat.add_mul, Nat.mul_add]
      omega
    omega
  have hm₁_le_sq : edges₁.length ≤ x.n * x.n := length_edgeListOf_le_sq x.H₁
  have hm1_w : 2 + 2 * edges₁.length < 2 ^ w := by omega
  have hpow_lin : (16 * ω + 3) * (x.n + 2) < 2 ^ w := by
    have h1 : 16 * ω + 3 ≤ 2 ^ (16 * ω + 3) := by
      have := Nat.lt_two_pow_self (n := 16 * ω + 3)
      omega
    have h2 : 2 ^ (16 * ω + 3) ≤ (x.n + 2) ^ (16 * ω + 3) :=
      Nat.pow_le_pow_left (by omega : 2 ≤ x.n + 2) (16 * ω + 3)
    have h3 : (x.n + 2) ^ (16 * ω + 3) * (x.n + 2) = (x.n + 2) ^ c_word := by
      dsimp [c_word]
      rw [← Nat.pow_succ]
    have h4 : (16 * ω + 3) * (x.n + 2) ≤ (x.n + 2) ^ (16 * ω + 3) * (x.n + 2) :=
      Nat.mul_le_mul_right (x.n + 2) (h1.trans h2)
    omega
  have hlin_expand : (16 * ω + 3) * (x.n + 2) = 16 * (ω * x.n) + 32 * ω + 3 * x.n + 6 := by
    rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.mul_assoc 16 ω x.n]
    omega
  have hm₂_le_lin' : m₂ ≤ 3 * (ω * x.n) := by
    rwa [Nat.mul_assoc] at hm₂_le_lin
  have hB_le_lin : (3 * ω - 2) * x.n ≤ 3 * (ω * x.n) := by
    have := Nat.mul_le_mul_right x.n (by omega : 3 * ω - 2 ≤ 3 * ω)
    rwa [Nat.mul_assoc] at this
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have h2n_w : 2 * x.n < 2 ^ w := by omega
  have hB_w : (3 * ω - 2) * x.n + 2 < 2 ^ w := by omega
  have h2m2_w : 2 + 2 * edges₂.length < 2 ^ w := by omega
  have h3w_w : 3 * ω < 2 ^ w := by omega
  -- Phase 1: `initAlg33Prog ω`
  have hin₀ : s₀.arrs inArr = [x.n, edges₁.length] ++ flatEdges edges₁ := hs₀
  rcases initAlg33Prog_exec hω x.H₁ edges₁ hedges₁ hm₁_ge2 hn_pos
      hw2 hn_w hm1_w hB_w hin₀ with
    ⟨s₁, t₁, hex₁, ht₁, hr0_1, _, hr2_1, hr3_1, hr4_1, hr5_1, hr6_1,
      hend₁, hal₁, htau₁, hpar₁, hlast_al₁, hlast_Z₁, hpart₁⟩
  -- Phase 2a: initial `findDupLeafProg`
  have hw : 1 < 2 ^ w := by omega
  have hm₂_w : edges₂.length < 2 ^ w := by omega
  rcases findDupLeafProg_exec (Finset.univ : Finset (Fin edges₂.length))
      (initFTau edges₂.length) hw hm₂_w hw2 hal₁ htau₁
      (by rw [hr2_1, hlen_e2]) hr4_1 with
    ⟨s₂, t₂, hex₂, ht₂, hr7_inv₂, harr₂, hreg₂⟩
  -- Phase 2b: `while` loop (`alg33While_exec` with `k_rem := m₂ - 1`)
  have hG2_le : graphOfEdgeList edges₂ hloop₂ ≤ x.H₁ :=
    graphOfEdgeList_take_le hedges₁ m₂
  have hcert_init : Step6CertInv ω x.H₁ edges₂ hloop₂ Finset.univ ∅ ∅ 0 0 :=
    Or.inl ⟨rfl, rfl, rfl⟩
  have hleaves_init : 2 * (treeLeaves (parentTree 2 (fun _ => 0))).card = 2 + 2 := by
    rw [treeLeaves_parentTree_two]
    rfl
  have hpot_init : 2 * (Finset.univ : Finset (Fin edges₂.length)).card ≤ 2 + 2 * (m₂ - 1) := by
    rw [Finset.card_univ, Fintype.card_fin, hlen_e2]
    omega
  have hpar₁' : IsParentArr edges₂.length 2 (fun _ => 0) 6 s₁ := by
    rwa [hlen_e2]
  rcases alg33While_exec (by omega : 1 ≤ ω) hedges₂ hG2_le hw2 h2n_w h2m2_w h3w_w (m₂ - 1)
      (by decide : 0 < 2) Finset.univ ∅ ∅ 0 0 (initFTau edges₂.length) (fun _ => 0)
      hpart₁ hcert_init hleaves_init hpot_init
      (s := s₂)
      (hend₁.of_arrs_eq (harr₂ 2 (by decide)) (harr₂ 3 (by decide)))
      (hal₁.of_arr_eq (harr₂ 4 (by decide)))
      (htau₁.of_arr_eq (harr₂ 5 (by decide)))
      (hpar₁'.of_arr_eq (harr₂ 6 (by decide)))
      (hlast_al₁.of_arr_eq (harr₂ 7 (by decide)))
      (hlast_Z₁.of_arr_eq (harr₂ 8 (by decide)))
      (by rw [hreg₂ 0 (by decide) (by decide) (by decide) (by decide) (by decide), hr0_1])
      (by rw [hreg₂ 2 (by decide) (by decide) (by decide) (by decide) (by decide), hr2_1, hlen_e2])
      (by rw [hreg₂ 3 (by decide) (by decide) (by decide) (by decide) (by decide), hr3_1, hlen_e2])
      (by rw [hreg₂ 4 (by decide) (by decide) (by decide) (by decide) (by decide), hr4_1])
      (by rw [hreg₂ 5 (by decide) (by decide) (by decide) (by decide) (by decide), hr5_1])
      (by rw [hreg₂ 6 (by decide) (by decide) (by decide) (by decide) (by decide), hr6_1])
      hr7_inv₂ with
    ⟨s₃, t₃, t', ht'_pos, aliveSet', lastAliveSet', Z_step6', step6_flag', last_g',
      f_tau', p', hex₃, ht₃, _, hal₃, htau₃, hpar₃, hlast_al₃, hlast_Z₃,
      hpart₃, hcert₃, _, hinj₃, hr0_3, hr2_3, _, hr4_3, hr5_3, hr6_3⟩
  -- Phase 3: `writeAlg33OutProg`
  have ht'_le : t' ≤ 2 * edges₂.length := hpar₃.2.1
  have hout_w : 3 + 3 * edges₂.length + t' + x.n < 2 ^ w := by omega
  have hflag_le : step6_flag' ≤ 1 := by
    rcases hcert₃ with ⟨rfl, _, _⟩ | ⟨rfl, _⟩ <;> omega
  have hg_le : last_g' ≤ edges₂.length := by
    rcases hcert₃ with ⟨_, _, rfl⟩ | ⟨_, hg_lt, _⟩ <;> omega
  rcases writeAlg33OutProg_exec ht'_pos aliveSet' lastAliveSet' Z_step6' f_tau' p'
      hw3 hout_w hflag_le hg_le hal₃ htau₃ hpar₃ hlast_al₃ hlast_Z₃
      hr0_3 hr2_3 hr4_3 hr5_3 hr6_3 with
    ⟨s₄, t₄, arr6_out, hex₄, ht₄, harr6_len, harr6_eq, hout₄⟩
  -- Output validity
  have hvalid : IsValidAlg33OutputCases ω x (decAlg33Out ω x (s₄.arrs outArr)) :=
    isValidAlg33OutputCases_decAlg33Out hω x ht'_pos aliveSet' lastAliveSet' Z_step6' f_tau' p'
      hal₃ htau₃ harr6_len harr6_eq hlast_al₃ hlast_Z₃ hpart₃ hcert₃ hinj₃ hout₄
  -- Quadratic running time bound `t₁ + ((t₂ + t₃) + t₄) ≤ C_step * (x.n + 1) ^ 2`
  have htime : t₁ + ((t₂ + t₃) + t₄) ≤ C_step * (alg33Size x + 1) ^ 2 := by
    change t₁ + ((t₂ + t₃) + t₄) ≤ C_step * (x.n + 1) ^ 2
    rw [hlen_e2] at ht₂ ht₃ ht₄
    let S := (x.n + 1) ^ 2
    have hS_eq : S = (x.n + 1) * (x.n + 1) := Nat.pow_two (x.n + 1)
    have hS_expand : S = x.n * x.n + 2 * x.n + 1 := by
      rw [hS_eq, Nat.add_mul, Nat.mul_add]
      omega
    have h1_S : 1 ≤ S := by omega
    have hn_S : x.n ≤ S := by omega
    have hm₂_B : m₂ ≤ B_fac * x.n := hm₂_le_lin
    have hm₂_BS : m₂ ≤ B_fac * S :=
      hm₂_B.trans (Nat.mul_le_mul_left B_fac hn_S)
    have hB_pos : 1 ≤ B_fac := by dsimp [B_fac]; omega
    have h1_BS : 1 ≤ B_fac * S := by
      calc 1 = 1 * 1 := rfl
        _ ≤ B_fac * S := Nat.mul_le_mul hB_pos h1_S
    have hiter_le : iterStepMax ω x.n m₂ + 30 * m₂ + 12 ≤ K_iter * (B_fac * (x.n + 1)) := by
      have hn_X : x.n ≤ B_fac * (x.n + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        have : 1 * x.n ≤ B_fac * x.n := Nat.mul_le_mul_right x.n hB_pos
        omega
      have hm_X : m₂ ≤ B_fac * (x.n + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have h1_X : 1 ≤ B_fac * (x.n + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      exact iterStepMax_le_mul ω x.n m₂ (B_fac * (x.n + 1)) hn_X hm_X h1_X
    have hloop_le : (m₂ - 1) * (iterStepMax ω x.n m₂ + 30 * m₂ + 12) ≤
        B_fac * K_iter * (B_fac * S) := by
      have hm₂_le' : m₂ - 1 ≤ B_fac * (x.n + 1) := by
        rw [Nat.mul_add]
        omega
      have hmul := Nat.mul_le_mul hm₂_le' hiter_le
      have hrhs : (B_fac * (x.n + 1)) * (K_iter * (B_fac * (x.n + 1))) =
          B_fac * K_iter * (B_fac * S) := by
        dsimp [S]
        rw [Nat.pow_two]
        ac_rfl
      omega
    have hB_ge6 : 6 ≤ B_fac := by dsimp [B_fac]; omega
    have hBS_le_BB : B_fac * S ≤ B_fac * (B_fac * S) := by
      calc B_fac * S = 1 * (B_fac * S) := (Nat.one_mul _).symm
        _ ≤ B_fac * (B_fac * S) := Nat.mul_le_mul_right _ hB_pos
    have hK_le : B_fac * (B_fac * S) ≤ B_fac * K_iter * (B_fac * S) := by
      have : B_fac ≤ B_fac * K_iter := by
        calc B_fac = B_fac * 1 := (Nat.mul_one _).symm
          _ ≤ B_fac * K_iter := Nat.mul_le_mul_left B_fac hK_pos
      exact Nat.mul_le_mul_right (B_fac * S) this
    have hC_expand : C_step * S =
        500 * (B_fac * S) + 10 * (B_fac * K_iter * (B_fac * S)) + 500 * S := by
      dsimp [C_step]
      rw [Nat.add_mul, Nat.add_mul]
      ac_rfl
    change t₁ + ((t₂ + t₃) + t₄) ≤ C_step * S
    omega
  exact ⟨s₄, t₁ + ((t₂ + t₃) + t₄), .seq hex₁ (.seq (.seq hex₂ hex₃) hex₄), htime, hvalid⟩

/-- **Graph Minors XIII, (3.3) Algorithm** (pages 72–75):
"(3.3) Algorithm.
*Input:* A graph $G$ with $|E(G)| \ge 2$.
*Output:* A subgraph $G'$ of $G$ and a branch-decomposition of $G'$ of width $\le 3\omega$, such that either $G' = G$ or $G'$ has branch-width $\ge \omega$.
*Running time:* $O(v^2 + \varepsilon)$."

For every fixed integer `ω ≥ 2`, `alg33Prog ω` computes in `O(v²)` time on the Word RAM a valid
output `out` satisfying `IsValidAlg33Output ω x (decAlg33Out ω x out)`:
- `(decAlg33Out ω x out).G' ≤ x.H₁`;
- `IsBranchDecompOfWidthLe (3 * ω) (decAlg33Out ω x out).G' (decAlg33Out ω x out).T (decAlg33Out ω x out).τ`;
- `(decAlg33Out ω x out).G' = x.H₁ ∨ ¬ GM13.GraphBranchWidthLE (decAlg33Out ω x out).G'.toGMGraph (ω - 1)`. -/
theorem gm13_algorithm_3_3 (ω : ℕ) (hω : 2 ≤ ω) :
    ComputesArrRelInTime alg33Size encAlg33In
      (fun x out => IsValidAlg33Output ω x (decAlg33Out ω x out))
      (alg33Prog ω) (fun v => (v + 1) ^ 2) := by
  rcases algorithm_3_3_cases ω hω with ⟨C_step, c_word, hC, hc, hexec⟩
  refine ⟨C_step, c_word, hC, hc, fun x s₀ hs₀ => ?_⟩
  rcases hexec x s₀ hs₀ with ⟨s', t, hex, htime, hcases⟩
  exact ⟨s', t, hex, htime, hcases.to_isValidAlg33Output hω⟩

end GraphMinor.Compute
