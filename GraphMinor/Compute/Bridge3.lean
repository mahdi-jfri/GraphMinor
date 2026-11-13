module

public import GraphMinor.GM13.Section3
public import GraphMinor.Compute.Bridge13
public import GraphMinor.Compute.BranchDecomp
public import GraphMinor.Compute.Algorithm41Comb
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Bridge for GM XIII Section 3 and 4 Branch-Decompositions and High Branch-Width

This file bridges the algorithmic branch-decomposition representations in `GraphMinor.Compute`
(`IsBranchDecompOfWidthLe`, `IsDigraphBranchDecompOfWidthLe`, `IsMultiBranchDecompOfWidthLe`,
`IsValidBranchDecompCode`) with the mathematical branch-decomposition definitions and theorems of
Graph Minors XIII (`GM13.IsGraphBranchDecomposition`, `GM13.graphBranchDecompWidth`,
`GM13.GraphBranchWidthLE`, `GM13.theorem_3_1_proof`, `GM13.theorem_3_2_proof`,
`GM13.algorithm_3_3_step_6_deleteEdge`):

1. **Goal 1 (Two-way branch-decomposition bridge):**
   - Finite tree rooting (`exists_iso_parentTree_of_isTree_card`): every finite tree `T : SimpleGraph ι`
     on `t = Fintype.card ι > 0` vertices is isomorphic (`SimpleGraph.Iso`) to `parentTree t p` for
     some parent map `p : ℕ → ℕ` with `p 0 = 0` and `p z < z` for `0 < z < t`.
   - Simple graphs (`SimpleGraph.toGMGraph`): equivalence between `IsBranchDecompOfWidthLe B G T τ`
     and `GM13.IsGraphBranchDecomposition G.toGMGraph T τ ∧ GM13.graphBranchDecompWidth G.toGMGraph T τ ≤ B`,
     and between `GM13.GraphBranchWidthLE G.toGMGraph B` and existence of `IsBranchDecompOfWidthLe B G (parentTree t p) τ`.
   - Digraphs and multigraphs (`ComputeDigraph.toGMDigraph.toGraph`, `MultiDigraph.toGMDigraph.toGraph`):
     both directions between `IsValidBranchDecompCode B G bdCode` (and `IsMultiBranchDecompOfWidthLe`)
     and `GM13.IsGraphBranchDecomposition` / `GM13.graphBranchDecompWidth ≤ B` / `GM13.GraphBranchWidthLE`.
2. **Goal 2 (High branch-width in Algorithm (3.3)):**
   - Proves `¬ GM13.GraphBranchWidthLE G'.toGMGraph (ω - 1)` (for simple graphs) and
     `¬ GM13.GraphBranchWidthLE G'.toGMDigraph.toGraph (ω - 1)` (for multigraphs) from the two
     cases of Algorithm (3.3) (`|E(G')| > ((3/2)ω - 1)|V(G)|` and the Step (6) certificate
     `(G_step6, g, Z)` with `G' = G_step6 \ {g}`) using `GM13.theorem_3_2_proof`, `GM13.theorem_3_1_proof`, and
     `GM13.algorithm_3_3_step_6_deleteEdge` (together with leaf-splitting for `ω = 2`).
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open scoped BigOperators
open GraphMinor GraphMinor.GM10 GraphMinor.GM13

/-! ### Section 1: Tree Size Bound, Multigraph Edge Enumeration, and `IsValidBranchDecompCode` -/

/-- In any cubic/leaf tree `parentTree t p` whose leaves are in bijection with `Fin G.numEdges`,
the degree-sum formula implies `t + 2 = 2 * G.numEdges`, and hence `t ≤ 2 * G.numEdges`. -/
theorem t_le_two_mul_numEdges_of_branchDecomp {ω t : ℕ} {G : ComputeDigraph}
    {p : ℕ → ℕ} {τ : Fin G.numEdges → Fin t}
    (ht : 0 < t) (hp : ∀ z, 0 < z → z < t → p z < z)
    (hbd : IsDigraphBranchDecompOfWidthLe ω G (parentTree t p) τ) :
    t ≤ 2 * G.numEdges := by
  let T := parentTree t p
  have hleaves_card : (treeLeaves T).card = G.numEdges := by
    rw [← Fintype.card_fin G.numEdges, ← Finset.card_univ]
    symm
    refine Finset.card_bij (fun (e : Fin G.numEdges) _ => τ e) ?_ ?_ ?_
    · intro e _
      exact hbd.2.1.1 (Set.mem_univ e)
    · intro e₁ _ e₂ _ heq
      exact hbd.2.1.2.1 (Set.mem_univ e₁) (Set.mem_univ e₂) heq
    · intro v hv
      rcases hbd.2.1.2.2 hv with ⟨e, _, rfl⟩
      exact ⟨e, Finset.mem_univ e, rfl⟩
  have hdeg_eq : ∀ v : Fin t,
      T.degree v + (if v ∈ treeLeaves T then 2 else 0) = 3 := by
    intro v
    by_cases hv : v ∈ treeLeaves T
    · have h1 : T.degree v = 1 := (mem_treeLeaves T v).mp hv
      simp [hv, h1]
    · have hne1 : T.degree v ≠ 1 := fun h1 => hv ((mem_treeLeaves T v).mpr h1)
      rcases hbd.1.2 v with h1 | h3
      · exact False.elim (hne1 h1)
      · simp [hv]
        exact h3
  have hsum :
      ∑ v : Fin t, (T.degree v + (if v ∈ treeLeaves T then 2 else 0)) =
        ∑ _v : Fin t, 3 :=
    Finset.sum_congr rfl (fun v _ => hdeg_eq v)
  rw [Finset.sum_add_distrib] at hsum
  have hsum_deg : ∑ v : Fin t, T.degree v = 2 * T.edgeFinset.card :=
    T.sum_degrees_eq_twice_card_edges
  have hsum_ite :
      (∑ v : Fin t, if v ∈ treeLeaves T then 2 else 0) = 2 * (treeLeaves T).card := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hsum_three : (∑ _v : Fin t, 3) = 3 * t := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
  have hedges : T.edgeFinset.card + 1 = t := parentTree_card_edgeFinset ht hp
  omega

/-- Explicit list of all individual directed edges of `G : MultiDigraph n` (with multiplicity),
of length `G.numEdges`. -/
def MultiDigraph.edgeListWithMult {n : ℕ} (G : MultiDigraph n) : List (Fin n × Fin n) :=
  G.activePairsList.flatMap (fun p => List.replicate (G.edgeMult p.1 p.2) p)

theorem MultiDigraph.length_edgeListWithMult {n : ℕ} (G : MultiDigraph n) :
    G.edgeListWithMult.length = G.numEdges := by
  unfold MultiDigraph.edgeListWithMult
  rw [List.length_flatMap]
  have hsum := G.sumEdgeMult_activePairsList
  rw [MultiDigraph.sumEdgeMult_eq_map_sum] at hsum
  simpa [Function.comp_def] using hsum

/-- Endpoint pair `(tail, head)` of the `e`-th edge of `G : MultiDigraph n`. -/
def MultiDigraph.edgeEndpoints {n : ℕ} (G : MultiDigraph n) (e : Fin G.numEdges) :
    Fin n × Fin n :=
  G.edgeListWithMult[e.1]'(by rw [G.length_edgeListWithMult]; exact e.2)

/-- Convert a `G : MultiDigraph n` to a `ComputeDigraph` on `n` vertices and `G.numEdges` edges,
where edge `e : Fin G.numEdges` has tail `(G.edgeEndpoints e).1` and head `(G.edgeEndpoints e).2`. -/
abbrev MultiDigraph.toMultiComputeDigraph {n : ℕ} (G : MultiDigraph n) : ComputeDigraph where
  numVerts := n
  numEdges := G.numEdges
  head := fun e => (G.edgeEndpoints e).2
  tail := fun e => (G.edgeEndpoints e).1

/-- Convert `(G, Z)` (`G : MultiDigraph n`, `Z : List (Fin n)`) to a `ComputeRootedDigraph Z.length`. -/
abbrev MultiDigraph.toMultiComputeRootedDigraph {n : ℕ} (G : MultiDigraph n) (Z : List (Fin n)) :
    ComputeRootedDigraph Z.length where
  digraph := G.toMultiComputeDigraph
  roots := fun i => Z[i.1]'i.2

/-- A branch-decomposition `(T, τ)` of `G : MultiDigraph n` of width `≤ ω`. -/
abbrev IsMultiBranchDecompOfWidthLe {n t : ℕ} (ω : ℕ) (G : MultiDigraph n)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (τ : Fin G.numEdges → Fin t) : Prop :=
  IsDigraphBranchDecompOfWidthLe ω G.toMultiComputeDigraph T τ

/-- Flat `List ℕ` serialization of a branch-decomposition `(T, τ)` where `T = parentTree t p` has
`t` vertices (`Fin t`), `G` has `m` edges (`Fin m`), `parList = [p 0, ..., p (t - 1)]`, and
`tauList = [(τ 0).1, ..., (τ (m - 1)).1]`:
`[t, m] ++ parList ++ tauList`. -/
def encBranchDecomp (t m : ℕ) (parList tauList : List ℕ) : List ℕ :=
  [t, m] ++ parList ++ tauList

/-- Number of tree vertices `t = |V(T)|` read from a serialized branch-decomposition `bdCode`. -/
def bdNumTreeVerts (bdCode : List ℕ) : ℕ :=
  bdCode.getD 0 0

/-- Number of graph edges `m = |E(G)|` read from a serialized branch-decomposition `bdCode`. -/
def bdNumGraphEdges (bdCode : List ℕ) : ℕ :=
  bdCode.getD 1 0

/-- Parent map `p : ℕ → ℕ` of the tree `T` read from `bdCode` at offset `2 + z`. -/
def bdParent (bdCode : List ℕ) (z : ℕ) : ℕ :=
  bdCode.getD (2 + z) 0

/-- The tree `T = parentTree t p : SimpleGraph (Fin t)` decoded from `bdCode`. -/
abbrev bdTree (bdCode : List ℕ) : SimpleGraph (Fin (bdNumTreeVerts bdCode)) :=
  parentTree (bdNumTreeVerts bdCode) (bdParent bdCode)

/-- The leaf assignment `τ : Fin G.numEdges → Fin t` decoded from `bdCode` at offset `2 + t + e.1`. -/
def bdTau {n : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (ht : 0 < bdNumTreeVerts bdCode) (e : Fin G.numEdges) : Fin (bdNumTreeVerts bdCode) :=
  let v := bdCode.getD (2 + bdNumTreeVerts bdCode + e.1) 0
  if hv : v < bdNumTreeVerts bdCode then ⟨v, hv⟩ else ⟨0, ht⟩

/-- Validity predicate for a serialized branch-decomposition `bdCode : List ℕ` of `G : MultiDigraph n`
of width `≤ B`:
* `bdNumGraphEdges bdCode = G.numEdges`, `bdNumTreeVerts bdCode ≤ 2 * G.numEdges`, and
  `bdCode.length = 2 + bdNumTreeVerts bdCode + G.numEdges`;
* either `G.numEdges ≤ 1` and `bdNumTreeVerts bdCode = 0` (the page 70 convention when `|E(G)| ≤ 1`),
* or `2 ≤ G.numEdges`, `0 < bdNumTreeVerts bdCode`, `bdParent bdCode 0 = 0`,
  `bdParent bdCode z < z` for `0 < z < bdNumTreeVerts bdCode`, every edge maps to a vertex
  `< bdNumTreeVerts bdCode`, and `(bdTree bdCode, bdTau G bdCode ht)` is a branch-decomposition of
  `G` of width `≤ B`. -/
def IsValidBranchDecompCode (B : ℕ) {n : ℕ} (G : MultiDigraph n) (bdCode : List ℕ) : Prop :=
  let t := bdNumTreeVerts bdCode
  let m := bdNumGraphEdges bdCode
  m = G.numEdges ∧
  t ≤ 2 * m ∧
  bdCode.length = 2 + t + m ∧
  ((G.numEdges ≤ 1 ∧ t = 0 ∧ ∀ i < m, bdCode.getD (2 + i) 0 = 0) ∨
   (2 ≤ G.numEdges ∧
    ∃ ht : 0 < t,
      bdCode.getD 2 0 = 0 ∧
      (∀ z, 0 < z → z < t → bdParent bdCode z < z) ∧
      (∀ e : Fin G.numEdges, bdCode.getD (2 + t + e.1) 0 < t) ∧
      IsMultiBranchDecompOfWidthLe B G (bdTree bdCode) (bdTau G bdCode ht)))

theorem IsValidBranchDecompCode.mono {B₁ B₂ : ℕ} {n : ℕ} {G : MultiDigraph n} {bdCode : List ℕ}
    (h : IsValidBranchDecompCode B₁ G bdCode) (hB : B₁ ≤ B₂) :
    IsValidBranchDecompCode B₂ G bdCode := by
  rcases h with ⟨hm, ht_le, hlen, hcase⟩
  refine ⟨hm, ht_le, hlen, ?_⟩
  rcases hcase with hle1 | ⟨hge2, ht, hp0, hp, htau, hcub, hbij, hord⟩
  · exact Or.inl hle1
  · exact Or.inr ⟨hge2, ht, hp0, hp, htau, hcub, hbij, fun f hf => le_trans (hord f hf) hB⟩

/-- `G : MultiDigraph n` has a branch-decomposition of width `≤ ω` (including the convention on
GM XIII page 70: "(If there are no branch-decompositions of $G$, then $|E(G)| \le 1$ and $G$ has
branch-width 0 by convention.)"). -/
def HasBranchDecompOfWidthLe {n : ℕ} (G : MultiDigraph n) (ω : ℕ) : Prop :=
  G.numEdges ≤ 1 ∨
  ∃ (t : ℕ) (T : SimpleGraph (Fin t)) (_ : DecidableRel T.Adj) (τ : Fin G.numEdges → Fin t),
    IsMultiBranchDecompOfWidthLe ω G T τ

theorem IsValidBranchDecompCode.hasBranchDecompOfWidthLe {B : ℕ} {n : ℕ} {G : MultiDigraph n}
    {bdCode : List ℕ} (h : IsValidBranchDecompCode B G bdCode) :
    HasBranchDecompOfWidthLe G B := by
  rcases h with ⟨_, _, _, hle1 | ⟨_, ht, _, _, _, hbd⟩⟩
  · exact Or.inl hle1.1
  · exact Or.inr ⟨bdNumTreeVerts bdCode, bdTree bdCode, inferInstance, bdTau G bdCode ht, hbd⟩

theorem HasBranchDecompOfWidthLe.mono {n ω₁ ω₂ : ℕ} {G : MultiDigraph n}
    (h : HasBranchDecompOfWidthLe G ω₁) (hω : ω₁ ≤ ω₂) :
    HasBranchDecompOfWidthLe G ω₂ := by
  rcases h with hle1 | ⟨t, T, hdec, τ, htree, hbij, hcut⟩
  · exact Or.inl hle1
  · exact Or.inr ⟨t, T, hdec, τ, htree, hbij, fun f hf => le_trans (hcut f hf) hω⟩

/-- `G : MultiDigraph n` has branch-width `≥ ω` (GM XIII Section 3, page 70):
`|E(G)| ≥ 2` and no branch-decomposition of `G` has width `< ω`. -/
def HasBranchWidthGe {n : ℕ} (G : MultiDigraph n) (ω : ℕ) : Prop :=
  2 ≤ G.numEdges ∧ ∀ w_bd < ω, ¬ HasBranchDecompOfWidthLe G w_bd

theorem not_hasBranchWidthGe_of_hasBranchDecompOfWidthLe {n ω₁ ω₂ : ℕ} {G : MultiDigraph n}
    (hbd : HasBranchDecompOfWidthLe G ω₁) (h42 : ω₁ < ω₂) :
    ¬ HasBranchWidthGe G ω₂ := by
  intro ⟨_, hno⟩
  exact hno ω₁ h42 hbd

/-- The high-branch-width case information produced by Algorithm (3.3) when `G' ≠ G`
(matching `IsValidAlg33Output` in `GraphMinor/Compute/Algorithm33.lean`):
`G'` is a simple graph (`G'.NoLoops` and `∀ u v, G'.edgeMult u v + G'.edgeMult v u ≤ 1`), and
either:
1. `(G'.toSimpleGraph.edgeFinset.card : ℚ) ≤ ((3/2)ω - 1)n + 1` and
   `(G'.toSimpleGraph.edgeFinset.card : ℚ) > ((3/2)ω - 1)n` (GM XIII (3.2), page 72); or
2. Step (6) occurred: there exist `G_step6 ≤ G.toSimpleGraph`, `g ∈ G_step6.edgeFinset`, and
   `Z ⊆ V(G)` with `|Z| = 3ω` such that `G'.toSimpleGraph = G_step6.deleteEdges {g}` and `G_step6`
   has no separation of order `≤ ω` balanced on `Z` (`sep.IsBalancedQ Z`, GM XIII (3.1), page 71). -/
def IsAlg33HighWidthCase (ω : ℕ) {n : ℕ} (G G' : MultiDigraph n) : Prop :=
  haveI := Classical.decRel G'.toSimpleGraph.Adj
  (∀ u : Fin n, G'.edgeMult u u = 0) ∧
  (∀ u v : Fin n, G'.edgeMult u v + G'.edgeMult v u ≤ 1) ∧
  (((G'.toSimpleGraph.edgeFinset.card : ℚ) ≤ ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ) + 1 ∧
    (G'.toSimpleGraph.edgeFinset.card : ℚ) > ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ)) ∨
   (∃ (G_step6 : SimpleGraph (Fin n)) (g : Sym2 (Fin n)) (Z : Finset (Fin n)),
     haveI := Classical.decRel G_step6.Adj
     G_step6 ≤ G.toSimpleGraph ∧
     g ∈ G_step6.edgeFinset ∧
     Z.card = 3 * ω ∧
     G'.toSimpleGraph ≤ G_step6.deleteEdges {g} ∧
     G'.toSimpleGraph = G_step6.deleteEdges {g} ∧
     ∀ sep : GraphSeparation G_step6, sep.order ≤ ω → ¬ sep.IsBalancedQ Z))

theorem parentTree_congr (t : ℕ) (p₁ p₂ : ℕ → ℕ)
    (h : ∀ z, 0 < z → z < t → p₁ z = p₂ z) :
    parentTree t p₁ = parentTree t p₂ := by
  ext u v
  unfold parentTree
  constructor <;> rintro ⟨hne, ⟨hu, hvp⟩ | ⟨hv, hup⟩⟩
  · exact ⟨hne, Or.inl ⟨hu, hvp.trans (h u.1 hu u.2)⟩⟩
  · exact ⟨hne, Or.inr ⟨hv, hup.trans (h v.1 hv v.2)⟩⟩
  · exact ⟨hne, Or.inl ⟨hu, hvp.trans (h u.1 hu u.2).symm⟩⟩
  · exact ⟨hne, Or.inr ⟨hv, hup.trans (h v.1 hv v.2).symm⟩⟩

theorem list_getD_eq_getElem (l : List ℕ) (i d : ℕ) (hi : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD, hi]

theorem getD_two_add_cons_cons (a b : ℕ) (xs : List ℕ) (i : ℕ) :
    (a :: b :: xs).getD (2 + i) 0 = xs.getD i 0 := by
  have h : 2 + i = i + 1 + 1 := by omega
  rw [h]
  rfl

/-- Constructor for `IsValidBranchDecompCode` when `G.numEdges ≤ 1`. -/
theorem isValidBranchDecompCode_le_one (B : ℕ) {n : ℕ} (G : MultiDigraph n)
    (hle : G.numEdges ≤ 1) :
    IsValidBranchDecompCode B G ([0, G.numEdges] ++ List.replicate G.numEdges 0) := by
  unfold IsValidBranchDecompCode bdNumTreeVerts bdNumGraphEdges
  refine ⟨rfl, by simp, by simp; omega, Or.inl ⟨hle, rfl, fun i hi => ?_⟩⟩
  change (0 :: G.numEdges :: List.replicate G.numEdges 0).getD (2 + i) 0 = 0
  rw [getD_two_add_cons_cons, list_getD_eq_getElem _ _ _ (by simp; exact hi)]
  simp

theorem isDigraphBranchDecompOfWidthLe_congr {t : ℕ} (ω : ℕ) (G : ComputeDigraph)
    {T₁ T₂ : SimpleGraph (Fin t)} [DecidableRel T₁.Adj] [DecidableRel T₂.Adj]
    {τ₁ τ₂ : Fin G.numEdges → Fin t}
    (hT : T₁ = T₂) (hτ : τ₁ = τ₂)
    (h : IsDigraphBranchDecompOfWidthLe ω G T₁ τ₁) :
    IsDigraphBranchDecompOfWidthLe ω G T₂ τ₂ := by
  subst hT hτ
  convert h

/-- Constructor for `IsValidBranchDecompCode` when `2 ≤ G.numEdges`. -/
theorem isValidBranchDecompCode_of_ge_two (B : ℕ) {n t : ℕ} (G : MultiDigraph n)
    (parList tauList : List ℕ) (p : ℕ → ℕ) (τ : Fin G.numEdges → Fin t)
    (hge2 : 2 ≤ G.numEdges)
    (ht_pos : 0 < t)
    (ht_le : t ≤ 2 * G.numEdges)
    (hpar_len : parList.length = t)
    (htau_len : tauList.length = G.numEdges)
    (hpar0 : parList[0]'(by omega) = 0)
    (hpar_eq : ∀ z (hz : z < t), 0 < z → parList[z]'(by omega) = p z)
    (hp_lt : ∀ z, 0 < z → z < t → p z < z)
    (htau_eq : ∀ e : Fin G.numEdges, tauList[e.1]'(by omega) = (τ e).1)
    (hbd : IsMultiBranchDecompOfWidthLe B G (parentTree t p) τ) :
    IsValidBranchDecompCode B G (encBranchDecomp t G.numEdges parList tauList) := by
  let bdCode := encBranchDecomp t G.numEdges parList tauList
  have ht_bd : bdNumTreeVerts bdCode = t := rfl
  have hm_bd : bdNumGraphEdges bdCode = G.numEdges := rfl
  have hlen_bd : bdCode.length = 2 + t + G.numEdges := by
    simp [bdCode, encBranchDecomp, hpar_len, htau_len]
    omega
  have hgetD_2 : ∀ i, bdCode.getD (2 + i) 0 = (parList ++ tauList).getD i 0 := by
    intro i
    exact getD_two_add_cons_cons t G.numEdges (parList ++ tauList) i
  have hp2 : bdCode.getD 2 0 = 0 := by
    have h0 := hgetD_2 0
    have hlen_pt : 0 < (parList ++ tauList).length := by simp [hpar_len]; omega
    rw [list_getD_eq_getElem (parList ++ tauList) 0 0 hlen_pt,
        List.getElem_append_left (by omega)] at h0
    simpa [hpar0] using h0
  have hpar_z : ∀ z (hz : z < t), 0 < z → bdParent bdCode z = p z := by
    intro z hz hz_pos
    unfold bdParent
    have hlen_pt : z < (parList ++ tauList).length := by simp [hpar_len]; omega
    rw [hgetD_2 z, list_getD_eq_getElem (parList ++ tauList) z 0 hlen_pt,
        List.getElem_append_left (by omega), hpar_eq z hz hz_pos]
  have htau_e : ∀ e : Fin G.numEdges, bdCode.getD (2 + t + e.1) 0 = (τ e).1 := by
    intro e
    have hadd : 2 + t + e.1 = 2 + (t + e.1) := by omega
    have hlen_pt : t + e.1 < (parList ++ tauList).length := by simp [hpar_len, htau_len]
    rw [hadd, hgetD_2 (t + e.1),
        list_getD_eq_getElem (parList ++ tauList) (t + e.1) 0 hlen_pt,
        List.getElem_append_right (by omega)]
    have hsub : t + e.1 - parList.length = e.1 := by omega
    simp only [hsub, htau_eq e]
  refine ⟨hm_bd, by rw [ht_bd]; exact ht_le, by rw [ht_bd]; exact hlen_bd,
    Or.inr ⟨hge2, ht_pos, hp2, ?_, ?_, ?_⟩⟩
  · intro z hz_pos hz_lt
    rw [ht_bd] at hz_lt
    rw [hpar_z z hz_lt hz_pos]
    exact hp_lt z hz_pos hz_lt
  · intro e
    rw [ht_bd, htau_e e]
    exact (τ e).2
  · have htree_eq : parentTree t p = bdTree bdCode := by
      symm
      apply parentTree_congr
      intro z hz_pos hz_lt
      exact hpar_z z hz_lt hz_pos
    have htau_fn : τ = bdTau G bdCode ht_pos := by
      funext e
      unfold bdTau
      dsimp only
      have hval : bdCode.getD (2 + bdNumTreeVerts bdCode + e.1) 0 = (τ e).1 := by
        rw [ht_bd, htau_e e]
      have hlt : bdCode.getD (2 + bdNumTreeVerts bdCode + e.1) 0 < bdNumTreeVerts bdCode := by
        rw [hval, ht_bd]; exact (τ e).2
      simp only [hlt, ↓reduceDIte]
      exact (Fin.ext hval).symm
    exact @isDigraphBranchDecompOfWidthLe_congr t B G.toMultiComputeDigraph
      (parentTree t p) (bdTree bdCode)
      (instDecidableRelParentTreeAdj t p) (instDecidableRelParentTreeAdj t (bdParent bdCode))
      τ (bdTau G bdCode ht_pos) htree_eq htau_fn hbd

theorem MultiDigraph.mem_edgeListWithMult_iff {n : ℕ} (G : MultiDigraph n) (p : Fin n × Fin n) :
    p ∈ G.edgeListWithMult ↔ 0 < G.edgeMult p.1 p.2 := by
  unfold MultiDigraph.edgeListWithMult
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨q, hq, hrep⟩
    rw [List.mem_replicate] at hrep
    rcases hrep with ⟨hne, rfl⟩
    exact (G.mem_activePairsList p).mp hq
  · intro hpos
    exact ⟨p, (G.mem_activePairsList p).mpr hpos, List.mem_replicate.mpr ⟨by omega, rfl⟩⟩

theorem MultiDigraph.exists_edgeEndpoints_of_edgeMult_pos {n : ℕ} (G : MultiDigraph n)
    {u v : Fin n} (hpos : 0 < G.edgeMult u v) :
    ∃ e : Fin G.numEdges, G.edgeEndpoints e = (u, v) := by
  have hmem : (u, v) ∈ G.edgeListWithMult := (G.mem_edgeListWithMult_iff (u, v)).mpr hpos
  rcases List.getElem_of_mem hmem with ⟨i, hi, heq⟩
  exact ⟨⟨i, by rw [← G.length_edgeListWithMult]; exact hi⟩, heq⟩

theorem MultiDigraph.edgeMult_edgeEndpoints_pos {n : ℕ} (G : MultiDigraph n)
    (e : Fin G.numEdges) :
    0 < G.edgeMult (G.edgeEndpoints e).1 (G.edgeEndpoints e).2 := by
  have hmem : G.edgeEndpoints e ∈ G.edgeListWithMult := List.getElem_mem _
  exact (G.mem_edgeListWithMult_iff _).mp hmem

theorem MultiDigraph.toSimpleGraph_adj_edgeEndpoints {n : ℕ} (G : MultiDigraph n)
    (e : Fin G.numEdges) (hne : (G.edgeEndpoints e).1 ≠ (G.edgeEndpoints e).2) :
    G.toSimpleGraph.Adj (G.edgeEndpoints e).1 (G.edgeEndpoints e).2 := by
  rw [G.toSimpleGraph_adj]
  exact ⟨hne, Or.inl (G.edgeMult_edgeEndpoints_pos e)⟩

/-- Helper: in `l.flatMap (fun a => List.replicate (f a) a)` for `l.Nodup`, identical elements
appear contiguously. -/
theorem flatMap_replicate_contiguous {α : Type*} {l : List α} (hl : l.Nodup) (f : α → ℕ)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hk : k < (l.flatMap (fun a => List.replicate (f a) a)).length)
    (heq : (l.flatMap (fun a => List.replicate (f a) a))[i]'(by omega) =
           (l.flatMap (fun a => List.replicate (f a) a))[k]'hk) :
    (l.flatMap (fun a => List.replicate (f a) a))[j]'(by omega) =
    (l.flatMap (fun a => List.replicate (f a) a))[i]'(by omega) := by
  induction l generalizing i j k with
  | nil => simp at hk
  | cons a as ih =>
    rcases List.nodup_cons.mp hl with ⟨ha_not_mem, has_nodup⟩
    let L₁ := List.replicate (f a) a
    let L₂ := as.flatMap (fun x => List.replicate (f x) x)
    have hL₁ : L₁.length = f a := List.length_replicate
    have hk' : k < (L₁ ++ L₂).length := hk
    have hk_sum : k < f a + L₂.length := by simpa [L₁, L₂] using hk
    change (L₁ ++ L₂)[i]'(by omega) = (L₁ ++ L₂)[k]'hk' at heq
    change (L₁ ++ L₂)[j]'(by omega) = (L₁ ++ L₂)[i]'(by omega)
    by_cases hi_lt : i < f a
    · have hi_eq : (L₁ ++ L₂)[i]'(by omega) = a := by
        rw [List.getElem_append_left (by omega)]
        simp [L₁]
      by_cases hk_lt : k < f a
      · have hj_lt : j < f a := by omega
        have hj_eq : (L₁ ++ L₂)[j]'(by omega) = a := by
          rw [List.getElem_append_left (by omega)]
          simp [L₁]
        rw [hj_eq, hi_eq]
      · exfalso
        have hk_mem : (L₁ ++ L₂)[k]'hk' ∈ L₂ := by
          rw [List.getElem_append_right (by omega)]
          exact List.getElem_mem _
        rw [← heq, hi_eq] at hk_mem
        dsimp [L₂] at hk_mem
        rw [List.mem_flatMap] at hk_mem
        rcases hk_mem with ⟨b, hb_mem, hb_rep⟩
        rw [List.mem_replicate] at hb_rep
        rcases hb_rep with ⟨_, rfl⟩
        exact ha_not_mem hb_mem
    · have hk_sub : k - f a < (as.flatMap (fun x => List.replicate (f x) x)).length := by
        change k - f a < L₂.length
        omega
      have h_i : (L₁ ++ L₂)[i]'(by omega) = L₂[i - f a]'(by omega) := by
        rw [List.getElem_append_right (by omega)]
        simp [hL₁]
      have h_j : (L₁ ++ L₂)[j]'(by omega) = L₂[j - f a]'(by omega) := by
        rw [List.getElem_append_right (by omega)]
        simp [hL₁]
      have h_k : (L₁ ++ L₂)[k]'hk' = L₂[k - f a]'(by omega) := by
        rw [List.getElem_append_right (by omega)]
        simp [hL₁]
      rw [h_i, h_k] at heq
      rw [h_j, h_i]
      exact ih has_nodup (by omega) (by omega) hk_sub heq

/-- Contiguity of identical directed edges in `G.edgeEndpoints`: if `e₁.1 ≤ e₂.1 ≤ e₃.1` and
`G.edgeEndpoints e₁ = G.edgeEndpoints e₃`, then `G.edgeEndpoints e₂ = G.edgeEndpoints e₁`. -/
theorem MultiDigraph.edgeEndpoints_contiguous {n : ℕ} (G : MultiDigraph n)
    {e₁ e₂ e₃ : Fin G.numEdges} (h12 : e₁.1 ≤ e₂.1) (h23 : e₂.1 ≤ e₃.1)
    (heq : G.edgeEndpoints e₁ = G.edgeEndpoints e₃) :
    G.edgeEndpoints e₂ = G.edgeEndpoints e₁ := by
  have hk : e₃.1 < (G.activePairsList.flatMap (fun p => List.replicate (G.edgeMult p.1 p.2) p)).length := by
    have hlen := G.length_edgeListWithMult
    unfold MultiDigraph.edgeListWithMult at hlen
    omega
  exact flatMap_replicate_contiguous G.nodup_activePairsList (fun p => G.edgeMult p.1 p.2)
    h12 h23 hk heq

/-! ### Section 2: Finite Tree Rooting (`T ≃g parentTree t p`) and Isomorphism Transfer -/

/-- Any graph isomorphism `φ : T ≃g T'` satisfies `T.map φ.toEquiv.toEmbedding = T'`. -/
theorem _root_.SimpleGraph.Iso.map_eq {ι ι' : Type*} {T : SimpleGraph ι} {T' : SimpleGraph ι'}
    (φ : T ≃g T') : T.map φ.toEquiv.toEmbedding = T' := by
  ext u' v'
  obtain ⟨u, rfl⟩ := φ.surjective u'
  obtain ⟨v, rfl⟩ := φ.surjective v'
  exact (SimpleGraph.Iso.map φ.toEquiv T).map_rel_iff.trans φ.map_rel_iff.symm

/-- Transporting `GM13.IsGraphBranchDecomposition` along a tree isomorphism `φ : T ≃g T'`. -/
theorem isGraphBranchDecomposition_of_iso {α β ι ι' : Type*} [Fintype ι] [Fintype ι']
    {G : Graph α β} {T : SimpleGraph ι} {T' : SimpleGraph ι'}
    (φ : T ≃g T') {τ : β → ι}
    (hbd : GM13.IsGraphBranchDecomposition G T τ) :
    GM13.IsGraphBranchDecomposition G T' (φ ∘ τ) := by
  have hmap : T' = T.map φ.toEquiv.toEmbedding := (SimpleGraph.Iso.map_eq φ).symm
  refine ⟨?_, ?_⟩
  · rw [hmap]
    rcases hbd.isTernaryOrEmpty with hempty | htern
    · exact Or.inl (@Equiv.isEmpty _ _ φ.toEquiv.symm hempty)
    · exact Or.inr (htern.map φ.toEquiv)
  · rw [congrArg GM10.leafSet hmap, GM10.leafSet_map]
    exact φ.injective.injOn.bijOn_image.comp hbd.bijOn

/-- Transporting `GM13.graphBranchEdgeOrder` along a tree isomorphism `φ : T ≃g T'`. -/
theorem graphBranchEdgeOrder_of_iso {α β ι ι' : Type*} [Fintype ι] [Fintype ι']
    (G : Graph α β) {T : SimpleGraph ι} {T' : SimpleGraph ι'}
    (φ : T ≃g T') (τ : β → ι) (f : Sym2 ι) :
    GM13.graphBranchEdgeOrder G T' (φ ∘ τ) (f.map φ) =
      GM13.graphBranchEdgeOrder G T τ f := by
  unfold GM13.graphBranchEdgeOrder
  congr 1
  ext v
  simp only [Set.mem_sep_iff, Function.comp_apply]
  refine and_congr_right fun _ => exists_congr fun f₁ => and_congr_right fun _ =>
    exists_congr fun f₂ => and_congr_right fun _ => and_congr_left fun _ => not_congr ?_
  let ψ : (T.deleteEdges {f}) ≃g (T'.deleteEdges {f.map φ}) :=
    { toEquiv := φ.toEquiv
      map_rel_iff' := by
        intro x y
        simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
        refine and_congr φ.map_rel_iff (not_congr ?_)
        change Sym2.map φ s(x, y) = Sym2.map φ f ↔ s(x, y) = f
        exact (Sym2.map.injective φ.injective).eq_iff }
  exact ⟨fun ⟨w⟩ => ⟨(w.map ψ.symm.toHom).copy (φ.symm_apply_apply _) (φ.symm_apply_apply _)⟩,
    fun ⟨w⟩ => ⟨w.map ψ.toHom⟩⟩

/-- Transporting `GM13.graphBranchDecompWidth` along a tree isomorphism `φ : T ≃g T'`. -/
theorem graphBranchDecompWidth_of_iso {α β ι ι' : Type*} [Fintype ι] [Fintype ι']
    (G : Graph α β) {T : SimpleGraph ι} {T' : SimpleGraph ι'}
    (φ : T ≃g T') (τ : β → ι) :
    GM13.graphBranchDecompWidth G T' (φ ∘ τ) =
      GM13.graphBranchDecompWidth G T τ := by
  unfold GM13.graphBranchDecompWidth
  congr 1
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨f', hf', rfl⟩
    obtain ⟨f, rfl⟩ : ∃ f : Sym2 ι, Sym2.map φ f = f' := by
      induction f' using Sym2.ind with | _ x' y' =>
      exact ⟨s(φ.symm x', φ.symm y'), by simp⟩
    refine ⟨f, ?_, (graphBranchEdgeOrder_of_iso G φ τ f).symm⟩
    induction f using Sym2.ind with | _ x y =>
    have hf'' : T'.Adj (φ x) (φ y) := by simpa [SimpleGraph.mem_edgeSet] using hf'
    simpa [SimpleGraph.mem_edgeSet] using φ.map_rel_iff.mp hf''
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f.map φ, ?_, graphBranchEdgeOrder_of_iso G φ τ f⟩
    induction f using Sym2.ind with | _ x y =>
    have hf' : T.Adj x y := by simpa [SimpleGraph.mem_edgeSet] using hf
    simpa [SimpleGraph.mem_edgeSet] using φ.map_rel_iff.mpr hf'

/-- Every finite non-empty tree `T : SimpleGraph ι` with `t = Fintype.card ι > 0` is isomorphic to
`parentTree t p` for some parent function `p : ℕ → ℕ` with `p 0 = 0` and `p z < z` for all
`0 < z < t`. Proved by induction on `t`, peeling a degree-1 leaf at the highest index `t - 1`. -/
theorem exists_iso_parentTree_of_isTree_card :
    ∀ (t : ℕ) (_ : 0 < t) {ι : Type*} [Fintype ι] (T : SimpleGraph ι),
      T.IsTree → Fintype.card ι = t →
      ∃ (p : ℕ → ℕ), p 0 = 0 ∧ (∀ z, 0 < z → z < t → p z < z) ∧
        Nonempty (T ≃g parentTree t p) := by
  intro t
  induction t with
  | zero =>
    intro ht
    omega
  | succ t ih =>
    intro _ ι _ T hT hcard
    by_cases ht0 : t = 0
    · subst ht0
      have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      have e : ι ≃ Fin 1 := Fintype.equivOfCardEq (by simp [hcard])
      refine ⟨fun _ => 0, rfl, fun z hz1 hz2 => by omega, ⟨{
        toEquiv := e
        map_rel_iff' := fun {x y} => by
          have hxy : x = y := Subsingleton.elim x y
          subst hxy
          simp
      }⟩⟩
    · have ht_pos : 0 < t := Nat.pos_of_ne_zero ht0
      have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨v₀, hv₀⟩ := hT.exists_vert_degree_one_of_nontrivial
      have hv₀_uniq := hv₀
      rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hv₀_uniq
      rcases hv₀_uniq with ⟨w₀, hadj_v₀w₀, huniq_w₀⟩
      have hw₀_ne : w₀ ≠ v₀ := hadj_v₀w₀.ne.symm
      let S : Set ι := {v₀}ᶜ
      have hT'_tree : (T.induce S).IsTree :=
        GM10.isTree_induce_compl_singleton hT hv₀
      have hcard_S : Fintype.card S = t := by
        have h1 : Fintype.card (↑({v₀} : Set ι)) = 1 := Fintype.card_unique
        rw [Fintype.card_compl_set ({v₀} : Set ι), hcard, h1, Nat.add_sub_cancel]
      obtain ⟨p', hp'0, hp', ⟨iso'⟩⟩ := ih ht_pos (T.induce S) hT'_tree hcard_S
      let w_idx : Fin t := iso' ⟨w₀, hw₀_ne⟩
      let p : ℕ → ℕ := fun z => if z = t then w_idx.1 else p' z
      have hp0 : p 0 = 0 := by
        dsimp [p]
        rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), hp'0]
      have hp_lt : ∀ z, 0 < z → z < t + 1 → p z < z := by
        intro z hz_pos hz_lt
        dsimp [p]
        split_ifs with hzt
        · subst hzt
          exact w_idx.2
        · exact hp' z hz_pos (by omega)
      let f_inv (i : Fin (t + 1)) : ι :=
        if hi : i.1 < t then (iso'.symm ⟨i.1, hi⟩).1 else v₀
      let f_to (x : ι) : Fin (t + 1) :=
        if hx : x = v₀ then ⟨t, Nat.lt_succ_self t⟩
        else ⟨(iso' ⟨x, hx⟩).1, Nat.lt_trans (iso' ⟨x, hx⟩).2 (Nat.lt_succ_self t)⟩
      have hleft_inv : Function.LeftInverse f_to f_inv := by
        intro i
        by_cases hi : i.1 < t
        · have hinv : f_inv i = (iso'.symm ⟨i.1, hi⟩).1 := by simp [f_inv, hi]
          have hne : (iso'.symm ⟨i.1, hi⟩).1 ≠ v₀ := (iso'.symm ⟨i.1, hi⟩).2
          rw [hinv]
          dsimp [f_to]
          simp only [hne, ↓reduceDIte]
          have hsub : (⟨(iso'.symm ⟨i.1, hi⟩).1, hne⟩ : S) = iso'.symm ⟨i.1, hi⟩ :=
            Subtype.ext rfl
          rw [hsub, iso'.apply_symm_apply]
        · have hi_eq : i.1 = t := by omega
          have hinv : f_inv i = v₀ := by simp [f_inv, hi]
          rw [hinv]
          dsimp [f_to]
          simp only [↓reduceDIte]
          exact Fin.ext hi_eq.symm
      have hright_inv : Function.RightInverse f_to f_inv := by
        intro x
        dsimp [f_to, f_inv]
        by_cases hx : x = v₀
        · subst hx
          simp only [↓reduceDIte, Nat.lt_irrefl]
        · simp only [hx, ↓reduceDIte, (iso' ⟨x, hx⟩).2]
          exact congrArg Subtype.val (iso'.symm_apply_apply ⟨x, hx⟩)
      have hiso_symm : parentTree (t + 1) p ≃g T :=
        { toEquiv :=
            { toFun := f_inv
              invFun := f_to
              left_inv := hleft_inv
              right_inv := hright_inv }
          map_rel_iff' := by
            intro i j
            dsimp [f_inv]
            by_cases hi : i.1 < t
            · by_cases hj : j.1 < t
              · simp only [hi, hj, ↓reduceDIte]
                have hadj_p : (parentTree (t + 1) p).Adj i j ↔
                    (parentTree t p').Adj ⟨i.1, hi⟩ ⟨j.1, hj⟩ := by
                  rw [parentTree_adj_of_lt hp_lt, parentTree_adj_of_lt hp']
                  have hi_ne : i.1 ≠ t := by omega
                  have hj_ne : j.1 ≠ t := by omega
                  simp [p, hi_ne, hj_ne]
                rw [hadj_p, ← iso'.symm.map_rel_iff]
                rfl
              · have hj_eq : j.1 = t := by omega
                simp only [hi, hj, ↓reduceDIte]
                rw [parentTree_adj_of_lt hp_lt]
                have hnot1 : ¬ (0 < i.1 ∧ j.1 = p i.1) := by
                  rintro ⟨hi_pos, hjp⟩
                  have : p i.1 < i.1 := hp_lt i.1 hi_pos i.2
                  omega
                have h2 : (0 < j.1 ∧ i.1 = p j.1) ↔ i.1 = w_idx.1 := by
                  simp [hj_eq, ht_pos, p]
                rw [or_iff_right hnot1, h2]
                constructor
                · intro hadj_T
                  have hu_eq : (iso'.symm ⟨i.1, hi⟩).1 = w₀ := huniq_w₀ _ hadj_T.symm
                  have hsub_eq : iso'.symm ⟨i.1, hi⟩ = ⟨w₀, hw₀_ne⟩ := Subtype.ext hu_eq
                  have hfin_eq : (⟨i.1, hi⟩ : Fin t) = w_idx := by
                    dsimp [w_idx]
                    rw [← hsub_eq, iso'.apply_symm_apply]
                  exact congrArg Fin.val hfin_eq
                · intro hi_w
                  have hfin_eq : (⟨i.1, hi⟩ : Fin t) = w_idx := Fin.ext hi_w
                  have hsub_eq : iso'.symm ⟨i.1, hi⟩ = ⟨w₀, hw₀_ne⟩ := by
                    rw [hfin_eq]
                    exact iso'.symm_apply_apply ⟨w₀, hw₀_ne⟩
                  have hu_eq : (iso'.symm ⟨i.1, hi⟩).1 = w₀ := congrArg Subtype.val hsub_eq
                  rw [hu_eq]
                  exact hadj_v₀w₀.symm
            · have hi_eq : i.1 = t := by omega
              by_cases hj : j.1 < t
              · simp only [hi, hj, ↓reduceDIte]
                rw [parentTree_adj_of_lt hp_lt]
                have hnot2 : ¬ (0 < j.1 ∧ i.1 = p j.1) := by
                  rintro ⟨hj_pos, hip⟩
                  have : p j.1 < j.1 := hp_lt j.1 hj_pos j.2
                  omega
                have h1 : (0 < i.1 ∧ j.1 = p i.1) ↔ j.1 = w_idx.1 := by
                  simp [hi_eq, ht_pos, p]
                rw [or_iff_left hnot2, h1]
                constructor
                · intro hadj_T
                  have hu_eq : (iso'.symm ⟨j.1, hj⟩).1 = w₀ := huniq_w₀ _ hadj_T
                  have hsub_eq : iso'.symm ⟨j.1, hj⟩ = ⟨w₀, hw₀_ne⟩ := Subtype.ext hu_eq
                  have hfin_eq : (⟨j.1, hj⟩ : Fin t) = w_idx := by
                    dsimp [w_idx]
                    rw [← hsub_eq, iso'.apply_symm_apply]
                  exact congrArg Fin.val hfin_eq
                · intro hj_w
                  have hfin_eq : (⟨j.1, hj⟩ : Fin t) = w_idx := Fin.ext hj_w
                  have hsub_eq : iso'.symm ⟨j.1, hj⟩ = ⟨w₀, hw₀_ne⟩ := by
                    rw [hfin_eq]
                    exact iso'.symm_apply_apply ⟨w₀, hw₀_ne⟩
                  have hu_eq : (iso'.symm ⟨j.1, hj⟩).1 = w₀ := congrArg Subtype.val hsub_eq
                  rw [hu_eq]
                  exact hadj_v₀w₀
              · have hj_eq : j.1 = t := by omega
                have hij : i = j := Fin.ext (hi_eq.trans hj_eq.symm)
                subst hij
                simp [hi] }
      exact ⟨p, hp0, hp_lt, ⟨hiso_symm.symm⟩⟩


/-! ### Section 3: Goal 1 for Simple Graphs (`IsBranchDecompOfWidthLe` ↔ `GM13`) -/

/-- `IsCubicOrLeafTree T` in `GraphMinor.Compute` is equivalent to `GM10.IsTernaryTree T`. -/
theorem isCubicOrLeafTree_iff_isTernaryTree {t : ℕ}
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] :
    IsCubicOrLeafTree T ↔ GM10.IsTernaryTree T := by
  refine ⟨fun ⟨hT, hdeg⟩ => ⟨hT, fun v => ?_⟩, fun ⟨hT, hdeg⟩ => ⟨hT, fun v => ?_⟩⟩
  · have h := hdeg v
    rw [← SimpleGraph.ncard_neighborSet] at h ⊢
    exact h
  · have h := hdeg v
    rw [← SimpleGraph.ncard_neighborSet] at h ⊢
    exact h

/-- For any cubic/leaf tree `T : SimpleGraph (Fin t)`,
`(treeLeaves T : Set (Fin t)) = GM10.leafSet T`. -/
theorem coe_treeLeaves_eq_leafSet {t : ℕ}
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (hcub : IsCubicOrLeafTree T) :
    (↑(treeLeaves T) : Set (Fin t)) = GM10.leafSet T := by
  ext v
  simp only [Finset.mem_coe, treeLeaves, Finset.mem_filter, Finset.mem_univ, true_and,
    GM10.leafSet, GM10.IsLeaf, Set.mem_ofPred_eq, ← SimpleGraph.ncard_neighborSet]
  have hdeg := hcub.2 v
  rw [← SimpleGraph.ncard_neighborSet] at hdeg
  omega

/-- In any cubic/leaf tree `parentTree t p`, the degree-sum formula implies
`t + 2 = 2 * (treeLeaves (parentTree t p)).card`, and hence `t ≤ 2 * (treeLeaves (parentTree t p)).card`. -/
theorem t_le_two_mul_card_treeLeaves {t : ℕ} {p : ℕ → ℕ}
    (ht : 0 < t) (hp : ∀ z, 0 < z → z < t → p z < z)
    (hcub : IsCubicOrLeafTree (parentTree t p)) :
    t ≤ 2 * (treeLeaves (parentTree t p)).card := by
  let T := parentTree t p
  have hdeg_eq : ∀ v : Fin t,
      T.degree v + (if v ∈ treeLeaves T then 2 else 0) = 3 := by
    intro v
    by_cases hv : v ∈ treeLeaves T
    · have h1 : T.degree v = 1 := (mem_treeLeaves T v).mp hv
      simp [hv, h1]
    · have hne1 : T.degree v ≠ 1 := fun h1 => hv ((mem_treeLeaves T v).mpr h1)
      rcases hcub.2 v with h1 | h3
      · exact False.elim (hne1 h1)
      · simp [hv]
        exact h3
  have hsum :
      ∑ v : Fin t, (T.degree v + (if v ∈ treeLeaves T then 2 else 0)) =
        ∑ _v : Fin t, 3 :=
    Finset.sum_congr rfl (fun v _ => hdeg_eq v)
  rw [Finset.sum_add_distrib] at hsum
  have hsum_deg : ∑ v : Fin t, T.degree v = 2 * T.edgeFinset.card :=
    T.sum_degrees_eq_twice_card_edges
  have hsum_ite :
      (∑ v : Fin t, if v ∈ treeLeaves T then 2 else 0) = 2 * (treeLeaves T).card := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hsum_three : (∑ _v : Fin t, 3) = 3 * t := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
  have hedges : T.edgeFinset.card + 1 = t := parentTree_card_edgeFinset ht hp
  change t ≤ 2 * (treeLeaves T).card
  omega

/-- Upper bound characterization for `GM13.graphBranchDecompWidth`. -/
theorem graphBranchDecompWidth_le_iff {α β ι : Type*} [Fintype ι]
    (G : Graph α β) (T : SimpleGraph ι) (τ : β → ι) (B : ℕ) :
    GM13.graphBranchDecompWidth G T τ ≤ B ↔
      ∀ f ∈ T.edgeSet, GM13.graphBranchEdgeOrder G T τ f ≤ B := by
  unfold GM13.graphBranchDecompWidth
  have hfin : (GM13.graphBranchEdgeOrder G T τ '' T.edgeSet).Finite :=
    (Set.toFinite T.edgeSet).image _
  constructor
  · intro hle f hf
    exact le_trans (le_csSup hfin.bddAbove ⟨f, hf, rfl⟩) hle
  · intro h
    by_cases hne : (GM13.graphBranchEdgeOrder G T τ '' T.edgeSet).Nonempty
    · refine csSup_le hne ?_
      rintro _ ⟨f, hf, rfl⟩
      exact h f hf
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp

/-- Incidence in `G.toGMGraph` for a simple graph `G : SimpleGraph α`. -/
theorem toGMGraph_inc_iff {α : Type*} (G : SimpleGraph α) (e : Sym2 α) (v : α) :
    G.toGMGraph.Inc e v ↔ e ∈ G.edgeSet ∧ v ∈ e := by
  constructor
  · rintro ⟨w, hlink⟩
    rw [Graph.ofSimpleGraph_isLink] at hlink
    rcases hlink with ⟨rfl, he⟩
    exact ⟨he, Sym2.mem_mk_left v w⟩
  · rintro ⟨he, hv⟩
    rcases Sym2.mem_iff_exists.mp hv with ⟨w, rfl⟩
    exact ⟨w, (Graph.ofSimpleGraph_isLink G _ _ _).mpr ⟨rfl, he⟩⟩

/-- Cardinality of `E(G.toGMGraph)` for a finite simple graph `G : SimpleGraph (Fin n)`. -/
theorem ncard_edgeSet_toGMGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    E(G.toGMGraph).ncard = G.edgeFinset.card := by
  change G.edgeSet.ncard = G.edgeFinset.card
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]

/-- Cardinality of `V(G.toGMGraph)` for a finite simple graph `G : SimpleGraph (Fin n)`. -/
theorem ncard_vertexSet_toGMGraph {n : ℕ} (G : SimpleGraph (Fin n)) :
    V(G.toGMGraph).ncard = n := by
  change (Set.univ : Set (Fin n)).ncard = n
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- For a simple graph `G : SimpleGraph (Fin n)`, `treeEdgeOrder G T τ f` equals
`GM13.graphBranchEdgeOrder G.toGMGraph T τ f`. -/
theorem treeEdgeOrder_eq_graphBranchEdgeOrder {n t : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : SimpleGraph (Fin t)) (τ : Sym2 (Fin n) → Fin t) (f : Sym2 (Fin t)) :
    treeEdgeOrder G T τ f = GM13.graphBranchEdgeOrder G.toGMGraph T τ f := by
  unfold treeEdgeOrder GM13.graphBranchEdgeOrder
  have hset : (↑(treeEdgeCutVerts G T τ f) : Set (Fin n)) =
      {v ∈ V(G.toGMGraph) | ∃ f₁ ∈ E(G.toGMGraph), ∃ f₂ ∈ E(G.toGMGraph),
        ¬ (T.deleteEdges {f}).Reachable (τ f₁) (τ f₂) ∧
        G.toGMGraph.Inc f₁ v ∧ G.toGMGraph.Inc f₂ v} := by
    ext v
    have hV : V(G.toGMGraph) = Set.univ := rfl
    have hE : E(G.toGMGraph) = G.edgeSet := rfl
    simp only [Finset.mem_coe, mem_treeEdgeCutVerts, hV, Set.mem_univ, hE,
      toGMGraph_inc_iff, true_and, SimpleGraph.mem_edgeFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨e₁, he₁, e₂, he₂, hv₁, hv₂, hnr⟩
      exact ⟨e₁, he₁, e₂, he₂, hnr, ⟨he₁, hv₁⟩, ⟨he₂, hv₂⟩⟩
    · rintro ⟨e₁, he₁, e₂, he₂, hnr, ⟨_, hv₁⟩, ⟨_, hv₂⟩⟩
      exact ⟨e₁, he₁, e₂, he₂, hv₁, hv₂, hnr⟩
  rw [← hset, Set.ncard_coe_finset]

/-- Equivalence between `IsBranchDecompOfWidthLe B G T τ` and `GM13`'s
`IsGraphBranchDecomposition G.toGMGraph T τ ∧ graphBranchDecompWidth G.toGMGraph T τ ≤ B`
(with `0 < t`). -/
theorem isBranchDecompOfWidthLe_iff_gm13 {n t : ℕ} (B : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (τ : Sym2 (Fin n) → Fin t) :
    IsBranchDecompOfWidthLe B G T τ ↔
      0 < t ∧ GM13.IsGraphBranchDecomposition G.toGMGraph T τ ∧
        GM13.graphBranchDecompWidth G.toGMGraph T τ ≤ B := by
  have hE : E(G.toGMGraph) = (G.edgeFinset : Set (Sym2 (Fin n))) := by
    rw [G.coe_edgeFinset]; rfl
  constructor
  · rintro ⟨hcub, hbij, hord⟩
    have htern : GM10.IsTernaryTree T := (isCubicOrLeafTree_iff_isTernaryTree T).mp hcub
    have hne : Nonempty (Fin t) := htern.isTree.connected.nonempty
    have ht_pos : 0 < t := Fin.pos_iff_nonempty.mpr hne
    have hbij' : Set.BijOn τ E(G.toGMGraph) (GM10.leafSet T) := by
      rwa [hE, ← coe_treeLeaves_eq_leafSet T hcub]
    refine ⟨ht_pos, ⟨Or.inr htern, hbij'⟩,
      (graphBranchDecompWidth_le_iff G.toGMGraph T τ B).mpr ?_⟩
    intro f hf
    rw [← treeEdgeOrder_eq_graphBranchEdgeOrder]
    exact hord f (T.mem_edgeFinset.mpr hf)
  · rintro ⟨ht_pos, hbd, hw⟩
    have hne : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht_pos
    have htern : GM10.IsTernaryTree T := by
      rcases hbd.isTernaryOrEmpty with hempty | htern
      · exact False.elim (not_nonempty_iff.mpr hempty hne)
      · exact htern
    have hcub : IsCubicOrLeafTree T := (isCubicOrLeafTree_iff_isTernaryTree T).mpr htern
    have hbij : Set.BijOn τ (G.edgeFinset : Set (Sym2 (Fin n))) (treeLeaves T : Set (Fin t)) := by
      have h := hbd.bijOn
      rwa [hE, ← coe_treeLeaves_eq_leafSet T hcub] at h
    refine ⟨hcub, hbij, fun f hf => ?_⟩
    rw [treeEdgeOrder_eq_graphBranchEdgeOrder]
    exact (graphBranchDecompWidth_le_iff G.toGMGraph T τ B).mp hw f (T.mem_edgeFinset.mp hf)

/-- Forward direction of Goal 1 for simple graphs: `IsBranchDecompOfWidthLe B G T τ` gives
`GM13.IsGraphBranchDecomposition G.toGMGraph T τ`. -/
theorem IsBranchDecompOfWidthLe.isGraphBranchDecomposition {n t : ℕ} {B : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj] {τ : Sym2 (Fin n) → Fin t}
    (h : IsBranchDecompOfWidthLe B G T τ) :
    GM13.IsGraphBranchDecomposition G.toGMGraph T τ :=
  ((isBranchDecompOfWidthLe_iff_gm13 B G T τ).mp h).2.1

/-- Forward direction of Goal 1 for simple graphs: `IsBranchDecompOfWidthLe B G T τ` gives
`GM13.graphBranchDecompWidth G.toGMGraph T τ ≤ B`. -/
theorem IsBranchDecompOfWidthLe.graphBranchDecompWidth_le {n t : ℕ} {B : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj] {τ : Sym2 (Fin n) → Fin t}
    (h : IsBranchDecompOfWidthLe B G T τ) :
    GM13.graphBranchDecompWidth G.toGMGraph T τ ≤ B :=
  ((isBranchDecompOfWidthLe_iff_gm13 B G T τ).mp h).2.2

/-- Forward direction of Goal 1 for simple graphs: `IsBranchDecompOfWidthLe B G T τ` implies
`GM13.GraphBranchWidthLE G.toGMGraph B`. -/
theorem IsBranchDecompOfWidthLe.graphBranchWidthLE {n t : ℕ} {B : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj] {τ : Sym2 (Fin n) → Fin t}
    (h : IsBranchDecompOfWidthLe B G T τ) :
    GM13.GraphBranchWidthLE G.toGMGraph B :=
  Or.inr ⟨Fin t, inferInstance, T, τ, h.isGraphBranchDecomposition, h.graphBranchDecompWidth_le⟩

/-- Converse direction of Goal 1 for simple graphs: any `GM13` branch-decomposition `(T, τ)` of
`G.toGMGraph` of width `≤ B` on a non-empty index type `ι` gives `IsBranchDecompOfWidthLe B G
(parentTree t p) τ'` for a rooted parent-array tree `parentTree t p`. -/
theorem exists_parentTree_isBranchDecompOfWidthLe_of_gm13 {n : ℕ} {B : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [Nonempty ι] (T : SimpleGraph ι) (τ : Sym2 (Fin n) → ι)
    (hbd : GM13.IsGraphBranchDecomposition G.toGMGraph T τ)
    (hw : GM13.graphBranchDecompWidth G.toGMGraph T τ ≤ B) :
    ∃ (t : ℕ) (p : ℕ → ℕ) (τ' : Sym2 (Fin n) → Fin t),
      0 < t ∧ t ≤ 2 * G.edgeFinset.card ∧ p 0 = 0 ∧ (∀ z, 0 < z → z < t → p z < z) ∧
      IsBranchDecompOfWidthLe B G (parentTree t p) τ' := by
  have htern : GM10.IsTernaryTree T := by
    rcases hbd.isTernaryOrEmpty with hempty | htern
    · exact False.elim (not_nonempty_iff.mpr hempty ‹Nonempty ι›)
    · exact htern
  let t := Fintype.card ι
  have ht_pos : 0 < t := Fintype.card_pos
  obtain ⟨p, hp0, hp_lt, ⟨φ⟩⟩ := exists_iso_parentTree_of_isTree_card t ht_pos T htern.isTree rfl
  let τ' : Sym2 (Fin n) → Fin t := φ ∘ τ
  have hbd' : GM13.IsGraphBranchDecomposition G.toGMGraph (parentTree t p) τ' :=
    isGraphBranchDecomposition_of_iso φ hbd
  have hw' : GM13.graphBranchDecompWidth G.toGMGraph (parentTree t p) τ' ≤ B := by
    rw [graphBranchDecompWidth_of_iso G.toGMGraph φ τ]
    exact hw
  have hisbd : IsBranchDecompOfWidthLe B G (parentTree t p) τ' :=
    (isBranchDecompOfWidthLe_iff_gm13 B G (parentTree t p) τ').mpr ⟨ht_pos, hbd', hw'⟩
  have hleaves_card : (treeLeaves (parentTree t p)).card = G.edgeFinset.card := by
    symm
    refine Finset.card_bij (fun e _ => τ' e) ?_ ?_ ?_
    · intro e he
      exact hisbd.2.1.1 he
    · intro e₁ he₁ e₂ he₂ heq
      exact hisbd.2.1.2.1 he₁ he₂ heq
    · intro v hv
      rcases hisbd.2.1.2.2 hv with ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
  have ht_le : t ≤ 2 * G.edgeFinset.card := by
    have h := t_le_two_mul_card_treeLeaves ht_pos hp_lt hisbd.1
    omega
  exact ⟨t, p, τ', ht_pos, ht_le, hp0, hp_lt, hisbd⟩

/-- Full equivalence between `GM13.GraphBranchWidthLE G.toGMGraph B` and the existence of a
`parentTree` branch-decomposition `IsBranchDecompOfWidthLe B G (parentTree t p) τ` (or `|E(G)| ≤ 1`). -/
theorem graphBranchWidthLE_toGMGraph_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B : ℕ) :
    GM13.GraphBranchWidthLE G.toGMGraph B ↔
      G.edgeFinset.card ≤ 1 ∨
      ∃ (t : ℕ) (p : ℕ → ℕ) (τ : Sym2 (Fin n) → Fin t),
        0 < t ∧ t ≤ 2 * G.edgeFinset.card ∧ p 0 = 0 ∧ (∀ z, 0 < z → z < t → p z < z) ∧
        IsBranchDecompOfWidthLe B G (parentTree t p) τ := by
  constructor
  · rintro (hle1 | ⟨ι, hfin, T, τ, hbd, hw⟩)
    · rw [ncard_edgeSet_toGMGraph] at hle1
      exact Or.inl hle1
    · rcases isEmpty_or_nonempty ι with hempty | hne
      · have hleaf_emp : GM10.leafSet T = ∅ := Set.eq_empty_of_isEmpty _
        have hE_emp : E(G.toGMGraph) = ∅ := by
          rw [← Set.image_eq_empty (f := τ), hbd.bijOn.image_eq, hleaf_emp]
        have hle1 : G.edgeFinset.card ≤ 1 := by
          rw [← ncard_edgeSet_toGMGraph, hE_emp, Set.ncard_empty]
          exact Nat.zero_le _
        exact Or.inl hle1
      · exact Or.inr (exists_parentTree_isBranchDecompOfWidthLe_of_gm13 G T τ hbd hw)
  · rintro (hle1 | ⟨t, p, τ, _, _, _, _, hbd⟩)
    · refine Or.inl ?_
      rwa [ncard_edgeSet_toGMGraph]
    · exact hbd.graphBranchWidthLE


/-! ### Section 4: Goal 1 for `ComputeDigraph`, `MultiDigraph`, and `IsValidBranchDecompCode` -/

/-- Incidence in `D.toGraph` for any `D : GM13.Digraph α β`. -/
theorem digraphToGraph_inc_iff {α β : Type*} (D : GM13.Digraph α β) (e : β) (v : α) :
    D.toGraph.Inc e v ↔ e ∈ D.edgeSet ∧ (D.head e = v ∨ D.tail e = v) := by
  constructor
  · rintro ⟨w, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨he, Or.inl rfl⟩
    · exact ⟨he, Or.inr rfl⟩
  · rintro ⟨he, rfl | rfl⟩
    · exact ⟨D.tail e, he, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨D.head e, he, Or.inr ⟨rfl, rfl⟩⟩

@[simp]
theorem mem_digraphTreeEdgeCutVerts {t : ℕ} (G : ComputeDigraph)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin G.numEdges → Fin t) (f : Sym2 (Fin t)) (w : Fin G.numVerts) :
    w ∈ digraphTreeEdgeCutVerts G T τ f ↔
      ∃ e₁ : Fin G.numEdges, ∃ e₂ : Fin G.numEdges,
        digraphIncident G w e₁ ∧ digraphIncident G w e₂ ∧
        ¬ (T.deleteEdges {f}).Reachable (τ e₁) (τ e₂) := by
  simp [digraphTreeEdgeCutVerts]

/-- Lift a leaf assignment `τ : Fin D.numEdges → Fin t` along an edge equivalence
`eEquiv : Fin D.numEdges ≃ D_gm.edgeSet`. -/
noncomputable def tauToGM {β : Type*} {D : ComputeDigraph} {D_gm : GM13.Digraph ℕ β}
    (eEquiv : Fin D.numEdges ≃ D_gm.edgeSet) {t : ℕ} (ht : 0 < t)
    (τ : Fin D.numEdges → Fin t) (e : β) : Fin t :=
  open Classical in
  if he : e ∈ D_gm.edgeSet then τ (eEquiv.symm ⟨e, he⟩) else ⟨0, ht⟩

@[simp]
theorem tauToGM_apply_equiv {β : Type*} {D : ComputeDigraph} {D_gm : GM13.Digraph ℕ β}
    (eEquiv : Fin D.numEdges ≃ D_gm.edgeSet) {t : ℕ} (ht : 0 < t)
    (τ : Fin D.numEdges → Fin t) (i : Fin D.numEdges) :
    tauToGM eEquiv ht τ (eEquiv i).1 = τ i := by
  classical
  unfold tauToGM
  have he : (eEquiv i).1 ∈ D_gm.edgeSet := (eEquiv i).2
  simp only [he, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]

/-- When `D : ComputeDigraph` and `D_gm : GM13.Digraph ℕ β` have matching vertex set
`{u : ℕ | u < D.numVerts}` and an endpoint-preserving edge bijection
`eEquiv : Fin D.numEdges ≃ D_gm.edgeSet`, `digraphTreeEdgeOrder` on `D` equals
`GM13.graphBranchEdgeOrder` on `D_gm.toGraph`. -/
theorem digraphTreeEdgeOrder_eq_graphBranchEdgeOrder_of_equiv
    {β : Type*} {D : ComputeDigraph} {D_gm : GM13.Digraph ℕ β}
    (hV : ∀ u : ℕ, u ∈ D_gm.vertexSet ↔ u < D.numVerts)
    (eEquiv : Fin D.numEdges ≃ D_gm.edgeSet)
    (hhead : ∀ i : Fin D.numEdges, D_gm.head (eEquiv i).1 = (D.head i).1)
    (htail : ∀ i : Fin D.numEdges, D_gm.tail (eEquiv i).1 = (D.tail i).1)
    {t : ℕ} (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin D.numEdges → Fin t)
    (f : Sym2 (Fin t)) (τ_gm : β → Fin t)
    (hτ_eq : ∀ i : Fin D.numEdges, τ_gm (eEquiv i).1 = τ i) :
    digraphTreeEdgeOrder D T τ f = GM13.graphBranchEdgeOrder D_gm.toGraph T τ_gm f := by
  unfold digraphTreeEdgeOrder GM13.graphBranchEdgeOrder
  have hinc : ∀ (i : Fin D.numEdges) (v : Fin D.numVerts),
      D_gm.toGraph.Inc (eEquiv i).1 v.1 ↔ digraphIncident D v i := by
    intro i v
    rw [digraphToGraph_inc_iff]
    have he : (eEquiv i).1 ∈ D_gm.edgeSet := (eEquiv i).2
    rw [and_iff_right he, hhead i, htail i]
    unfold digraphIncident
    simp only [Fin.ext_iff]
  have himg : Fin.val '' (↑(digraphTreeEdgeCutVerts D T τ f) : Set (Fin D.numVerts)) =
      {u ∈ V(D_gm.toGraph) | ∃ f₁ ∈ E(D_gm.toGraph), ∃ f₂ ∈ E(D_gm.toGraph),
        ¬ (T.deleteEdges {f}).Reachable (τ_gm f₁) (τ_gm f₂) ∧
        D_gm.toGraph.Inc f₁ u ∧ D_gm.toGraph.Inc f₂ u} := by
    ext u
    simp only [Set.mem_image, Finset.mem_coe, mem_digraphTreeEdgeCutVerts, Set.mem_ofPred_eq]
    have hVD : V(D_gm.toGraph) = D_gm.vertexSet := rfl
    have hED : E(D_gm.toGraph) = D_gm.edgeSet := rfl
    rw [hVD, hED, hV]
    constructor
    · rintro ⟨v, ⟨i₁, i₂, hv₁, hv₂, hnr⟩, rfl⟩
      refine ⟨v.2, (eEquiv i₁).1, (eEquiv i₁).2, (eEquiv i₂).1, (eEquiv i₂).2, ?_,
        (hinc i₁ v).mpr hv₁, (hinc i₂ v).mpr hv₂⟩
      rwa [hτ_eq i₁, hτ_eq i₂]
    · rintro ⟨hu, e₁, he₁, e₂, he₂, hnr, hinc₁, hinc₂⟩
      let v : Fin D.numVerts := ⟨u, hu⟩
      let i₁ : Fin D.numEdges := eEquiv.symm ⟨e₁, he₁⟩
      let i₂ : Fin D.numEdges := eEquiv.symm ⟨e₂, he₂⟩
      have he₁_eq : (eEquiv i₁).1 = e₁ := congrArg Subtype.val (eEquiv.apply_symm_apply ⟨e₁, he₁⟩)
      have he₂_eq : (eEquiv i₂).1 = e₂ := congrArg Subtype.val (eEquiv.apply_symm_apply ⟨e₂, he₂⟩)
      refine ⟨v, ⟨i₁, i₂, ?_, ?_, ?_⟩, rfl⟩
      · exact (hinc i₁ v).mp (by simpa [he₁_eq, v] using hinc₁)
      · exact (hinc i₂ v).mp (by simpa [he₂_eq, v] using hinc₂)
      · have hτ₁ : τ i₁ = τ_gm e₁ := by rw [← hτ_eq i₁, he₁_eq]
        have hτ₂ : τ i₂ = τ_gm e₂ := by rw [← hτ_eq i₂, he₂_eq]
        rwa [hτ₁, hτ₂]
  rw [← himg, Set.ncard_image_of_injective _ Fin.val_injective, Set.ncard_coe_finset]

/-- Equivalence between `IsDigraphBranchDecompOfWidthLe B D T τ` and
`GM13`'s `IsGraphBranchDecomposition D_gm.toGraph T τ_gm ∧ graphBranchDecompWidth D_gm.toGraph T τ_gm ≤ B`
(with `0 < t`). -/
theorem isDigraphBranchDecompOfWidthLe_iff_gm13_of_equiv
    {β : Type*} {D : ComputeDigraph} {D_gm : GM13.Digraph ℕ β}
    (hV : ∀ u : ℕ, u ∈ D_gm.vertexSet ↔ u < D.numVerts)
    (eEquiv : Fin D.numEdges ≃ D_gm.edgeSet)
    (hhead : ∀ i : Fin D.numEdges, D_gm.head (eEquiv i).1 = (D.head i).1)
    (htail : ∀ i : Fin D.numEdges, D_gm.tail (eEquiv i).1 = (D.tail i).1)
    {t : ℕ} (B : ℕ) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin D.numEdges → Fin t) (τ_gm : β → Fin t)
    (hτ_eq : ∀ i : Fin D.numEdges, τ_gm (eEquiv i).1 = τ i) :
    IsDigraphBranchDecompOfWidthLe B D T τ ↔
      0 < t ∧ GM13.IsGraphBranchDecomposition D_gm.toGraph T τ_gm ∧
        GM13.graphBranchDecompWidth D_gm.toGraph T τ_gm ≤ B := by
  have hED : E(D_gm.toGraph) = D_gm.edgeSet := rfl
  have hbij_iff : ∀ S : Set (Fin t),
      Set.BijOn τ Set.univ S ↔ Set.BijOn τ_gm E(D_gm.toGraph) S := by
    intro S
    rw [hED]
    refine ⟨fun ⟨hmaps, hinj, hsurj⟩ => ⟨?_, ?_, ?_⟩,
      fun ⟨hmaps, hinj, hsurj⟩ => ⟨?_, ?_, ?_⟩⟩
    · intro e he
      let i := eEquiv.symm ⟨e, he⟩
      have he_eq : (eEquiv i).1 = e := congrArg Subtype.val (eEquiv.apply_symm_apply ⟨e, he⟩)
      rw [← he_eq, hτ_eq i]
      exact hmaps (Set.mem_univ i)
    · intro e₁ he₁ e₂ he₂ heq
      let i₁ := eEquiv.symm ⟨e₁, he₁⟩
      let i₂ := eEquiv.symm ⟨e₂, he₂⟩
      have he₁_eq : (eEquiv i₁).1 = e₁ := congrArg Subtype.val (eEquiv.apply_symm_apply ⟨e₁, he₁⟩)
      have he₂_eq : (eEquiv i₂).1 = e₂ := congrArg Subtype.val (eEquiv.apply_symm_apply ⟨e₂, he₂⟩)
      rw [← he₁_eq, ← he₂_eq, hτ_eq i₁, hτ_eq i₂] at heq
      have hi : i₁ = i₂ := hinj (Set.mem_univ i₁) (Set.mem_univ i₂) heq
      rw [← he₁_eq, ← he₂_eq, hi]
    · intro v hv
      rcases hsurj hv with ⟨i, _, rfl⟩
      exact ⟨(eEquiv i).1, (eEquiv i).2, hτ_eq i⟩
    · intro i _
      rw [← hτ_eq i]
      exact hmaps (eEquiv i).2
    · intro i₁ _ i₂ _ heq
      rw [← hτ_eq i₁, ← hτ_eq i₂] at heq
      have hsub : eEquiv i₁ = eEquiv i₂ :=
        Subtype.ext (hinj (eEquiv i₁).2 (eEquiv i₂).2 heq)
      exact eEquiv.injective hsub
    · intro v hv
      rcases hsurj hv with ⟨e, he, rfl⟩
      let i := eEquiv.symm ⟨e, he⟩
      have he_eq : (eEquiv i).1 = e := congrArg Subtype.val (eEquiv.apply_symm_apply ⟨e, he⟩)
      refine ⟨i, Set.mem_univ i, ?_⟩
      rw [← hτ_eq i, he_eq]
  constructor
  · rintro ⟨hcub, hbij, hord⟩
    have htern : GM10.IsTernaryTree T := (isCubicOrLeafTree_iff_isTernaryTree T).mp hcub
    have hne : Nonempty (Fin t) := htern.isTree.connected.nonempty
    have ht_pos : 0 < t := Fin.pos_iff_nonempty.mpr hne
    have hbij' : Set.BijOn τ_gm E(D_gm.toGraph) (GM10.leafSet T) := by
      rw [← coe_treeLeaves_eq_leafSet T hcub]
      exact (hbij_iff _).mp hbij
    refine ⟨ht_pos, ⟨Or.inr htern, hbij'⟩,
      (graphBranchDecompWidth_le_iff D_gm.toGraph T τ_gm B).mpr ?_⟩
    intro f hf
    rw [← digraphTreeEdgeOrder_eq_graphBranchEdgeOrder_of_equiv hV eEquiv hhead htail T τ f τ_gm hτ_eq]
    exact hord f (T.mem_edgeFinset.mpr hf)
  · rintro ⟨ht_pos, hbd, hw⟩
    have hne : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht_pos
    have htern : GM10.IsTernaryTree T := by
      rcases hbd.isTernaryOrEmpty with hempty | htern
      · exact False.elim (not_nonempty_iff.mpr hempty hne)
      · exact htern
    have hcub : IsCubicOrLeafTree T := (isCubicOrLeafTree_iff_isTernaryTree T).mpr htern
    have hbij : Set.BijOn τ Set.univ (treeLeaves T : Set (Fin t)) := by
      refine (hbij_iff _).mpr ?_
      rw [coe_treeLeaves_eq_leafSet T hcub]
      exact hbd.bijOn
    refine ⟨hcub, hbij, fun f hf => ?_⟩
    rw [digraphTreeEdgeOrder_eq_graphBranchEdgeOrder_of_equiv hV eEquiv hhead htail T τ f τ_gm hτ_eq]
    exact (graphBranchDecompWidth_le_iff D_gm.toGraph T τ_gm B).mp hw f (T.mem_edgeFinset.mp hf)

/-- Canonical edge equivalence `Fin D.numEdges ≃ D.toGMDigraph.edgeSet` for `D : ComputeDigraph`. -/
def ComputeDigraph.edgeEquiv (D : ComputeDigraph) : Fin D.numEdges ≃ D.toGMDigraph.edgeSet where
  toFun i := ⟨i.1, i.2⟩
  invFun e := ⟨e.1, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ComputeDigraph.mem_vertexSet_toGMDigraph (D : ComputeDigraph) (u : ℕ) :
    u ∈ D.toGMDigraph.vertexSet ↔ u < D.numVerts := Iff.rfl

theorem ComputeDigraph.head_edgeEquiv (D : ComputeDigraph) (i : Fin D.numEdges) :
    D.toGMDigraph.head (D.edgeEquiv i).1 = (D.head i).1 := by
  change (if h : i.1 < D.numEdges then (D.head ⟨i.1, h⟩).1 else 0) = (D.head i).1
  simp [i.2]

theorem ComputeDigraph.tail_edgeEquiv (D : ComputeDigraph) (i : Fin D.numEdges) :
    D.toGMDigraph.tail (D.edgeEquiv i).1 = (D.tail i).1 := by
  change (if h : i.1 < D.numEdges then (D.tail ⟨i.1, h⟩).1 else 0) = (D.tail i).1
  simp [i.2]

/-- Equivalence between `IsDigraphBranchDecompOfWidthLe B D T τ` and `GM13` branch-decompositions
of `D.toGMDigraph.toGraph`. -/
theorem isDigraphBranchDecompOfWidthLe_iff_toGMDigraph {t : ℕ} (ht : 0 < t) (B : ℕ)
    (D : ComputeDigraph) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin D.numEdges → Fin t) :
    IsDigraphBranchDecompOfWidthLe B D T τ ↔
      GM13.IsGraphBranchDecomposition D.toGMDigraph.toGraph T (tauToGM D.edgeEquiv ht τ) ∧
        GM13.graphBranchDecompWidth D.toGMDigraph.toGraph T (tauToGM D.edgeEquiv ht τ) ≤ B := by
  rw [isDigraphBranchDecompOfWidthLe_iff_gm13_of_equiv D.mem_vertexSet_toGMDigraph D.edgeEquiv
    D.head_edgeEquiv D.tail_edgeEquiv B T τ (tauToGM D.edgeEquiv ht τ)
    (tauToGM_apply_equiv D.edgeEquiv ht τ), and_iff_right ht]

/-- Forward direction of Goal 1 for `ComputeDigraph`: `IsDigraphBranchDecompOfWidthLe B D T τ`
implies `GM13.GraphBranchWidthLE D.toGMDigraph.toGraph B`. -/
theorem IsDigraphBranchDecompOfWidthLe.graphBranchWidthLE {t : ℕ} {B : ℕ}
    {D : ComputeDigraph} {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Fin D.numEdges → Fin t} (h : IsDigraphBranchDecompOfWidthLe B D T τ) :
    GM13.GraphBranchWidthLE D.toGMDigraph.toGraph B := by
  have htern : GM10.IsTernaryTree T := (isCubicOrLeafTree_iff_isTernaryTree T).mp h.1
  have ht : 0 < t := Fin.pos_iff_nonempty.mpr htern.isTree.connected.nonempty
  rcases (isDigraphBranchDecompOfWidthLe_iff_toGMDigraph ht B D T τ).mp h with ⟨hbd, hw⟩
  exact Or.inr ⟨Fin t, inferInstance, T, tauToGM D.edgeEquiv ht τ, hbd, hw⟩

/-- Endpoint lemmas for `G.edgeEquiv : Fin G.toComputeDigraph.numEdges ≃ G.toGMDigraph.edgeSet`. -/
theorem MultiDigraph.mem_vertexSet_toGMDigraph {n : ℕ} (G : MultiDigraph n) (u : ℕ) :
    u ∈ G.toGMDigraph.vertexSet ↔ u < n := Iff.rfl

theorem MultiDigraph.head_edgeEquiv {n : ℕ} (G : MultiDigraph n)
    (i : Fin G.toComputeDigraph.numEdges) :
    G.toGMDigraph.head (G.edgeEquiv i).1 = (G.toComputeDigraph.head i).1 := by
  change (G.edgeEquiv i).1.2.1 = ((G.directedEdgesList[i.1]'i.2).2).1
  simpa [MultiDigraph.edgeEquiv, MultiDigraph.edgeToGMTriple] using
    congrArg Prod.snd (G.getElem_directedEdgeTriples_fst_snd i.1 i.2)

theorem MultiDigraph.tail_edgeEquiv {n : ℕ} (G : MultiDigraph n)
    (i : Fin G.toComputeDigraph.numEdges) :
    G.toGMDigraph.tail (G.edgeEquiv i).1 = (G.toComputeDigraph.tail i).1 := by
  change (G.edgeEquiv i).1.1 = ((G.directedEdgesList[i.1]'i.2).1).1
  simpa [MultiDigraph.edgeEquiv, MultiDigraph.edgeToGMTriple] using
    congrArg Prod.fst (G.getElem_directedEdgeTriples_fst_snd i.1 i.2)

/-- Equivalence between `IsDigraphBranchDecompOfWidthLe B G.toComputeDigraph T τ` and `GM13`
branch-decompositions of `G.toGMDigraph.toGraph`. -/
theorem isDigraphBranchDecompOfWidthLe_toComputeDigraph_iff_gm13
    {n t : ℕ} (ht : 0 < t) (B : ℕ) (G : MultiDigraph n)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin G.toComputeDigraph.numEdges → Fin t) :
    IsDigraphBranchDecompOfWidthLe B G.toComputeDigraph T τ ↔
      GM13.IsGraphBranchDecomposition G.toGMDigraph.toGraph T (tauToGM G.edgeEquiv ht τ) ∧
        GM13.graphBranchDecompWidth G.toGMDigraph.toGraph T (tauToGM G.edgeEquiv ht τ) ≤ B := by
  rw [isDigraphBranchDecompOfWidthLe_iff_gm13_of_equiv G.mem_vertexSet_toGMDigraph G.edgeEquiv
    G.head_edgeEquiv G.tail_edgeEquiv B T τ (tauToGM G.edgeEquiv ht τ)
    (tauToGM_apply_equiv G.edgeEquiv ht τ), and_iff_right ht]

/-- Directed edge triples `(u.1, v.1, k)` enumerated in the order of `G.activePairsList`
(matching `G.edgeListWithMult` and `G.toMultiComputeDigraph`). -/
def MultiDigraph.multiEdgeTriples {n : ℕ} (G : MultiDigraph n) : List (ℕ × ℕ × ℕ) :=
  G.activePairsList.flatMap (fun p =>
    (List.range (G.edgeMult p.1 p.2)).map (fun k => (p.1.1, p.2.1, k)))

theorem MultiDigraph.map_multiEdgeTriples {n : ℕ} (G : MultiDigraph n) :
    G.multiEdgeTriples.map (fun e => (e.1, e.2.1)) =
      G.edgeListWithMult.map (fun p => (p.1.1, p.2.1)) := by
  unfold MultiDigraph.multiEdgeTriples MultiDigraph.edgeListWithMult
  simp [List.map_flatMap, Function.comp_def]

@[simp]
theorem MultiDigraph.length_multiEdgeTriples {n : ℕ} (G : MultiDigraph n) :
    G.multiEdgeTriples.length = G.numEdges := by
  have h := congrArg List.length G.map_multiEdgeTriples
  simpa [G.length_edgeListWithMult] using h

theorem MultiDigraph.getElem_multiEdgeTriples_fst_snd {n : ℕ} (G : MultiDigraph n)
    (i : Fin G.numEdges) :
    let hi' : i.1 < G.multiEdgeTriples.length := by
      rw [G.length_multiEdgeTriples]; exact i.2
    ((G.multiEdgeTriples[i.1]'hi').1, (G.multiEdgeTriples[i.1]'hi').2.1) =
      ((G.edgeEndpoints i).1.1, (G.edgeEndpoints i).2.1) := by
  intro hi'
  have hi_len : i.1 < G.edgeListWithMult.length := by
    rw [G.length_edgeListWithMult]; exact i.2
  have h := congrArg (fun L : List (ℕ × ℕ) => L[i.1]?) G.map_multiEdgeTriples
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi_len] at h
  exact Option.some.inj h

@[simp]
theorem MultiDigraph.mem_multiEdgeTriples_iff {n : ℕ} (G : MultiDigraph n)
    (e : ℕ × ℕ × ℕ) :
    e ∈ G.multiEdgeTriples ↔ e ∈ G.toGMDigraph.edgeSet := by
  rcases e with ⟨u, v, k⟩
  simp only [MultiDigraph.multiEdgeTriples, MultiDigraph.toGMDigraph, List.mem_flatMap,
    MultiDigraph.mem_activePairsList, List.mem_map, List.mem_range, Prod.mk.injEq,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨u', v'⟩, _, k', hk', rfl, rfl, rfl⟩
    exact ⟨u'.2, v'.2, hk'⟩
  · rintro ⟨hu, hv, hk⟩
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), Nat.zero_lt_of_lt hk, k, hk, rfl, rfl, rfl⟩

theorem MultiDigraph.nodup_multiEdgeTriples {n : ℕ} (G : MultiDigraph n) :
    G.multiEdgeTriples.Nodup := by
  unfold MultiDigraph.multiEdgeTriples
  refine List.nodup_flatMap.2 ⟨fun p _ => ?_, G.nodup_activePairsList.imp fun hne x hx₁ hx₂ => ?_⟩
  · refine List.Nodup.map (fun k₁ k₂ h => ?_) List.nodup_range
    simpa using h
  · simp only [List.mem_map, List.mem_range] at hx₁ hx₂
    rcases hx₁ with ⟨_, _, rfl⟩
    rcases hx₂ with ⟨_, _, heq⟩
    apply hne
    ext
    · exact (Prod.mk.inj heq).1.symm
    · exact (Prod.mk.inj (Prod.mk.inj heq).2).1.symm

/-- Map an edge index `i : Fin G.numEdges` to the corresponding edge triple in
`G.toGMDigraph.edgeSet`. -/
def MultiDigraph.multiEdgeToGMTriple {n : ℕ} (G : MultiDigraph n)
    (i : Fin G.numEdges) : G.toGMDigraph.edgeSet :=
  ⟨G.multiEdgeTriples[i.1]'(by rw [G.length_multiEdgeTriples]; exact i.2),
   (G.mem_multiEdgeTriples_iff _).mp (List.getElem_mem _)⟩

theorem MultiDigraph.bijective_multiEdgeToGMTriple {n : ℕ} (G : MultiDigraph n) :
    Function.Bijective G.multiEdgeToGMTriple := by
  constructor
  · intro i j heq
    have hval := congrArg Subtype.val heq
    dsimp [MultiDigraph.multiEdgeToGMTriple] at hval
    have hinj := (G.nodup_multiEdgeTriples.getElem_inj_iff
      (i := i.1) (j := j.1)
      (hi := by rw [G.length_multiEdgeTriples]; exact i.2)
      (hj := by rw [G.length_multiEdgeTriples]; exact j.2)).mp hval
    exact Fin.ext hinj
  · rintro ⟨e, he⟩
    have hmem : e ∈ G.multiEdgeTriples := (G.mem_multiEdgeTriples_iff e).mpr he
    rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, heq⟩
    refine ⟨⟨idx, by rw [← G.length_multiEdgeTriples]; exact hidx⟩, Subtype.ext heq⟩

/-- Canonical bijection between `Fin G.numEdges` (`G.toMultiComputeDigraph`) and
`G.toGMDigraph.edgeSet`. -/
noncomputable def MultiDigraph.multiEdgeEquiv {n : ℕ} (G : MultiDigraph n) :
    Fin G.numEdges ≃ G.toGMDigraph.edgeSet :=
  Equiv.ofBijective G.multiEdgeToGMTriple G.bijective_multiEdgeToGMTriple

@[simp]
theorem MultiDigraph.multiEdgeEquiv_apply {n : ℕ} (G : MultiDigraph n)
    (i : Fin G.numEdges) :
    G.multiEdgeEquiv i = G.multiEdgeToGMTriple i :=
  rfl

theorem MultiDigraph.head_multiEdgeEquiv {n : ℕ} (G : MultiDigraph n)
    (i : Fin G.numEdges) :
    G.toGMDigraph.head (G.multiEdgeEquiv i).1 = (G.toMultiComputeDigraph.head i).1 := by
  change (G.multiEdgeEquiv i).1.2.1 = (G.edgeEndpoints i).2.1
  simpa [MultiDigraph.multiEdgeEquiv, MultiDigraph.multiEdgeToGMTriple] using
    congrArg Prod.snd (G.getElem_multiEdgeTriples_fst_snd i)

theorem MultiDigraph.tail_multiEdgeEquiv {n : ℕ} (G : MultiDigraph n)
    (i : Fin G.numEdges) :
    G.toGMDigraph.tail (G.multiEdgeEquiv i).1 = (G.toMultiComputeDigraph.tail i).1 := by
  change (G.multiEdgeEquiv i).1.1 = (G.edgeEndpoints i).1.1
  simpa [MultiDigraph.multiEdgeEquiv, MultiDigraph.multiEdgeToGMTriple] using
    congrArg Prod.fst (G.getElem_multiEdgeTriples_fst_snd i)

/-- Leaf map on `G.toGMDigraph.toGraph` induced by `τ : Fin G.numEdges → Fin t`. -/
noncomputable abbrev multiTauGM {n t : ℕ} (G : MultiDigraph n) (ht : 0 < t)
    (τ : Fin G.numEdges → Fin t) (e : ℕ × ℕ × ℕ) : Fin t :=
  tauToGM (D := G.toMultiComputeDigraph) G.multiEdgeEquiv ht τ e

/-- Equivalence between `IsMultiBranchDecompOfWidthLe B G T τ` and `GM13` branch-decompositions of
`G.toGMDigraph.toGraph`. -/
theorem isMultiBranchDecompOfWidthLe_iff_gm13 {n t : ℕ} (B : ℕ) (G : MultiDigraph n)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin G.numEdges → Fin t) (ht : 0 < t) :
    IsMultiBranchDecompOfWidthLe B G T τ ↔
      GM13.IsGraphBranchDecomposition G.toGMDigraph.toGraph T (multiTauGM G ht τ) ∧
        GM13.graphBranchDecompWidth G.toGMDigraph.toGraph T (multiTauGM G ht τ) ≤ B := by
  unfold IsMultiBranchDecompOfWidthLe multiTauGM
  rw [isDigraphBranchDecompOfWidthLe_iff_gm13_of_equiv
    (D := G.toMultiComputeDigraph) G.mem_vertexSet_toGMDigraph G.multiEdgeEquiv
    G.head_multiEdgeEquiv G.tail_multiEdgeEquiv B T τ
    (tauToGM (D := G.toMultiComputeDigraph) G.multiEdgeEquiv ht τ)
    (tauToGM_apply_equiv (D := G.toMultiComputeDigraph) G.multiEdgeEquiv ht τ), and_iff_right ht]

/-- Equivalence between `IsMultiBranchDecompOfWidthLe B G T (fun i => τ_gm (G.multiEdgeEquiv i).1)`
and `GM13` branch-decompositions of `G.toGMDigraph.toGraph` for any `τ_gm : ℕ × ℕ × ℕ → Fin t`. -/
theorem isMultiBranchDecompOfWidthLe_of_gm13_iff {n t : ℕ} (ht : 0 < t) (B : ℕ)
    (G : MultiDigraph n) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ_gm : ℕ × ℕ × ℕ → Fin t) :
    IsMultiBranchDecompOfWidthLe B G T (fun i => τ_gm (G.multiEdgeEquiv i).1) ↔
      GM13.IsGraphBranchDecomposition G.toGMDigraph.toGraph T τ_gm ∧
        GM13.graphBranchDecompWidth G.toGMDigraph.toGraph T τ_gm ≤ B := by
  unfold IsMultiBranchDecompOfWidthLe
  rw [isDigraphBranchDecompOfWidthLe_iff_gm13_of_equiv
    (D := G.toMultiComputeDigraph) G.mem_vertexSet_toGMDigraph G.multiEdgeEquiv
    G.head_multiEdgeEquiv G.tail_multiEdgeEquiv B T (fun i => τ_gm (G.multiEdgeEquiv i).1) τ_gm
    (fun _ => rfl), and_iff_right ht]

/-- Canonical edge-index bijection `Fin G.toComputeDigraph.numEdges ≃ Fin G.numEdges`
relating `G.toComputeDigraph` (`directedEdgesList`) and `G.toMultiComputeDigraph` (`edgeListWithMult`). -/
noncomputable def MultiDigraph.computeToMultiEdgeEquiv {n : ℕ} (G : MultiDigraph n) :
    Fin G.toComputeDigraph.numEdges ≃ Fin G.numEdges :=
  G.edgeEquiv.trans G.multiEdgeEquiv.symm

/-- Converting a branch-decomposition `(T, τ)` of `G.toMultiComputeDigraph` (`IsMultiBranchDecompOfWidthLe`)
to one of `G.toComputeDigraph` (`IsDigraphBranchDecompOfWidthLe`) via `G.computeToMultiEdgeEquiv`. -/
theorem isDigraphBranchDecompOfWidthLe_toComputeDigraph_iff_isMultiBranchDecompOfWidthLe
    {n t : ℕ} (B : ℕ) (G : MultiDigraph n)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin G.numEdges → Fin t) :
    IsDigraphBranchDecompOfWidthLe B G.toComputeDigraph T (τ ∘ G.computeToMultiEdgeEquiv) ↔
      IsMultiBranchDecompOfWidthLe B G T τ := by
  by_cases ht : 0 < t
  · rw [isMultiBranchDecompOfWidthLe_iff_gm13 B G T τ ht]
    unfold multiTauGM
    rw [isDigraphBranchDecompOfWidthLe_iff_gm13_of_equiv
      (D := G.toComputeDigraph) G.mem_vertexSet_toGMDigraph G.edgeEquiv
      G.head_edgeEquiv G.tail_edgeEquiv B T (τ ∘ G.computeToMultiEdgeEquiv)
      (tauToGM (D := G.toMultiComputeDigraph) G.multiEdgeEquiv ht τ) ?_, and_iff_right ht]
    intro i
    change tauToGM (D := G.toMultiComputeDigraph) G.multiEdgeEquiv ht τ (G.edgeEquiv i).1 =
      τ (G.multiEdgeEquiv.symm (G.edgeEquiv i))
    have h1 : G.edgeEquiv i = G.multiEdgeEquiv (G.multiEdgeEquiv.symm (G.edgeEquiv i)) :=
      (G.multiEdgeEquiv.apply_symm_apply _).symm
    rw [congrArg Subtype.val h1, tauToGM_apply_equiv (D := G.toMultiComputeDigraph)]
  · have ht0 : t = 0 := by omega
    subst ht0
    constructor <;> rintro ⟨hcub, _⟩ <;>
      { have hpos : 0 < 0 := Fin.pos_iff_nonempty.mpr
          ((isCubicOrLeafTree_iff_isTernaryTree T).mp hcub).isTree.connected.nonempty
        omega }

/-- Leaf map on `G.toGMDigraph.toGraph` decoded from `bdCode : List ℕ`. -/
noncomputable abbrev bdTauGM {n : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (ht : 0 < bdNumTreeVerts bdCode) (e : ℕ × ℕ × ℕ) : Fin (bdNumTreeVerts bdCode) :=
  multiTauGM G ht (bdTau G bdCode ht) e

/-- Forward direction of Goal 1 for `IsValidBranchDecompCode` when `2 ≤ G.numEdges`:
`(bdTree bdCode, bdTauGM G bdCode ht)` is a `GM13` branch-decomposition of `G.toGMDigraph.toGraph`
of width `≤ B`. -/
theorem IsValidBranchDecompCode.isGraphBranchDecomposition_and_width_le {B : ℕ} {n : ℕ}
    {G : MultiDigraph n} {bdCode : List ℕ}
    (h : IsValidBranchDecompCode B G bdCode) (hge2 : 2 ≤ G.numEdges) :
    ∃ ht : 0 < bdNumTreeVerts bdCode,
      GM13.IsGraphBranchDecomposition G.toGMDigraph.toGraph (bdTree bdCode) (bdTauGM G bdCode ht) ∧
      GM13.graphBranchDecompWidth G.toGMDigraph.toGraph (bdTree bdCode) (bdTauGM G bdCode ht) ≤ B := by
  rcases h with ⟨_, _, _, ⟨hle1, _⟩ | ⟨_, ht, _, _, _, hbd⟩⟩
  · omega
  · exact ⟨ht, (isMultiBranchDecompOfWidthLe_iff_gm13 B G (bdTree bdCode) (bdTau G bdCode ht) ht).mp hbd⟩

/-- Forward direction of Goal 1 for `IsValidBranchDecompCode`: any valid code of width `≤ B`
implies `GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B`. -/
theorem IsValidBranchDecompCode.graphBranchWidthLE {B : ℕ} {n : ℕ}
    {G : MultiDigraph n} {bdCode : List ℕ}
    (h : IsValidBranchDecompCode B G bdCode) :
    GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B := by
  rcases h with ⟨_, _, _, ⟨hle1, _⟩ | ⟨_, ht, _, _, _, hbd⟩⟩
  · refine Or.inl ?_
    change G.toGMDigraph.edgeSet.ncard ≤ 1
    rwa [G.ncard_edgeSet_toGMDigraph]
  · rcases (isMultiBranchDecompOfWidthLe_iff_gm13 B G (bdTree bdCode) (bdTau G bdCode ht) ht).mp hbd with
      ⟨hbd_gm, hw_gm⟩
    exact Or.inr ⟨Fin (bdNumTreeVerts bdCode), inferInstance, bdTree bdCode,
      bdTauGM G bdCode ht, hbd_gm, hw_gm⟩

/-- Forward direction of Goal 1 for `HasBranchDecompOfWidthLe`: implies
`GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B`. -/
theorem HasBranchDecompOfWidthLe.graphBranchWidthLE {B : ℕ} {n : ℕ}
    {G : MultiDigraph n} (h : HasBranchDecompOfWidthLe G B) :
    GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B := by
  rcases h with hle1 | ⟨t, T, hdec, τ, hbd⟩
  · refine Or.inl ?_
    change G.toGMDigraph.edgeSet.ncard ≤ 1
    rwa [G.ncard_edgeSet_toGMDigraph]
  · have htern : GM10.IsTernaryTree T := (isCubicOrLeafTree_iff_isTernaryTree T).mp hbd.1
    have ht : 0 < t := Fin.pos_iff_nonempty.mpr htern.isTree.connected.nonempty
    rcases (isMultiBranchDecompOfWidthLe_iff_gm13 B G T τ ht).mp hbd with ⟨hbd_gm, hw_gm⟩
    exact Or.inr ⟨Fin t, inferInstance, T, multiTauGM G ht τ, hbd_gm, hw_gm⟩

/-- Converse direction of Goal 1 for `MultiDigraph`: any `GM13` branch-decomposition `(T, τ_gm)` of
`G.toGMDigraph.toGraph` of width `≤ B` on a finite index type `ι` has a valid code
`IsValidBranchDecompCode B G bdCode`. -/
theorem exists_isValidBranchDecompCode_of_isGraphBranchDecomposition {B : ℕ} {n : ℕ}
    (G : MultiDigraph n) {ι : Type*} [Fintype ι]
    (T : SimpleGraph ι) (τ_gm : ℕ × ℕ × ℕ → ι)
    (hbd : GM13.IsGraphBranchDecomposition G.toGMDigraph.toGraph T τ_gm)
    (hw : GM13.graphBranchDecompWidth G.toGMDigraph.toGraph T τ_gm ≤ B) :
    ∃ bdCode : List ℕ, IsValidBranchDecompCode B G bdCode := by
  by_cases hle1 : G.numEdges ≤ 1
  · exact ⟨[0, G.numEdges] ++ List.replicate G.numEdges 0, isValidBranchDecompCode_le_one B G hle1⟩
  · have hge2 : 2 ≤ G.numEdges := by omega
    rcases isEmpty_or_nonempty ι with hempty | hne
    · have hleaf_emp : GM10.leafSet T = ∅ := Set.eq_empty_of_isEmpty _
      have hE_emp : E(G.toGMDigraph.toGraph) = ∅ := by
        rw [← Set.image_eq_empty (f := τ_gm), hbd.bijOn.image_eq, hleaf_emp]
      have hm0 : G.numEdges = 0 := by
        rw [← G.ncard_edgeSet_toGMDigraph]
        change E(G.toGMDigraph.toGraph).ncard = 0
        rw [hE_emp, Set.ncard_empty]
      omega
    · have htern : GM10.IsTernaryTree T := by
        rcases hbd.isTernaryOrEmpty with hempty | htern
        · exact False.elim (not_nonempty_iff.mpr hempty hne)
        · exact htern
      let t := Fintype.card ι
      have ht_pos : 0 < t := Fintype.card_pos
      obtain ⟨p, hp0, hp_lt, ⟨φ⟩⟩ := exists_iso_parentTree_of_isTree_card t ht_pos T htern.isTree rfl
      let τ_gm' : ℕ × ℕ × ℕ → Fin t := φ ∘ τ_gm
      have hbd' : GM13.IsGraphBranchDecomposition G.toGMDigraph.toGraph (parentTree t p) τ_gm' :=
        isGraphBranchDecomposition_of_iso φ hbd
      have hw' : GM13.graphBranchDecompWidth G.toGMDigraph.toGraph (parentTree t p) τ_gm' ≤ B := by
        rw [graphBranchDecompWidth_of_iso G.toGMDigraph.toGraph φ τ_gm]
        exact hw
      let τ : Fin G.numEdges → Fin t := fun i => τ_gm' (G.multiEdgeEquiv i).1
      have hbd_multi : IsMultiBranchDecompOfWidthLe B G (parentTree t p) τ :=
        (isMultiBranchDecompOfWidthLe_of_gm13_iff ht_pos B G (parentTree t p) τ_gm').mpr ⟨hbd', hw'⟩
      have ht_le : t ≤ 2 * G.numEdges :=
        t_le_two_mul_numEdges_of_branchDecomp ht_pos hp_lt hbd_multi
      let parList : List ℕ := List.ofFn (fun z : Fin t => if z.1 = 0 then 0 else p z.1)
      let tauList : List ℕ := List.ofFn (fun e : Fin G.numEdges => (τ e).1)
      refine ⟨encBranchDecomp t G.numEdges parList tauList,
        isValidBranchDecompCode_of_ge_two B G parList tauList p τ hge2 ht_pos ht_le
          (by simp [parList]) (by simp [tauList]) (by simp [parList])
          (fun z hz hz_pos => by simp [parList, Nat.ne_of_gt hz_pos])
          hp_lt (fun e => by simp [tauList]) hbd_multi⟩

/-- Converse direction of Goal 1 for `MultiDigraph`: `GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B`
implies the existence of a valid branch-decomposition code `IsValidBranchDecompCode B G bdCode`. -/
theorem exists_isValidBranchDecompCode_of_graphBranchWidthLE {B : ℕ} {n : ℕ}
    {G : MultiDigraph n} (h : GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B) :
    ∃ bdCode : List ℕ, IsValidBranchDecompCode B G bdCode := by
  rcases h with hle1 | ⟨ι, hfin, T, τ_gm, hbd, hw⟩
  · have hle1' : G.numEdges ≤ 1 := by
      rw [← G.ncard_edgeSet_toGMDigraph]
      exact hle1
    exact ⟨[0, G.numEdges] ++ List.replicate G.numEdges 0, isValidBranchDecompCode_le_one B G hle1'⟩
  · exact exists_isValidBranchDecompCode_of_isGraphBranchDecomposition G T τ_gm hbd hw

/-- Full equivalence between `GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B` and the existence of
a valid branch-decomposition code `IsValidBranchDecompCode B G bdCode`. -/
theorem graphBranchWidthLE_toGMDigraph_iff_exists_isValidBranchDecompCode {n : ℕ}
    (G : MultiDigraph n) (B : ℕ) :
    GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B ↔
      ∃ bdCode : List ℕ, IsValidBranchDecompCode B G bdCode :=
  ⟨exists_isValidBranchDecompCode_of_graphBranchWidthLE,
   fun ⟨_, h⟩ => h.graphBranchWidthLE⟩

/-- Full equivalence between `HasBranchDecompOfWidthLe G B` and
`GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B`. -/
theorem hasBranchDecompOfWidthLe_iff_graphBranchWidthLE {n : ℕ}
    (G : MultiDigraph n) (B : ℕ) :
    HasBranchDecompOfWidthLe G B ↔ GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B :=
  ⟨HasBranchDecompOfWidthLe.graphBranchWidthLE,
   fun h => by
     rcases exists_isValidBranchDecompCode_of_graphBranchWidthLE h with ⟨_, hcode⟩
     exact hcode.hasBranchDecompOfWidthLe⟩

/-! ## Section 5: High Branch-Width Certificates from `(3.1)`, `(3.2)`, and Step (6) of `(3.3)` -/

/-- Width monotonicity of `GM13.GraphBranchWidthLE`: if `B₁ ≤ B₂` and
`GM13.GraphBranchWidthLE G B₁`, then `GM13.GraphBranchWidthLE G B₂`. -/
theorem graphBranchWidthLE_mono_width {α β : Type*} {G : Graph α β} {B₁ B₂ : ℕ}
    (hle : B₁ ≤ B₂) (h : GM13.GraphBranchWidthLE G B₁) :
    GM13.GraphBranchWidthLE G B₂ := by
  rcases h with h1 | ⟨ι, hfin, T, τ, hbd, hw⟩
  · exact Or.inl h1
  · exact Or.inr ⟨ι, hfin, T, τ, hbd, hw.trans hle⟩

/-- By `GM13.theorem_3_2_proof` (GM XIII (3.2), page 72), if `2 ≤ ω` and
`(3 * ω - 2) * n < 2 * G.edgeFinset.card` (that is, `|E(G)| > ((3/2)ω - 1)|V(G)|`), then
`¬ GM13.GraphBranchWidthLE G.toGMGraph ω`. -/
theorem not_graphBranchWidthLE_of_edge_gt {n ω : ℕ} (hω : 2 ≤ ω)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hgt : (3 * ω - 2) * n < 2 * G.edgeFinset.card) :
    ¬ GM13.GraphBranchWidthLE G.toGMGraph ω := by
  intro hbw
  have hle := (GM13.theorem_3_2_proof G.toGMGraph (Set.toFinite _) (Set.toFinite _)
    (isSimpleGraph_ofSimpleGraph G) ω hω hbw).2
  rw [ncard_edgeSet_toGMGraph, ncard_vertexSet_toGMGraph] at hle
  omega

/-- Corollary of `not_graphBranchWidthLE_of_edge_gt`: if `2 ≤ ω` and
`((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ) < (G.edgeFinset.card : ℚ)`, then
`¬ GM13.GraphBranchWidthLE G.toGMGraph (ω - 1)`. -/
theorem not_graphBranchWidthLE_sub_one_of_edge_gt_rat {n ω : ℕ} (hω : 2 ≤ ω)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hgt : ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ) < (G.edgeFinset.card : ℚ)) :
    ¬ GM13.GraphBranchWidthLE G.toGMGraph (ω - 1) := by
  have hgt_nat : (3 * ω - 2) * n < 2 * G.edgeFinset.card := by
    have hω_cast : ((3 * ω - 2 : ℕ) : ℚ) = (3 : ℚ) * (ω : ℚ) - 2 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hq : ((3 * ω - 2 : ℕ) : ℚ) * (n : ℚ) < 2 * (G.edgeFinset.card : ℚ) := by
      rw [hω_cast]
      linarith
    exact_mod_cast hq
  intro hbw1
  exact not_graphBranchWidthLE_of_edge_gt hω G hgt_nat
    (graphBranchWidthLE_mono_width (by omega) hbw1)

/-- Convert a subgraph `H ≤ G.toGMGraph` into a `SimpleGraph (Fin n)` with the same edges. -/
def simpleGraphOfSubGMGraph {n : ℕ} (G : SimpleGraph (Fin n))
    (H : Graph (Fin n) (Sym2 (Fin n))) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ s(u, v) ∈ E(H)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

lemma simpleGraphOfSubGMGraph_verts {n : ℕ} {G : SimpleGraph (Fin n)}
    {H : Graph (Fin n) (Sym2 (Fin n))} (hH : H ≤ G.toGMGraph)
    {u v : Fin n} (hadj : (simpleGraphOfSubGMGraph G H).Adj u v) :
    u ∈ V(H) ∧ v ∈ V(H) := by
  rcases (H.edge_mem_iff_exists_isLink s(u, v)).mp hadj.2 with ⟨x, y, hxy⟩
  have hxyG : G.toGMGraph.IsLink s(u, v) x y := hH.isLink_mono hxy
  rw [Graph.ofSimpleGraph_isLink] at hxyG
  have hxV : x ∈ V(H) := H.left_mem_of_isLink hxy
  have hyV : y ∈ V(H) := H.left_mem_of_isLink hxy.symm
  rcases Sym2.eq_iff.mp hxyG.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hxV, hyV⟩
  · exact ⟨hyV, hxV⟩

/-- Convert a `GM13.IsGraphSeparation G.toGMGraph A B` into a `GraphSeparation G`. -/
noncomputable def graphSeparationOfGM {n : ℕ} (G : SimpleGraph (Fin n))
    {A B : Graph (Fin n) (Sym2 (Fin n))}
    (hsep : GM06.IsGraphSeparation G.toGMGraph A B) : GraphSeparation G where
  VA := (Set.toFinite V(A)).toFinset
  VB := (Set.toFinite V(B)).toFinset
  EA := simpleGraphOfSubGMGraph G A
  EB := simpleGraphOfSubGMGraph G B
  union_verts := by
    ext u
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Finset.mem_univ, iff_true]
    have hu : u ∈ V(A) ∪ V(B) := by
      rw [hsep.2.2.1]
      exact Set.mem_univ u
    exact hu
  EA_le _ _ h := h.1
  EB_le _ _ h := h.1
  union_edges := by
    ext u v
    simp only [SimpleGraph.sup_adj, simpleGraphOfSubGMGraph]
    refine ⟨fun h => h.elim And.left And.left, fun hadj => ?_⟩
    have heG : s(u, v) ∈ E(G.toGMGraph) := hadj
    rw [← hsep.2.2.2.1] at heG
    rcases heG with heA | heB
    · exact Or.inl ⟨hadj, heA⟩
    · exact Or.inr ⟨hadj, heB⟩
  disj_edges := by
    ext u v
    simp only [SimpleGraph.inf_adj, simpleGraphOfSubGMGraph, SimpleGraph.bot_adj, iff_false]
    rintro ⟨⟨_, hA⟩, ⟨_, hB⟩⟩
    exact Set.disjoint_left.mp hsep.2.2.2.2 hA hB
  EA_verts u v hadj := by
    simp only [Set.Finite.mem_toFinset]
    exact simpleGraphOfSubGMGraph_verts hsep.1 hadj
  EB_verts u v hadj := by
    simp only [Set.Finite.mem_toFinset]
    exact simpleGraphOfSubGMGraph_verts hsep.2.1 hadj

@[simp]
theorem order_graphSeparationOfGM {n : ℕ} (G : SimpleGraph (Fin n))
    {A B : Graph (Fin n) (Sym2 (Fin n))}
    (hsep : GM06.IsGraphSeparation G.toGMGraph A B) :
    (graphSeparationOfGM G hsep).order = GM13.graphSeparationOrder A B := by
  unfold GraphSeparation.order GM13.graphSeparationOrder graphSeparationOfGM
  dsimp only
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite (V(A) ∩ V(B)))]
  congr 1
  ext u
  simp

/-- By `GM13.theorem_3_1_proof` (GM XIII (3.1), page 71), if `2 ≤ ω` and `G` has no balanced separation
of order `≤ ω` with respect to `Z`, then `¬ GM13.GraphBranchWidthLE G.toGMGraph ω`. -/
theorem not_graphBranchWidthLE_of_no_balanced_sep {n ω : ℕ} (hω : 2 ≤ ω)
    (G : SimpleGraph (Fin n)) (Z : Finset (Fin n))
    (hno_sep : ∀ sep : GraphSeparation G, sep.order ≤ ω → ¬ sep.IsBalancedQ Z) :
    ¬ GM13.GraphBranchWidthLE G.toGMGraph ω := by
  intro hbw
  obtain ⟨A, B, hsep, hord, hbalA, hbalB⟩ :=
    GM13.theorem_3_1_proof G.toGMGraph (Set.toFinite _) (Set.toFinite _) ω hω hbw
      (Z : Set (Fin n)) (Set.subset_univ _)
  let sep := graphSeparationOfGM G hsep
  have hord_sep : sep.order ≤ ω := by
    rw [order_graphSeparationOfGM]
    exact hord
  have hZA_eq : (Z \ sep.VA).card = ((Z : Set (Fin n)) \ V(A)).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    congr 1
    ext u
    dsimp [sep, graphSeparationOfGM]
    simp
  have hZB_eq : (Z \ sep.VB).card = ((Z : Set (Fin n)) \ V(B)).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    congr 1
    ext u
    dsimp [sep, graphSeparationOfGM]
    simp
  have hZAB_eq : (Z ∩ (sep.VA ∩ sep.VB)).card =
      ((Z : Set (Fin n)) ∩ (V(A) ∩ V(B))).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    congr 1
    ext u
    dsimp [sep, graphSeparationOfGM]
    simp
  have hZ_eq : Z.card = (Z : Set (Fin n)).ncard := (Set.ncard_coe_finset Z).symm
  have hbal_nat : sep.IsBalancedNat Z := by
    unfold GraphSeparation.IsBalancedNat
    rw [hZA_eq, hZB_eq, hZAB_eq, hZ_eq]
    exact ⟨hbalA, hbalB⟩
  exact hno_sep sep hord_sep ((sep.isBalancedQ_iff_isBalancedNat Z).mpr hbal_nat)

/-- Deleting an edge set `s` commutes with `SimpleGraph.toGMGraph`. -/
theorem toGMGraph_deleteEdges {α : Type*} (G : SimpleGraph α) (s : Set (Sym2 α)) :
    (G.deleteEdges s).toGMGraph = G.toGMGraph.deleteEdges s := by
  ext e x y
  · rfl
  · simp only [SimpleGraph.toGMGraph, Graph.ofSimpleGraph_isLink, Graph.deleteEdges_isLink,
      SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff, and_assoc]

/-- Base case `ω = 2` (`ω - 1 = 1`) for edge deletion in Step (6) of Algorithm (3.3):
if `g ∈ G.edgeFinset` and `GM13.GraphBranchWidthLE (G.deleteEdges {g}).toGMGraph 1`, then
`GM13.GraphBranchWidthLE G.toGMGraph 2`. -/
theorem graphBranchWidthLE_two_of_deleteEdge_one {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {g : Sym2 (Fin n)} (hg : g ∈ G.edgeFinset)
    (hbw1 : GM13.GraphBranchWidthLE (G.deleteEdges {g}).toGMGraph 1) :
    GM13.GraphBranchWidthLE G.toGMGraph 2 := by
  classical
  let G' := G.deleteEdges {g}
  have hG'_edges : G'.edgeFinset = G.edgeFinset.erase g := by
    ext e
    simp [G', SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges, and_comm]
  have hcard_G : G.edgeFinset.card = G'.edgeFinset.card + 1 := by
    rw [hG'_edges, Finset.card_erase_add_one hg]
  rcases (graphBranchWidthLE_toGMGraph_iff G' 1).mp hbw1 with
    hle1 | ⟨t, p, τ, ht, _, hp0, hp, hbd⟩
  · by_cases hc0 : G'.edgeFinset.card = 0
    · exact (graphBranchWidthLE_toGMGraph_iff G 2).mpr (Or.inl (by omega))
    · have hc1 : G'.edgeFinset.card = 1 := by omega
      rcases Finset.card_eq_one.mp hc1 with ⟨e₁, he₁_eq⟩
      have he₁_mem' : e₁ ∈ G'.edgeFinset := by rw [he₁_eq]; exact Finset.mem_singleton_self e₁
      have he₁_erase : e₁ ∈ G.edgeFinset.erase g := hG'_edges ▸ he₁_mem'
      have he₁_G : e₁ ∈ G.edgeFinset := Finset.mem_of_mem_erase he₁_erase
      have he₁_ne : e₁ ≠ g := Finset.ne_of_mem_erase he₁_erase
      let τ₁ : Sym2 (Fin n) → Fin 2 := fun e => if e = g then ⟨0, by decide⟩ else ⟨1, by decide⟩
      have hpart : IsPartialBranchDecomp 2 G (parentTree 2 (fun _ => 0)) τ₁ :=
        isPartialBranchDecomp_init (by omega) G hg he₁_G he₁_ne τ₁ (by simp [τ₁])
          (fun e _ hne => by simp [τ₁, hne])
      have hbd2 : IsBranchDecompOfWidthLe 2 G (parentTree 2 (fun _ => 0)) τ₁ := by
        refine ⟨hpart.1, ⟨?_, ?_, ?_⟩, ?_⟩
        · intro e he
          exact hpart.2.1 e he
        · intro a ha b hb hab
          by_cases hag : a = g <;> by_cases hbg : b = g
          · exact hag.trans hbg.symm
          · simp [τ₁, hag, hbg] at hab
          · simp [τ₁, hag, hbg] at hab
          · have ha' : a ∈ G'.edgeFinset := by
              rw [hG'_edges]
              exact Finset.mem_erase.mpr ⟨hag, ha⟩
            have hb' : b ∈ G'.edgeFinset := by
              rw [hG'_edges]
              exact Finset.mem_erase.mpr ⟨hbg, hb⟩
            rw [he₁_eq, Finset.mem_singleton] at ha' hb'
            exact ha'.trans hb'.symm
        · intro v hv
          rcases hpart.2.2.1 v hv with ⟨e, he, rfl⟩
          exact ⟨e, he, rfl⟩
        · intro f hf
          have hp2 : ∀ z, 0 < z → z < 2 → (fun _ => 0) z < z := fun z hz _ => hz
          rcases exists_pos_of_mem_edgeFinset_parentTree hp2 hf with ⟨x, hx_pos, hf_eq⟩
          have hx_lt2 : x.1 < 2 := x.2
          have hx1 : x = ⟨1, by decide⟩ := Fin.ext (by change x.1 = 1; omega)
          have hf_eq01 : f = s(⟨0, by decide⟩, ⟨1, by decide⟩) := by
            rw [hf_eq]
            exact congrArg₂ (fun a b => s(a, b)) (Fin.ext rfl) hx1
          rw [hf_eq01]
          have hdeg1 : (parentTree 2 (fun _ => 0)).degree ⟨1, by decide⟩ = 1 :=
            degree_parentTree_two ⟨1, by decide⟩
          have hadj01 : (parentTree 2 (fun _ => 0)).Adj ⟨0, by decide⟩ ⟨1, by decide⟩ := by
            rw [parentTree_adj_of_lt hp2]
            exact Or.inr ⟨by decide, rfl⟩
          have hconn : (parentTree 2 (fun _ => 0)).Connected :=
            parentTree_connected (by omega) hp2
          unfold treeEdgeOrder
          rw [treeEdgeCutVerts_leaf_eq G hconn τ₁ hdeg1 hadj01]
          have hsub : leafCutVerts G τ₁ ⟨1, by omega⟩ ⊆
              Finset.univ.filter (fun w : Fin n => w ∈ g) := by
            intro w hw
            rw [mem_leafCutVerts] at hw
            rcases hw with ⟨_, ⟨e₂, _, hw₂, hne1⟩⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases he₂_eq : e₂ = g
            · rwa [← he₂_eq]
            · exact False.elim (hne1 (by simp [τ₁, he₂_eq]))
          exact (Finset.card_le_card hsub).trans (card_incident_edge_le_two g)
      exact hbd2.graphBranchWidthLE
  · have hleaves_pos : 0 < (treeLeaves (parentTree t p)).card := by
      have htle := t_le_two_mul_card_treeLeaves ht hp hbd.1
      omega
    rcases Finset.card_pos.mp hleaves_pos with ⟨v_any, hv_any⟩
    rcases hbd.2.1.2.2 hv_any with ⟨e_any, he_any_fin, _⟩
    have hG'_ne : G'.edgeFinset.Nonempty := ⟨e_any, he_any_fin⟩
    obtain ⟨e₀, he₀, hshare₀⟩ :
        ∃ e₀ ∈ G'.edgeFinset,
          (∃ e ∈ G'.edgeFinset, ∃ w : Fin n, w ∈ g ∧ w ∈ e) →
          ∃ u₀ : Fin n, u₀ ∈ g ∧ u₀ ∈ e₀ := by
      by_cases h : ∃ e ∈ G'.edgeFinset, ∃ w : Fin n, w ∈ g ∧ w ∈ e
      · rcases h with ⟨e₀, he₀, u₀, hu₀_g, hu₀_e₀⟩
        exact ⟨e₀, he₀, fun _ => ⟨u₀, hu₀_g, hu₀_e₀⟩⟩
      · rcases hG'_ne with ⟨e₀, he₀⟩
        exact ⟨e₀, he₀, fun h' => False.elim (h h')⟩
    have he₀_erase : e₀ ∈ G.edgeFinset.erase g := hG'_edges ▸ he₀
    have he₀_G : e₀ ∈ G.edgeFinset := Finset.mem_of_mem_erase he₀_erase
    have he₀_ne_g : e₀ ≠ g := Finset.ne_of_mem_erase he₀_erase
    let v : Fin t := τ e₀
    have hv : v ∈ treeLeaves (parentTree t p) := hbd.2.1.1 he₀
    have hτ_eq_v_iff : ∀ e ∈ G'.edgeFinset, τ e = v ↔ e = e₀ := by
      intro e he
      refine ⟨fun heq => hbd.2.1.2.1 he he₀ heq, fun h => h ▸ rfl⟩
    let p' := splitLeafParent p t v.1
    have hp' : ∀ z, 0 < z → z < t + 2 → p' z < z := splitLeafParent_lt hp v.2
    let τ' : Sym2 (Fin n) → Fin (t + 2) := fun e =>
      if e = g then ⟨t, by omega⟩
      else if e = e₀ then ⟨t + 1, by omega⟩
      else ⟨(τ e).1, by omega⟩
    have hτ'_g : τ' g = ⟨t, by omega⟩ := by simp [τ']
    have hτ'_e₀ : τ' e₀ = ⟨t + 1, by omega⟩ := by simp [τ', he₀_ne_g]
    have hτ'_other : ∀ e, e ≠ g → e ≠ e₀ → (τ' e).1 = (τ e).1 := by
      intro e heg hee₀
      simp [τ', heg, hee₀]
    have hbd_G : IsBranchDecompOfWidthLe 2 G (parentTree (t + 2) p') τ' := by
      refine ⟨isCubicOrLeafTree_splitLeafParent hp ht hbd.1 hv, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro e he_fin
        rw [Finset.mem_coe, mem_treeLeaves_splitLeafParent_iff hp ht hv]
        by_cases heg : e = g
        · subst heg; exact Or.inl (congrArg Fin.val hτ'_g)
        · by_cases hee₀ : e = e₀
          · subst hee₀; exact Or.inr (Or.inl (congrArg Fin.val hτ'_e₀))
          · right; right
            have he' : e ∈ G'.edgeFinset := by
              rw [hG'_edges]
              exact Finset.mem_erase.mpr ⟨heg, he_fin⟩
            have hev : τ e ≠ v := fun h => hee₀ ((hτ_eq_v_iff e he').mp h)
            have hval := hτ'_other e heg hee₀
            refine ⟨by rw [hval]; exact (τ e).2, ?_, ?_⟩
            · have h_eq : (⟨(τ' e).1, by rw [hval]; exact (τ e).2⟩ : Fin t) = τ e := Fin.ext hval
              rw [h_eq]
              exact hbd.2.1.1 he'
            · rw [hval]
              exact fun h => hev (Fin.ext h)
      · intro e₁ he₁_fin e₂ he₂_fin heq
        have hval : (τ' e₁).1 = (τ' e₂).1 := congrArg Fin.val heq
        by_cases h1g : e₁ = g <;> by_cases h2g : e₂ = g
        · exact h1g.trans h2g.symm
        · subst h1g
          rw [hτ'_g] at hval
          by_cases h2e₀ : e₂ = e₀
          · subst h2e₀; rw [hτ'_e₀] at hval; dsimp at hval; omega
          · rw [hτ'_other e₂ h2g h2e₀] at hval
            have := (τ e₂).2; dsimp at hval; omega
        · subst h2g
          rw [hτ'_g] at hval
          by_cases h1e₀ : e₁ = e₀
          · subst h1e₀; rw [hτ'_e₀] at hval; dsimp at hval; omega
          · rw [hτ'_other e₁ h1g h1e₀] at hval
            have := (τ e₁).2; dsimp at hval; omega
        · by_cases h1e₀ : e₁ = e₀ <;> by_cases h2e₀ : e₂ = e₀
          · exact h1e₀.trans h2e₀.symm
          · subst h1e₀
            rw [hτ'_e₀, hτ'_other e₂ h2g h2e₀] at hval
            have := (τ e₂).2; dsimp at hval; omega
          · subst h2e₀
            rw [hτ'_e₀, hτ'_other e₁ h1g h1e₀] at hval
            have := (τ e₁).2; dsimp at hval; omega
          · rw [hτ'_other e₁ h1g h1e₀, hτ'_other e₂ h2g h2e₀] at hval
            have he₁' : e₁ ∈ G'.edgeFinset := by
              rw [hG'_edges]
              exact Finset.mem_erase.mpr ⟨h1g, he₁_fin⟩
            have he₂' : e₂ ∈ G'.edgeFinset := by
              rw [hG'_edges]
              exact Finset.mem_erase.mpr ⟨h2g, he₂_fin⟩
            exact hbd.2.1.2.1 he₁' he₂' (Fin.ext hval)
      · intro w hw
        rw [Finset.mem_coe, mem_treeLeaves_splitLeafParent_iff hp ht hv] at hw
        rcases hw with hwt | hwt1 | ⟨hw_lt, hw_leaf, hw_ne⟩
        · exact ⟨g, hg, hτ'_g.trans (Fin.ext hwt.symm)⟩
        · exact ⟨e₀, he₀_G, hτ'_e₀.trans (Fin.ext hwt1.symm)⟩
        · rcases hbd.2.1.2.2 hw_leaf with ⟨e, he', he_eq⟩
          have he_erase : e ∈ G.edgeFinset.erase g := hG'_edges ▸ he'
          have heg : e ≠ g := Finset.ne_of_mem_erase he_erase
          have hee₀ : e ≠ e₀ := by
            intro h
            exact hw_ne (congrArg Fin.val (he_eq.symm.trans (h ▸ rfl)))
          refine ⟨e, Finset.mem_of_mem_erase he_erase, Fin.ext ?_⟩
          rw [hτ'_other e heg hee₀, congrArg Fin.val he_eq]
      · intro f hf
        rcases exists_pos_of_mem_edgeFinset_parentTree hp' hf with ⟨x, hx_pos, hf_eq⟩
        by_cases hx_lt : x.1 < t
        · let x₀ : Fin t := ⟨x.1, hx_lt⟩
          have hx₀_pos : 0 < x₀.1 := hx_pos
          let px₀ : Fin t := ⟨p x₀.1, Nat.lt_trans (hp x₀.1 hx₀_pos x₀.2) x₀.2⟩
          have hf₀_mem : s(px₀, x₀) ∈ (parentTree t p).edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, parentTree_adj_of_lt hp]
            exact Or.inr ⟨hx₀_pos, rfl⟩
          have hord₀ : (treeEdgeCutVerts G' (parentTree t p) τ s(px₀, x₀)).card ≤ 1 :=
            hbd.2.2 (s(px₀, x₀)) hf₀_mem
          have hsub_g : inSubtree p' x.1 (τ' g).1 = inSubtree p x₀.1 v.1 := by
            rw [hτ'_g]
            exact inSubtree_splitLeafParent_left hp ht v.2 hx_lt
          have hsub_G' : ∀ e ∈ G'.edgeFinset,
              inSubtree p' x.1 (τ' e).1 = inSubtree p x₀.1 (τ e).1 := by
            intro e he
            have heg : e ≠ g := Finset.ne_of_mem_erase (hG'_edges ▸ he)
            by_cases hee₀ : e = e₀
            · subst hee₀
              rw [hτ'_e₀]
              exact inSubtree_splitLeafParent_right hp v.2 hx_lt
            · rw [hτ'_other e heg hee₀]
              exact inSubtree_splitLeafParent_of_lt hp v.2 hx_lt (τ e).1 (τ e).2
          let px' : Fin (t + 2) := ⟨p' x.1, Nat.lt_trans (hp' x.1 hx_pos x.2) x.2⟩
          rw [hf_eq]
          change (treeEdgeCutVerts G (parentTree (t + 2) p') τ' s(px', x)).card ≤ 2
          by_cases hshare : ∃ e ∈ G'.edgeFinset, ∃ w : Fin n, w ∈ g ∧ w ∈ e
          · rcases hshare₀ hshare with ⟨u₀, hu₀_g, hu₀_e₀⟩
            rcases exists_insert_superset_of_mem_edge ({u₀} : Finset (Fin n)) g
              (Finset.mem_singleton_self u₀) hu₀_g with ⟨x_other, hx_other⟩
            have hsub_cut : treeEdgeCutVerts G (parentTree (t + 2) p') τ' s(px', x) ⊆
                insert x_other (treeEdgeCutVerts G' (parentTree t p) τ s(px₀, x₀)) := by
              intro w hw
              rw [mem_treeEdgeCutVerts] at hw
              rcases hw with ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, hnr⟩
              rw [parentTree_deleteEdge_reachable_iff (by omega) hp' hx_pos] at hnr
              by_cases hw_x : w = x_other
              · subst hw_x
                exact Finset.mem_insert_self _ _
              · apply Finset.mem_insert_of_mem
                rw [mem_treeEdgeCutVerts]
                have hw_g_eq : w ∈ g → w = u₀ := by
                  intro hwg
                  have hmem := hx_other (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwg⟩)
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
                  exact hmem.resolve_left hw_x
                by_cases h1g : e₁ = g <;> by_cases h2g : e₂ = g
                · subst h1g h2g; exact False.elim (hnr rfl)
                · subst h1g
                  have hw_u₀ : w = u₀ := hw_g_eq hw₁
                  subst hw_u₀
                  have he₂' : e₂ ∈ G'.edgeFinset := by
                    rw [hG'_edges]; exact Finset.mem_erase.mpr ⟨h2g, he₂⟩
                  refine ⟨e₀, he₀, e₂, he₂', hu₀_e₀, hw₂, ?_⟩
                  rw [parentTree_deleteEdge_reachable_iff ht hp hx₀_pos]
                  rw [hsub_g, hsub_G' e₂ he₂'] at hnr
                  exact hnr
                · subst h2g
                  have hw_u₀ : w = u₀ := hw_g_eq hw₂
                  subst hw_u₀
                  have he₁' : e₁ ∈ G'.edgeFinset := by
                    rw [hG'_edges]; exact Finset.mem_erase.mpr ⟨h1g, he₁⟩
                  refine ⟨e₁, he₁', e₀, he₀, hw₁, hu₀_e₀, ?_⟩
                  rw [parentTree_deleteEdge_reachable_iff ht hp hx₀_pos]
                  rw [hsub_G' e₁ he₁', hsub_g] at hnr
                  exact hnr
                · have he₁' : e₁ ∈ G'.edgeFinset := by
                    rw [hG'_edges]; exact Finset.mem_erase.mpr ⟨h1g, he₁⟩
                  have he₂' : e₂ ∈ G'.edgeFinset := by
                    rw [hG'_edges]; exact Finset.mem_erase.mpr ⟨h2g, he₂⟩
                  refine ⟨e₁, he₁', e₂, he₂', hw₁, hw₂, ?_⟩
                  rw [parentTree_deleteEdge_reachable_iff ht hp hx₀_pos]
                  rw [hsub_G' e₁ he₁', hsub_G' e₂ he₂'] at hnr
                  exact hnr
            have hcard := (Finset.card_le_card hsub_cut).trans (Finset.card_insert_le _ _)
            omega
          · have hsub_cut : treeEdgeCutVerts G (parentTree (t + 2) p') τ' s(px', x) ⊆
                treeEdgeCutVerts G' (parentTree t p) τ s(px₀, x₀) := by
              intro w hw
              rw [mem_treeEdgeCutVerts] at hw ⊢
              rcases hw with ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, hnr⟩
              rw [parentTree_deleteEdge_reachable_iff (by omega) hp' hx_pos] at hnr
              by_cases h1g : e₁ = g <;> by_cases h2g : e₂ = g
              · subst h1g h2g; exact False.elim (hnr rfl)
              · subst h1g
                have he₂' : e₂ ∈ G'.edgeFinset := by
                  rw [hG'_edges]; exact Finset.mem_erase.mpr ⟨h2g, he₂⟩
                exact False.elim (hshare ⟨e₂, he₂', w, hw₁, hw₂⟩)
              · subst h2g
                have he₁' : e₁ ∈ G'.edgeFinset := by
                  rw [hG'_edges]; exact Finset.mem_erase.mpr ⟨h1g, he₁⟩
                exact False.elim (hshare ⟨e₁, he₁', w, hw₂, hw₁⟩)
              · have he₁' : e₁ ∈ G'.edgeFinset := by
                  rw [hG'_edges]; exact Finset.mem_erase.mpr ⟨h1g, he₁⟩
                have he₂' : e₂ ∈ G'.edgeFinset := by
                  rw [hG'_edges]; exact Finset.mem_erase.mpr ⟨h2g, he₂⟩
                refine ⟨e₁, he₁', e₂, he₂', hw₁, hw₂, ?_⟩
                rw [parentTree_deleteEdge_reachable_iff ht hp hx₀_pos]
                rw [hsub_G' e₁ he₁', hsub_G' e₂ he₂'] at hnr
                exact hnr
            have hcard := (Finset.card_le_card hsub_cut).trans hord₀
            omega
        · have hconn' : (parentTree (t + 2) p').Connected :=
            parentTree_connected (by omega) hp'
          have hx_lt2 : x.1 < t + 2 := x.2
          rcases (by omega : x.1 = t ∨ x.1 = t + 1) with hxt | hxt1
          · have hx_eq : x = ⟨t, by omega⟩ := Fin.ext hxt
            have hdeg_t : (parentTree (t + 2) p').degree ⟨t, by omega⟩ = 1 :=
              degree_splitLeafParent_left hp ht v
            let pt : Fin (t + 2) := ⟨p' t, Nat.lt_trans (hp' t ht (by omega)) (by omega)⟩
            have hadj_t : (parentTree (t + 2) p').Adj pt ⟨t, by omega⟩ := by
              rw [parentTree_adj_of_lt hp']
              exact Or.inr ⟨ht, rfl⟩
            have hf_eq_t : f = s(pt, ⟨t, by omega⟩) := by
              rw [hf_eq]
              exact congrArg₂ (fun a b => s(a, b)) (Fin.ext (by simp [pt, hxt])) hx_eq
            rw [hf_eq_t]
            unfold treeEdgeOrder
            rw [treeEdgeCutVerts_leaf_eq G hconn' τ' hdeg_t hadj_t]
            have hsub : leafCutVerts G τ' ⟨t, by omega⟩ ⊆
                Finset.univ.filter (fun w : Fin n => w ∈ g) := by
              intro w hw
              rw [mem_leafCutVerts] at hw
              rcases hw with ⟨⟨e₁, _, hw₁, h1⟩, _⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases he₁_g : e₁ = g
              · rwa [← he₁_g]
              · by_cases he₁_e₀ : e₁ = e₀
                · subst he₁_e₀
                  have hval := congrArg Fin.val (h1.symm.trans hτ'_e₀)
                  dsimp at hval; omega
                · have hval1 : (τ' e₁).1 = t := congrArg Fin.val h1
                  have hval2 := hτ'_other e₁ he₁_g he₁_e₀
                  have := (τ e₁).2
                  omega
            exact (Finset.card_le_card hsub).trans (card_incident_edge_le_two g)
          · have hx_eq : x = ⟨t + 1, by omega⟩ := Fin.ext hxt1
            have hdeg_t1 : (parentTree (t + 2) p').degree ⟨t + 1, by omega⟩ = 1 :=
              degree_splitLeafParent_right hp v
            let pt1 : Fin (t + 2) :=
              ⟨p' (t + 1), Nat.lt_trans (hp' (t + 1) (by omega) (by omega)) (by omega)⟩
            have hadj_t1 : (parentTree (t + 2) p').Adj pt1 ⟨t + 1, by omega⟩ := by
              rw [parentTree_adj_of_lt hp']
              exact Or.inr ⟨by omega, rfl⟩
            have hf_eq_t1 : f = s(pt1, ⟨t + 1, by omega⟩) := by
              rw [hf_eq]
              exact congrArg₂ (fun a b => s(a, b)) (Fin.ext (by simp [pt1, hxt1])) hx_eq
            rw [hf_eq_t1]
            unfold treeEdgeOrder
            rw [treeEdgeCutVerts_leaf_eq G hconn' τ' hdeg_t1 hadj_t1]
            have hsub : leafCutVerts G τ' ⟨t + 1, by omega⟩ ⊆
                Finset.univ.filter (fun w : Fin n => w ∈ e₀) := by
              intro w hw
              rw [mem_leafCutVerts] at hw
              rcases hw with ⟨⟨e₁, _, hw₁, h1⟩, _⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases he₁_e₀ : e₁ = e₀
              · rwa [← he₁_e₀]
              · by_cases he₁_g : e₁ = g
                · subst he₁_g
                  have hval := congrArg Fin.val (h1.symm.trans hτ'_g)
                  dsimp at hval; omega
                · have hval1 : (τ' e₁).1 = t + 1 := congrArg Fin.val h1
                  have hval2 := hτ'_other e₁ he₁_g he₁_e₀
                  have := (τ e₁).2
                  omega
            exact (Finset.card_le_card hsub).trans (card_incident_edge_le_two e₀)
    exact hbd_G.graphBranchWidthLE

/-- Step (6) of Algorithm (3.3) (GM XIII page 74): for any `2 ≤ ω` and `g ∈ G.edgeFinset`,
if `GM13.GraphBranchWidthLE (G.deleteEdges {g}).toGMGraph (ω - 1)`, then
`GM13.GraphBranchWidthLE G.toGMGraph ω`.
Proved using `GM13.algorithm_3_3_step_6_deleteEdge` for `3 ≤ ω` and
`graphBranchWidthLE_two_of_deleteEdge_one` for `ω = 2`. -/
theorem graphBranchWidthLE_of_deleteEdge_sub_one {n ω : ℕ} (hω : 2 ≤ ω)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {g : Sym2 (Fin n)} (hg : g ∈ G.edgeFinset)
    (hbw : GM13.GraphBranchWidthLE (G.deleteEdges {g}).toGMGraph (ω - 1)) :
    GM13.GraphBranchWidthLE G.toGMGraph ω := by
  by_cases hω3 : 3 ≤ ω
  · rw [toGMGraph_deleteEdges] at hbw
    have hg_gm : g ∈ E(G.toGMGraph) := G.mem_edgeFinset.mp hg
    have hbw_add : GM13.GraphBranchWidthLE G.toGMGraph ((ω - 1) + 1) :=
      GM13.algorithm_3_3_step_6_deleteEdge G.toGMGraph (Set.toFinite _) (Set.toFinite _)
        hg_gm (by omega) hbw
    have heq : (ω - 1) + 1 = ω := by omega
    rwa [heq] at hbw_add
  · have hω2 : ω = 2 := by omega
    subst hω2
    exact graphBranchWidthLE_two_of_deleteEdge_one G hg hbw

/-- In Step (6) of Algorithm (3.3), if `G' = G_step6.deleteEdges {g}` with `g ∈ G_step6.edgeFinset`
and `G_step6` has no balanced separation of order `≤ ω` with respect to `Z`, then
`¬ GM13.GraphBranchWidthLE G'.toGMGraph (ω - 1)`. -/
theorem not_graphBranchWidthLE_sub_one_of_step6 {n ω : ℕ} (hω : 2 ≤ ω)
    {G' G_step6 : SimpleGraph (Fin n)} [DecidableRel G_step6.Adj]
    {g : Sym2 (Fin n)} (hg : g ∈ G_step6.edgeFinset)
    (Z : Finset (Fin n))
    (heq : G' = G_step6.deleteEdges {g})
    (hno_sep : ∀ sep : GraphSeparation G_step6, sep.order ≤ ω → ¬ sep.IsBalancedQ Z) :
    ¬ GM13.GraphBranchWidthLE G'.toGMGraph (ω - 1) := by
  subst heq
  intro hbw1
  exact not_graphBranchWidthLE_of_no_balanced_sep hω G_step6 Z hno_sep
    (graphBranchWidthLE_of_deleteEdge_sub_one hω G_step6 hg hbw1)

/-- Main high-branch-width deduction for simple graphs in Algorithm (3.3):
either `G' = G`, or `¬ GM13.GraphBranchWidthLE G'.toGMGraph (ω - 1)`, proved from the two
high-width cases (`|E(G')| > ((3/2)ω - 1)|V(G)|` via `GM13.theorem_3_2_proof`, and Step (6) via
`GM13.theorem_3_1_proof` and `GM13.algorithm_3_3_step_6_deleteEdge`). -/
theorem eq_or_not_graphBranchWidthLE_of_alg33_cases {n ω : ℕ} (hω : 2 ≤ ω)
    (G G' G_step6 : SimpleGraph (Fin n)) [DecidableRel G'.Adj] [DecidableRel G_step6.Adj]
    (g : Sym2 (Fin n)) (Z : Finset (Fin n))
    (hcases :
      G' = G ∨
      (G' ≠ G ∧
       (G'.edgeFinset.card : ℚ) ≤ ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ) + 1 ∧
       (G'.edgeFinset.card : ℚ) > ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ)) ∨
      (G_step6 ≤ G ∧
       g ∈ G_step6.edgeFinset ∧
       Z.card = 3 * ω ∧
       G' ≤ G_step6.deleteEdges {g} ∧
       G' = G_step6.deleteEdges {g} ∧
       ∀ sep : GraphSeparation G_step6, sep.order ≤ ω → ¬ sep.IsBalancedQ Z)) :
    G' = G ∨ ¬ GM13.GraphBranchWidthLE G'.toGMGraph (ω - 1) := by
  rcases hcases with rfl | ⟨_, _, hgt⟩ | ⟨_, hg, _, _, heq, hno_sep⟩
  · exact Or.inl rfl
  · exact Or.inr (not_graphBranchWidthLE_sub_one_of_edge_gt_rat hω G' hgt)
  · exact Or.inr (not_graphBranchWidthLE_sub_one_of_step6 hω hg Z heq hno_sep)

/-- For a simple `MultiDigraph` (`∀ u, G.edgeMult u u = 0` and
`∀ u v, G.edgeMult u v + G.edgeMult v u ≤ 1`), the unordered endpoint map
`i ↦ s((G.edgeEndpoints i).1, (G.edgeEndpoints i).2)` is a bijection between `Fin G.numEdges`
and `G.toSimpleGraph.edgeFinset`. -/
theorem MultiDigraph.simpleEdge_properties {n : ℕ} (G : MultiDigraph n)
    (hloop : ∀ u : Fin n, G.edgeMult u u = 0)
    (hmult : ∀ u v : Fin n, G.edgeMult u v + G.edgeMult v u ≤ 1) :
    (∀ i : Fin G.numEdges,
      s((G.edgeEndpoints i).1, (G.edgeEndpoints i).2) ∈ G.toSimpleGraph.edgeFinset) ∧
    (∀ g ∈ G.toSimpleGraph.edgeFinset,
      ∃ i : Fin G.numEdges, s((G.edgeEndpoints i).1, (G.edgeEndpoints i).2) = g) ∧
    Function.Injective (fun i : Fin G.numEdges =>
      s((G.edgeEndpoints i).1, (G.edgeEndpoints i).2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hpos := G.edgeMult_edgeEndpoints_pos i
    have hne : (G.edgeEndpoints i).1 ≠ (G.edgeEndpoints i).2 := by
      intro heq
      rw [heq, hloop] at hpos
      omega
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨hne, Or.inl hpos⟩
  · intro g hg
    induction g using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hg
      rcases hg.2 with huv | hvu
      · have hmem : (u, v) ∈ G.edgeListWithMult := by
          simp only [MultiDigraph.edgeListWithMult, List.mem_flatMap,
            MultiDigraph.mem_activePairsList, List.mem_replicate]
          exact ⟨(u, v), huv, Nat.ne_of_gt huv, rfl⟩
        rcases List.mem_iff_getElem.mp hmem with ⟨k, hk, hget⟩
        refine ⟨⟨k, by rwa [← G.length_edgeListWithMult]⟩, ?_⟩
        change s((G.edgeListWithMult[k]'hk).1, (G.edgeListWithMult[k]'hk).2) = s(u, v)
        rw [hget]
      · have hmem : (v, u) ∈ G.edgeListWithMult := by
          simp only [MultiDigraph.edgeListWithMult, List.mem_flatMap,
            MultiDigraph.mem_activePairsList, List.mem_replicate]
          exact ⟨(v, u), hvu, Nat.ne_of_gt hvu, rfl⟩
        rcases List.mem_iff_getElem.mp hmem with ⟨k, hk, hget⟩
        refine ⟨⟨k, by rwa [← G.length_edgeListWithMult]⟩, ?_⟩
        change s((G.edgeListWithMult[k]'hk).1, (G.edgeListWithMult[k]'hk).2) = s(u, v)
        rw [hget, Sym2.eq_swap]
  · intro i₁ i₂ heq
    have hpos₁ := G.edgeMult_edgeEndpoints_pos i₁
    have hpos₂ := G.edgeMult_edgeEndpoints_pos i₂
    have h12 : G.edgeEndpoints i₁ = G.edgeEndpoints i₂ := by
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso
        have hm := hmult (G.edgeEndpoints i₂).1 (G.edgeEndpoints i₂).2
        rw [h1, h2] at hpos₁
        omega
    have hfst_snd₁ := G.getElem_multiEdgeTriples_fst_snd i₁
    have hfst_snd₂ := G.getElem_multiEdgeTriples_fst_snd i₂
    have hmem₁ := (G.multiEdgeEquiv i₁).2
    have hmem₂ := (G.multiEdgeEquiv i₂).2
    change (G.multiEdgeEquiv i₁).1 ∈ G.toGMDigraph.edgeSet at hmem₁
    change (G.multiEdgeEquiv i₂).1 ∈ G.toGMDigraph.edgeSet at hmem₂
    dsimp [MultiDigraph.toGMDigraph] at hmem₁ hmem₂
    rcases hmem₁ with ⟨hu₁, hv₁, hk₁⟩
    rcases hmem₂ with ⟨hu₂, hv₂, hk₂⟩
    have hu₁_eq : (⟨(G.multiEdgeEquiv i₁).1.1, hu₁⟩ : Fin n) = (G.edgeEndpoints i₁).1 :=
      Fin.ext (congrArg Prod.fst hfst_snd₁)
    have hv₁_eq : (⟨(G.multiEdgeEquiv i₁).1.2.1, hv₁⟩ : Fin n) = (G.edgeEndpoints i₁).2 :=
      Fin.ext (congrArg Prod.snd hfst_snd₁)
    have hu₂_eq : (⟨(G.multiEdgeEquiv i₂).1.1, hu₂⟩ : Fin n) = (G.edgeEndpoints i₂).1 :=
      Fin.ext (congrArg Prod.fst hfst_snd₂)
    have hv₂_eq : (⟨(G.multiEdgeEquiv i₂).1.2.1, hv₂⟩ : Fin n) = (G.edgeEndpoints i₂).2 :=
      Fin.ext (congrArg Prod.snd hfst_snd₂)
    have hk₁' : (G.multiEdgeEquiv i₁).1.2.2 <
        G.edgeMult (G.edgeEndpoints i₁).1 (G.edgeEndpoints i₁).2 :=
      hu₁_eq ▸ hv₁_eq ▸ hk₁
    have hk₂' : (G.multiEdgeEquiv i₂).1.2.2 <
        G.edgeMult (G.edgeEndpoints i₁).1 (G.edgeEndpoints i₁).2 :=
      h12 ▸ hu₂_eq ▸ hv₂_eq ▸ hk₂
    have hm1 := hmult (G.edgeEndpoints i₁).1 (G.edgeEndpoints i₁).2
    have htri_eq : (G.multiEdgeEquiv i₁).1 = (G.multiEdgeEquiv i₂).1 := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · calc
        (G.multiEdgeEquiv i₁).1.1 = (G.edgeEndpoints i₁).1.1 := congrArg Prod.fst hfst_snd₁
        _ = (G.edgeEndpoints i₂).1.1 := by rw [h12]
        _ = (G.multiEdgeEquiv i₂).1.1 := (congrArg Prod.fst hfst_snd₂).symm
      · calc
        (G.multiEdgeEquiv i₁).1.2.1 = (G.edgeEndpoints i₁).2.1 := congrArg Prod.snd hfst_snd₁
        _ = (G.edgeEndpoints i₂).2.1 := by rw [h12]
        _ = (G.multiEdgeEquiv i₂).1.2.1 := (congrArg Prod.snd hfst_snd₂).symm
      · omega
    exact G.multiEdgeEquiv.injective (Subtype.ext htri_eq)

/-- For a simple `MultiDigraph` (`∀ u, G.edgeMult u u = 0` and
`∀ u v, G.edgeMult u v + G.edgeMult v u ≤ 1`), `GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B`
implies `GM13.GraphBranchWidthLE G.toSimpleGraph.toGMGraph B`. -/
theorem graphBranchWidthLE_toSimpleGraph_of_toGMDigraph {n : ℕ} (G : MultiDigraph n)
    (hloop : ∀ u : Fin n, G.edgeMult u u = 0)
    (hmult : ∀ u v : Fin n, G.edgeMult u v + G.edgeMult v u ≤ 1)
    {B : ℕ} (hbw : GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B) :
    GM13.GraphBranchWidthLE G.toSimpleGraph.toGMGraph B := by
  classical
  obtain ⟨hmem, hsurj, hinj⟩ := G.simpleEdge_properties hloop hmult
  let f_edge : Fin G.numEdges → Sym2 (Fin n) :=
    fun i => s((G.edgeEndpoints i).1, (G.edgeEndpoints i).2)
  rcases (hasBranchDecompOfWidthLe_iff_graphBranchWidthLE G B).mpr hbw with
    hle1 | ⟨t, T, hdec, τ, hbd⟩
  · have hsub : G.toSimpleGraph.edgeFinset ⊆ Finset.univ.image f_edge := by
      intro g hg
      rcases hsurj g hg with ⟨i, rfl⟩
      exact Finset.mem_image_of_mem f_edge (Finset.mem_univ i)
    have hcard : G.toSimpleGraph.edgeFinset.card ≤ G.numEdges := by
      calc
        G.toSimpleGraph.edgeFinset.card ≤ (Finset.univ.image f_edge).card :=
          Finset.card_le_card hsub
        _ ≤ (Finset.univ : Finset (Fin G.numEdges)).card := Finset.card_image_le
        _ = G.numEdges := by simp
    exact (graphBranchWidthLE_toGMGraph_iff G.toSimpleGraph B).mpr (Or.inl (hcard.trans hle1))
  · have ht : 0 < t := Fin.pos_iff_nonempty.mpr hbd.1.1.connected.nonempty
    let τ_simp : Sym2 (Fin n) → Fin t := fun g =>
      if h : ∃ i : Fin G.numEdges, f_edge i = g then τ h.choose else ⟨0, ht⟩
    have hτ_eq : ∀ i : Fin G.numEdges, τ_simp (f_edge i) = τ i := by
      intro i
      have hex : ∃ j : Fin G.numEdges, f_edge j = f_edge i := ⟨i, rfl⟩
      simp only [τ_simp, hex, ↓reduceDIte]
      exact congrArg τ (hinj hex.choose_spec)
    have hinc_iff : ∀ (w : Fin n) (i : Fin G.numEdges),
        digraphIncident G.toMultiComputeDigraph w i ↔ w ∈ f_edge i := by
      intro w i
      unfold digraphIncident
      dsimp [MultiDigraph.toMultiComputeDigraph, f_edge]
      rw [Sym2.mem_iff, or_comm]
      exact ⟨fun h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm),
             fun h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm)⟩
    rcases hbd with ⟨hcub, ⟨hmaps, hinj_τ, hsurj_τ⟩, hord⟩
    have hbd_simp : IsBranchDecompOfWidthLe B G.toSimpleGraph T τ_simp := by
      refine ⟨hcub, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro g hg
        rcases hsurj g hg with ⟨i, rfl⟩
        rw [hτ_eq i]
        exact hmaps (Set.mem_univ i)
      · intro g₁ hg₁ g₂ hg₂ heq
        rcases hsurj g₁ hg₁ with ⟨i₁, rfl⟩
        rcases hsurj g₂ hg₂ with ⟨i₂, rfl⟩
        rw [hτ_eq i₁, hτ_eq i₂] at heq
        exact congrArg f_edge (hinj_τ (Set.mem_univ i₁) (Set.mem_univ i₂) heq)
      · intro v hv
        rcases hsurj_τ hv with ⟨i, _, rfl⟩
        exact ⟨f_edge i, hmem i, hτ_eq i⟩
      · intro f hf
        have hcut_eq : treeEdgeCutVerts G.toSimpleGraph T τ_simp f =
            digraphTreeEdgeCutVerts G.toMultiComputeDigraph T τ f := by
          ext w
          simp only [treeEdgeCutVerts, digraphTreeEdgeCutVerts, Finset.mem_filter,
            Finset.mem_univ, true_and, SimpleGraph.mem_edgeFinset]
          constructor
          · rintro ⟨g₁, hg₁, g₂, hg₂, hw₁, hw₂, hnr⟩
            rcases hsurj g₁ (G.toSimpleGraph.mem_edgeFinset.mpr hg₁) with ⟨i₁, rfl⟩
            rcases hsurj g₂ (G.toSimpleGraph.mem_edgeFinset.mpr hg₂) with ⟨i₂, rfl⟩
            rw [← hinc_iff] at hw₁ hw₂
            rw [hτ_eq i₁, hτ_eq i₂] at hnr
            exact ⟨i₁, i₂, hw₁, hw₂, hnr⟩
          · rintro ⟨i₁, i₂, hw₁, hw₂, hnr⟩
            rw [hinc_iff] at hw₁ hw₂
            rw [← hτ_eq i₁, ← hτ_eq i₂] at hnr
            exact ⟨f_edge i₁, G.toSimpleGraph.mem_edgeFinset.mp (hmem i₁),
                   f_edge i₂, G.toSimpleGraph.mem_edgeFinset.mp (hmem i₂), hw₁, hw₂, hnr⟩
        unfold treeEdgeOrder digraphTreeEdgeOrder at *
        rw [hcut_eq]
        exact hord f hf
    exact hbd_simp.graphBranchWidthLE

/-- Main high-branch-width deduction for multigraphs in Algorithm (3.3):
any `G'` satisfying `IsAlg33HighWidthCase ω G G'` (with `2 ≤ ω`) has
`¬ GM13.GraphBranchWidthLE G'.toGMDigraph.toGraph (ω - 1)`. -/
theorem IsAlg33HighWidthCase.not_graphBranchWidthLE {n ω : ℕ} (hω : 2 ≤ ω)
    {G G' : MultiDigraph n} (h : IsAlg33HighWidthCase ω G G') :
    ¬ GM13.GraphBranchWidthLE G'.toGMDigraph.toGraph (ω - 1) := by
  rcases h with ⟨hloop, hmult, hcases⟩
  intro hbw
  have hbw_simp : GM13.GraphBranchWidthLE G'.toSimpleGraph.toGMGraph (ω - 1) :=
    graphBranchWidthLE_toSimpleGraph_of_toGMDigraph G' hloop hmult hbw
  rcases hcases with ⟨_, hgt⟩ | ⟨G_step6, g, Z, _, hg, _, _, heq, hno_sep⟩
  · exact @not_graphBranchWidthLE_sub_one_of_edge_gt_rat n ω hω G'.toSimpleGraph
      (Classical.decRel _) hgt hbw_simp
  · exact @not_graphBranchWidthLE_sub_one_of_step6 n ω hω G'.toSimpleGraph G_step6
      (Classical.decRel _) g hg Z heq hno_sep hbw_simp

end GraphMinor.Compute


