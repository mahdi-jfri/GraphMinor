module

public import GraphMinor.Compute.Specs105

/-!
# Step (2) of GM XIII Algorithm (10.5): Branch-Decomposition Extension on the Word RAM

This file formalizes Step (2) of Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths
Problem*, Algorithm (10.5) (page 109):

> **Step (2).** If step (1) finds a branch-decomposition of $G_i \setminus Z$ of width $\le \omega$,
> it is easy to convert it to a branch-decomposition of $G_i$ of width $\le \max(\omega, 2) + \xi$.
> Then we apply (4.1) to find the $\delta$-folio of $G_i$ relative to $Z$, and stop.

## Mathematical & Algorithmic Overview

Given a directed multigraph `G : MultiDigraph n`, a root subset `Z : Finset (Fin n)` with
`|Z| ≤ ξ`, and a written-out branch-decomposition `(t₀, par₀, f_tau₀)` of `(G.deleteVertices Z)`
of width `≤ ω`:

1. **Edge correspondence (`directedEdgesList_deleteVertices` and `filterIdx`):**
   `(G.deleteVertices Z).directedEdgesList` is the sublist of `G.directedEdgesList` filtered by
   `p.1 ∉ Z ∧ p.2 ∉ Z`. For any edge `e` of `G` with both endpoints outside `Z`, its index in
   `(G.deleteVertices Z).directedEdgesList` is `filterIdx G.directedEdgesList P e`.
2. **Partial branch-decomposition (`IsPartialDigraphBD`):**
   We maintain a subset `S ⊆ Fin m` of edges of `D = G.toComputeDigraph` containing all edges of
   `D` with both endpoints outside `Z`, a cubic-or-leaf parent-array tree `parentTree t par`, and a
   bijection `τ : S → treeLeaves (parentTree t par)` such that on every tree edge `f`, the set of
   cut vertices outside `Z` (`partialCutVertsOutsideZ D Z S (parentTree t par) τ f`) has
   cardinality at most `max ω 2`.
3. **Edge insertion by leaf splitting (`IsPartialDigraphBD.splitLeaf`):**
   Each remaining edge `e ∉ S` has at least one endpoint in `Z`, so it is incident with at most one
   vertex `w` outside `Z`. Using an array `vertEdge[0..n-1]` storing an incident tree edge `e_ref ∈ S`
   for each vertex (or `m` if none), we pick `e_ref = vertEdge[w]` if `w ∉ Z` and `vertEdge[w] < m`,
   and an arbitrary base edge `e_base ∈ S` otherwise, and subdivide leaf `τ e_ref` into two leaves
   `t` (for `e`) and `t + 1` (for `e_ref`). This preserves `(partialCutVertsOutsideZ ...).card ≤ max ω 2`.
4. **Completion (`IsPartialDigraphBD.to_isDigraphBranchDecompOfWidthLe`):**
   When `S = Finset.univ`, every cut vertex of any tree edge `f` either lies in
   `partialCutVertsOutsideZ` or belongs to `Z`, giving order `≤ max ω 2 + |Z| ≤ max ω 2 + ξ`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical
open scoped BigOperators

/-! ### Section 1: List Filter Indexing (`filterIdx`) and `(G.deleteVertices Z).directedEdgesList` -/

/-- Number of elements in the prefix `L.take e` satisfying boolean predicate `P`. -/
def filterIdx {α : Type*} (L : List α) (P : α → Bool) (e : ℕ) : ℕ :=
  ((L.take e).filter P).length

@[simp]
theorem filterIdx_zero {α : Type*} (L : List α) (P : α → Bool) :
    filterIdx L P 0 = 0 := rfl

@[simp]
theorem filterIdx_length {α : Type*} (L : List α) (P : α → Bool) :
    filterIdx L P L.length = (L.filter P).length := by
  simp [filterIdx]

theorem filterIdx_succ {α : Type*} (L : List α) (P : α → Bool) {e : ℕ} (he : e < L.length) :
    filterIdx L P (e + 1) = if P L[e] then filterIdx L P e + 1 else filterIdx L P e := by
  unfold filterIdx
  rw [List.take_add_one, List.getElem?_eq_getElem he, Option.toList_some, List.filter_append]
  by_cases h : P L[e] = true
  · simp [h]
  · have hf : P L[e] = false := Bool.eq_false_iff.mpr h
    simp [hf]

theorem filterIdx_mono {α : Type*} (L : List α) (P : α → Bool) {a b : ℕ} (hab : a ≤ b) :
    filterIdx L P a ≤ filterIdx L P b := by
  unfold filterIdx
  have htake : L.take a = (L.take b).take a := by
    rw [List.take_take, Nat.min_eq_left hab]
  rw [htake]
  have hsplit : L.take b = (L.take b).take a ++ (L.take b).drop a :=
    (List.take_append_drop a (L.take b)).symm
  conv_rhs => rw [hsplit, List.filter_append, List.length_append]
  omega

theorem filterIdx_strictMono_of_true {α : Type*} (L : List α) (P : α → Bool)
    {e₁ e₂ : ℕ} (he₁ : e₁ < e₂) (he₂ : e₂ ≤ L.length)
    (hP : P (L[e₁]'(Nat.lt_of_lt_of_le he₁ he₂)) = true) :
    filterIdx L P e₁ < filterIdx L P e₂ := by
  have h1 : filterIdx L P (e₁ + 1) = filterIdx L P e₁ + 1 := by
    rw [filterIdx_succ L P (Nat.lt_of_lt_of_le he₁ he₂)]
    simp [hP]
  have h2 : filterIdx L P (e₁ + 1) ≤ filterIdx L P e₂ :=
    filterIdx_mono L P he₁
  omega

theorem filterIdx_lt_length_filter {α : Type*} (L : List α) (P : α → Bool)
    {e : ℕ} (he : e < L.length) (hP : P L[e] = true) :
    filterIdx L P e < (L.filter P).length := by
  rw [← filterIdx_length]
  exact filterIdx_strictMono_of_true L P he (le_refl _) hP

theorem getElem_filter_filterIdx {α : Type*} (L : List α) (P : α → Bool)
    {e : ℕ} (he : e < L.length) (hP : P L[e] = true) :
    (L.filter P)[filterIdx L P e]'(filterIdx_lt_length_filter L P he hP) = L[e] := by
  have hsplit : L = L.take e ++ L[e] :: L.drop (e + 1) := by
    conv_lhs => rw [← List.take_append_drop e L, List.drop_eq_getElem_cons he]
  have hfilt : L.filter P = (L.take e).filter P ++ L[e] :: (L.drop (e + 1)).filter P := by
    conv_lhs => rw [hsplit]
    rw [List.filter_append, List.filter_cons_of_pos hP]
  have hget :
      (L.filter P)[filterIdx L P e]'(filterIdx_lt_length_filter L P he hP) =
        ((L.take e).filter P ++ L[e] :: (L.drop (e + 1)).filter P)[((L.take e).filter P).length]'(by
          simp) := by
    congr 1
  rw [hget, List.getElem_append_right (le_refl _)]
  simp

theorem exists_filterIdx_eq_of_lt {α : Type*} (L : List α) (P : α → Bool) :
    ∀ {k : ℕ} (hk : k ≤ L.length) {j : ℕ}, j < filterIdx L P k →
      ∃ (e : ℕ) (he : e < k),
        P (L[e]'(Nat.lt_of_lt_of_le he hk)) = true ∧ filterIdx L P e = j
  | 0, _, j, hj => by simp at hj
  | k + 1, hk, j, hj => by
    have hk_lt : k < L.length := Nat.lt_of_succ_le hk
    rw [filterIdx_succ L P hk_lt] at hj
    by_cases hPk : P L[k] = true
    · simp only [hPk, ↓reduceIte] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · rcases exists_filterIdx_eq_of_lt L P (Nat.le_of_lt hk_lt) hlt with ⟨e, he, hPe, hfe⟩
        exact ⟨e, Nat.lt_succ_of_lt he, hPe, hfe⟩
      · exact ⟨k, Nat.lt_succ_self k, hPk, rfl⟩
    · simp only [hPk, Bool.false_eq_true, ↓reduceIte] at hj
      rcases exists_filterIdx_eq_of_lt L P (Nat.le_of_lt hk_lt) hj with ⟨e, he, hPe, hfe⟩
      exact ⟨e, Nat.lt_succ_of_lt he, hPe, hfe⟩

theorem exists_filterIdx_eq {α : Type*} (L : List α) (P : α → Bool)
    {j : ℕ} (hj : j < (L.filter P).length) :
    ∃ (e : ℕ) (he : e < L.length), P L[e] = true ∧ filterIdx L P e = j := by
  rw [← filterIdx_length] at hj
  exact exists_filterIdx_eq_of_lt L P (le_refl _) hj

/-- Boolean predicate testing whether an ordered pair `(u, v)` has both endpoints outside `Z`. -/
def edgeOutsideZPred {n : ℕ} (Z : Finset (Fin n)) (p : Fin n × Fin n) : Bool :=
  decide (p.1 ∉ Z ∧ p.2 ∉ Z)

/-- `(G.deleteVertices Z).directedEdgesList` is the sublist of `G.directedEdgesList` filtered by
`edgeOutsideZPred Z`. -/
theorem MultiDigraph.directedEdgesList_deleteVertices {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    (G.deleteVertices Z).directedEdgesList =
      G.directedEdgesList.filter (edgeOutsideZPred Z) := by
  unfold MultiDigraph.directedEdgesList edgeOutsideZPred
  rw [List.filter_flatMap]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.filter_flatMap]
  refine List.flatMap_congr fun v _ => ?_
  by_cases h : u ∉ Z ∧ v ∉ Z
  · simp [MultiDigraph.deleteVertices, h]
  · simp [MultiDigraph.deleteVertices, h]

/-- Number of edges of `G.deleteVertices Z` is at most `G.numEdges`. -/
theorem MultiDigraph.numEdges_deleteVertices_le {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    (G.deleteVertices Z).numEdges ≤ G.numEdges := by
  rw [← (G.deleteVertices Z).length_directedEdgesList, ← G.length_directedEdgesList,
    G.directedEdgesList_deleteVertices Z]
  exact List.length_filter_le _ _

/-! ### Section 2: Combinatorial Partial Branch-Decomposition Outside `Z` -/

/-- The subset of edges of `D : ComputeDigraph` that have both endpoints outside `Z`. -/
def edgesOutsideZ (D : ComputeDigraph) (Z : Finset (Fin D.numVerts)) : Finset (Fin D.numEdges) :=
  Finset.univ.filter (fun e : Fin D.numEdges => D.tail e ∉ Z ∧ D.head e ∉ Z)

@[simp]
theorem mem_edgesOutsideZ (D : ComputeDigraph) (Z : Finset (Fin D.numVerts))
    (e : Fin D.numEdges) :
    e ∈ edgesOutsideZ D Z ↔ D.tail e ∉ Z ∧ D.head e ∉ Z := by
  simp [edgesOutsideZ]

/-- Cut vertices outside `Z` for a tree edge `f` with respect to a partial edge set
`S ⊆ Fin D.numEdges`. -/
noncomputable def partialCutVertsOutsideZ {t : ℕ} (D : ComputeDigraph)
    (Z : Finset (Fin D.numVerts)) (S : Finset (Fin D.numEdges))
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin D.numEdges → Fin t) (f : Sym2 (Fin t)) : Finset (Fin D.numVerts) :=
  Finset.univ.filter (fun x : Fin D.numVerts =>
    x ∉ Z ∧
    ∃ e₁ ∈ S, ∃ e₂ ∈ S,
      digraphIncident D x e₁ ∧ digraphIncident D x e₂ ∧
      ¬ (T.deleteEdges {f}).Reachable (τ e₁) (τ e₂))

@[simp]
theorem mem_partialCutVertsOutsideZ {t : ℕ} (D : ComputeDigraph)
    (Z : Finset (Fin D.numVerts)) (S : Finset (Fin D.numEdges))
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin D.numEdges → Fin t) (f : Sym2 (Fin t)) (x : Fin D.numVerts) :
    x ∈ partialCutVertsOutsideZ D Z S T τ f ↔
      x ∉ Z ∧
      ∃ e₁ ∈ S, ∃ e₂ ∈ S,
        digraphIncident D x e₁ ∧ digraphIncident D x e₂ ∧
        ¬ (T.deleteEdges {f}).Reachable (τ e₁) (τ e₂) := by
  unfold partialCutVertsOutsideZ
  simp

/-- Any vertex incident with a single edge `e` of `D` belongs to `{D.head e, D.tail e}`, which has
cardinality at most `2`. -/
theorem mem_head_tail_of_digraphIncident (D : ComputeDigraph)
    {x : Fin D.numVerts} {e : Fin D.numEdges} (hinc : digraphIncident D x e) :
    x ∈ ({D.head e, D.tail e} : Finset (Fin D.numVerts)) := by
  rcases hinc with rfl | rfl <;> simp

theorem card_head_tail_le_two (D : ComputeDigraph) (e : Fin D.numEdges) :
    ({D.head e, D.tail e} : Finset (Fin D.numVerts)).card ≤ 2 :=
  Finset.card_le_two

/-- If an edge `e` is not in `edgesOutsideZ D Z`, then at most one of its endpoints lies outside `Z`:
any vertex `x ∉ Z` incident with `e` equals `if D.tail e ∉ Z then D.tail e else D.head e`. -/
theorem eq_outsideEndpoint_of_notMem_edgesOutsideZ (D : ComputeDigraph)
    (Z : Finset (Fin D.numVerts)) {e : Fin D.numEdges} (he : e ∉ edgesOutsideZ D Z)
    {x : Fin D.numVerts} (hxZ : x ∉ Z) (hinc : digraphIncident D x e) :
    x = if D.tail e ∉ Z then D.tail e else D.head e := by
  rw [mem_edgesOutsideZ, not_and_or, not_not, not_not] at he
  rcases hinc with rfl | rfl
  · have htailZ : D.tail e ∈ Z := he.resolve_right hxZ
    simp [htailZ]
  · simp [hxZ]

/-- Combinatorial invariant for a partial branch-decomposition `(parentTree t p, τ)` of `D` on an
edge subset `S ⊆ Fin D.numEdges` containing `edgesOutsideZ D Z`. -/
structure IsPartialDigraphBD (B : ℕ) (D : ComputeDigraph) (Z : Finset (Fin D.numVerts))
    (S : Finset (Fin D.numEdges)) (t : ℕ) (p : ℕ → ℕ) (τ : Fin D.numEdges → Fin t) : Prop where
  ht : 0 < t
  hp : ∀ z, 0 < z → z < t → p z < z
  hcub : IsCubicOrLeafTree (parentTree t p)
  hsub : edgesOutsideZ D Z ⊆ S
  hbij : Set.BijOn τ (S : Set (Fin D.numEdges)) (treeLeaves (parentTree t p) : Set (Fin t))
  hcut : ∀ f ∈ (parentTree t p).edgeFinset,
    (partialCutVertsOutsideZ D Z S (parentTree t p) τ f).card ≤ B

/-- Leaf-splitting step: inserting a new edge `e_new ∉ S` by subdividing the leaf `τ e_ref` for
a reference edge `e_ref ∈ S` preserves `IsPartialDigraphBD (max ω 2) D Z`. -/
theorem IsPartialDigraphBD.splitLeaf {ω : ℕ} {D : ComputeDigraph}
    {Z : Finset (Fin D.numVerts)} {S : Finset (Fin D.numEdges)}
    {t : ℕ} {p : ℕ → ℕ} {τ : Fin D.numEdges → Fin t}
    (hpart : IsPartialDigraphBD (max ω 2) D Z S t p τ)
    {e_new e_ref : Fin D.numEdges}
    (he_new : e_new ∉ S)
    (he_ref : e_ref ∈ S)
    (href_inc :
      let w := if D.tail e_new ∉ Z then D.tail e_new else D.head e_new
      w ∉ Z → (∃ e' ∈ S, digraphIncident D w e') → digraphIncident D w e_ref) :
    let v := τ e_ref
    let p' := splitLeafParent p t v.1
    let τ' : Fin D.numEdges → Fin (t + 2) := fun e =>
      if e = e_new then ⟨t, by omega⟩
      else if e = e_ref then ⟨t + 1, by omega⟩
      else ⟨(τ e).1, Nat.lt_trans (τ e).2 (by omega)⟩
    IsPartialDigraphBD (max ω 2) D Z (insert e_new S) (t + 2) p' τ' := by
  intro v p' τ'
  have ht := hpart.ht
  have hp := hpart.hp
  have hv_leaf : v ∈ treeLeaves (parentTree t p) := hpart.hbij.mapsTo he_ref
  have hp' : ∀ z, 0 < z → z < t + 2 → p' z < z := splitLeafParent_lt hp v.2
  have hcub' : IsCubicOrLeafTree (parentTree (t + 2) p') :=
    isCubicOrLeafTree_splitLeafParent hp ht hpart.hcub hv_leaf
  have hsub' : edgesOutsideZ D Z ⊆ insert e_new S :=
    Finset.Subset.trans hpart.hsub (Finset.subset_insert e_new S)
  have he_new_ne_ref : e_new ≠ e_ref := fun h => he_new (h ▸ he_ref)
  -- 1. Prove `Set.BijOn τ' (insert e_new S) (treeLeaves (parentTree (t + 2) p'))`
  have hbij' :
      Set.BijOn τ' ((insert e_new S : Finset (Fin D.numEdges)) : Set (Fin D.numEdges))
        (treeLeaves (parentTree (t + 2) p') : Set (Fin (t + 2))) := by
    refine ⟨fun e he => ?_, fun e₁ he₁ e₂ he₂ heq => ?_, fun u hu => ?_⟩
    · rw [Finset.mem_coe, Finset.mem_insert] at he
      rw [Finset.mem_coe, mem_treeLeaves_splitLeafParent_iff hp ht hv_leaf]
      by_cases h1 : e = e_new
      · subst h1
        simp [τ']
      · have heS : e ∈ S := he.resolve_left h1
        by_cases h2 : e = e_ref
        · subst h2
          simp [τ', h1]
        · right; right
          have hleaf_e : τ e ∈ treeLeaves (parentTree t p) := hpart.hbij.mapsTo heS
          have hne_v : (τ e).1 ≠ v.1 := by
            intro hval
            exact h2 (hpart.hbij.injOn heS he_ref (Fin.ext hval))
          simp only [τ', h1, h2, ↓reduceIte]
          exact ⟨(τ e).2, hleaf_e, hne_v⟩
    · rw [Finset.mem_coe, Finset.mem_insert] at he₁ he₂
      have hval := congrArg Fin.val heq
      by_cases h1a : e₁ = e_new <;> by_cases h2a : e₂ = e_new
      · exact h1a.trans h2a.symm
      · subst h1a
        have he₂S : e₂ ∈ S := he₂.resolve_left h2a
        by_cases h2b : e₂ = e_ref
        · subst h2b; simp [τ', he_new_ne_ref.symm] at hval
        · simp [τ', h2a, h2b] at hval
          have := (τ e₂).2; omega
      · subst h2a
        have he₁S : e₁ ∈ S := he₁.resolve_left h1a
        by_cases h1b : e₁ = e_ref
        · subst h1b; simp [τ', he_new_ne_ref.symm] at hval
        · simp [τ', h1a, h1b] at hval
          have := (τ e₁).2; omega
      · have he₁S : e₁ ∈ S := he₁.resolve_left h1a
        have he₂S : e₂ ∈ S := he₂.resolve_left h2a
        by_cases h1b : e₁ = e_ref <;> by_cases h2b : e₂ = e_ref
        · exact h1b.trans h2b.symm
        · subst h1b
          simp [τ', h1a, h2a, h2b] at hval
          have := (τ e₂).2; omega
        · subst h2b
          simp [τ', h1a, h2a, h1b] at hval
          have := (τ e₁).2; omega
        · simp [τ', h1a, h2a, h1b, h2b] at hval
          exact hpart.hbij.injOn he₁S he₂S (Fin.ext hval)
    · rw [Finset.mem_coe, mem_treeLeaves_splitLeafParent_iff hp ht hv_leaf] at hu
      rcases hu with hut | hut1 | ⟨hu_lt, hu_leaf, hu_ne⟩
      · refine ⟨e_new, by simp, ?_⟩
        ext; simp [τ', hut]
      · refine ⟨e_ref, by simp [he_ref], ?_⟩
        ext; simp [τ', he_new_ne_ref.symm, hut1]
      · rcases hpart.hbij.surjOn hu_leaf with ⟨e, heS, hτe⟩
        have he_ne_new : e ≠ e_new := fun h => he_new (h ▸ heS)
        have he_ne_ref : e ≠ e_ref := by
          intro h
          subst h
          exact hu_ne (congrArg Fin.val hτe.symm)
        refine ⟨e, Finset.mem_coe.mpr (Finset.mem_insert_of_mem heS), ?_⟩
        ext
        simp [τ', he_ne_new, he_ne_ref, congrArg Fin.val hτe]
  -- 2. Prove the cut-vertex bound for all edges `f' ∈ (parentTree (t + 2) p').edgeFinset`
  refine ⟨by omega, hp', hcub', hsub', hbij', fun f' hf' => ?_⟩
  rcases exists_pos_of_mem_edgeFinset_parentTree hp' hf' with ⟨y, hy_pos, rfl⟩
  by_cases hy_lt : y.1 < t
  · -- Case 1: Old tree edge `0 < y.1 < t`
    let y₀ : Fin t := ⟨y.1, hy_lt⟩
    let py₀ : Fin t := ⟨p y.1, Nat.lt_trans (hp y.1 hy_pos hy_lt) hy_lt⟩
    let f₀ : Sym2 (Fin t) := s(py₀, y₀)
    have hf₀ : f₀ ∈ (parentTree t p).edgeFinset := by
      rw [mem_edgeFinset, mem_edgeSet, parentTree_adj_of_lt hp]
      exact Or.inr ⟨hy_pos, rfl⟩
    have hsub_cut :
        partialCutVertsOutsideZ D Z (insert e_new S) (parentTree (t + 2) p') τ'
          s(⟨p' y.1, Nat.lt_trans (hp' y.1 hy_pos y.2) y.2⟩, y) ⊆
        partialCutVertsOutsideZ D Z S (parentTree t p) τ f₀ := by
      intro x hx
      rw [mem_partialCutVertsOutsideZ] at hx ⊢
      rcases hx with ⟨hxZ, e₁, he₁, e₂, he₂, hinc₁, hinc₂, hnr⟩
      rw [parentTree_deleteEdge_reachable_iff (by omega) hp' hy_pos] at hnr
      -- For every `e ∈ S`, `inSubtree p' y.1 (τ' e).1 = inSubtree p y.1 (τ e).1`
      have hinSub_S : ∀ e ∈ S, inSubtree p' y.1 (τ' e).1 = inSubtree p y.1 (τ e).1 := by
        intro e heS
        have he_ne_new : e ≠ e_new := fun h => he_new (h ▸ heS)
        by_cases he_eq_ref : e = e_ref
        · subst he_eq_ref
          simp only [τ', he_ne_new, ↓reduceIte]
          exact inSubtree_splitLeafParent_right hp v.2 hy_lt
        · simp only [τ', he_ne_new, he_eq_ref, ↓reduceIte]
          exact inSubtree_splitLeafParent_of_lt hp v.2 hy_lt (τ e).1 (τ e).2
      have hinSub_new : inSubtree p' y.1 (τ' e_new).1 = inSubtree p y.1 (τ e_ref).1 := by
        simp only [τ', ↓reduceIte]
        exact inSubtree_splitLeafParent_left hp ht v.2 hy_lt
      have he_new_not_out : e_new ∉ edgesOutsideZ D Z :=
        fun h => he_new (hpart.hsub h)
      -- Replace `e_new` by `e_ref` if needed
      let r₁ : Fin D.numEdges := if e₁ = e_new then e_ref else e₁
      let r₂ : Fin D.numEdges := if e₂ = e_new then e_ref else e₂
      have hr₁S : r₁ ∈ S := by
        dsimp [r₁]; split_ifs with h1
        · exact he_ref
        · exact (Finset.mem_insert.mp he₁).resolve_left h1
      have hr₂S : r₂ ∈ S := by
        dsimp [r₂]; split_ifs with h2
        · exact he_ref
        · exact (Finset.mem_insert.mp he₂).resolve_left h2
      have hinSub_r₁ : inSubtree p' y.1 (τ' e₁).1 = inSubtree p y.1 (τ r₁).1 := by
        dsimp [r₁]; split_ifs with h1
        · subst h1; exact hinSub_new
        · exact hinSub_S e₁ ((Finset.mem_insert.mp he₁).resolve_left h1)
      have hinSub_r₂ : inSubtree p' y.1 (τ' e₂).1 = inSubtree p y.1 (τ r₂).1 := by
        dsimp [r₂]; split_ifs with h2
        · subst h2; exact hinSub_new
        · exact hinSub_S e₂ ((Finset.mem_insert.mp he₂).resolve_left h2)
      have hne_sub : inSubtree p y.1 (τ r₁).1 ≠ inSubtree p y.1 (τ r₂).1 := by
        rwa [← hinSub_r₁, ← hinSub_r₂]
      have hinc_r₁ : digraphIncident D x r₁ := by
        dsimp [r₁]; split_ifs with h1
        · subst h1
          have hxw := eq_outsideEndpoint_of_notMem_edgesOutsideZ D Z he_new_not_out hxZ hinc₁
          have he₂_ne_new : e₂ ≠ e₁ := fun h => by subst h; exact hnr rfl
          have he₂S : e₂ ∈ S := (Finset.mem_insert.mp he₂).resolve_left he₂_ne_new
          rw [hxw] at hxZ hinc₂ ⊢
          exact href_inc hxZ ⟨e₂, he₂S, hinc₂⟩
        · exact hinc₁
      have hinc_r₂ : digraphIncident D x r₂ := by
        dsimp [r₂]; split_ifs with h2
        · subst h2
          have hxw := eq_outsideEndpoint_of_notMem_edgesOutsideZ D Z he_new_not_out hxZ hinc₂
          have he₁_ne_new : e₁ ≠ e₂ := fun h => by subst h; exact hnr rfl
          have he₁S : e₁ ∈ S := (Finset.mem_insert.mp he₁).resolve_left he₁_ne_new
          rw [hxw] at hxZ hinc₁ ⊢
          exact href_inc hxZ ⟨e₁, he₁S, hinc₁⟩
        · exact hinc₂
      refine ⟨hxZ, r₁, hr₁S, r₂, hr₂S, hinc_r₁, hinc_r₂, ?_⟩
      change ¬((parentTree t p).deleteEdges
        {s(⟨p y₀.1, Nat.lt_trans (hp y₀.1 hy_pos y₀.2) y₀.2⟩, y₀)}).Reachable (τ r₁) (τ r₂)
      rw [parentTree_deleteEdge_reachable_iff ht hp (x := y₀) hy_pos]
      exact hne_sub
    exact le_trans (Finset.card_le_card hsub_cut) (hpart.hcut f₀ hf₀)
  · -- Case 2: New leaf edge `y.1 = t` or `y.1 = t + 1`
    rcases (by omega : y.1 = t ∨ y.1 = t + 1) with hyt | hyt1
    · -- `y.1 = t` (leaf edge of `e_new`)
      have hsub_new :
          partialCutVertsOutsideZ D Z (insert e_new S) (parentTree (t + 2) p') τ'
            s(⟨p' y.1, Nat.lt_trans (hp' y.1 hy_pos y.2) y.2⟩, y) ⊆
          {D.head e_new, D.tail e_new} := by
        intro x hx
        rw [mem_partialCutVertsOutsideZ] at hx
        rcases hx with ⟨_, e₁, he₁, e₂, he₂, hinc₁, hinc₂, hnr⟩
        rw [parentTree_deleteEdge_reachable_iff (by omega) hp' hy_pos] at hnr
        rw [hyt, inSubtree_splitLeafParent_new_left hp ht v.2 (τ' e₁).1 (τ' e₁).2,
          inSubtree_splitLeafParent_new_left hp ht v.2 (τ' e₂).1 (τ' e₂).2] at hnr
        have h_one_eq_t : (τ' e₁).1 = t ∨ (τ' e₂).1 = t := by
          by_contra hnot
          rcases not_or.mp hnot with ⟨h1, h2⟩
          simp [h1, h2] at hnr
        have h_eq_new : ∀ {e : Fin D.numEdges}, (τ' e).1 = t → e = e_new := by
          intro e hval
          by_contra hne
          by_cases href : e = e_ref
          · simp [τ', href, he_new_ne_ref.symm] at hval
          · simp [τ', hne, href] at hval
            have := (τ e).2; omega
        rcases h_one_eq_t with h1 | h2
        · rw [h_eq_new h1] at hinc₁
          exact mem_head_tail_of_digraphIncident D hinc₁
        · rw [h_eq_new h2] at hinc₂
          exact mem_head_tail_of_digraphIncident D hinc₂
      calc (partialCutVertsOutsideZ D Z (insert e_new S) (parentTree (t + 2) p') τ' _).card
        _ ≤ ({D.head e_new, D.tail e_new} : Finset (Fin D.numVerts)).card :=
          Finset.card_le_card hsub_new
        _ ≤ 2 := card_head_tail_le_two D e_new
        _ ≤ max ω 2 := Nat.le_max_right ω 2
    · -- `y.1 = t + 1` (leaf edge of `e_ref`)
      have hsub_ref :
          partialCutVertsOutsideZ D Z (insert e_new S) (parentTree (t + 2) p') τ'
            s(⟨p' y.1, Nat.lt_trans (hp' y.1 hy_pos y.2) y.2⟩, y) ⊆
          {D.head e_ref, D.tail e_ref} := by
        intro x hx
        rw [mem_partialCutVertsOutsideZ] at hx
        rcases hx with ⟨_, e₁, he₁, e₂, he₂, hinc₁, hinc₂, hnr⟩
        rw [parentTree_deleteEdge_reachable_iff (by omega) hp' hy_pos] at hnr
        rw [hyt1, inSubtree_splitLeafParent_new_right hp v.2 (τ' e₁).1 (τ' e₁).2,
          inSubtree_splitLeafParent_new_right hp v.2 (τ' e₂).1 (τ' e₂).2] at hnr
        have h_one_eq_t1 : (τ' e₁).1 = t + 1 ∨ (τ' e₂).1 = t + 1 := by
          by_contra hnot
          rcases not_or.mp hnot with ⟨h1, h2⟩
          simp [h1, h2] at hnr
        have h_eq_ref : ∀ {e : Fin D.numEdges}, (τ' e).1 = t + 1 → e = e_ref := by
          intro e hval
          by_contra href
          by_cases hne : e = e_new
          · simp [τ', hne] at hval
          · simp [τ', hne, href] at hval
            have := (τ e).2; omega
        rcases h_one_eq_t1 with h1 | h2
        · rw [h_eq_ref h1] at hinc₁
          exact mem_head_tail_of_digraphIncident D hinc₁
        · rw [h_eq_ref h2] at hinc₂
          exact mem_head_tail_of_digraphIncident D hinc₂
      calc (partialCutVertsOutsideZ D Z (insert e_new S) (parentTree (t + 2) p') τ' _).card
        _ ≤ ({D.head e_ref, D.tail e_ref} : Finset (Fin D.numVerts)).card :=
          Finset.card_le_card hsub_ref
        _ ≤ 2 := card_head_tail_le_two D e_ref
        _ ≤ max ω 2 := Nat.le_max_right ω 2

/-- When `S = Finset.univ` and `Z.card ≤ ξ`, a partial branch-decomposition of width `≤ B` outside
`Z` is a full branch-decomposition of `D` of width `≤ B + ξ`. -/
theorem IsPartialDigraphBD.to_isDigraphBranchDecompOfWidthLe {B ξ : ℕ}
    {D : ComputeDigraph} {Z : Finset (Fin D.numVerts)}
    {t : ℕ} {p : ℕ → ℕ} {τ : Fin D.numEdges → Fin t}
    (hpart : IsPartialDigraphBD B D Z Finset.univ t p τ)
    (hZ : Z.card ≤ ξ) :
    IsDigraphBranchDecompOfWidthLe (B + ξ) D (parentTree t p) τ := by
  refine ⟨hpart.hcub, ?_, fun f hf => ?_⟩
  · simpa using hpart.hbij
  · have hsub :
        digraphTreeEdgeCutVerts D (parentTree t p) τ f ⊆
          partialCutVertsOutsideZ D Z Finset.univ (parentTree t p) τ f ∪ Z := by
      intro x hx
      rw [mem_digraphTreeEdgeCutVerts_iff] at hx
      rcases hx with ⟨e₁, e₂, hinc₁, hinc₂, hnr⟩
      rw [Finset.mem_union, mem_partialCutVertsOutsideZ]
      by_cases hxZ : x ∈ Z
      · exact Or.inr hxZ
      · exact Or.inl ⟨hxZ, e₁, Finset.mem_univ e₁, e₂, Finset.mem_univ e₂, hinc₁, hinc₂, hnr⟩
    unfold digraphTreeEdgeOrder
    calc (digraphTreeEdgeCutVerts D (parentTree t p) τ f).card
      _ ≤ (partialCutVertsOutsideZ D Z Finset.univ (parentTree t p) τ f ∪ Z).card :=
        Finset.card_le_card hsub
      _ ≤ (partialCutVertsOutsideZ D Z Finset.univ (parentTree t p) τ f).card + Z.card :=
        Finset.card_union_le _ _
      _ ≤ B + ξ := Nat.add_le_add (hpart.hcut f hf) hZ

/-- Base case B2 (`|E(G_i \ Z)| < 2`, `|E(G_i)| ≥ 2`): given two distinct edges `e₀ ≠ e₁` of `D`
such that `edgesOutsideZ D Z ⊆ {e₀, e₁}`, the 2-vertex tree `parentTree 2 (fun _ => 0)` with
`τ e := if e = e₀ then 0 else 1` is a valid `IsPartialDigraphBD (max ω 2)` on `{e₀, e₁}`. -/
theorem isPartialDigraphBD_of_two_edges (ω : ℕ) (D : ComputeDigraph)
    (Z : Finset (Fin D.numVerts)) {e₀ e₁ : Fin D.numEdges} (hne : e₀ ≠ e₁)
    (hsub : edgesOutsideZ D Z ⊆ ({e₀, e₁} : Finset (Fin D.numEdges))) :
    IsPartialDigraphBD (max ω 2) D Z ({e₀, e₁} : Finset (Fin D.numEdges)) 2 (fun _ => 0)
      (fun e => if e = e₀ then ⟨0, by omega⟩ else ⟨1, by omega⟩) where
  ht := by omega
  hp := fun z hz_pos hz_lt => by omega
  hcub := isCubicOrLeafTree_parentTree_two
  hsub := hsub
  hbij := by
    rw [treeLeaves_parentTree_two]
    refine ⟨fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _), fun a ha b hb heq => ?_, fun v _ => ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      have hval := congrArg Fin.val heq
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · simp [hne.symm] at hval
      · simp [hne.symm] at hval
      · rfl
    · fin_cases v
      · exact ⟨e₀, by simp, by simp⟩
      · exact ⟨e₁, by simp, by simp [hne.symm]⟩
  hcut := by
    intro f hf
    have hsub_cut :
        partialCutVertsOutsideZ D Z ({e₀, e₁} : Finset (Fin D.numEdges))
          (parentTree 2 (fun _ => 0))
          (fun e => if e = e₀ then ⟨0, by omega⟩ else ⟨1, by omega⟩) f ⊆
        {D.head e₀, D.tail e₀} := by
      intro x hx
      rw [mem_partialCutVertsOutsideZ] at hx
      rcases hx with ⟨_, a, ha, b, hb, hinc_a, hinc_b, hnr⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl
      · exact mem_head_tail_of_digraphIncident D hinc_a
      · rcases hb with rfl | rfl
        · exact mem_head_tail_of_digraphIncident D hinc_b
        · exfalso; exact hnr (Reachable.refl _)
    calc (partialCutVertsOutsideZ D Z ({e₀, e₁} : Finset (Fin D.numEdges)) _ _ f).card
      _ ≤ ({D.head e₀, D.tail e₀} : Finset (Fin D.numVerts)).card :=
        Finset.card_le_card hsub_cut
      _ ≤ 2 := card_head_tail_le_two D e₀
      _ ≤ max ω 2 := Nat.le_max_right ω 2

theorem edgeOutsideZPred_getElem_iff {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (e : Fin G.toComputeDigraph.numEdges) :
    edgeOutsideZPred Z (G.directedEdgesList[e.1]'e.2) = true ↔
      e ∈ edgesOutsideZ G.toComputeDigraph Z := by
  rw [mem_edgesOutsideZ]
  simp [edgeOutsideZPred, MultiDigraph.toComputeDigraph]

theorem filterIdx_lt_numEdges_deleteVertices {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    {e : Fin G.toComputeDigraph.numEdges} (he : e ∈ edgesOutsideZ G.toComputeDigraph Z) :
    filterIdx G.directedEdgesList (edgeOutsideZPred Z) e.1 <
      (G.deleteVertices Z).toComputeDigraph.numEdges := by
  have hP : edgeOutsideZPred Z (G.directedEdgesList[e.1]'e.2) = true :=
    (edgeOutsideZPred_getElem_iff G Z e).mpr he
  have hlt := filterIdx_lt_length_filter G.directedEdgesList (edgeOutsideZPred Z) e.2 hP
  rwa [← G.directedEdgesList_deleteVertices Z] at hlt

/-- Cardinality of `edgesOutsideZ G.toComputeDigraph Z` equals `(G.deleteVertices Z).numEdges`. -/
theorem card_edgesOutsideZ_eq {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    (edgesOutsideZ G.toComputeDigraph Z).card = (G.deleteVertices Z).numEdges := by
  rw [← (G.deleteVertices Z).length_directedEdgesList,
    ← Finset.card_fin (G.deleteVertices Z).directedEdgesList.length]
  refine Finset.card_bij
    (fun (e : Fin G.toComputeDigraph.numEdges) (he : e ∈ edgesOutsideZ G.toComputeDigraph Z) =>
      (⟨filterIdx G.directedEdgesList (edgeOutsideZPred Z) e.1,
        filterIdx_lt_numEdges_deleteVertices G Z he⟩ :
          Fin (G.deleteVertices Z).directedEdgesList.length))
    (fun _ _ => Finset.mem_univ _)
    (fun e₁ he₁ e₂ he₂ heq => ?_)
    (fun j _ => ?_)
  · have hval :
        filterIdx G.directedEdgesList (edgeOutsideZPred Z) e₁.1 =
          filterIdx G.directedEdgesList (edgeOutsideZPred Z) e₂.1 :=
      congrArg Fin.val heq
    have hP₁ : edgeOutsideZPred Z (G.directedEdgesList[e₁.1]'e₁.2) = true :=
      (edgeOutsideZPred_getElem_iff G Z e₁).mpr he₁
    have hP₂ : edgeOutsideZPred Z (G.directedEdgesList[e₂.1]'e₂.2) = true :=
      (edgeOutsideZPred_getElem_iff G Z e₂).mpr he₂
    rcases lt_trichotomy e₁.1 e₂.1 with hlt | heq_val | hgt
    · have := filterIdx_strictMono_of_true G.directedEdgesList (edgeOutsideZPred Z)
        hlt (Nat.le_of_lt e₂.2) hP₁
      omega
    · exact Fin.ext heq_val
    · have := filterIdx_strictMono_of_true G.directedEdgesList (edgeOutsideZPred Z)
        hgt (Nat.le_of_lt e₁.2) hP₂
      omega
  · have hj_lt : j.1 < (G.directedEdgesList.filter (edgeOutsideZPred Z)).length := by
      rw [← G.directedEdgesList_deleteVertices Z]
      exact j.2
    rcases exists_filterIdx_eq G.directedEdgesList (edgeOutsideZPred Z) hj_lt with
      ⟨e, he_lt, hPe, hfe⟩
    let eFin : Fin G.toComputeDigraph.numEdges := ⟨e, he_lt⟩
    have he_mem : eFin ∈ edgesOutsideZ G.toComputeDigraph Z :=
      (edgeOutsideZPred_getElem_iff G Z eFin).mp hPe
    exact ⟨eFin, he_mem, Fin.ext hfe⟩

/-- Base case B1 (`|E(G_i \ Z)| ≥ 2`): a branch-decomposition of `(G.deleteVertices Z).toComputeDigraph`
of width `≤ ω` lifts via `filterIdx` to a partial branch-decomposition of `G.toComputeDigraph` on
`edgesOutsideZ G.toComputeDigraph Z` of width `≤ max ω 2`. -/
theorem isPartialDigraphBD_of_deleteVertices {n t₀ ω : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) {par₀ f_tau₀ : ℕ → ℕ}
    (ht₀ : 0 < t₀)
    (hpar₀ : ∀ z, 0 < z → z < t₀ → par₀ z < z)
    (htau₀ : ∀ j < (G.deleteVertices Z).toComputeDigraph.numEdges, f_tau₀ j < t₀)
    (hbd₀ : IsDigraphBranchDecompOfWidthLe ω (G.deleteVertices Z).toComputeDigraph
      (parentTree t₀ par₀) (fun j => ⟨f_tau₀ j.1, htau₀ j.1 j.2⟩))
    {τ : Fin G.toComputeDigraph.numEdges → Fin t₀}
    (hτ : ∀ (e : Fin G.toComputeDigraph.numEdges),
        e ∈ edgesOutsideZ G.toComputeDigraph Z →
      (τ e).1 = f_tau₀ (filterIdx G.directedEdgesList (edgeOutsideZPred Z) e.1)) :
    IsPartialDigraphBD (max ω 2) G.toComputeDigraph Z
      (edgesOutsideZ G.toComputeDigraph Z) t₀ par₀ τ where
  ht := ht₀
  hp := hpar₀
  hcub := hbd₀.1
  hsub := Finset.Subset.refl _
  hbij := by
    refine ⟨fun e he => ?_, fun e₁ he₁ e₂ he₂ heq => ?_, fun v hv => ?_⟩
    · have hj_lt := filterIdx_lt_numEdges_deleteVertices G Z he
      let j : Fin (G.deleteVertices Z).toComputeDigraph.numEdges := ⟨_, hj_lt⟩
      have hτ_eq : τ e = ⟨f_tau₀ j.1, htau₀ j.1 j.2⟩ := Fin.ext (hτ e he)
      rw [hτ_eq]
      exact hbd₀.2.1.1 (Set.mem_univ j)
    · have hj₁_lt := filterIdx_lt_numEdges_deleteVertices G Z he₁
      have hj₂_lt := filterIdx_lt_numEdges_deleteVertices G Z he₂
      let j₁ : Fin (G.deleteVertices Z).toComputeDigraph.numEdges := ⟨_, hj₁_lt⟩
      let j₂ : Fin (G.deleteVertices Z).toComputeDigraph.numEdges := ⟨_, hj₂_lt⟩
      have hτ₁ : τ e₁ = ⟨f_tau₀ j₁.1, htau₀ j₁.1 j₁.2⟩ := Fin.ext (hτ e₁ he₁)
      have hτ₂ : τ e₂ = ⟨f_tau₀ j₂.1, htau₀ j₂.1 j₂.2⟩ := Fin.ext (hτ e₂ he₂)
      have hj_eq : j₁ = j₂ :=
        hbd₀.2.1.2.1 (Set.mem_univ j₁) (Set.mem_univ j₂) (hτ₁.symm.trans (heq.trans hτ₂))
      have hval :
          filterIdx G.directedEdgesList (edgeOutsideZPred Z) e₁.1 =
            filterIdx G.directedEdgesList (edgeOutsideZPred Z) e₂.1 :=
        congrArg Fin.val hj_eq
      have hP₁ : edgeOutsideZPred Z (G.directedEdgesList[e₁.1]'e₁.2) = true :=
        (edgeOutsideZPred_getElem_iff G Z e₁).mpr he₁
      have hP₂ : edgeOutsideZPred Z (G.directedEdgesList[e₂.1]'e₂.2) = true :=
        (edgeOutsideZPred_getElem_iff G Z e₂).mpr he₂
      rcases lt_trichotomy e₁.1 e₂.1 with hlt | heq_val | hgt
      · have := filterIdx_strictMono_of_true G.directedEdgesList (edgeOutsideZPred Z)
          hlt (Nat.le_of_lt e₂.2) hP₁
        omega
      · exact Fin.ext heq_val
      · have := filterIdx_strictMono_of_true G.directedEdgesList (edgeOutsideZPred Z)
          hgt (Nat.le_of_lt e₁.2) hP₂
        omega
    · rcases hbd₀.2.1.2.2 hv with ⟨j, _, hj_eq⟩
      have hj_lt : j.1 < (G.directedEdgesList.filter (edgeOutsideZPred Z)).length := by
        rw [← G.directedEdgesList_deleteVertices Z]
        exact j.2
      rcases exists_filterIdx_eq G.directedEdgesList (edgeOutsideZPred Z) hj_lt with
        ⟨e, he_lt, hPe, hfe⟩
      let eFin : Fin G.toComputeDigraph.numEdges := ⟨e, he_lt⟩
      have he_mem : eFin ∈ edgesOutsideZ G.toComputeDigraph Z :=
        (edgeOutsideZPred_getElem_iff G Z eFin).mp hPe
      refine ⟨eFin, he_mem, ?_⟩
      apply Fin.ext
      rw [hτ eFin he_mem, hfe, ← congrArg Fin.val hj_eq]
  hcut := by
    intro f hf
    have hsub_cut :
        partialCutVertsOutsideZ G.toComputeDigraph Z (edgesOutsideZ G.toComputeDigraph Z)
          (parentTree t₀ par₀) τ f ⊆
        digraphTreeEdgeCutVerts (G.deleteVertices Z).toComputeDigraph
          (parentTree t₀ par₀) (fun j => ⟨f_tau₀ j.1, htau₀ j.1 j.2⟩) f := by
      intro x hx
      rw [mem_partialCutVertsOutsideZ] at hx
      rw [mem_digraphTreeEdgeCutVerts_iff]
      rcases hx with ⟨_, e₁, he₁, e₂, he₂, hinc₁, hinc₂, hnr⟩
      have hj₁_lt := filterIdx_lt_numEdges_deleteVertices G Z he₁
      have hj₂_lt := filterIdx_lt_numEdges_deleteVertices G Z he₂
      let j₁ : Fin (G.deleteVertices Z).toComputeDigraph.numEdges := ⟨_, hj₁_lt⟩
      let j₂ : Fin (G.deleteVertices Z).toComputeDigraph.numEdges := ⟨_, hj₂_lt⟩
      have hP₁ : edgeOutsideZPred Z (G.directedEdgesList[e₁.1]'e₁.2) = true :=
        (edgeOutsideZPred_getElem_iff G Z e₁).mpr he₁
      have hP₂ : edgeOutsideZPred Z (G.directedEdgesList[e₂.1]'e₂.2) = true :=
        (edgeOutsideZPred_getElem_iff G Z e₂).mpr he₂
      have hget₁ :
          (G.deleteVertices Z).directedEdgesList[j₁.1]'j₁.2 =
            G.directedEdgesList[e₁.1]'e₁.2 := by
        have h1 := getElem_filter_filterIdx G.directedEdgesList (edgeOutsideZPred Z) e₁.2 hP₁
        simpa [G.directedEdgesList_deleteVertices Z, j₁] using h1
      have hget₂ :
          (G.deleteVertices Z).directedEdgesList[j₂.1]'j₂.2 =
            G.directedEdgesList[e₂.1]'e₂.2 := by
        have h2 := getElem_filter_filterIdx G.directedEdgesList (edgeOutsideZPred Z) e₂.2 hP₂
        simpa [G.directedEdgesList_deleteVertices Z, j₂] using h2
      have hinc_j₁ : digraphIncident (G.deleteVertices Z).toComputeDigraph x j₁ := by
        unfold digraphIncident MultiDigraph.toComputeDigraph at hinc₁ ⊢
        dsimp only at hinc₁ ⊢
        rwa [hget₁]
      have hinc_j₂ : digraphIncident (G.deleteVertices Z).toComputeDigraph x j₂ := by
        unfold digraphIncident MultiDigraph.toComputeDigraph at hinc₂ ⊢
        dsimp only at hinc₂ ⊢
        rwa [hget₂]
      have hτ₁ : τ e₁ = ⟨f_tau₀ j₁.1, htau₀ j₁.1 j₁.2⟩ := Fin.ext (hτ e₁ he₁)
      have hτ₂ : τ e₂ = ⟨f_tau₀ j₂.1, htau₀ j₂.1 j₂.2⟩ := Fin.ext (hτ e₂ he₂)
      refine ⟨j₁, j₂, hinc_j₁, hinc_j₂, ?_⟩
      rwa [← hτ₁, ← hτ₂]
    calc (partialCutVertsOutsideZ G.toComputeDigraph Z _ _ τ f).card
      _ ≤ digraphTreeEdgeOrder (G.deleteVertices Z).toComputeDigraph
            (parentTree t₀ par₀) (fun j => ⟨f_tau₀ j.1, htau₀ j.1 j.2⟩) f :=
        Finset.card_le_card hsub_cut
      _ ≤ ω := hbd₀.2.2 f hf
      _ ≤ max ω 2 := Nat.le_max_left ω 2

/-! ### Section 3: Expanding `G.enc` into `(tailArr, headArr)` on the Word RAM -/

theorem pair_idx_inj {n : ℕ} {u₁ v₁ u₂ v₂ : Fin n}
    (h : u₁.1 * n + v₁.1 = u₂.1 * n + v₂.1) : u₁ = u₂ ∧ v₁ = v₂ := by
  have hu : u₁.1 = u₂.1 := by
    rcases lt_trichotomy u₁.1 u₂.1 with hlt | heq | hgt
    · nlinarith [v₁.2]
    · exact heq
    · nlinarith [v₂.2]
  have hv : v₁.1 = v₂.1 := by rw [hu] at h; omega
  exact ⟨Fin.ext hu, Fin.ext hv⟩

/-- Loop body of `buildMultMatProg`: reads the `k`-th active pair `(u, v, mult)` from `a_G`
(`r_54 = k`) and writes `a_mat[u * n + v] := mult` (`r_26 = n`). -/
def buildMultMatBody (a_G a_mat : Arr) : Cmd :=
  .seq (.assign 55 (.op .add (.const 2) (.op .mul (.const 3) (.reg 54))))
    (.seq (.assign 56 (.read a_G (.reg 55)))
      (.seq (.assign 57 (.read a_G (.op .add (.reg 55) (.const 1))))
        (.seq (.assign 58 (.read a_G (.op .add (.reg 55) (.const 2))))
          (.seq (.assign 59 (.op .add (.op .mul (.reg 56) (.reg 26)) (.reg 57)))
            (.write a_mat (.reg 59) (.reg 58))))))

/-- Word RAM program building the `n × n` multiplicity matrix `a_mat[u * n + v] = G.edgeMult u v`
from `s.arrs a_G = G.enc` (with `s.regs 26 = n` and `s.regs 27 = G.numActivePairs`). -/
def buildMultMatProg (a_G a_mat : Arr) : Cmd :=
  .seq (.assign 53 (.op .mul (.reg 26) (.reg 26)))
    (.seq (.alloc a_mat (.reg 53))
      (.seq (.assign 54 (.const 0))
        (forUp 54 (.reg 27) (buildMultMatBody a_G a_mat))))

theorem buildMultMatProg_exec {w n : ℕ} (G : MultiDigraph n) (a_G a_mat : Arr)
    (hne : a_G ≠ a_mat)
    (hw : 3 < 2 ^ w)
    (hnn_w : n * n < 2 ^ w)
    (henc_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w)
    {s : State}
    (hG : s.arrs a_G = G.enc)
    (hr26 : s.regs 26 = n)
    (hr27 : s.regs 27 = G.numActivePairs) :
    ∃ s' t,
      Exec w (buildMultMatProg a_G a_mat) s s' t ∧
      t ≤ 45 * (n * n) + 45 * G.numActivePairs + 20 ∧
      (∃ hlen : (s'.arrs a_mat).length = n * n,
        ∀ u v : Fin n,
          (s'.arrs a_mat)[u.1 * n + v.1]'(by
            rw [hlen]; nlinarith [u.2, v.2]) = G.edgeMult u v) ∧
      (∀ a : Arr, a ≠ a_mat → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 53 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · omega
    · nlinarith
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  -- 1. r_53 := n * n
  let s₁ := s.setReg 53 (n * n)
  have hex₁ : Exec w (.assign 53 (.op .mul (.reg 26) (.reg 26))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr26, hn_w, hnn_w])
  -- 2. alloc a_mat (.reg 53)
  let s₂ := s₁.setArr a_mat (List.replicate (n * n) 0)
  have hex₂ : Exec w (.alloc a_mat (.reg 53)) s₁ s₂ (1 + n * n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hnn_w])
  -- 3. r_54 := 0
  let s₃ := s₂.setReg 54 0
  have hex₃ : Exec w (.assign 54 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 4. forUp 54 (.reg 27) (buildMultMatBody a_G a_mat)
  let Inv (k : ℕ) (st : State) : Prop :=
    st.arrs a_G = G.enc ∧
    st.regs 26 = n ∧
    st.regs 27 = G.numActivePairs ∧
    st.regs 54 = k ∧
    (∃ hlen : (st.arrs a_mat).length = n * n,
      (∀ j (hj : j < k) (hj' : j < G.activePairsList.length),
        let p := G.activePairsList[j]'hj'
        (st.arrs a_mat)[p.1.1 * n + p.2.1]'(by rw [hlen]; nlinarith [p.1.2, p.2.2]) =
          G.edgeMult p.1 p.2) ∧
      (∀ u v : Fin n,
        (∀ j (hj : j < k) (hj' : j < G.activePairsList.length),
          G.activePairsList[j]'hj' ≠ (u, v)) →
        (st.arrs a_mat)[u.1 * n + v.1]'(by rw [hlen]; nlinarith [u.2, v.2]) = 0)) ∧
    (∀ a : Arr, a ≠ a_mat → st.arrs a = s.arrs a) ∧
    (∀ r : Reg, r < 53 → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₃ := by
    refine ⟨by simp [s₃, s₂, s₁, hne, hG],
      by simp [s₃, s₂, s₁, hr26],
      by simp [s₃, s₂, s₁, hr27],
      by simp [s₃],
      ⟨by simp [s₃, s₂],
       fun j hj _ => by omega,
       fun u v _ => by simp [s₃, s₂]⟩,
      fun a ha => by simp [s₃, s₂, s₁, ha],
      fun r hr => ?_⟩
    have hr54 : r ≠ 54 := by intro h; subst h; revert hr; decide
    have hr53 : r ≠ 53 := by intro h; subst h; revert hr; decide
    simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hr54, State.setReg_regs_ne _ _ hr53]
  have hLoop :
      ⦃Inv 0⦄[w] forUp 54 (.reg 27) (buildMultMatBody a_G a_mat) ⦃Inv G.numActivePairs⦄ ≤
        fun _ => 3 + G.numActivePairs * (7 + 28) := by
    apply Triple.forUp_const Inv G.numActivePairs 28 h1_w hm'_w
    · intro k _ st ⟨_, _, hr27_k, hr54_k, _, _, _⟩
      exact ⟨hr54_k, by simp [Expr.eval, checkWord, hr27_k, hm'_w]⟩
    · intro k hk st ⟨hG_k, hr26_k, hr27_k, hr54_k, ⟨hlen_k, hset_k, hzero_k⟩, harr_k, hreg_k⟩
      have hk_len : k < G.activePairsList.length := hk
      let p := G.activePairsList[k]'hk_len
      let u := p.1
      let v := p.2
      let mult := G.edgeMult u v
      have hlen_enc : (st.arrs a_G).length = 2 + 3 * G.numActivePairs := by
        rw [hG_k, G.length_enc]
      have hlt0 : 2 + 3 * k < (st.arrs a_G).length := by omega
      have hlt1 : 2 + 3 * k + 1 < (st.arrs a_G).length := by omega
      have hlt2 : 2 + 3 * k + 2 < (st.arrs a_G).length := by omega
      have hget_u : (st.arrs a_G)[2 + 3 * k]'hlt0 = u.1 := by
        have h1 : (st.arrs a_G)[2 + 3 * k]'hlt0 = (G.enc)[2 + 3 * k]'(by rw [G.length_enc]; omega) := by
          simp only [hG_k]
        rw [h1]
        unfold MultiDigraph.enc
        rw [List.getElem_append_right (by simp)]
        simpa [Nat.add_sub_cancel_left] using G.getElem_flatTriples_fst G.activePairsList k hk_len
      have hget_v : (st.arrs a_G)[2 + 3 * k + 1]'hlt1 = v.1 := by
        have h1 : (st.arrs a_G)[2 + 3 * k + 1]'hlt1 = (G.enc)[2 + 3 * k + 1]'(by rw [G.length_enc]; omega) := by
          simp only [hG_k]
        rw [h1]
        unfold MultiDigraph.enc
        rw [List.getElem_append_right (by simp; omega)]
        have hidx : 2 + 3 * k + 1 - 2 = 3 * k + 1 := by omega
        simpa [hidx] using G.getElem_flatTriples_snd G.activePairsList k hk_len
      have hget_m : (st.arrs a_G)[2 + 3 * k + 2]'hlt2 = mult := by
        have h1 : (st.arrs a_G)[2 + 3 * k + 2]'hlt2 = (G.enc)[2 + 3 * k + 2]'(by rw [G.length_enc]; omega) := by
          simp only [hG_k]
        rw [h1]
        unfold MultiDigraph.enc
        rw [List.getElem_append_right (by simp)]
        have hidx : 2 + 3 * k + 2 - 2 = 3 * k + 2 := by omega
        simpa [hidx] using G.getElem_flatTriples_mult G.activePairsList k hk_len
      have hk_w : k < 2 ^ w := by omega
      have h3k_w : 3 * k < 2 ^ w := by omega
      have h23k_w : 2 + 3 * k < 2 ^ w := by omega
      have h23k1_w : 2 + 3 * k + 1 < 2 ^ w := by omega
      have h23k2_w : 2 + 3 * k + 2 < 2 ^ w := by omega
      have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
      have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
      have hmult_w : mult < 2 ^ w :=
        Nat.lt_of_le_of_lt (G.edgeMult_le_numEdges u v) hm_w
      have hidx_lt : u.1 * n + v.1 < n * n := by nlinarith [u.2, v.2]
      have hidx_w : u.1 * n + v.1 < 2 ^ w := by omega
      have hun_w : u.1 * n < 2 ^ w := by omega
      let st₁ := st.setReg 55 (2 + 3 * k)
      have hex_55 : Exec w (.assign 55 (.op .add (.const 2) (.op .mul (.const 3) (.reg 54)))) st st₁ 6 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr54_k, hk_w, hw, h2_w, h3k_w, h23k_w])
      let st₂ := st₁.setReg 56 u.1
      have hex_56 : Exec w (.assign 56 (.read a_G (.reg 55))) st₁ st₂ 3 :=
        .assign (by simp [st₁, Expr.eval, checkWord, h23k_w, hlt0, hget_u, hu_w])
      let st₃ := st₂.setReg 57 v.1
      have hex_57 : Exec w (.assign 57 (.read a_G (.op .add (.reg 55) (.const 1)))) st₂ st₃ 5 :=
        .assign (by simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h23k_w, h1_w, h23k1_w,
            hlt1, hget_v, hv_w])
      let st₄ := st₃.setReg 58 mult
      have hex_58 : Exec w (.assign 58 (.read a_G (.op .add (.reg 55) (.const 2)))) st₃ st₄ 5 :=
        .assign (by simp [st₃, st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h23k_w, h2_w, h23k2_w,
            hlt2, hget_m, hmult_w])
      let st₅ := st₄.setReg 59 (u.1 * n + v.1)
      have hex_59 : Exec w (.assign 59 (.op .add (.op .mul (.reg 56) (.reg 26)) (.reg 57))) st₄ st₅ 6 :=
        .assign (by simp [st₄, st₃, st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr26_k, hu_w, hn_w, hun_w, hv_w, hidx_w])
      let st₆ := st₅.writeArr a_mat (u.1 * n + v.1) mult
      have hex_w : Exec w (.write a_mat (.reg 59) (.reg 58)) st₅ st₆ 3 :=
        .write (by simp [st₅, Expr.eval, checkWord, hidx_w])
          (by simp [st₅, st₄, Expr.eval, checkWord, hmult_w])
          (by simp [st₅, st₄, st₃, st₂, st₁, hlen_k, hidx_lt])
      refine ⟨st₆, 28,
        .seq hex_55 (.seq hex_56 (.seq hex_57 (.seq hex_58 (.seq hex_59 hex_w)))),
        le_refl 28,
        ⟨by simp [st₆, st₅, st₄, st₃, st₂, st₁, hne, hG_k],
         by simp [st₆, st₅, st₄, st₃, st₂, st₁, hr26_k],
         by simp [st₆, st₅, st₄, st₃, st₂, st₁, hr27_k],
         by simp [st₆],
         ⟨by simp [st₆, st₅, st₄, st₃, st₂, st₁, hlen_k],
          fun j hj hj' => ?_,
          fun u' v' hne_uv => ?_⟩,
         fun a ha => by simp [st₆, st₅, st₄, st₃, st₂, st₁, ha, harr_k a ha],
         fun r hr => ?_⟩,
        by simp [st₆, st₅, st₄, st₃, st₂, st₁, hr54_k]⟩
      · simp only [st₆, st₅, st₄, st₃, st₂, st₁, State.setReg_arrs, State.writeArr_arrs_self]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · have hne_jk : G.activePairsList[j]'hj' ≠ p := by
            intro heq
            exact (Nat.ne_of_lt hlt) ((List.Nodup.getElem_inj_iff G.nodup_activePairsList).mp heq)
          have hne_idx : (G.activePairsList[j]'hj').1.1 * n + (G.activePairsList[j]'hj').2.1 ≠
              u.1 * n + v.1 := by
            intro hidx
            rcases pair_idx_inj hidx with ⟨h1, h2⟩
            exact hne_jk (Prod.ext h1 h2)
          rw [List.getElem_set_ne hne_idx.symm]
          exact hset_k j hlt hj'
        · exact List.getElem_set_self _
      · simp only [st₆, st₅, st₄, st₃, st₂, st₁, State.setReg_arrs, State.writeArr_arrs_self]
        have hne_k : p ≠ (u', v') := hne_uv k (Nat.lt_succ_self k) hk_len
        have hne_idx : u'.1 * n + v'.1 ≠ u.1 * n + v.1 := by
          intro hidx
          rcases pair_idx_inj hidx.symm with ⟨h1, h2⟩
          exact hne_k (Prod.ext h1 h2)
        rw [List.getElem_set_ne hne_idx.symm]
        exact hzero_k u' v' (fun j hj hj' => hne_uv j (Nat.lt_succ_of_lt hj) hj')
      · have hr54 : r ≠ 54 := by intro h; subst h; revert hr; decide
        have hr55 : r ≠ 55 := by intro h; subst h; revert hr; decide
        have hr56 : r ≠ 56 := by intro h; subst h; revert hr; decide
        have hr57 : r ≠ 57 := by intro h; subst h; revert hr; decide
        have hr58 : r ≠ 58 := by intro h; subst h; revert hr; decide
        have hr59 : r ≠ 59 := by intro h; subst h; revert hr; decide
        simp [st₆, st₅, st₄, st₃, st₂, st₁,
          State.setReg_regs_ne _ _ hr54,
          State.setReg_regs_ne _ _ hr59,
          State.setReg_regs_ne _ _ hr58,
          State.setReg_regs_ne _ _ hr57,
          State.setReg_regs_ne _ _ hr56,
          State.setReg_regs_ne _ _ hr55,
          hreg_k r hr]
  rcases hLoop s₃ hInv₀ with
    ⟨s₄, t₄, hex₄, ht₄, _, _, _, _, ⟨hlen₄, hset₄, hzero₄⟩, harr₄, hreg₄⟩
  dsimp only at ht₄
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by omega,
    ⟨hlen₄, fun u v => ?_⟩, harr₄, hreg₄⟩
  by_cases hpos : 0 < G.edgeMult u v
  · have hmem : (u, v) ∈ G.activePairsList := (G.mem_activePairsList (u, v)).mpr hpos
    rcases List.mem_iff_getElem.mp hmem with ⟨j, hj, heq⟩
    have h := hset₄ j hj hj
    have hj1 : (G.activePairsList[j]'hj).1 = u := congrArg Prod.fst heq
    have hj2 : (G.activePairsList[j]'hj).2 = v := congrArg Prod.snd heq
    simpa [hj1, hj2] using h
  · have hzero_mult : G.edgeMult u v = 0 := by omega
    rw [hzero_mult]
    apply hzero₄ u v
    intro j _ hj' heq
    have hmem : (u, v) ∈ G.activePairsList := heq ▸ List.getElem_mem hj'
    exact hpos ((G.mem_activePairsList (u, v)).mp hmem)

/-- Prefix-matching predicate for `(a_tail, a_head)` against a list `L : List (Fin n × Fin n)`. -/
def MatchesEdgePrefix {n : ℕ} (m : ℕ) (L : List (Fin n × Fin n))
    (a_tail a_head : Arr) (s : State) : Prop :=
  (s.arrs a_tail).length = m ∧
  (s.arrs a_head).length = m ∧
  L.length ≤ m ∧
  s.regs 55 = L.length ∧
  ∀ i (hi : i < L.length),
    (s.arrs a_tail).getD i 0 = (L[i]'hi).1.1 ∧
    (s.arrs a_head).getD i 0 = (L[i]'hi).2.1

/-- Innermost loop body appending `(u, v)` (`r_56 = u.1`, `r_57 = v.1`) at cursor `r_55`. -/
def appendReplicateBody (a_tail a_head : Arr) : Cmd :=
  .seq (.write a_tail (.reg 55) (.reg 56))
    (.seq (.write a_head (.reg 55) (.reg 57))
      (.assign 55 (.op .add (.reg 55) (.const 1))))

/-- Innermost loop appending `mult` (`r_58`) copies of `(u, v)` (`r_56, r_57`) to `(a_tail, a_head)`. -/
def appendReplicateProg (a_tail a_head : Arr) : Cmd :=
  .seq (.assign 60 (.const 0))
    (forUp 60 (.reg 58) (appendReplicateBody a_tail a_head))

theorem appendReplicateProg_exec {w n m : ℕ} (L : List (Fin n × Fin n))
    (u v : Fin n) (mult : ℕ) (a_tail a_head : Arr)
    (hne_th : a_tail ≠ a_head)
    (hw : 1 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hm_w : m < 2 ^ w)
    (hfit : L.length + mult ≤ m)
    {s : State}
    (hmatch : MatchesEdgePrefix m L a_tail a_head s)
    (hr56 : s.regs 56 = u.1)
    (hr57 : s.regs 57 = v.1)
    (hr58 : s.regs 58 = mult) :
    ∃ s' t,
      Exec w (appendReplicateProg a_tail a_head) s s' t ∧
      t ≤ 5 + 17 * mult ∧
      MatchesEdgePrefix m (L ++ List.replicate mult (u, v)) a_tail a_head s' ∧
      (∀ a : Arr, a ≠ a_tail → a ≠ a_head → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 55 → r ≠ 60 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hmult_w : mult < 2 ^ w := by omega
  have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
  have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
  let s₁ := s.setReg 60 0
  have hex₁ : Exec w (.assign 60 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (c : ℕ) (st : State) : Prop :=
    MatchesEdgePrefix m (L ++ List.replicate c (u, v)) a_tail a_head st ∧
    st.regs 56 = u.1 ∧
    st.regs 57 = v.1 ∧
    st.regs 58 = mult ∧
    st.regs 60 = c ∧
    (∀ a : Arr, a ≠ a_tail → a ≠ a_head → st.arrs a = s.arrs a) ∧
    (∀ r : Reg, r ≠ 55 → r ≠ 60 → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₁ := by
    rcases hmatch with ⟨ht, hh, hle, hr55, hget⟩
    refine ⟨⟨by simp [s₁, ht], by simp [s₁, hh], by simp [hle], by simp [s₁, hr55],
        fun i hi => by simpa [s₁] using hget i (by simpa using hi)⟩,
      by simp [s₁, hr56],
      by simp [s₁, hr57],
      by simp [s₁, hr58],
      by simp [s₁],
      fun a ha1 ha2 => by simp [s₁],
      fun r hr1 hr2 => by simp [s₁, State.setReg_regs_ne _ _ hr2]⟩
  have hLoop :
      ⦃Inv 0⦄[w] forUp 60 (.reg 58) (appendReplicateBody a_tail a_head) ⦃Inv mult⦄ ≤
        fun _ => 3 + mult * (7 + 10) := by
    apply Triple.forUp_const Inv mult 10 hw hmult_w
    · intro c _ st ⟨_, _, _, hr58_c, hr60_c, _, _⟩
      exact ⟨hr60_c, by simp [Expr.eval, checkWord, hr58_c, hmult_w]⟩
    · intro c hc st ⟨⟨ht_c, hh_c, hle_c, hr55_c, hget_c⟩, hr56_c, hr57_c, hr58_c, hr60_c, harr_c, hreg_c⟩
      have hpos_lt : L.length + c < m := by omega
      have hpos_w : L.length + c < 2 ^ w := by omega
      have hpos1_w : L.length + c + 1 < 2 ^ w := by omega
      have hr55_val : st.regs 55 = L.length + c := by simpa using hr55_c
      let st₁ := st.writeArr a_tail (L.length + c) u.1
      have hex_wt : Exec w (.write a_tail (.reg 55) (.reg 56)) st st₁ 3 :=
        .write (by simp [Expr.eval, checkWord, hr55_val, hpos_w])
          (by simp [Expr.eval, checkWord, hr56_c, hu_w])
          (by simp [ht_c, hpos_lt])
      let st₂ := st₁.writeArr a_head (L.length + c) v.1
      have hex_wh : Exec w (.write a_head (.reg 55) (.reg 57)) st₁ st₂ 3 :=
        .write (by simp [st₁, Expr.eval, checkWord, hr55_val, hpos_w])
          (by simp [st₁, Expr.eval, checkWord, hr57_c, hv_w])
          (by simp [st₁, hne_th.symm, hh_c, hpos_lt])
      let st₃ := st₂.setReg 55 (L.length + c + 1)
      have hex_inc : Exec w (.assign 55 (.op .add (.reg 55) (.const 1))) st₂ st₃ 4 :=
        .assign (by simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr55_val, hpos_w, hw, hpos1_w])
      refine ⟨st₃, 10, .seq hex_wt (.seq hex_wh hex_inc), le_refl 10,
        ⟨⟨by simp [st₃, st₂, st₁, hne_th, ht_c],
          by simp [st₃, st₂, st₁, hh_c],
          by simp; omega,
          by simp [st₃]; omega,
          fun i hi => ?_⟩,
         by simp [st₃, st₂, st₁, hr56_c],
         by simp [st₃, st₂, st₁, hr57_c],
         by simp [st₃, st₂, st₁, hr58_c],
         by simp [st₃],
         fun a ha1 ha2 => by simp [st₃, st₂, st₁, ha1, ha2, harr_c a ha1 ha2],
         fun r hr1 hr2 => by
           simp [st₃, st₂, st₁, State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2,
             hreg_c r hr1 hr2]⟩,
        by simp [st₃, st₂, st₁, hr60_c]⟩
      have harr_t : st₃.arrs a_tail = (st.arrs a_tail).set (L.length + c) u.1 := by
        simp [st₃, st₂, st₁, hne_th]
      have harr_h : st₃.arrs a_head = (st.arrs a_head).set (L.length + c) v.1 := by
        simp [st₃, st₂, st₁, hne_th.symm]
      simp only [State.setReg_arrs, harr_t, harr_h]
      have hi_lt : i < L.length + (c + 1) := by simpa using hi
      have hi_m : i < m := by omega
      have hgetD_t : ((st.arrs a_tail).set (L.length + c) u.1).getD i 0 =
          ((st.arrs a_tail).set (L.length + c) u.1)[i]'(by simp [ht_c, hi_m]) :=
        (List.getElem_eq_getD (fallback := 0)).symm
      have hgetD_h : ((st.arrs a_head).set (L.length + c) v.1).getD i 0 =
          ((st.arrs a_head).set (L.length + c) v.1)[i]'(by simp [hh_c, hi_m]) :=
        (List.getElem_eq_getD (fallback := 0)).symm
      rw [hgetD_t, hgetD_h]
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < (L.length + c) + 1 by omega) with hlt | rfl
      · have hne_i : L.length + c ≠ i := by omega
        have hgetD_t2 : (st.arrs a_tail)[i]'(by rw [ht_c]; exact hi_m) = (st.arrs a_tail).getD i 0 :=
          List.getElem_eq_getD (fallback := 0)
        have hgetD_h2 : (st.arrs a_head)[i]'(by rw [hh_c]; exact hi_m) = (st.arrs a_head).getD i 0 :=
          List.getElem_eq_getD (fallback := 0)
        rw [List.getElem_set_ne hne_i, List.getElem_set_ne hne_i, hgetD_t2, hgetD_h2]
        have hlt' : i < (L ++ List.replicate c (u, v)).length := by simp; omega
        have hprev := hget_c i hlt'
        have hrep_eq :
            (L ++ List.replicate (c + 1) (u, v))[i]'hi =
              (L ++ List.replicate c (u, v))[i]'hlt' := by
          simp only [List.replicate_succ', ← List.append_assoc, List.getElem_append_left hlt']
        rwa [hrep_eq]
      · rw [List.getElem_set_self _, List.getElem_set_self _]
        have hrep_last :
            (L ++ List.replicate (c + 1) (u, v))[L.length + c]'hi = (u, v) := by
          rw [List.getElem_append_right (by omega)]
          simp
        rw [hrep_last]
        exact ⟨rfl, rfl⟩
  rcases hLoop s₁ hInv₀ with ⟨s₂, t₂, hex₂, ht₂, hmatch₂, _, _, _, _, harr₂, hreg₂⟩
  dsimp only at ht₂
  exact ⟨s₂, _, .seq hex₁ hex₂, by omega, hmatch₂, harr₂, hreg₂⟩

/-- Prefix of row `u` of `G.directedEdgesList` up to column `v_lim`. -/
def directedEdgesRowPrefix {n : ℕ} (G : MultiDigraph n) (u : Fin n) (v_lim : ℕ) :
    List (Fin n × Fin n) :=
  ((List.finRange n).take v_lim).flatMap (fun v => List.replicate (G.edgeMult u v) (u, v))

@[simp]
theorem directedEdgesRowPrefix_zero {n : ℕ} (G : MultiDigraph n) (u : Fin n) :
    directedEdgesRowPrefix G u 0 = [] := rfl

theorem directedEdgesRowPrefix_succ {n : ℕ} (G : MultiDigraph n) (u : Fin n)
    {v : ℕ} (hv : v < n) :
    directedEdgesRowPrefix G u (v + 1) =
      directedEdgesRowPrefix G u v ++ List.replicate (G.edgeMult u ⟨v, hv⟩) (u, ⟨v, hv⟩) := by
  unfold directedEdgesRowPrefix
  have hlen : v < (List.finRange n).length := by simp [hv]
  rw [List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some, List.flatMap_append]
  simp

theorem directedEdgesRowPrefix_full {n : ℕ} (G : MultiDigraph n) (u : Fin n) :
    directedEdgesRowPrefix G u n =
      (List.finRange n).flatMap (fun v => List.replicate (G.edgeMult u v) (u, v)) := by
  unfold directedEdgesRowPrefix
  rw [List.take_of_length_le (by simp)]

/-- Prefix of `G.directedEdgesList` up to row `u_lim`. -/
def directedEdgesPrefix {n : ℕ} (G : MultiDigraph n) (u_lim : ℕ) : List (Fin n × Fin n) :=
  ((List.finRange n).take u_lim).flatMap (fun u =>
    (List.finRange n).flatMap (fun v => List.replicate (G.edgeMult u v) (u, v)))

@[simp]
theorem directedEdgesPrefix_zero {n : ℕ} (G : MultiDigraph n) :
    directedEdgesPrefix G 0 = [] := rfl

theorem directedEdgesPrefix_succ {n : ℕ} (G : MultiDigraph n) {u : ℕ} (hu : u < n) :
    directedEdgesPrefix G (u + 1) =
      directedEdgesPrefix G u ++ directedEdgesRowPrefix G ⟨u, hu⟩ n := by
  unfold directedEdgesPrefix
  have hlen : u < (List.finRange n).length := by simp [hu]
  rw [List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some, List.flatMap_append]
  simp [directedEdgesRowPrefix_full]

theorem directedEdgesPrefix_full {n : ℕ} (G : MultiDigraph n) :
    directedEdgesPrefix G n = G.directedEdgesList := by
  unfold directedEdgesPrefix MultiDigraph.directedEdgesList
  rw [List.take_of_length_le (by simp)]

theorem length_directedEdgesPrefix_add_rowPrefix_le {n : ℕ} (G : MultiDigraph n)
    {u : ℕ} (hu : u < n) (v : ℕ) (_hv : v ≤ n) :
    (directedEdgesPrefix G u ++ directedEdgesRowPrefix G ⟨u, hu⟩ v).length ≤ G.numEdges := by
  rw [← G.length_directedEdgesList, ← directedEdgesPrefix_full G]
  have hsplit_v : List.finRange n = (List.finRange n).take v ++ (List.finRange n).drop v :=
    (List.take_append_drop v (List.finRange n)).symm
  have h1 : directedEdgesRowPrefix G ⟨u, hu⟩ n =
      directedEdgesRowPrefix G ⟨u, hu⟩ v ++
        (((List.finRange n).drop v).flatMap (fun v' => List.replicate (G.edgeMult ⟨u, hu⟩ v') (⟨u, hu⟩, v'))) := by
    rw [directedEdgesRowPrefix_full]
    unfold directedEdgesRowPrefix
    rw [← List.flatMap_append, ← hsplit_v]
  have hsplit_u : List.finRange n = (List.finRange n).take (u + 1) ++ (List.finRange n).drop (u + 1) :=
    (List.take_append_drop (u + 1) (List.finRange n)).symm
  have h2 : directedEdgesPrefix G n =
      directedEdgesPrefix G u ++ directedEdgesRowPrefix G ⟨u, hu⟩ n ++
        (((List.finRange n).drop (u + 1)).flatMap (fun u' =>
          (List.finRange n).flatMap (fun v' => List.replicate (G.edgeMult u' v') (u', v')))) := by
    rw [← directedEdgesPrefix_succ G hu, directedEdgesPrefix_full]
    unfold directedEdgesPrefix MultiDigraph.directedEdgesList
    rw [← List.flatMap_append, ← hsplit_u]
  rw [h2, h1]
  simp only [List.length_append]
  omega

/-- Loop body for column `v` (`r_57`) in row `u` (`r_56`): reads `mult = a_mat[u * n + v]` into `r_58`
and appends `mult` copies of `(u, v)` to `(a_tail, a_head)`. -/
def expandRowBody (a_mat a_tail a_head : Arr) : Cmd :=
  .seq (.assign 59 (.op .add (.op .mul (.reg 56) (.reg 26)) (.reg 57)))
    (.seq (.assign 58 (.read a_mat (.reg 59)))
      (appendReplicateProg a_tail a_head))

/-- Loop over `v = 0 .. n - 1` (`r_57 < r_26`) expanding row `u` (`r_56`) of `a_mat`. -/
def expandRowProg (a_mat a_tail a_head : Arr) : Cmd :=
  .seq (.assign 57 (.const 0))
    (forUp 57 (.reg 26) (expandRowBody a_mat a_tail a_head))

theorem expandRowProg_exec {w n : ℕ} (G : MultiDigraph n) (u : Fin n)
    (a_mat a_tail a_head : Arr)
    (hne_mt : a_mat ≠ a_tail) (hne_mh : a_mat ≠ a_head) (hne_th : a_tail ≠ a_head)
    (hw : 1 < 2 ^ w)
    (hnn_w : n * n < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w)
    {s : State}
    (hmatch : MatchesEdgePrefix G.numEdges (directedEdgesPrefix G u.1) a_tail a_head s)
    (hr26 : s.regs 26 = n)
    (hr56 : s.regs 56 = u.1)
    (hmat : ∃ hlen : (s.arrs a_mat).length = n * n,
      ∀ x y : Fin n,
        (s.arrs a_mat)[x.1 * n + y.1]'(by rw [hlen]; nlinarith [x.2, y.2]) = G.edgeMult x y) :
    ∃ s' t,
      Exec w (expandRowProg a_mat a_tail a_head) s s' t ∧
      t ≤ 5 + 21 * n + 17 * ∑ v : Fin n, G.edgeMult u v ∧
      MatchesEdgePrefix G.numEdges (directedEdgesPrefix G (u.1 + 1)) a_tail a_head s' ∧
      s'.regs 26 = n ∧
      s'.regs 56 = u.1 ∧
      (∃ hlen : (s'.arrs a_mat).length = n * n,
        ∀ x y : Fin n,
          (s'.arrs a_mat)[x.1 * n + y.1]'(by rw [hlen]; nlinarith [x.2, y.2]) = G.edgeMult x y) ∧
      (∀ a : Arr, a ≠ a_tail → a ≠ a_head → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 53 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · omega
    · nlinarith
  let st_v0 := s.setReg 57 0
  have hex_v0 : Exec w (.assign 57 (.const 0)) s st_v0 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let InnerInv (v : ℕ) (stv : State) : Prop :=
    MatchesEdgePrefix G.numEdges (directedEdgesPrefix G u.1 ++ directedEdgesRowPrefix G u v) a_tail a_head stv ∧
    stv.regs 26 = n ∧
    stv.regs 56 = u.1 ∧
    stv.regs 57 = v ∧
    (∃ hlen : (stv.arrs a_mat).length = n * n,
      ∀ x y : Fin n,
        (stv.arrs a_mat)[x.1 * n + y.1]'(by rw [hlen]; nlinarith [x.2, y.2]) = G.edgeMult x y) ∧
    (∀ a : Arr, a ≠ a_tail → a ≠ a_head → stv.arrs a = s.arrs a) ∧
    (∀ r : Reg, r < 53 → stv.regs r = s.regs r)
  have hInner₀ : InnerInv 0 st_v0 := by
    rcases hmatch with ⟨ht, hh, hle, hr55, hget⟩
    refine ⟨⟨by simp [st_v0, ht], by simp [st_v0, hh], by simpa using hle, by simpa [st_v0] using hr55,
        fun i hi => by simpa [st_v0] using hget i (by simpa using hi)⟩,
      by simp [st_v0, hr26],
      by simp [st_v0, hr56],
      by simp [st_v0],
      ⟨by simp [st_v0, hmat.1], fun x y => by simpa [st_v0] using hmat.2 x y⟩,
      fun a ha2 ha3 => by simp [st_v0],
      fun r hr => ?_⟩
    have hr57 : r ≠ 57 := by intro h; subst h; revert hr; decide
    simp [st_v0, State.setReg_regs_ne _ _ hr57]
  let colCost (v : ℕ) : ℕ :=
    14 + 17 * (if hv : v < n then G.edgeMult u ⟨v, hv⟩ else 0)
  have hInnerLoop :
      ⦃InnerInv 0⦄[w] forUp 57 (.reg 26) (expandRowBody a_mat a_tail a_head) ⦃InnerInv n⦄ ≤
        fun _ => 3 + ∑ v ∈ Finset.range n, (7 + colCost v) := by
    apply Triple.forUp_sum InnerInv n colCost hw hn_w
    · intro v _ stv ⟨_, hr26_v, _, hr57_v, _, _, _⟩
      exact ⟨hr57_v, by simp [Expr.eval, checkWord, hr26_v, hn_w]⟩
    · intro v hv stv ⟨hmatch_v, hr26_v, hr56_v, hr57_v, ⟨hlen_mv, hmat_mv⟩, harr_v, hreg_v⟩
      have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
      have hv_w : v < 2 ^ w := by omega
      have hidx_lt : u.1 * n + v < n * n := by nlinarith [u.2, hv]
      have hidx_w : u.1 * n + v < 2 ^ w := by omega
      have hun_w : u.1 * n < 2 ^ w := by omega
      have hmult_w : G.edgeMult u ⟨v, hv⟩ < 2 ^ w :=
        Nat.lt_of_le_of_lt (G.edgeMult_le_numEdges u ⟨v, hv⟩) hm_w
      let stv₁ := stv.setReg 59 (u.1 * n + v)
      have hex_59 : Exec w (.assign 59 (.op .add (.op .mul (.reg 56) (.reg 26)) (.reg 57))) stv stv₁ 6 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr56_v, hr26_v, hr57_v, hu_w, hn_w, hun_w, hv_w, hidx_w])
      let stv₂ := stv₁.setReg 58 (G.edgeMult u ⟨v, hv⟩)
      have hlt_mv : u.1 * n + v < (stv.arrs a_mat).length := by omega
      have hex_58 : Exec w (.assign 58 (.read a_mat (.reg 59))) stv₁ stv₂ 3 :=
        .assign (by
          have hget : (stv.arrs a_mat)[u.1 * n + v]'hlt_mv = G.edgeMult u ⟨v, hv⟩ := hmat_mv u ⟨v, hv⟩
          simp [stv₁, Expr.eval, checkWord, hidx_w, hlt_mv, hget, hmult_w])
      have hfit :
          (directedEdgesPrefix G u.1 ++ directedEdgesRowPrefix G u v).length + G.edgeMult u ⟨v, hv⟩ ≤ G.numEdges := by
        have hle := length_directedEdgesPrefix_add_rowPrefix_le G u.2 (v + 1) (by omega)
        rw [directedEdgesRowPrefix_succ G u hv, ← List.append_assoc, List.length_append,
          List.length_replicate] at hle
        exact hle
      have hmatch_v2 : MatchesEdgePrefix G.numEdges
          (directedEdgesPrefix G u.1 ++ directedEdgesRowPrefix G u v) a_tail a_head stv₂ := by
        rcases hmatch_v with ⟨ht, hh, hle, hr55, hget⟩
        exact ⟨by simp [stv₂, stv₁, ht], by simp [stv₂, stv₁, hh], hle,
          by simp [stv₂, stv₁, hr55], fun i hi => by simpa [stv₂, stv₁] using hget i hi⟩
      rcases appendReplicateProg_exec
          (directedEdgesPrefix G u.1 ++ directedEdgesRowPrefix G u v)
          u ⟨v, hv⟩ (G.edgeMult u ⟨v, hv⟩) a_tail a_head hne_th hw hn_w hm_w hfit hmatch_v2
          (by simp [stv₂, stv₁, hr56_v]) (by simp [stv₂, stv₁, hr57_v]) (by simp [stv₂]) with
        ⟨stv₃, t_rep, hex_rep, ht_rep, hmatch_v3, harr_rep, hreg_rep⟩
      have hmatch_next :
          MatchesEdgePrefix G.numEdges (directedEdgesPrefix G u.1 ++ directedEdgesRowPrefix G u (v + 1))
            a_tail a_head (stv₃.setReg 57 (v + 1)) := by
        rw [directedEdgesRowPrefix_succ G u hv, ← List.append_assoc]
        rcases hmatch_v3 with ⟨ht, hh, hle, hr55, hget⟩
        exact ⟨by simp [ht], by simp [hh], hle, by simp [hr55], fun i hi => by simpa using hget i hi⟩
      have hcol_eq : colCost v = 14 + 17 * G.edgeMult u ⟨v, hv⟩ := by simp [colCost, hv]
      refine ⟨stv₃, 6 + (3 + t_rep), .seq hex_59 (.seq hex_58 hex_rep), by dsimp only; omega,
        ⟨hmatch_next,
         by simp [hreg_rep 26 (by decide) (by decide), stv₂, stv₁, hr26_v],
         by simp [hreg_rep 56 (by decide) (by decide), stv₂, stv₁, hr56_v],
         by simp,
         ⟨by simp [harr_rep a_mat hne_mt hne_mh, stv₂, stv₁, hlen_mv],
          fun x y => by simpa [harr_rep a_mat hne_mt hne_mh, stv₂, stv₁] using hmat_mv x y⟩,
         fun a ha2 ha3 => by simp [harr_rep a ha2 ha3, stv₂, stv₁, harr_v a ha2 ha3],
         fun r hr => ?_⟩,
        by simp [hreg_rep 57 (by decide) (by decide), stv₂, stv₁, hr57_v]⟩
      have hr55 : r ≠ 55 := by intro h; subst h; revert hr; decide
      have hr57 : r ≠ 57 := by intro h; subst h; revert hr; decide
      have hr58 : r ≠ 58 := by intro h; subst h; revert hr; decide
      have hr59 : r ≠ 59 := by intro h; subst h; revert hr; decide
      have hr60 : r ≠ 60 := by intro h; subst h; revert hr; decide
      simp [State.setReg_regs_ne _ _ hr57, hreg_rep r hr55 hr60, stv₂, stv₁,
        State.setReg_regs_ne _ _ hr58, State.setReg_regs_ne _ _ hr59, hreg_v r hr]
  rcases hInnerLoop st_v0 hInner₀ with
    ⟨st_vn, t_vn, hex_vn, ht_vn, hmatch_vn, hr26_vn, hr56_vn, _, hmat_vn, harr_vn, hreg_vn⟩
  dsimp only at ht_vn
  have hsum_col :
      ∑ v ∈ Finset.range n, (7 + colCost v) =
        21 * n + 17 * ∑ v : Fin n, G.edgeMult u v := by
    have hcongr :
        ∑ v ∈ Finset.range n, (7 + colCost v) =
          ∑ v : Fin n, (21 + 17 * G.edgeMult u v) := by
      rw [Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [Finset.mem_range] at hv
      simp [colCost, hv]
      omega
    rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Nat.mul_comm]
  rw [hsum_col] at ht_vn
  have hmatch_u_next :
      MatchesEdgePrefix G.numEdges (directedEdgesPrefix G (u.1 + 1)) a_tail a_head st_vn := by
    rw [directedEdgesPrefix_succ G u.2]
    exact hmatch_vn
  exact ⟨st_vn, 2 + t_vn, .seq hex_v0 hex_vn, by omega,
    hmatch_u_next, hr26_vn, hr56_vn, hmat_vn, harr_vn, hreg_vn⟩

private theorem expandEdgesProg_time_bound (n m m' t₁ t₅ : ℕ)
    (hm' : m' ≤ n * n)
    (ht₁ : t₁ ≤ 45 * (n * n) + 45 * m' + 20)
    (ht₅ : t₅ ≤ 3 + (12 * n + 21 * (n * n) + 17 * m)) :
    t₁ + (1 + m + (1 + m + (2 + (2 + t₅)))) ≤ 135 * (n + m + 1) ^ 2 := by
  have hsq : (n + m + 1) ^ 2 = n * n + m * m + 2 * (n * m) + 2 * n + 2 * m + 1 := by ring
  omega

/-- Complete Word RAM program expanding `s.arrs a_G = G.enc` into `a_tail` and `a_head` of length
`m = G.numEdges` (`r_28`) using scratch matrix `a_mat` (`r_26 = n`, `r_27 = G.numActivePairs`). -/
def expandEdgesProg (a_G a_mat a_tail a_head : Arr) : Cmd :=
  .seq (buildMultMatProg a_G a_mat)
    (.seq (.alloc a_tail (.reg 28))
      (.seq (.alloc a_head (.reg 28))
        (.seq (.assign 55 (.const 0))
          (.seq (.assign 56 (.const 0))
            (forUp 56 (.reg 26) (expandRowProg a_mat a_tail a_head))))))

theorem expandEdgesProg_exec {w n : ℕ} (G : MultiDigraph n)
    (a_G a_mat a_tail a_head : Arr)
    (hne_Gm : a_G ≠ a_mat)
    (hne_mt : a_mat ≠ a_tail) (hne_mh : a_mat ≠ a_head) (hne_th : a_tail ≠ a_head)
    (hw : 3 < 2 ^ w)
    (hnn_w : n * n < 2 ^ w)
    (henc_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w)
    {s : State}
    (hG : s.arrs a_G = G.enc)
    (hr26 : s.regs 26 = n)
    (hr27 : s.regs 27 = G.numActivePairs)
    (hr28 : s.regs 28 = G.numEdges) :
    ∃ s' t,
      Exec w (expandEdgesProg a_G a_mat a_tail a_head) s s' t ∧
      t ≤ 135 * (n + G.numEdges + 1) ^ 2 ∧
      (∃ (ht : (s'.arrs a_tail).length = G.numEdges) (hh : (s'.arrs a_head).length = G.numEdges),
        ∀ e : Fin G.toComputeDigraph.numEdges,
          (s'.arrs a_tail)[e.1]'(by rw [ht, ← G.length_directedEdgesList]; exact e.2) =
            (G.toComputeDigraph.tail e).1 ∧
          (s'.arrs a_head)[e.1]'(by rw [hh, ← G.length_directedEdgesList]; exact e.2) =
            (G.toComputeDigraph.head e).1) ∧
      (∀ a : Arr, a ≠ a_mat → a ≠ a_tail → a ≠ a_head → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 53 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · omega
    · nlinarith
  -- 1. buildMultMatProg
  rcases buildMultMatProg_exec G a_G a_mat hne_Gm hw hnn_w henc_w hm_w hG hr26 hr27 with
    ⟨s₁, t₁, hex₁, ht₁, ⟨hlen_mat, hmat₁⟩, harr₁, hreg₁⟩
  have hr26_1 : s₁.regs 26 = n := (hreg₁ 26 (by decide)).trans hr26
  have hr28_1 : s₁.regs 28 = G.numEdges := (hreg₁ 28 (by decide)).trans hr28
  -- 2. alloc a_tail (.reg 28)
  let s₂ := s₁.setArr a_tail (List.replicate G.numEdges 0)
  have hex₂ : Exec w (.alloc a_tail (.reg 28)) s₁ s₂ (1 + G.numEdges) :=
    .alloc (by simp [Expr.eval, checkWord, hr28_1, hm_w])
  -- 3. alloc a_head (.reg 28)
  let s₃ := s₂.setArr a_head (List.replicate G.numEdges 0)
  have hex₃ : Exec w (.alloc a_head (.reg 28)) s₂ s₃ (1 + G.numEdges) :=
    .alloc (by simp [s₂, Expr.eval, checkWord, hr28_1, hm_w])
  -- 4. r_55 := 0, r_56 := 0
  let s₃' := s₃.setReg 55 0
  let s₄ := s₃'.setReg 56 0
  have hex₄a : Exec w (.assign 55 (.const 0)) s₃ s₃' 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hex₄b : Exec w (.assign 56 (.const 0)) s₃' s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 5. Outer loop over u = 0 .. n - 1
  let OuterInv (u : ℕ) (st : State) : Prop :=
    MatchesEdgePrefix G.numEdges (directedEdgesPrefix G u) a_tail a_head st ∧
    st.regs 26 = n ∧
    st.regs 56 = u ∧
    (∃ hlen : (st.arrs a_mat).length = n * n,
      ∀ x y : Fin n,
        (st.arrs a_mat)[x.1 * n + y.1]'(by rw [hlen]; nlinarith [x.2, y.2]) = G.edgeMult x y) ∧
    (∀ a : Arr, a ≠ a_mat → a ≠ a_tail → a ≠ a_head → st.arrs a = s.arrs a) ∧
    (∀ r : Reg, r < 53 → st.regs r = s.regs r)
  have hOuter₀ : OuterInv 0 s₄ := by
    refine ⟨⟨by simp [s₄, s₃', s₃, s₂, hne_th], by simp [s₄, s₃', s₃], by simp,
        by simp [s₄, s₃'],
        fun i hi => by simp at hi⟩,
      by simp [s₄, s₃', s₃, s₂, hr26_1],
      by simp [s₄],
      ⟨by simp [s₄, s₃', s₃, s₂, hne_mt, hne_mh, hlen_mat],
       fun x y => by simpa [s₄, s₃', s₃, s₂, hne_mt, hne_mh] using hmat₁ x y⟩,
      fun a ha1 ha2 ha3 => by simp [s₄, s₃', s₃, s₂, ha2, ha3, harr₁ a ha1],
      fun r hr => ?_⟩
    have hr56 : r ≠ 56 := by intro h; subst h; revert hr; decide
    have hr55 : r ≠ 55 := by intro h; subst h; revert hr; decide
    simp [s₄, s₃', s₃, s₂, State.setReg_regs_ne _ _ hr56, State.setReg_regs_ne _ _ hr55, hreg₁ r hr]
  let rowCost (u : ℕ) : ℕ :=
    5 + 21 * n + 17 * (if hu : u < n then ∑ v : Fin n, G.edgeMult ⟨u, hu⟩ v else 0)
  have hOuterLoop :
      ⦃OuterInv 0⦄[w] forUp 56 (.reg 26) (expandRowProg a_mat a_tail a_head) ⦃OuterInv n⦄ ≤
        fun _ => 3 + ∑ u ∈ Finset.range n, (7 + rowCost u) := by
    apply Triple.forUp_sum OuterInv n rowCost h1_w hn_w
    · intro u _ st ⟨_, hr26_u, hr56_u, _, _, _⟩
      exact ⟨hr56_u, by simp [Expr.eval, checkWord, hr26_u, hn_w]⟩
    · intro u hu st ⟨hmatch_u, hr26_u, hr56_u, hmat_u, harr_u, hreg_u⟩
      rcases expandRowProg_exec G ⟨u, hu⟩ a_mat a_tail a_head hne_mt hne_mh hne_th h1_w hnn_w hm_w
          hmatch_u hr26_u hr56_u hmat_u with
        ⟨st_vn, t_vn, hex_vn, ht_vn, hmatch_vn, hr26_vn, hr56_vn, hmat_vn, harr_vn, hreg_vn⟩
      have hmatch_u_next :
          MatchesEdgePrefix G.numEdges (directedEdgesPrefix G (u + 1)) a_tail a_head (st_vn.setReg 56 (u + 1)) := by
        rcases hmatch_vn with ⟨ht, hh, hle, hr55, hget⟩
        exact ⟨by simp [ht], by simp [hh], hle, by simp [hr55], fun i hi => by simpa using hget i hi⟩
      have hrow_eq : rowCost u = 5 + 21 * n + 17 * ∑ v : Fin n, G.edgeMult ⟨u, hu⟩ v := by
        simp [rowCost, hu]
      refine ⟨st_vn, t_vn, hex_vn, by dsimp only; omega,
        ⟨hmatch_u_next,
         by simp [hr26_vn],
         by simp,
         ⟨by simp [hmat_vn.1], fun x y => by simpa using hmat_vn.2 x y⟩,
         fun a ha1 ha2 ha3 => by simp [harr_vn a ha2 ha3, harr_u a ha1 ha2 ha3],
         fun r hr => ?_⟩,
        hr56_vn⟩
      have hr56 : r ≠ 56 := by intro h; subst h; revert hr; decide
      simp [State.setReg_regs_ne _ _ hr56, hreg_vn r hr, hreg_u r hr]
  rcases hOuterLoop s₄ hOuter₀ with
    ⟨s₅, t₅, hex₅, ht₅, hmatch₅, _, _, _, harr₅, hreg₅⟩
  dsimp only at ht₅
  have hsum_outer :
      ∑ u ∈ Finset.range n, (7 + rowCost u) =
        12 * n + 21 * (n * n) + 17 * G.numEdges := by
    have hcongr :
        ∑ u ∈ Finset.range n, (7 + rowCost u) =
          ∑ u : Fin n, ((12 + 21 * n) + 17 * ∑ v : Fin n, G.edgeMult u v) := by
      rw [Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.mem_range] at hu
      simp only [rowCost, hu, ↓reduceDIte]
      omega
    rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum]
    change ∑ x : Fin n, (12 + 21 * n) + 17 * G.numEdges = 12 * n + 21 * (n * n) + 17 * G.numEdges
    simp [Nat.mul_comm]
    ring
  rw [hsum_outer] at ht₅
  rw [directedEdgesPrefix_full] at hmatch₅
  rcases hmatch₅ with ⟨ht₅_len, hh₅_len, _, _, hget₅⟩
  refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄a (.seq hex₄b hex₅)))),
    expandEdgesProg_time_bound n G.numEdges G.numActivePairs t₁ t₅ G.numActivePairs_le_sq ht₁ ht₅,
    ⟨ht₅_len, hh₅_len, fun e => ?_⟩, harr₅, hreg₅⟩
  rw [List.getElem_eq_getD (fallback := 0), List.getElem_eq_getD (fallback := 0)]
  exact hget₅ e.1 e.2

/-! ### Section 4: Converting the Branch-Decomposition on the Word RAM (`convertBDProg`) -/

theorem getD_set_of_lt (xs : List ℕ) {i j : ℕ} (v d : ℕ) (hj : j < xs.length) :
    (xs.set i v).getD j d = if i = j then v else xs.getD j d := by
  have hj' : j < (xs.set i v).length := by simp [hj]
  have h1 : (xs.set i v).getD j d = (xs.set i v)[j]'hj' :=
    (List.getElem_eq_getD (fallback := d)).symm
  have h2 : xs.getD j d = xs[j]'hj :=
    (List.getElem_eq_getD (fallback := d)).symm
  rw [h1, h2, List.getElem_set]

theorem getD_replicate_of_lt {n j : ℕ} (v d : ℕ) (hj : j < n) :
    (List.replicate n v).getD j d = v := by
  have hj' : j < (List.replicate n v).length := by simp [hj]
  have h1 : (List.replicate n v).getD j d = (List.replicate n v)[j]'hj' :=
    (List.getElem_eq_getD (fallback := d)).symm
  rw [h1, List.getElem_replicate]

theorem exec_assign_read_getD {w : ℕ} (r : Reg) (a : Arr) (r_idx : Reg)
    {s : State} {idx val : ℕ}
    (hr_idx : s.regs r_idx = idx)
    (hidx_w : idx < 2 ^ w)
    (hidx_len : idx < (s.arrs a).length)
    (hval : (s.arrs a).getD idx 0 = val)
    (hval_w : val < 2 ^ w) :
    Exec w (.assign r (.read a (.reg r_idx))) s (s.setReg r val) 3 := by
  have hget : (s.arrs a)[idx]'hidx_len = val :=
    (List.getElem_eq_getD (fallback := 0)).trans hval
  exact .assign (by simp [Expr.eval, checkWord, hr_idx, hidx_w, hidx_len, hget, hval_w])

theorem exec_write_reg {w : ℕ} (a : Arr) (r_idx r_val : Reg)
    {s : State} {idx val : ℕ}
    (hr_idx : s.regs r_idx = idx)
    (hr_val : s.regs r_val = val)
    (hidx_w : idx < 2 ^ w)
    (hval_w : val < 2 ^ w)
    (hidx_len : idx < (s.arrs a).length) :
    Exec w (.write a (.reg r_idx) (.reg r_val)) s (s.writeArr a idx val) 3 :=
  .write (by simp [Expr.eval, checkWord, hr_idx, hidx_w])
    (by simp [Expr.eval, checkWord, hr_val, hval_w]) hidx_len

theorem exec_write_const {w : ℕ} (a : Arr) (r_idx : Reg) (val : ℕ)
    {s : State} {idx : ℕ}
    (hr_idx : s.regs r_idx = idx)
    (hidx_w : idx < 2 ^ w)
    (hval_w : val < 2 ^ w)
    (hidx_len : idx < (s.arrs a).length) :
    Exec w (.write a (.reg r_idx) (.const val)) s (s.writeArr a idx val) 3 :=
  .write (by simp [Expr.eval, checkWord, hr_idx, hidx_w])
    (by simp [Expr.eval, checkWord, hval_w]) hidx_len

/-- Copy the first `r_len` words of `a_src` into an already-allocated `a_dst` using `r_55` and `r_56`. -/
def copyIntoProg (a_src a_dst : Arr) (r_len : Reg) : Cmd :=
  .seq (.assign 55 (.const 0))
    (forUp 55 (.reg r_len)
      (.seq (.assign 56 (.read a_src (.reg 55)))
        (.write a_dst (.reg 55) (.reg 56))))

theorem copyIntoProg_exec {w k : ℕ} (a_src a_dst : Arr) (r_len : Reg)
    (hne : a_src ≠ a_dst) (hr55 : r_len ≠ 55) (hr56 : r_len ≠ 56)
    (hw : 1 < 2 ^ w) (hk_w : k < 2 ^ w)
    {s : State}
    (hr_len : s.regs r_len = k)
    (hsrc_len : k ≤ (s.arrs a_src).length)
    (hdst_len : k ≤ (s.arrs a_dst).length)
    (hsrc_w : ∀ i < k, (s.arrs a_src).getD i 0 < 2 ^ w) :
    ∃ s' t,
      Exec w (copyIntoProg a_src a_dst r_len) s s' t ∧
      t ≤ 13 * k + 5 ∧
      (s'.arrs a_dst).length = (s.arrs a_dst).length ∧
      (∀ i < k, (s'.arrs a_dst).getD i 0 = (s.arrs a_src).getD i 0) ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 55 → r ≠ 56 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 55 0
  have hex₁ : Exec w (.assign 55 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (c : ℕ) (st : State) : Prop :=
    (st.arrs a_dst).length = (s.arrs a_dst).length ∧
    (∀ i < c, (st.arrs a_dst).getD i 0 = (s.arrs a_src).getD i 0) ∧
    st.regs r_len = k ∧
    st.regs 55 = c ∧
    (∀ a : Arr, a ≠ a_dst → st.arrs a = s.arrs a) ∧
    (∀ r : Reg, r ≠ 55 → r ≠ 56 → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₁ :=
    ⟨by simp [s₁], fun i hi => by omega,
     by simp [s₁, State.setReg_regs_ne _ _ hr55, hr_len],
     by simp [s₁], fun a _ => by simp [s₁],
     fun r hr1 _ => by simp [s₁, State.setReg_regs_ne _ _ hr1]⟩
  have hLoop :
      ⦃Inv 0⦄[w] forUp 55 (.reg r_len)
        (.seq (.assign 56 (.read a_src (.reg 55)))
          (.write a_dst (.reg 55) (.reg 56))) ⦃Inv k⦄ ≤
        fun _ => 3 + k * (7 + 6) := by
    apply Triple.forUp_const Inv k 6 hw hk_w
    · intro c _ st ⟨_, _, hrk, hr55_c, _, _⟩
      exact ⟨hr55_c, by simp [Expr.eval, checkWord, hrk, hk_w]⟩
    · intro c hc st ⟨hlen_c, hget_c, hrk, hr55_c, harr_c, hreg_c⟩
      have hc_w : c < 2 ^ w := by omega
      have hsrc_eq : st.arrs a_src = s.arrs a_src := harr_c a_src hne
      have hc_src : c < (st.arrs a_src).length := by rw [hsrc_eq]; omega
      have hc_dst : c < (st.arrs a_dst).length := by omega
      have hval_w : (st.arrs a_src).getD c 0 < 2 ^ w := by
        rw [hsrc_eq]; exact hsrc_w c hc
      let st₁ := st.setReg 56 ((st.arrs a_src).getD c 0)
      have hex_r : Exec w (.assign 56 (.read a_src (.reg 55))) st st₁ 3 :=
        exec_assign_read_getD 56 a_src 55 hr55_c hc_w hc_src rfl hval_w
      let st₂ := st₁.writeArr a_dst c ((st.arrs a_src).getD c 0)
      have hex_w : Exec w (.write a_dst (.reg 55) (.reg 56)) st₁ st₂ 3 :=
        exec_write_reg a_dst 55 56 (by simp [st₁, hr55_c]) (by simp [st₁]) hc_w hval_w
          (by simp [st₁, hc_dst])
      refine ⟨st₂, 6, .seq hex_r hex_w, le_refl 6,
        ⟨by simp [st₂, st₁, hlen_c],
         fun i hi => ?_,
         by simp [st₂, st₁, State.setReg_regs_ne _ _ hr55, State.setReg_regs_ne _ _ hr56, hrk],
         by simp [st₂, st₁],
         fun a ha => by simp [st₂, st₁, ha, harr_c a ha],
         fun r hr1 hr2 => by
           simp [st₂, st₁, State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2,
             hreg_c r hr1 hr2]⟩,
        by simp [st₂, st₁, hr55_c]⟩
      have harr_d : (st₂.setReg 55 (c + 1)).arrs a_dst =
          (st.arrs a_dst).set c ((s.arrs a_src).getD c 0) := by
        simp [st₂, st₁, hsrc_eq]
      rw [harr_d, getD_set_of_lt _ _ _ (by omega)]
      split_ifs with heq
      · subst heq; rfl
      · exact hget_c i (by omega)
  rcases hLoop s₁ hInv₀ with ⟨s₂, t₂, hex₂, ht₂, hlen₂, hget₂, _, _, harr₂, hreg₂⟩
  dsimp only at ht₂
  exact ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hlen₂, hget₂, harr₂, hreg₂⟩

/-- Allocate `a_dst` of length `r_len` and copy the first `r_len` words of `a_src` into `a_dst`. -/
def copyPrefixProg (a_src a_dst : Arr) (r_len : Reg) : Cmd :=
  .seq (.alloc a_dst (.reg r_len))
    (copyIntoProg a_src a_dst r_len)

theorem copyPrefixProg_exec {w k : ℕ} (a_src a_dst : Arr) (r_len : Reg)
    (hne : a_src ≠ a_dst) (hr55 : r_len ≠ 55) (hr56 : r_len ≠ 56)
    (hw : 1 < 2 ^ w) (hk_w : k < 2 ^ w)
    {s : State}
    (hr_len : s.regs r_len = k)
    (hsrc_len : k ≤ (s.arrs a_src).length)
    (hsrc_w : ∀ i < k, (s.arrs a_src).getD i 0 < 2 ^ w) :
    ∃ s' t,
      Exec w (copyPrefixProg a_src a_dst r_len) s s' t ∧
      t ≤ 14 * k + 6 ∧
      (s'.arrs a_dst).length = k ∧
      (∀ i < k, (s'.arrs a_dst).getD i 0 = (s.arrs a_src).getD i 0) ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 55 → r ≠ 56 → s'.regs r = s.regs r) := by
  let s₁ := s.setArr a_dst (List.replicate k 0)
  have hex₁ : Exec w (.alloc a_dst (.reg r_len)) s s₁ (1 + k) :=
    .alloc (by simp [Expr.eval, checkWord, hr_len, hk_w])
  have hsrc₁ : s₁.arrs a_src = s.arrs a_src := by simp [s₁, hne]
  have hr_len₁ : s₁.regs r_len = k := hr_len
  have hdst_len₁ : k ≤ (s₁.arrs a_dst).length := by simp [s₁]
  rcases copyIntoProg_exec a_src a_dst r_len hne hr55 hr56 hw hk_w (s := s₁)
      hr_len₁
      (by rw [hsrc₁]; exact hsrc_len)
      hdst_len₁
      (fun i hi => by rw [hsrc₁]; exact hsrc_w i hi) with
    ⟨s₂, t₂, hex₂, ht₂, hlen₂, hget₂, harr₂, hreg₂⟩
  rw [hsrc₁] at hget₂
  refine ⟨s₂, (1 + k) + t₂, .seq hex₁ hex₂, by omega,
    by simpa [s₁] using hlen₂, hget₂,
    fun a ha => by simp [harr₂ a ha, s₁, ha],
    fun r hr1 hr2 => by simpa [s₁] using hreg₂ r hr1 hr2⟩

/-- Invariant asserting that `a_tail = b + 5` and `a_head = b + 6` hold the tails and heads of
all edges of `G.toComputeDigraph`. -/
def EdgesExpandedInv {n : ℕ} (G : MultiDigraph n) (b : Arr) (s : State) : Prop :=
  (s.arrs (b + 5)).length = G.numEdges ∧
  (s.arrs (b + 6)).length = G.numEdges ∧
  ∀ e : Fin G.toComputeDigraph.numEdges,
    (s.arrs (b + 5)).getD e.1 0 = (G.toComputeDigraph.tail e).1 ∧
    (s.arrs (b + 6)).getD e.1 0 = (G.toComputeDigraph.head e).1

/-- Invariant asserting that `arr` (`b + 7`) has length `G.numEdges` and stores `1` at `e.1` if and
only if `e ∈ S` (and `0` otherwise). -/
def InTreeInv {n : ℕ} (G : MultiDigraph n)
    (S : Finset (Fin G.toComputeDigraph.numEdges)) (arr : List ℕ) : Prop :=
  arr.length = G.numEdges ∧
  ∀ e : Fin G.toComputeDigraph.numEdges,
    arr.getD e.1 0 = if e ∈ S then 1 else 0

theorem inTreeInv_empty {n : ℕ} (G : MultiDigraph n) :
    InTreeInv G ∅ (List.replicate G.numEdges 0) := by
  refine ⟨by simp, fun e => ?_⟩
  have he_lt : e.1 < G.numEdges := by rw [← G.length_directedEdgesList]; exact e.2
  rw [getD_replicate_of_lt 0 0 he_lt]
  simp

private theorem arr_add_ne (b : Arr) {i j : ℕ} (h : i ≠ j) : (b + i : Arr) ≠ b + j :=
  fun heq => h (Nat.add_left_cancel heq)

@[simp]
private theorem arr_add_eq_add_iff (b : Arr) (i j : ℕ) :
    (b + i : Arr) = b + j ↔ i = j :=
  Nat.add_left_cancel_iff

private theorem arr_ne_add_right (b : Arr) {k : ℕ} (hk : k ≠ 0) : (b : Arr) ≠ b + k := by
  intro h
  have h' : (b : ℕ) + 0 = (b : ℕ) + k := by simpa using h
  exact hk (Nat.add_left_cancel h').symm

private theorem arr_ne_add_of_lt {a b : Arr} (ha : a < b + 2) (k : ℕ) (hk : 2 ≤ k) :
    a ≠ b + k :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (Nat.add_le_add_left hk b))

private theorem reg_lt_53_of_lt_52 {r : Reg} (hr : r < 52) : r < 53 :=
  Nat.lt_trans hr (by decide)

private theorem reg_ne_of_lt_52 {r : Reg} (hr : r < 52) (k : Reg) (hk : 52 ≤ k) : r ≠ k :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le hr hk)

/-- Invariant asserting that `arr` (`b + 8`) has length `n` and for each vertex `u : Fin n`,
either `arr[u] = 0` and no edge in `S` is incident with `u`, or `arr[u] = e.1 + 1` for some edge
`e ∈ S` incident with `u`. -/
def VertEdgeInv {n : ℕ} (G : MultiDigraph n)
    (S : Finset (Fin G.toComputeDigraph.numEdges)) (arr : List ℕ) : Prop :=
  arr.length = n ∧
  ∀ u : Fin n,
    (arr.getD u.1 0 = 0 ∧ ∀ e ∈ S, ¬digraphIncident G.toComputeDigraph u e) ∨
    (∃ e ∈ S, arr.getD u.1 0 = e.1 + 1 ∧ digraphIncident G.toComputeDigraph u e)

theorem vertEdgeInv_empty {n : ℕ} (G : MultiDigraph n) :
    VertEdgeInv G ∅ (List.replicate n 0) := by
  refine ⟨by simp, fun u => ?_⟩
  left
  rw [getD_replicate_of_lt 0 0 u.2]
  exact ⟨rfl, fun _ h => by simp at h⟩

theorem vertEdgeInv_insert {n : ℕ} (G : MultiDigraph n)
    {S : Finset (Fin G.toComputeDigraph.numEdges)} {arr : List ℕ}
    (hinv : VertEdgeInv G S arr) (e : Fin G.toComputeDigraph.numEdges) :
    VertEdgeInv G (insert e S)
      ((arr.set (G.toComputeDigraph.tail e).1 (e.1 + 1)).set
        (G.toComputeDigraph.head e).1 (e.1 + 1)) := by
  rcases hinv with ⟨hlen, hvert⟩
  refine ⟨by simp [hlen], fun u => ?_⟩
  have hu_len1 : u.1 < (arr.set (G.toComputeDigraph.tail e).1 (e.1 + 1)).length := by
    simp [hlen, u.2]
  rw [getD_set_of_lt _ _ _ hu_len1, getD_set_of_lt _ _ _ (by rw [hlen]; exact u.2)]
  split_ifs with hh ht
  · right
    exact ⟨e, Finset.mem_insert_self e S, rfl, Or.inl (Fin.ext hh)⟩
  · right
    exact ⟨e, Finset.mem_insert_self e S, rfl, Or.inr (Fin.ext ht)⟩
  · have hnot_inc_e : ¬digraphIncident G.toComputeDigraph u e := by
      rintro (h1 | h2)
      · exact hh (congrArg Fin.val h1)
      · exact ht (congrArg Fin.val h2)
    rcases hvert u with ⟨hc0, hnone⟩ | ⟨e', he'S, hc_eq, hinc⟩
    · left
      refine ⟨hc0, fun e' he' => ?_⟩
      rcases Finset.mem_insert.mp he' with rfl | he'S
      · exact hnot_inc_e
      · exact hnone e' he'S
    · right
      exact ⟨e', Finset.mem_insert_of_mem he'S, hc_eq, hinc⟩

theorem vertEdgeInv_lookup {n : ℕ} (G : MultiDigraph n)
    {S : Finset (Fin G.toComputeDigraph.numEdges)} {arr : List ℕ}
    (hinv : VertEdgeInv G S arr)
    {e_base : Fin G.toComputeDigraph.numEdges} (hbase : e_base ∈ S)
    (w : Fin n) :
    let c := arr.getD w.1 0
    let e_ref_val := if 0 < c then c - 1 else e_base.1
    ∃ href_lt : e_ref_val < G.toComputeDigraph.numEdges,
      let e_ref : Fin G.toComputeDigraph.numEdges := ⟨e_ref_val, href_lt⟩
      e_ref ∈ S ∧
      ((∃ e' ∈ S, digraphIncident G.toComputeDigraph w e') →
        digraphIncident G.toComputeDigraph w e_ref) := by
  intro c e_ref_val
  rcases hinv.2 w with ⟨hc0, hnone⟩ | ⟨e, heS, hc_eq, hinc⟩
  · have href_eq : e_ref_val = e_base.1 := by
      dsimp only [e_ref_val]; split_ifs with h <;> (dsimp only [c] at h; omega)
    have href_lt : e_ref_val < G.toComputeDigraph.numEdges := by rw [href_eq]; exact e_base.2
    refine ⟨href_lt, ?_, ?_⟩
    · have : (⟨e_ref_val, href_lt⟩ : Fin G.toComputeDigraph.numEdges) = e_base := Fin.ext href_eq
      rwa [this]
    · rintro ⟨e', he'S, hinc'⟩
      exfalso
      exact hnone e' he'S hinc'
  · have href_eq : e_ref_val = e.1 := by
      dsimp only [e_ref_val]; split_ifs with h <;> (dsimp only [c] at h ⊢; omega)
    have href_lt : e_ref_val < G.toComputeDigraph.numEdges := by rw [href_eq]; exact e.2
    refine ⟨href_lt, ?_, fun _ => ?_⟩
    · have : (⟨e_ref_val, href_lt⟩ : Fin G.toComputeDigraph.numEdges) = e := Fin.ext href_eq
      rwa [this]
    · have : (⟨e_ref_val, href_lt⟩ : Fin G.toComputeDigraph.numEdges) = e := Fin.ext href_eq
      rwa [this]

/-- Program marking edge `r_e` as present in `S`: sets `(b + 7)[r_e] := 1` and updates
`(b + 8)[tail e] := r_e + 1` and `(b + 8)[head e] := r_e + 1`. -/
def markEdgeInTreeProg (b : Arr) (r_e : Reg) : Cmd :=
  .seq (.write (b + 7) (.reg r_e) (.const 1))
    (.seq (.assign 56 (.read (b + 5) (.reg r_e)))
      (.seq (.assign 57 (.read (b + 6) (.reg r_e)))
        (.seq (.assign 59 (.op .add (.reg r_e) (.const 1)))
          (.seq (.write (b + 8) (.reg 56) (.reg 59))
            (.write (b + 8) (.reg 57) (.reg 59))))))

theorem markEdgeInTreeProg_exec {w n : ℕ} (G : MultiDigraph n) (b : Arr) (r_e : Reg)
    (hr56 : r_e ≠ 56) (hr57 : r_e ≠ 57) (_hr59 : r_e ≠ 59)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hm1_w : G.numEdges + 1 < 2 ^ w)
    {S : Finset (Fin G.toComputeDigraph.numEdges)}
    (e : Fin G.toComputeDigraph.numEdges)
    {s : State}
    (hr_e : s.regs r_e = e.1)
    (hedges : EdgesExpandedInv G b s)
    (hintree : InTreeInv G S (s.arrs (b + 7)))
    (hvert : VertEdgeInv G S (s.arrs (b + 8))) :
    ∃ s' t,
      Exec w (markEdgeInTreeProg b r_e) s s' t ∧
      t ≤ 19 ∧
      InTreeInv G (insert e S) (s'.arrs (b + 7)) ∧
      VertEdgeInv G (insert e S) (s'.arrs (b + 8)) ∧
      (∀ a : Arr, a ≠ b + 7 → a ≠ b + 8 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 56 → r ≠ 57 → r ≠ 59 → s'.regs r = s.regs r) := by
  have he_m : e.1 < G.numEdges := by rw [← G.length_directedEdgesList]; exact e.2
  have he_w : e.1 < 2 ^ w := by omega
  have he1_w : e.1 + 1 < 2 ^ w := by omega
  let u := G.toComputeDigraph.tail e
  let v := G.toComputeDigraph.head e
  have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
  have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
  rcases hedges with ⟨hlen_t, hlen_h, hget_th⟩
  have htu : (s.arrs (b + 5)).getD e.1 0 = u.1 := (hget_th e).1
  have hhv : (s.arrs (b + 6)).getD e.1 0 = v.1 := (hget_th e).2
  -- 1. write (b + 7) (.reg r_e) (.const 1)
  let s₁ := s.writeArr (b + 7) e.1 1
  have hex₁ : Exec w (.write (b + 7) (.reg r_e) (.const 1)) s s₁ 3 :=
    exec_write_const (b + 7) r_e 1 hr_e he_w hw (by rw [hintree.1]; exact he_m)
  -- 2. assign 56 (.read (b + 5) (.reg r_e))
  let s₂ := s₁.setReg 56 u.1
  have hex₂ : Exec w (.assign 56 (.read (b + 5) (.reg r_e))) s₁ s₂ 3 :=
    exec_assign_read_getD (w := w) 56 (b + 5) r_e (s := s₁)
      (by simp [s₁, hr_e]) he_w (by simp [s₁, hlen_t, he_m]) (by simp [s₁]; exact htu) hu_w
  -- 3. assign 57 (.read (b + 6) (.reg r_e))
  let s₃ := s₂.setReg 57 v.1
  have hex₃ : Exec w (.assign 57 (.read (b + 6) (.reg r_e))) s₂ s₃ 3 :=
    exec_assign_read_getD (w := w) 57 (b + 6) r_e (s := s₂)
      (by simp [s₂, s₁, State.setReg_regs_ne _ _ hr56, hr_e]) he_w
      (by simp [s₂, s₁, hlen_h, he_m]) (by simp [s₂, s₁]; exact hhv) hv_w
  -- 4. assign 59 (.op .add (.reg r_e) (.const 1))
  let s₄ := s₃.setReg 59 (e.1 + 1)
  have hex₄ : Exec w (.assign 59 (.op .add (.reg r_e) (.const 1))) s₃ s₄ 4 :=
    .assign (by simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hr57, State.setReg_regs_ne _ _ hr56,
      Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_e, he_w, hw, he1_w])
  -- 5. write (b + 8) (.reg 56) (.reg 59)
  let s₅ := s₄.writeArr (b + 8) u.1 (e.1 + 1)
  have hex₅ : Exec w (.write (b + 8) (.reg 56) (.reg 59)) s₄ s₅ 3 :=
    exec_write_reg (b + 8) 56 59 (by simp [s₄, s₃, s₂]) (by simp [s₄]) hu_w he1_w
      (by simp [s₄, s₃, s₂, s₁, hvert.1, u.2])
  -- 6. write (b + 8) (.reg 57) (.reg 59)
  let s₆ := s₅.writeArr (b + 8) v.1 (e.1 + 1)
  have hex₆ : Exec w (.write (b + 8) (.reg 57) (.reg 59)) s₅ s₆ 3 :=
    exec_write_reg (b + 8) 57 59 (by simp [s₅, s₄, s₃]) (by simp [s₅, s₄]) hv_w he1_w
      (by simp [s₅, s₄, s₃, s₂, s₁, hvert.1, v.2])
  have hintree' : InTreeInv G (insert e S) (s₆.arrs (b + 7)) := by
    have harr7 : s₆.arrs (b + 7) = (s.arrs (b + 7)).set e.1 1 := by
      simp [s₆, s₅, s₄, s₃, s₂, s₁]
    rw [harr7]
    refine ⟨by simp [hintree.1], fun e' => ?_⟩
    have he'_m : e'.1 < G.numEdges := by rw [← G.length_directedEdgesList]; exact e'.2
    rw [getD_set_of_lt _ _ _ (by rw [hintree.1]; exact he'_m), hintree.2 e']
    by_cases h : e.1 = e'.1
    · have heq : e' = e := Fin.ext h.symm
      subst heq
      simp
    · have hne : e' ≠ e := fun heq => h (congrArg Fin.val heq.symm)
      simp [h, hne]
  have hvert' : VertEdgeInv G (insert e S) (s₆.arrs (b + 8)) := by
    have harr8 : s₆.arrs (b + 8) = ((s.arrs (b + 8)).set u.1 (e.1 + 1)).set v.1 (e.1 + 1) := by
      simp [s₆, s₅, s₄, s₃, s₂, s₁]
    rw [harr8]
    exact vertEdgeInv_insert G hvert e
  refine ⟨s₆, 19, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), le_refl 19,
    hintree', hvert',
    fun a ha7 ha8 => by simp [s₆, s₅, s₄, s₃, s₂, s₁, ha7, ha8],
    fun r hr1 hr2 hr3 => by
      simp [s₆, s₅, s₄, s₃, s₂, s₁,
        State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2, State.setReg_regs_ne _ _ hr3]⟩

/-- Invariant asserting that `arr_par` (`b + 9`) has length `2 * G.numEdges + 1` and agrees with
`p` on `0 .. t - 1`, and `arr_tau` (`b + 10`) has length `G.numEdges` and agrees with `τ` on `S`. -/
def ParTauInv {n : ℕ} (G : MultiDigraph n)
    (S : Finset (Fin G.toComputeDigraph.numEdges)) (t : ℕ) (p : ℕ → ℕ)
    (τ : Fin G.toComputeDigraph.numEdges → Fin t)
    (arr_par arr_tau : List ℕ) : Prop :=
  arr_par.length = 2 * G.numEdges + 1 ∧
  arr_tau.length = G.numEdges ∧
  (∀ z < t, arr_par.getD z 0 = p z) ∧
  (∀ e ∈ S, arr_tau.getD e.1 0 = (τ e).1)

/-- Program updating `a_par_work` (`b + 9`), `a_tau_work` (`b + 10`), and `r_52` (`t ↦ t + 2`)
when splitting leaf `τ e_ref` (`e_ref` in `r_62`) for new edge `e_new` (`e_new` in `r_55`). -/
def splitLeafWorkProg (b : Arr) : Cmd :=
  .seq (.assign 63 (.read (b + 10) (.reg 62)))
    (.seq (.write (b + 9) (.reg 52) (.reg 63))
      (.seq (.assign 59 (.op .add (.reg 52) (.const 1)))
        (.seq (.write (b + 9) (.reg 59) (.reg 63))
          (.seq (.write (b + 10) (.reg 55) (.reg 52))
            (.seq (.write (b + 10) (.reg 62) (.reg 59))
              (.assign 52 (.op .add (.reg 52) (.const 2))))))))

theorem splitLeafWorkProg_exec {w n t : ℕ} (G : MultiDigraph n) (b : Arr)
    (hw : 2 < 2 ^ w) (hm_w : 2 * G.numEdges + 1 < 2 ^ w)
    {S : Finset (Fin G.toComputeDigraph.numEdges)}
    {p : ℕ → ℕ} {τ : Fin G.toComputeDigraph.numEdges → Fin t}
    (ht_bound : t + 2 ≤ 2 * G.numEdges + 1)
    {e_new e_ref : Fin G.toComputeDigraph.numEdges}
    (he_new : e_new ∉ S) (he_ref : e_ref ∈ S)
    {s : State}
    (hr52 : s.regs 52 = t)
    (hr55 : s.regs 55 = e_new.1)
    (hr62 : s.regs 62 = e_ref.1)
    (hpt : ParTauInv G S t p τ (s.arrs (b + 9)) (s.arrs (b + 10))) :
    let p' := splitLeafParent p t (τ e_ref).1
    let τ' : Fin G.toComputeDigraph.numEdges → Fin (t + 2) := fun e =>
      if e = e_new then ⟨t, by omega⟩
      else if e = e_ref then ⟨t + 1, by omega⟩
      else ⟨(τ e).1, Nat.lt_trans (τ e).2 (by omega)⟩
    ∃ s' time,
      Exec w (splitLeafWorkProg b) s s' time ∧
      time ≤ 23 ∧
      s'.regs 52 = t + 2 ∧
      ParTauInv G (insert e_new S) (t + 2) p' τ' (s'.arrs (b + 9)) (s'.arrs (b + 10)) ∧
      (∀ a : Arr, a ≠ b + 9 → a ≠ b + 10 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 52 → r ≠ 59 → r ≠ 63 → s'.regs r = s.regs r) := by
  intro p' τ'
  rcases hpt with ⟨hlen_par, hlen_tau, hpar_get, htau_get⟩
  have h1_w : 1 < 2 ^ w := by omega
  have he_new_m : e_new.1 < G.numEdges := by rw [← G.length_directedEdgesList]; exact e_new.2
  have he_ref_m : e_ref.1 < G.numEdges := by rw [← G.length_directedEdgesList]; exact e_ref.2
  have he_new_w : e_new.1 < 2 ^ w := by omega
  have he_ref_w : e_ref.1 < 2 ^ w := by omega
  have ht_w : t < 2 ^ w := by omega
  have ht1_w : t + 1 < 2 ^ w := by omega
  have ht2_w : t + 2 < 2 ^ w := by omega
  let v := (τ e_ref).1
  have hv_t : v < t := (τ e_ref).2
  have hv_w : v < 2 ^ w := by omega
  have htau_ref : (s.arrs (b + 10)).getD e_ref.1 0 = v := htau_get e_ref he_ref
  have hne_edges : e_new ≠ e_ref := fun h => he_new (h ▸ he_ref)
  have hne_val : e_new.1 ≠ e_ref.1 := fun h => hne_edges (Fin.ext h)
  -- 1. assign 63 (.read (b + 10) (.reg 62))
  let s₁ := s.setReg 63 v
  have hex₁ : Exec w (.assign 63 (.read (b + 10) (.reg 62))) s s₁ 3 :=
    exec_assign_read_getD (w := w) 63 (b + 10) 62 (s := s)
      hr62 he_ref_w (by rw [hlen_tau]; exact he_ref_m) htau_ref hv_w
  -- 2. write (b + 9) (.reg 52) (.reg 63)
  let s₂ := s₁.writeArr (b + 9) t v
  have hex₂ : Exec w (.write (b + 9) (.reg 52) (.reg 63)) s₁ s₂ 3 :=
    exec_write_reg (b + 9) 52 63 (by simp [s₁, hr52]) (by simp [s₁]) ht_w hv_w
      (by simp [s₁, hlen_par]; omega)
  -- 3. assign 59 (.op .add (.reg 52) (.const 1))
  let s₃ := s₂.setReg 59 (t + 1)
  have hex₃ : Exec w (.assign 59 (.op .add (.reg 52) (.const 1))) s₂ s₃ 4 :=
    .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr52, ht_w, h1_w, ht1_w])
  -- 4. write (b + 9) (.reg 59) (.reg 63)
  let s₄ := s₃.writeArr (b + 9) (t + 1) v
  have hex₄ : Exec w (.write (b + 9) (.reg 59) (.reg 63)) s₃ s₄ 3 :=
    exec_write_reg (b + 9) 59 63 (by simp [s₃]) (by simp [s₃, s₂, s₁]) ht1_w hv_w
      (by simp [s₃, s₂, s₁, hlen_par]; omega)
  -- 5. write (b + 10) (.reg 55) (.reg 52)
  let s₅ := s₄.writeArr (b + 10) e_new.1 t
  have hex₅ : Exec w (.write (b + 10) (.reg 55) (.reg 52)) s₄ s₅ 3 :=
    exec_write_reg (b + 10) 55 52 (by simp [s₄, s₃, s₂, s₁, hr55]) (by simp [s₄, s₃, s₂, s₁, hr52])
      he_new_w ht_w (by simp [s₄, s₃, s₂, s₁, hlen_tau, he_new_m])
  -- 6. write (b + 10) (.reg 62) (.reg 59)
  let s₆ := s₅.writeArr (b + 10) e_ref.1 (t + 1)
  have hex₆ : Exec w (.write (b + 10) (.reg 62) (.reg 59)) s₅ s₆ 3 :=
    exec_write_reg (b + 10) 62 59 (by simp [s₅, s₄, s₃, s₂, s₁, hr62]) (by simp [s₅, s₄, s₃])
      he_ref_w ht1_w (by simp [s₅, s₄, s₃, s₂, s₁, hlen_tau, he_ref_m])
  -- 7. assign 52 (.op .add (.reg 52) (.const 2))
  let s₇ := s₆.setReg 52 (t + 2)
  have hex₇ : Exec w (.assign 52 (.op .add (.reg 52) (.const 2))) s₆ s₇ 4 :=
    .assign (by simp [s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr52, ht_w, hw, ht2_w])
  have harr_par7 : s₇.arrs (b + 9) = ((s.arrs (b + 9)).set t v).set (t + 1) v := by
    simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]
  have harr_tau7 : s₇.arrs (b + 10) = ((s.arrs (b + 10)).set e_new.1 t).set e_ref.1 (t + 1) := by
    simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]
  refine ⟨s₇, 23, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    le_refl 23, by simp [s₇], ⟨?_, ?_, ?_, ?_⟩,
    fun a ha9 ha10 => by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha9, ha10],
    fun r hr1 hr2 hr3 => by
      simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁,
        State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2, State.setReg_regs_ne _ _ hr3]⟩
  · rw [harr_par7]; simp [hlen_par]
  · rw [harr_tau7]; simp [hlen_tau]
  · intro z hz
    rw [harr_par7, getD_set_of_lt _ _ _ (by simp [hlen_par]; omega),
        getD_set_of_lt _ _ _ (by rw [hlen_par]; omega)]
    unfold p' splitLeafParent
    split_ifs with h1 h2 h3
    · rfl
    · exfalso; omega
    · rfl
    · exfalso; omega
    · exfalso; omega
    · exact hpar_get z (by omega)
  · intro e he
    have he_m : e.1 < G.numEdges := by rw [← G.length_directedEdgesList]; exact e.2
    rw [harr_tau7, getD_set_of_lt _ _ _ (by simp [hlen_tau, he_m]),
        getD_set_of_lt _ _ _ (by rw [hlen_tau]; exact he_m)]
    by_cases h_ref : e = e_ref
    · subst h_ref
      simp [τ', hne_edges.symm]
    · have hne_ref_val : e_ref.1 ≠ e.1 := fun h => h_ref (Fin.ext h.symm)
      by_cases h_new : e = e_new
      · subst h_new
        simp [τ', hne_val.symm]
      · have hne_new_val : e_new.1 ≠ e.1 := fun h => h_new (Fin.ext h.symm)
        have heS : e ∈ S := (Finset.mem_insert.mp he).resolve_left h_new
        simp only [τ', h_new, h_ref, hne_ref_val, hne_new_val, ↓reduceIte]
        exact htau_get e heS

theorem getD_bitSetList {n : ℕ} (Z : Finset (Fin n)) (u : Fin n) :
    (bitSetList Z).getD u.1 0 = if u ∈ Z then 1 else 0 := by
  have h1 : (bitSetList Z).getD u.1 0 =
      (bitSetList Z)[u.1]'(by rw [length_bitSetList]; exact u.2) :=
    (List.getElem_eq_getD (fallback := 0)).symm
  rw [h1, getElem_bitSetList Z u.1 u.2]

/-- Subset of `edgesOutsideZ D Z` with edge index `< k`. -/
def edgesOutsideZUpTo (D : ComputeDigraph) (Z : Finset (Fin D.numVerts)) (k : ℕ) :
    Finset (Fin D.numEdges) :=
  (edgesOutsideZ D Z).filter (fun e => e.1 < k)

@[simp]
theorem mem_edgesOutsideZUpTo (D : ComputeDigraph) (Z : Finset (Fin D.numVerts)) (k : ℕ)
    (e : Fin D.numEdges) :
    e ∈ edgesOutsideZUpTo D Z k ↔ e ∈ edgesOutsideZ D Z ∧ e.1 < k := by
  unfold edgesOutsideZUpTo
  exact Finset.mem_filter

@[simp]
theorem edgesOutsideZUpTo_zero (D : ComputeDigraph) (Z : Finset (Fin D.numVerts)) :
    edgesOutsideZUpTo D Z 0 = ∅ := by
  ext e
  rw [mem_edgesOutsideZUpTo]
  simp

theorem edgesOutsideZUpTo_full {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    edgesOutsideZUpTo G.toComputeDigraph Z G.numEdges = edgesOutsideZ G.toComputeDigraph Z := by
  ext e
  rw [mem_edgesOutsideZUpTo]
  have he_m : e.1 < G.numEdges := by rw [← G.length_directedEdgesList]; exact e.2
  exact and_iff_left he_m

theorem edgesOutsideZUpTo_succ_of_mem (D : ComputeDigraph) (Z : Finset (Fin D.numVerts))
    {e : Fin D.numEdges} (he : e ∈ edgesOutsideZ D Z) :
    edgesOutsideZUpTo D Z (e.1 + 1) = insert e (edgesOutsideZUpTo D Z e.1) := by
  ext e'
  rw [mem_edgesOutsideZUpTo, Finset.mem_insert, mem_edgesOutsideZUpTo]
  constructor
  · rintro ⟨he', hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
    · exact Or.inr ⟨he', hlt'⟩
    · exact Or.inl (Fin.ext heq)
  · rintro (rfl | ⟨he', hlt'⟩)
    · exact ⟨he, Nat.lt_succ_self _⟩
    · exact ⟨he', Nat.lt_succ_of_lt hlt'⟩

theorem edgesOutsideZUpTo_succ_of_notMem (D : ComputeDigraph) (Z : Finset (Fin D.numVerts))
    {e : Fin D.numEdges} (he : e ∉ edgesOutsideZ D Z) :
    edgesOutsideZUpTo D Z (e.1 + 1) = edgesOutsideZUpTo D Z e.1 := by
  ext e'
  rw [mem_edgesOutsideZUpTo, mem_edgesOutsideZUpTo]
  constructor
  · rintro ⟨he', hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
    · exact ⟨he', hlt'⟩
    · exfalso; exact he (Fin.ext heq ▸ he')
  · rintro ⟨he', hlt'⟩
    exact ⟨he', Nat.lt_succ_of_lt hlt'⟩

/-- Program reading `u = a_tail[r_55]`, `v = a_head[r_55]`, and setting `r_58 = Z[u] + Z[v]`. -/
def checkEdgeOutsideZProg (b : Arr) : Cmd :=
  .seq (.assign 56 (.read (b + 5) (.reg 55)))
    (.seq (.assign 57 (.read (b + 6) (.reg 55)))
      (.seq (.assign 58 (.read (b + 1) (.reg 56)))
        (.seq (.assign 59 (.read (b + 1) (.reg 57)))
          (.assign 58 (.op .add (.reg 58) (.reg 59))))))

theorem checkEdgeOutsideZProg_exec {w n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (b : Arr)
    (hw : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (e : Fin G.toComputeDigraph.numEdges)
    {s : State}
    (hr55 : s.regs 55 = e.1)
    (hedges : EdgesExpandedInv G b s)
    (hZ : s.arrs (b + 1) = bitSetList Z) :
    let u := G.toComputeDigraph.tail e
    let v := G.toComputeDigraph.head e
    let zsum := (if u ∈ Z then 1 else 0) + (if v ∈ Z then 1 else 0)
    ∃ s' t,
      Exec w (checkEdgeOutsideZProg b) s s' t ∧
      t ≤ 16 ∧
      s'.regs 56 = u.1 ∧
      s'.regs 57 = v.1 ∧
      s'.regs 58 = zsum ∧
      (zsum = 0 ↔ e ∈ edgesOutsideZ G.toComputeDigraph Z) ∧
      s'.arrs = s.arrs ∧
      (∀ r : Reg, r ≠ 56 → r ≠ 57 → r ≠ 58 → r ≠ 59 → s'.regs r = s.regs r) := by
  intro u v zsum
  have he_m : e.1 < G.numEdges := by rw [← G.length_directedEdgesList]; exact e.2
  have he_w : e.1 < 2 ^ w := by omega
  have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
  have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
  let zu : ℕ := if u ∈ Z then 1 else 0
  let zv : ℕ := if v ∈ Z then 1 else 0
  have hzu_w : zu < 2 ^ w := by dsimp [zu]; split_ifs <;> omega
  have hzv_w : zv < 2 ^ w := by dsimp [zv]; split_ifs <;> omega
  have hzsum_w : zu + zv < 2 ^ w := by dsimp [zu, zv]; split_ifs <;> omega
  rcases hedges with ⟨hlen_t, hlen_h, hget_th⟩
  have htu : (s.arrs (b + 5)).getD e.1 0 = u.1 := (hget_th e).1
  have hhv : (s.arrs (b + 6)).getD e.1 0 = v.1 := (hget_th e).2
  have hZ_len : (s.arrs (b + 1)).length = n := by rw [hZ, length_bitSetList]
  have hZ_u : (s.arrs (b + 1)).getD u.1 0 = zu := by rw [hZ, getD_bitSetList]
  have hZ_v : (s.arrs (b + 1)).getD v.1 0 = zv := by rw [hZ, getD_bitSetList]
  let s₁ := s.setReg 56 u.1
  have hex₁ : Exec w (.assign 56 (.read (b + 5) (.reg 55))) s s₁ 3 :=
    exec_assign_read_getD 56 (b + 5) 55 hr55 he_w (by rw [hlen_t]; exact he_m) htu hu_w
  let s₂ := s₁.setReg 57 v.1
  have hex₂ : Exec w (.assign 57 (.read (b + 6) (.reg 55))) s₁ s₂ 3 :=
    exec_assign_read_getD 57 (b + 6) 55 (by simp [s₁, hr55]) he_w
      (by simp [s₁, hlen_h, he_m]) (by simp [s₁]; exact hhv) hv_w
  let s₃ := s₂.setReg 58 zu
  have hex₃ : Exec w (.assign 58 (.read (b + 1) (.reg 56))) s₂ s₃ 3 :=
    exec_assign_read_getD 58 (b + 1) 56 (by simp [s₂, s₁]) hu_w
      (by simp [s₂, s₁, hZ_len, u.2]) (by simp [s₂, s₁]; exact hZ_u) hzu_w
  let s₄ := s₃.setReg 59 zv
  have hex₄ : Exec w (.assign 59 (.read (b + 1) (.reg 57))) s₃ s₄ 3 :=
    exec_assign_read_getD 59 (b + 1) 57 (by simp [s₃, s₂]) hv_w
      (by simp [s₃, s₂, s₁, hZ_len, v.2]) (by simp [s₃, s₂, s₁]; exact hZ_v) hzv_w
  let s₅ := s₄.setReg 58 (zu + zv)
  have hex₅ : Exec w (.assign 58 (.op .add (.reg 58) (.reg 59))) s₄ s₅ 4 :=
    .assign (by simp [s₄, s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hzu_w, hzv_w, hzsum_w])
  have hzsum_iff : zsum = 0 ↔ e ∈ edgesOutsideZ G.toComputeDigraph Z := by
    rw [mem_edgesOutsideZ]
    dsimp [zsum, u, v]
    constructor
    · intro h0
      split_ifs at h0 with huZ hvZ hvZ <;> try omega
      exact ⟨huZ, hvZ⟩
    · rintro ⟨huZ, hvZ⟩
      simp [huZ, hvZ]
  refine ⟨s₅, 16, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), le_refl 16,
    by simp [s₅, s₄, s₃, s₂, s₁],
    by simp [s₅, s₄, s₃, s₂],
    by simp [s₅, zsum, zu, zv],
    hzsum_iff, rfl,
    fun r hr1 hr2 hr3 hr4 => by
      simp [s₅, s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2,
        State.setReg_regs_ne _ _ hr3, State.setReg_regs_ne _ _ hr4]⟩

/-- Then-branch of Pass 1 when `e ∈ edgesOutsideZ D Z`: copies `(b + 3)[r_53]` to `(b + 10)[r_55]`,
marks `e` in `S`, sets `r_60 := r_55`, and increments `r_53`. -/
def pass1ThenProg (b : Arr) : Cmd :=
  .seq (.assign 59 (.read (b + 3) (.reg 53)))
    (.seq (.write (b + 10) (.reg 55) (.reg 59))
      (.seq (markEdgeInTreeProg b 55)
        (.seq (.assign 60 (.reg 55))
          (.assign 53 (.op .add (.reg 53) (.const 1))))))

/-- Loop body of Pass 1 for edge `r_55`. -/
def pass1Body (b : Arr) : Cmd :=
  .seq (checkEdgeOutsideZProg b)
    (.ite (.op .eq (.reg 58) (.const 0))
      (pass1ThenProg b)
      .skip)

/-- Pass 1 of `convertBDProg`: scans all edges `e = 0 .. m - 1` (`r_28 = m`), populates `(b + 10)[e]`,
`(b + 7)[e]`, and `(b + 8)` for all `e ∈ edgesOutsideZ D Z`, and counts `r_53 = m_del`. -/
def pass1Prog (b : Arr) : Cmd :=
  .seq (.assign 53 (.const 0))
    (.seq (.assign 60 (.const 0))
      (.seq (.assign 55 (.const 0))
        (forUp 55 (.reg 28) (pass1Body b))))

theorem pass1Prog_exec {w n t₀ : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (b : Arr)
    (f_tau₀ : ℕ → ℕ)
    (hw : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm1_w : G.numEdges + 1 < 2 ^ w)
    (ht₀_w : t₀ < 2 ^ w)
    (htau₀_lt : ∀ j < (G.deleteVertices Z).numEdges, f_tau₀ j < t₀)
    (hm_pos : 0 < G.numEdges)
    {s : State}
    (hr28 : s.regs 28 = G.numEdges)
    (hedges : EdgesExpandedInv G b s)
    (hZ : s.arrs (b + 1) = bitSetList Z)
    (hb3_len : (s.arrs (b + 3)).length = (G.deleteVertices Z).numEdges)
    (hb3_get : ∀ j < (G.deleteVertices Z).numEdges, (s.arrs (b + 3)).getD j 0 = f_tau₀ j)
    (hb7 : s.arrs (b + 7) = List.replicate G.numEdges 0)
    (hb8 : s.arrs (b + 8) = List.replicate n 0)
    (hb10_len : (s.arrs (b + 10)).length = G.numEdges) :
    ∃ s' t,
      Exec w (pass1Prog b) s s' t ∧
      t ≤ 58 * G.numEdges + 9 ∧
      s'.regs 53 = (G.deleteVertices Z).numEdges ∧
      InTreeInv G (edgesOutsideZ G.toComputeDigraph Z) (s'.arrs (b + 7)) ∧
      VertEdgeInv G (edgesOutsideZ G.toComputeDigraph Z) (s'.arrs (b + 8)) ∧
      (s'.arrs (b + 10)).length = G.numEdges ∧
      (∀ e ∈ edgesOutsideZ G.toComputeDigraph Z,
        (s'.arrs (b + 10)).getD e.1 0 =
          f_tau₀ (filterIdx G.directedEdgesList (edgeOutsideZPred Z) e.1)) ∧
      (∃ he₀ : s'.regs 60 < G.toComputeDigraph.numEdges,
        ((edgesOutsideZ G.toComputeDigraph Z).Nonempty →
          ⟨s'.regs 60, he₀⟩ ∈ edgesOutsideZ G.toComputeDigraph Z)) ∧
      (∀ a : Arr, a ≠ b + 7 → a ≠ b + 8 → a ≠ b + 10 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 53 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hm_w : G.numEdges < 2 ^ w := by omega
  have hm_eq : G.toComputeDigraph.numEdges = G.numEdges := G.length_directedEdgesList
  have hm_del_eq : (G.deleteVertices Z).toComputeDigraph.numEdges = (G.deleteVertices Z).numEdges :=
    (G.deleteVertices Z).length_directedEdgesList
  have hm_del_le : (G.deleteVertices Z).numEdges ≤ G.numEdges := G.numEdges_deleteVertices_le Z
  let s₀₁ := s.setReg 53 0
  let s₀₂ := s₀₁.setReg 60 0
  let s₁ := s₀₂.setReg 55 0
  have hex₀₁ : Exec w (.assign 53 (.const 0)) s s₀₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hex₀₂ : Exec w (.assign 60 (.const 0)) s₀₁ s₀₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hex₀₃ : Exec w (.assign 55 (.const 0)) s₀₂ s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (c : ℕ) (st : State) : Prop :=
    st.regs 28 = G.numEdges ∧
    st.regs 53 = filterIdx G.directedEdgesList (edgeOutsideZPred Z) c ∧
    st.regs 55 = c ∧
    InTreeInv G (edgesOutsideZUpTo G.toComputeDigraph Z c) (st.arrs (b + 7)) ∧
    VertEdgeInv G (edgesOutsideZUpTo G.toComputeDigraph Z c) (st.arrs (b + 8)) ∧
    (st.arrs (b + 10)).length = G.numEdges ∧
    (∀ e ∈ edgesOutsideZUpTo G.toComputeDigraph Z c,
      (st.arrs (b + 10)).getD e.1 0 =
        f_tau₀ (filterIdx G.directedEdgesList (edgeOutsideZPred Z) e.1)) ∧
    (∃ he₀ : st.regs 60 < G.toComputeDigraph.numEdges,
      ((edgesOutsideZUpTo G.toComputeDigraph Z c).Nonempty →
        ⟨st.regs 60, he₀⟩ ∈ edgesOutsideZUpTo G.toComputeDigraph Z c)) ∧
    (∀ a : Arr, a ≠ b + 7 → a ≠ b + 8 → a ≠ b + 10 → st.arrs a = s.arrs a) ∧
    (∀ r : Reg, r < 53 → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₁ := by
    refine ⟨by simp [s₁, s₀₂, s₀₁, hr28], by simp [s₁, s₀₂, s₀₁], by simp [s₁, s₀₂, s₀₁],
      by rw [edgesOutsideZUpTo_zero]; simpa [s₁, s₀₂, s₀₁, hb7] using inTreeInv_empty G,
      by rw [edgesOutsideZUpTo_zero]; simpa [s₁, s₀₂, s₀₁, hb8] using vertEdgeInv_empty G,
      by simp [s₁, s₀₂, s₀₁, hb10_len],
      fun e he => by simp at he,
      ⟨by rw [hm_eq]; simpa [s₁, s₀₂, s₀₁] using hm_pos,
        fun hne => by rw [edgesOutsideZUpTo_zero] at hne; simp at hne⟩,
      fun a _ _ _ => by simp [s₁, s₀₂, s₀₁],
      fun r hr => ?_⟩
    have hr55 : r ≠ 55 := by intro h; subst h; revert hr; decide
    have hr60 : r ≠ 60 := by intro h; subst h; revert hr; decide
    have hr53 : r ≠ 53 := by intro h; subst h; revert hr; decide
    simp [s₁, s₀₂, s₀₁, State.setReg_regs_ne _ _ hr55, State.setReg_regs_ne _ _ hr60,
      State.setReg_regs_ne _ _ hr53]
  have hLoop :
      ⦃Inv 0⦄[w] forUp 55 (.reg 28) (pass1Body b) ⦃Inv G.numEdges⦄ ≤
        fun _ => 3 + G.numEdges * (7 + 51) := by
    apply Triple.forUp_const Inv G.numEdges 51 h1_w hm_w
    · intro c _ st ⟨hr28_c, _, hr55_c, _, _, _, _, _, _, _⟩
      exact ⟨hr55_c, by simp [Expr.eval, checkWord, hr28_c, hm_w]⟩
    · intro c hc st ⟨hr28_c, hr53_c, hr55_c, hintree_c, hvert_c, hb10_c, htau_c,
        ⟨he₀_lt, he₀_mem⟩, harr_c, hreg_c⟩
      let e : Fin G.toComputeDigraph.numEdges := ⟨c, by rw [hm_eq]; exact hc⟩
      have hedges_st : EdgesExpandedInv G b st := by
        rcases hedges with ⟨ht, hh, hth⟩
        have h5 := harr_c (b + 5) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
        have h6 := harr_c (b + 6) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
        exact ⟨by rw [h5, ht], by rw [h6, hh], fun e' => by rw [h5, h6]; exact hth e'⟩
      have hZ_st : st.arrs (b + 1) = bitSetList Z := by
        rw [harr_c (b + 1) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)), hZ]
      rcases checkEdgeOutsideZProg_exec G Z b hw hn_w hm_w e hr55_c hedges_st hZ_st with
        ⟨st₁, t₁, hex₁, ht₁, _, _, hr58_1, hzsum_iff, harr₁, hreg₁⟩
      let zsum := (if G.toComputeDigraph.tail e ∈ Z then 1 else 0) +
        (if G.toComputeDigraph.head e ∈ Z then 1 else 0)
      have hzsum_w : zsum < 2 ^ w := by dsimp [zsum]; split_ifs <;> omega
      by_cases hmem : e ∈ edgesOutsideZ G.toComputeDigraph Z
      · -- True branch: `zsum = 0`
        have hz0 : zsum = 0 := hzsum_iff.mpr hmem
        have hr58_zero : st₁.regs 58 = 0 := hr58_1.trans hz0
        have hcond : (.op .eq (.reg 58) (.const 0) : Expr).eval w st₁ = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr58_zero, h0_w, h1_w]
        let j := filterIdx G.directedEdgesList (edgeOutsideZPred Z) e.1
        have hj_lt : j < (G.deleteVertices Z).numEdges := by
          rw [← hm_del_eq]
          exact filterIdx_lt_numEdges_deleteVertices G Z hmem
        have hj_w : j < 2 ^ w := by omega
        have hj1_w : j + 1 < 2 ^ w := by omega
        have hr53_1 : st₁.regs 53 = j := by
          rw [hreg₁ 53 (by decide) (by decide) (by decide) (by decide), hr53_c]
        have hr55_1 : st₁.regs 55 = e.1 := by
          rw [hreg₁ 55 (by decide) (by decide) (by decide) (by decide), hr55_c]
        have hb3_1 : st₁.arrs (b + 3) = s.arrs (b + 3) := by
          rw [harr₁, harr_c (b + 3) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))]
        have htau_j_w : f_tau₀ j < 2 ^ w := Nat.lt_trans (htau₀_lt j hj_lt) ht₀_w
        -- 1. assign 59 (.read (b + 3) (.reg 53))
        let st₂ := st₁.setReg 59 (f_tau₀ j)
        have hex₂ : Exec w (.assign 59 (.read (b + 3) (.reg 53))) st₁ st₂ 3 :=
          exec_assign_read_getD 59 (b + 3) 53 hr53_1 hj_w
            (by rw [hb3_1, hb3_len]; exact hj_lt) (by rw [hb3_1]; exact hb3_get j hj_lt) htau_j_w
        -- 2. write (b + 10) (.reg 55) (.reg 59)
        let st₃ := st₂.writeArr (b + 10) e.1 (f_tau₀ j)
        have hex₃ : Exec w (.write (b + 10) (.reg 55) (.reg 59)) st₂ st₃ 3 :=
          exec_write_reg (b + 10) 55 59 (by simp [st₂, hr55_1]) (by simp [st₂])
            (by dsimp [e]; omega) htau_j_w (by simp [st₂, harr₁, hb10_c]; exact hc)
        -- 3. markEdgeInTreeProg b 55
        have hedges_3 : EdgesExpandedInv G b st₃ := by
          rcases hedges_st with ⟨ht, hh, hth⟩
          exact ⟨by simp [st₃, st₂, harr₁, ht], by simp [st₃, st₂, harr₁, hh],
            fun e' => by simpa [st₃, st₂, harr₁] using hth e'⟩
        rcases markEdgeInTreeProg_exec G b 55 (by decide) (by decide) (by decide)
            h1_w hn_w hm1_w e (by simp [st₃, st₂, hr55_1]) hedges_3
            (by simpa [st₃, st₂, harr₁] using hintree_c)
            (by simpa [st₃, st₂, harr₁] using hvert_c) with
          ⟨st₄, t₄, hex₄, ht₄, hintree₄, hvert₄, harr₄, hreg₄⟩
        -- 4. assign 60 (.reg 55)
        have hr55_4 : st₄.regs 55 = e.1 := by
          rw [hreg₄ 55 (by decide) (by decide) (by decide)]; simp [st₃, st₂, hr55_1]
        have hr53_4 : st₄.regs 53 = j := by
          rw [hreg₄ 53 (by decide) (by decide) (by decide)]; simp [st₃, st₂, hr53_1]
        let st₅ := st₄.setReg 60 e.1
        have hex₅ : Exec w (.assign 60 (.reg 55)) st₄ st₅ 2 :=
          .assign (by simp [Expr.eval, checkWord, hr55_4, show e.1 < 2 ^ w by dsimp [e]; omega])
        -- 5. assign 53 (.op .add (.reg 53) (.const 1))
        let st₆ := st₅.setReg 53 (j + 1)
        have hex₆ : Exec w (.assign 53 (.op .add (.reg 53) (.const 1))) st₅ st₆ 4 :=
          .assign (by simp [st₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr53_4, hj_w, h1_w, hj1_w])
        have hex_then : Exec w (pass1ThenProg b) st₁ st₆ (3 + (3 + (t₄ + (2 + 4)))) :=
          .seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))
        have hex_ite : Exec w (.ite (.op .eq (.reg 58) (.const 0)) (pass1ThenProg b) .skip)
            st₁ st₆ (3 + (3 + (3 + (t₄ + (2 + 4))))) :=
          .ite_true hcond (by decide) hex_then
        have hS_succ : edgesOutsideZUpTo G.toComputeDigraph Z (c + 1) =
            insert e (edgesOutsideZUpTo G.toComputeDigraph Z c) :=
          edgesOutsideZUpTo_succ_of_mem G.toComputeDigraph Z hmem
        have hP_true : edgeOutsideZPred Z (G.directedEdgesList[c]'e.2) = true :=
          (edgeOutsideZPred_getElem_iff G Z e).mpr hmem
        have hfilt_succ : filterIdx G.directedEdgesList (edgeOutsideZPred Z) (c + 1) = j + 1 := by
          rw [filterIdx_succ G.directedEdgesList (edgeOutsideZPred Z) e.2]
          dsimp [e, j]
          simp [hP_true]
        have harr10_6 : st₆.arrs (b + 10) = (st.arrs (b + 10)).set c (f_tau₀ j) := by
          rw [show st₆.arrs = st₄.arrs from rfl,
              harr₄ (b + 10) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))]
          simp [st₃, st₂, harr₁, e]
        refine ⟨st₆, t₁ + (3 + (3 + (3 + (t₄ + (2 + 4))))), .seq hex₁ hex_ite, by dsimp only; omega,
          ⟨?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
          by simp [st₆, st₅, hr55_4, e]⟩
        · simp [st₆, st₅, hreg₄ 28 (by decide) (by decide) (by decide), st₃, st₂,
            hreg₁ 28 (by decide) (by decide) (by decide) (by decide), hr28_c]
        · simp [st₆, hfilt_succ]
        · rw [hS_succ]; simpa [st₆, st₅] using hintree₄
        · rw [hS_succ]; simpa [st₆, st₅] using hvert₄
        · simp [harr10_6, hb10_c]
        · intro e' he'
          have he'_m : e'.1 < G.numEdges := by rw [← hm_eq]; exact e'.2
          rw [State.setReg_arrs, harr10_6, getD_set_of_lt _ _ _ (by rw [hb10_c]; exact he'_m)]
          rw [hS_succ, Finset.mem_insert] at he'
          rcases he' with rfl | he'S
          · simp [j, e]
          · have hlt_c : e'.1 < c := (mem_edgesOutsideZUpTo G.toComputeDigraph Z c e').mp he'S |>.2
            have hne_c : c ≠ e'.1 := by omega
            simp only [hne_c, ↓reduceIte]
            exact htau_c e' he'S
        · have he₀_lt6 : (st₆.setReg 55 (c + 1)).regs 60 < G.toComputeDigraph.numEdges := e.2
          refine ⟨he₀_lt6, fun _ => ?_⟩
          rw [hS_succ]
          have h60 : (st₆.setReg 55 (c + 1)).regs 60 = e.1 := rfl
          have heq : (⟨(st₆.setReg 55 (c + 1)).regs 60, he₀_lt6⟩ : Fin G.toComputeDigraph.numEdges) = e :=
            Fin.ext h60
          rw [heq]
          exact Finset.mem_insert_self e _
        · intro a ha7 ha8 ha10
          simp [st₆, st₅, harr₄ a ha7 ha8, st₃, st₂, ha10, harr₁, harr_c a ha7 ha8 ha10]
        · intro r hr
          have hr55 : r ≠ 55 := by intro h; subst h; revert hr; decide
          have hr53 : r ≠ 53 := by intro h; subst h; revert hr; decide
          have hr60 : r ≠ 60 := by intro h; subst h; revert hr; decide
          have hr56 : r ≠ 56 := by intro h; subst h; revert hr; decide
          have hr57 : r ≠ 57 := by intro h; subst h; revert hr; decide
          have hr58 : r ≠ 58 := by intro h; subst h; revert hr; decide
          have hr59 : r ≠ 59 := by intro h; subst h; revert hr; decide
          simp [st₆, st₅, State.setReg_regs_ne _ _ hr55, State.setReg_regs_ne _ _ hr53,
            State.setReg_regs_ne _ _ hr60, hreg₄ r hr56 hr57 hr59, st₃, st₂,
            State.setReg_regs_ne _ _ hr59, hreg₁ r hr56 hr57 hr58 hr59, hreg_c r hr]
      · -- False branch: `zsum ≠ 0`
        have hzne : zsum ≠ 0 := fun h0 => hmem (hzsum_iff.mp h0)
        have hr58_ne : st₁.regs 58 ≠ 0 := by rw [hr58_1]; exact hzne
        have hr58_w : st₁.regs 58 < 2 ^ w := by rw [hr58_1]; exact hzsum_w
        have hcond : (.op .eq (.reg 58) (.const 0) : Expr).eval w st₁ = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr58_ne, h0_w, hr58_w]
        have hex_ite : Exec w (.ite (.op .eq (.reg 58) (.const 0)) (pass1ThenProg b) .skip)
            st₁ st₁ (3 + 1) :=
          .ite_false hcond (.skip st₁)
        have hS_succ : edgesOutsideZUpTo G.toComputeDigraph Z (c + 1) =
            edgesOutsideZUpTo G.toComputeDigraph Z c :=
          edgesOutsideZUpTo_succ_of_notMem G.toComputeDigraph Z hmem
        have hP_false : ¬edgeOutsideZPred Z (G.directedEdgesList[c]'e.2) = true :=
          fun h => hmem ((edgeOutsideZPred_getElem_iff G Z e).mp h)
        have hfilt_succ :
            filterIdx G.directedEdgesList (edgeOutsideZPred Z) (c + 1) =
              filterIdx G.directedEdgesList (edgeOutsideZPred Z) c := by
          rw [filterIdx_succ G.directedEdgesList (edgeOutsideZPred Z) e.2]
          dsimp [e]
          simp [hP_false]
        have hr60_1 : (st₁.setReg 55 (c + 1)).regs 60 = st.regs 60 := by
          simp [hreg₁ 60 (by decide) (by decide) (by decide) (by decide)]
        refine ⟨st₁, t₁ + (3 + 1), .seq hex₁ hex_ite, by dsimp only; omega,
          ⟨by simp [hreg₁ 28 (by decide) (by decide) (by decide) (by decide), hr28_c],
           by simp [hreg₁ 53 (by decide) (by decide) (by decide) (by decide), hr53_c, hfilt_succ],
           by simp,
           by rw [hS_succ]; simpa [harr₁] using hintree_c,
           by rw [hS_succ]; simpa [harr₁] using hvert_c,
           by simp [harr₁, hb10_c],
           fun e' he' => by rw [hS_succ] at he'; simpa [harr₁] using htau_c e' he',
           ⟨by rw [hr60_1]; exact he₀_lt, fun hne => ?_⟩,
           fun a ha7 ha8 ha10 => by simp [harr₁, harr_c a ha7 ha8 ha10],
           fun r hr => ?_⟩,
          by simp [hreg₁ 55 (by decide) (by decide) (by decide) (by decide), hr55_c]⟩
        · rw [hS_succ] at hne ⊢
          convert he₀_mem hne using 1
          ext; exact hr60_1
        · have hr55 : r ≠ 55 := by intro h; subst h; revert hr; decide
          have hr56 : r ≠ 56 := by intro h; subst h; revert hr; decide
          have hr57 : r ≠ 57 := by intro h; subst h; revert hr; decide
          have hr58 : r ≠ 58 := by intro h; subst h; revert hr; decide
          have hr59 : r ≠ 59 := by intro h; subst h; revert hr; decide
          simp [State.setReg_regs_ne _ _ hr55, hreg₁ r hr56 hr57 hr58 hr59, hreg_c r hr]
  rcases hLoop s₁ hInv₀ with
    ⟨s₂, t₂, hex₂, ht₂, _, hr53_2, _, hintree_2, hvert_2, hb10_2, htau_2, he₀_2, harr_2, hreg_2⟩
  dsimp only at ht₂
  rw [edgesOutsideZUpTo_full] at hintree_2 hvert_2 htau_2 he₀_2
  have hfilt_full :
      filterIdx G.directedEdgesList (edgeOutsideZPred Z) G.numEdges =
        (G.deleteVertices Z).numEdges := by
    rw [← G.length_directedEdgesList, filterIdx_length, ← G.directedEdgesList_deleteVertices Z,
      (G.deleteVertices Z).length_directedEdgesList]
  rw [hfilt_full] at hr53_2
  exact ⟨s₂, 2 + (2 + (2 + t₂)), .seq hex₀₁ (.seq hex₀₂ (.seq hex₀₃ hex₂)), by omega,
    hr53_2, hintree_2, hvert_2, hb10_2, htau_2, he₀_2, harr_2, hreg_2⟩

theorem parentTree_congr_of_pos (t : ℕ) (p₁ p₂ : ℕ → ℕ)
    (h : ∀ z, 0 < z → z < t → p₁ z = p₂ z) :
    parentTree t p₁ = parentTree t p₂ := by
  ext u v
  unfold parentTree
  simp only [ne_eq]
  apply and_congr_right
  intro _
  constructor
  · rintro (⟨hu, hvp⟩ | ⟨hv, hup⟩)
    · exact Or.inl ⟨hu, hvp.trans (h u.1 hu u.2)⟩
    · exact Or.inr ⟨hv, hup.trans (h v.1 hv v.2)⟩
  · rintro (⟨hu, hvp⟩ | ⟨hv, hup⟩)
    · exact Or.inl ⟨hu, hvp.trans (h u.1 hu u.2).symm⟩
    · exact Or.inr ⟨hv, hup.trans (h v.1 hv v.2).symm⟩

/-- Combined state invariant for Pass 3 of `convertBDProg` after scanning the first `c` edges:
there exist an edge subset `S ⊆ Fin D.numEdges` containing `edgesOutsideZ D Z` and all edges
with index `< c`, a tree size `t` with `t + 2 * (G.numEdges - S.card) ≤ 2 * G.numEdges + 1`,
a parent function `p : ℕ → ℕ` with `p 0 < t`, and a leaf map `τ : Fin D.numEdges → Fin t`
satisfying `IsPartialDigraphBD (max ω 2) D Z S t p τ`, `ParTauInv`, `InTreeInv`, `VertEdgeInv`,
and `s.regs 60 ∈ S`. -/
def Pass3StateInv {n : ℕ} (ω : ℕ) (G : MultiDigraph n) (Z : Finset (Fin n))
    (b : Arr) (c : ℕ) (s : State) : Prop :=
  ∃ (S : Finset (Fin G.toComputeDigraph.numEdges))
    (t : ℕ) (p : ℕ → ℕ) (τ : Fin G.toComputeDigraph.numEdges → Fin t),
    IsPartialDigraphBD (max ω 2) G.toComputeDigraph Z S t p τ ∧
    p 0 < t ∧
    (∀ e : Fin G.toComputeDigraph.numEdges, e.1 < c → e ∈ S) ∧
    t + 2 * (G.numEdges - S.card) ≤ 2 * G.numEdges + 1 ∧
    s.regs 52 = t ∧
    ParTauInv G S t p τ (s.arrs (b + 9)) (s.arrs (b + 10)) ∧
    InTreeInv G S (s.arrs (b + 7)) ∧
    VertEdgeInv G S (s.arrs (b + 8)) ∧
    ∃ he₀ : s.regs 60 < G.toComputeDigraph.numEdges,
      (⟨s.regs 60, he₀⟩ : Fin G.toComputeDigraph.numEdges) ∈ S

/-- Subcase B2 of Pass 2 (`m_del < 2`, `2 ≤ m`): initializes the 2-vertex tree `parentTree 2 (fun _ => 0)`
on `{e₀, e₁}` where `e₀ = r_60` and `e₁ = if e₀ == 0 then 1 else 0`. -/
def pass2SmallProg (b : Arr) : Cmd :=
  .seq (.ite (.op .eq (.reg 60) (.const 0))
      (.assign 61 (.const 1))
      (.assign 61 (.const 0)))
    (.seq (.assign 52 (.const 2))
      (.seq (.assign 55 (.const 0))
        (.seq (.write (b + 9) (.reg 55) (.const 0))
          (.seq (.assign 55 (.const 1))
            (.seq (.write (b + 9) (.reg 55) (.const 0))
              (.seq (.write (b + 10) (.reg 60) (.const 0))
                (.seq (.write (b + 10) (.reg 61) (.const 1))
                  (.seq (markEdgeInTreeProg b 60)
                    (markEdgeInTreeProg b 61)))))))))

/-- Pass 2 of `convertBDProg`: branches on `r_53 < 2` (`m_del < 2`) to initialize either the
2-edge tree (`pass2SmallProg`) or the lifted branch-decomposition from `b + 2` (`copyIntoProg`). -/
def pass2Prog (b : Arr) : Cmd :=
  .ite (.op .lt (.reg 53) (.const 2))
    (pass2SmallProg b)
    (.seq (.write (b + 2) (.const 0) (.const 0))
      (copyIntoProg (b + 2) (b + 9) 52))

theorem pass2Prog_exec {w n t₀ ω : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (b : Arr)
    (par₀ f_tau₀ : ℕ → ℕ)
    (hw : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm_w : 2 * G.numEdges + 1 < 2 ^ w)
    (hm_ge2 : 2 ≤ G.numEdges)
    (hbd₀ : IsWrittenDigraphBD ω (G.deleteVertices Z).toComputeDigraph t₀ par₀ f_tau₀)
    {s : State}
    (hr52 : s.regs 52 = t₀)
    (hr53 : s.regs 53 = (G.deleteVertices Z).numEdges)
    (hedges : EdgesExpandedInv G b s)
    (hb2_len : (s.arrs (b + 2)).length = t₀)
    (hb2_get : ∀ z < t₀, (s.arrs (b + 2)).getD z 0 = par₀ z)
    (hb9_len : (s.arrs (b + 9)).length = 2 * G.numEdges + 1)
    (hb10_len : (s.arrs (b + 10)).length = G.numEdges)
    (htau_get : ∀ e ∈ edgesOutsideZ G.toComputeDigraph Z,
      (s.arrs (b + 10)).getD e.1 0 =
        f_tau₀ (filterIdx G.directedEdgesList (edgeOutsideZPred Z) e.1))
    (hintree : InTreeInv G (edgesOutsideZ G.toComputeDigraph Z) (s.arrs (b + 7)))
    (hvert : VertEdgeInv G (edgesOutsideZ G.toComputeDigraph Z) (s.arrs (b + 8)))
    (he₀_inv : ∃ he₀ : s.regs 60 < G.toComputeDigraph.numEdges,
      ((edgesOutsideZ G.toComputeDigraph Z).Nonempty →
        ⟨s.regs 60, he₀⟩ ∈ edgesOutsideZ G.toComputeDigraph Z)) :
    ∃ s' time,
      Exec w (pass2Prog b) s s' time ∧
      time ≤ 26 * G.numEdges + 65 ∧
      Pass3StateInv ω G Z b 0 s' ∧
      (∀ a : Arr, a ≠ b + 2 → a ≠ b + 7 → a ≠ b + 8 → a ≠ b + 9 → a ≠ b + 10 →
        s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 52 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hm_eq : G.toComputeDigraph.numEdges = G.numEdges := G.length_directedEdgesList
  have hm_del_eq : (G.deleteVertices Z).toComputeDigraph.numEdges = (G.deleteVertices Z).numEdges :=
    (G.deleteVertices Z).length_directedEdgesList
  have hm_del_le : (G.deleteVertices Z).numEdges ≤ G.numEdges := G.numEdges_deleteVertices_le Z
  have hm_del_w : (G.deleteVertices Z).numEdges < 2 ^ w := by omega
  rcases he₀_inv with ⟨he₀, he₀_mem⟩
  let e₀ : Fin G.toComputeDigraph.numEdges := ⟨s.regs 60, he₀⟩
  have he₀_m : e₀.1 < G.numEdges := by rw [← hm_eq]; exact e₀.2
  have he₀_w : e₀.1 < 2 ^ w := by omega
  by_cases hlt2 : (G.deleteVertices Z).numEdges < 2
  · -- Subcase B2: `(G.deleteVertices Z).numEdges < 2`
    have hcond : (.op .lt (.reg 53) (.const 2) : Expr).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr53, hlt2, hm_del_w, hw, h1_w]
    have hsub₀ : edgesOutsideZ G.toComputeDigraph Z ⊆ {e₀} := by
      intro e he
      rw [Finset.mem_singleton]
      have hcard_le1 : (edgesOutsideZ G.toComputeDigraph Z).card ≤ 1 := by
        rw [card_edgesOutsideZ_eq G Z]
        omega
      exact Finset.card_le_one.mp hcard_le1 e he e₀ (he₀_mem ⟨e, he⟩)
    let e₁_val : ℕ := if e₀.1 = 0 then 1 else 0
    have he₁_m : e₁_val < G.numEdges := by dsimp [e₁_val]; split_ifs <;> omega
    have he₁_w : e₁_val < 2 ^ w := by omega
    let e₁ : Fin G.toComputeDigraph.numEdges := ⟨e₁_val, by rw [hm_eq]; exact he₁_m⟩
    have hne_01 : e₀ ≠ e₁ := by
      intro h
      have hval : e₀.1 = e₁_val := congrArg Fin.val h
      dsimp [e₁_val] at hval
      split_ifs at hval <;> omega
    have hne_val_01 : e₀.1 ≠ e₁.1 := fun h => hne_01 (Fin.ext h)
    have hsub_01 : edgesOutsideZ G.toComputeDigraph Z ⊆ ({e₀, e₁} : Finset (Fin G.toComputeDigraph.numEdges)) := by
      intro e he
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (Finset.mem_singleton.mp (hsub₀ he))
    -- 1. ite (.op .eq (.reg 60) (.const 0)) (.assign 61 (.const 1)) (.assign 61 (.const 0))
    let s₁ := s.setReg 61 e₁_val
    have hex₁ : Exec w (.ite (.op .eq (.reg 60) (.const 0))
        (.assign 61 (.const 1)) (.assign 61 (.const 0))) s s₁ 5 := by
      by_cases he0 : e₀.1 = 0
      · have hc0 : (.op .eq (.reg 60) (.const 0) : Expr).eval w s = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, show s.regs 60 = 0 from he0, h0_w, h1_w]
        have he₁_eq : e₁_val = 1 := by simp [e₁_val, he0]
        rw [show s₁ = s.setReg 61 1 by simp [s₁, he₁_eq]]
        exact .ite_true hc0 (by decide) (.assign (by simp [Expr.eval, checkWord, h1_w]))
      · have hr60_ne : s.regs 60 ≠ 0 := he0
        have hr60_w : s.regs 60 < 2 ^ w := he₀_w
        have hc0 : (.op .eq (.reg 60) (.const 0) : Expr).eval w s = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr60_ne, hr60_w, h0_w]
        have he₁_eq : e₁_val = 0 := by simp [e₁_val, he0]
        rw [show s₁ = s.setReg 61 0 by simp [s₁, he₁_eq]]
        exact .ite_false hc0 (.assign (by simp [Expr.eval, checkWord, h0_w]))
    -- 2. assign 52 2, assign 55 0, write (b+9) 55 0, assign 55 1, write (b+9) 55 0,
    --    write (b+10) 60 0, write (b+10) 61 1
    let s₂ := s₁.setReg 52 2
    have hex₂ : Exec w (.assign 52 (.const 2)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    let s₃ := s₂.setReg 55 0
    have hex₃ : Exec w (.assign 55 (.const 0)) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    let s₄ := s₃.writeArr (b + 9) 0 0
    have hex₄ : Exec w (.write (b + 9) (.reg 55) (.const 0)) s₃ s₄ 3 :=
      exec_write_const (b + 9) 55 0 (by simp [s₃]) h0_w h0_w
        (by simp [s₃, s₂, s₁, hb9_len])
    let s₅ := s₄.setReg 55 1
    have hex₅ : Exec w (.assign 55 (.const 1)) s₄ s₅ 2 :=
      .assign (by simp [Expr.eval, checkWord, h1_w])
    let s₆ := s₅.writeArr (b + 9) 1 0
    have hex₆ : Exec w (.write (b + 9) (.reg 55) (.const 0)) s₅ s₆ 3 :=
      exec_write_const (b + 9) 55 0 (by simp [s₅]) h1_w h0_w
        (by simp [s₅, s₄, s₃, s₂, s₁, hb9_len]; omega)
    let s₇ := s₆.writeArr (b + 10) e₀.1 0
    have hex₇ : Exec w (.write (b + 10) (.reg 60) (.const 0)) s₆ s₇ 3 :=
      exec_write_const (b + 10) 60 0 (by simp [s₆, s₅, s₄, s₃, s₂, s₁]; rfl) he₀_w h0_w
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hb10_len, he₀_m])
    let s₈ := s₇.writeArr (b + 10) e₁.1 1
    have hex₈ : Exec w (.write (b + 10) (.reg 61) (.const 1)) s₇ s₈ 3 :=
      exec_write_const (b + 10) 61 1 (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]; rfl) he₁_w h1_w
        (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hb10_len, e₁, he₁_m])
    -- 3. markEdgeInTreeProg b 60 and markEdgeInTreeProg b 61
    have hedges_8 : EdgesExpandedInv G b s₈ := by
      rcases hedges with ⟨ht, hh, hth⟩
      exact ⟨by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ht],
        by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hh],
        fun e => by simpa [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hth e⟩
    rcases markEdgeInTreeProg_exec G b 60 (by decide) (by decide) (by decide)
        h1_w hn_w (by omega) e₀ (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁]; rfl) hedges_8
        (by simpa [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hintree)
        (by simpa [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hvert) with
      ⟨s₉, t₉, hex₉, ht₉, hintree₉, hvert₉, harr₉, hreg₉⟩
    have hedges_9 : EdgesExpandedInv G b s₉ := by
      rcases hedges_8 with ⟨ht, hh, hth⟩
      have h5 := harr₉ (b + 5) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
      have h6 := harr₉ (b + 6) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
      exact ⟨by rw [h5, ht], by rw [h6, hh], fun e => by rw [h5, h6]; exact hth e⟩
    have hr61_9 : s₉.regs 61 = e₁.1 := by
      rw [hreg₉ 61 (by decide) (by decide) (by decide)]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁]; rfl
    rcases markEdgeInTreeProg_exec G b 61 (by decide) (by decide) (by decide)
        h1_w hn_w (by omega) e₁ hr61_9 hedges_9 hintree₉ hvert₉ with
      ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hintree₁₀, hvert₁₀, harr₁₀, hreg₁₀⟩
    have hex_small : Exec w (pass2SmallProg b) s s₁₀
        (5 + (2 + (2 + (3 + (2 + (3 + (3 + (3 + (t₉ + t₁₀))))))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀))))))))
    have hex_ite : Exec w (pass2Prog b) s s₁₀
        (3 + (5 + (2 + (2 + (3 + (2 + (3 + (3 + (3 + (t₉ + t₁₀)))))))))) :=
      .ite_true hcond (by decide) hex_small
    have hS_eq : insert e₁ (insert e₀ (edgesOutsideZ G.toComputeDigraph Z)) =
        ({e₀, e₁} : Finset (Fin G.toComputeDigraph.numEdges)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl | hx)
        · exact Or.inr rfl
        · exact Or.inl rfl
        · exact Or.inl (Finset.mem_singleton.mp (hsub₀ hx))
      · rintro (rfl | rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
    rw [hS_eq] at hintree₁₀ hvert₁₀
    have harr9_10 : s₁₀.arrs (b + 9) = ((s.arrs (b + 9)).set 0 0).set 1 0 := by
      rw [harr₁₀ (b + 9) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)),
          harr₉ (b + 9) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁]
    have harr10_10 : s₁₀.arrs (b + 10) = ((s.arrs (b + 10)).set e₀.1 0).set e₁.1 1 := by
      rw [harr₁₀ (b + 10) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)),
          harr₉ (b + 10) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁]
    have hr52_10 : s₁₀.regs 52 = 2 := by
      rw [hreg₁₀ 52 (by decide) (by decide) (by decide),
          hreg₉ 52 (by decide) (by decide) (by decide)]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂]
    have hr60_10 : s₁₀.regs 60 = e₀.1 := by
      rw [hreg₁₀ 60 (by decide) (by decide) (by decide),
          hreg₉ 60 (by decide) (by decide) (by decide)]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁]; rfl
    refine ⟨s₁₀, _, hex_ite, by omega,
      ⟨{e₀, e₁}, 2, fun _ => 0,
       fun e => if e = e₀ then ⟨0, by omega⟩ else ⟨1, by omega⟩,
       isPartialDigraphBD_of_two_edges ω G.toComputeDigraph Z hne_01 hsub_01,
       by dsimp; omega,
       fun _ h => by omega,
       by rw [Finset.card_pair hne_01]; omega,
       hr52_10,
       ⟨by rw [harr9_10]; simp [hb9_len],
        by rw [harr10_10]; simp [hb10_len],
        fun z hz => by
          rw [harr9_10, getD_set_of_lt _ _ _ (by simp [hb9_len]; omega),
              getD_set_of_lt _ _ _ (by rw [hb9_len]; omega)]
          rcases (by omega : z = 0 ∨ z = 1) with rfl | rfl <;> simp,
        fun e he => by
          rw [harr10_10, getD_set_of_lt _ _ _ (by simp [hb10_len]; rw [← hm_eq]; exact e.2),
              getD_set_of_lt _ _ _ (by rw [hb10_len, ← hm_eq]; exact e.2)]
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl
          · simp [hne_val_01.symm]
          · simp [hne_01.symm]⟩,
       hintree₁₀, hvert₁₀,
       ⟨hr60_10.symm ▸ e₀.2, by
         have heq : (⟨s₁₀.regs 60, hr60_10.symm ▸ e₀.2⟩ : Fin G.toComputeDigraph.numEdges) = e₀ :=
           Fin.ext hr60_10
         rw [heq]; simp⟩⟩,
      fun a _ ha7 ha8 ha9 ha10 => by
        rw [harr₁₀ a ha7 ha8, harr₉ a ha7 ha8]
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha9, ha10],
      fun r hr => ?_⟩
    have hr56 : r ≠ 56 := by intro h; subst h; revert hr; decide
    have hr57 : r ≠ 57 := by intro h; subst h; revert hr; decide
    have hr59 : r ≠ 59 := by intro h; subst h; revert hr; decide
    have hr55 : r ≠ 55 := by intro h; subst h; revert hr; decide
    have hr52' : r ≠ 52 := by intro h; subst h; revert hr; decide
    have hr61 : r ≠ 61 := by intro h; subst h; revert hr; decide
    rw [hreg₁₀ r hr56 hr57 hr59, hreg₉ r hr56 hr57 hr59]
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
      State.setReg_regs_ne _ _ hr55, State.setReg_regs_ne _ _ hr52', State.setReg_regs_ne _ _ hr61]
  · -- Subcase B1: `2 ≤ (G.deleteVertices Z).numEdges`
    have hge2 : 2 ≤ (G.deleteVertices Z).numEdges := by omega
    have hcond : (.op .lt (.reg 53) (.const 2) : Expr).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr53, hlt2, hm_del_w, hw]
    rcases hbd₀ with ⟨ht₀_pos, ht₀_le, hpar₀_lt, htau₀_lt, hbd₀_or⟩
    rw [hm_del_eq] at ht₀_le htau₀_lt
    have ht₀_le_m : t₀ ≤ 2 * G.numEdges + 1 := by omega
    have ht₀_w : t₀ < 2 ^ w := by omega
    rcases hbd₀_or with hle1 | ⟨htau₀, hbd₀_full⟩
    · exfalso; rw [hm_del_eq] at hle1; omega
    · let par₀' (z : ℕ) : ℕ := if z = 0 then 0 else par₀ z
      have hpar₀'_lt : ∀ z, 0 < z → z < t₀ → par₀' z < z := by
        intro z hz_pos hz_lt
        simp [par₀', Nat.ne_of_gt hz_pos, hpar₀_lt z hz_pos hz_lt]
      have htree_eq : parentTree t₀ par₀' = parentTree t₀ par₀ :=
        parentTree_congr_of_pos t₀ par₀' par₀ (fun z hz_pos _ => by simp [par₀', Nat.ne_of_gt hz_pos])
      have hbd₀'_full : IsDigraphBranchDecompOfWidthLe ω (G.deleteVertices Z).toComputeDigraph
          (parentTree t₀ par₀') (fun j => ⟨f_tau₀ j.1, htau₀ j.1 j.2⟩) := by
        convert hbd₀_full using 1
      let s₀ := s.writeArr (b + 2) 0 0
      have hex₀ : Exec w (.write (b + 2) (.const 0) (.const 0)) s s₀ 3 :=
        .write (by simp [Expr.eval, checkWord, h0_w]) (by simp [Expr.eval, checkWord, h0_w])
          (by rw [hb2_len]; exact ht₀_pos)
      have hb2_get₀ : ∀ z < t₀, (s₀.arrs (b + 2)).getD z 0 = par₀' z := by
        intro z hz
        have hset : s₀.arrs (b + 2) = (s.arrs (b + 2)).set 0 0 := by simp [s₀]
        rw [hset, getD_set_of_lt _ _ _ (by rw [hb2_len]; exact hz)]
        by_cases hz0 : z = 0
        · subst hz0; simp [par₀']
        · simp only [par₀', hz0, Ne.symm hz0, ↓reduceIte, hb2_get z hz]
      have hb2_w₀ : ∀ z < t₀, (s₀.arrs (b + 2)).getD z 0 < 2 ^ w := by
        intro z hz
        rw [hb2_get₀ z hz]
        by_cases hz0 : z = 0
        · subst hz0; simp [par₀', h0_w]
        · have hz_pos : 0 < z := by omega
          exact Nat.lt_trans (Nat.lt_trans (hpar₀'_lt z hz_pos hz) hz) ht₀_w
      have hr52_0 : s₀.regs 52 = t₀ := hr52
      rcases copyIntoProg_exec (b + 2) (b + 9) 52 (arr_add_ne b (by decide)) (by decide) (by decide)
          h1_w ht₀_w (s := s₀) hr52_0 (by simp [s₀, hb2_len])
          (by simp [s₀, hb9_len, ht₀_le_m]) hb2_w₀ with
        ⟨s₁, t₁, hex₁, ht₁, hlen₁, hget₁, harr₁, hreg₁⟩
      have hex_ite : Exec w (pass2Prog b) s s₁ (3 + (3 + t₁)) :=
        .ite_false hcond (.seq hex₀ hex₁)
      let τ₁ : Fin G.toComputeDigraph.numEdges → Fin t₀ := fun e =>
        if he : e ∈ edgesOutsideZ G.toComputeDigraph Z then
          ⟨f_tau₀ (filterIdx G.directedEdgesList (edgeOutsideZPred Z) e.1),
            htau₀ _ (filterIdx_lt_numEdges_deleteVertices G Z he)⟩
        else ⟨0, ht₀_pos⟩
      have hpart : IsPartialDigraphBD (max ω 2) G.toComputeDigraph Z
          (edgesOutsideZ G.toComputeDigraph Z) t₀ par₀' τ₁ :=
        isPartialDigraphBD_of_deleteVertices G Z ht₀_pos hpar₀'_lt htau₀ hbd₀'_full
          (fun e he => by simp [τ₁, he])
      have hcard_S : (edgesOutsideZ G.toComputeDigraph Z).card = (G.deleteVertices Z).numEdges :=
        card_edgesOutsideZ_eq G Z
      have hne_S : (edgesOutsideZ G.toComputeDigraph Z).Nonempty :=
        Finset.card_pos.mp (by rw [hcard_S]; omega)
      have hr52_1 : s₁.regs 52 = t₀ := by
        rw [hreg₁ 52 (by decide) (by decide)]; simp [s₀, hr52]
      have hr60_1 : s₁.regs 60 = e₀.1 := by
        rw [hreg₁ 60 (by decide) (by decide)]; simp [s₀]; rfl
      refine ⟨s₁, 3 + (3 + t₁), hex_ite, by omega,
        ⟨edgesOutsideZ G.toComputeDigraph Z, t₀, par₀', τ₁, hpart, ht₀_pos,
         fun _ h => by omega,
         by rw [hcard_S]; omega,
         hr52_1,
         ⟨by rw [hlen₁]; simp [s₀, hb9_len],
          by rw [harr₁ (b + 10) (arr_add_ne b (by decide))]; simp [s₀, hb10_len],
          fun z hz => (hget₁ z hz).trans (hb2_get₀ z hz),
          fun e he => by
            rw [harr₁ (b + 10) (arr_add_ne b (by decide))]
            simp only [s₀, State.writeArr_arrs_ne _ _ _ (arr_add_ne b (by decide) : (b + 10 : Arr) ≠ b + 2)]
            rw [htau_get e he]
            simp [τ₁, he]⟩,
         by rw [harr₁ (b + 7) (arr_add_ne b (by decide))]; simpa [s₀] using hintree,
         by rw [harr₁ (b + 8) (arr_add_ne b (by decide))]; simpa [s₀] using hvert,
         ⟨hr60_1.symm ▸ e₀.2, by
           have heq : (⟨s₁.regs 60, hr60_1.symm ▸ e₀.2⟩ : Fin G.toComputeDigraph.numEdges) = e₀ :=
             Fin.ext hr60_1
           rw [heq]; exact he₀_mem hne_S⟩⟩,
        fun a ha2 _ _ ha9 _ => by rw [harr₁ a ha9]; simp [s₀, ha2],
        fun r hr => by
          rw [hreg₁ r (by intro h; subst h; revert hr; decide)
            (by intro h; subst h; revert hr; decide)]
          simp [s₀]⟩

/-- Inner branch of `pass3Body`: when edge `r_55` is not yet in `S`, finds its unique candidate
endpoint `w` outside `Z` (`r_61`), looks up an incident edge `e_ref ∈ S` (`r_62`, falling back to
`r_60`), splits leaf `τ e_ref`, and marks `r_55` in `S`. -/
def pass3InsertProg (b : Arr) : Cmd :=
  .seq (.assign 56 (.read (b + 5) (.reg 55)))
    (.seq (.assign 57 (.read (b + 6) (.reg 55)))
      (.seq (.assign 58 (.read (b + 1) (.reg 56)))
        (.seq (.ite (.op .eq (.reg 58) (.const 0))
            (.assign 61 (.reg 56))
            (.assign 61 (.reg 57)))
          (.seq (.assign 59 (.read (b + 8) (.reg 61)))
            (.seq (.ite (.op .lt (.const 0) (.reg 59))
                (.assign 62 (.op .sub (.reg 59) (.const 1)))
                (.assign 62 (.reg 60)))
              (.seq (splitLeafWorkProg b)
                (markEdgeInTreeProg b 55)))))))

/-- Loop body of Pass 3 for edge `r_55`: checks `(b + 7)[r_55] == 0` and inserts `r_55` if needed. -/
def pass3Body (b : Arr) : Cmd :=
  .seq (.assign 58 (.read (b + 7) (.reg 55)))
    (.ite (.op .eq (.reg 58) (.const 0))
      (pass3InsertProg b)
      .skip)

/-- Pass 3 of `convertBDProg`: scans all edges `r_55 = 0 .. r_28 - 1` and inserts every remaining
edge into the partial branch-decomposition. -/
def pass3Prog (b : Arr) : Cmd :=
  .seq (.assign 55 (.const 0))
    (forUp 55 (.reg 28) (pass3Body b))

theorem pass3Prog_exec {w n ω : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (b : Arr)
    (hw : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm_w : 2 * G.numEdges + 1 < 2 ^ w)
    {s : State}
    (hr28 : s.regs 28 = G.numEdges)
    (hedges : EdgesExpandedInv G b s)
    (hZ : s.arrs (b + 1) = bitSetList Z)
    (hstate₀ : Pass3StateInv ω G Z b 0 s) :
    ∃ s' time,
      Exec w (pass3Prog b) s s' time ∧
      time ≤ 81 * G.numEdges + 5 ∧
      Pass3StateInv ω G Z b G.numEdges s' ∧
      (∀ a : Arr, a ≠ b + 7 → a ≠ b + 8 → a ≠ b + 9 → a ≠ b + 10 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 52 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hm_eq : G.toComputeDigraph.numEdges = G.numEdges := G.length_directedEdgesList
  let s₁ := s.setReg 55 0
  have hex₀ : Exec w (.assign 55 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (c : ℕ) (st : State) : Prop :=
    st.regs 28 = G.numEdges ∧
    st.regs 55 = c ∧
    Pass3StateInv ω G Z b c st ∧
    (∀ a : Arr, a ≠ b + 7 → a ≠ b + 8 → a ≠ b + 9 → a ≠ b + 10 → st.arrs a = s.arrs a) ∧
    (∀ r : Reg, r < 52 → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₁ := by
    rcases hstate₀ with ⟨S₀, t₀, p₀, τ₀, hpart₀, hp0₀, hlt₀, hsize₀, hr52₀, hpt₀, hin₀, hv₀, he₀₀⟩
    refine ⟨by simp [s₁, hr28], by simp [s₁],
      ⟨S₀, t₀, p₀, τ₀, hpart₀, hp0₀, hlt₀, hsize₀, by simp [s₁, hr52₀],
       by simpa [s₁] using hpt₀, by simpa [s₁] using hin₀, by simpa [s₁] using hv₀,
       by simpa [s₁] using he₀₀⟩,
      fun a _ _ _ _ => by simp [s₁],
      fun r hr => ?_⟩
    have hr55 : r ≠ 55 := by intro h; subst h; revert hr; decide
    simp [s₁, State.setReg_regs_ne _ _ hr55]
  have hLoop :
      ⦃Inv 0⦄[w] forUp 55 (.reg 28) (pass3Body b) ⦃Inv G.numEdges⦄ ≤
        fun _ => 3 + G.numEdges * (7 + 74) := by
    apply Triple.forUp_const Inv G.numEdges 74 h1_w (by omega)
    · intro c _ st ⟨hr28_c, hr55_c, _, _, _⟩
      exact ⟨hr55_c, by simp [Expr.eval, checkWord, hr28_c, show G.numEdges < 2 ^ w by omega]⟩
    · intro c hc st ⟨hr28_c, hr55_c,
        ⟨S, t, p, τ, hpart, hp0, he_lt_c, hsize_c, hr52_c, hpt_c, hintree_c, hvert_c, ⟨he₀_lt, he₀_mem⟩⟩,
        harr_c, hreg_c⟩
      let e_new : Fin G.toComputeDigraph.numEdges := ⟨c, by rw [hm_eq]; exact hc⟩
      have hc_w : c < 2 ^ w := by omega
      have hflag_val : (st.arrs (b + 7)).getD c 0 = if e_new ∈ S then 1 else 0 := hintree_c.2 e_new
      have hflag_w : (if e_new ∈ S then 1 else 0) < 2 ^ w := by split_ifs <;> omega
      -- 1. assign 58 (.read (b + 7) (.reg 55))
      let st₁ := st.setReg 58 (if e_new ∈ S then 1 else 0)
      have hex₁ : Exec w (.assign 58 (.read (b + 7) (.reg 55))) st st₁ 3 :=
        exec_assign_read_getD 58 (b + 7) 55 hr55_c hc_w (by rw [hintree_c.1]; exact hc) hflag_val hflag_w
      by_cases he_mem : e_new ∈ S
      · -- Already in `S`: `r_58 = 1`
        have hcond : (.op .eq (.reg 58) (.const 0) : Expr).eval w st₁ = some 0 := by
          simp [st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, he_mem, h0_w, h1_w]
        have hex_ite : Exec w (.ite (.op .eq (.reg 58) (.const 0)) (pass3InsertProg b) .skip)
            st₁ st₁ (3 + 1) :=
          .ite_false hcond (.skip st₁)
        refine ⟨st₁, 3 + (3 + 1), .seq hex₁ hex_ite, by dsimp only; omega,
          ⟨by simp [st₁, hr28_c],
           by simp [st₁],
           ⟨S, t, p, τ, hpart, hp0,
            fun e' he' => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp he' with hlt | heq
              · exact he_lt_c e' hlt
              · have : e' = e_new := Fin.ext heq
                rwa [this],
            hsize_c,
            by simp [st₁, hr52_c],
            by simpa [st₁] using hpt_c,
            by simpa [st₁] using hintree_c,
            by simpa [st₁] using hvert_c,
            ⟨he₀_lt, he₀_mem⟩⟩,
           fun a ha7 ha8 ha9 ha10 => by simp [st₁, harr_c a ha7 ha8 ha9 ha10],
           fun r hr => ?_⟩,
          by simp [st₁, hr55_c]⟩
        have hr55 : r ≠ 55 := by intro h; subst h; revert hr; decide
        have hr58 : r ≠ 58 := by intro h; subst h; revert hr; decide
        simp [st₁, State.setReg_regs_ne _ _ hr55, State.setReg_regs_ne _ _ hr58, hreg_c r hr]
      · -- Not in `S`: `r_58 = 0`, insert `e_new`
        have hcond : (.op .eq (.reg 58) (.const 0) : Expr).eval w st₁ = some 1 := by
          simp [st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, he_mem, h0_w, h1_w]
        have hcard_lt : S.card < G.numEdges := by
          have hlt : S.card < (Finset.univ : Finset (Fin G.toComputeDigraph.numEdges)).card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
              ⟨Finset.subset_univ S, fun h => he_mem (h.symm ▸ Finset.mem_univ e_new)⟩)
          rw [Finset.card_univ, Fintype.card_fin] at hlt
          exact hlt.trans_eq hm_eq
        have hcard_ins : (insert e_new S).card = S.card + 1 := Finset.card_insert_of_notMem he_mem
        have ht2_le : t + 2 ≤ 2 * G.numEdges + 1 := by omega
        have hedges_st : EdgesExpandedInv G b st := by
          rcases hedges with ⟨ht_e, hh_e, hth_e⟩
          have h5 := harr_c (b + 5) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
            (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
          have h6 := harr_c (b + 6) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
            (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
          exact ⟨by rw [h5, ht_e], by rw [h6, hh_e], fun e' => by rw [h5, h6]; exact hth_e e'⟩
        have hZ_st : st.arrs (b + 1) = bitSetList Z := by
          rw [harr_c (b + 1) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
            (arr_add_ne b (by decide)) (arr_add_ne b (by decide)), hZ]
        let u := G.toComputeDigraph.tail e_new
        let v := G.toComputeDigraph.head e_new
        have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
        have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
        -- 1. assign 56 (.read (b + 5) (.reg 55))
        let st₂ := st₁.setReg 56 u.1
        have hex₂ : Exec w (.assign 56 (.read (b + 5) (.reg 55))) st₁ st₂ 3 :=
          exec_assign_read_getD 56 (b + 5) 55 (by simp [st₁, hr55_c]) hc_w
            (by simp [st₁, hedges_st.1, hc]) (by simp [st₁]; exact (hedges_st.2.2 e_new).1) hu_w
        -- 2. assign 57 (.read (b + 6) (.reg 55))
        let st₃ := st₂.setReg 57 v.1
        have hex₃ : Exec w (.assign 57 (.read (b + 6) (.reg 55))) st₂ st₃ 3 :=
          exec_assign_read_getD 57 (b + 6) 55 (by simp [st₂, st₁, hr55_c]) hc_w
            (by simp [st₂, st₁, hedges_st.2.1, hc]) (by simp [st₂, st₁]; exact (hedges_st.2.2 e_new).2) hv_w
        -- 3. assign 58 (.read (b + 1) (.reg 56))
        let zu := if u ∈ Z then 1 else 0
        have hzu_w : zu < 2 ^ w := by dsimp [zu]; split_ifs <;> omega
        let st₄ := st₃.setReg 58 zu
        have hex₄ : Exec w (.assign 58 (.read (b + 1) (.reg 56))) st₃ st₄ 3 :=
          exec_assign_read_getD 58 (b + 1) 56 (by simp [st₃, st₂]) hu_w
            (by simp [st₃, st₂, st₁, hZ_st, u.2])
            (by simp [st₃, st₂, st₁, hZ_st, zu]) hzu_w
        -- 4. ite (.op .eq (.reg 58) (.const 0)) (.assign 61 (.reg 56)) (.assign 61 (.reg 57))
        let w_vert : Fin n := if u ∉ Z then u else v
        have hw_vert_w : w_vert.1 < 2 ^ w := Nat.lt_trans w_vert.2 hn_w
        let st₅ := st₄.setReg 61 w_vert.1
        have hex₅ : Exec w (.ite (.op .eq (.reg 58) (.const 0))
            (.assign 61 (.reg 56)) (.assign 61 (.reg 57))) st₄ st₅ 5 := by
          by_cases huZ : u ∉ Z
          · have hzu0 : zu = 0 := by simp [zu, huZ]
            have hc_z : (.op .eq (.reg 58) (.const 0) : Expr).eval w st₄ = some 1 := by
              simp [st₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hzu0, h0_w, h1_w]
            have hw_eq : w_vert.1 = u.1 := by simp [w_vert, huZ]
            rw [show st₅ = st₄.setReg 61 u.1 by simp [st₅, hw_eq]]
            exact .ite_true hc_z (by decide)
              (.assign (by simp [st₄, st₃, st₂, Expr.eval, checkWord, hu_w]))
          · have huZ' : u ∈ Z := Decidable.not_not.mp huZ
            have hzu1 : zu = 1 := by simp [zu, huZ']
            have hc_z : (.op .eq (.reg 58) (.const 0) : Expr).eval w st₄ = some 0 := by
              simp [st₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hzu1, h0_w, h1_w]
            have hw_eq : w_vert.1 = v.1 := by simp [w_vert, huZ']
            rw [show st₅ = st₄.setReg 61 v.1 by simp [st₅, hw_eq]]
            exact .ite_false hc_z
              (.assign (by simp [st₄, st₃, Expr.eval, checkWord, hv_w]))
        -- 5. assign 59 (.read (b + 8) (.reg 61))
        let e_base : Fin G.toComputeDigraph.numEdges := ⟨st.regs 60, he₀_lt⟩
        have hbase_mem : e_base ∈ S := he₀_mem
        rcases vertEdgeInv_lookup G hvert_c hbase_mem w_vert with
          ⟨href_lt, href_mem, href_inc⟩
        let c_w := (st.arrs (b + 8)).getD w_vert.1 0
        let e_ref_val := if 0 < c_w then c_w - 1 else e_base.1
        let e_ref : Fin G.toComputeDigraph.numEdges := ⟨e_ref_val, href_lt⟩
        have hcw_le : c_w ≤ G.numEdges := by
          rcases hvert_c.2 w_vert with ⟨hc0, _⟩ | ⟨e, _, hc_eq, _⟩
          · dsimp [c_w]; omega
          · have : e.1 < G.numEdges := by rw [← hm_eq]; exact e.2
            dsimp [c_w]; omega
        have hcw_w : c_w < 2 ^ w := by omega
        let st₆ := st₅.setReg 59 c_w
        have hex₆ : Exec w (.assign 59 (.read (b + 8) (.reg 61))) st₅ st₆ 3 :=
          exec_assign_read_getD 59 (b + 8) 61 (by simp [st₅]) hw_vert_w
            (by simp [st₅, st₄, st₃, st₂, st₁, hvert_c.1, w_vert.2])
            (by simp [st₅, st₄, st₃, st₂, st₁, c_w]) hcw_w
        -- 6. ite (.op .lt (.const 0) (.reg 59)) (.assign 62 (.op .sub (.reg 59) (.const 1))) (.assign 62 (.reg 60))
        let st₇ := st₆.setReg 62 e_ref.1
        have hbase_w : st.regs 60 < 2 ^ w := by
          have : st.regs 60 < G.numEdges := by rw [← hm_eq]; exact he₀_lt
          omega
        have hex₇ : ∃ t₇,
            Exec w (.ite (.op .lt (.const 0) (.reg 59))
              (.assign 62 (.op .sub (.reg 59) (.const 1)))
              (.assign 62 (.reg 60))) st₆ st₇ t₇ ∧
            t₇ ≤ 7 := by
          by_cases hcw_pos : 0 < c_w
          · have hc_pos : (.op .lt (.const 0) (.reg 59) : Expr).eval w st₆ = some 1 := by
              simp [st₆, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcw_pos, h0_w, h1_w, hcw_w]
            have href_eq : e_ref.1 = c_w - 1 := by simp [e_ref, e_ref_val, hcw_pos]
            have hcw1_w : c_w - 1 < 2 ^ w := by omega
            refine ⟨3 + 4, ?_, by omega⟩
            rw [show st₇ = st₆.setReg 62 (c_w - 1) by simp [st₇, href_eq]]
            exact .ite_true hc_pos (by decide)
              (.assign (by simp [st₆, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcw_w, h1_w, hcw1_w]))
          · have hc_zero : (.op .lt (.const 0) (.reg 59) : Expr).eval w st₆ = some 0 := by
              simp [st₆, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcw_pos, h0_w, hcw_w]
            have href_eq : e_ref.1 = st.regs 60 := by simp [e_ref, e_ref_val, hcw_pos, e_base]
            refine ⟨3 + 2, ?_, by omega⟩
            rw [show st₇ = st₆.setReg 62 (st.regs 60) by simp [st₇, href_eq]]
            exact .ite_false hc_zero
              (.assign (by simp [st₆, st₅, st₄, st₃, st₂, st₁, Expr.eval, checkWord, hbase_w]))
        rcases hex₇ with ⟨t₇, hex₇, ht₇⟩
        -- 7. splitLeafWorkProg b
        rcases splitLeafWorkProg_exec G b hw hm_w ht2_le
            he_mem href_mem (s := st₇)
            (by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, hr52_c])
            (by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, hr55_c]; rfl)
            rfl
            (by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hpt_c) with
          ⟨st₈, t₈, hex₈, ht₈, hr52_8, hpt_8, harr₈, hreg₈⟩
        -- 8. markEdgeInTreeProg b 55
        have hedges_8 : EdgesExpandedInv G b st₈ := by
          rcases hedges_st with ⟨ht_e, hh_e, hth_e⟩
          have h5 := harr₈ (b + 5) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
          have h6 := harr₈ (b + 6) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
          exact ⟨by simp [h5, st₇, st₆, st₅, st₄, st₃, st₂, st₁, ht_e],
            by simp [h6, st₇, st₆, st₅, st₄, st₃, st₂, st₁, hh_e],
            fun e' => by simpa [h5, h6, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hth_e e'⟩
        have hr55_8 : st₈.regs 55 = e_new.1 := by
          rw [hreg₈ 55 (by decide) (by decide) (by decide)]
          simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, hr55_c]; rfl
        have hintree_8 : InTreeInv G S (st₈.arrs (b + 7)) := by
          rw [harr₈ (b + 7) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))]
          simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hintree_c
        have hvert_8 : VertEdgeInv G S (st₈.arrs (b + 8)) := by
          rw [harr₈ (b + 8) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))]
          simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hvert_c
        rcases markEdgeInTreeProg_exec G b 55 (by decide) (by decide) (by decide)
            h1_w hn_w (by omega) e_new hr55_8 hedges_8 hintree_8 hvert_8 with
          ⟨st₉, t₉, hex₉, ht₉, hintree₉, hvert₉, harr₉, hreg₉⟩
        have hex_ins : Exec w (pass3InsertProg b) st₁ st₉
            (3 + (3 + (3 + (5 + (3 + (t₇ + (t₈ + t₉))))))) :=
          .seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ hex₉))))))
        have hex_ite : Exec w (.ite (.op .eq (.reg 58) (.const 0)) (pass3InsertProg b) .skip)
            st₁ st₉ (3 + (3 + (3 + (3 + (5 + (3 + (t₇ + (t₈ + t₉)))))))) :=
          .ite_true hcond (by decide) hex_ins
        let p' := splitLeafParent p t (τ e_ref).1
        let τ' : Fin G.toComputeDigraph.numEdges → Fin (t + 2) := fun e =>
          if e = e_new then ⟨t, by omega⟩
          else if e = e_ref then ⟨t + 1, by omega⟩
          else ⟨(τ e).1, Nat.lt_trans (τ e).2 (by omega)⟩
        have hpart' : IsPartialDigraphBD (max ω 2) G.toComputeDigraph Z (insert e_new S)
            (t + 2) p' τ' :=
          hpart.splitLeaf he_mem href_mem (fun _ hex => href_inc hex)
        have hp0' : p' 0 < t + 2 := by
          dsimp [p', splitLeafParent]
          have := hpart.ht
          split_ifs <;> omega
        have hr52_9 : st₉.regs 52 = t + 2 := by
          rw [hreg₉ 52 (by decide) (by decide) (by decide)]; exact hr52_8
        have hr60_9 : st₉.regs 60 = st.regs 60 := by
          rw [hreg₉ 60 (by decide) (by decide) (by decide),
              hreg₈ 60 (by decide) (by decide) (by decide)]
          simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁]
        have hpt_9 : ParTauInv G (insert e_new S) (t + 2) p' τ'
            (st₉.arrs (b + 9)) (st₉.arrs (b + 10)) := by
          rw [harr₉ (b + 9) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)),
              harr₉ (b + 10) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))]
          exact hpt_8
        refine ⟨st₉, 3 + (3 + (3 + (3 + (3 + (5 + (3 + (t₇ + (t₈ + t₉)))))))),
          .seq hex₁ hex_ite, by dsimp only; omega,
          ⟨?_, by simp, ?_, ?_, ?_⟩,
          by rw [hreg₉ 55 (by decide) (by decide) (by decide), hr55_8]⟩
        · rw [State.setReg_regs_ne _ _ (by decide),
              hreg₉ 28 (by decide) (by decide) (by decide),
              hreg₈ 28 (by decide) (by decide) (by decide)]
          simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, hr28_c]
        · have h60 : (st₉.setReg 55 (c + 1)).regs 60 = e_base.1 := by simp [hr60_9, e_base]
          have he₀_lt9 : (st₉.setReg 55 (c + 1)).regs 60 < G.toComputeDigraph.numEdges := by
            rw [h60]; exact e_base.2
          refine ⟨insert e_new S, t + 2, p', τ',
            hpart', hp0',
            fun e' he' => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp he' with hlt | heq
              · exact Finset.mem_insert_of_mem (he_lt_c e' hlt)
              · have : e' = e_new := Fin.ext heq
                rw [this]
                exact Finset.mem_insert_self e_new S,
            by rw [hcard_ins]; omega,
            by simp [hr52_9],
            by simpa using hpt_9,
            by simpa using hintree₉,
            by simpa using hvert₉,
            ⟨he₀_lt9, ?_⟩⟩
          have heq : (⟨(st₉.setReg 55 (c + 1)).regs 60, he₀_lt9⟩ :
              Fin G.toComputeDigraph.numEdges) = e_base :=
            Fin.ext h60
          rw [heq]
          exact Finset.mem_insert_of_mem hbase_mem
        · intro a ha7 ha8 ha9 ha10
          rw [State.setReg_arrs, harr₉ a ha7 ha8, harr₈ a ha9 ha10]
          simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, harr_c a ha7 ha8 ha9 ha10]
        · intro r hr
          have hr52 : r ≠ 52 := by intro h; subst h; revert hr; decide
          have hr55 : r ≠ 55 := by intro h; subst h; revert hr; decide
          have hr56 : r ≠ 56 := by intro h; subst h; revert hr; decide
          have hr57 : r ≠ 57 := by intro h; subst h; revert hr; decide
          have hr58 : r ≠ 58 := by intro h; subst h; revert hr; decide
          have hr59 : r ≠ 59 := by intro h; subst h; revert hr; decide
          have hr61 : r ≠ 61 := by intro h; subst h; revert hr; decide
          have hr62 : r ≠ 62 := by intro h; subst h; revert hr; decide
          have hr63 : r ≠ 63 := by intro h; subst h; revert hr; decide
          rw [State.setReg_regs_ne _ _ hr55, hreg₉ r hr56 hr57 hr59, hreg₈ r hr52 hr59 hr63]
          simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁,
            State.setReg_regs_ne _ _ hr62, State.setReg_regs_ne _ _ hr59,
            State.setReg_regs_ne _ _ hr61, State.setReg_regs_ne _ _ hr58,
            State.setReg_regs_ne _ _ hr57, State.setReg_regs_ne _ _ hr56,
            hreg_c r hr]
  rcases hLoop s₁ hInv₀ with ⟨s₂, t₂, hex₂, ht₂, _, _, hstate₂, harr₂, hreg₂⟩
  dsimp only at ht₂
  exact ⟨s₂, 2 + t₂, .seq hex₀ hex₂, by omega, hstate₂, harr₂, hreg₂⟩

theorem eq_ofFn_of_getD_eq {k : ℕ} {arr : List ℕ} {f : ℕ → ℕ}
    (hlen : arr.length = k) (hget : ∀ i < k, arr.getD i 0 = f i) :
    arr = List.ofFn (fun i : Fin k => f i.1) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    have hi : i < k := by simpa [hlen] using hi1
    have h1 : arr.getD i 0 = arr[i]'hi1 := by
      simp [List.getD, List.getElem?_eq_getElem hi1]
    rw [← h1, hget i hi, List.getElem_ofFn]

theorem getD_ofFn {k : ℕ} (f : Fin k → ℕ) {i : ℕ} (hi : i < k) :
    (List.ofFn f).getD i 0 = f ⟨i, hi⟩ := by
  have hlen : i < (List.ofFn f).length := by simp [hi]
  simp [List.getD, List.getElem?_eq_getElem hlen]

/-- Trivial branch of `convertBDProg` when `G.numEdges < 2`: outputs the 1-vertex tree `t = 1`. -/
def convertBDSmallProg (b : Arr) : Cmd :=
  .seq (.assign 52 (.const 1))
    (.seq (.alloc (b + 2) (.const 1))
      (.alloc (b + 3) (.reg 28)))

/-- Main branch of `convertBDProg` when `2 ≤ G.numEdges`: allocates work arrays `b + 7 .. b + 10`,
runs `pass1Prog`, `pass2Prog`, `pass3Prog`, and copies the resulting `par` and `tau` into `b + 2`
and `b + 3`. -/
def convertBDLargeProg (b : Arr) : Cmd :=
  .seq (.alloc (b + 7) (.reg 28))
    (.seq (.alloc (b + 8) (.reg 26))
      (.seq (.assign 55 (.op .add (.op .mul (.const 2) (.reg 28)) (.const 1)))
        (.seq (.alloc (b + 9) (.reg 55))
          (.seq (.alloc (b + 10) (.reg 28))
            (.seq (pass1Prog b)
              (.seq (pass2Prog b)
                (.seq (pass3Prog b)
                  (.seq (copyPrefixProg (b + 9) (b + 2) 52)
                    (copyPrefixProg (b + 10) (b + 3) 28)))))))))

private theorem convertBD_small_time_bound {n m t₁ : ℕ}
    (ht₁ : t₁ ≤ 135 * (n + m + 1) ^ 2) :
    t₁ + (3 + (2 + ((1 + 1) + (1 + m)))) ≤ 350 * (n + m + 1) ^ 2 := by
  have hsq : (n + m + 1) ^ 2 = n * n + m * m + 2 * (n * m) + 2 * n + 2 * m + 1 := by ring
  omega

private theorem convertBD_large_time_bound {n m t₁ t_p1 t_p2 t_p3 t_c1 t_c2 t : ℕ}
    (ht₁ : t₁ ≤ 135 * (n + m + 1) ^ 2)
    (ht_p1 : t_p1 ≤ 58 * m + 9)
    (ht_p2 : t_p2 ≤ 26 * m + 65)
    (ht_p3 : t_p3 ≤ 81 * m + 5)
    (ht_c1 : t_c1 ≤ 14 * t + 6)
    (ht_c2 : t_c2 ≤ 14 * m + 6)
    (ht_le : t ≤ 2 * m + 1) :
    t₁ + (3 + ((1 + m) + ((1 + n) + (6 + ((1 + (2 * m + 1)) +
      ((1 + m) + (t_p1 + (t_p2 + (t_p3 + (t_c1 + t_c2)))))))))) ≤
      350 * (n + m + 1) ^ 2 := by
  have hsq : (n + m + 1) ^ 2 = n * n + m * m + 2 * (n * m) + 2 * n + 2 * m + 1 := by ring
  omega

/-- Complete Word RAM program for Step (2) of GM XIII Algorithm (10.5):
converts a written-out branch-decomposition of `G \ Z` of width `≤ ω` in `(r_52, b + 2, b + 3)`
into a written-out branch-decomposition of `G` of width `≤ max ω 2 + ξ` in `(r_52, b + 2, b + 3)`. -/
def convertBDProg (b : Arr) : Cmd :=
  .seq (expandEdgesProg b (b + 4) (b + 5) (b + 6))
    (.ite (.op .lt (.reg 28) (.const 2))
      (convertBDSmallProg b)
      (convertBDLargeProg b))

theorem convertBDProg_exec {w n t₀ ω ξ : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (b : Arr)
    (par₀ f_tau₀ : ℕ → ℕ)
    (hZ_card : Z.card ≤ ξ)
    (hw : 3 < 2 ^ w)
    (hnn_w : n * n < 2 ^ w)
    (henc_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm_w : 2 * G.numEdges + 1 < 2 ^ w)
    (hbd₀ : IsWrittenDigraphBD ω (G.deleteVertices Z).toComputeDigraph t₀ par₀ f_tau₀)
    {s : State}
    (hG : s.arrs b = G.enc)
    (hZ : s.arrs (b + 1) = bitSetList Z)
    (hr26 : s.regs 26 = n)
    (hr27 : s.regs 27 = G.numActivePairs)
    (hr28 : s.regs 28 = G.numEdges)
    (hr52 : s.regs 52 = t₀)
    (hb2 : s.arrs (b + 2) = List.ofFn (fun z : Fin t₀ => par₀ z.1))
    (hb3 : s.arrs (b + 3) =
      List.ofFn (fun e : Fin (G.deleteVertices Z).toComputeDigraph.numEdges => f_tau₀ e.1)) :
    ∃ s' time t par f_tau,
      Exec w (convertBDProg b) s s' time ∧
      time ≤ 350 * (n + G.numEdges + 1) ^ 2 ∧
      s'.regs 52 = t ∧
      s'.arrs (b + 2) = List.ofFn (fun z : Fin t => par z.1) ∧
      s'.arrs (b + 3) = List.ofFn (fun e : Fin G.toComputeDigraph.numEdges => f_tau e.1) ∧
      s'.arrs (b + 5) =
        List.ofFn (fun e : Fin G.toComputeDigraph.numEdges => (G.toComputeDigraph.tail e).1) ∧
      s'.arrs (b + 6) =
        List.ofFn (fun e : Fin G.toComputeDigraph.numEdges => (G.toComputeDigraph.head e).1) ∧
      IsWrittenDigraphBD (max ω 2 + ξ) G.toComputeDigraph t par f_tau ∧
      (∀ a : Arr, a < b + 2 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < 52 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · omega
    · nlinarith
  have hm_eq : G.toComputeDigraph.numEdges = G.numEdges := G.length_directedEdgesList
  have hm_del_eq : (G.deleteVertices Z).toComputeDigraph.numEdges = (G.deleteVertices Z).numEdges :=
    (G.deleteVertices Z).length_directedEdgesList
  -- 1. expandEdgesProg b (b + 4) (b + 5) (b + 6)
  rcases expandEdgesProg_exec G b (b + 4) (b + 5) (b + 6)
      (arr_ne_add_right b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
      (arr_add_ne b (by decide))
      hw hnn_w henc_w (by omega) hG hr26 hr27 hr28 with
    ⟨s₁, t₁, hex₁, ht₁, ⟨ht_len₁, hh_len₁, hth₁⟩, harr₁, hreg₁⟩
  have hedges₁ : EdgesExpandedInv G b s₁ := by
    refine ⟨ht_len₁, hh_len₁, fun e => ?_⟩
    have he_m : e.1 < G.numEdges := by rw [← hm_eq]; exact e.2
    have hlt_t : e.1 < (s₁.arrs (b + 5)).length := by rw [ht_len₁]; exact he_m
    have hlt_h : e.1 < (s₁.arrs (b + 6)).length := by rw [hh_len₁]; exact he_m
    have h1 : (s₁.arrs (b + 5)).getD e.1 0 = (s₁.arrs (b + 5))[e.1]'hlt_t := by
      simp [List.getD, List.getElem?_eq_getElem hlt_t]
    have h2 : (s₁.arrs (b + 6)).getD e.1 0 = (s₁.arrs (b + 6))[e.1]'hlt_h := by
      simp [List.getD, List.getElem?_eq_getElem hlt_h]
    rw [h1, h2]
    exact hth₁ e
  have hb5_1 : s₁.arrs (b + 5) =
      List.ofFn (fun e : Fin G.toComputeDigraph.numEdges => (G.toComputeDigraph.tail e).1) := by
    apply List.ext_getElem (by simp [ht_len₁])
    intro i hi1 hi2
    rw [List.getElem_ofFn]
    exact (hth₁ ⟨i, by simpa using hi2⟩).1
  have hb6_1 : s₁.arrs (b + 6) =
      List.ofFn (fun e : Fin G.toComputeDigraph.numEdges => (G.toComputeDigraph.head e).1) := by
    apply List.ext_getElem (by simp [hh_len₁])
    intro i hi1 hi2
    rw [List.getElem_ofFn]
    exact (hth₁ ⟨i, by simpa using hi2⟩).2
  have hr26_1 : s₁.regs 26 = n := (hreg₁ 26 (by decide)).trans hr26
  have hr28_1 : s₁.regs 28 = G.numEdges := (hreg₁ 28 (by decide)).trans hr28
  have hr52_1 : s₁.regs 52 = t₀ := (hreg₁ 52 (by decide)).trans hr52
  -- 2. Branch on `G.numEdges < 2`
  by_cases hm_lt2 : G.numEdges < 2
  · -- Small case: `G.numEdges < 2`
    have hcond : (.op .lt (.reg 28) (.const 2) : Expr).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr28_1, hm_lt2, h1_w, h2_w,
        show G.numEdges < 2 ^ w by omega]
    let s₂ := s₁.setReg 52 1
    have hex₂ : Exec w (.assign 52 (.const 1)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, h1_w])
    let s₃ := s₂.setArr (b + 2) (List.replicate 1 0)
    have hex₃ : Exec w (.alloc (b + 2) (.const 1)) s₂ s₃ (1 + 1) :=
      .alloc (by simp [Expr.eval, checkWord, h1_w])
    let s₄ := s₃.setArr (b + 3) (List.replicate G.numEdges 0)
    have hex₄ : Exec w (.alloc (b + 3) (.reg 28)) s₃ s₄ (1 + G.numEdges) :=
      .alloc (by simp [s₃, s₂, Expr.eval, checkWord, hr28_1, show G.numEdges < 2 ^ w by omega])
    have hex_small : Exec w (convertBDSmallProg b) s₁ s₄ (2 + ((1 + 1) + (1 + G.numEdges))) :=
      .seq hex₂ (.seq hex₃ hex₄)
    have hex_ite : Exec w (.ite (.op .lt (.reg 28) (.const 2)) (convertBDSmallProg b) (convertBDLargeProg b))
        s₁ s₄ (3 + (2 + ((1 + 1) + (1 + G.numEdges)))) :=
      .ite_true hcond (by decide) hex_small
    refine ⟨s₄, t₁ + (3 + (2 + ((1 + 1) + (1 + G.numEdges)))), 1, fun _ => 0, fun _ => 0,
      .seq hex₁ hex_ite, convertBD_small_time_bound ht₁,
      by simp [s₄, s₃, s₂],
      by simp [s₄, s₃],
      by simp [s₄],
      by simp [s₄, s₃, s₂, hb5_1],
      by simp [s₄, s₃, s₂, hb6_1],
      ⟨by omega, by omega, fun _ h1 h2 => by omega, fun _ _ => Nat.zero_lt_one,
        Or.inl (by rw [hm_eq]; omega)⟩,
      fun a ha => by
        have ha2 := arr_ne_add_of_lt ha 2 (by decide)
        have ha3 := arr_ne_add_of_lt ha 3 (by decide)
        have ha4 := arr_ne_add_of_lt ha 4 (by decide)
        have ha5 := arr_ne_add_of_lt ha 5 (by decide)
        have ha6 := arr_ne_add_of_lt ha 6 (by decide)
        simp [s₄, s₃, s₂, ha2, ha3, harr₁ a ha4 ha5 ha6],
      fun r hr => by
        have hr52' := reg_ne_of_lt_52 hr 52 (by decide)
        have hr53 := reg_lt_53_of_lt_52 hr
        simp [s₄, s₃, s₂, State.setReg_regs_ne _ _ hr52', hreg₁ r hr53]⟩
  · -- Large case: `2 ≤ G.numEdges`
    have hm_ge2 : 2 ≤ G.numEdges := by omega
    have hcond : (.op .lt (.reg 28) (.const 2) : Expr).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr28_1, hm_lt2, h0_w, h2_w,
        show G.numEdges < 2 ^ w by omega]
    -- Allocate b + 7, b + 8, b + 9, b + 10
    let s₂ := s₁.setArr (b + 7) (List.replicate G.numEdges 0)
    have hex₂ : Exec w (.alloc (b + 7) (.reg 28)) s₁ s₂ (1 + G.numEdges) :=
      .alloc (by simp [Expr.eval, checkWord, hr28_1, show G.numEdges < 2 ^ w by omega])
    let s₃ := s₂.setArr (b + 8) (List.replicate n 0)
    have hex₃ : Exec w (.alloc (b + 8) (.reg 26)) s₂ s₃ (1 + n) :=
      .alloc (by simp [s₂, Expr.eval, checkWord, hr26_1, hn_w])
    let s₄ := s₃.setReg 55 (2 * G.numEdges + 1)
    have hex₄ : Exec w (.assign 55 (.op .add (.op .mul (.const 2) (.reg 28)) (.const 1))) s₃ s₄ 6 :=
      .assign (by simp [s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr28_1, h2_w, h1_w, hm_w, show G.numEdges < 2 ^ w by omega,
        show 2 * G.numEdges < 2 ^ w by omega])
    let s₅ := s₄.setArr (b + 9) (List.replicate (2 * G.numEdges + 1) 0)
    have hex₅ : Exec w (.alloc (b + 9) (.reg 55)) s₄ s₅ (1 + (2 * G.numEdges + 1)) :=
      .alloc (by simp [s₄, Expr.eval, checkWord, hm_w])
    let s₆ := s₅.setArr (b + 10) (List.replicate G.numEdges 0)
    have hex₆ : Exec w (.alloc (b + 10) (.reg 28)) s₅ s₆ (1 + G.numEdges) :=
      .alloc (by simp [s₅, s₄, s₃, s₂, Expr.eval, checkWord, hr28_1, show G.numEdges < 2 ^ w by omega])
    -- Establish preconditions for pass1Prog_exec on s₆
    have hedges₆ : EdgesExpandedInv G b s₆ := by
      rcases hedges₁ with ⟨ht, hh, hth⟩
      exact ⟨by simp [s₆, s₅, s₄, s₃, s₂, ht],
        by simp [s₆, s₅, s₄, s₃, s₂, hh],
        fun e => by simpa [s₆, s₅, s₄, s₃, s₂] using hth e⟩
    have hZ₆ : s₆.arrs (b + 1) = bitSetList Z := by
      simp [s₆, s₅, s₄, s₃, s₂,
        harr₁ (b + 1) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)), hZ]
    have hb2_6 : s₆.arrs (b + 2) = List.ofFn (fun z : Fin t₀ => par₀ z.1) := by
      simp [s₆, s₅, s₄, s₃, s₂,
        harr₁ (b + 2) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)), hb2]
    have hb3_6 : s₆.arrs (b + 3) =
        List.ofFn (fun e : Fin (G.deleteVertices Z).toComputeDigraph.numEdges => f_tau₀ e.1) := by
      simp [s₆, s₅, s₄, s₃, s₂,
        harr₁ (b + 3) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)), hb3]
    have hb3_len₆ : (s₆.arrs (b + 3)).length = (G.deleteVertices Z).numEdges := by
      rw [hb3_6, List.length_ofFn, hm_del_eq]
    have hb3_get₆ : ∀ j < (G.deleteVertices Z).numEdges, (s₆.arrs (b + 3)).getD j 0 = f_tau₀ j := by
      intro j hj
      rw [hb3_6, getD_ofFn _ (by rw [hm_del_eq]; exact hj)]
    have ht₀_w : t₀ < 2 ^ w := by
      have := hbd₀.2.1
      have := G.numEdges_deleteVertices_le Z
      rw [hm_del_eq] at *
      omega
    have htau₀_lt : ∀ j < (G.deleteVertices Z).numEdges, f_tau₀ j < t₀ := by
      intro j hj
      exact hbd₀.2.2.2.1 j (by rw [hm_del_eq]; exact hj)
    rcases pass1Prog_exec G Z b f_tau₀ h2_w hn_w (by omega) ht₀_w htau₀_lt (by omega) (s := s₆)
        (by simp [s₆, s₅, s₄, s₃, s₂, hr28_1]) hedges₆ hZ₆ hb3_len₆ hb3_get₆
        (by simp [s₆, s₅, s₄, s₃, s₂])
        (by simp [s₆, s₅, s₄, s₃, s₂])
        (by simp [s₆]) with
      ⟨s₇, t_p1, hex_p1, ht_p1, hr53_7, hintree_7, hvert_7, hb10_len_7, htau_get_7, he₀_7, harr_7, hreg_7⟩
    -- Establish preconditions for pass2Prog_exec on s₇
    have hedges₇ : EdgesExpandedInv G b s₇ := by
      rcases hedges₆ with ⟨ht, hh, hth⟩
      have h5 := harr_7 (b + 5) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
      have h6 := harr_7 (b + 6) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
      exact ⟨by rw [h5, ht], by rw [h6, hh], fun e => by rw [h5, h6]; exact hth e⟩
    have hb2_7 : s₇.arrs (b + 2) = List.ofFn (fun z : Fin t₀ => par₀ z.1) := by
      rw [harr_7 (b + 2) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)), hb2_6]
    have hb2_len₇ : (s₇.arrs (b + 2)).length = t₀ := by rw [hb2_7, List.length_ofFn]
    have hb2_get₇ : ∀ z < t₀, (s₇.arrs (b + 2)).getD z 0 = par₀ z := by
      intro z hz; rw [hb2_7, getD_ofFn _ hz]
    have hb9_len₇ : (s₇.arrs (b + 9)).length = 2 * G.numEdges + 1 := by
      rw [harr_7 (b + 9) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))]
      simp [s₆, s₅]
    have hr52_7 : s₇.regs 52 = t₀ := by
      rw [hreg_7 52 (by decide)]; simp [s₆, s₅, s₄, s₃, s₂, hr52_1]
    rcases pass2Prog_exec G Z b par₀ f_tau₀ h2_w hn_w hm_w hm_ge2 hbd₀
        hr52_7 hr53_7 hedges₇ hb2_len₇ hb2_get₇ hb9_len₇ hb10_len_7 htau_get_7
        hintree_7 hvert_7 he₀_7 with
      ⟨s₈, t_p2, hex_p2, ht_p2, hstate_8, harr_8, hreg_8⟩
    -- Establish preconditions for pass3Prog_exec on s₈
    have hedges₈ : EdgesExpandedInv G b s₈ := by
      rcases hedges₇ with ⟨ht, hh, hth⟩
      have h5 := harr_8 (b + 5) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
        (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
      have h6 := harr_8 (b + 6) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
        (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
      exact ⟨by rw [h5, ht], by rw [h6, hh], fun e => by rw [h5, h6]; exact hth e⟩
    have hZ₈ : s₈.arrs (b + 1) = bitSetList Z := by
      rw [harr_8 (b + 1) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
          (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)),
          harr_7 (b + 1) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)), hZ₆]
    have hr28_8 : s₈.regs 28 = G.numEdges := by
      rw [hreg_8 28 (by decide), hreg_7 28 (by decide)]
      simp [s₆, s₅, s₄, s₃, s₂, hr28_1]
    rcases pass3Prog_exec G Z b h2_w hn_w hm_w hr28_8 hedges₈ hZ₈ hstate_8 with
      ⟨s₉, t_p3, hex_p3, ht_p3, hstate_9, harr_9, hreg_9⟩
    -- Extract the completed branch-decomposition from hstate_9
    rcases hstate_9 with ⟨S, t, p, τ, hpart, hp0, he_all, hsize_9, hr52_9, hpt_9, _, _, _⟩
    have hS_univ : S = Finset.univ := by
      ext e
      simp only [Finset.mem_univ, iff_true]
      exact he_all e (by rw [← hm_eq]; exact e.2)
    subst hS_univ
    have hcard_univ : (Finset.univ : Finset (Fin G.toComputeDigraph.numEdges)).card = G.numEdges := by
      rw [Finset.card_univ, Fintype.card_fin, hm_eq]
    have ht_le : t ≤ 2 * G.numEdges + 1 := by rw [hcard_univ] at hsize_9; omega
    have ht_w : t < 2 ^ w := by omega
    rcases hpt_9 with ⟨hb9_len₉, hb10_len₉, hb9_get₉, hb10_get₉⟩
    have hb9_w : ∀ z < t, (s₉.arrs (b + 9)).getD z 0 < 2 ^ w := by
      intro z hz
      rw [hb9_get₉ z hz]
      by_cases hz0 : z = 0
      · subst hz0; omega
      · have := hpart.hp z (by omega) hz
        omega
    -- Copy prefix of b + 9 to b + 2
    rcases copyPrefixProg_exec (b + 9) (b + 2) 52 (arr_add_ne b (by decide)) (by decide) (by decide)
        h1_w ht_w hr52_9 (by rw [hb9_len₉]; exact ht_le) hb9_w with
      ⟨s₁₀, t_c1, hex_c1, ht_c1, hb2_len₁₀, hb2_get₁₀, harr₁₀, hreg₁₀⟩
    -- Copy prefix of b + 10 to b + 3
    have hr28_10 : s₁₀.regs 28 = G.numEdges := by
      rw [hreg₁₀ 28 (by decide) (by decide), hreg_9 28 (by decide)]; exact hr28_8
    have hb10_len₁₀ : G.numEdges ≤ (s₁₀.arrs (b + 10)).length := by
      rw [harr₁₀ (b + 10) (arr_add_ne b (by decide)), hb10_len₉]
    have hb10_w : ∀ j < G.numEdges, (s₁₀.arrs (b + 10)).getD j 0 < 2 ^ w := by
      intro j hj
      rw [harr₁₀ (b + 10) (arr_add_ne b (by decide))]
      let e : Fin G.toComputeDigraph.numEdges := ⟨j, by rw [hm_eq]; exact hj⟩
      rw [hb10_get₉ e (Finset.mem_univ e)]
      exact Nat.lt_trans (τ e).2 ht_w
    rcases copyPrefixProg_exec (b + 10) (b + 3) 28 (arr_add_ne b (by decide)) (by decide) (by decide)
        h1_w (by omega) hr28_10 hb10_len₁₀ hb10_w with
      ⟨s₁₁, t_c2, hex_c2, ht_c2, hb3_len₁₁, hb3_get₁₁, harr₁₁, hreg₁₁⟩
    have hex_large : Exec w (convertBDLargeProg b) s₁ s₁₁
        ((1 + G.numEdges) + ((1 + n) + (6 + ((1 + (2 * G.numEdges + 1)) +
          ((1 + G.numEdges) + (t_p1 + (t_p2 + (t_p3 + (t_c1 + t_c2))))))))) :=
      .seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
        (.seq hex_p1 (.seq hex_p2 (.seq hex_p3 (.seq hex_c1 hex_c2))))))))
    have hex_ite : Exec w (.ite (.op .lt (.reg 28) (.const 2)) (convertBDSmallProg b) (convertBDLargeProg b))
        s₁ s₁₁ (3 + ((1 + G.numEdges) + ((1 + n) + (6 + ((1 + (2 * G.numEdges + 1)) +
          ((1 + G.numEdges) + (t_p1 + (t_p2 + (t_p3 + (t_c1 + t_c2)))))))))) :=
      .ite_false hcond hex_large
    let f_tau (j : ℕ) : ℕ :=
      if hj : j < G.toComputeDigraph.numEdges then (τ ⟨j, hj⟩).1 else 0
    have htau_lt : ∀ j < G.toComputeDigraph.numEdges, f_tau j < t := by
      intro j hj
      simp only [f_tau, hj, ↓reduceDIte]
      exact (τ ⟨j, hj⟩).2
    have hbd_full : IsDigraphBranchDecompOfWidthLe (max ω 2 + ξ) G.toComputeDigraph
        (parentTree t p) (fun j => ⟨f_tau j.1, htau_lt j.1 j.2⟩) := by
      have htau_eq : (fun j : Fin G.toComputeDigraph.numEdges =>
          (⟨f_tau j.1, htau_lt j.1 j.2⟩ : Fin t)) = τ := by
        ext j
        simp only [f_tau, j.2, ↓reduceDIte]
      rw [htau_eq]
      exact hpart.to_isDigraphBranchDecompOfWidthLe (by simpa using hZ_card)
    refine ⟨s₁₁,
      t₁ + (3 + ((1 + G.numEdges) + ((1 + n) + (6 + ((1 + (2 * G.numEdges + 1)) +
        ((1 + G.numEdges) + (t_p1 + (t_p2 + (t_p3 + (t_c1 + t_c2)))))))))),
      t, p, f_tau, .seq hex₁ hex_ite,
      convertBD_large_time_bound ht₁ ht_p1 ht_p2 ht_p3 ht_c1 ht_c2 ht_le,
      by rw [hreg₁₁ 52 (by decide) (by decide), hreg₁₀ 52 (by decide) (by decide), hr52_9],
      by
        rw [harr₁₁ (b + 2) (arr_add_ne b (by decide))]
        exact eq_ofFn_of_getD_eq hb2_len₁₀ (fun z hz => (hb2_get₁₀ z hz).trans (hb9_get₉ z hz)),
      by
        refine eq_ofFn_of_getD_eq (by rw [hm_eq]; exact hb3_len₁₁) (fun j hj => ?_)
        have hj_m : j < G.numEdges := by rw [← hm_eq]; exact hj
        rw [hb3_get₁₁ j hj_m, harr₁₀ (b + 10) (arr_add_ne b (by decide)),
            hb10_get₉ ⟨j, hj⟩ (Finset.mem_univ _)]
        simp only [f_tau, hj, ↓reduceDIte],
      by
        rw [harr₁₁ (b + 5) (arr_add_ne b (by decide)), harr₁₀ (b + 5) (arr_add_ne b (by decide)),
          harr_9 (b + 5) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
            (arr_add_ne b (by decide)) (arr_add_ne b (by decide)),
          harr_8 (b + 5) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
            (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)),
          harr_7 (b + 5) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))]
        simp [s₆, s₅, s₄, s₃, s₂, hb5_1],
      by
        rw [harr₁₁ (b + 6) (arr_add_ne b (by decide)), harr₁₀ (b + 6) (arr_add_ne b (by decide)),
          harr_9 (b + 6) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
            (arr_add_ne b (by decide)) (arr_add_ne b (by decide)),
          harr_8 (b + 6) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))
            (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)),
          harr_7 (b + 6) (arr_add_ne b (by decide)) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))]
        simp [s₆, s₅, s₄, s₃, s₂, hb6_1],
      ⟨hpart.ht, by rw [hm_eq]; exact ht_le, hpart.hp,
        htau_lt,
        Or.inr ⟨htau_lt, hbd_full⟩⟩,
      fun a ha => by
        have ha2 := arr_ne_add_of_lt ha 2 (by decide)
        have ha3 := arr_ne_add_of_lt ha 3 (by decide)
        have ha4 := arr_ne_add_of_lt ha 4 (by decide)
        have ha5 := arr_ne_add_of_lt ha 5 (by decide)
        have ha6 := arr_ne_add_of_lt ha 6 (by decide)
        have ha7 := arr_ne_add_of_lt ha 7 (by decide)
        have ha8 := arr_ne_add_of_lt ha 8 (by decide)
        have ha9 := arr_ne_add_of_lt ha 9 (by decide)
        have ha10 := arr_ne_add_of_lt ha 10 (by decide)
        rw [harr₁₁ a ha3, harr₁₀ a ha2, harr_9 a ha7 ha8 ha9 ha10,
            harr_8 a ha2 ha7 ha8 ha9 ha10, harr_7 a ha7 ha8 ha10]
        simp [s₆, s₅, s₄, s₃, s₂, ha7, ha8, ha9, ha10, harr₁ a ha4 ha5 ha6],
      fun r hr => by
        have hr53 := reg_lt_53_of_lt_52 hr
        have hr55 := reg_ne_of_lt_52 hr 55 (by decide)
        have hr56 := reg_ne_of_lt_52 hr 56 (by decide)
        rw [hreg₁₁ r hr55 hr56, hreg₁₀ r hr55 hr56, hreg_9 r hr, hreg_8 r hr, hreg_7 r hr53]
        simp [s₆, s₅, s₄, s₃, s₂, State.setReg_regs_ne _ _ hr55, hreg₁ r hr53]⟩

end GraphMinor.Compute
