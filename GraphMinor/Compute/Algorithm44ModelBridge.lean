module

public import GraphMinor.Compute.Specs4

/-!
# Model Equivalence Bridge for GM XIII Algorithm (4.4)

This file proves the exact equivalence between:
1. `HasDigraphModel edgesH G` (existence of a valid `MultiDigraphModel edgesH G`), and
2. `HasRootedDigraphModel (targetToComputeRootedDigraph p edgesH) (G.toComputeRootedDigraph [])`
   (existence of a `RootedDigraphModel` in the format of `FolioTable.lean`),
and shows that for any `M : RootedDigraphModel (targetToComputeRootedDigraph p edgesH) (G.toComputeRootedDigraph [])`,
there exists a valid `M_multi : MultiDigraphModel edgesH G` whose flat encoding `M_multi.enc` is
definitionally equal to `encRootedDigraphModel M`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Counting Edges by Endpoint Pair in `G.edgeListWithMult` -/

theorem countP_flatMap_replicate_activePairs {n : ℕ} (G : MultiDigraph n) (x y : Fin n) :
    ∀ (l : List (Fin n × Fin n)), l.Nodup →
      (l.flatMap (fun p => List.replicate (G.edgeMult p.1 p.2) p)).countP (· == (x, y)) =
        if (x, y) ∈ l then G.edgeMult x y else 0
  | [], _ => by simp
  | p :: l, hnodup => by
    rw [List.nodup_cons] at hnodup
    rcases hnodup with ⟨hp_not_mem, hl_nodup⟩
    rw [List.flatMap_cons, List.countP_append,
      countP_flatMap_replicate_activePairs G x y l hl_nodup]
    by_cases hpxy : p = (x, y)
    · subst hpxy
      have hrep : (List.replicate (G.edgeMult x y) (x, y)).countP (· == (x, y)) = G.edgeMult x y := by
        rw [List.countP_eq_length_filter, List.filter_eq_self.mpr (by simp), List.length_replicate]
      simp [hrep, hp_not_mem]
    · have hrep : (List.replicate (G.edgeMult p.1 p.2) p).countP (· == (x, y)) = 0 := by
        rw [List.countP_eq_zero]
        intro q hq
        rw [List.mem_replicate] at hq
        rcases hq with ⟨_, rfl⟩
        simpa using hpxy
      have hmem : ((x, y) ∈ p :: l) ↔ ((x, y) ∈ l) := by
        simp [Ne.symm hpxy]
      simp [hrep, hmem]

theorem countP_edgeListWithMult_eq {n : ℕ} (G : MultiDigraph n) (x y : Fin n) :
    G.edgeListWithMult.countP (· == (x, y)) = G.edgeMult x y := by
  unfold MultiDigraph.edgeListWithMult
  rw [countP_flatMap_replicate_activePairs G x y G.activePairsList G.nodup_activePairsList]
  split_ifs with h
  · rfl
  · rw [G.mem_activePairsList] at h
    dsimp at h
    omega

/-- List of edge indices `e : Fin G.numEdges` whose endpoints `(tail, head)` equal `(x, y)`. -/
def edgesWithEndpoints {n : ℕ} (G : MultiDigraph n) (x y : Fin n) : List (Fin G.numEdges) :=
  (List.finRange G.numEdges).filter (fun e => decide (G.edgeEndpoints e = (x, y)))

theorem nodup_edgesWithEndpoints {n : ℕ} (G : MultiDigraph n) (x y : Fin n) :
    (edgesWithEndpoints G x y).Nodup :=
  (List.nodup_finRange G.numEdges).filter _

theorem mem_edgesWithEndpoints {n : ℕ} (G : MultiDigraph n) (x y : Fin n) (e : Fin G.numEdges) :
    e ∈ edgesWithEndpoints G x y ↔ G.edgeEndpoints e = (x, y) := by
  simp [edgesWithEndpoints]

theorem length_edgesWithEndpoints {n : ℕ} (G : MultiDigraph n) (x y : Fin n) :
    (edgesWithEndpoints G x y).length = G.edgeMult x y := by
  unfold edgesWithEndpoints
  rw [← List.countP_eq_length_filter]
  have hmap : G.edgeListWithMult =
      (List.finRange G.numEdges).map (fun e => G.edgeEndpoints e) := by
    apply List.ext_getElem
    · simp [G.length_edgeListWithMult]
    · intro i h1 h2
      simp [MultiDigraph.edgeEndpoints]
  have hcount : G.edgeListWithMult.countP (· == (x, y)) =
      (List.finRange G.numEdges).countP (fun e => decide (G.edgeEndpoints e = (x, y))) := by
    conv_lhs => rw [hmap]
    rw [List.countP_map]
    congr 1
  rw [← hcount]
  exact countP_edgeListWithMult_eq G x y

theorem card_filter_edgeEndpoints_eq {n : ℕ} (G : MultiDigraph n) (x y : Fin n) :
    (Finset.univ.filter (fun e : Fin G.numEdges => G.edgeEndpoints e = (x, y))).card =
      G.edgeMult x y := by
  have htoFinset :
      (edgesWithEndpoints G x y).toFinset =
        Finset.univ.filter (fun e : Fin G.numEdges => G.edgeEndpoints e = (x, y)) := by
    ext e
    simp [mem_edgesWithEndpoints]
  rw [← htoFinset, List.toFinset_card_of_nodup (nodup_edgesWithEndpoints G x y),
    length_edgesWithEndpoints]

/-! ### Section 2: From `RootedDigraphModel` to `MultiDigraphModel` -/

/-- Canonical unordered pair `(min p.1 p.2, max p.1 p.2)` of a vertex pair `p : Fin n × Fin n`. -/
def canonEdgePair {n : ℕ} (p : Fin n × Fin n) : Fin n × Fin n :=
  if p.1 < p.2 then p else p.swap

/-- Set of canonical (`pair.1 < pair.2`) non-loop endpoint pairs of edges in `S.edges`. -/
def subgraphEdgePairs {n : ℕ} {G : MultiDigraph n} (S : DigraphSubgraph G.toMultiComputeDigraph) :
    Finset (Fin n × Fin n) :=
  (S.edges.image (fun e => canonEdgePair (G.edgeEndpoints e))).filter (fun pair => pair.1 < pair.2)

/-- Duplicate-free list of canonical non-loop endpoint pairs of
`S : DigraphSubgraph G.toMultiComputeDigraph`. -/
noncomputable def subgraphEdgePairsList {n : ℕ} {G : MultiDigraph n}
    (S : DigraphSubgraph G.toMultiComputeDigraph) : List (Fin n × Fin n) :=
  (subgraphEdgePairs S).toList

@[simp]
theorem mem_subgraphEdgePairsList {n : ℕ} {G : MultiDigraph n}
    (S : DigraphSubgraph G.toMultiComputeDigraph) (pair : Fin n × Fin n) :
    pair ∈ subgraphEdgePairsList S ↔
      pair.1 < pair.2 ∧
        ∃ e ∈ S.edges, G.edgeEndpoints e = pair ∨ G.edgeEndpoints e = pair.swap := by
  unfold subgraphEdgePairsList subgraphEdgePairs canonEdgePair
  simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨e, he, heq⟩, hlt⟩
    refine ⟨hlt, e, he, ?_⟩
    split_ifs at heq with h
    · exact Or.inl heq
    · exact Or.inr (by rw [← heq]; rfl)
  · rintro ⟨hlt, e, he, heq | heq⟩
    · refine ⟨⟨e, he, ?_⟩, hlt⟩
      rw [heq]
      simp [hlt]
    · refine ⟨⟨e, he, ?_⟩, hlt⟩
      rw [heq]
      simp only [Prod.fst_swap, Prod.snd_swap, Prod.swap_swap, ite_eq_right_iff]
      intro h
      exact False.elim (Nat.lt_asymm hlt h)

theorem nodup_subgraphEdgePairsList {n : ℕ} {G : MultiDigraph n}
    (S : DigraphSubgraph G.toMultiComputeDigraph) :
    (subgraphEdgePairsList S).Nodup :=
  Finset.nodup_toList _

theorem branchTreeGraph_subgraphEdgePairsList_eq {n : ℕ} {G : MultiDigraph n}
    (S : DigraphSubgraph G.toMultiComputeDigraph) :
    branchTreeGraph (subgraphEdgePairsList S) = S.underlyingSimpleGraph := by
  ext x y
  simp only [branchTreeGraph, DigraphSubgraph.underlyingSimpleGraph,
    mem_subgraphEdgePairsList, MultiDigraph.toMultiComputeDigraph]
  refine and_congr_right fun hne => ?_
  constructor
  · rintro (⟨_, e, he, hpair | hpair⟩ | ⟨_, e, he, hpair | hpair⟩)
    · exact ⟨e, he, Or.inr ⟨congrArg Prod.snd hpair, congrArg Prod.fst hpair⟩⟩
    · exact ⟨e, he, Or.inl ⟨congrArg Prod.snd hpair, congrArg Prod.fst hpair⟩⟩
    · exact ⟨e, he, Or.inl ⟨congrArg Prod.snd hpair, congrArg Prod.fst hpair⟩⟩
    · exact ⟨e, he, Or.inr ⟨congrArg Prod.snd hpair, congrArg Prod.fst hpair⟩⟩
  · rintro ⟨e, he, ⟨hhd, htl⟩ | ⟨hhd, htl⟩⟩
    · rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hlt, e, he, Or.inr (Prod.ext htl hhd)⟩
      · exact Or.inr ⟨hgt, e, he, Or.inl (Prod.ext htl hhd)⟩
    · rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hlt, e, he, Or.inl (Prod.ext htl hhd)⟩
      · exact Or.inr ⟨hgt, e, he, Or.inr (Prod.ext htl hhd)⟩

theorem isConnectedBranchSet_subgraphEdgePairsList {n : ℕ} {G : MultiDigraph n}
    {S : DigraphSubgraph G.toMultiComputeDigraph} (hS : S.IsNonNullConnected) :
    IsConnectedBranchSet S.verts (subgraphEdgePairsList S) := by
  refine ⟨hS.1, nodup_subgraphEdgePairsList S, ?_, ?_⟩
  · intro pair hpair
    rw [mem_subgraphEdgePairsList] at hpair
    rcases hpair with ⟨hlt, e, he, rfl | heq⟩
    · refine ⟨S.tail_mem he, S.head_mem he, ne_of_lt hlt, ?_⟩
      rw [mem_subgraphEdgePairsList]
      intro hrev
      exact Nat.lt_asymm hlt hrev.1
    · have h1 : pair.1 = (G.edgeEndpoints e).2 := (congrArg Prod.snd heq).symm
      have h2 : pair.2 = (G.edgeEndpoints e).1 := (congrArg Prod.fst heq).symm
      refine ⟨h1 ▸ S.head_mem he, h2 ▸ S.tail_mem he, ne_of_lt hlt, ?_⟩
      rw [mem_subgraphEdgePairsList]
      intro hrev
      exact Nat.lt_asymm hlt hrev.1
  · intro x hx y hy
    rw [branchTreeGraph_subgraphEdgePairsList_eq]
    exact hS.2 x hx y hy

/-- Convert a `RootedDigraphModel (targetToOrientedComputeRootedDigraph p edgesH flips)` in
`G.toMultiComputeRootedDigraph []` to a `MultiDigraphModel edgesH G`. -/
noncomputable def MultiDigraphModel.ofOrientedRootedDigraphModel {p n : ℕ}
    {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    (flips : Fin edgesH.length → Bool)
    (M : RootedDigraphModel (targetToOrientedComputeRootedDigraph p edgesH flips)
      (G.toMultiComputeRootedDigraph [])) :
    MultiDigraphModel edgesH G where
  branchSet u := (M.vertMap u).verts
  treeEdges u := subgraphEdgePairsList (M.vertMap u)
  edgeMap k :=
    if flips k then (G.edgeEndpoints (M.edgeMap k)).swap
    else G.edgeEndpoints (M.edgeMap k)

theorem card_filter_edgeEndpoints_or_swap_eq {n : ℕ} (G : MultiDigraph n)
    {x y : Fin n} (hxy : x ≠ y) :
    (Finset.univ.filter (fun e : Fin G.numEdges =>
      G.edgeEndpoints e = (x, y) ∨ G.edgeEndpoints e = (y, x))).card =
      G.edgeMult x y + G.edgeMult y x := by
  let A := Finset.univ.filter (fun e : Fin G.numEdges => G.edgeEndpoints e = (x, y))
  let B := Finset.univ.filter (fun e : Fin G.numEdges => G.edgeEndpoints e = (y, x))
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at heA heB
    rw [heA] at heB
    exact hxy (Prod.ext_iff.mp heB).1
  have hunion :
      Finset.univ.filter (fun e : Fin G.numEdges =>
        G.edgeEndpoints e = (x, y) ∨ G.edgeEndpoints e = (y, x)) = A ∪ B := by
    ext e; simp [A, B]
  rw [hunion, Finset.card_union_of_disjoint hdisj,
    card_filter_edgeEndpoints_eq G x y, card_filter_edgeEndpoints_eq G y x]

theorem MultiDigraphModel.isValid_ofOrientedRootedDigraphModel {p n : ℕ}
    {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    (flips : Fin edgesH.length → Bool)
    (M : RootedDigraphModel (targetToOrientedComputeRootedDigraph p edgesH flips)
      (G.toMultiComputeRootedDigraph [])) :
    (MultiDigraphModel.ofOrientedRootedDigraphModel flips M).IsValid := by
  let M' := MultiDigraphModel.ofOrientedRootedDigraphModel flips M
  have hconn : ∀ u : Fin p, IsConnectedBranchSet (M'.branchSet u) (M'.treeEdges u) :=
    fun u => isConnectedBranchSet_subgraphEdgePairsList (M.connected u)
  refine ⟨hconn, M.vert_disjoint, ?_, ?_, ?_⟩
  · intro k
    have htl := M.tail_mem_vertMap k
    have hhd := M.head_mem_vertMap k
    change (G.edgeEndpoints (M.edgeMap k)).1 ∈
      (M.vertMap (if flips k then (edgesH[k.1]'k.2).2 else (edgesH[k.1]'k.2).1)).verts at htl
    change (G.edgeEndpoints (M.edgeMap k)).2 ∈
      (M.vertMap (if flips k then (edgesH[k.1]'k.2).1 else (edgesH[k.1]'k.2).2)).verts at hhd
    dsimp only [M', MultiDigraphModel.ofOrientedRootedDigraphModel]
    cases hfk : flips k <;> simp_all
  · intro x
    rw [M'.treeEdgeCount_self_eq_zero hconn x, Nat.zero_add,
      ← card_filter_edgeEndpoints_eq G x x]
    let K_xx : Finset (Fin edgesH.length) :=
      Finset.univ.filter (fun k : Fin edgesH.length => M'.edgeMap k = (x, x))
    have hmod_eq : M'.modelEdgeCount x x = K_xx.card := by
      unfold MultiDigraphModel.modelEdgeCount K_xx
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange edgesH.length).filter _)]
      congr 1; ext k; simp
    rw [hmod_eq, ← Finset.card_image_of_injective K_xx M.edge_injective]
    apply Finset.card_le_card
    intro e he
    rcases Finset.mem_image.mp he with ⟨k, hk, rfl⟩
    have hk_eq : M'.edgeMap k = (x, x) := (Finset.mem_filter.mp hk).2
    dsimp only [M', MultiDigraphModel.ofOrientedRootedDigraphModel] at hk_eq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hk_eq with hfk
    · exact Prod.ext (congrArg Prod.snd hk_eq) (congrArg Prod.fst hk_eq)
    · exact hk_eq
  · intro x y hxy
    rw [← card_filter_edgeEndpoints_or_swap_eq G hxy]
    let U_xy : Finset (Fin p) :=
      Finset.univ.filter (fun u : Fin p => (x, y) ∈ M'.treeEdges u ∨ (y, x) ∈ M'.treeEdges u)
    let K_xy : Finset (Fin edgesH.length) :=
      Finset.univ.filter (fun k : Fin edgesH.length =>
        M'.edgeMap k = (x, y) ∨ M'.edgeMap k = (y, x))
    have htree_eq : M'.treeEdgeCount x y + M'.treeEdgeCount y x = U_xy.card := by
      let U₁ := Finset.univ.filter (fun u : Fin p => (x, y) ∈ M'.treeEdges u)
      let U₂ := Finset.univ.filter (fun u : Fin p => (y, x) ∈ M'.treeEdges u)
      have h1 : M'.treeEdgeCount x y = U₁.card := by
        unfold MultiDigraphModel.treeEdgeCount U₁
        rw [← List.toFinset_card_of_nodup ((List.nodup_finRange p).filter _)]
        congr 1; ext u; simp
      have h2 : M'.treeEdgeCount y x = U₂.card := by
        unfold MultiDigraphModel.treeEdgeCount U₂
        rw [← List.toFinset_card_of_nodup ((List.nodup_finRange p).filter _)]
        congr 1; ext u; simp
      have hdisj_U : Disjoint U₁ U₂ := by
        rw [Finset.disjoint_left]
        intro u hu₁ hu₂
        simp only [U₁, U₂, Finset.mem_filter, Finset.mem_univ, true_and] at hu₁ hu₂
        exact ((hconn u).2.2.1 (x, y) hu₁).2.2.2 hu₂
      have hunion_U : U_xy = U₁ ∪ U₂ := by ext u; simp [U_xy, U₁, U₂]
      rw [h1, h2, hunion_U, Finset.card_union_of_disjoint hdisj_U]
    have hmod_eq : M'.modelEdgeCount x y + M'.modelEdgeCount y x = K_xy.card := by
      let K₁ := Finset.univ.filter (fun k : Fin edgesH.length => M'.edgeMap k = (x, y))
      let K₂ := Finset.univ.filter (fun k : Fin edgesH.length => M'.edgeMap k = (y, x))
      have h1 : M'.modelEdgeCount x y = K₁.card := by
        unfold MultiDigraphModel.modelEdgeCount K₁
        rw [← List.toFinset_card_of_nodup ((List.nodup_finRange edgesH.length).filter _)]
        congr 1; ext k; simp
      have h2 : M'.modelEdgeCount y x = K₂.card := by
        unfold MultiDigraphModel.modelEdgeCount K₂
        rw [← List.toFinset_card_of_nodup ((List.nodup_finRange edgesH.length).filter _)]
        congr 1; ext k; simp
      have hdisj_K : Disjoint K₁ K₂ := by
        rw [Finset.disjoint_left]
        intro k hk₁ hk₂
        simp only [K₁, K₂, Finset.mem_filter, Finset.mem_univ, true_and] at hk₁ hk₂
        rw [hk₁] at hk₂
        exact hxy (Prod.ext_iff.mp hk₂).1
      have hunion_K : K_xy = K₁ ∪ K₂ := by ext k; simp [K_xy, K₁, K₂]
      rw [h1, h2, hunion_K, Finset.card_union_of_disjoint hdisj_K]
    rw [htree_eq, hmod_eq]
    have hex_tree : ∀ u ∈ U_xy,
        ∃ e ∈ (M.vertMap u).edges, G.edgeEndpoints e = (x, y) ∨ G.edgeEndpoints e = (y, x) := by
      intro u hu
      simp only [U_xy, Finset.mem_filter, Finset.mem_univ, true_and, M',
        MultiDigraphModel.ofOrientedRootedDigraphModel, mem_subgraphEdgePairsList] at hu
      rcases hu with ⟨_, e, he, hpair⟩ | ⟨_, e, he, hpair⟩
      · exact ⟨e, he, hpair⟩
      · exact ⟨e, he, hpair.symm⟩
    choose f_tree hf_tree_mem hf_tree_end using hex_tree
    let E_tree : Finset (Fin G.numEdges) := U_xy.attach.image (fun u => f_tree u.1 u.2)
    let E_mod : Finset (Fin G.numEdges) := K_xy.image M.edgeMap
    have hcard_tree : U_xy.card = E_tree.card := by
      rw [Finset.card_image_of_injective, Finset.card_attach]
      intro u₁ u₂ hfeq
      ext
      by_contra hne
      have hx₁ : x ∈ (M.vertMap u₁.1).verts := by
        rcases hf_tree_end u₁.1 u₁.2 with hend | hend
        · have h1 := (M.vertMap u₁.1).tail_mem (hf_tree_mem u₁.1 u₁.2)
          change (G.edgeEndpoints (f_tree u₁.1 u₁.2)).1 ∈ (M.vertMap u₁.1).verts at h1
          rwa [hend] at h1
        · have h1 := (M.vertMap u₁.1).head_mem (hf_tree_mem u₁.1 u₁.2)
          change (G.edgeEndpoints (f_tree u₁.1 u₁.2)).2 ∈ (M.vertMap u₁.1).verts at h1
          rwa [hend] at h1
      have hx₂ : x ∈ (M.vertMap u₂.1).verts := by
        rcases hf_tree_end u₂.1 u₂.2 with hend | hend
        · have h2 := (M.vertMap u₂.1).tail_mem (hf_tree_mem u₂.1 u₂.2)
          change (G.edgeEndpoints (f_tree u₂.1 u₂.2)).1 ∈ (M.vertMap u₂.1).verts at h2
          rwa [hend] at h2
        · have h2 := (M.vertMap u₂.1).head_mem (hf_tree_mem u₂.1 u₂.2)
          change (G.edgeEndpoints (f_tree u₂.1 u₂.2)).2 ∈ (M.vertMap u₂.1).verts at h2
          rwa [hend] at h2
      exact Finset.disjoint_left.mp (M.vert_disjoint u₁.1 u₂.1 (by omega)) hx₁ hx₂
    have hcard_mod : K_xy.card = E_mod.card :=
      (Finset.card_image_of_injective K_xy M.edge_injective).symm
    have hdisj : Disjoint E_tree E_mod := by
      rw [Finset.disjoint_left]
      intro e he_tree he_mod
      rcases Finset.mem_image.mp he_tree with ⟨u, _, rfl⟩
      rcases Finset.mem_image.mp he_mod with ⟨k, _, hk_eq⟩
      have hmem_k : M.edgeMap k ∈ (M.vertMap u.1).edges := hk_eq ▸ hf_tree_mem u.1 u.2
      exact M.edge_notMem_vert u.1 k hmem_k
    have hsub : E_tree ∪ E_mod ⊆
        Finset.univ.filter (fun e : Fin G.numEdges =>
          G.edgeEndpoints e = (x, y) ∨ G.edgeEndpoints e = (y, x)) := by
      intro e he
      simp only [Finset.mem_union, E_tree, E_mod, Finset.mem_image] at he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases he with ⟨u, _, rfl⟩ | ⟨k, hk, rfl⟩
      · exact hf_tree_end u.1 u.2
      · have hk_mem := (Finset.mem_filter.mp hk).2
        dsimp only [M', MultiDigraphModel.ofOrientedRootedDigraphModel] at hk_mem
        split_ifs at hk_mem with hfk
        · rcases hk_mem with hk_eq | hk_eq
          · exact Or.inr (Prod.ext (congrArg Prod.snd hk_eq) (congrArg Prod.fst hk_eq))
          · exact Or.inl (Prod.ext (congrArg Prod.snd hk_eq) (congrArg Prod.fst hk_eq))
        · exact hk_mem
    rw [hcard_tree, hcard_mod, ← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub

/-! ### Section 3: From `MultiDigraphModel` to `RootedDigraphModel` -/

/-- Duplicate-free list of edge indices `e : Fin G.numEdges` whose undirected endpoints are
`{x, y}` (`G.edgeEndpoints e = (x, y) ∨ G.edgeEndpoints e = (y, x)`). -/
def undirEdges {n : ℕ} (G : MultiDigraph n) (x y : Fin n) : List (Fin G.numEdges) :=
  (List.finRange G.numEdges).filter (fun e =>
    decide (G.edgeEndpoints e = (x, y) ∨ G.edgeEndpoints e = (y, x)))

theorem nodup_undirEdges {n : ℕ} (G : MultiDigraph n) (x y : Fin n) :
    (undirEdges G x y).Nodup :=
  (List.nodup_finRange G.numEdges).filter _

theorem mem_undirEdges {n : ℕ} (G : MultiDigraph n) (x y : Fin n) (e : Fin G.numEdges) :
    e ∈ undirEdges G x y ↔ G.edgeEndpoints e = (x, y) ∨ G.edgeEndpoints e = (y, x) := by
  simp [undirEdges]

theorem undirEdges_comm {n : ℕ} (G : MultiDigraph n) (x y : Fin n) :
    undirEdges G x y = undirEdges G y x := by
  unfold undirEdges
  congr 1; funext e; simp [or_comm]

theorem length_undirEdges {n : ℕ} (G : MultiDigraph n) (x y : Fin n) :
    (undirEdges G x y).length =
      if x = y then G.edgeMult x x else G.edgeMult x y + G.edgeMult y x := by
  have htoFinset :
      (undirEdges G x y).toFinset =
        Finset.univ.filter (fun e : Fin G.numEdges =>
          G.edgeEndpoints e = (x, y) ∨ G.edgeEndpoints e = (y, x)) := by
    ext e; simp [mem_undirEdges]
  rw [← List.toFinset_card_of_nodup (nodup_undirEdges G x y), htoFinset]
  split_ifs with hxy
  · subst hxy
    simp [card_filter_edgeEndpoints_eq]
  · exact card_filter_edgeEndpoints_or_swap_eq G hxy

/-- Number of branch trees using undirected edge `{x, y}` in `M`. -/
def MultiDigraphModel.undirTreeCount {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} (M : MultiDigraphModel edgesH G) (x y : Fin n) : ℕ :=
  if x = y then M.treeEdgeCount x x else M.treeEdgeCount x y + M.treeEdgeCount y x

theorem MultiDigraphModel.undirTreeCount_comm {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} (M : MultiDigraphModel edgesH G) (x y : Fin n) :
    M.undirTreeCount x y = M.undirTreeCount y x := by
  unfold undirTreeCount
  split_ifs with h1 h2 h2
  · subst h1; rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · omega

/-- List of edge indices `j : Fin edgesH.length` mapped by `M.edgeMap` to `(x, y)` or `(y, x)`. -/
def MultiDigraphModel.undirModelFilter {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} (M : MultiDigraphModel edgesH G) (x y : Fin n) :
    List (Fin edgesH.length) :=
  (List.finRange edgesH.length).filter (fun j =>
    decide (M.edgeMap j = (x, y) ∨ M.edgeMap j = (y, x)))

theorem MultiDigraphModel.mem_undirModelFilter {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} (M : MultiDigraphModel edgesH G) (x y : Fin n)
    (j : Fin edgesH.length) :
    j ∈ M.undirModelFilter x y ↔ M.edgeMap j = (x, y) ∨ M.edgeMap j = (y, x) := by
  simp [undirModelFilter]

theorem MultiDigraphModel.undirModelFilter_comm {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} (M : MultiDigraphModel edgesH G) (x y : Fin n) :
    M.undirModelFilter x y = M.undirModelFilter y x := by
  unfold undirModelFilter
  congr 1; funext j; simp [or_comm]

theorem MultiDigraphModel.length_undirModelFilter {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} (M : MultiDigraphModel edgesH G) (x y : Fin n) :
    (M.undirModelFilter x y).length =
      if x = y then M.modelEdgeCount x x else M.modelEdgeCount x y + M.modelEdgeCount y x := by
  unfold undirModelFilter
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange edgesH.length).filter _)]
  split_ifs with hxy
  · subst hxy
    unfold modelEdgeCount
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange edgesH.length).filter _)]
    congr 1; ext j; simp
  · let K₁ := Finset.univ.filter (fun j : Fin edgesH.length => M.edgeMap j = (x, y))
    let K₂ := Finset.univ.filter (fun j : Fin edgesH.length => M.edgeMap j = (y, x))
    have h1 : M.modelEdgeCount x y = K₁.card := by
      unfold modelEdgeCount K₁
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange edgesH.length).filter _)]
      congr 1; ext j; simp
    have h2 : M.modelEdgeCount y x = K₂.card := by
      unfold modelEdgeCount K₂
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange edgesH.length).filter _)]
      congr 1; ext j; simp
    have hdisj : Disjoint K₁ K₂ := by
      rw [Finset.disjoint_left]
      intro j hj₁ hj₂
      simp only [K₁, K₂, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
      rw [hj₁] at hj₂
      exact hxy (Prod.ext_iff.mp hj₂).1
    rw [h1, h2, ← Finset.card_union_of_disjoint hdisj]
    congr 1; ext j; simp [K₁, K₂]

/-- Given a valid `M : MultiDigraphModel edgesH G`, there exists an edge orientation
`flips : Fin edgesH.length → Bool` and a `RootedDigraphModel` of
`targetToOrientedComputeRootedDigraph p edgesH flips` in `G`. -/
theorem MultiDigraphModel.exists_orientedRootedDigraphModel {p n : ℕ}
    {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    (M : MultiDigraphModel edgesH G) (hM : M.IsValid) :
    ∃ flips : Fin edgesH.length → Bool,
      HasRootedDigraphModel (targetToOrientedComputeRootedDigraph p edgesH flips)
        (G.toMultiComputeRootedDigraph []) := by
  rcases hM with ⟨hconn, hdisj, hedges, hloop, hmult⟩
  let vertSub (u : Fin p) : DigraphSubgraph G.toMultiComputeDigraph := {
    verts := M.branchSet u
    edges := Finset.univ.filter (fun e : Fin G.numEdges =>
      (G.edgeEndpoints e ∈ M.treeEdges u ∨ (G.edgeEndpoints e).swap ∈ M.treeEdges u) ∧
      (undirEdges G (G.edgeEndpoints e).1 (G.edgeEndpoints e).2).idxOf e = 0)
    head_mem := fun e he => by
      rcases (Finset.mem_filter.mp he).2 with ⟨hmem | hmem, _⟩
      · exact ((hconn u).2.2.1 _ hmem).2.1
      · exact ((hconn u).2.2.1 _ hmem).1
    tail_mem := fun e he => by
      rcases (Finset.mem_filter.mp he).2 with ⟨hmem | hmem, _⟩
      · exact ((hconn u).2.2.1 _ hmem).1
      · exact ((hconn u).2.2.1 _ hmem).2.1
  }
  have hmem_filter : ∀ k : Fin edgesH.length,
      k ∈ M.undirModelFilter (M.edgeMap k).1 (M.edgeMap k).2 := by
    intro k
    rw [M.mem_undirModelFilter]
    exact Or.inl rfl
  have hidx_lt : ∀ k : Fin edgesH.length,
      M.undirTreeCount (M.edgeMap k).1 (M.edgeMap k).2 +
        (M.undirModelFilter (M.edgeMap k).1 (M.edgeMap k).2).idxOf k <
      (undirEdges G (M.edgeMap k).1 (M.edgeMap k).2).length := by
    intro k
    have hlt_mod :
        (M.undirModelFilter (M.edgeMap k).1 (M.edgeMap k).2).idxOf k <
          (M.undirModelFilter (M.edgeMap k).1 (M.edgeMap k).2).length :=
      List.idxOf_lt_length_of_mem (hmem_filter k)
    rw [M.length_undirModelFilter] at hlt_mod
    rw [length_undirEdges]
    unfold MultiDigraphModel.undirTreeCount
    split_ifs with hxy
    · simp only [hxy, ↓reduceIte] at hlt_mod
      have hm := hloop (M.edgeMap k).2
      rw [hxy]
      omega
    · simp only [hxy, ↓reduceIte] at hlt_mod
      have hm := hmult (M.edgeMap k).1 (M.edgeMap k).2 hxy
      omega
  let edgeChoice (k : Fin edgesH.length) : Fin G.numEdges :=
    (undirEdges G (M.edgeMap k).1 (M.edgeMap k).2)[
      M.undirTreeCount (M.edgeMap k).1 (M.edgeMap k).2 +
        (M.undirModelFilter (M.edgeMap k).1 (M.edgeMap k).2).idxOf k]'(hidx_lt k)
  have hedgeChoice_end : ∀ k : Fin edgesH.length,
      G.edgeEndpoints (edgeChoice k) = M.edgeMap k ∨
        G.edgeEndpoints (edgeChoice k) = (M.edgeMap k).swap := by
    intro k
    exact (mem_undirEdges G (M.edgeMap k).1 (M.edgeMap k).2 _).mp (List.getElem_mem _)
  have hedgeChoice_idxOf : ∀ k : Fin edgesH.length,
      (undirEdges G (M.edgeMap k).1 (M.edgeMap k).2).idxOf (edgeChoice k) =
        M.undirTreeCount (M.edgeMap k).1 (M.edgeMap k).2 +
        (M.undirModelFilter (M.edgeMap k).1 (M.edgeMap k).2).idxOf k := by
    intro k
    exact List.Nodup.idxOf_getElem (nodup_undirEdges G (M.edgeMap k).1 (M.edgeMap k).2) _ _
  let flips (k : Fin edgesH.length) : Bool :=
    decide (G.edgeEndpoints (edgeChoice k) ≠ M.edgeMap k)
  refine ⟨flips, ⟨{
    vertMap := vertSub
    edgeMap := edgeChoice
    connected := fun u => by
      refine ⟨(hconn u).1, fun a ha b hb => ?_⟩
      have hreach := (hconn u).2.2.2 a ha b hb
      have hsub : branchTreeGraph (M.treeEdges u) ≤ (vertSub u).underlyingSimpleGraph := by
        intro w₁ w₂ hadj
        rcases hadj with ⟨hne, hmem | hmem⟩
        · have htree_pos : 0 < M.treeEdgeCount w₁ w₂ := by
            unfold MultiDigraphModel.treeEdgeCount
            rw [List.length_pos_iff_exists_mem]
            exact ⟨u, by simp [hmem]⟩
          have h0_lt : 0 < (undirEdges G w₁ w₂).length := by
            rw [length_undirEdges]
            simp only [hne, ↓reduceIte]
            have := hmult w₁ w₂ hne; omega
          let e₀ := (undirEdges G w₁ w₂)[0]'h0_lt
          have he₀_end : G.edgeEndpoints e₀ = (w₁, w₂) ∨ G.edgeEndpoints e₀ = (w₂, w₁) :=
            (mem_undirEdges G w₁ w₂ _).mp (List.getElem_mem _)
          have he₀_idx : (undirEdges G w₁ w₂).idxOf e₀ = 0 :=
            List.Nodup.idxOf_getElem (nodup_undirEdges G w₁ w₂) 0 h0_lt
          rcases he₀_end with hend | hend
          · refine ⟨hne, e₀, ?_, Or.inr ⟨congrArg Prod.snd hend, congrArg Prod.fst hend⟩⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (by rw [hend]; exact hmem), by
              rw [show (G.edgeEndpoints e₀).1 = w₁ from congrArg Prod.fst hend,
                  show (G.edgeEndpoints e₀).2 = w₂ from congrArg Prod.snd hend]
              exact he₀_idx⟩
          · refine ⟨hne, e₀, ?_, Or.inl ⟨congrArg Prod.snd hend, congrArg Prod.fst hend⟩⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (by rw [hend]; exact hmem), by
              rw [show (G.edgeEndpoints e₀).1 = w₂ from congrArg Prod.fst hend,
                  show (G.edgeEndpoints e₀).2 = w₁ from congrArg Prod.snd hend,
                  undirEdges_comm G w₂ w₁]
              exact he₀_idx⟩
        · have htree_pos : 0 < M.treeEdgeCount w₂ w₁ := by
            unfold MultiDigraphModel.treeEdgeCount
            rw [List.length_pos_iff_exists_mem]
            exact ⟨u, by simp [hmem]⟩
          have h0_lt : 0 < (undirEdges G w₂ w₁).length := by
            rw [length_undirEdges]
            simp only [hne.symm, ↓reduceIte]
            have := hmult w₂ w₁ hne.symm; omega
          let e₀ := (undirEdges G w₂ w₁)[0]'h0_lt
          have he₀_end : G.edgeEndpoints e₀ = (w₂, w₁) ∨ G.edgeEndpoints e₀ = (w₁, w₂) :=
            (mem_undirEdges G w₂ w₁ _).mp (List.getElem_mem _)
          have he₀_idx : (undirEdges G w₂ w₁).idxOf e₀ = 0 :=
            List.Nodup.idxOf_getElem (nodup_undirEdges G w₂ w₁) 0 h0_lt
          rcases he₀_end with hend | hend
          · refine ⟨hne, e₀, ?_, Or.inl ⟨congrArg Prod.snd hend, congrArg Prod.fst hend⟩⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (by rw [hend]; exact hmem), by
              rw [show (G.edgeEndpoints e₀).1 = w₂ from congrArg Prod.fst hend,
                  show (G.edgeEndpoints e₀).2 = w₁ from congrArg Prod.snd hend]
              exact he₀_idx⟩
          · refine ⟨hne, e₀, ?_, Or.inr ⟨congrArg Prod.snd hend, congrArg Prod.fst hend⟩⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (by rw [hend]; exact hmem), by
              rw [show (G.edgeEndpoints e₀).1 = w₁ from congrArg Prod.fst hend,
                  show (G.edgeEndpoints e₀).2 = w₂ from congrArg Prod.snd hend,
                  undirEdges_comm G w₁ w₂]
              exact he₀_idx⟩
      exact SimpleGraph.Reachable.mono hsub hreach
    vert_disjoint := hdisj
    edge_injective := fun k₁ k₂ heq => by
      have hend₁ := hedgeChoice_end k₁
      have hend₂ := hedgeChoice_end k₂
      rw [← heq] at hend₂
      have hpair_eq : M.edgeMap k₂ = M.edgeMap k₁ ∨ M.edgeMap k₂ = (M.edgeMap k₁).swap := by
        rcases hend₁ with h1 | h1 <;> rcases hend₂ with h2 | h2
        · rw [h1] at h2; exact Or.inl h2.symm
        · rw [h1] at h2
          exact Or.inr (Prod.ext (congrArg Prod.snd h2).symm (congrArg Prod.fst h2).symm)
        · rw [h1] at h2
          exact Or.inr h2.symm
        · rw [h1] at h2
          exact Or.inl (Prod.ext (congrArg Prod.snd h2).symm (congrArg Prod.fst h2).symm)
      have hlist_eq :
          undirEdges G (M.edgeMap k₂).1 (M.edgeMap k₂).2 =
            undirEdges G (M.edgeMap k₁).1 (M.edgeMap k₁).2 := by
        rcases hpair_eq with hp | hp
        · rw [hp]
        · rw [hp]; exact undirEdges_comm G _ _
      have htree_eq :
          M.undirTreeCount (M.edgeMap k₂).1 (M.edgeMap k₂).2 =
            M.undirTreeCount (M.edgeMap k₁).1 (M.edgeMap k₁).2 := by
        rcases hpair_eq with hp | hp
        · rw [hp]
        · rw [hp]; exact M.undirTreeCount_comm _ _
      have hfilt_eq :
          M.undirModelFilter (M.edgeMap k₂).1 (M.edgeMap k₂).2 =
            M.undirModelFilter (M.edgeMap k₁).1 (M.edgeMap k₁).2 := by
        rcases hpair_eq with hp | hp
        · rw [hp]
        · rw [hp]; exact M.undirModelFilter_comm _ _
      have hidx1 := hedgeChoice_idxOf k₁
      have hidx2 := hedgeChoice_idxOf k₂
      rw [← heq, hlist_eq, htree_eq, hfilt_eq] at hidx2
      have hidx_eq :
          (M.undirModelFilter (M.edgeMap k₁).1 (M.edgeMap k₁).2).idxOf k₁ =
            (M.undirModelFilter (M.edgeMap k₁).1 (M.edgeMap k₁).2).idxOf k₂ := by omega
      exact (List.idxOf_inj
        (l := M.undirModelFilter (M.edgeMap k₁).1 (M.edgeMap k₁).2)
        (x := k₁) (y := k₂) (hmem_filter k₁)).mp hidx_eq
    edge_notMem_vert := fun v k hmem => by
      rcases (Finset.mem_filter.mp hmem).2 with ⟨htree_mem, hidx0⟩
      have hend := hedgeChoice_end k
      have hlist_eq :
          undirEdges G (G.edgeEndpoints (edgeChoice k)).1 (G.edgeEndpoints (edgeChoice k)).2 =
            undirEdges G (M.edgeMap k).1 (M.edgeMap k).2 := by
        rcases hend with h1 | h1
        · rw [h1]
        · rw [h1]; exact undirEdges_comm G _ _
      rw [hlist_eq, hedgeChoice_idxOf k] at hidx0
      have hpair_tree :
          M.edgeMap k ∈ M.treeEdges v ∨ (M.edgeMap k).swap ∈ M.treeEdges v := by
        rcases hend with h1 | h1
        · rwa [h1] at htree_mem
        · rw [h1] at htree_mem
          exact htree_mem.symm
      have hne_xy : (M.edgeMap k).1 ≠ (M.edgeMap k).2 := by
        rcases hpair_tree with hm | hm
        · exact ((hconn v).2.2.1 _ hm).2.2.1
        · exact (((hconn v).2.2.1 _ hm).2.2.1).symm
      have htree_pos : 0 < M.undirTreeCount (M.edgeMap k).1 (M.edgeMap k).2 := by
        unfold MultiDigraphModel.undirTreeCount
        simp only [hne_xy, ↓reduceIte]
        rcases hpair_tree with hm | hm
        · have hpos : 0 < M.treeEdgeCount (M.edgeMap k).1 (M.edgeMap k).2 := by
            unfold MultiDigraphModel.treeEdgeCount
            rw [List.length_pos_iff_exists_mem]
            exact ⟨v, List.mem_filter.mpr ⟨List.mem_finRange v, decide_eq_true hm⟩⟩
          omega
        · have hpos : 0 < M.treeEdgeCount (M.edgeMap k).2 (M.edgeMap k).1 := by
            unfold MultiDigraphModel.treeEdgeCount
            rw [List.length_pos_iff_exists_mem]
            exact ⟨v, List.mem_filter.mpr ⟨List.mem_finRange v, decide_eq_true hm⟩⟩
          omega
      omega
    head_mem_vertMap := fun k => by
      change (G.edgeEndpoints (edgeChoice k)).2 ∈
        M.branchSet (if flips k then (edgesH[k.1]'k.2).1 else (edgesH[k.1]'k.2).2)
      dsimp only [flips]
      by_cases hne : G.edgeEndpoints (edgeChoice k) = M.edgeMap k
      · simp [hne, (hedges k).2]
      · rcases hedgeChoice_end k with h1 | h1
        · exact absurd h1 hne
        · simp [hne, congrArg Prod.snd h1, (hedges k).1]
    tail_mem_vertMap := fun k => by
      change (G.edgeEndpoints (edgeChoice k)).1 ∈
        M.branchSet (if flips k then (edgesH[k.1]'k.2).2 else (edgesH[k.1]'k.2).1)
      dsimp only [flips]
      by_cases hne : G.edgeEndpoints (edgeChoice k) = M.edgeMap k
      · simp [hne, (hedges k).1]
      · rcases hedgeChoice_end k with h1 | h1
        · exact absurd h1 hne
        · simp [hne, congrArg Prod.fst h1, (hedges k).2]
    root_mem_vertMap := fun i => Fin.elim0 i
  }⟩⟩

/-- **Equivalence between `HasDigraphModel` and `HasRootedDigraphModel` for some orientation
`flips : Fin edgesH.length → Bool` (`Z = []`):** -/
theorem hasDigraphModel_iff_exists_hasRootedDigraphModel {p n : ℕ}
    (edgesH : List (Fin p × Fin p)) (G : MultiDigraph n) :
    HasDigraphModel edgesH G ↔
      ∃ flips : Fin edgesH.length → Bool,
        HasRootedDigraphModel (targetToOrientedComputeRootedDigraph p edgesH flips)
          (G.toMultiComputeRootedDigraph []) := by
  constructor
  · rintro ⟨M, hM⟩
    exact M.exists_orientedRootedDigraphModel hM
  · rintro ⟨flips, ⟨M⟩⟩
    exact ⟨MultiDigraphModel.ofOrientedRootedDigraphModel flips M,
      MultiDigraphModel.isValid_ofOrientedRootedDigraphModel flips M⟩

/-! ### Section 4: Properties of `FolioSetRep.decodedAt` and Isomorphism Permutations -/

theorem FolioSetRep.decRootedDigraph_decodedAt {q δ : ℕ} (F : FolioSetRep q δ)
    (i : Fin F.codes.length) :
    decRootedDigraph q (F.codes[i.1]'i.2) = some (F.decodedAt i) := by
  have hc : IsDetailLeCode q δ (F.codes[i.1]'i.2) := F.all_detail _ (List.getElem_mem _)
  unfold FolioSetRep.decodedAt
  dsimp only
  split
  · next H h => exact h
  · next h => unfold IsDetailLeCode at hc; rw [h] at hc; exact False.elim hc

theorem FolioSetRep.enc_decodedAt {q δ : ℕ} (F : FolioSetRep q δ)
    (i : Fin F.codes.length) :
    F.codes[i.1]'i.2 = encRootedDigraph (F.decodedAt i) := by
  have hc : IsDetailLeCode q δ (F.codes[i.1]'i.2) := F.all_detail _ (List.getElem_mem _)
  unfold IsDetailLeCode at hc
  rw [F.decRootedDigraph_decodedAt i] at hc
  exact hc.1

theorem FolioSetRep.hasDetailLe_decodedAt {q δ : ℕ} (F : FolioSetRep q δ)
    (i : Fin F.codes.length) :
    (F.decodedAt i).HasDetailLe δ := by
  have hc : IsDetailLeCode q δ (F.codes[i.1]'i.2) := F.all_detail _ (List.getElem_mem _)
  unfold IsDetailLeCode at hc
  rw [F.decRootedDigraph_decodedAt i] at hc
  exact hc.2

theorem FolioSetRep.isIsoRootedDigraphCode_getElem_iff {q δ : ℕ} (F : FolioSetRep q δ)
    (H : ComputeRootedDigraph q) (i : Fin F.codes.length) :
    IsIsoRootedDigraphCode q (encRootedDigraph H) (F.codes[i.1]'i.2) ↔
      IsRootedDigraphIso H (F.decodedAt i) := by
  rw [F.enc_decodedAt i, isIsoRootedDigraphCode_enc_iff]

theorem FolioSetRep.memIso_iff_exists_fin {q δ : ℕ} (F : FolioSetRep q δ)
    (H : ComputeRootedDigraph q) :
    F.MemIso H ↔ ∃ i : Fin F.codes.length, IsRootedDigraphIso H (F.decodedAt i) := by
  unfold FolioSetRep.MemIso
  constructor
  · rintro ⟨c, hc_mem, hiso⟩
    rcases List.mem_iff_getElem.mp hc_mem with ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, (F.isIsoRootedDigraphCode_getElem_iff H ⟨i, hi⟩).mp hiso⟩
  · rintro ⟨i, hiso⟩
    exact ⟨F.codes[i.1]'i.2, List.getElem_mem _,
      (F.isIsoRootedDigraphCode_getElem_iff H i).mpr hiso⟩

/-! ### Section 5: Length-Prefixed Record Lists and `encRootedDigraphModel` Slice Lemmas -/

/-- Flat length-prefixed serialization of a list of records `recs : List (List ℕ)`:
`[recs.length] ++ recs.flatMap (fun r => r.length :: r)`. -/
def encRecordList (recs : List (List ℕ)) : List ℕ :=
  [recs.length] ++ recs.flatMap (fun r => r.length :: r)

/-- Word offset of the `i`-th record (specifically, its length word `recs[i].length`) inside
`encRecordList recs`. -/
def recordOffset (recs : List (List ℕ)) (i : ℕ) : ℕ :=
  1 + ((recs.take i).map (fun r => 1 + r.length)).sum

theorem encFolioSetRep_eq_encRecordList {q δ : ℕ} (F : FolioSetRep q δ) :
    encFolioSetRep F = encRecordList F.codes := rfl

theorem encFolioModels_eq_encRecordList {q δ : ℕ} {G : ComputeRootedDigraph q}
    (F : FolioSetRep q δ)
    (models : ∀ i : Fin F.codes.length, RootedDigraphModel (F.decodedAt i) G) :
    encFolioModels F models =
      encRecordList ((List.finRange F.codes.length).map (fun i =>
        encRootedDigraphModel (models i))) := by
  unfold encFolioModels encRecordList
  simp [List.flatMap_map]

@[simp]
theorem recordOffset_zero (recs : List (List ℕ)) :
    recordOffset recs 0 = 1 := rfl

theorem recordOffset_succ {recs : List (List ℕ)} {i : ℕ} (hi : i < recs.length) :
    recordOffset recs (i + 1) = recordOffset recs i + 1 + (recs[i]'hi).length := by
  unfold recordOffset
  rw [take_add_one_eq_append_getElem recs i hi, List.map_append, List.sum_append]
  simp
  omega

theorem length_flatMap_len_cons (l : List (List ℕ)) :
    (l.flatMap (fun r => r.length :: r)).length = (l.map (fun r => 1 + r.length)).sum := by
  induction l with
  | nil => simp
  | cons r rs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.map_cons,
      List.sum_cons, ih]
    omega

theorem list_eq_take_append_cons_drop {α : Type*} (l : List α) (i : ℕ) (hi : i < l.length) :
    l = l.take i ++ (l[i]'hi) :: l.drop (i + 1) := by
  calc l
    _ = l.take (i + 1) ++ l.drop (i + 1) := (List.take_append_drop (i + 1) l).symm
    _ = (l.take i ++ [l[i]'hi]) ++ l.drop (i + 1) := by
      rw [take_add_one_eq_append_getElem l i hi]
    _ = l.take i ++ (l[i]'hi) :: l.drop (i + 1) := by simp

theorem encRecordList_split {recs : List (List ℕ)} {i : ℕ} (hi : i < recs.length) :
    ∃ pre suf : List ℕ,
      encRecordList recs = pre ++ ((recs[i]'hi).length :: (recs[i]'hi)) ++ suf ∧
      pre.length = recordOffset recs i := by
  refine ⟨[recs.length] ++ (recs.take i).flatMap (fun r => r.length :: r),
    (recs.drop (i + 1)).flatMap (fun r => r.length :: r), ?_, ?_⟩
  · unfold encRecordList
    have hsplit := congrArg (List.flatMap (fun r : List ℕ => r.length :: r))
      (list_eq_take_append_cons_drop recs i hi)
    simp only [List.flatMap_append, List.flatMap_cons] at hsplit
    simp only [List.cons_append, List.append_assoc]
    exact congrArg (recs.length :: ·) hsplit
  · rw [List.length_append, List.length_singleton, length_flatMap_len_cons]
    rfl

theorem recordOffset_le_length (recs : List (List ℕ)) (i : ℕ) :
    recordOffset recs i ≤ (encRecordList recs).length := by
  unfold recordOffset encRecordList
  rw [List.length_append, List.length_singleton, length_flatMap_len_cons]
  have hsplit : recs = recs.take i ++ recs.drop i := (List.take_append_drop i recs).symm
  conv_rhs => rw [hsplit, List.map_append, List.sum_append]
  omega

theorem sum_map_le_length_mul {α : Type*} (l : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ x ∈ l, f x ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hr : f r ≤ B := h r List.mem_cons_self
    have hrs : (rs.map f).sum ≤ rs.length * B :=
      ih (fun x hx => h x (List.mem_cons_of_mem r hx))
    nlinarith

theorem length_encFolioSetRep_le {q δ : ℕ} (F : FolioSetRep q δ) :
    (encFolioSetRep F).length ≤
      1 + (allDetailLeCodes q δ).length * (3 + q + 2 * δ) := by
  rw [encFolioSetRep_eq_encRecordList]
  unfold encRecordList
  rw [List.length_append, List.length_singleton, length_flatMap_len_cons]
  have hle_sum :
      (F.codes.map (fun r => 1 + r.length)).sum ≤
        F.codes.length * (3 + q + 2 * δ) := by
    apply sum_map_le_length_mul
    intro r hr
    have hlen := (length_and_words_le_of_isDetailLeCode (F.all_detail r hr)).1
    omega
  have hlen_codes := length_codes_le_allDetailLeCodes F
  nlinarith

theorem length_encFolioModels_le {q δ : ℕ} {G : ComputeRootedDigraph q}
    (F : FolioSetRep q δ)
    (models : ∀ i : Fin F.codes.length, RootedDigraphModel (F.decodedAt i) G) :
    (encFolioModels F models).length ≤
      1 + (allDetailLeCodes q δ).length * (3 + 2 * δ + (q + δ) * G.digraph.numVerts) := by
  rw [encFolioModels_eq_encRecordList]
  unfold encRecordList
  rw [List.length_append, List.length_singleton, length_flatMap_len_cons, List.map_map]
  have hle_sum :
      (List.map ((fun r : List ℕ => 1 + r.length) ∘
          fun i => encRootedDigraphModel (models i))
        (List.finRange F.codes.length)).sum ≤
      (List.finRange F.codes.length).length *
        (3 + 2 * δ + (q + δ) * G.digraph.numVerts) := by
    apply sum_map_le_length_mul
    intro i _
    dsimp only [Function.comp_apply]
    rw [length_encRootedDigraphModel]
    have hdet : (F.decodedAt i).HasDetailLe δ := F.hasDetailLe_decodedAt i
    have hm : (F.decodedAt i).digraph.numEdges ≤ δ := hdet.1
    have hv : (F.decodedAt i).digraph.numVerts ≤ q + δ :=
      (F.decodedAt i).numVerts_le_of_hasDetailLe hdet
    have hmul : (F.decodedAt i).digraph.numVerts * G.digraph.numVerts ≤
        (q + δ) * G.digraph.numVerts :=
      Nat.mul_le_mul_right G.digraph.numVerts hv
    omega
  rw [List.length_finRange] at hle_sum
  have hlen_codes := length_codes_le_allDetailLeCodes F
  have hmul := Nat.mul_le_mul_right (3 + 2 * δ + (q + δ) * G.digraph.numVerts) hlen_codes
  omega

/-- Element access for the tail of edge `e` in `encRootedDigraphModel M`. -/
theorem encRootedDigraphModel_getElem_tail {q : ℕ} {H G : ComputeRootedDigraph q}
    (M : RootedDigraphModel H G) (e : Fin H.digraph.numEdges) :
    (encRootedDigraphModel M)[2 + 2 * e.1]? = some (G.digraph.tail (M.edgeMap e)).1 := by
  unfold encRootedDigraphModel
  rw [List.getElem?_append_left (by
    rw [List.length_append, length_flatMap_edges]
    simp)]
  rw [List.getElem?_append_right (by simp)]
  have hsub : 2 + 2 * e.1 - [H.digraph.numVerts, H.digraph.numEdges].length = 2 * e.1 := by
    simp
  rw [hsub]
  exact getElem_flatMap_edges_even
    (fun k => G.digraph.tail (M.edgeMap k))
    (fun k => G.digraph.head (M.edgeMap k)) e

/-- Element access for the head of edge `e` in `encRootedDigraphModel M`. -/
theorem encRootedDigraphModel_getElem_head {q : ℕ} {H G : ComputeRootedDigraph q}
    (M : RootedDigraphModel H G) (e : Fin H.digraph.numEdges) :
    (encRootedDigraphModel M)[2 + 2 * e.1 + 1]? = some (G.digraph.head (M.edgeMap e)).1 := by
  unfold encRootedDigraphModel
  rw [List.getElem?_append_left (by
    rw [List.length_append, length_flatMap_edges]
    simp; omega)]
  rw [List.getElem?_append_right (by simp; omega)]
  have hsub : 2 + 2 * e.1 + 1 - [H.digraph.numVerts, H.digraph.numEdges].length =
      2 * e.1 + 1 := by simp; omega
  rw [hsub]
  exact getElem_flatMap_edges_odd
    (fun k => G.digraph.tail (M.edgeMap k))
    (fun k => G.digraph.head (M.edgeMap k)) e

/-- Slice decomposition of `encRootedDigraphModel M` at vertex `u : Fin H.digraph.numVerts`. -/
theorem encRootedDigraphModel_vertSlice {q : ℕ} {H G : ComputeRootedDigraph q}
    (M : RootedDigraphModel H G) (u : Fin H.digraph.numVerts) :
    ∃ pre suf : List ℕ,
      encRootedDigraphModel M = pre ++ bitSetList (M.vertMap u).verts ++ suf ∧
      pre.length = 2 + 2 * H.digraph.numEdges + u.1 * G.digraph.numVerts := by
  let edgePart := [H.digraph.numVerts, H.digraph.numEdges] ++
    (List.finRange H.digraph.numEdges).flatMap (fun e =>
      [(G.digraph.tail (M.edgeMap e)).1, (G.digraph.head (M.edgeMap e)).1])
  let vList := List.finRange H.digraph.numVerts
  have hu_lt : u.1 < vList.length := by simp [vList, u.2]
  have hv_get : vList[u.1]'hu_lt = u := by simp [vList]
  have hv_split : vList = vList.take u.1 ++ u :: vList.drop (u.1 + 1) := by
    have h0 := list_eq_take_append_cons_drop vList u.1 hu_lt
    rwa [hv_get] at h0
  refine ⟨edgePart ++ (vList.take u.1).flatMap (fun x => bitSetList (M.vertMap x).verts),
    (vList.drop (u.1 + 1)).flatMap (fun x => bitSetList (M.vertMap x).verts), ?_, ?_⟩
  · unfold encRootedDigraphModel
    change edgePart ++ vList.flatMap (fun x => bitSetList (M.vertMap x).verts) = _
    have hflat :
        vList.flatMap (fun x => bitSetList (M.vertMap x).verts) =
          (vList.take u.1).flatMap (fun x => bitSetList (M.vertMap x).verts) ++
            bitSetList (M.vertMap u).verts ++
            (vList.drop (u.1 + 1)).flatMap (fun x => bitSetList (M.vertMap x).verts) := by
      conv_lhs => rw [hv_split]
      simp [List.append_assoc]
    rw [hflat]
    simp [List.append_assoc]
  · have hedge_len : edgePart.length = 2 + 2 * H.digraph.numEdges := by
      dsimp only [edgePart]
      rw [List.length_append, length_flatMap_edges]
      simp
    have htake_len :
        ((vList.take u.1).flatMap (fun x => bitSetList (M.vertMap x).verts)).length =
          u.1 * G.digraph.numVerts := by
      rw [List.length_flatMap]
      have hmap :
          List.map (fun x => (bitSetList (M.vertMap x).verts).length) (vList.take u.1) =
            List.replicate (vList.take u.1).length G.digraph.numVerts := by
        rw [List.map_eq_replicate_iff]
        intro x _
        exact length_bitSetList (M.vertMap x).verts
      rw [hmap, List.sum_replicate, smul_eq_mul, List.length_take, List.length_finRange,
        Nat.min_eq_left (Nat.le_of_lt u.2)]
    rw [List.length_append, hedge_len, htake_len]

/-! ### Section 6: Word RAM Helpers for Record Matching and Model Extraction -/

theorem getElem_append_cons_length (pre suf : List ℕ) (val : ℕ)
    (h : pre.length < (pre ++ val :: suf).length) :
    (pre ++ val :: suf)[pre.length]'h = val := by
  rw [List.getElem_append_right le_rfl]
  simp

/-- Write `r_val` at `a_buf[r_pos]` and increment `r_pos` by `1`. -/
def bufPush1 (a_buf : Arr) (r_pos r_val : Reg) : Cmd :=
  .seq (.write a_buf (.reg r_pos) (.reg r_val))
    (.assign r_pos (.op .add (.reg r_pos) (.const 1)))

theorem bufPush1_exec {w : ℕ} (a_buf : ℕ) (r_pos r_val : ℕ)
    (pfx : List ℕ) (rem val : ℕ)
    (hw : 1 < 2 ^ w) (hpos_w : pfx.length + 1 < 2 ^ w) (hval_w : val < 2 ^ w)
    {s : State}
    (hbuf : s.arrs a_buf = pfx ++ List.replicate (rem + 1) 0)
    (hrpos : s.regs r_pos = pfx.length)
    (hrval : s.regs r_val = val) :
    ∃ s' t,
      Exec w (bufPush1 a_buf r_pos r_val) s s' t ∧
      t ≤ 7 ∧
      s'.arrs a_buf = (pfx ++ [val]) ++ List.replicate rem 0 ∧
      s'.regs r_pos = (pfx ++ [val]).length ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → s'.regs r = s.regs r) := by
  have hp0_w : pfx.length < 2 ^ w := by omega
  have hlen1 : pfx.length < (s.arrs a_buf).length := by simp [hbuf]
  let s₁ := s.writeArr a_buf pfx.length val
  have hex₁ : Exec w (.write a_buf (.reg r_pos) (.reg r_val)) s s₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hrpos, hp0_w])
      (by simp [Expr.eval, checkWord, hrval, hval_w]) hlen1
  have hbuf₁ : s₁.arrs a_buf = (pfx ++ [val]) ++ List.replicate rem 0 := by
    simp only [s₁, State.writeArr_arrs_self, hbuf]
    exact set_append_replicate_succ pfx rem val
  let s₂ := s₁.setReg r_pos (pfx.length + 1)
  have hex₂ : Exec w (.assign r_pos (.op .add (.reg r_pos) (.const 1))) s₁ s₂ 4 :=
    .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos, hp0_w, hw, hpos_w])
  refine ⟨s₂, 3 + 4, .seq hex₁ hex₂, by omega,
    by simpa [s₂] using hbuf₁,
    by simp [s₂],
    fun a ha => by simp [s₂, s₁, show (a : Arr) ≠ a_buf from ha],
    fun r hr => by simp [s₂, s₁, show (r : Reg) ≠ r_pos from hr]⟩

/-- Body of `bufAppendSlice`: read `a_src[r_src + r_j]` into `r_tmp` and push to `a_dst[r_pos]`. -/
def bufAppendSliceBody (a_src a_dst : Arr) (r_src r_pos r_j r_tmp : Reg) : Cmd :=
  .seq (.assign r_tmp (.read a_src (.op .add (.reg r_src) (.reg r_j))))
    (bufPush1 a_dst r_pos r_tmp)

/-- Append `r_n` words from `a_src` starting at offset `r_src` into `a_dst` starting at `r_pos`. -/
def bufAppendSlice (a_src a_dst : Arr) (r_src r_pos r_n r_j r_tmp : Reg) : Cmd :=
  .seq (.assign r_j (.const 0))
    (forUp r_j (.reg r_n) (bufAppendSliceBody a_src a_dst r_src r_pos r_j r_tmp))

theorem bufAppendSliceLoop_exec {w src_off n : ℕ} (a_src a_dst : ℕ)
    (r_src r_pos r_n r_j r_tmp : ℕ)
    (hne_sd : a_src ≠ a_dst)
    (hr_src_pos : r_src ≠ r_pos) (hr_src_j : r_src ≠ r_j) (hr_src_tmp : r_src ≠ r_tmp)
    (hr_n_pos : r_n ≠ r_pos) (hr_n_j : r_n ≠ r_j) (hr_n_tmp : r_n ≠ r_tmp)
    (hr_pos_j : r_pos ≠ r_j) (hr_pos_tmp : r_pos ≠ r_tmp)
    (hr_j_tmp : r_j ≠ r_tmp)
    (hw : 1 < 2 ^ w)
    (mid pre suf pfx : List ℕ) (k rem : ℕ)
    (hk_mid : k + mid.length = n)
    (hpre_len : pre.length = src_off + k)
    (hsrc_w : src_off + n < 2 ^ w)
    (hdst_w : pfx.length + mid.length < 2 ^ w)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = pre ++ mid ++ suf)
    (hdst : s.arrs a_dst = pfx ++ List.replicate (mid.length + rem) 0)
    (hrsrc : s.regs r_src = src_off)
    (hrpos : s.regs r_pos = pfx.length)
    (hrn : s.regs r_n = n)
    (hrj : s.regs r_j = k) :
    ∃ s' t,
      Exec w (forUp r_j (.reg r_n) (bufAppendSliceBody a_src a_dst r_src r_pos r_j r_tmp)) s s' t ∧
      t ≤ 3 + 19 * mid.length ∧
      s'.arrs a_dst = (pfx ++ mid) ++ List.replicate rem 0 ∧
      s'.regs r_pos = (pfx ++ mid).length ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → r ≠ r_j → r ≠ r_tmp → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction mid generalizing pre pfx k s with
  | nil =>
    have hk_eq : k = n := by simp at hk_mid; omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_j) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrn, hn_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by simp, by simpa using hdst,
      by simpa using hrpos, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | cons val rest ih =>
    simp only [List.length_cons] at hk_mid hdst hdst_w
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hsoff_w : src_off < 2 ^ w := by omega
    have hsoff_k_w : src_off + k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_j) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrn, hk_w, hn_w, hk_lt, hw]
    have hval_w : val < 2 ^ w := hmid_w val List.mem_cons_self
    have hsrc_split : s.arrs a_src = pre ++ val :: (rest ++ suf) := by
      simpa [List.append_assoc] using hsrc
    have hsrc_len : src_off + k < (s.arrs a_src).length := by
      rw [hsrc_split, List.length_append, List.length_cons]
      omega
    have hsrc_get : (s.arrs a_src)[src_off + k]'hsrc_len = val := by
      have hlen' : pre.length < (pre ++ val :: (rest ++ suf)).length := by
        rw [List.length_append, List.length_cons]; omega
      have hget := getElem_append_cons_length pre (rest ++ suf) val hlen'
      simp [hsrc_split, hpre_len]
    have heval_rd :
        (Expr.read a_src (.op .add (.reg r_src) (.reg r_j))).eval w s = some val := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrsrc, hrj, hsoff_w, hk_w,
        hsoff_k_w, hsrc_len, hsrc_get, hval_w]
    let s₁ := s.setReg r_tmp val
    have hex₁ : Exec w (.assign r_tmp (.read a_src (.op .add (.reg r_src) (.reg r_j)))) s s₁ 5 :=
      .assign heval_rd
    have hdst₁ : s₁.arrs a_dst = pfx ++ List.replicate ((rest.length + rem) + 1) 0 := by
      have hrep_eq : rest.length + 1 + rem = (rest.length + rem) + 1 := by omega
      simpa [s₁, hrep_eq] using hdst
    rcases bufPush1_exec a_dst r_pos r_tmp pfx (rest.length + rem) val hw (by omega) hval_w
        hdst₁ (by simp [s₁, hr_pos_tmp, hrpos]) (by simp [s₁]) with
      ⟨s₂, t₂, hex₂, ht₂, hdst₂, hrpos₂, harr₂, hreg₂⟩
    have hex_body : Exec w (bufAppendSliceBody a_src a_dst r_src r_pos r_j r_tmp) s s₂ (5 + t₂) :=
      .seq hex₁ hex₂
    have hrj₂ : s₂.regs r_j = k := by
      rw [hreg₂ r_j hr_pos_j.symm]
      simp [s₁, hr_j_tmp, hrj]
    have hinc : (Expr.op .add (.reg r_j) (.const 1)).eval w s₂ = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj₂, hk_w, hw,
        show k + 1 < 2 ^ w by omega]
    let s₃ := s₂.setReg r_j (k + 1)
    have hex_inc : Exec w (.assign r_j (.op .add (.reg r_j) (.const 1))) s₂ s₃ 4 :=
      .assign hinc
    have hsrc₃ : s₃.arrs a_src = (pre ++ [val]) ++ rest ++ suf := by
      simp [s₃, harr₂ a_src hne_sd, s₁, hsrc, List.append_assoc]
    have hdst₃ : s₃.arrs a_dst = (pfx ++ [val]) ++ List.replicate (rest.length + rem) 0 := by
      simpa [s₃] using hdst₂
    rcases ih (pre ++ [val]) (pfx ++ [val]) (k + 1) (by omega)
        (by simp [hpre_len]; omega)
        (by simp; omega)
        (fun x hx => hmid_w x (List.mem_cons_of_mem val hx))
        hsrc₃ hdst₃
        (by simp [s₃, hr_src_j, hreg₂ r_src hr_src_pos, s₁, hr_src_tmp, hrsrc])
        (by simp [s₃, hr_pos_j, hrpos₂])
        (by simp [s₃, hr_n_j, hreg₂ r_n hr_n_pos, s₁, hr_n_tmp, hrn])
        (by simp [s₃]) with
      ⟨s', t_rest, hex_rest, ht_rest, hdst', hrpos', harr', hreg'⟩
    refine ⟨s', 3 + ((5 + t₂) + 4) + t_rest,
      .while_true hcond (by omega) (.seq hex_body hex_inc) hex_rest,
      by simp only [List.length_cons]; omega,
      by simpa [List.append_assoc] using hdst',
      by simpa [List.append_assoc] using hrpos',
      fun a ha => by rw [harr' a ha, State.setReg_arrs, harr₂ a ha, State.setReg_arrs],
      fun r hr1 hr2 hr3 => by
        rw [hreg' r hr1 hr2 hr3]
        simp [s₃, s₁, hr2, hr3, hreg₂ r hr1]⟩

theorem bufAppendSlice_exec {w src_off n : ℕ} (a_src a_dst : ℕ)
    (r_src r_pos r_n r_j r_tmp : ℕ)
    (hne_sd : a_src ≠ a_dst)
    (hr_src_pos : r_src ≠ r_pos) (hr_src_j : r_src ≠ r_j) (hr_src_tmp : r_src ≠ r_tmp)
    (hr_n_pos : r_n ≠ r_pos) (hr_n_j : r_n ≠ r_j) (hr_n_tmp : r_n ≠ r_tmp)
    (hr_pos_j : r_pos ≠ r_j) (hr_pos_tmp : r_pos ≠ r_tmp)
    (hr_j_tmp : r_j ≠ r_tmp)
    (hw : 1 < 2 ^ w)
    (pre mid suf pfx : List ℕ) (rem : ℕ)
    (hpre_len : pre.length = src_off)
    (hmid_len : mid.length = n)
    (hsrc_w : src_off + n < 2 ^ w)
    (hdst_w : pfx.length + n < 2 ^ w)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = pre ++ mid ++ suf)
    (hdst : s.arrs a_dst = pfx ++ List.replicate (n + rem) 0)
    (hrsrc : s.regs r_src = src_off)
    (hrpos : s.regs r_pos = pfx.length)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (bufAppendSlice a_src a_dst r_src r_pos r_n r_j r_tmp) s s' t ∧
      t ≤ 5 + 19 * n ∧
      s'.arrs a_dst = (pfx ++ mid) ++ List.replicate rem 0 ∧
      s'.regs r_pos = (pfx ++ mid).length ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → r ≠ r_j → r ≠ r_tmp → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_j 0
  have hex₁ : Exec w (.assign r_j (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases bufAppendSliceLoop_exec a_src a_dst r_src r_pos r_n r_j r_tmp
      hne_sd hr_src_pos hr_src_j hr_src_tmp hr_n_pos hr_n_j hr_n_tmp
      hr_pos_j hr_pos_tmp hr_j_tmp hw mid pre suf pfx 0 rem
      (by omega) (by omega) hsrc_w (by omega) hmid_w (s := s₁)
      (by simpa [s₁] using hsrc)
      (by simpa [s₁, hmid_len] using hdst)
      (by simp [s₁, hr_src_j, hrsrc])
      (by simp [s₁, hr_pos_j, hrpos])
      (by simp [s₁, hr_n_j, hrn])
      (by simp [s₁]) with
    ⟨s', t₂, hex₂, ht₂, hdst', hrpos', harr', hreg'⟩
  refine ⟨s', 2 + t₂, .seq hex₁ hex₂, by omega, hdst', hrpos',
    fun a ha => by rw [harr' a ha]; rfl,
    fun r hr1 hr2 hr3 => by rw [hreg' r hr1 hr2 hr3]; simp [s₁, hr2]⟩

/-- Compare a constant list `ws : List ℕ` against `a_src[r_off + idx ..]`, setting `r_eq := 0`
on the first mismatch and stopping immediately. -/
def checkListAtOffset (a_src : Arr) (r_off r_eq r_tmp : Reg) : ℕ → List ℕ → Cmd
  | _, [] => .skip
  | idx, w₀ :: ws =>
    .seq (.assign r_tmp (.read a_src (.op .add (.reg r_off) (.const idx))))
      (.ite (.op .eq (.reg r_tmp) (.const w₀))
        (checkListAtOffset a_src r_off r_eq r_tmp (idx + 1) ws)
        (.assign r_eq (.const 0)))

theorem checkListAtOffset_exec {w off : ℕ} (a_src : ℕ) (r_off r_eq r_tmp : ℕ)
    (_hr_off_eq : r_off ≠ r_eq) (hr_off_tmp : r_off ≠ r_tmp) (hr_eq_tmp : r_eq ≠ r_tmp)
    (hw : 1 < 2 ^ w)
    (ws mid pre suf : List ℕ) (idx : ℕ)
    (hlen : mid.length = ws.length)
    (hpre_len : pre.length = off + idx)
    (hoff_w : off + idx + ws.length < 2 ^ w)
    (hidx_w : idx + ws.length < 2 ^ w)
    (hws_w : ∀ x ∈ ws, x < 2 ^ w)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = pre ++ mid ++ suf)
    (hroff : s.regs r_off = off)
    (hreq : s.regs r_eq = 1) :
    ∃ s' t,
      Exec w (checkListAtOffset a_src r_off r_eq r_tmp idx ws) s s' t ∧
      t ≤ 1 + 13 * ws.length ∧
      s'.regs r_eq = (if mid = ws then 1 else 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_eq → r ≠ r_tmp → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hoff0_w : off < 2 ^ w := by omega
  induction ws generalizing idx pre mid s with
  | nil =>
    have hmid_nil : mid = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hmid_nil
    refine ⟨s, 1, .skip s, by simp, by simp [hreq], fun _ => rfl, fun _ _ _ => rfl⟩
  | cons w₀ ws' ih =>
    rcases mid with _ | ⟨m₀, mid'⟩
    · simp at hlen
    simp only [List.length_cons] at hlen hoff_w hidx_w
    have hidx0_w : idx < 2 ^ w := by omega
    have hoff_idx_w : off + idx < 2 ^ w := by omega
    have hw0_w : w₀ < 2 ^ w := hws_w w₀ List.mem_cons_self
    have hm0_w : m₀ < 2 ^ w := hmid_w m₀ List.mem_cons_self
    have hsrc_split : s.arrs a_src = pre ++ m₀ :: (mid' ++ suf) := by
      simpa [List.append_assoc] using hsrc
    have hsrc_len : off + idx < (s.arrs a_src).length := by
      rw [hsrc_split, List.length_append, List.length_cons]; omega
    have hsrc_get : (s.arrs a_src)[off + idx]'hsrc_len = m₀ := by
      have hlen' : pre.length < (pre ++ m₀ :: (mid' ++ suf)).length := by
        rw [List.length_append, List.length_cons]; omega
      have hget := getElem_append_cons_length pre (mid' ++ suf) m₀ hlen'
      simp [hsrc_split, hpre_len]
    have heval_rd :
        (Expr.read a_src (.op .add (.reg r_off) (.const idx))).eval w s = some m₀ := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hroff, hoff0_w, hidx0_w,
        hoff_idx_w, hsrc_len, hsrc_get, hm0_w]
    let s₁ := s.setReg r_tmp m₀
    have hex₁ : Exec w (.assign r_tmp (.read a_src (.op .add (.reg r_off) (.const idx)))) s s₁ 5 :=
      .assign heval_rd
    by_cases heq : m₀ = w₀
    · subst heq
      have hcond : (Expr.op .eq (.reg r_tmp) (.const m₀)).eval w s₁ = some 1 := by
        simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hm0_w, hw]
      have hsrc₁ : s₁.arrs a_src = (pre ++ [m₀]) ++ mid' ++ suf := by
        simp [s₁, hsrc, List.append_assoc]
      rcases ih mid' (pre ++ [m₀]) (idx + 1) (by omega) (by simp [hpre_len]; omega)
          (by omega) (by omega)
          (fun x hx => hws_w x (List.mem_cons_of_mem m₀ hx))
          (fun x hx => hmid_w x (List.mem_cons_of_mem m₀ hx)) (s := s₁)
          hsrc₁ (by simp [s₁, hr_off_tmp, hroff]) (by simp [s₁, hr_eq_tmp, hreq]) with
        ⟨s', t_rest, hex_rest, ht_rest, hreq', harr', hreg'⟩
      refine ⟨s', 5 + (3 + t_rest), .seq hex₁ (.ite_true hcond (by omega) hex_rest),
        by simp only [List.length_cons]; omega,
        by simpa using hreq',
        fun a => by rw [harr' a]; rfl,
        fun r hr1 hr2 => by rw [hreg' r hr1 hr2]; simp [s₁, hr2]⟩
    · have hcond : (Expr.op .eq (.reg r_tmp) (.const w₀)).eval w s₁ = some 0 := by
        simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hm0_w, hw0_w, heq, h0_w]
      let s₂ := s₁.setReg r_eq 0
      have hex₂ : Exec w (.assign r_eq (.const 0)) s₁ s₂ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      refine ⟨s₂, 5 + (3 + 2), .seq hex₁ (.ite_false hcond hex₂),
        by simp only [List.length_cons]; omega,
        by simp [s₂, heq],
        fun _ => rfl,
        fun r hr1 hr2 => by simp [s₂, s₁, hr1, hr2]⟩

/-- Check whether the length-prefixed record `(c.length :: c)` at `r_off` in `a_src` equals
`targetCode`, storing `1` or `0` in `r_eq`. -/
def checkRecordMatch (a_src : Arr) (r_off r_eq r_tmp : Reg) (targetCode : List ℕ) : Cmd :=
  .seq (.assign r_eq (.const 1))
    (.seq (.assign r_tmp (.read a_src (.reg r_off)))
      (.ite (.op .eq (.reg r_tmp) (.const targetCode.length))
        (checkListAtOffset a_src r_off r_eq r_tmp 1 targetCode)
        (.assign r_eq (.const 0))))

theorem checkRecordMatch_exec {w off : ℕ} (a_src : ℕ) (r_off r_eq r_tmp : ℕ)
    (hr_off_eq : r_off ≠ r_eq) (hr_off_tmp : r_off ≠ r_tmp) (hr_eq_tmp : r_eq ≠ r_tmp)
    (hw : 1 < 2 ^ w)
    (targetCode c pre suf : List ℕ)
    (hpre_len : pre.length = off)
    (hoff_w : off + 1 + targetCode.length < 2 ^ w)
    (hclen_w : c.length < 2 ^ w)
    (htarget_w : ∀ x ∈ targetCode, x < 2 ^ w)
    (hc_w : ∀ x ∈ c, x < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = pre ++ (c.length :: c) ++ suf)
    (hroff : s.regs r_off = off) :
    ∃ s' t,
      Exec w (checkRecordMatch a_src r_off r_eq r_tmp targetCode) s s' t ∧
      t ≤ 12 + 13 * targetCode.length ∧
      s'.regs r_eq = (if c = targetCode then 1 else 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_eq → r ≠ r_tmp → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hoff0_w : off < 2 ^ w := by omega
  have htlen_w : targetCode.length < 2 ^ w := by omega
  let s₁ := s.setReg r_eq 1
  have hex₁ : Exec w (.assign r_eq (.const 1)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hsrc_split : s.arrs a_src = pre ++ c.length :: (c ++ suf) := by
    simpa [List.append_assoc] using hsrc
  have hsrc_len : off < (s.arrs a_src).length := by
    rw [hsrc_split, List.length_append, List.length_cons]; omega
  have hsrc_get : (s.arrs a_src)[off]'hsrc_len = c.length := by
    simp [hsrc_split, hpre_len]
  have heval_rd : (Expr.read a_src (.reg r_off)).eval w s₁ = some c.length := by
    simp [s₁, Expr.eval, checkWord, hr_off_eq, hroff, hoff0_w, hsrc_len, hsrc_get, hclen_w]
  let s₂ := s₁.setReg r_tmp c.length
  have hex₂ : Exec w (.assign r_tmp (.read a_src (.reg r_off))) s₁ s₂ 3 :=
    .assign heval_rd
  by_cases hlen_eq : c.length = targetCode.length
  · have hcond : (Expr.op .eq (.reg r_tmp) (.const targetCode.length)).eval w s₂ = some 1 := by
      simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hlen_eq, htlen_w, hw]
    have hsrc₂ : s₂.arrs a_src = (pre ++ [c.length]) ++ c ++ suf := by
      simp [s₂, s₁, hsrc, List.append_assoc]
    rcases checkListAtOffset_exec a_src r_off r_eq r_tmp hr_off_eq hr_off_tmp hr_eq_tmp hw
        targetCode c (pre ++ [c.length]) suf 1 hlen_eq (by simp [hpre_len])
        hoff_w (by omega) htarget_w hc_w (s := s₂) hsrc₂
        (by simp [s₂, s₁, hr_off_tmp, hr_off_eq, hroff])
        (by simp [s₂, s₁, hr_eq_tmp]) with
      ⟨s', t_rest, hex_rest, ht_rest, hreq', harr', hreg'⟩
    refine ⟨s', 2 + (3 + (3 + t_rest)),
      .seq hex₁ (.seq hex₂ (.ite_true hcond (by omega) hex_rest)),
      by omega, hreq',
      fun a => by rw [harr' a]; rfl,
      fun r hr1 hr2 => by rw [hreg' r hr1 hr2]; simp [s₂, s₁, hr1, hr2]⟩
  · have hne_code : c ≠ targetCode := fun h => hlen_eq (congrArg List.length h)
    have hcond : (Expr.op .eq (.reg r_tmp) (.const targetCode.length)).eval w s₂ = some 0 := by
      simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hclen_w, htlen_w, hlen_eq, h0_w]
    let s₃ := s₂.setReg r_eq 0
    have hex₃ : Exec w (.assign r_eq (.const 0)) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    refine ⟨s₃, 2 + (3 + (3 + 2)),
      .seq hex₁ (.seq hex₂ (.ite_false hcond hex₃)),
      by omega,
      by simp [s₃, hne_code],
      fun _ => rfl,
      fun r hr1 hr2 => by simp [s₃, s₂, s₁, hr1, hr2]⟩

/-! ### Section 7: Permuted Model Writing and Target Model Extraction on the Word RAM -/

theorem models_getElem_tail {n : ℕ} {H : ComputeRootedDigraph 0} {G : MultiDigraph n}
    (M : RootedDigraphModel H (G.toMultiComputeRootedDigraph []))
    (pre suf : List ℕ) (m_off : ℕ) (hpre : pre.length = m_off)
    (e : Fin H.digraph.numEdges) :
    (pre ++ ((encRootedDigraphModel M).length :: encRootedDigraphModel M) ++ suf)[m_off + (3 + 2 * e.1)]? =
      some (G.edgeEndpoints (M.edgeMap e)).1.1 := by
  have hlen_M := length_encRootedDigraphModel M
  have he := e.2
  have hsub : m_off + (3 + 2 * e.1) - pre.length = (2 + 2 * e.1) + 1 := by omega
  rw [List.append_assoc, List.getElem?_append_right (by omega), hsub,
    List.cons_append, List.getElem?_cons_succ,
    List.getElem?_append_left (by simp [hlen_M]; omega)]
  exact encRootedDigraphModel_getElem_tail M e

theorem models_getElem_head {n : ℕ} {H : ComputeRootedDigraph 0} {G : MultiDigraph n}
    (M : RootedDigraphModel H (G.toMultiComputeRootedDigraph []))
    (pre suf : List ℕ) (m_off : ℕ) (hpre : pre.length = m_off)
    (e : Fin H.digraph.numEdges) :
    (pre ++ ((encRootedDigraphModel M).length :: encRootedDigraphModel M) ++ suf)[m_off + (3 + 2 * e.1 + 1)]? =
      some (G.edgeEndpoints (M.edgeMap e)).2.1 := by
  have hlen_M := length_encRootedDigraphModel M
  have he := e.2
  have hsub : m_off + (3 + 2 * e.1 + 1) - pre.length = (2 + 2 * e.1 + 1) + 1 := by omega
  rw [List.append_assoc, List.getElem?_append_right (by omega), hsub,
    List.cons_append, List.getElem?_cons_succ,
    List.getElem?_append_left (by simp [hlen_M]; omega)]
  exact encRootedDigraphModel_getElem_head M e

theorem models_vertSlice {n : ℕ} {H : ComputeRootedDigraph 0} {G : MultiDigraph n}
    (M : RootedDigraphModel H (G.toMultiComputeRootedDigraph []))
    (pre suf : List ℕ) (m_off : ℕ) (hpre : pre.length = m_off)
    (u : Fin H.digraph.numVerts) :
    ∃ pre' suf' : List ℕ,
      pre ++ ((encRootedDigraphModel M).length :: encRootedDigraphModel M) ++ suf =
        pre' ++ bitSetList (M.vertMap u).verts ++ suf' ∧
      pre'.length = (m_off + (3 + 2 * H.digraph.numEdges)) + u.1 * n := by
  rcases encRootedDigraphModel_vertSlice M u with ⟨pre_u, suf_u, hM, hpre_u⟩
  refine ⟨pre ++ [(encRootedDigraphModel M).length] ++ pre_u, suf_u ++ suf, ?_, ?_⟩
  · rw [hM]; simp [List.append_assoc]
  · simp [hpre, hpre_u]; omega

/-- Copy permuted edge endpoint pairs from `a_models` (at record offset `r_base + 4`) into `a_out`
(at write offset `r_base + 7`), using scratch registers `r_base + 8` and `r_base + 9`. Each entry
`(eIdx, swap)` in `fe` specifies the edge index `eIdx` in `encRootedDigraphModel` and whether to
swap its `(tail, head)` endpoints (`swap = true`). -/
def copyPermutedEdgesProg (a_models a_out : Arr) (r_base : Reg) : List (ℕ × Bool) → Cmd
  | [] => .skip
  | (eIdx, swap) :: rest =>
    let off1 := if swap then 3 + 2 * eIdx + 1 else 3 + 2 * eIdx
    let off2 := if swap then 3 + 2 * eIdx else 3 + 2 * eIdx + 1
    .seq (.assign (r_base + 8)
        (.read a_models (.op .add (.reg (r_base + 4)) (.const off1))))
      (.seq (.assign (r_base + 9)
          (.read a_models (.op .add (.reg (r_base + 4)) (.const off2))))
        (.seq (bufPush2 a_out (r_base + 7) (r_base + 8) (r_base + 9))
          (copyPermutedEdgesProg a_models a_out r_base rest)))

theorem copyPermutedEdgesProg_exec {w n m_off : ℕ} {H : ComputeRootedDigraph 0}
    {G : MultiDigraph n} (M : RootedDigraphModel H (G.toMultiComputeRootedDigraph []))
    (a_models a_out r_base : ℕ)
    (hne_mo : a_models ≠ a_out)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hmoff_w : m_off + 3 + 2 * H.digraph.numEdges < 2 ^ w)
    (pre suf : List ℕ) (hpre : pre.length = m_off)
    (fe : List (Fin H.digraph.numEdges × Bool))
    (pfx : List ℕ) (rem : ℕ)
    (hpfx_w : pfx.length + 2 * fe.length < 2 ^ w)
    {s : State}
    (hmodels : s.arrs a_models =
      pre ++ ((encRootedDigraphModel M).length :: encRootedDigraphModel M) ++ suf)
    (hout : s.arrs a_out = pfx ++ List.replicate (2 * fe.length + rem) 0)
    (hrmoff : s.regs (r_base + 4) = m_off)
    (hrpos : s.regs (r_base + 7) = pfx.length) :
    ∃ s' t,
      Exec w (copyPermutedEdgesProg a_models a_out r_base
        (fe.map (fun p => (p.1.1, p.2)))) s s' t ∧
      t ≤ 1 + 26 * fe.length ∧
      s'.arrs a_out =
        (pfx ++ fe.flatMap (fun p =>
          let ep := if p.2 then (G.edgeEndpoints (M.edgeMap p.1)).swap
            else G.edgeEndpoints (M.edgeMap p.1)
          [ep.1.1, ep.2.1])) ++ List.replicate rem 0 ∧
      s'.regs (r_base + 7) =
        (pfx ++ fe.flatMap (fun p =>
          let ep := if p.2 then (G.edgeEndpoints (M.edgeMap p.1)).swap
            else G.edgeEndpoints (M.edgeMap p.1)
          [ep.1.1, ep.2.1])).length ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 7, s'.regs r = s.regs r) := by
  have hmoff0_w : m_off < 2 ^ w := by omega
  induction fe generalizing pfx s with
  | nil =>
    refine ⟨s, 1, .skip s, by simp, by simpa using hout, by simpa using hrpos,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | cons p rest ih =>
    rcases p with ⟨e, swap⟩
    simp only [List.length_cons] at hpfx_w hout
    have he := e.2
    have hc1_w : 3 + 2 * e.1 < 2 ^ w := by omega
    have hc2_w : 3 + 2 * e.1 + 1 < 2 ^ w := by omega
    have hidx1_w : m_off + (3 + 2 * e.1) < 2 ^ w := by omega
    have hidx2_w : m_off + (3 + 2 * e.1 + 1) < 2 ^ w := by omega
    let off1 := if swap then 3 + 2 * e.1 + 1 else 3 + 2 * e.1
    let off2 := if swap then 3 + 2 * e.1 else 3 + 2 * e.1 + 1
    let ep := if swap then (G.edgeEndpoints (M.edgeMap e)).swap else G.edgeEndpoints (M.edgeMap e)
    let u := ep.1.1
    let v := ep.2.1
    have hoff1_w : off1 < 2 ^ w := by dsimp [off1]; split_ifs <;> omega
    have hoff2_w : off2 < 2 ^ w := by dsimp [off2]; split_ifs <;> omega
    have hmoff1_w : m_off + off1 < 2 ^ w := by dsimp [off1]; split_ifs <;> omega
    have hmoff2_w : m_off + off2 < 2 ^ w := by dsimp [off2]; split_ifs <;> omega
    have hu_w : u < 2 ^ w := Nat.lt_trans ep.1.2 hn_w
    have hv_w : v < 2 ^ w := Nat.lt_trans ep.2.2 hn_w
    have hget_u : (s.arrs a_models)[m_off + off1]? = some u := by
      rw [hmodels]
      dsimp [off1, u, ep]
      cases swap
      · exact models_getElem_tail M pre suf m_off hpre e
      · exact models_getElem_head M pre suf m_off hpre e
    rcases List.getElem?_eq_some_iff.mp hget_u with ⟨hlen_u, hval_u⟩
    have heval_u :
        (Expr.read a_models (.op .add (.reg (r_base + 4)) (.const off1))).eval w s =
          some u := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrmoff, hmoff0_w, hoff1_w,
        hmoff1_w, hlen_u, hval_u, hu_w]
    let s₁ := s.setReg (r_base + 8) u
    have hex₁ :
        Exec w (.assign (r_base + 8)
          (.read a_models (.op .add (.reg (r_base + 4)) (.const off1)))) s s₁ 5 :=
      .assign heval_u
    have hget_v : (s.arrs a_models)[m_off + off2]? = some v := by
      rw [hmodels]
      dsimp [off2, v, ep]
      cases swap
      · exact models_getElem_head M pre suf m_off hpre e
      · exact models_getElem_tail M pre suf m_off hpre e
    rcases List.getElem?_eq_some_iff.mp hget_v with ⟨hlen_v, hval_v⟩
    have heval_v :
        (Expr.read a_models (.op .add (.reg (r_base + 4)) (.const off2))).eval w s₁ =
          some v := by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrmoff, hmoff0_w, hoff2_w,
        hmoff2_w, hlen_v, hval_v, hv_w]
    let s₂ := s₁.setReg (r_base + 9) v
    have hex₂ :
        Exec w (.assign (r_base + 9)
          (.read a_models (.op .add (.reg (r_base + 4)) (.const off2)))) s₁ s₂ 5 :=
      .assign heval_v
    have hout₂ : s₂.arrs a_out = pfx ++ List.replicate ((2 * rest.length + rem) + 2) 0 := by
      have hrep : 2 * (rest.length + 1) + rem = (2 * rest.length + rem) + 2 := by omega
      simpa [s₂, s₁, hrep] using hout
    rcases bufPush2_exec a_out (r_base + 7) (r_base + 8) (r_base + 9)
        pfx (2 * rest.length + rem) u v hw2 (by omega) hu_w hv_w
        hout₂ (by simp [s₂, s₁, hrpos]) (by simp [s₂, s₁]) (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, hout₃, hrpos₃, harr₃, hreg₃⟩
    have hmodels₃ : s₃.arrs a_models =
        pre ++ ((encRootedDigraphModel M).length :: encRootedDigraphModel M) ++ suf := by
      rw [harr₃ a_models hne_mo]; exact hmodels
    rcases ih (pfx ++ [u, v]) (by simp; omega) hmodels₃ hout₃
        (by rw [hreg₃ (r_base + 4) (by omega)]; simp [s₂, s₁, hrmoff])
        hrpos₃ with
      ⟨s', t_rest, hex_rest, ht_rest, hout', hrpos', harr', hreg'⟩
    refine ⟨s', 5 + (5 + (t₃ + t_rest)),
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex_rest)),
      by simp only [List.length_cons]; omega,
      by simpa [List.append_assoc, u, v, ep] using hout',
      by simpa [List.append_assoc, u, v, ep] using hrpos',
      fun a ha => by rw [harr' a ha, harr₃ a ha]; rfl,
      fun r hr => by
        rw [hreg' r hr, hreg₃ r (by omega)]
        simp [s₂, s₁, show r ≠ r_base + 8 by omega, show r ≠ r_base + 9 by omega]⟩

/-- Copy permuted vertex indicator bitsets of length `r_base` (`n`) from `a_models` (at record
offset `r_base + 4`) into `a_out` (at write offset `r_base + 7`), using scratch registers
`r_base + 8 .. r_base + 10`. -/
def copyPermutedVertsProg (m : ℕ) (a_models a_out : Arr) (r_base : Reg) : List ℕ → Cmd
  | [] => .skip
  | vIdx :: rest =>
    .seq (.assign (r_base + 8)
        (.op .add (.op .add (.reg (r_base + 4)) (.const (3 + 2 * m)))
          (.op .mul (.const vIdx) (.reg r_base))))
      (.seq (bufAppendSlice a_models a_out (r_base + 8) (r_base + 7)
          r_base (r_base + 9) (r_base + 10))
        (copyPermutedVertsProg m a_models a_out r_base rest))

theorem copyPermutedVertsProg_exec {w n m_off : ℕ} {H : ComputeRootedDigraph 0}
    {G : MultiDigraph n} (M : RootedDigraphModel H (G.toMultiComputeRootedDigraph []))
    (a_models a_out r_base : ℕ)
    (hne_mo : a_models ≠ a_out)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hmoff_w : m_off + 3 + 2 * H.digraph.numEdges + H.digraph.numVerts * n < 2 ^ w)
    (hv_w : H.digraph.numVerts < 2 ^ w)
    (pre suf : List ℕ) (hpre : pre.length = m_off)
    (fv : List (Fin H.digraph.numVerts))
    (pfx : List ℕ) (rem : ℕ)
    (hpfx_w : pfx.length + fv.length * n < 2 ^ w)
    {s : State}
    (hmodels : s.arrs a_models =
      pre ++ ((encRootedDigraphModel M).length :: encRootedDigraphModel M) ++ suf)
    (hout : s.arrs a_out = pfx ++ List.replicate (fv.length * n + rem) 0)
    (hrn : s.regs r_base = n)
    (hrmoff : s.regs (r_base + 4) = m_off)
    (hrpos : s.regs (r_base + 7) = pfx.length) :
    ∃ s' t,
      Exec w (copyPermutedVertsProg H.digraph.numEdges a_models a_out r_base (fv.map Fin.val))
        s s' t ∧
      t ≤ 1 + (13 + 19 * n) * fv.length ∧
      s'.arrs a_out =
        (pfx ++ fv.flatMap (fun u => bitSetList (M.vertMap u).verts)) ++ List.replicate rem 0 ∧
      s'.regs (r_base + 7) =
        (pfx ++ fv.flatMap (fun u => bitSetList (M.vertMap u).verts)).length ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 7, s'.regs r = s.regs r) := by
  have hmoff0_w : m_off < 2 ^ w := by omega
  have hc_hdr_w : 3 + 2 * H.digraph.numEdges < 2 ^ w := by omega
  have hmoff_hdr_w : m_off + (3 + 2 * H.digraph.numEdges) < 2 ^ w := by omega
  induction fv generalizing pfx s with
  | nil =>
    refine ⟨s, 1, .skip s, by simp, by simpa using hout, by simpa using hrpos,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | cons u rest ih =>
    simp only [List.length_cons] at hpfx_w hout
    have hu_lt := u.2
    have hu_w : u.1 < 2 ^ w := by omega
    have hu1_le : (u.1 + 1) * n ≤ H.digraph.numVerts * n :=
      Nat.mul_le_mul_right n (by omega)
    have hun_eq : (u.1 + 1) * n = u.1 * n + n := by ring
    have hun_w : u.1 * n < 2 ^ w := by omega
    let src_off := (m_off + (3 + 2 * H.digraph.numEdges)) + u.1 * n
    have hsrc_off_w : src_off < 2 ^ w := by dsimp [src_off]; omega
    have hsrc_n_w : src_off + n < 2 ^ w := by dsimp [src_off]; omega
    have heval_src :
        (Expr.op .add (.op .add (.reg (r_base + 4)) (.const (3 + 2 * H.digraph.numEdges)))
          (.op .mul (.const u.1) (.reg r_base))).eval w s = some src_off := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrmoff, hrn, hmoff0_w, hc_hdr_w,
        hmoff_hdr_w, hu_w, hn_w, hun_w, src_off, hsrc_off_w]
    let s₁ := s.setReg (r_base + 8) src_off
    have hex₁ :
        Exec w (.assign (r_base + 8)
          (.op .add (.op .add (.reg (r_base + 4)) (.const (3 + 2 * H.digraph.numEdges)))
            (.op .mul (.const u.1) (.reg r_base)))) s s₁ 8 :=
      .assign heval_src
    rcases models_vertSlice M pre suf m_off hpre u with ⟨pre', suf', hslice, hpre'_len⟩
    have hmodels₁ : s₁.arrs a_models = pre' ++ bitSetList (M.vertMap u).verts ++ suf' := by
      simpa [s₁, hmodels] using hslice
    have hout₁ : s₁.arrs a_out = pfx ++ List.replicate (n + (rest.length * n + rem)) 0 := by
      have hrep : (rest.length + 1) * n + rem = n + (rest.length * n + rem) := by ring
      simpa [s₁, hrep] using hout
    have hlen_bs : (bitSetList (M.vertMap u).verts).length = n :=
      length_bitSetList (M.vertMap u).verts
    have hbs_w : ∀ x ∈ bitSetList (M.vertMap u).verts, x < 2 ^ w := by
      intro x hx
      rcases List.mem_iff_getElem.mp hx with ⟨idx, hidx, rfl⟩
      have := getElem_bitSetList_le_one (M.vertMap u).verts idx hidx
      omega
    have hpfx_n_w : pfx.length + n < 2 ^ w := by
      have : n ≤ (rest.length + 1) * n := Nat.le_mul_of_pos_left n (by omega)
      omega
    rcases bufAppendSlice_exec a_models a_out (r_base + 8) (r_base + 7)
        r_base (r_base + 9) (r_base + 10)
        hne_mo (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) hw
        pre' (bitSetList (M.vertMap u).verts) suf' pfx (rest.length * n + rem)
        hpre'_len hlen_bs hsrc_n_w hpfx_n_w hbs_w (s := s₁)
        hmodels₁ hout₁ (by simp [s₁]; rfl) (by simp [s₁, hrpos]) (by simp [s₁, hrn]) with
      ⟨s₂, t₂, hex₂, ht₂, hout₂, hrpos₂, harr₂, hreg₂⟩
    have hmodels₂ : s₂.arrs a_models =
        pre ++ ((encRootedDigraphModel M).length :: encRootedDigraphModel M) ++ suf := by
      rw [harr₂ a_models hne_mo]; exact hmodels
    have hpfx2_w : (pfx ++ bitSetList (M.vertMap u).verts).length + rest.length * n < 2 ^ w := by
      rw [List.length_append, hlen_bs]
      have hmul : (rest.length + 1) * n = n + rest.length * n := by ring
      omega
    rcases ih (pfx ++ bitSetList (M.vertMap u).verts) hpfx2_w hmodels₂ hout₂
        (by rw [hreg₂ r_base (by omega) (by omega) (by omega)]; simp [s₁, hrn])
        (by rw [hreg₂ (r_base + 4) (by omega) (by omega) (by omega)]; simp [s₁, hrmoff])
        hrpos₂ with
      ⟨s', t_rest, hex_rest, ht_rest, hout', hrpos', harr', hreg'⟩
    have ht_step : 8 + (t₂ + t_rest) ≤ 1 + (13 + 19 * n) * (rest.length + 1) := by
      have hmul : (13 + 19 * n) * (rest.length + 1) =
          (13 + 19 * n) * rest.length + 13 + 19 * n := by ring
      omega
    refine ⟨s', 8 + (t₂ + t_rest), .seq hex₁ (.seq hex₂ hex_rest),
      by simpa only [List.length_cons] using ht_step,
      by simpa [List.append_assoc] using hout',
      by simpa [List.append_assoc] using hrpos',
      fun a ha => by rw [harr' a ha, harr₂ a ha]; rfl,
      fun r hr => by
        rw [hreg' r hr, hreg₂ r (by omega) (by omega) (by omega)]
        simp [s₁, show r ≠ r_base + 8 by omega]⟩

/-- Allocate `a_out` of size `3 + 2 * m + p * n`, write `[1, p, m]`, and copy the permuted edges
`fe` and permuted vertex bitsets `fv` from the model record at `r_base + 4` in `a_models`. -/
def writeIsoModelProg (p m : ℕ) (fe : List (ℕ × Bool)) (fv : List ℕ)
    (a_models a_out : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 7)
      (.op .add (.const (3 + 2 * m)) (.op .mul (.const p) (.reg r_base))))
    (.seq (.alloc a_out (.reg (r_base + 7)))
      (.seq (.assign (r_base + 7) (.const 0))
        (.seq (.assign (r_base + 8) (.const 1))
          (.seq (.assign (r_base + 9) (.const p))
            (.seq (.assign (r_base + 10) (.const m))
              (.seq (bufPush3 a_out (r_base + 7) (r_base + 8) (r_base + 9) (r_base + 10))
                (.seq (copyPermutedEdgesProg a_models a_out r_base fe)
                  (copyPermutedVertsProg m a_models a_out r_base fv))))))))

theorem writeIsoModelProg_exec {w p n m_off : ℕ}
    (edgesH : List (Fin p × Fin p))
    (flips : Fin edgesH.length → Bool)
    {H : ComputeRootedDigraph 0} {G : MultiDigraph n}
    (iso : RootedDigraphIso (targetToOrientedComputeRootedDigraph p edgesH flips) H)
    (M : RootedDigraphModel H (G.toMultiComputeRootedDigraph []))
    (fe : List (ℕ × Bool)) (fv : List ℕ)
    (hfe : fe = (List.finRange edgesH.length).map (fun k => ((iso.edgeEquiv k).1, flips k)))
    (hfv : fv = (List.finRange p).map (fun u => (iso.vertEquiv u).1))
    (a_models a_out r_base : ℕ)
    (hne_mo : a_models ≠ a_out)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hp_w : p < 2 ^ w)
    (hout_len_w : 3 + 2 * edgesH.length + p * n < 2 ^ w)
    (hmoff_w : m_off + 3 + 2 * edgesH.length + p * n < 2 ^ w)
    (pre suf : List ℕ) (hpre : pre.length = m_off)
    {s : State}
    (hmodels : s.arrs a_models =
      pre ++ ((encRootedDigraphModel M).length :: encRootedDigraphModel M) ++ suf)
    (hrn : s.regs r_base = n)
    (hrmoff : s.regs (r_base + 4) = m_off) :
    ∃ s' t,
      Exec w (writeIsoModelProg p edgesH.length fe fv a_models a_out r_base) s s' t ∧
      t ≤ 40 + 28 * edgesH.length + (14 + 20 * n) * p ∧
      s'.arrs a_out =
        [1] ++ (MultiDigraphModel.ofOrientedRootedDigraphModel flips (M.ofIsoLeft iso)).enc ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 7, s'.regs r = s.regs r) := by
  let m := edgesH.length
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm_w : m < 2 ^ w := by omega
  have hc_hdr_w : 3 + 2 * m < 2 ^ w := by omega
  have hpn_w : p * n < 2 ^ w := by omega
  have hv_eq : H.digraph.numVerts = p := by
    have hcard := Fintype.card_congr iso.vertEquiv
    simpa using hcard.symm
  have hm_eq : H.digraph.numEdges = m := by
    have hcard := Fintype.card_congr iso.edgeEquiv
    simpa [m] using hcard.symm
  let alloc_sz := (3 + 2 * m) + p * n
  have halloc_w : alloc_sz < 2 ^ w := hout_len_w
  have heval_sz :
      (Expr.op .add (.const (3 + 2 * m)) (.op .mul (.const p) (.reg r_base))).eval w s =
        some alloc_sz := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn, hc_hdr_w, hp_w, hn_w,
      hpn_w, alloc_sz, halloc_w]
  let s₁ := s.setReg (r_base + 7) alloc_sz
  have hex₁ :
      Exec w (.assign (r_base + 7)
        (.op .add (.const (3 + 2 * m)) (.op .mul (.const p) (.reg r_base)))) s s₁ 6 :=
    .assign heval_sz
  let s₂ := s₁.setArr a_out (List.replicate alloc_sz 0)
  have hex₂ : Exec w (.alloc a_out (.reg (r_base + 7))) s₁ s₂ (1 + alloc_sz) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, halloc_w])
  let s₃ := s₂.setReg (r_base + 7) 0
  have hex₃ : Exec w (.assign (r_base + 7) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg (r_base + 8) 1
  have hex₄ : Exec w (.assign (r_base + 8) (.const 1)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₅ := s₄.setReg (r_base + 9) p
  have hex₅ : Exec w (.assign (r_base + 9) (.const p)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hp_w])
  let s₆ := s₅.setReg (r_base + 10) m
  have hex₆ : Exec w (.assign (r_base + 10) (.const m)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hm_w])
  have hout₆ : s₆.arrs a_out = ([] : List ℕ) ++ List.replicate ((2 * m + p * n) + 3) 0 := by
    have hrep : alloc_sz = (2 * m + p * n) + 3 := by dsimp [alloc_sz]; omega
    simp [s₆, s₅, s₄, s₃, s₂, hrep]
  rcases bufPush3_exec a_out (r_base + 7) (r_base + 8) (r_base + 9) (r_base + 10)
      [] (2 * m + p * n) 1 p m hw3 (by simp; omega) hw hp_w hm_w
      hout₆ (by simp [s₆, s₅, s₄, s₃]) (by simp [s₆, s₅, s₄])
      (by simp [s₆, s₅]) (by simp [s₆]) with
    ⟨s₇, t₇, hex₇, ht₇, hout₇, hrpos₇, harr₇, hreg₇⟩
  let feFin : List (Fin H.digraph.numEdges × Bool) :=
    (List.finRange m).map (fun k => (iso.edgeEquiv k, flips k))
  have hfe_map : fe = feFin.map (fun p => (p.1.1, p.2)) := by
    rw [hfe]
    simp [feFin, List.map_map, Function.comp_def, m]
  have hfeFin_len : feFin.length = m := by simp [feFin]
  have hmodels₇ : s₇.arrs a_models =
      pre ++ ((encRootedDigraphModel M).length :: encRootedDigraphModel M) ++ suf := by
    rw [harr₇ a_models hne_mo]
    simp [s₆, s₅, s₄, s₃, s₂, State.setArr_arrs_ne _ _ hne_mo, s₁, hmodels]
  have hout₇' : s₇.arrs a_out = [1, p, m] ++ List.replicate (2 * feFin.length + p * n) 0 := by
    simpa [hfeFin_len] using hout₇
  rcases copyPermutedEdgesProg_exec M a_models a_out r_base hne_mo hw2 hn_w
      (by omega) pre suf hpre feFin [1, p, m] (p * n) (by simp [hfeFin_len]; omega)
      hmodels₇ hout₇'
      (by rw [hreg₇ (r_base + 4) (by omega)]; simp [s₆, s₅, s₄, s₃, s₂, s₁, hrmoff])
      (by simpa using hrpos₇) with
    ⟨s₈, t₈, hex₈, ht₈, hout₈, hrpos₈, harr₈, hreg₈⟩
  rw [← hfe_map] at hex₈
  let fvFin : List (Fin H.digraph.numVerts) := (List.finRange p).map iso.vertEquiv
  have hfv_map : fv = fvFin.map Fin.val := by
    rw [hfv]
    simp [fvFin, List.map_map, Function.comp_def]
  have hfvFin_len : fvFin.length = p := by simp [fvFin]
  have hmodels₈ : s₈.arrs a_models =
      pre ++ ((encRootedDigraphModel M).length :: encRootedDigraphModel M) ++ suf := by
    rw [harr₈ a_models hne_mo]; exact hmodels₇
  let pfx₈ := [1, p, m] ++ feFin.flatMap (fun q =>
    let ep := if q.2 then (G.edgeEndpoints (M.edgeMap q.1)).swap
      else G.edgeEndpoints (M.edgeMap q.1)
    [ep.1.1, ep.2.1])
  have hpfx₈_len : pfx₈.length = 3 + 2 * m := by
    have hflat_len := length_flatMap_edges
      (fun k : Fin m =>
        (if flips k then (G.edgeEndpoints (M.edgeMap (iso.edgeEquiv k))).swap
         else G.edgeEndpoints (M.edgeMap (iso.edgeEquiv k))).1)
      (fun k : Fin m =>
        (if flips k then (G.edgeEndpoints (M.edgeMap (iso.edgeEquiv k))).swap
         else G.edgeEndpoints (M.edgeMap (iso.edgeEquiv k))).2)
    dsimp [pfx₈, feFin]
    rw [List.flatMap_map, hflat_len]
    omega
  have hout₈' : s₈.arrs a_out = pfx₈ ++ List.replicate (fvFin.length * n + 0) 0 := by
    simpa [pfx₈, hfvFin_len] using hout₈
  rcases copyPermutedVertsProg_exec M a_models a_out r_base hne_mo hw hn_w
      (by rw [hv_eq, hm_eq]; exact hmoff_w) (by omega) pre suf hpre fvFin pfx₈ 0
      (by rw [hpfx₈_len, hfvFin_len]; omega)
      hmodels₈ hout₈'
      (by rw [hreg₈ r_base (by omega), hreg₇ r_base (by omega)]
          simp [s₆, s₅, s₄, s₃, s₂, s₁, hrn])
      (by rw [hreg₈ (r_base + 4) (by omega), hreg₇ (r_base + 4) (by omega)]
          simp [s₆, s₅, s₄, s₃, s₂, s₁, hrmoff])
      hrpos₈ with
    ⟨s', t₉, hex₉, ht₉, hout₉, _, harr₉, hreg₉⟩
  rw [← hfv_map, hm_eq] at hex₉
  have hout_eq :
      s'.arrs a_out =
        [1] ++ (MultiDigraphModel.ofOrientedRootedDigraphModel flips (M.ofIsoLeft iso)).enc := by
    unfold MultiDigraphModel.enc MultiDigraphModel.ofOrientedRootedDigraphModel
    have h1 :
        feFin.flatMap (fun q =>
          let ep := if q.2 then (G.edgeEndpoints (M.edgeMap q.1)).swap
            else G.edgeEndpoints (M.edgeMap q.1)
          [ep.1.1, ep.2.1]) =
        (List.finRange m).flatMap (fun k =>
          [(if flips k then (G.edgeEndpoints ((M.ofIsoLeft iso).edgeMap k)).swap
            else G.edgeEndpoints ((M.ofIsoLeft iso).edgeMap k)).1.1,
           (if flips k then (G.edgeEndpoints ((M.ofIsoLeft iso).edgeMap k)).swap
            else G.edgeEndpoints ((M.ofIsoLeft iso).edgeMap k)).2.1]) := by
      simp [feFin, List.flatMap_map, RootedDigraphModel.ofIsoLeft]
    have h2 :
        fvFin.flatMap (fun u => bitSetList (M.vertMap u).verts) =
        (List.finRange p).flatMap (fun u =>
          bitSetList ((M.ofIsoLeft iso).vertMap u).verts) := by
      simp [fvFin, List.flatMap_map, RootedDigraphModel.ofIsoLeft]
    simpa [pfx₈, h1, h2, List.append_assoc, m] using hout₉
  have ht_total :
      6 + ((1 + alloc_sz) + (2 + (2 + (2 + (2 + (t₇ + (t₈ + t₉))))))) ≤
        40 + 28 * m + (14 + 20 * n) * p := by
    dsimp [alloc_sz]
    rw [hfeFin_len] at ht₈
    rw [hfvFin_len] at ht₉
    have hmul : (14 + 20 * n) * p = 14 * p + 20 * (p * n) := by ring
    have hmul9 : (13 + 19 * n) * p = 13 * p + 19 * (p * n) := by ring
    omega
  refine ⟨s', 6 + ((1 + alloc_sz) + (2 + (2 + (2 + (2 + (t₇ + (t₈ + t₉))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ hex₉))))))),
    ht_total, hout_eq,
    fun a ha => by
      rw [harr₉ a ha, harr₈ a ha, harr₇ a ha]
      simp [s₆, s₅, s₄, s₃, s₂, State.setArr_arrs_ne _ _ ha, s₁],
    fun r hr => by
      rw [hreg₉ r hr, hreg₈ r hr, hreg₇ r (by omega)]
      simp [s₆, s₅, s₄, s₃, s₂, s₁, show r ≠ r_base + 7 by omega,
        show r ≠ r_base + 8 by omega, show r ≠ r_base + 9 by omega,
        show r ≠ r_base + 10 by omega]⟩

/-- Precomputed candidate code and isomorphism index maps for a target graph with `p` vertices
and `m` edges. -/
structure IsoTargetCandidate (p m : ℕ) where
  code : List ℕ
  fe : List (ℕ × Bool)
  fv : List ℕ

/-- Validity of a candidate `cand : IsoTargetCandidate p edgesH.length`: `cand.code` is a valid
detail-`≤ (edgesH.length + p)` code decoding to a `0`-rooted digraph `H_c` isomorphic to
`targetToOrientedComputeRootedDigraph p edgesH flips` (for some orientation `flips`) via an
isomorphism `iso` whose edge and vertex index maps are `cand.fe` and `cand.fv`. -/
def IsoTargetCandidate.IsValid {p : ℕ} (edgesH : List (Fin p × Fin p))
    (cand : IsoTargetCandidate p edgesH.length) : Prop :=
  IsDetailLeCode 0 (edgesH.length + p) cand.code ∧
  ∃ (flips : Fin edgesH.length → Bool)
    (H_c : ComputeRootedDigraph 0)
    (iso : RootedDigraphIso (targetToOrientedComputeRootedDigraph p edgesH flips) H_c),
    decRootedDigraph 0 cand.code = some H_c ∧
    cand.fe = (List.finRange edgesH.length).map (fun k => ((iso.edgeEquiv k).1, flips k)) ∧
    cand.fv = (List.finRange p).map (fun u => (iso.vertEquiv u).1)

theorem IsoTargetCandidate.IsValid.code_length {p : ℕ} {edgesH : List (Fin p × Fin p)}
    {cand : IsoTargetCandidate p edgesH.length} (h : cand.IsValid edgesH) :
    cand.code.length = 2 + 2 * edgesH.length := by
  rcases h with ⟨hdet, flips, H_c, iso, hdec, _, _⟩
  unfold IsDetailLeCode at hdet
  rw [hdec] at hdet
  rcases hdet with ⟨hcode, _⟩
  have hm_eq : H_c.digraph.numEdges = edgesH.length := by
    have hcard := Fintype.card_congr iso.edgeEquiv
    simpa using hcard.symm
  rw [hcode, length_encRootedDigraph, hm_eq]

theorem IsoTargetCandidate.IsValid.words_le {p : ℕ} {edgesH : List (Fin p × Fin p)}
    {cand : IsoTargetCandidate p edgesH.length} (h : cand.IsValid edgesH) :
    ∀ x ∈ cand.code, x ≤ edgesH.length + p := by
  simpa using (length_and_words_le_of_isDetailLeCode h.1).2

/-- Finite list of all detail-`≤ (edgesH.length + p)` codes isomorphic to
`targetToOrientedComputeRootedDigraph p edgesH flips` for some orientation `flips`. -/
def targetIsoCodes (p : ℕ) (edgesH : List (Fin p × Fin p)) : List (List ℕ) :=
  (allDetailLeCodes 0 (edgesH.length + p)).filter (fun c =>
    decide (∃ flips : Fin edgesH.length → Bool,
      IsIsoRootedDigraphCode 0
        (encRootedDigraph (targetToOrientedComputeRootedDigraph p edgesH flips)) c))

/-- Construct an `IsoTargetCandidate` from a code `c : List ℕ`. -/
noncomputable def mkIsoTargetCandidate (p : ℕ) (edgesH : List (Fin p × Fin p)) (c : List ℕ) :
    IsoTargetCandidate p edgesH.length :=
  match decRootedDigraph 0 c with
  | some H_c =>
    if h : ∃ flips : Fin edgesH.length → Bool,
        IsRootedDigraphIso (targetToOrientedComputeRootedDigraph p edgesH flips) H_c then
      let flips := Classical.choose h
      let iso := Classical.choice (Classical.choose_spec h)
      { code := c
        fe := (List.finRange edgesH.length).map (fun k => ((iso.edgeEquiv k).1, flips k))
        fv := (List.finRange p).map (fun u => (iso.vertEquiv u).1) }
    else
      { code := c, fe := [], fv := [] }
  | none => { code := c, fe := [], fv := [] }

@[simp]
theorem mkIsoTargetCandidate_code (p : ℕ) (edgesH : List (Fin p × Fin p)) (c : List ℕ) :
    (mkIsoTargetCandidate p edgesH c).code = c := by
  unfold mkIsoTargetCandidate
  cases decRootedDigraph 0 c with
  | none => rfl
  | some H_c => dsimp only; split_ifs <;> rfl

/-- Finite list of all valid `IsoTargetCandidate`s for `(p, edgesH)`. -/
noncomputable def targetCandidates (p : ℕ) (edgesH : List (Fin p × Fin p)) :
    List (IsoTargetCandidate p edgesH.length) :=
  (targetIsoCodes p edgesH).map (mkIsoTargetCandidate p edgesH)

theorem targetCandidates_valid (p : ℕ) (edgesH : List (Fin p × Fin p)) :
    ∀ cand ∈ targetCandidates p edgesH, cand.IsValid edgesH := by
  intro cand hcand
  unfold targetCandidates targetIsoCodes at hcand
  simp only [List.mem_map, List.mem_filter, mem_allDetailLeCodes_iff,
    decide_eq_true_eq] at hcand
  rcases hcand with ⟨c, ⟨hdet, flips, hiso⟩, rfl⟩
  refine ⟨by simpa using hdet, ?_⟩
  unfold IsIsoRootedDigraphCode at hiso
  rw [decRootedDigraph_encRootedDigraph] at hiso
  cases hdec : decRootedDigraph 0 c with
  | none => rw [hdec] at hiso; exact False.elim hiso
  | some H_c =>
    rw [hdec] at hiso
    have hex : ∃ flips : Fin edgesH.length → Bool,
        IsRootedDigraphIso (targetToOrientedComputeRootedDigraph p edgesH flips) H_c :=
      ⟨flips, hiso⟩
    refine ⟨Classical.choose hex, H_c, Classical.choice (Classical.choose_spec hex), ?_, ?_, ?_⟩
    · simpa [mkIsoTargetCandidate_code] using hdec
    · unfold mkIsoTargetCandidate
      simp [hdec, hex]
    · unfold mkIsoTargetCandidate
      simp [hdec, hex]

theorem mem_map_code_targetCandidates_iff {p : ℕ} (edgesH : List (Fin p × Fin p))
    (F : FolioSetRep 0 (edgesH.length + p)) (i : Fin F.codes.length) :
    F.codes[i.1]'i.2 ∈ (targetCandidates p edgesH).map IsoTargetCandidate.code ↔
      ∃ flips : Fin edgesH.length → Bool,
        IsRootedDigraphIso
          (targetToOrientedComputeRootedDigraph p edgesH flips) (F.decodedAt i) := by
  have hmap : (targetCandidates p edgesH).map IsoTargetCandidate.code =
      targetIsoCodes p edgesH := by
    unfold targetCandidates
    rw [List.map_map]
    have hfun : (IsoTargetCandidate.code ∘ mkIsoTargetCandidate p edgesH) = id := by
      funext c; exact mkIsoTargetCandidate_code p edgesH c
    simp [hfun]
  rw [hmap]
  unfold targetIsoCodes
  rw [List.mem_filter, mem_allDetailLeCodes_iff, decide_eq_true_eq]
  have hdet : IsDetailLeCode 0 (edgesH.length + p) (F.codes[i.1]'i.2) :=
    F.all_detail _ (List.getElem_mem _)
  simp only [F.isIsoRootedDigraphCode_getElem_iff
    (targetToOrientedComputeRootedDigraph p edgesH _) i]
  exact ⟨fun h => h.2, fun h => ⟨hdet, h⟩⟩

/-- Predicate stating that `out` encodes `[1] ++ M.enc` for a valid `MultiDigraphModel edgesH G`. -/
def HasValidModelOut {p n : ℕ} (edgesH : List (Fin p × Fin p)) (G : MultiDigraph n)
    (out : List ℕ) : Prop :=
  ∃ M : MultiDigraphModel edgesH G, M.IsValid ∧ out = [1] ++ M.enc

/-- Check whether the current folio record at `r_base + 3` in `a_folio` matches any candidate in
`cands` (when `r_base + 5 == 0`), and if so extract the corresponding model from `a_models` (at
`r_base + 4`) into `a_out` and set `r_base + 5 := 1`. -/
def checkAndExtractProg (p m : ℕ) (a_folio a_models a_out : Arr) (r_base : Reg) :
    List (IsoTargetCandidate p m) → Cmd
  | [] => .skip
  | cand :: rest =>
    .seq (.ite (.op .eq (.reg (r_base + 5)) (.const 0))
        (.seq (checkRecordMatch a_folio (r_base + 3) (r_base + 6) (r_base + 8) cand.code)
          (.ite (.op .eq (.reg (r_base + 6)) (.const 1))
            (.seq (writeIsoModelProg p m cand.fe cand.fv a_models a_out r_base)
              (.assign (r_base + 5) (.const 1)))
            .skip))
        .skip)
      (checkAndExtractProg p m a_folio a_models a_out r_base rest)

/-- Step time bound per candidate in `checkAndExtractProg`. -/
def candStepTime (p m n : ℕ) : ℕ :=
  90 + 54 * m + (14 + 20 * n) * p

theorem checkAndExtractProg_exec {w p n f_off m_off : ℕ}
    (edgesH : List (Fin p × Fin p))
    {G : MultiDigraph n}
    (F : FolioSetRep 0 (edgesH.length + p))
    (models : ∀ i : Fin F.codes.length,
      RootedDigraphModel (F.decodedAt i) (G.toMultiComputeRootedDigraph []))
    (i : Fin F.codes.length)
    (a_folio a_models a_out r_base : ℕ)
    (hne_fo : a_folio ≠ a_out) (hne_mo : a_models ≠ a_out)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hp_w : p < 2 ^ w)
    (_hδ_w : edgesH.length + p < 2 ^ w)
    (hout_len_w : 3 + 2 * edgesH.length + p * n < 2 ^ w)
    (hfoff_w : f_off + 3 + 2 * (edgesH.length + p) < 2 ^ w)
    (hmoff_w : m_off + 3 + 2 * edgesH.length + p * n < 2 ^ w)
    (pre_f suf_f pre_m suf_m : List ℕ)
    (hpre_f : pre_f.length = f_off) (hpre_m : pre_m.length = m_off)
    (cands : List (IsoTargetCandidate p edgesH.length))
    (hcands_val : ∀ cand ∈ cands, cand.IsValid edgesH)
    {s : State}
    (hfolio : s.arrs a_folio =
      pre_f ++ ((F.codes[i.1]'i.2).length :: (F.codes[i.1]'i.2)) ++ suf_f)
    (hmodels : s.arrs a_models =
      pre_m ++ ((encRootedDigraphModel (models i)).length ::
        encRootedDigraphModel (models i)) ++ suf_m)
    (hrn : s.regs r_base = n)
    (hrfoff : s.regs (r_base + 3) = f_off)
    (hrmoff : s.regs (r_base + 4) = m_off)
    (hinv : (s.regs (r_base + 5) = 1 ∧ HasValidModelOut edgesH G (s.arrs a_out)) ∨
            (s.regs (r_base + 5) = 0 ∧ s.arrs a_out = [0])) :
    ∃ s' t,
      Exec w (checkAndExtractProg p edgesH.length a_folio a_models a_out r_base cands) s s' t ∧
      t ≤ 1 + candStepTime p edgesH.length n * cands.length ∧
      ((s.regs (r_base + 5) = 1 ∨
        F.codes[i.1]'i.2 ∈ cands.map IsoTargetCandidate.code) →
        s'.regs (r_base + 5) = 1 ∧ HasValidModelOut edgesH G (s'.arrs a_out)) ∧
      ((s.regs (r_base + 5) = 0 ∧
        F.codes[i.1]'i.2 ∉ cands.map IsoTargetCandidate.code) →
        s'.regs (r_base + 5) = 0 ∧ s'.arrs a_out = [0]) ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 5, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hc_det : IsDetailLeCode 0 (edgesH.length + p) (F.codes[i.1]'i.2) :=
    F.all_detail _ (List.getElem_mem _)
  rcases length_and_words_le_of_isDetailLeCode hc_det with ⟨hclen_le, hc_words_le⟩
  have hclen_w : (F.codes[i.1]'i.2).length < 2 ^ w := by omega
  have hc_w : ∀ x ∈ F.codes[i.1]'i.2, x < 2 ^ w := by
    intro x hx; have := hc_words_le x hx; omega
  induction cands generalizing s with
  | nil =>
    refine ⟨s, 1, .skip s, by simp, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · intro h
      rcases h with h1 | hmem
      · rcases hinv with ⟨_, hmod⟩ | ⟨h0, _⟩
        · exact ⟨h1, hmod⟩
        · omega
      · simp at hmem
    · intro ⟨h0, _⟩
      rcases hinv with ⟨h1, _⟩ | ⟨_, hout0⟩
      · omega
      · exact ⟨h0, hout0⟩
  | cons cand rest ih =>
    have hcand_val : cand.IsValid edgesH := hcands_val cand List.mem_cons_self
    have hrest_val : ∀ x ∈ rest, x.IsValid edgesH :=
      fun x hx => hcands_val x (List.mem_cons_of_mem cand hx)
    have hcand_len : cand.code.length = 2 + 2 * edgesH.length := hcand_val.code_length
    have hcand_w : ∀ x ∈ cand.code, x < 2 ^ w := by
      intro x hx; have := hcand_val.words_le x hx; omega
    rcases hinv with ⟨hfound1, hmod⟩ | ⟨hfound0, hout0⟩
    · -- Already found (`r_base + 5 == 1`):
      have hcond : (Expr.op .eq (.reg (r_base + 5)) (.const 0)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hfound1, hw, h0_w]
      have hex_ite :
          Exec w (.ite (.op .eq (.reg (r_base + 5)) (.const 0))
            (.seq (checkRecordMatch a_folio (r_base + 3) (r_base + 6) (r_base + 8) cand.code)
              (.ite (.op .eq (.reg (r_base + 6)) (.const 1))
                (.seq (writeIsoModelProg p edgesH.length cand.fe cand.fv a_models a_out r_base)
                  (.assign (r_base + 5) (.const 1)))
                .skip))
            .skip) s s (3 + 1) :=
        .ite_false hcond (.skip s)
      rcases ih hrest_val hfolio hmodels hrn hrfoff hrmoff (Or.inl ⟨hfound1, hmod⟩) with
        ⟨s', t_rest, hex_rest, ht_rest, hfound_out, hnot_out, harr', hreg'⟩
      have ht_step : (3 + 1) + t_rest ≤
          1 + candStepTime p edgesH.length n * (rest.length + 1) := by
        unfold candStepTime at ht_rest ⊢
        have hmul :
            (90 + 54 * edgesH.length + (14 + 20 * n) * p) * (rest.length + 1) =
              (90 + 54 * edgesH.length + (14 + 20 * n) * p) * rest.length +
                90 + 54 * edgesH.length + (14 + 20 * n) * p := by ring
        omega
      refine ⟨s', (3 + 1) + t_rest, .seq hex_ite hex_rest,
        by simpa only [List.length_cons] using ht_step,
        fun _ => hfound_out (Or.inl hfound1),
        fun ⟨h0, _⟩ => by omega,
        harr', hreg'⟩
    · -- Not yet found (`r_base + 5 == 0`):
      have hcond0 : (Expr.op .eq (.reg (r_base + 5)) (.const 0)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hfound0, hw, h0_w]
      rcases checkRecordMatch_exec a_folio (r_base + 3) (r_base + 6) (r_base + 8)
          (by omega) (by omega) (by omega) hw cand.code (F.codes[i.1]'i.2) pre_f suf_f
          hpre_f (by omega) hclen_w hcand_w hc_w hfolio hrfoff with
        ⟨s₁, t₁, hex₁, ht₁, hreq₁, harr₁, hreg₁⟩
      by_cases heq_code : F.codes[i.1]'i.2 = cand.code
      · -- Match! Extract model and set `r_base + 5 := 1`:
        have hreq1_val : s₁.regs (r_base + 6) = 1 := by simp [hreq₁, heq_code]
        have hcond1 : (Expr.op .eq (.reg (r_base + 6)) (.const 1)).eval w s₁ = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreq1_val, hw]
        rcases hcand_val with ⟨_, flips, H_c, iso, hdec_c, hfe_c, hfv_c⟩
        have hdec_i := F.decRootedDigraph_decodedAt i
        rw [heq_code, hdec_c] at hdec_i
        have hH_eq : H_c = F.decodedAt i := Option.some.inj hdec_i
        subst hH_eq
        have hmodels₁ : s₁.arrs a_models =
            pre_m ++ ((encRootedDigraphModel (models i)).length ::
              encRootedDigraphModel (models i)) ++ suf_m := by
          rw [harr₁ a_models]; exact hmodels
        rcases writeIsoModelProg_exec edgesH flips iso (models i) cand.fe cand.fv hfe_c hfv_c
            a_models a_out r_base hne_mo hw3 hn_w hp_w hout_len_w hmoff_w pre_m suf_m hpre_m
            hmodels₁
            (by rw [hreg₁ r_base (by omega) (by omega)]; exact hrn)
            (by rw [hreg₁ (r_base + 4) (by omega) (by omega)]; exact hrmoff) with
          ⟨s₂, t₂, hex₂, ht₂, hout₂, harr₂, hreg₂⟩
        let s₃ := s₂.setReg (r_base + 5) 1
        have hex₃ : Exec w (.assign (r_base + 5) (.const 1)) s₂ s₃ 2 :=
          .assign (by simp [Expr.eval, checkWord, hw])
        have hex_ite :
            Exec w (.ite (.op .eq (.reg (r_base + 5)) (.const 0))
              (.seq (checkRecordMatch a_folio (r_base + 3) (r_base + 6) (r_base + 8) cand.code)
                (.ite (.op .eq (.reg (r_base + 6)) (.const 1))
                  (.seq (writeIsoModelProg p edgesH.length cand.fe cand.fv a_models a_out r_base)
                    (.assign (r_base + 5) (.const 1)))
                  .skip))
              .skip) s s₃ (3 + (t₁ + (3 + (t₂ + 2)))) :=
          .ite_true hcond0 (by omega) (.seq hex₁ (.ite_true hcond1 (by omega) (.seq hex₂ hex₃)))
        have hmod₃ : HasValidModelOut edgesH G (s₃.arrs a_out) := by
          refine ⟨MultiDigraphModel.ofOrientedRootedDigraphModel flips ((models i).ofIsoLeft iso),
            MultiDigraphModel.isValid_ofOrientedRootedDigraphModel flips _, ?_⟩
          simpa [s₃] using hout₂
        have hfolio₃ : s₃.arrs a_folio =
            pre_f ++ ((F.codes[i.1]'i.2).length :: (F.codes[i.1]'i.2)) ++ suf_f := by
          simp [s₃, harr₂ a_folio hne_fo, harr₁ a_folio, hfolio]
        have hmodels₃ : s₃.arrs a_models =
            pre_m ++ ((encRootedDigraphModel (models i)).length ::
              encRootedDigraphModel (models i)) ++ suf_m := by
          simp [s₃, harr₂ a_models hne_mo, harr₁ a_models, hmodels]
        rcases ih hrest_val hfolio₃ hmodels₃
            (by simp [s₃, hreg₂ r_base (by omega), hreg₁ r_base (by omega) (by omega), hrn])
            (by simp [s₃, hreg₂ (r_base + 3) (by omega),
                hreg₁ (r_base + 3) (by omega) (by omega), hrfoff])
            (by simp [s₃, hreg₂ (r_base + 4) (by omega),
                hreg₁ (r_base + 4) (by omega) (by omega), hrmoff])
            (Or.inl ⟨by simp [s₃], hmod₃⟩) with
          ⟨s', t_rest, hex_rest, ht_rest, hfound_out, _, harr', hreg'⟩
        have ht_step : (3 + (t₁ + (3 + (t₂ + 2)))) + t_rest ≤
            1 + candStepTime p edgesH.length n * (rest.length + 1) := by
          rw [hcand_len] at ht₁
          unfold candStepTime at ht_rest ⊢
          have hmul :
              (90 + 54 * edgesH.length + (14 + 20 * n) * p) * (rest.length + 1) =
                (90 + 54 * edgesH.length + (14 + 20 * n) * p) * rest.length +
                  90 + 54 * edgesH.length + (14 + 20 * n) * p := by ring
          omega
        refine ⟨s', (3 + (t₁ + (3 + (t₂ + 2)))) + t_rest, .seq hex_ite hex_rest,
          by simpa only [List.length_cons] using ht_step,
          fun _ => hfound_out (Or.inl (by simp [s₃])),
          fun ⟨_, hnot_mem⟩ => False.elim (hnot_mem (by simp [heq_code])),
          fun a ha => by rw [harr' a ha, State.setReg_arrs, harr₂ a ha, harr₁ a],
          fun r hr => by
            rw [hreg' r hr]
            simp only [s₃, State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 5)]
            rw [hreg₂ r (by omega), hreg₁ r (by omega) (by omega)]⟩
      · -- Not a match:
        have hreq0_val : s₁.regs (r_base + 6) = 0 := by simp [hreq₁, heq_code]
        have hcond1 : (Expr.op .eq (.reg (r_base + 6)) (.const 1)).eval w s₁ = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreq0_val, hw, h0_w]
        have hex_ite :
            Exec w (.ite (.op .eq (.reg (r_base + 5)) (.const 0))
              (.seq (checkRecordMatch a_folio (r_base + 3) (r_base + 6) (r_base + 8) cand.code)
                (.ite (.op .eq (.reg (r_base + 6)) (.const 1))
                  (.seq (writeIsoModelProg p edgesH.length cand.fe cand.fv a_models a_out r_base)
                    (.assign (r_base + 5) (.const 1)))
                  .skip))
              .skip) s s₁ (3 + (t₁ + (3 + 1))) :=
          .ite_true hcond0 (by omega) (.seq hex₁ (.ite_false hcond1 (.skip s₁)))
        have hfound0_s1 : s₁.regs (r_base + 5) = 0 := by
          rw [hreg₁ (r_base + 5) (by omega) (by omega)]; exact hfound0
        have hout0_s1 : s₁.arrs a_out = [0] := by
          rw [harr₁ a_out]; exact hout0
        rcases ih hrest_val
            (by rw [harr₁ a_folio]; exact hfolio)
            (by rw [harr₁ a_models]; exact hmodels)
            (by rw [hreg₁ r_base (by omega) (by omega)]; exact hrn)
            (by rw [hreg₁ (r_base + 3) (by omega) (by omega)]; exact hrfoff)
            (by rw [hreg₁ (r_base + 4) (by omega) (by omega)]; exact hrmoff)
            (Or.inr ⟨hfound0_s1, hout0_s1⟩) with
          ⟨s', t_rest, hex_rest, ht_rest, hfound_out, hnot_out, harr', hreg'⟩
        have ht_step : (3 + (t₁ + (3 + 1))) + t_rest ≤
            1 + candStepTime p edgesH.length n * (rest.length + 1) := by
          rw [hcand_len] at ht₁
          unfold candStepTime at ht_rest ⊢
          have hmul :
              (90 + 54 * edgesH.length + (14 + 20 * n) * p) * (rest.length + 1) =
                (90 + 54 * edgesH.length + (14 + 20 * n) * p) * rest.length +
                  90 + 54 * edgesH.length + (14 + 20 * n) * p := by ring
          omega
        refine ⟨s', (3 + (t₁ + (3 + 1))) + t_rest, .seq hex_ite hex_rest,
          by simpa only [List.length_cons] using ht_step,
          ?_, ?_,
          fun a ha => by rw [harr' a ha, harr₁ a],
          fun r hr => by rw [hreg' r hr, hreg₁ r (by omega) (by omega)]⟩
        · intro h
          rcases h with h1 | hmem
          · omega
          · rcases List.mem_cons.mp hmem with hhead | htail
            · exact False.elim (heq_code hhead)
            · exact hfound_out (Or.inr htail)
        · intro ⟨_, hnot_mem⟩
          have hnot_tail : F.codes[i.1]'i.2 ∉ rest.map IsoTargetCandidate.code :=
            fun h => hnot_mem (List.mem_cons_of_mem _ h)
          exact hnot_out ⟨hfound0_s1, hnot_tail⟩

/-- Loop body of `extractTargetModelProg`: check/extract record `i` (`r_base + 2`), then advance
`r_base + 3` (`f_off`) and `r_base + 4` (`m_off`). -/
def extractTargetModelBody (p m : ℕ) (cands : List (IsoTargetCandidate p m))
    (a_folio a_models a_out : Arr) (r_base : Reg) : Cmd :=
  .seq (checkAndExtractProg p m a_folio a_models a_out r_base cands)
    (.seq (.assign (r_base + 8) (.read a_folio (.reg (r_base + 3))))
      (.seq (.assign (r_base + 3)
          (.op .add (.op .add (.reg (r_base + 3)) (.const 1)) (.reg (r_base + 8))))
        (.seq (.assign (r_base + 8) (.read a_models (.reg (r_base + 4))))
          (.assign (r_base + 4)
            (.op .add (.op .add (.reg (r_base + 4)) (.const 1)) (.reg (r_base + 8)))))))

/-- Predicate stating that some record `j < i` in `F.codes` belongs to
`cands.map IsoTargetCandidate.code`. -/
def FoundCandidateBefore {p m q δ : ℕ} (cands : List (IsoTargetCandidate p m))
    (F : FolioSetRep q δ) (i : ℕ) : Prop :=
  ∃ j : Fin F.codes.length, j.1 < i ∧ F.codes[j.1]'j.2 ∈ cands.map IsoTargetCandidate.code

theorem extractTargetModelLoop_exec {w p n : ℕ}
    (edgesH : List (Fin p × Fin p))
    {G : MultiDigraph n}
    (F : FolioSetRep 0 (edgesH.length + p))
    (models : ∀ i : Fin F.codes.length,
      RootedDigraphModel (F.decodedAt i) (G.toMultiComputeRootedDigraph []))
    (a_folio a_models a_out r_base : ℕ)
    (hne_fo : a_folio ≠ a_out) (hne_mo : a_models ≠ a_out)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hp_w : p < 2 ^ w)
    (hδ_w : edgesH.length + p < 2 ^ w)
    (hout_len_w : 3 + 2 * edgesH.length + p * n < 2 ^ w)
    (hf_len_w : (encFolioSetRep F).length + 3 + 2 * (edgesH.length + p) < 2 ^ w)
    (hm_len_w : (encFolioModels F models).length + 3 + 2 * edgesH.length + p * n < 2 ^ w)
    (cands : List (IsoTargetCandidate p edgesH.length))
    (hcands_val : ∀ cand ∈ cands, cand.IsValid edgesH)
    (rem i : ℕ) (hrem : i + rem = F.codes.length)
    {s : State}
    (hfolio : s.arrs a_folio = encFolioSetRep F)
    (hmodels : s.arrs a_models = encFolioModels F models)
    (hrn : s.regs r_base = n)
    (hrk : s.regs (r_base + 1) = F.codes.length)
    (hri : s.regs (r_base + 2) = i)
    (hrfoff : s.regs (r_base + 3) = recordOffset F.codes i)
    (hrmoff : s.regs (r_base + 4) =
      recordOffset ((List.finRange F.codes.length).map (fun j =>
        encRootedDigraphModel (models j))) i)
    (hinv : (FoundCandidateBefore cands F i ∧
              s.regs (r_base + 5) = 1 ∧
              HasValidModelOut edgesH G (s.arrs a_out)) ∨
            (¬ FoundCandidateBefore cands F i ∧
              s.regs (r_base + 5) = 0 ∧
              s.arrs a_out = [0])) :
    ∃ s' t,
      Exec w (forUp (r_base + 2) (.reg (r_base + 1))
        (extractTargetModelBody p edgesH.length cands a_folio a_models a_out r_base)) s s' t ∧
      t ≤ 3 + (26 + candStepTime p edgesH.length n * cands.length) * rem ∧
      ((FoundCandidateBefore cands F F.codes.length ∧
        HasValidModelOut edgesH G (s'.arrs a_out)) ∨
       (¬ FoundCandidateBefore cands F F.codes.length ∧
        s'.arrs a_out = [0])) ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 2, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  let modelRecs := (List.finRange F.codes.length).map (fun j =>
    encRootedDigraphModel (models j))
  have hmodelRecs_len : modelRecs.length = F.codes.length := by simp [modelRecs]
  have hk_w : F.codes.length < 2 ^ w := by
    have : F.codes.length ≤ (encFolioSetRep F).length := by
      unfold encFolioSetRep
      rw [List.length_append, List.length_singleton, length_flatMap_len_cons]
      have : F.codes.length ≤ (F.codes.map (fun r => 1 + r.length)).sum := by
        induction F.codes with
        | nil => simp
        | cons r rs ih => simp; omega
      omega
    omega
  induction rem generalizing i s with
  | zero =>
    have hi_eq : i = F.codes.length := by omega
    subst hi_eq
    have hcond : (Expr.op .lt (.reg (r_base + 2)) (.reg (r_base + 1))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrk, hk_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by simp, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    rcases hinv with ⟨hfb, _, hmod⟩ | ⟨hnfb, _, hout0⟩
    · exact Or.inl ⟨hfb, hmod⟩
    · exact Or.inr ⟨hnfb, hout0⟩
  | succ rem ih =>
    have hi_lt : i < F.codes.length := by omega
    have hi_w : i < 2 ^ w := by omega
    let iFin : Fin F.codes.length := ⟨i, hi_lt⟩
    have hcond : (Expr.op .lt (.reg (r_base + 2)) (.reg (r_base + 1))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrk, hi_w, hk_w, hi_lt, hw]
    let f_off := recordOffset F.codes i
    let m_off := recordOffset modelRecs i
    have hfoff_le : f_off ≤ (encFolioSetRep F).length := by
      rw [encFolioSetRep_eq_encRecordList]
      exact recordOffset_le_length F.codes i
    have hmoff_le : m_off ≤ (encFolioModels F models).length := by
      rw [encFolioModels_eq_encRecordList]
      exact recordOffset_le_length modelRecs i
    rcases encRecordList_split hi_lt with ⟨pre_f, suf_f, hsplit_f, hpre_f⟩
    have hi_m_lt : i < modelRecs.length := by omega
    rcases encRecordList_split hi_m_lt with ⟨pre_m, suf_m, hsplit_m, hpre_m⟩
    have hrec_m_eq : modelRecs[i]'hi_m_lt = encRootedDigraphModel (models iFin) := by
      dsimp [modelRecs]
      rw [List.getElem_map]
      exact congrArg (fun x => encRootedDigraphModel (models x)) (Fin.ext (by simp [iFin]))
    have hfolio_split : s.arrs a_folio =
        pre_f ++ ((F.codes[iFin.1]'iFin.2).length :: (F.codes[iFin.1]'iFin.2)) ++ suf_f := by
      rw [hfolio, encFolioSetRep_eq_encRecordList]
      exact hsplit_f
    have hmodels_split : s.arrs a_models =
        pre_m ++ ((encRootedDigraphModel (models iFin)).length ::
          encRootedDigraphModel (models iFin)) ++ suf_m := by
      rw [hmodels, encFolioModels_eq_encRecordList]
      simpa [modelRecs, hrec_m_eq] using hsplit_m
    have hinv_ce :
        (s.regs (r_base + 5) = 1 ∧ HasValidModelOut edgesH G (s.arrs a_out)) ∨
        (s.regs (r_base + 5) = 0 ∧ s.arrs a_out = [0]) := by
      rcases hinv with ⟨_, h1, hmod⟩ | ⟨_, h0, hout0⟩
      · exact Or.inl ⟨h1, hmod⟩
      · exact Or.inr ⟨h0, hout0⟩
    rcases checkAndExtractProg_exec edgesH F models iFin a_folio a_models a_out r_base
        hne_fo hne_mo hw3 hn_w hp_w hδ_w hout_len_w (by omega) (by omega)
        pre_f suf_f pre_m suf_m hpre_f hpre_m cands hcands_val
        hfolio_split hmodels_split hrn hrfoff hrmoff hinv_ce with
      ⟨s₁, t₁, hex₁, ht₁, hce_found, hce_not, harr₁, hreg₁⟩
    -- Advance `f_off`:
    have hfolio₁_split : s₁.arrs a_folio =
        pre_f ++ (F.codes[iFin.1]'iFin.2).length :: ((F.codes[iFin.1]'iFin.2) ++ suf_f) := by
      rw [harr₁ a_folio hne_fo]
      simpa [List.append_assoc] using hfolio_split
    have hflen_lt : f_off < (s₁.arrs a_folio).length := by
      rw [hfolio₁_split, List.length_append, List.length_cons]; omega
    have hfget : (s₁.arrs a_folio)[f_off]'hflen_lt = (F.codes[iFin.1]'iFin.2).length := by
      simp [hfolio₁_split, f_off, ← hpre_f]
    have hfoff_next : recordOffset F.codes (i + 1) =
        (f_off + 1) + (F.codes[iFin.1]'iFin.2).length := by
      simpa [f_off, iFin, Nat.add_assoc] using recordOffset_succ hi_lt
    have hfoff_next_le : recordOffset F.codes (i + 1) ≤ (encFolioSetRep F).length := by
      rw [encFolioSetRep_eq_encRecordList]
      exact recordOffset_le_length F.codes (i + 1)
    have hclen_f_w : (F.codes[iFin.1]'iFin.2).length < 2 ^ w := by omega
    have hrfoff₁ : s₁.regs (r_base + 3) = f_off := by
      rw [hreg₁ (r_base + 3) (by omega)]; exact hrfoff
    have heval_rf : (Expr.read a_folio (.reg (r_base + 3))).eval w s₁ =
        some (F.codes[iFin.1]'iFin.2).length := by
      simp [Expr.eval, checkWord, hrfoff₁, show f_off < 2 ^ w by omega,
        hflen_lt, hfget, hclen_f_w]
    let s₂ := s₁.setReg (r_base + 8) (F.codes[iFin.1]'iFin.2).length
    have hex₂ : Exec w (.assign (r_base + 8) (.read a_folio (.reg (r_base + 3)))) s₁ s₂ 3 :=
      .assign heval_rf
    have heval_addf :
        (Expr.op .add (.op .add (.reg (r_base + 3)) (.const 1))
          (.reg (r_base + 8))).eval w s₂ = some (recordOffset F.codes (i + 1)) := by
      simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrfoff₁,
        show f_off < 2 ^ w by omega, hw, show f_off + 1 < 2 ^ w by omega,
        hclen_f_w, ← hfoff_next, show recordOffset F.codes (i + 1) < 2 ^ w by omega]
    let s₃ := s₂.setReg (r_base + 3) (recordOffset F.codes (i + 1))
    have hex₃ : Exec w (.assign (r_base + 3)
        (.op .add (.op .add (.reg (r_base + 3)) (.const 1)) (.reg (r_base + 8)))) s₂ s₃ 6 :=
      .assign heval_addf
    -- Advance `m_off`:
    have hmodels₃_split : s₃.arrs a_models =
        pre_m ++ (encRootedDigraphModel (models iFin)).length ::
          (encRootedDigraphModel (models iFin) ++ suf_m) := by
      simp only [s₃, s₂, State.setReg_arrs, harr₁ a_models hne_mo]
      simpa [List.append_assoc] using hmodels_split
    have hmlen_lt : m_off < (s₃.arrs a_models).length := by
      rw [hmodels₃_split, List.length_append, List.length_cons]; omega
    have hmget : (s₃.arrs a_models)[m_off]'hmlen_lt =
        (encRootedDigraphModel (models iFin)).length := by
      simp [hmodels₃_split, m_off, ← hpre_m]
    have hmoff_next : recordOffset modelRecs (i + 1) =
        (m_off + 1) + (encRootedDigraphModel (models iFin)).length := by
      have hsucc := recordOffset_succ hi_m_lt
      simpa [m_off, hrec_m_eq, Nat.add_assoc] using hsucc
    have hmoff_next_le : recordOffset modelRecs (i + 1) ≤ (encFolioModels F models).length := by
      rw [encFolioModels_eq_encRecordList]
      exact recordOffset_le_length modelRecs (i + 1)
    have hclen_m_w : (encRootedDigraphModel (models iFin)).length < 2 ^ w := by omega
    have hrmoff₃ : s₃.regs (r_base + 4) = m_off := by
      simp only [s₃, s₂, State.setReg_regs_ne _ _ (by omega : r_base + 4 ≠ r_base + 3),
        State.setReg_regs_ne _ _ (by omega : r_base + 4 ≠ r_base + 8)]
      rw [hreg₁ (r_base + 4) (by omega)]; exact hrmoff
    have heval_rm : (Expr.read a_models (.reg (r_base + 4))).eval w s₃ =
        some (encRootedDigraphModel (models iFin)).length := by
      simp [Expr.eval, checkWord, hrmoff₃, show m_off < 2 ^ w by omega,
        hmlen_lt, hmget, hclen_m_w]
    let s₄ := s₃.setReg (r_base + 8) (encRootedDigraphModel (models iFin)).length
    have hex₄ : Exec w (.assign (r_base + 8) (.read a_models (.reg (r_base + 4)))) s₃ s₄ 3 :=
      .assign heval_rm
    have heval_addm :
        (Expr.op .add (.op .add (.reg (r_base + 4)) (.const 1))
          (.reg (r_base + 8))).eval w s₄ = some (recordOffset modelRecs (i + 1)) := by
      simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrmoff₃,
        show m_off < 2 ^ w by omega, hw, show m_off + 1 < 2 ^ w by omega,
        hclen_m_w, ← hmoff_next, show recordOffset modelRecs (i + 1) < 2 ^ w by omega]
    let s₅ := s₄.setReg (r_base + 4) (recordOffset modelRecs (i + 1))
    have hex₅ : Exec w (.assign (r_base + 4)
        (.op .add (.op .add (.reg (r_base + 4)) (.const 1)) (.reg (r_base + 8)))) s₄ s₅ 6 :=
      .assign heval_addm
    have hex_body :
        Exec w (extractTargetModelBody p edgesH.length cands a_folio a_models a_out r_base)
          s s₅ (t₁ + (3 + (6 + (3 + 6)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
    -- Increment `i`:
    have hri₅ : s₅.regs (r_base + 2) = i := by
      simp only [s₅, s₄, s₃, s₂,
        State.setReg_regs_ne _ _ (by omega : r_base + 2 ≠ r_base + 4),
        State.setReg_regs_ne _ _ (by omega : r_base + 2 ≠ r_base + 8),
        State.setReg_regs_ne _ _ (by omega : r_base + 2 ≠ r_base + 3)]
      rw [hreg₁ (r_base + 2) (by omega)]; exact hri
    have heval_inc :
        (Expr.op .add (.reg (r_base + 2)) (.const 1)).eval w s₅ = some (i + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₅, hi_w, hw,
        show i + 1 < 2 ^ w by omega]
    let s₆ := s₅.setReg (r_base + 2) (i + 1)
    have hex_inc : Exec w (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.const 1)))
        s₅ s₆ 4 :=
      .assign heval_inc
    -- Establish loop invariant at `i + 1`:
    have hinv₆ :
        (FoundCandidateBefore cands F (i + 1) ∧
          s₆.regs (r_base + 5) = 1 ∧
          HasValidModelOut edgesH G (s₆.arrs a_out)) ∨
        (¬ FoundCandidateBefore cands F (i + 1) ∧
          s₆.regs (r_base + 5) = 0 ∧
          s₆.arrs a_out = [0]) := by
      have hr5_eq : s₆.regs (r_base + 5) = s₁.regs (r_base + 5) := by
        simp [s₆, s₅, s₄, s₃, s₂]
      have hout_eq : s₆.arrs a_out = s₁.arrs a_out := rfl
      rw [hr5_eq, hout_eq]
      rcases hinv with ⟨hfb, h1, _⟩ | ⟨hnfb, h0, _⟩
      · rcases hce_found (Or.inl h1) with ⟨hr5_1, hmod_1⟩
        refine Or.inl ⟨?_, hr5_1, hmod_1⟩
        rcases hfb with ⟨j, hj_lt, hj_mem⟩
        exact ⟨j, by omega, hj_mem⟩
      · by_cases hmem_i : F.codes[iFin.1]'iFin.2 ∈ cands.map IsoTargetCandidate.code
        · rcases hce_found (Or.inr hmem_i) with ⟨hr5_1, hmod_1⟩
          exact Or.inl ⟨⟨iFin, by simp [iFin], hmem_i⟩, hr5_1, hmod_1⟩
        · rcases hce_not ⟨h0, hmem_i⟩ with ⟨hr5_0, hout_0⟩
          refine Or.inr ⟨?_, hr5_0, hout_0⟩
          rintro ⟨j, hj_lt, hj_mem⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj_lt with hj_lt_i | hj_eq_i
          · exact hnfb ⟨j, hj_lt_i, hj_mem⟩
          · have hj_eq : j = iFin := Fin.ext hj_eq_i
            subst hj_eq
            exact hmem_i hj_mem
    rcases ih (i + 1) (by omega) (s := s₆)
        (by simp [s₆, s₅, s₄, s₃, s₂, harr₁ a_folio hne_fo, hfolio])
        (by simp [s₆, s₅, s₄, s₃, s₂, harr₁ a_models hne_mo, hmodels])
        (by simp [s₆, s₅, s₄, s₃, s₂, hreg₁ r_base (by omega), hrn])
        (by simp [s₆, s₅, s₄, s₃, s₂, hreg₁ (r_base + 1) (by omega), hrk])
        (by simp [s₆])
        (by simp [s₆, s₅, s₄, s₃])
        (by simp [s₆, s₅]; rfl)
        hinv₆ with
      ⟨s', t_rest, hex_rest, ht_rest, hout_final, harr', hreg'⟩
    have ht_step :
        3 + ((t₁ + (3 + (6 + (3 + 6)))) + 4) + t_rest ≤
          3 + (26 + candStepTime p edgesH.length n * cands.length) * (rem + 1) := by
      have hmul :
          (26 + candStepTime p edgesH.length n * cands.length) * (rem + 1) =
            (26 + candStepTime p edgesH.length n * cands.length) * rem +
              26 + candStepTime p edgesH.length n * cands.length := by ring
      omega
    refine ⟨s', 3 + ((t₁ + (3 + (6 + (3 + 6)))) + 4) + t_rest,
      .while_true hcond (by omega) (.seq hex_body hex_inc) hex_rest,
      ht_step, hout_final,
      fun a ha => by rw [harr' a ha]; simp [s₆, s₅, s₄, s₃, s₂, harr₁ a ha],
      fun r hr => by
        rw [hreg' r hr]
        simp only [s₆, s₅, s₄, s₃, s₂,
          State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 2),
          State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 4),
          State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 8),
          State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 3)]
        exact hreg₁ r (by omega)⟩

/-- Word RAM post-processing program for GM XIII Algorithm (4.4) Step (3):
Reads `n = a_G[0]` and `k = a_folio[0]`, initializes `a_out = [0]`, `r_base + 3 := 1`,
`r_base + 4 := 1`, `r_base + 5 := 0`, and loops `i = 0 ..< k` executing `extractTargetModelBody`. -/
noncomputable def extractTargetModelProg (p : ℕ) (edgesH : List (Fin p × Fin p))
    (a_G a_folio a_models a_out : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read a_G (.const 0)))
    (.seq (.assign (r_base + 1) (.read a_folio (.const 0)))
      (.seq (.alloc a_out (.const 1))
        (.seq (.write a_out (.const 0) (.const 0))
          (.seq (.assign (r_base + 3) (.const 1))
            (.seq (.assign (r_base + 4) (.const 1))
              (.seq (.assign (r_base + 5) (.const 0))
                (.seq (.assign (r_base + 2) (.const 0))
                  (forUp (r_base + 2) (.reg (r_base + 1))
                    (extractTargetModelBody p edgesH.length (targetCandidates p edgesH)
                      a_folio a_models a_out r_base)))))))))

/-- Time bound for `extractTargetModelProg` as a function of `p`, `m = edgesH.length`, and `n`. -/
def extractTargetModelTime (p m n : ℕ) : ℕ :=
  let K := (allDetailLeCodes 0 (m + p)).length
  25 + (26 + candStepTime p m n * K) * K

theorem extractTargetModelProg_exec {w p n : ℕ}
    (edgesH : List (Fin p × Fin p))
    (G : MultiDigraph n)
    (F : FolioSetRep 0 (edgesH.length + p))
    (models : ∀ i : Fin F.codes.length,
      RootedDigraphModel (F.decodedAt i) (G.toMultiComputeRootedDigraph []))
    (hfolio_prop : ∀ H : ComputeRootedDigraph 0, H.HasDetailLe (edgesH.length + p) →
      (F.MemIso H ↔ HasRootedDigraphModel H (G.toMultiComputeRootedDigraph [])))
    (a_G a_folio a_models a_out r_base : ℕ)
    (_hne_go : a_G ≠ a_out) (hne_fo : a_folio ≠ a_out) (hne_mo : a_models ≠ a_out)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hp_w : p < 2 ^ w)
    (hδ_w : edgesH.length + p < 2 ^ w)
    (hout_len_w : 3 + 2 * edgesH.length + p * n < 2 ^ w)
    (hf_len_w : (encFolioSetRep F).length + 3 + 2 * (edgesH.length + p) < 2 ^ w)
    (hm_len_w : (encFolioModels F models).length + 3 + 2 * edgesH.length + p * n < 2 ^ w)
    {s : State}
    (hG : s.arrs a_G = G.enc)
    (hfolio : s.arrs a_folio = encFolioSetRep F)
    (hmodels : s.arrs a_models = encFolioModels F models) :
    ∃ s' t,
      Exec w (extractTargetModelProg p edgesH a_G a_folio a_models a_out r_base) s s' t ∧
      t ≤ extractTargetModelTime p edgesH.length n ∧
      ((∃ M : MultiDigraphModel edgesH G, M.IsValid ∧ s'.arrs a_out = [1] ++ M.enc) ∨
       (¬ HasDigraphModel edgesH G ∧ s'.arrs a_out = [0])) ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hk_w : F.codes.length < 2 ^ w := by
    have : F.codes.length ≤ (encFolioSetRep F).length := by
      unfold encFolioSetRep
      rw [List.length_append, List.length_singleton, length_flatMap_len_cons]
      have : F.codes.length ≤ (F.codes.map (fun r => 1 + r.length)).sum := by
        induction F.codes with
        | nil => simp
        | cons r rs ih => simp; omega
      omega
    omega
  -- 1. Read `n = a_G[0]`:
  have hG_len : 0 < (s.arrs a_G).length := by rw [hG, G.length_enc]; omega
  have hG_get : (s.arrs a_G)[0]'hG_len = n := by simp [hG, MultiDigraph.enc]
  let s₁ := s.setReg r_base n
  have hex₁ : Exec w (.assign r_base (.read a_G (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hG_len, hG_get, hn_w])
  -- 2. Read `k = a_folio[0]`:
  have hf_len0 : 0 < (s.arrs a_folio).length := by
    simp [hfolio, encFolioSetRep]
  have hf_get0 : (s.arrs a_folio)[0]'hf_len0 = F.codes.length := by
    simp [hfolio, encFolioSetRep]
  let s₂ := s₁.setReg (r_base + 1) F.codes.length
  have hex₂ : Exec w (.assign (r_base + 1) (.read a_folio (.const 0))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, h0_w, hf_len0, hf_get0, hk_w])
  -- 3. `alloc a_out 1` and `write a_out 0 0`:
  let s₃ := s₂.setArr a_out (List.replicate 1 0)
  have hex₃ : Exec w (.alloc a_out (.const 1)) s₂ s₃ 2 :=
    .alloc (by simp [Expr.eval, checkWord, hw])
  let s₄ := s₃.writeArr a_out 0 0
  have hex₄ : Exec w (.write a_out (.const 0) (.const 0)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₃])
  -- 4. Initialize `r_base + 3 := 1`, `r_base + 4 := 1`, `r_base + 5 := 0`, `r_base + 2 := 0`:
  let s₅ := s₄.setReg (r_base + 3) 1
  have hex₅ : Exec w (.assign (r_base + 3) (.const 1)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₆ := s₅.setReg (r_base + 4) 1
  have hex₆ : Exec w (.assign (r_base + 4) (.const 1)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₇ := s₆.setReg (r_base + 5) 0
  have hex₇ : Exec w (.assign (r_base + 5) (.const 0)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₈ := s₇.setReg (r_base + 2) 0
  have hex₈ : Exec w (.assign (r_base + 2) (.const 0)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 5. Execute loop:
  have hinv₈ :
      (FoundCandidateBefore (targetCandidates p edgesH) F 0 ∧
        s₈.regs (r_base + 5) = 1 ∧
        HasValidModelOut edgesH G (s₈.arrs a_out)) ∨
      (¬ FoundCandidateBefore (targetCandidates p edgesH) F 0 ∧
        s₈.regs (r_base + 5) = 0 ∧
        s₈.arrs a_out = [0]) := by
    refine Or.inr ⟨?_, by simp [s₈, s₇], by simp [s₈, s₇, s₆, s₅, s₄, s₃, State.writeArr]⟩
    rintro ⟨j, hj, _⟩
    omega
  rcases extractTargetModelLoop_exec edgesH F models a_folio a_models a_out r_base
      hne_fo hne_mo hw3 hn_w hp_w hδ_w hout_len_w hf_len_w hm_len_w
      (targetCandidates p edgesH) (targetCandidates_valid p edgesH)
      F.codes.length 0 (by omega) (s := s₈)
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, State.writeArr,
          State.setArr_arrs_ne _ _ hne_fo, s₂, s₁, hfolio])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, State.writeArr,
          State.setArr_arrs_ne _ _ hne_mo, s₂, s₁, hmodels])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂])
      (by simp [s₈])
      (by simp [s₈, s₇, s₆, s₅])
      (by simp [s₈, s₇, s₆])
      hinv₈ with
    ⟨s', t_loop, hex_loop, ht_loop, hout_loop, harr', hreg'⟩
  -- 6. Connect `FoundCandidateBefore` to `HasDigraphModel edgesH G`:
  have hfound_iff :
      FoundCandidateBefore (targetCandidates p edgesH) F F.codes.length ↔
        HasDigraphModel edgesH G := by
    unfold FoundCandidateBefore
    have hex_iff :
        (∃ j : Fin F.codes.length, j.1 < F.codes.length ∧
          F.codes[j.1]'j.2 ∈ (targetCandidates p edgesH).map IsoTargetCandidate.code) ↔
        (∃ flips : Fin edgesH.length → Bool,
          ∃ j : Fin F.codes.length,
            IsRootedDigraphIso
              (targetToOrientedComputeRootedDigraph p edgesH flips) (F.decodedAt j)) := by
      constructor
      · rintro ⟨j, _, hj_mem⟩
        rcases (mem_map_code_targetCandidates_iff edgesH F j).mp hj_mem with ⟨flips, hj_iso⟩
        exact ⟨flips, j, hj_iso⟩
      · rintro ⟨flips, j, hj_iso⟩
        exact ⟨j, j.2, (mem_map_code_targetCandidates_iff edgesH F j).mpr ⟨flips, hj_iso⟩⟩
    rw [hex_iff]
    simp only [← F.memIso_iff_exists_fin]
    have hfolio_ex :
        (∃ flips : Fin edgesH.length → Bool,
          F.MemIso (targetToOrientedComputeRootedDigraph p edgesH flips)) ↔
        (∃ flips : Fin edgesH.length → Bool,
          HasRootedDigraphModel (targetToOrientedComputeRootedDigraph p edgesH flips)
            (G.toMultiComputeRootedDigraph [])) := by
      refine exists_congr fun flips => ?_
      exact hfolio_prop (targetToOrientedComputeRootedDigraph p edgesH flips)
        (targetToOrientedComputeRootedDigraph_hasDetailLe p edgesH flips)
    rw [hfolio_ex]
    exact (hasDigraphModel_iff_exists_hasRootedDigraphModel edgesH G).symm
  have hout_final :
      (∃ M : MultiDigraphModel edgesH G, M.IsValid ∧ s'.arrs a_out = [1] ++ M.enc) ∨
      (¬ HasDigraphModel edgesH G ∧ s'.arrs a_out = [0]) := by
    rcases hout_loop with ⟨_, hmod⟩ | ⟨hnfb, hout0⟩
    · exact Or.inl hmod
    · exact Or.inr ⟨fun h => hnfb (hfound_iff.mpr h), hout0⟩
  -- 7. Time bound:
  have ht_total :
      3 + (3 + (2 + (3 + (2 + (2 + (2 + (2 + t_loop))))))) ≤
        extractTargetModelTime p edgesH.length n := by
    unfold extractTargetModelTime
    dsimp only
    have hcands_le :
        (targetCandidates p edgesH).length ≤
          (allDetailLeCodes 0 (edgesH.length + p)).length := by
      unfold targetCandidates targetIsoCodes
      rw [List.length_map]
      exact List.length_filter_le _ _
    have hcodes_le := length_codes_le_allDetailLeCodes F
    have hstep_le :
        26 + candStepTime p edgesH.length n * (targetCandidates p edgesH).length ≤
          26 + candStepTime p edgesH.length n *
            (allDetailLeCodes 0 (edgesH.length + p)).length := by
      have := Nat.mul_le_mul_left (candStepTime p edgesH.length n) hcands_le
      omega
    have hprod_le :
        (26 + candStepTime p edgesH.length n * (targetCandidates p edgesH).length) *
          F.codes.length ≤
        (26 + candStepTime p edgesH.length n *
          (allDetailLeCodes 0 (edgesH.length + p)).length) *
          (allDetailLeCodes 0 (edgesH.length + p)).length :=
      Nat.mul_le_mul hstep_le hcodes_le
    omega
  refine ⟨s', 3 + (3 + (2 + (3 + (2 + (2 + (2 + (2 + t_loop))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ hex_loop))))))),
    ht_total, hout_final,
    fun a ha => by
      rw [harr' a ha]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, State.writeArr, State.setArr_arrs_ne _ _ ha, s₂, s₁],
    fun r hr => by
      rw [hreg' r (by omega)]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
        show r ≠ r_base + 2 by omega, show r ≠ r_base + 5 by omega,
        show r ≠ r_base + 4 by omega, show r ≠ r_base + 3 by omega,
        show r ≠ r_base + 1 by omega, show r ≠ r_base by omega]⟩

end GraphMinor.Compute
