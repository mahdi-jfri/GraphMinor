module

public import GraphMinor.GM01.Defs
import GraphMinor.GM01.Contraction
import GraphMinor.GM01.GridPaths
import GraphMinor.GM01.TreeSubgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-!
# Graph Minors I, (2.3) and (2.4): Disjoint Paths Meeting Connected Subgraphs in Order

This file formalizes (2.3) and (2.4) of Robertson and Seymour, *Graph Minors I. Excluding a forest*
(pages 43–44):
* `GM01.theorem_2_3`: if `P₁, …, Pₘ` are disjoint paths of `G ∈ 𝓕_θ` and `B₁, …, Bₙ` are disjoint
  connected subgraphs of `G` such that each `Pᵢ` meets each `Bⱼ`, and for `j < j'` all vertices of
  `Bⱼ` on `Pᵢ` occur before all vertices of `B_{j'}`, then `m < θ ^ 2 / 2` or `n < θ ^ (2 * θ - 2)`.
* `GM01.theorem_2_4`: if instead each `Bⱼ` meets at least `θ ^ 2 / 2` of `P₁, …, Pₘ`, then
  `n < θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2)`.
-/

public section

namespace GraphMinor.GM01

open SimpleGraph Set

variable {α : Type*}

/-! ### Helper lemmas for the edge-deletion and contraction reductions of (2.3) -/

/-- If a connected subgraph `B` is not a tree (`¬ IsTreeSubgraph B`), it has an edge `e ∈ B.edgeSet`
whose deletion `B.deleteEdges {e}` remains connected. -/
private lemma exists_edge_deleteEdges_connected_of_not_isTreeSubgraph
    {B : (⊤ : SimpleGraph α).Subgraph} (hB_conn : B.Connected) (hnot_tree : ¬ IsTreeSubgraph B) :
    ∃ e ∈ B.edgeSet, (B.deleteEdges {e}).Connected := by
  have hB_coe_conn : B.coe.Connected := hB_conn.coe
  have hnot_acyc : ¬ B.coe.IsAcyclic := fun hacyc ↦ hnot_tree ⟨hB_coe_conn, hacyc⟩
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge] at hnot_acyc
  push Not at hnot_acyc
  obtain ⟨u, v, hadj, hnot_bridge⟩ := hnot_acyc
  have : Nonempty B.verts := hB_coe_conn.nonempty
  have hdel_coe_conn : (B.coe.deleteEdges {s(u, v)}).Connected :=
    hB_coe_conn.preconnected.connected_deleteEdges_of_not_isBridge hnot_bridge
  refine ⟨s((u : α), (v : α)), hadj, ?_⟩
  rw [Subgraph.connected_iff]
  have hverts_eq : (B.deleteEdges {s((u : α), (v : α))}).verts = B.verts := rfl
  refine ⟨?_, hverts_eq ▸ hB_conn.nonempty⟩
  rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
  intro x y hx hy
  change x ∈ B.verts at hx
  change y ∈ B.verts at hy
  obtain ⟨p⟩ := hdel_coe_conn.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  have hwalk : ∀ {w₁ w₂ : B.verts}, (B.coe.deleteEdges {s(u, v)}).Walk w₁ w₂ →
      ∃ q : (⊤ : SimpleGraph α).Walk w₁.1 w₂.1,
        q.toSubgraph ≤ B.deleteEdges {s((u : α), (v : α))} := by
    intro w₁ w₂ q
    induction q with
    | @nil w₁ =>
      refine ⟨.nil, ?_⟩
      rw [Walk.toSubgraph, singletonSubgraph_le_iff]
      exact w₁.2
    | @cons w₁ w₂ w₃ h q ih =>
      obtain ⟨q', hq'⟩ := ih
      rw [SimpleGraph.deleteEdges_adj, mem_singleton_iff] at h
      have hdel_adj : (B.deleteEdges {s((u : α), (v : α))}).Adj w₁.1 w₂.1 := by
        rw [Subgraph.deleteEdges_adj, mem_singleton_iff]
        refine ⟨h.1, fun heq ↦ h.2 ?_⟩
        rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Sym2.eq_iff.2 (Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩)
        · exact Sym2.eq_iff.2 (Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩)
      refine ⟨Walk.cons (Subgraph.adj_sub _ hdel_adj) q', ?_⟩
      rw [Walk.toSubgraph]
      exact sup_le (subgraphOfAdj_le_of_adj _ hdel_adj) hq'
  exact hwalk p

/-- If a path `P` and a subgraph `B` share at most one vertex, they share no edge. -/
private lemma notMem_edgeSet_of_ncard_inter_le_one {P : Path α} {B : (⊤ : SimpleGraph α).Subgraph}
    (hinter : (P.verts ∩ B.verts).ncard ≤ 1) {e : Sym2 α} (he : e ∈ B.edgeSet) :
    e ∉ P.toSubgraph.edgeSet := by
  intro heP
  induction e with | h u v =>
  have hadjB : B.Adj u v := he
  have hadjP : P.toSubgraph.Adj u v := heP
  have huv : u ≠ v := hadjB.ne
  have hu : u ∈ P.verts ∩ B.verts := ⟨hadjP.fst_mem, hadjB.fst_mem⟩
  have hv : v ∈ P.verts ∩ B.verts := ⟨hadjP.snd_mem, hadjB.snd_mem⟩
  have hsub : ({u, v} : Set α) ⊆ P.verts ∩ B.verts := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  have h2 : ({u, v} : Set α).ncard = 2 := ncard_pair huv
  have hle : 2 ≤ (P.verts ∩ B.verts).ncard := by
    rw [← h2]
    exact ncard_le_ncard hsub (P.verts_finite.subset inter_subset_left)
  omega

/-- If `B` is connected, meets `S`, and has a vertex `y ∉ S`, then `B` has an edge `s(u, v)` with
`v ∉ S`. -/
private lemma exists_adj_notMem_of_connected {B : (⊤ : SimpleGraph α).Subgraph} {S : Set α}
    (hB_conn : B.Connected) {x y : α} (hxB : x ∈ B.verts) (hxS : x ∈ S)
    (hyB : y ∈ B.verts) (hyS : y ∉ S) :
    ∃ u v, B.Adj u v ∧ v ∉ S := by
  obtain ⟨P, hP, hfirst, hlast⟩ := exists_path_of_preconnected hB_conn.preconnected hyB hxB
  have hne : P.first ≠ P.last := by
    rw [hfirst, hlast]
    exact fun heq ↦ hyS (heq ▸ hxS)
  have hnil : ¬ P.walk.Nil := Walk.not_nil_of_ne hne
  refine ⟨P.walk.snd, P.first, ?_, hfirst.symm ▸ hyS⟩
  exact (hP.2 (P.walk.toSubgraph_adj_snd hnil)).symm

/-! ### Contracting internal vertices of tree subgraphs into stars for the `J₂` bound in (2.3) -/

/-- The star subgraph with center `c` and leaves `{v | IsLeafOf Q v}`. -/
private def starOfTree (Q : (⊤ : SimpleGraph α).Subgraph) (c : α) :
    (⊤ : SimpleGraph α).Subgraph where
  verts := {c} ∪ {v | IsLeafOf Q v}
  Adj x y := x ≠ y ∧ ((x = c ∧ IsLeafOf Q y) ∨ (y = c ∧ IsLeafOf Q x))
  adj_sub := fun h ↦ (top_adj _ _).2 h.1
  edge_vert := by
    rintro x _ ⟨_, ⟨rfl, _⟩ | ⟨_, hx⟩⟩
    · exact Or.inl rfl
    · exact Or.inr hx
  symm := ⟨by
    rintro x y ⟨hne, h | h⟩
    · exact ⟨hne.symm, Or.inr h⟩
    · exact ⟨hne.symm, Or.inl h⟩⟩

private lemma isStarWithCenter_starOfTree (Q : (⊤ : SimpleGraph α).Subgraph) (c : α) :
    IsStarWithCenter (starOfTree Q c) c := by
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · intro v hv hne
    rcases hv with rfl | hvL
    · exact (hne rfl).elim
    · exact ⟨hne.symm, Or.inl ⟨rfl, hvL⟩⟩
  · rintro u v ⟨_, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩
    · exact Or.inl rfl
    · exact Or.inr rfl

private lemma starOfTree_verts_subset {Q : (⊤ : SimpleGraph α).Subgraph} {c : α}
    (hc : c ∈ Q.verts) : (starOfTree Q c).verts ⊆ Q.verts := by
  rintro x (rfl | hxL)
  · exact hc
  · exact hxL.1

private lemma starOfTree_le_contractSubgraph {G Q : (⊤ : SimpleGraph α).Subgraph} {c : α}
    (hQ_le : Q ≤ G) (hQ_fin : Q.verts.Finite) (hQ_conn : Q.Connected)
    (hL : 3 ≤ {v | IsLeafOf Q v}.ncard)
    (hc : c ∈ (Q.deleteVerts {v | IsLeafOf Q v}).verts) :
    starOfTree Q c ≤ contractSubgraph G (Q.deleteVerts {v | IsLeafOf Q v}) c := by
  let L := {v | IsLeafOf Q v}
  let C := Q.deleteVerts L
  have hcQ : c ∈ Q.verts := hc.1
  have hcL : c ∉ L := hc.2
  have hadj_int := (connected_deleteVerts_leaves hQ_fin hQ_conn hL).2
  refine ⟨?_, ?_⟩
  · rintro x (rfl | hxL)
    · exact ⟨hQ_le.1 hcQ, fun h ↦ h.2 rfl⟩
    · refine ⟨hQ_le.1 hxL.1, fun ⟨hxC, _⟩ ↦ hxC.2 hxL⟩
  · rintro x y ⟨hne, ⟨rfl, hyL⟩ | ⟨rfl, hxL⟩⟩
    · obtain ⟨z, hzC, hyz⟩ := hadj_int y hyL
      have hy_notC : y ∉ C.verts := fun hyC ↦ hyC.2 hyL
      exact ⟨⟨hQ_le.1 hcQ, fun h ↦ h.2 rfl⟩, ⟨hQ_le.1 hyL.1, fun h ↦ hy_notC h.1⟩,
        hne, z, y, contractMap_of_mem hzC, contractMap_of_notMem hy_notC, hQ_le.2 hyz.symm⟩
    · obtain ⟨z, hzC, hxz⟩ := hadj_int x hxL
      have hx_notC : x ∉ C.verts := fun hxC ↦ hxC.2 hxL
      exact ⟨⟨hQ_le.1 hxL.1, fun h ↦ hx_notC h.1⟩, ⟨hQ_le.1 hcQ, fun h ↦ h.2 rfl⟩,
        hne, x, z, contractMap_of_notMem hx_notC, contractMap_of_mem hzC, hQ_le.2 hxz⟩

/-- Bound on the number of tree subgraphs with `θ` end-vertices in (2.3), obtained by contracting
each tree's internal vertex set `(Q k).deleteVerts {v | IsLeafOf (Q k) v}` into a star center and
applying (2.2) (`theorem_2_2_simple`). -/
private lemma bound_trees_by_2_2 {θ r : ℕ} (hθ : 6 ≤ θ) {G : (⊤ : SimpleGraph α).Subgraph}
    (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (P : Fin θ → Path α) (Q : Fin r → (⊤ : SimpleGraph α).Subgraph)
    (hP_in : ∀ i, (P i).IsIn G)
    (hP_disj : Pairwise fun i i' ↦ Disjoint (P i).verts (P i').verts)
    (hQ_le : ∀ k, Q k ≤ G)
    (hQ_tree : ∀ k, IsTreeSubgraph (Q k))
    (hQ_leaves : ∀ k, {v | IsLeafOf (Q k) v}.ncard = θ)
    (hQ_disj : Pairwise fun k k' ↦ Disjoint (Q k).verts (Q k').verts)
    (hPQ_inter : ∀ i k, ((P i).verts ∩ (Q k).verts).ncard = 1)
    (hPQ_leaf : ∀ i k, ∀ v ∈ (P i).verts ∩ (Q k).verts, IsLeafOf (Q k) v)
    (hP_ord : ∀ i, (P i).MeetsInOrder Q) :
    r < θ * (θ - 1) := by
  classical
  let L (k : Fin r) : Set α := {v | IsLeafOf (Q k) v}
  let C (k : Fin r) : (⊤ : SimpleGraph α).Subgraph := (Q k).deleteVerts (L k)
  have hC_le_Q : ∀ k, C k ≤ Q k := fun _ ↦ Subgraph.deleteVerts_le
  have hQ_fin : ∀ k, (Q k).verts.Finite := fun k ↦ hG_fin.subset (hQ_le k).1
  have hL_ge3 : ∀ k, 3 ≤ (L k).ncard := by
    intro k
    change 3 ≤ {v | IsLeafOf (Q k) v}.ncard
    rw [hQ_leaves k]
    omega
  have hC_conn : ∀ k, (C k).Connected :=
    fun k ↦ (connected_deleteVerts_leaves (hQ_fin k) (hQ_tree k).connected (hL_ge3 k)).1
  have h_ex_c : ∀ k, ∃ c, c ∈ (C k).verts := fun k ↦ (hC_conn k).nonempty
  choose c hc using h_ex_c
  let S (k : Fin r) : (⊤ : SimpleGraph α).Subgraph := starOfTree (Q k) (c k)
  have hS_verts_sub : ∀ k, (S k).verts ⊆ (Q k).verts :=
    fun k ↦ starOfTree_verts_subset ((hC_le_Q k).1 (hc k))
  have hP_disj_C : ∀ i k, Disjoint (P i).verts (C k).verts := by
    intro i k
    rw [Set.disjoint_left]
    intro x hxP hxC
    exact hxC.2 (hPQ_leaf i k x ⟨hxP, hxC.1⟩)
  let G_seq : ℕ → (⊤ : SimpleGraph α).Subgraph := fun t ↦
    Nat.recOn t G (fun t' Gt' ↦
      if ht' : t' < r then contractSubgraph Gt' (C ⟨t', ht'⟩) (c ⟨t', ht'⟩) else Gt')
  have hQ_le_seq : ∀ (t : ℕ) (k : Fin r), t ≤ k.val → Q k ≤ G_seq t := by
    intro t
    induction t with
    | zero => exact fun k _ ↦ hQ_le k
    | succ t' ih =>
      intro k htk
      have ht' : t' < r := lt_of_lt_of_le (Nat.lt_succ_self t') (htk.trans (le_of_lt k.isLt))
      change Q k ≤ (if ht' : t' < r then contractSubgraph (G_seq t') (C ⟨t', ht'⟩) (c ⟨t', ht'⟩)
        else G_seq t')
      rw [dite_eq_left ht']
      refine le_contractSubgraph_of_disjoint (ih k (Nat.le_of_succ_le htk)) ?_
      have hne : k ≠ ⟨t', ht'⟩ := fun h ↦ by
        have := congrArg Fin.val h
        dsimp at this
        omega
      exact (hQ_disj hne).mono_right (sdiff_subset.trans (hC_le_Q ⟨t', ht'⟩).1)
  have hG_seq_props : ∀ t : ℕ, (G_seq t).verts.Finite ∧ G_seq t ∈ 𝓕 θ := by
    intro t
    induction t with
    | zero => exact ⟨hG_fin, hG⟩
    | succ t' ih =>
      change (if ht' : t' < r then contractSubgraph (G_seq t') (C ⟨t', ht'⟩) (c ⟨t', ht'⟩)
        else G_seq t').verts.Finite ∧
        (if ht' : t' < r then contractSubgraph (G_seq t') (C ⟨t', ht'⟩) (c ⟨t', ht'⟩)
        else G_seq t') ∈ 𝓕 θ
      split_ifs with ht'
      · have hC_le_t' : C ⟨t', ht'⟩ ≤ G_seq t' :=
          (hC_le_Q ⟨t', ht'⟩).trans (hQ_le_seq t' ⟨t', ht'⟩ le_rfl)
        exact ⟨ih.1.subset (contractSubgraph_verts_subset _ _ _),
          mem_𝓕_contractSubgraph ih.1 ih.2 hC_le_t' (hC_conn ⟨t', ht'⟩) (hc ⟨t', ht'⟩)⟩
      · exact ih
  have hP_le_seq : ∀ (t : ℕ) (i : Fin θ), (P i).toSubgraph ≤ G_seq t := by
    intro t i
    induction t with
    | zero => exact hP_in i
    | succ t' ih =>
      change (P i).toSubgraph ≤ (if ht' : t' < r then
        contractSubgraph (G_seq t') (C ⟨t', ht'⟩) (c ⟨t', ht'⟩) else G_seq t')
      split_ifs with ht'
      · exact le_contractSubgraph_of_disjoint ih
          ((hP_disj_C i ⟨t', ht'⟩).mono_right sdiff_subset)
      · exact ih
  have hS_le_seq : ∀ (t : ℕ) (k : Fin r), k.val + 1 ≤ t → S k ≤ G_seq t := by
    intro t
    induction t with
    | zero =>
      intro k hk
      omega
    | succ t' ih =>
      intro k hk
      change S k ≤ (if ht' : t' < r then
        contractSubgraph (G_seq t') (C ⟨t', ht'⟩) (c ⟨t', ht'⟩) else G_seq t')
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hlt
      · rw [dite_eq_left k.isLt]
        exact starOfTree_le_contractSubgraph (hQ_le_seq k.val k le_rfl)
          (hQ_fin k) (hQ_tree k).connected (hL_ge3 k) (hc k)
      · split_ifs with ht'
        · refine le_contractSubgraph_of_disjoint (ih k hlt) ?_
          have hne : k ≠ ⟨t', ht'⟩ := fun h ↦ by
            have := congrArg Fin.val h
            dsimp at this
            omega
          exact ((hQ_disj hne).mono_left (hS_verts_sub k)).mono_right
            (sdiff_subset.trans (hC_le_Q ⟨t', ht'⟩).1)
        · exact ih k hlt
  let G' := G_seq r
  have hG'_fin : G'.verts.Finite := (hG_seq_props r).1
  have hG'_mem : G' ∈ 𝓕 θ := (hG_seq_props r).2
  have hPS_inter_eq : ∀ i k, (P i).verts ∩ (S k).verts = (P i).verts ∩ (Q k).verts := by
    intro i k
    ext x
    refine ⟨fun ⟨hxP, hxS⟩ ↦ ⟨hxP, hS_verts_sub k hxS⟩, fun ⟨hxP, hxQ⟩ ↦ ⟨hxP, ?_⟩⟩
    exact Or.inr (hPQ_leaf i k x ⟨hxP, hxQ⟩)
  have h2_2 := theorem_2_2_simple (by omega : 3 ≤ θ) hG'_fin hG'_mem P S c
    (fun i ↦ hP_le_seq r i) hP_disj
    (fun k ↦ hS_le_seq r k k.isLt)
    (fun k ↦ isStarWithCenter_starOfTree (Q k) (c k))
    (fun k₁ k₂ hne ↦ (hQ_disj hne).mono (hS_verts_sub k₁) (hS_verts_sub k₂))
    (fun i k ↦ by rw [hPS_inter_eq i k]; exact hPQ_inter i k)
    (fun i k hcP ↦ (hP_disj_C i k).notMem_of_mem_left hcP (hc k))
    (fun i k₁ k₂ hlt u hu v hv ↦ by
      rw [hPS_inter_eq i k₁] at hu
      rw [hPS_inter_eq i k₂] at hv
      exact hP_ord i hlt u hu v hv)
  exact h2_2.resolve_left (Nat.lt_irrefl θ)

/-! ### Main theorems (2.3) and (2.4) -/

/-- **Graph Minors I, (2.3)** (page 43):
"If $P_1, \dots, P_m$ are disjoint paths of $G \in \mathcal{F}_\theta$, and $B_1, \dots, B_n$ are
disjoint connected subgraphs of $G$, and each $P_i$ meets each $B_j$, and for $1 \le j < j' \le n$
all vertices of $B_j$ on $P_i$ occur before all vertices of $B_{j'}$, then either
$m < \frac{1}{2}\theta^2$ or $n < \theta^{2\theta - 2}$."
This is the simple special case. The full statement is `GM01.Full.theorem_2_3_proof`. -/
theorem theorem_2_3_simple {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    {G : (⊤ : SimpleGraph α).Subgraph} (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (P : Fin m → Path α) (B : Fin n → (⊤ : SimpleGraph α).Subgraph)
    (hP_in : ∀ i, (P i).IsIn G)
    (hP_disj : Pairwise fun i i' ↦ Disjoint (P i).verts (P i').verts)
    (hB_le : ∀ j, B j ≤ G)
    (hB_conn : ∀ j, (B j).Connected)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (hPB_meet : ∀ i j, ((P i).verts ∩ (B j).verts).Nonempty)
    (hP_ord : ∀ i, (P i).MeetsInOrder B) :
    m < θ ^ 2 / 2 ∨ n < θ ^ (2 * θ - 2) := by
  classical
  -- Proceed by strong induction on `|E(G)| + m` (a minimal counterexample in `|E(G)| + m`).
  suffices h_ind : ∀ (M : ℕ) (m : ℕ) (G : (⊤ : SimpleGraph α).Subgraph)
      (P : Fin m → Path α) (B : Fin n → (⊤ : SimpleGraph α).Subgraph),
      G.edgeSet.ncard + m = M →
      G.verts.Finite → G ∈ 𝓕 θ →
      (∀ i, (P i).IsIn G) →
      (Pairwise fun i i' ↦ Disjoint (P i).verts (P i').verts) →
      (∀ j, B j ≤ G) →
      (∀ j, (B j).Connected) →
      (Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts) →
      (∀ i j, ((P i).verts ∩ (B j).verts).Nonempty) →
      (∀ i, (P i).MeetsInOrder B) →
      m < θ ^ 2 / 2 ∨ n < θ ^ (2 * θ - 2) from
    h_ind (G.edgeSet.ncard + m) m G P B rfl hG_fin hG hP_in hP_disj hB_le hB_conn hB_disj
      hPB_meet hP_ord
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro m G P B hM hG_fin hG hP_in hP_disj hB_le hB_conn hB_disj hPB_meet hP_ord
    by_contra! h_contra
    obtain ⟨hm_ge, hn_ge⟩ := h_contra
    -- Step 0: "Then evidently we have `m = ½ θ²`."
    have hm_eq : m = θ ^ 2 / 2 := by
      rcases eq_or_lt_of_le hm_ge with heq | hlt
      · exact heq.symm
      · exfalso
        let P' : Fin (θ ^ 2 / 2) → Path α := fun i ↦ P (Fin.castLE hm_ge i)
        have hlt_M : G.edgeSet.ncard + θ ^ 2 / 2 < M := by omega
        have hres := ih (G.edgeSet.ncard + θ ^ 2 / 2) hlt_M (θ ^ 2 / 2) G P' B rfl hG_fin hG
          (fun i ↦ hP_in _)
          (fun _ _ hne ↦ hP_disj ((Fin.castLE_injective hm_ge).ne hne))
          hB_le hB_conn hB_disj (fun i j ↦ hPB_meet _ j) (fun i ↦ hP_ord _)
        rcases hres with h1 | h2 <;> omega
    -- Step 1: "If some `Pᵢ` has more than one vertex in common with some `Bⱼ`, we may contract the
    -- edges of `Pᵢ` between the two vertices of `Bⱼ` and produce a smaller counterexample."
    have hPB_one : ∀ i j, ((P i).verts ∩ (B j).verts).ncard = 1 := by
      intro i₀ j₀
      have hfin_inter : ((P i₀).verts ∩ (B j₀).verts).Finite :=
        (P i₀).verts_finite.subset inter_subset_left
      have hpos : 1 ≤ ((P i₀).verts ∩ (B j₀).verts).ncard :=
        (ncard_pos hfin_inter).2 (hPB_meet i₀ j₀)
      rcases eq_or_lt_of_le hpos with heq | hgt
      · exact heq.symm
      · exfalso
        obtain ⟨x, y, hx, hy, hxy⟩ := (one_lt_ncard_iff hfin_inter).1 hgt
        have h_ex_uv : ∃ u v, u ∈ (P i₀).verts ∩ (B j₀).verts ∧
            v ∈ (P i₀).verts ∩ (B j₀).verts ∧ (P i₀).Precedes u v := by
          rcases (P i₀).precedes_or_eq_or_precedes hx.1 hy.1 with hprec | rfl | hprec
          · exact ⟨x, y, hx, hy, hprec⟩
          · exact (hxy rfl).elim
          · exact ⟨y, x, hy, hx, hprec⟩
        obtain ⟨u, v, ⟨huP, huB⟩, ⟨hvP, hvB⟩, huv⟩ := h_ex_uv
        let R := (P i₀).subpath u v huP hvP (Or.inl huv)
        have hR_le_P : R.toSubgraph ≤ (P i₀).toSubgraph := (P i₀).subpath_toSubgraph_le _ _ _
        have hR_le_G : R.toSubgraph ≤ G := hR_le_P.trans (hP_in i₀)
        have huR : u ∈ R.verts := by
          change u ∈ ((P i₀).subpath u v huP hvP (Or.inl huv)).verts
          rw [(P i₀).mem_subpath_verts_iff]
          exact ⟨huP, Or.inr rfl, Or.inl huv⟩
        have hR_edge : R.toSubgraph.edgeSet.Nonempty := by
          have hne_uv : R.first ≠ R.last := by
            rw [(P i₀).subpath_first, (P i₀).subpath_last]
            exact huv.ne
          have hnil : ¬ R.walk.Nil := Walk.not_nil_of_ne hne_uv
          exact ⟨s(R.first, R.walk.snd), R.walk.toSubgraph_adj_snd hnil⟩
        have hB_disj_R : ∀ j, j ≠ j₀ → Disjoint (B j).verts R.verts := by
          intro j hne
          rw [Set.disjoint_left]
          intro w hwB hwR
          have hwP : w ∈ (P i₀).verts := hR_le_P.1 hwR
          change w ∈ ((P i₀).subpath u v huP hvP (Or.inl huv)).verts at hwR
          rw [(P i₀).mem_subpath_verts_iff] at hwR
          rcases lt_trichotomy j j₀ with hlt | rfl | hgt
          · have hwu := hP_ord i₀ hlt w ⟨hwP, hwB⟩ u ⟨huP, huB⟩
            rcases hwR.2.1 with huw | rfl
            · exact hwu.asymm huw
            · exact hwu.ne rfl
          · exact hne rfl
          · have hvw := hP_ord i₀ hgt v ⟨hvP, hvB⟩ w ⟨hwP, hwB⟩
            rcases hwR.2.2 with hwv | rfl
            · exact hvw.asymm hwv
            · exact hvw.ne rfl
        let G' := contractSubgraph G R.toSubgraph u
        let P' : Fin m → Path α := fun i ↦
          if i = i₀ then (P i₀).contractSubpath u v huP hvP huv else P i
        let B' : Fin n → (⊤ : SimpleGraph α).Subgraph := fun j ↦
          contractSubgraphMap R.verts u (B j)
        have hG'_fin : G'.verts.Finite := hG_fin.subset (contractSubgraph_verts_subset _ _ _)
        have hG'_mem : G' ∈ 𝓕 θ :=
          mem_𝓕_contractSubgraph hG_fin hG hR_le_G R.connected_toSubgraph huR
        have hG'_lt : G'.edgeSet.ncard < G.edgeSet.ncard :=
          ncard_edgeSet_contractSubgraph_lt hG_fin hR_le_G hR_edge u
        have hP'_verts_sub : ∀ i, (P' i).verts ⊆ (P i).verts := by
          intro i
          dsimp [P']
          split_ifs with hi
          · subst hi
            rw [(P i).contractSubpath_verts u v huP hvP huv]
            rintro x ⟨z, hz, rfl⟩
            by_cases hzR : z ∈ R.verts
            · rw [contractMap_of_mem hzR]
              exact huP
            · rw [contractMap_of_notMem hzR]
              exact hz
          · exact Subset.rfl
        have hB'_eq_of_ne : ∀ j, j ≠ j₀ → B' j = B j :=
          fun j hne ↦ contractSubgraphMap_eq_of_disjoint (hB_disj_R j hne)
        have hB'_verts_sub : ∀ j, (B' j).verts ⊆ (B j).verts := by
          intro j
          by_cases hj : j = j₀
          · subst hj
            dsimp [B', contractSubgraphMap]
            rintro x ⟨z, hz, rfl⟩
            by_cases hzR : z ∈ R.verts
            · rw [contractMap_of_mem hzR]
              exact huB
            · rw [contractMap_of_notMem hzR]
              exact hz
          · rw [hB'_eq_of_ne j hj]
        have hP'_in : ∀ i, (P' i).IsIn G' := by
          intro i
          dsimp [P']
          split_ifs with hi
          · exact (P i₀).contractSubpath_toSubgraph_le (hP_in i₀) u v huP hvP huv
          · refine le_contractSubgraph_of_disjoint (hP_in i) ?_
            exact (hP_disj hi).mono_right (sdiff_subset.trans hR_le_P.1)
        have hP'_disj : Pairwise fun i i' ↦ Disjoint (P' i).verts (P' i').verts :=
          fun i i' hne ↦ (hP_disj hne).mono (hP'_verts_sub i) (hP'_verts_sub i')
        have hB'_le : ∀ j, B' j ≤ G' :=
          fun j ↦ contractSubgraphMap_le ((hP_in i₀).1 huP) (hB_le j)
        have hB'_conn : ∀ j, (B' j).Connected :=
          fun j ↦ contractSubgraphMap_connected (hB_conn j)
        have hB'_disj : Pairwise fun j j' ↦ Disjoint (B' j).verts (B' j').verts :=
          fun j j' hne ↦ (hB_disj hne).mono (hB'_verts_sub j) (hB'_verts_sub j')
        have hP'B'_meet : ∀ i j, ((P' i).verts ∩ (B' j).verts).Nonempty := by
          intro i j
          by_cases hi : i = i₀ <;> by_cases hj : j = j₀
          · subst hi hj
            refine ⟨u, ?_, ?_⟩
            · simp only [P', ite_true, (P i).contractSubpath_verts u v huP hvP huv]
              exact ⟨u, huP, contractMap_of_mem huR⟩
            · exact ⟨u, huB, contractMap_of_mem huR⟩
          · subst hi
            obtain ⟨w, hwP, hwB⟩ := hPB_meet i j
            have hwR : w ∉ R.verts := (hB_disj_R j hj).notMem_of_mem_left hwB
            refine ⟨w, ?_, ?_⟩
            · simp only [P', ite_true, (P i).contractSubpath_verts u v huP hvP huv]
              exact ⟨w, hwP, contractMap_of_notMem hwR⟩
            · rw [hB'_eq_of_ne j hj]
              exact hwB
          · obtain ⟨w, hwP, hwB⟩ := hPB_meet i j
            have hwR : w ∉ R.verts := (hP_disj hi).notMem_of_mem_left hwP ∘ (fun h ↦ hR_le_P.1 h)
            refine ⟨w, ?_, ?_⟩
            · simp only [P', ite_eq_right hi]
              exact hwP
            · exact ⟨w, hwB, contractMap_of_notMem hwR⟩
          · obtain ⟨w, hwP, hwB⟩ := hPB_meet i j
            refine ⟨w, ?_, ?_⟩
            · simp only [P', ite_eq_right hi]
              exact hwP
            · rw [hB'_eq_of_ne j hj]
              exact hwB
        have hP'_ord : ∀ i, (P' i).MeetsInOrder B' := by
          intro i j₁ j₂ hlt x hx y hy
          have hx_orig : x ∈ (P i).verts ∩ (B j₁).verts :=
            ⟨hP'_verts_sub i hx.1, hB'_verts_sub j₁ hx.2⟩
          have hy_orig : y ∈ (P i).verts ∩ (B j₂).verts :=
            ⟨hP'_verts_sub i hy.1, hB'_verts_sub j₂ hy.2⟩
          have hprec := hP_ord i hlt x hx_orig y hy_orig
          dsimp [P'] at hx hy ⊢
          split_ifs at hx hy ⊢ with hi
          · subst hi
            exact ((P i).contractSubpath_precedes_iff u v huP hvP huv hx.1 hy.1).2 hprec
          · exact hprec
        have hres := ih (G'.edgeSet.ncard + m) (by omega) m G' P' B' rfl hG'_fin hG'_mem
          hP'_in hP'_disj hB'_le hB'_conn hB'_disj hP'B'_meet hP'_ord
        rcases hres with h1 | h2 <;> omega
    -- Step 2: "Each `Bⱼ` is a tree, for if some `Bⱼ` is not, we may delete an edge from it and
    -- produce a smaller counterexample."
    have hB_tree : ∀ j, IsTreeSubgraph (B j) := by
      intro j₀
      by_contra hnot_tree
      obtain ⟨e, heB₀, hdel_conn⟩ :=
        exists_edge_deleteEdges_connected_of_not_isTreeSubgraph (hB_conn j₀) hnot_tree
      have heG : e ∈ G.edgeSet := Subgraph.edgeSet_mono (hB_le j₀) heB₀
      let G' := G.deleteEdges {e}
      let B' : Fin n → (⊤ : SimpleGraph α).Subgraph := fun j ↦
        if j = j₀ then (B j₀).deleteEdges {e} else B j
      have hG'_fin : G'.verts.Finite := hG_fin
      have hG'_mem : G' ∈ 𝓕 θ := mem_𝓕_of_le (Subgraph.deleteEdges_le {e}) hG
      have hG'_lt : G'.edgeSet.ncard < G.edgeSet.ncard := by
        have hedge_eq : G'.edgeSet = G.edgeSet \ {e} := by
          ext x
          induction x with | h a b =>
          simp [G', Subgraph.deleteEdges_adj]
        rw [hedge_eq, ncard_sdiff_singleton_of_mem heG]
        have : 1 ≤ G.edgeSet.ncard :=
          (ncard_pos (finite_edgeSet_of_finite_verts hG_fin)).2 ⟨e, heG⟩
        omega
      have hB'_verts : ∀ j, (B' j).verts = (B j).verts := by
        intro j
        dsimp [B']
        split_ifs with hj
        · subst hj; rfl
        · rfl
      have hP_in' : ∀ i, (P i).IsIn G' := by
        intro i
        have he_notP : e ∉ (P i).toSubgraph.edgeSet :=
          notMem_edgeSet_of_ncard_inter_le_one (by rw [hPB_one i j₀]) heB₀
        refine ⟨(hP_in i).1, fun x y hxy ↦ ?_⟩
        rw [Subgraph.deleteEdges_adj, mem_singleton_iff]
        exact ⟨(hP_in i).2 hxy, fun heq ↦ he_notP (heq ▸ hxy)⟩
      have hB'_le : ∀ j, B' j ≤ G' := by
        intro j
        dsimp [B']
        split_ifs with hj
        · refine ⟨(hB_le j₀).1, fun x y hxy ↦ ?_⟩
          rw [Subgraph.deleteEdges_adj] at hxy ⊢
          exact ⟨(hB_le j₀).2 hxy.1, hxy.2⟩
        · refine ⟨(hB_le j).1, fun x y hxy ↦ ?_⟩
          rw [Subgraph.deleteEdges_adj, mem_singleton_iff]
          refine ⟨(hB_le j).2 hxy, fun heq ↦ ?_⟩
          have hxB₀ : x ∈ (B j₀).verts := (B j₀).edge_vert (heq ▸ heB₀)
          exact (hB_disj hj).notMem_of_mem_left hxy.fst_mem hxB₀
      have hB'_conn : ∀ j, (B' j).Connected := by
        intro j
        dsimp [B']
        split_ifs with hj
        · exact hdel_conn
        · exact hB_conn j
      have hB'_disj : Pairwise fun j j' ↦ Disjoint (B' j).verts (B' j').verts := by
        intro j j' hne
        rw [hB'_verts j, hB'_verts j']
        exact hB_disj hne
      have hPB'_meet : ∀ i j, ((P i).verts ∩ (B' j).verts).Nonempty := by
        intro i j
        rw [hB'_verts j]
        exact hPB_meet i j
      have hP_ord' : ∀ i, (P i).MeetsInOrder B' := by
        intro i j₁ j₂ hlt u hu v hv
        rw [hB'_verts j₁] at hu
        rw [hB'_verts j₂] at hv
        exact hP_ord i hlt u hu v hv
      have hres := ih (G'.edgeSet.ncard + m) (by omega) m G' P B' rfl hG'_fin hG'_mem
        hP_in' hP_disj hB'_le hB'_conn hB'_disj hPB'_meet hP_ord'
      rcases hres with h1 | h2 <;> omega
    -- Step 3: "Every vertex `v` of each `Bⱼ` is on some `Pᵢ`; for if not, we may contract some edge
    -- of `Bⱼ` incident with `v` and produce a smaller counterexample."
    have hB_verts_sub : ∀ j, (B j).verts ⊆ ⋃ i, (P i).verts := by
      intro j₀ y hyB₀
      by_contra hy_notP
      have hi₀_lt : 0 < m := by
        have : 6 * 6 ≤ θ ^ 2 := by nlinarith
        omega
      let i₀ : Fin m := ⟨0, hi₀_lt⟩
      obtain ⟨x₀, hx₀P, hx₀B⟩ := hPB_meet i₀ j₀
      have hx₀_U : x₀ ∈ ⋃ i, (P i).verts := mem_iUnion.2 ⟨i₀, hx₀P⟩
      obtain ⟨u, v, hadj_uv, hv_notP⟩ :=
        exists_adj_notMem_of_connected (hB_conn j₀) hx₀B hx₀_U hyB₀ hy_notP
      let C := (⊤ : SimpleGraph α).subgraphOfAdj (Subgraph.adj_sub _ hadj_uv)
      have hC_le_B₀ : C ≤ B j₀ := subgraphOfAdj_le_of_adj _ hadj_uv
      have hC_le_G : C ≤ G := hC_le_B₀.trans (hB_le j₀)
      have hC_conn : C.Connected := Subgraph.subgraphOfAdj_connected _
      have huC : u ∈ C.verts := by simp [C]
      have hC_edge : C.edgeSet.Nonempty := ⟨s(u, v), by simp [C]⟩
      have hC_sdiff : C.verts \ {u} = {v} := by
        ext z
        simp only [C, subgraphOfAdj_verts, mem_sdiff, mem_insert_iff, mem_singleton_iff]
        exact ⟨fun ⟨h, hne⟩ ↦ h.resolve_left hne, fun h ↦ ⟨Or.inr h, h ▸ hadj_uv.ne.symm⟩⟩
      let G' := contractSubgraph G C u
      let B' : Fin n → (⊤ : SimpleGraph α).Subgraph := fun j ↦
        contractSubgraphMap C.verts u (B j)
      have hG'_fin : G'.verts.Finite := hG_fin.subset (contractSubgraph_verts_subset _ _ _)
      have hG'_mem : G' ∈ 𝓕 θ := mem_𝓕_contractSubgraph hG_fin hG hC_le_G hC_conn huC
      have hG'_lt : G'.edgeSet.ncard < G.edgeSet.ncard :=
        ncard_edgeSet_contractSubgraph_lt hG_fin hC_le_G hC_edge u
      have hP_disj_C : ∀ i, Disjoint (P i).verts (C.verts \ {u}) := by
        intro i
        rw [hC_sdiff, disjoint_singleton_right]
        exact fun hvP ↦ hv_notP (mem_iUnion.2 ⟨i, hvP⟩)
      have hP_in' : ∀ i, (P i).IsIn G' :=
        fun i ↦ le_contractSubgraph_of_disjoint (hP_in i) (hP_disj_C i)
      have hB'_verts_sub : ∀ j, (B' j).verts ⊆ (B j).verts := by
        intro j
        by_cases hj : j = j₀
        · subst hj
          dsimp [B', contractSubgraphMap]
          rintro z ⟨w, hwB, rfl⟩
          by_cases hwC : w ∈ C.verts
          · rw [contractMap_of_mem hwC]
            exact hadj_uv.fst_mem
          · rw [contractMap_of_notMem hwC]
            exact hwB
        · rw [show B' j = B j from contractSubgraphMap_eq_of_disjoint
            ((hB_disj hj).mono_right hC_le_B₀.1)]
      have hPB'_eq : ∀ i j, (P i).verts ∩ (B' j).verts = (P i).verts ∩ (B j).verts := by
        intro i j
        ext z
        refine ⟨fun ⟨hzP, hzB'⟩ ↦ ⟨hzP, hB'_verts_sub j hzB'⟩, fun ⟨hzP, hzB⟩ ↦ ⟨hzP, ?_⟩⟩
        have hzv : z ≠ v := fun heq ↦ hv_notP (mem_iUnion.2 ⟨i, heq ▸ hzP⟩)
        by_cases hzu : z = u
        · subst hzu
          exact ⟨z, hzB, contractMap_of_mem huC⟩
        · have hz_notC : z ∉ C.verts := by
            intro hzC
            have : z ∈ C.verts \ {u} := ⟨hzC, hzu⟩
            rw [hC_sdiff, mem_singleton_iff] at this
            exact hzv this
          exact ⟨z, hzB, contractMap_of_notMem hz_notC⟩
      have hB'_le : ∀ j, B' j ≤ G' :=
        fun j ↦ contractSubgraphMap_le ((hB_le j₀).1 hadj_uv.fst_mem) (hB_le j)
      have hB'_conn : ∀ j, (B' j).Connected :=
        fun j ↦ contractSubgraphMap_connected (hB_conn j)
      have hB'_disj : Pairwise fun j j' ↦ Disjoint (B' j).verts (B' j').verts :=
        fun j j' hne ↦ (hB_disj hne).mono (hB'_verts_sub j) (hB'_verts_sub j')
      have hPB'_meet : ∀ i j, ((P i).verts ∩ (B' j).verts).Nonempty := by
        intro i j
        rw [hPB'_eq i j]
        exact hPB_meet i j
      have hP_ord' : ∀ i, (P i).MeetsInOrder B' := by
        intro i j₁ j₂ hlt x hx y hy
        rw [hPB'_eq i j₁] at hx
        rw [hPB'_eq i j₂] at hy
        exact hP_ord i hlt x hx y hy
      have hres := ih (G'.edgeSet.ncard + m) (by omega) m G' P B' rfl hG'_fin hG'_mem
        hP_in' hP_disj hB'_le hB'_conn hB'_disj hPB'_meet hP_ord'
      rcases hres with h1 | h2 <;> omega
    -- "It follows that each `Bⱼ` has exactly `½ θ²` vertices."
    have h_ex_v : ∀ i j, ∃ v, (P i).verts ∩ (B j).verts = {v} :=
      fun i j ↦ ncard_eq_one.1 (hPB_one i j)
    choose vPB hvPB using h_ex_v
    have hvPB_P : ∀ i j, vPB i j ∈ (P i).verts := by
      intro i j
      have : vPB i j ∈ (P i).verts ∩ (B j).verts := by rw [hvPB i j]; exact rfl
      exact this.1
    have hvPB_B : ∀ i j, vPB i j ∈ (B j).verts := by
      intro i j
      have : vPB i j ∈ (P i).verts ∩ (B j).verts := by rw [hvPB i j]; exact rfl
      exact this.2
    have hvPB_inj : ∀ j, Function.Injective (fun i : Fin m ↦ vPB i j) := by
      intro j i₁ i₂ heq
      by_contra hne
      change vPB i₁ j = vPB i₂ j at heq
      exact (hP_disj hne).notMem_of_mem_left (hvPB_P i₁ j) (heq ▸ hvPB_P i₂ j)
    have hB_verts_range : ∀ j, (B j).verts = Set.range (fun i : Fin m ↦ vPB i j) := by
      intro j
      ext x
      refine ⟨fun hxB ↦ ?_, ?_⟩
      · obtain ⟨i, hxP⟩ := mem_iUnion.1 (hB_verts_sub j hxB)
        have hx_inter : x ∈ (P i).verts ∩ (B j).verts := ⟨hxP, hxB⟩
        rw [hvPB i j, mem_singleton_iff] at hx_inter
        exact ⟨i, hx_inter.symm⟩
      · rintro ⟨i, rfl⟩
        exact hvPB_B i j
    have hB_ncard : ∀ j, (B j).verts.ncard = θ ^ 2 / 2 := by
      intro j
      rw [hB_verts_range j, ncard_range_of_injective (hvPB_inj j), Nat.card_fin, hm_eq]
    -- Step 4: "It is elementary that for `1 ≤ j ≤ n`, `Bⱼ` has a subgraph `Qⱼ` which is either a
    -- path with `θ` vertices or a tree with `θ` end-vertices."
    have h_ex_Q : ∀ j, ∃ Q ≤ B j,
        (IsPathSubgraph Q ∧ Q.verts.ncard = θ) ∨
        (IsTreeSubgraph Q ∧ {v | IsLeafOf Q v}.ncard = θ) :=
      fun j ↦ (hB_tree j).exists_path_or_tree_leaves (hG_fin.subset (hB_le j).1)
        hθ heven (hB_ncard j)
    choose Q hQ_le hQ_prop using h_ex_Q
    have hnot_path_of_leaves : ∀ {H : (⊤ : SimpleGraph α).Subgraph},
        {v | IsLeafOf H v}.ncard = θ → ¬ IsPathSubgraph H := by
      rintro H hleaves ⟨P₀, rfl⟩
      have hsub : {v | IsLeafOf P₀.toSubgraph v} ⊆ ({P₀.first, P₀.last} : Set α) := by
        intro x hx
        by_contra hne
        rw [mem_insert_iff, mem_singleton_iff, not_or] at hne
        exact not_isLeafOf_of_internal_mem_path P₀.verts_finite le_rfl hx.1 hne.1 hne.2 hx
      have hpair_le : ({P₀.first, P₀.last} : Set α).ncard ≤ 2 := by
        simpa using ncard_insert_le P₀.first {P₀.last}
      have hle2 : {v | IsLeafOf P₀.toSubgraph v}.ncard ≤ 2 :=
        (ncard_le_ncard hsub (Set.toFinite _)).trans hpair_le
      omega
    let W (j : Fin n) : Set α :=
      if IsPathSubgraph (Q j) then (Q j).verts else {v | IsLeafOf (Q j) v}
    have hW_sub_Q : ∀ j, W j ⊆ (Q j).verts := by
      intro j
      dsimp [W]
      split_ifs
      · exact Subset.rfl
      · exact fun _ hx ↦ hx.1
    have hW_ncard : ∀ j, (W j).ncard = θ := by
      intro j
      dsimp [W]
      split_ifs with hpath
      · rcases hQ_prop j with ⟨_, hcard⟩ | ⟨_, hcard⟩
        · exact hcard
        · exact (hnot_path_of_leaves hcard hpath).elim
      · rcases hQ_prop j with ⟨hpath', _⟩ | ⟨_, hcard⟩
        · exact (hpath hpath').elim
        · exact hcard
    -- "For `1 ≤ j ≤ n`, let `Iⱼ ⊆ {1, …, ½ θ²}` be `{i : Pᵢ meets Qⱼ in some vertex which, if Qⱼ is
    -- not a path, is an end-vertex of Qⱼ}`. Then `|Iⱼ| = θ` for all `j`."
    let I (j : Fin n) : Finset (Fin m) :=
      Finset.univ.filter (fun i ↦ vPB i j ∈ W j)
    have hI_card : ∀ j, (I j).card = θ := by
      intro j
      have hW_image : W j = (fun i : Fin m ↦ vPB i j) '' (I j : Set (Fin m)) := by
        ext x
        simp only [I, Finset.coe_filter, mem_image, mem_ofPred_eq]
        refine ⟨fun hxW ↦ ?_, ?_⟩
        · have hxB : x ∈ (B j).verts := (hQ_le j).1 (hW_sub_Q j hxW)
          rw [hB_verts_range j] at hxB
          rcases hxB with ⟨i, rfl⟩
          exact ⟨i, ⟨Finset.mem_univ _, hxW⟩, rfl⟩
        · rintro ⟨i, ⟨_, hiW⟩, rfl⟩
          exact hiW
      rw [← hW_ncard j, hW_image, ncard_image_of_injective _ (hvPB_inj j), ncard_coe_finset]
    let SubI := (Finset.powersetCard θ (Finset.univ : Finset (Fin m)))
    have hcard_SubI : Fintype.card SubI = (θ ^ 2 / 2).choose θ := by
      rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, hm_eq]
    have hI_mem_SubI : ∀ j, I j ∈ SubI :=
      fun j ↦ Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hI_card j⟩
    have hSubI_nonempty : Nonempty SubI := by
      have hn_pos : 0 < n := by
        have : 1 ≤ θ ^ (2 * θ - 2) := Nat.one_le_pow _ _ (by omega)
        omega
      exact ⟨⟨I ⟨0, hn_pos⟩, hI_mem_SubI ⟨0, hn_pos⟩⟩⟩
    let fI : Fin n → SubI := fun j ↦ ⟨I j, hI_mem_SubI j⟩
    let K := θ * θ.factorial / 2 + θ * (θ - 1)
    have h_pigeon : Fintype.card SubI * K ≤ Fintype.card (Fin n) := by
      rw [hcard_SubI, Fintype.card_fin]
      exact (nat_choose_grid_bound_2_3 hθ).trans hn_ge
    obtain ⟨I₀, hI₀_card⟩ := Fintype.exists_le_card_fiber_of_mul_le_card fI h_pigeon
    have hI₀_len : I₀.1.card = θ := (Finset.mem_powersetCard.1 I₀.2).2
    let J : Finset (Fin n) := Finset.univ.filter (fun j ↦ fI j = I₀)
    have hJ_card : K ≤ J.card := hI₀_card
    let J₁ : Finset (Fin n) := J.filter (fun j ↦ IsPathSubgraph (Q j))
    let J₂ : Finset (Fin n) := J.filter (fun j ↦ ¬ IsPathSubgraph (Q j))
    have hJ_split : J.card = J₁.card + J₂.card :=
      (Finset.card_filter_add_card_filter_not _).symm
    let embI := I₀.1.orderEmbOfFin hI₀_len
    let P_sub (a : Fin θ) : Path α := P (embI a)
    have hP_sub_in : ∀ a, (P_sub a).IsIn G := fun a ↦ hP_in (embI a)
    have hP_sub_disj : Pairwise fun a₁ a₂ ↦ Disjoint (P_sub a₁).verts (P_sub a₂).verts :=
      fun _ _ hne ↦ hP_disj (embI.injective.ne hne)
    have hv_mem_W : ∀ (a : Fin θ) {j : Fin n}, j ∈ J → vPB (embI a) j ∈ W j := by
      intro a j hj
      have hjI : I j = I₀.1 := congrArg Subtype.val (Finset.mem_filter.1 hj).2
      have ha_mem : embI a ∈ I j := hjI ▸ I₀.1.orderEmbOfFin_mem hI₀_len a
      exact (Finset.mem_filter.1 ha_mem).2
    have hPQ_inter_eq : ∀ (a : Fin θ) {j : Fin n}, j ∈ J →
        (P_sub a).verts ∩ (Q j).verts = {vPB (embI a) j} := by
      intro a j hj
      ext x
      rw [mem_singleton_iff]
      refine ⟨fun ⟨hxP, hxQ⟩ ↦ ?_, fun h ↦ ?_⟩
      · have hx_B : x ∈ (P (embI a)).verts ∩ (B j).verts := ⟨hxP, (hQ_le j).1 hxQ⟩
        rwa [hvPB (embI a) j, mem_singleton_iff] at hx_B
      · subst h
        exact ⟨hvPB_P (embI a) j, hW_sub_Q j (hv_mem_W a hj)⟩
    rcases le_or_gt (θ * θ.factorial / 2) J₁.card with hJ₁_ge | hJ₁_lt
    · -- Case 1: `|J₁| ≥ ½ θ · θ!`, contradict (2.1) (`theorem_2_1_simple`).
      let r₁ := J₁.card
      let embJ₁ := J₁.orderEmbOfFin rfl
      have h_ex_P_Q : ∀ k : Fin r₁, ∃ R : Path α, R.toSubgraph = Q (embJ₁ k) := by
        intro k
        have hk : embJ₁ k ∈ J₁ := J₁.orderEmbOfFin_mem rfl k
        exact (Finset.mem_filter.1 hk).2
      choose R₁ hR₁ using h_ex_P_Q
      have h2_1 := theorem_2_1_simple (by omega : 2 ≤ θ) hG_fin hG P_sub R₁ hP_sub_in hP_sub_disj
        (fun k ↦ by
          rw [Path.IsIn, hR₁ k]
          exact (hQ_le (embJ₁ k)).trans (hB_le (embJ₁ k)))
        (fun k₁ k₂ hne ↦ by
          change Disjoint (R₁ k₁).toSubgraph.verts (R₁ k₂).toSubgraph.verts
          rw [hR₁ k₁, hR₁ k₂]
          exact (hB_disj (embJ₁.injective.ne hne)).mono
            (hQ_le (embJ₁ k₁)).1 (hQ_le (embJ₁ k₂)).1)
        (fun a k ↦ by
          change ((P_sub a).verts ∩ (R₁ k).toSubgraph.verts).ncard = 1
          rw [hR₁ k, hPQ_inter_eq a (Finset.mem_filter.1 (J₁.orderEmbOfFin_mem rfl k)).1]
          exact ncard_singleton _)
        (fun a k₁ k₂ hlt u hu v hv ↦ by
          dsimp at hu hv
          rw [hR₁ k₁] at hu
          rw [hR₁ k₂] at hv
          exact hP_ord (embI a) (embJ₁.strictMono hlt) u
            ⟨hu.1, (hQ_le _).1 hu.2⟩ v ⟨hv.1, (hQ_le _).1 hv.2⟩)
      rcases h2_1 with hlt1 | hlt2 <;> omega
    · -- Case 2: `|J₂| ≥ θ(θ - 1)`, contradict `bound_trees_by_2_2` (from (2.2)).
      have hJ₂_ge : θ * (θ - 1) ≤ J₂.card := by omega
      let r₂ := J₂.card
      let embJ₂ := J₂.orderEmbOfFin rfl
      let Q₂ (k : Fin r₂) : (⊤ : SimpleGraph α).Subgraph := Q (embJ₂ k)
      have hk_mem_J₂ : ∀ k : Fin r₂, embJ₂ k ∈ J₂ := fun k ↦ J₂.orderEmbOfFin_mem rfl k
      have hk_mem_J : ∀ k : Fin r₂, embJ₂ k ∈ J := fun k ↦ (Finset.mem_filter.1 (hk_mem_J₂ k)).1
      have hk_not_path : ∀ k : Fin r₂, ¬ IsPathSubgraph (Q₂ k) :=
        fun k ↦ (Finset.mem_filter.1 (hk_mem_J₂ k)).2
      have hk_tree_leaves : ∀ k : Fin r₂,
          IsTreeSubgraph (Q₂ k) ∧ {v | IsLeafOf (Q₂ k) v}.ncard = θ := by
        intro k
        rcases hQ_prop (embJ₂ k) with ⟨hp, _⟩ | htr
        · exact (hk_not_path k hp).elim
        · exact htr
      have hlt_r₂ := bound_trees_by_2_2 hθ hG_fin hG P_sub Q₂ hP_sub_in hP_sub_disj
        (fun k ↦ (hQ_le (embJ₂ k)).trans (hB_le (embJ₂ k)))
        (fun k ↦ (hk_tree_leaves k).1)
        (fun k ↦ (hk_tree_leaves k).2)
        (fun k₁ k₂ hne ↦ (hB_disj (embJ₂.injective.ne hne)).mono
          (hQ_le (embJ₂ k₁)).1 (hQ_le (embJ₂ k₂)).1)
        (fun a k ↦ by
          rw [hPQ_inter_eq a (hk_mem_J k)]
          exact ncard_singleton _)
        (fun a k v hv ↦ by
          rw [hPQ_inter_eq a (hk_mem_J k), mem_singleton_iff] at hv
          subst hv
          have hw := hv_mem_W a (hk_mem_J k)
          dsimp [W] at hw
          rw [ite_eq_right (hk_not_path k)] at hw
          exact hw)
        (fun a k₁ k₂ hlt u hu v hv ↦
          hP_ord (embI a) (embJ₂.strictMono hlt) u
            ⟨hu.1, (hQ_le _).1 hu.2⟩ v ⟨hv.1, (hQ_le _).1 hv.2⟩)
      omega

/-- **Graph Minors I, (2.4)** (page 44):
"If $P_1, \dots, P_m$ are disjoint paths of $G \in \mathcal{F}_\theta$, and $B_1, \dots, B_n$ are
disjoint connected subgraphs of $G$, and each $B_j$ meets at least $\frac{1}{2}\theta^2$ of
$P_1, \dots, P_m$, and for $1 \le i \le m$ and for $1 \le j < j' \le n$, all vertices of $B_j$ on
$P_i$ occur before all vertices of $B_{j'}$, then
$n < \theta^{2\theta - 2} \binom{m}{\frac{1}{2}\theta^2}$."
(When `0 < n`, `θ ^ 2 / 2 ≤ m` follows from `hB_meet`; we include `hm : θ ^ 2 / 2 ≤ m` so the bound
also holds for `n = 0`, where otherwise `m.choose (θ ^ 2 / 2)` would vanish for `m < θ ^ 2 / 2`.)
The corrected general-graph form is `GM01.Full.theorem_2_4_proof`. -/
theorem theorem_2_4_simple {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) (hm : θ ^ 2 / 2 ≤ m)
    {G : (⊤ : SimpleGraph α).Subgraph} (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (P : Fin m → Path α) (B : Fin n → (⊤ : SimpleGraph α).Subgraph)
    (hP_in : ∀ i, (P i).IsIn G)
    (hP_disj : Pairwise fun i i' ↦ Disjoint (P i).verts (P i').verts)
    (hB_le : ∀ j, B j ≤ G)
    (hB_conn : ∀ j, (B j).Connected)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (hB_meet : ∀ j, θ ^ 2 / 2 ≤ {i : Fin m | ((P i).verts ∩ (B j).verts).Nonempty}.ncard)
    (hP_ord : ∀ i, (P i).MeetsInOrder B) :
    n < θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2) := by
  classical
  by_contra! hn_ge
  let M_full (j : Fin n) : Finset (Fin m) :=
    Finset.univ.filter (fun i ↦ ((P i).verts ∩ (B j).verts).Nonempty)
  have hM_card : ∀ j, θ ^ 2 / 2 ≤ (M_full j).card := by
    intro j
    have hset : ({i : Fin m | ((P i).verts ∩ (B j).verts).Nonempty} : Set (Fin m)) = M_full j := by
      ext i
      simp [M_full]
    have h := hB_meet j
    rwa [hset, ncard_coe_finset] at h
  -- "For `1 ≤ j ≤ n`, choose `Iⱼ ⊆ {1, …, m}` with `|Iⱼ| = ½ θ²` such that `Pᵢ` meets `Bⱼ` for
  -- each `i ∈ Iⱼ`."
  have h_ex_I : ∀ j, ∃ I ⊆ M_full j, I.card = θ ^ 2 / 2 :=
    fun j ↦ Finset.exists_subset_card_eq (hM_card j)
  choose I hI_sub hI_card using h_ex_I
  let SubI := Finset.powersetCard (θ ^ 2 / 2) (Finset.univ : Finset (Fin m))
  have hcard_SubI : Fintype.card SubI = m.choose (θ ^ 2 / 2) := by
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hI_mem_SubI : ∀ j, I j ∈ SubI :=
    fun j ↦ Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hI_card j⟩
  have hSubI_nonempty : Nonempty SubI := by
    obtain ⟨S, _, hS_card⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin m)))
        (by simpa using hm)
    exact ⟨⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS_card⟩⟩⟩
  let fI : Fin n → SubI := fun j ↦ ⟨I j, hI_mem_SubI j⟩
  have h_pigeon : Fintype.card SubI * θ ^ (2 * θ - 2) ≤ Fintype.card (Fin n) := by
    rw [hcard_SubI, Fintype.card_fin, mul_comm]
    exact hn_ge
  obtain ⟨I₀, hI₀_card⟩ := Fintype.exists_le_card_fiber_of_mul_le_card fI h_pigeon
  have hI₀_len : I₀.1.card = θ ^ 2 / 2 := (Finset.mem_powersetCard.1 I₀.2).2
  let J : Finset (Fin n) := Finset.univ.filter (fun j ↦ fI j = I₀)
  have hJ_card : θ ^ (2 * θ - 2) ≤ J.card := hI₀_card
  let embI := I₀.1.orderEmbOfFin hI₀_len
  let embJ := J.orderEmbOfFin rfl
  let P_sub (a : Fin (θ ^ 2 / 2)) : Path α := P (embI a)
  let B_sub (k : Fin J.card) : (⊤ : SimpleGraph α).Subgraph := B (embJ k)
  have h2_3 := theorem_2_3_simple hθ heven hG_fin hG P_sub B_sub
    (fun a ↦ hP_in (embI a))
    (fun _ _ hne ↦ hP_disj (embI.injective.ne hne))
    (fun k ↦ hB_le (embJ k))
    (fun k ↦ hB_conn (embJ k))
    (fun _ _ hne ↦ hB_disj (embJ.injective.ne hne))
    (fun a k ↦ by
      have hk : embJ k ∈ J := J.orderEmbOfFin_mem rfl k
      have hkI : I (embJ k) = I₀.1 := congrArg Subtype.val (Finset.mem_filter.1 hk).2
      have ha_mem : embI a ∈ I (embJ k) := hkI ▸ I₀.1.orderEmbOfFin_mem hI₀_len a
      exact (Finset.mem_filter.1 (hI_sub (embJ k) ha_mem)).2)
    (fun a k₁ k₂ hlt u hu v hv ↦ hP_ord (embI a) (embJ.strictMono hlt) u hu v hv)
  rcases h2_3 with hlt1 | hlt2 <;> omega

end GraphMinor.GM01



