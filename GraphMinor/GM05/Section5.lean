module

public import GraphMinor.GM05.Section5Aux
import Mathlib.Tactic.Ring

/-!
# Graph Minors V, Section 5: Webs and Meshes

This file formalizes Section 5 (pages 100–102) of Robertson and Seymour,
*Graph Minors. V. Excluding a planar graph*, J. Combin. Theory Ser. B 41 (1986) 92–114:

- `theorem_5_1`, (5.1): In a connected graph `G` with `v ∈ V_1 ∪ ⋯ ∪ V_{p^q}` where
  `V_1, …, V_{p^q} ⊆ V(G)` are disjoint and nonempty (`p ≥ 2`), either (i) there is a connected
  subgraph `C ≤ G` with `v ∈ V(C)` and `p` leaves `v_1, …, v_p ≠ v` of `C` with
  `V_{j_i} ∩ V(C) = {v_i}` for distinct `j_1, …, j_p`, or (ii) there is a path of `G` starting at
  `v` meeting exactly `q + 1` of `V_1, …, V_{p^q}`.
- `theorem_5_2`, (5.2): Given an `(m, n)`-mesh in `G ∈ 𝓕_θ` with `n = (θ²/2)^{q-1}` and
  `m = p n.choose q + (θ²/2) n.choose (θ²/2)`, there is a `(p, q)`-submesh in which the first
  family consists of paths.
- `theorem_5_3`, (5.3): If `G ∈ 𝓕_θ` then `G` has no `(θ₅, θ₆)`-mesh.
-/

@[expose] public section

namespace GraphMinor.GM05

open SimpleGraph Graph Set Relation GM01

universe u
variable {V : Type u}

/-! ## Helper Lemmas for (5.1) -/

/-- Along any walk in `G` from `z ∈ (componentSubgraph (G.deleteVerts L.verts) c).verts` to a vertex
of `L.verts`, there is an edge of `G` between `L.verts` and
`(componentSubgraph (G.deleteVerts L.verts) c).verts`. -/
private lemma exists_adj_componentSubgraph_deleteVerts
    {G L : (⊤ : SimpleGraph V).Subgraph}
    (c : (G.deleteVerts L.verts).coe.ConnectedComponent)
    {z y : V} (w : (⊤ : SimpleGraph V).Walk z y) (hwG : w.toSubgraph ≤ G)
    (hz : z ∈ (componentSubgraph (G.deleteVerts L.verts) c).verts) (hy : y ∈ L.verts) :
    ∃ w₀ ∈ L.verts, ∃ u₀ ∈ (componentSubgraph (G.deleteVerts L.verts) c).verts, G.Adj w₀ u₀ := by
  induction w with
  | @nil z =>
    obtain ⟨⟨z', hz'⟩, _, rfl⟩ := hz
    exact absurd hy hz'.2
  | @cons a b y hadj rest ih =>
    rw [Walk.toSubgraph, sup_le_iff] at hwG
    have hadjG : G.Adj a b := hwG.1.2 (by simp)
    by_cases hbL : b ∈ L.verts
    · exact ⟨b, hbL, a, hz, hadjG.symm⟩
    · have hbH : b ∈ (G.deleteVerts L.verts).verts := ⟨hadjG.snd_mem, hbL⟩
      obtain ⟨⟨a', ha'H⟩, ha'c, rfl⟩ := hz
      have hadj_coe : (G.deleteVerts L.verts).coe.Adj ⟨a', ha'H⟩ ⟨b, hbH⟩ :=
        ⟨ha'H, hbH, hadjG⟩
      have hbc : (G.deleteVerts L.verts).coe.connectedComponentMk ⟨b, hbH⟩ = c := by
        rw [← ha'c]
        exact ConnectedComponent.eq.2 ⟨.cons hadj_coe.symm .nil⟩
      have hb_comp : b ∈ (componentSubgraph (G.deleteVerts L.verts) c).verts :=
        ⟨⟨b, hbH⟩, hbc, rfl⟩
      exact ih hwG.2 hb_comp hy

/-- Key arithmetic inequality for Case 1 of (5.1): for `2 ≤ p` and any `q : ℕ`,
`(p - 1) * (p ^ q - 1) < p ^ (q + 1) - 1`. -/
private lemma mul_pred_pow_lt_pow_succ_pred {p q : ℕ} (hp : 2 ≤ p) :
    (p - 1) * (p ^ q - 1) < p ^ (q + 1) - 1 := by
  have hp_pos : 1 ≤ p := by omega
  have hpow_pos : 1 ≤ p ^ q := Nat.one_le_pow q p hp_pos
  have hid : p ^ (q + 1) = ((p - 1) + 1) * ((p ^ q - 1) + 1) := by
    rw [Nat.sub_add_cancel hp_pos, Nat.sub_add_cancel hpow_pos, pow_succ']
  have hexp : ((p - 1) + 1) * ((p ^ q - 1) + 1) =
      (p - 1) * (p ^ q - 1) + (p - 1) + (p ^ q - 1) + 1 := by ring
  omega

/-- Prepending a walk `w₁ : Walk v w₀` (which is a path) and an edge `hadj : Adj w₀ u₀` to a walk
`w₂ : Walk u₀ z` (which is a path), where `w₁` and `w₂` have disjoint supports and `w₀ ∉ w₂.support`,
produces a path. -/
private lemma isPath_append_cons_of_disjoint {v w₀ u₀ z : V}
    (w₁ : (⊤ : SimpleGraph V).Walk v w₀) (hw₁ : w₁.IsPath)
    (w₂ : (⊤ : SimpleGraph V).Walk u₀ z) (hw₂ : w₂.IsPath) :
    ∀ (hadj : (⊤ : SimpleGraph V).Adj w₀ u₀),
      (∀ x, x ∈ w₁.support → x ∈ w₂.support → False) →
      (w₁.append (.cons hadj w₂)).IsPath := by
  induction w₁ with
  | @nil w₀ =>
    intro hadj hdisj
    exact (Walk.cons_isPath_iff hadj w₂).2 ⟨hw₂, hdisj w₀ (by simp)⟩
  | @cons a b w₀ hadj₁ rest ih =>
    intro hadj hdisj
    rw [Walk.cons_isPath_iff] at hw₁
    rw [Walk.cons_append, Walk.cons_isPath_iff]
    refine ⟨ih hw₁.1 hadj (fun x hx₁ hx₂ ↦ hdisj x (List.mem_cons_of_mem a hx₁) hx₂), fun hm ↦ ?_⟩
    rw [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hm
    rcases hm with hm_rest | rfl | hm₂
    · exact hw₁.2 hm_rest
    · exact hw₁.2 rest.end_mem_support
    · exact hdisj a (by simp) hm₂

/-! ## Theorem (5.1) -/

/-- Graph Minors V, (5.1) (page 100):
"Let $v$ be a vertex of a connected graph $G$, and let $p, q \ge 0$ be integers. Let
$V_1, ..., V_{p^q} \subseteq V(G)$ be disjoint and non-empty, with
$v \in V_1 \cup \dots \cup V_{p^q}$. Then at least one of the following holds:
(i) there is a connected subgraph $C$ of $G$ with $v \in V(C)$, and there are $p$ vertices
$v_1, ..., v_p \ne v$ of $C$, each with valency 1 in $C$, and there are distinct
$j_1, ..., j_p \in \{1, ..., p^q\}$, such that
$$V_{j_i} \cap V(C) = \{v_i\} \qquad (1 \le i \le p);$$
(ii) there is a path of $G$ with initial vertex $v$, meeting exactly $q+1$ of
$V_1, ..., V_{p^q}$."

Note on `2 ≤ p`: When `p = 1` and `q ≥ 1`, `p^q = 1` so there is only one set `V₁`; since
`v ∈ V₁ ∩ V(C)`, `V₁ ∩ V(C) = {v₁}` forces `v₁ = v` (which excludes (i)), while no path can meet
`q + 1 ≥ 2` sets among `{V₁}` (which excludes (ii)). The proof on page 101 divides by `p^{q-1} - 1`
and uses `(p - 1)(p^{q-1} - 1) < p^q - 1`, which holds for `p ≥ 2`. The only application in the
paper is in (5.2) with `p = θ²/2 ≥ 18`. -/
theorem theorem_5_1_simple {G : (⊤ : SimpleGraph V).Subgraph} (hG_fin : G.verts.Finite)
    (hG_conn : G.Connected) {v : V} {p q : ℕ} (hp : 2 ≤ p)
    (Vset : Fin (p ^ q) → Set V)
    (hV_sub : ∀ j, Vset j ⊆ G.verts)
    (hV_disj : Pairwise fun j₁ j₂ ↦ Disjoint (Vset j₁) (Vset j₂))
    (hV_ne : ∀ j, (Vset j).Nonempty)
    (hv_mem : ∃ j₀, v ∈ Vset j₀) :
    (∃ (C : (⊤ : SimpleGraph V).Subgraph) (emb : Fin p ↪ Fin (p ^ q)) (v_leaf : Fin p → V),
      C ≤ G ∧ C.Connected ∧ v ∈ C.verts ∧
      ∀ i : Fin p, v_leaf i ≠ v ∧ IsLeafOf C (v_leaf i) ∧
        Vset (emb i) ∩ C.verts = {v_leaf i}) ∨
    (∃ P : GM01.Path V, P.toSubgraph ≤ G ∧ P.first = v ∧
      (metIndices Vset P.verts).card = q + 1) := by
  classical
  induction q generalizing G v with
  | zero =>
    obtain ⟨j₀, hv_j₀⟩ := hv_mem
    have hvG : v ∈ G.verts := hV_sub j₀ hv_j₀
    refine Or.inr ⟨GM01.Path.singleton v, ?_, rfl, ?_⟩
    · change (Walk.nil : (⊤ : SimpleGraph V).Walk v v).toSubgraph ≤ G
      simp [hvG]
    · rw [GM01.Path.singleton_verts]
      have heq : metIndices Vset {v} = {j₀} := by
        ext j
        simp only [metIndices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        refine ⟨fun ⟨w, hwV, hwv⟩ ↦ ?_, fun h ↦ ⟨v, h ▸ hv_j₀, Set.mem_singleton v⟩⟩
        rw [Set.mem_singleton_iff] at hwv
        subst hwv
        by_contra hne
        exact Set.disjoint_left.1 (hV_disj hne) hwV hv_j₀
      rw [heq, Finset.card_singleton]
  | succ q ih =>
    let M := p ^ (q + 1)
    obtain ⟨j₀, hv_j₀⟩ := hv_mem
    have hvG : v ∈ G.verts := hV_sub j₀ hv_j₀
    let U : Set V := ⋃ j ∈ ({j₀}ᶜ : Set (Fin M)), Vset j
    have hv_not_U : v ∉ U := by
      simp only [U, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff, not_exists]
      intro j hj hvw
      exact Set.disjoint_left.1 (hV_disj hj) hvw hv_j₀
    let H₀ := G.deleteVerts U
    have hvH₀ : v ∈ H₀.verts := ⟨hvG, hv_not_U⟩
    let c₀ := H₀.coe.connectedComponentMk ⟨v, hvH₀⟩
    let L := componentSubgraph H₀ c₀
    have hL_le_H₀ : L ≤ H₀ := componentSubgraph_le H₀ c₀
    have hL_le : L ≤ G := hL_le_H₀.trans Subgraph.deleteVerts_le
    have hL_conn : L.Connected := connected_componentSubgraph H₀ c₀
    have hvL : v ∈ L.verts := ⟨⟨v, hvH₀⟩, rfl, rfl⟩
    have hL_disj : ∀ j : Fin M, j ≠ j₀ → Disjoint L.verts (Vset j) := by
      intro j hj
      rw [Set.disjoint_left]
      intro x hxL hxV
      have hxH₀ : x ∈ H₀.verts := hL_le_H₀.1 hxL
      apply hxH₀.2
      simp only [U, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ⟨j, hj, hxV⟩
    have hL_max : ∀ {w₀ u₀ : V}, w₀ ∈ L.verts → u₀ ∉ L.verts → G.Adj w₀ u₀ →
        ∃ i : Fin M, i ≠ j₀ ∧ u₀ ∈ Vset i := by
      intro w₀ u₀ hw₀ hu₀ hadj
      by_contra! hnot
      have hu₀_not_U : u₀ ∉ U := by
        simp only [U, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff, not_exists]
        exact hnot
      have hu₀H₀ : u₀ ∈ H₀.verts := ⟨hadj.snd_mem, hu₀_not_U⟩
      obtain ⟨⟨w', hw'H₀⟩, hw'c₀, rfl⟩ := hw₀
      have hadj_coe : H₀.coe.Adj ⟨w', hw'H₀⟩ ⟨u₀, hu₀H₀⟩ :=
        ⟨hw'H₀, hu₀H₀, hadj⟩
      have hu₀c₀ : H₀.coe.connectedComponentMk ⟨u₀, hu₀H₀⟩ = c₀ := by
        rw [← hw'c₀]
        exact ConnectedComponent.eq.2 ⟨.cons hadj_coe.symm .nil⟩
      exact hu₀ ⟨⟨u₀, hu₀H₀⟩, hu₀c₀, rfl⟩
    let H := G.deleteVerts L.verts
    have hH_fin : H.verts.Finite := hG_fin.subset Subgraph.deleteVerts_le.1
    have : Finite H.verts := hH_fin
    let _ : Fintype H.coe.ConnectedComponent := Fintype.ofFinite H.coe.ConnectedComponent
    let B : H.coe.ConnectedComponent → (⊤ : SimpleGraph V).Subgraph := componentSubgraph H
    have hB_le_H : ∀ c, B c ≤ H := componentSubgraph_le H
    have hB_le : ∀ c, B c ≤ G := fun c ↦ (hB_le_H c).trans Subgraph.deleteVerts_le
    have hB_conn : ∀ c, (B c).Connected := connected_componentSubgraph H
    have hB_disj_L : ∀ c, Disjoint (B c).verts L.verts := by
      intro c
      rw [Set.disjoint_left]
      intro x hxB hxL
      exact ((hB_le_H c).1 hxB).2 hxL
    have hB_edge : ∀ c, ∃ w₀ ∈ L.verts, ∃ u₀ ∈ (B c).verts, G.Adj w₀ u₀ := by
      intro c
      obtain ⟨z, hz⟩ := (hB_conn c).nonempty
      obtain ⟨p_walk, hp_walk⟩ :=
        ((Subgraph.connected_iff_forall_exists_walk_subgraph G).1 hG_conn).2
          ((hB_le c).1 hz) hvG
      exact exists_adj_componentSubgraph_deleteVerts c p_walk hp_walk hz hvL
    let J : H.coe.ConnectedComponent → Finset (Fin M) := fun c ↦
      Finset.univ.filter fun j ↦ j ≠ j₀ ∧ (Vset j ∩ (B c).verts).Nonempty
    by_cases hcase2 : ∃ c : H.coe.ConnectedComponent, p ^ q ≤ (J c).card
    · -- Case 2: `|J_k| ≥ p^q` for some component `B_k` of `G \ V(L)`.
      obtain ⟨c, hc_card⟩ := hcase2
      obtain ⟨w₀, hw₀L, u₀, hu₀B, hadj₀⟩ := hB_edge c
      have hu₀_not_L : u₀ ∉ L.verts := Set.disjoint_left.1 (hB_disj_L c) hu₀B
      obtain ⟨i₀, hi₀_ne, hu₀V⟩ := hL_max hw₀L hu₀_not_L hadj₀
      have hi₀_J : i₀ ∈ J c := by
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hi₀_ne, u₀, hu₀V, hu₀B⟩
      have hpow_pos : 1 ≤ p ^ q := Nat.one_le_pow q p (by omega)
      have herase_card : p ^ q - 1 ≤ ((J c).erase i₀).card := by
        rw [Finset.card_erase_of_mem hi₀_J]
        omega
      obtain ⟨J_sub, hJ_sub, hJ_sub_card⟩ := Finset.exists_subset_card_eq herase_card
      let J' : Finset (Fin M) := insert i₀ J_sub
      have hi₀_not_sub : i₀ ∉ J_sub := fun hm ↦ (Finset.mem_erase.1 (hJ_sub hm)).1 rfl
      have hJ'_sub : J' ⊆ J c :=
        Finset.insert_subset hi₀_J (hJ_sub.trans (Finset.erase_subset i₀ (J c)))
      have hJ'_card : J'.card = p ^ q := by
        rw [Finset.card_insert_of_notMem hi₀_not_sub, hJ_sub_card]
        omega
      let eJ : Fin (p ^ q) ≃ J' := (Finset.equivFinOfCardEq hJ'_card).symm
      let embJ : Fin (p ^ q) ↪ Fin M := eJ.toEmbedding.trans (Function.Embedding.subtype _)
      let Vset' : Fin (p ^ q) → Set V := fun r ↦ Vset (embJ r) ∩ (B c).verts
      have hBc_fin : (B c).verts.Finite := hG_fin.subset (hB_le c).1
      have hV'_sub : ∀ r, Vset' r ⊆ (B c).verts := fun _ ↦ Set.inter_subset_right
      have hV'_disj : Pairwise fun r₁ r₂ ↦ Disjoint (Vset' r₁) (Vset' r₂) := by
        intro r₁ r₂ hne
        exact (hV_disj (embJ.injective.ne hne)).mono Set.inter_subset_left Set.inter_subset_left
      have hV'_ne : ∀ r, (Vset' r).Nonempty := by
        intro r
        have hmem : embJ r ∈ J c := hJ'_sub (eJ r).2
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact hmem.2
      have hu₀_mem' : ∃ r₀, u₀ ∈ Vset' r₀ := by
        refine ⟨eJ.symm ⟨i₀, Finset.mem_insert_self i₀ J_sub⟩, ?_⟩
        simp [Vset', embJ, hu₀V, hu₀B]
      rcases ih hBc_fin (hB_conn c) Vset' hV'_sub hV'_disj hV'_ne hu₀_mem' with
        ⟨C_B, emb_B, v_leaf, hCB_le, hCB_conn, hu₀CB, hCB_leaf⟩ | ⟨P_B, hPB_le, hPB_first, hPB_card⟩
      · -- Subcase 2(i): extend `C_B` to `C = C_B ⊔ (L ⊔ edge(w₀, u₀))`.
        let R := L ⊔ (⊤ : SimpleGraph V).subgraphOfAdj hadj₀.adj_sub
        have hR_le : R ≤ G := sup_le hL_le (subgraphOfAdj_le_of_adj G hadj₀)
        have hR_verts : R.verts = L.verts ∪ {w₀, u₀} := by
          ext x
          simp [R]
        let C := C_B ⊔ R
        have hC_le : C ≤ G := sup_le (hCB_le.trans (hB_le c)) hR_le
        have hC_conn : C.Connected := by
          have hL_edge_conn : R.Connected := by
            refine connected_sup_of_inter_nonempty hL_conn ?_ ⟨w₀, hw₀L, by simp⟩
            rw [← Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
            exact (Walk.cons hadj₀.adj_sub .nil).toSubgraph_connected
          exact connected_sup_of_inter_nonempty hCB_conn hL_edge_conn ⟨u₀, hu₀CB, Or.inr (by simp)⟩
        have hvC : v ∈ C.verts := Or.inr (Or.inl hvL)
        refine Or.inl ⟨C, emb_B.trans embJ, v_leaf, hC_le, hC_conn, hvC, fun i ↦ ?_⟩
        obtain ⟨hne_u₀, hleaf_CB, hinter_CB⟩ := hCB_leaf i
        have hvi_CB : v_leaf i ∈ C_B.verts := hleaf_CB.1
        have hvi_Bc : v_leaf i ∈ (B c).verts := hCB_le.1 hvi_CB
        have hvi_not_L : v_leaf i ∉ L.verts := Set.disjoint_left.1 (hB_disj_L c) hvi_Bc
        have hvi_ne_v : v_leaf i ≠ v := fun heq ↦ hvi_not_L (heq ▸ hvL)
        have hvi_not_R : v_leaf i ∉ R.verts := by
          rw [hR_verts]
          rintro (hL | rfl | rfl)
          · exact hvi_not_L hL
          · exact hvi_not_L hw₀L
          · exact hne_u₀ rfl
        have hleaf_C : IsLeafOf C (v_leaf i) := isLeafOf_sup_of_notMem_right hleaf_CB hvi_not_R
        have hj_mem_J : embJ (emb_B i) ∈ J c := hJ'_sub (eJ (emb_B i)).2
        have hj_ne_j₀ : embJ (emb_B i) ≠ j₀ := by
          simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hj_mem_J
          exact hj_mem_J.1
        have hinter_C : Vset (embJ (emb_B i)) ∩ C.verts = {v_leaf i} := by
          have hC_verts : C.verts = C_B.verts ∪ L.verts := by
            ext x
            simp only [C, R, Subgraph.verts_sup, subgraphOfAdj_verts, Set.mem_union,
              Set.mem_insert_iff, Set.mem_singleton_iff]
            refine ⟨?_, ?_⟩
            · rintro (hxCB | hxL | rfl | rfl)
              · exact Or.inl hxCB
              · exact Or.inr hxL
              · exact Or.inr hw₀L
              · exact Or.inl hu₀CB
            · rintro (hxCB | hxL)
              · exact Or.inl hxCB
              · exact Or.inr (Or.inl hxL)
          have hinter_CB' : Vset (embJ (emb_B i)) ∩ C_B.verts = {v_leaf i} := by
            have hsub : C_B.verts ⊆ (B c).verts := hCB_le.1
            have heq_inter :
                Vset (embJ (emb_B i)) ∩ (B c).verts ∩ C_B.verts =
                  Vset (embJ (emb_B i)) ∩ C_B.verts := by
              rw [Set.inter_assoc, Set.inter_eq_self_of_subset_right hsub]
            exact heq_inter ▸ hinter_CB
          have hinter_L : Vset (embJ (emb_B i)) ∩ L.verts = ∅ :=
            Set.disjoint_iff_inter_eq_empty.1 (hL_disj _ hj_ne_j₀).symm
          rw [hC_verts, Set.inter_union_distrib_left, hinter_CB', hinter_L, Set.union_empty]
        exact ⟨hvi_ne_v, hleaf_C, hinter_C⟩
      · -- Subcase 2(ii): prepend a path in `L` from `v` to `w₀` and the edge `(w₀, u₀)` to `P_B`.
        rcases P_B with ⟨u₀', last_B, walk_B, isPath_B⟩
        change u₀' = u₀ at hPB_first
        subst hPB_first
        change (metIndices Vset' walk_B.toSubgraph.verts).card = q + 1 at hPB_card
        obtain ⟨w_L, hw_L⟩ :=
          ((Subgraph.connected_iff_forall_exists_walk_subgraph L).1 hL_conn).2 hvL hw₀L
        let P_L : GM01.Path V := GM01.Path.ofWalk w_L
        have hp_L_le_L : P_L.walk.toSubgraph ≤ L :=
          (GM01.Path.ofWalk_toSubgraph_le w_L).trans hw_L
        have hdisj_LB : ∀ x, x ∈ P_L.walk.support → x ∈ walk_B.support → False := by
          intro x hx₁ hx₂
          have hxL : x ∈ L.verts := hp_L_le_L.1 (P_L.walk.mem_verts_toSubgraph.2 hx₁)
          have hxB : x ∈ (B c).verts := hPB_le.1 (walk_B.mem_verts_toSubgraph.2 hx₂)
          exact Set.disjoint_left.1 (hB_disj_L c) hxB hxL
        have hw_comb_path : (P_L.walk.append (.cons hadj₀.adj_sub walk_B)).IsPath :=
          isPath_append_cons_of_disjoint P_L.walk P_L.isPath walk_B isPath_B hadj₀.adj_sub hdisj_LB
        let P_full : GM01.Path V :=
          ⟨v, last_B, P_L.walk.append (.cons hadj₀.adj_sub walk_B), hw_comb_path⟩
        have hPfull_le : P_full.toSubgraph ≤ G := by
          have hcons_le : (Walk.cons hadj₀.adj_sub walk_B).toSubgraph ≤ G := by
            rw [Walk.toSubgraph]
            exact sup_le (subgraphOfAdj_le_of_adj G hadj₀) (hPB_le.trans (hB_le c))
          change (P_L.walk.append (.cons hadj₀.adj_sub walk_B)).toSubgraph ≤ G
          rw [Walk.toSubgraph_append]
          exact sup_le (hp_L_le_L.trans hL_le) hcons_le
        have hPB_sub_Pfull : {x | x ∈ walk_B.support} ⊆ P_full.verts := by
          intro x hx
          rw [GM01.Path.mem_verts_iff]
          change x ∈ (P_L.walk.append (.cons hadj₀.adj_sub walk_B)).support
          rw [Walk.mem_support_append_iff]
          right
          exact List.mem_cons_of_mem w₀ hx
        have hv_mem_Pfull : v ∈ P_full.verts := P_full.first_mem_verts
        have hcard_ge : q + 2 ≤ (metIndices Vset P_full.verts).card := by
          let S_mapped : Finset (Fin M) := (metIndices Vset' walk_B.toSubgraph.verts).map embJ
          have hj₀_not_S : j₀ ∉ S_mapped := by
            rw [Finset.mem_map]
            rintro ⟨r, _, hr_eq⟩
            have hr_J : embJ r ∈ J c := hJ'_sub (eJ r).2
            simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hr_J
            exact hr_J.1 hr_eq
          have hins_sub : insert j₀ S_mapped ⊆ metIndices Vset P_full.verts := by
            intro j hj
            rw [Finset.mem_insert] at hj
            simp only [metIndices, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hj with rfl | hjS
            · exact ⟨v, hv_j₀, hv_mem_Pfull⟩
            · rw [Finset.mem_map] at hjS
              obtain ⟨r, hr, rfl⟩ := hjS
              simp only [metIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hr
              obtain ⟨z, ⟨hzV, _⟩, hzPB⟩ := hr
              exact ⟨z, hzV, hPB_sub_Pfull (walk_B.mem_verts_toSubgraph.1 hzPB)⟩
          have hins_card : (insert j₀ S_mapped).card = q + 2 := by
            rw [Finset.card_insert_of_notMem hj₀_not_S, Finset.card_map, hPB_card]
          rw [← hins_card]
          exact Finset.card_le_card hins_sub
        obtain ⟨P', hP'_le, hP'_first, hP'_card⟩ :=
          exists_prefix_path_meeting_card_eq hV_disj hv_j₀ P_full rfl (by omega) hcard_ge
        exact Or.inr ⟨P', hP'_le.trans hPfull_le, hP'_first, hP'_card⟩
    · -- Case 1: `|J_k| < p^q` for all `k`.
      push Not at hcase2
      have hcover_univ :
          (Finset.univ : Finset H.coe.ConnectedComponent).biUnion J = Finset.univ.erase j₀ := by
        ext j
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, J, Finset.mem_filter,
          Finset.mem_erase]
        refine ⟨fun ⟨_, hj_ne, _⟩ ↦ ⟨hj_ne, trivial⟩, fun ⟨hj_ne, _⟩ ↦ ?_⟩
        obtain ⟨z, hzV⟩ := hV_ne j
        have hz_not_L : z ∉ L.verts :=
          fun hzL ↦ Set.disjoint_left.1 (hL_disj j hj_ne) hzL hzV
        have hzH : z ∈ H.verts := ⟨hV_sub j hzV, hz_not_L⟩
        let c := H.coe.connectedComponentMk ⟨z, hzH⟩
        exact ⟨c, hj_ne, z, hzV, ⟨z, hzH⟩, rfl, rfl⟩
      have hex_N : ∃ m : ℕ, ∃ N : Finset H.coe.ConnectedComponent,
          N.biUnion J = Finset.univ.erase j₀ ∧ N.card = m :=
        ⟨Finset.univ.card, Finset.univ, hcover_univ, rfl⟩
      obtain ⟨N, hN_cover, hN_card⟩ := Nat.find_spec hex_N
      have hp_le_N : p ≤ N.card := by
        by_contra! hlt
        have hpow_pos : 1 ≤ p ^ q := Nat.one_le_pow q p (by omega)
        have hbi_le : (N.biUnion J).card ≤ N.card * (p ^ q - 1) := by
          refine (Finset.card_biUnion_le).trans ?_
          have hsum : ∑ c ∈ N, (J c).card ≤ ∑ _c ∈ N, (p ^ q - 1) := by
            refine Finset.sum_le_sum fun c _ ↦ ?_
            have := hcase2 c
            omega
          simpa using hsum
        have hmul_le : N.card * (p ^ q - 1) ≤ (p - 1) * (p ^ q - 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have herase_eq : (Finset.univ.erase j₀).card = p ^ (q + 1) - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
        have hlt_pow := mul_pred_pow_lt_pow_succ_pred (q := q) hp
        rw [hN_cover, herase_eq] at hbi_le
        omega
      have hj_uniq : ∀ c ∈ N, ∃ j ∈ J c, ∀ c' ∈ N, c' ≠ c → j ∉ J c' := by
        intro c hcN
        by_contra! hall
        have hsub : N.biUnion J ⊆ (N.erase c).biUnion J := by
          intro j hj
          rw [Finset.mem_biUnion] at hj ⊢
          obtain ⟨c₁, hc₁N, hjc₁⟩ := hj
          by_cases hc₁ : c₁ = c
          · subst hc₁
            obtain ⟨c', hc'N, hc'ne, hjc'⟩ := hall j hjc₁
            exact ⟨c', Finset.mem_erase.2 ⟨hc'ne, hc'N⟩, hjc'⟩
          · exact ⟨c₁, Finset.mem_erase.2 ⟨hc₁, hc₁N⟩, hjc₁⟩
        have heq_cover : (N.erase c).biUnion J = Finset.univ.erase j₀ :=
          le_antisymm ((Finset.biUnion_subset_biUnion_of_subset_left J (Finset.erase_subset c N)).trans
            (le_of_eq hN_cover)) (hN_cover ▸ hsub)
        have hlt_card : (N.erase c).card < Nat.find hex_N := by
          rw [← hN_card]
          exact Finset.card_erase_lt_of_mem hcN
        exact Nat.find_min hex_N hlt_card ⟨N.erase c, heq_cover, rfl⟩
      obtain ⟨N₀, hN₀_sub, hN₀_card⟩ := Finset.exists_subset_card_eq hp_le_N
      let eN : Fin p ≃ N₀ := (Finset.equivFinOfCardEq hN₀_card).symm
      let c_of : Fin p → H.coe.ConnectedComponent := fun i ↦ (eN i).1
      have hc_mem_N : ∀ i, c_of i ∈ N := fun i ↦ hN₀_sub (eN i).2
      have hc_inj : Function.Injective c_of :=
        (Function.Embedding.subtype _).injective.comp eN.injective
      choose j_of hj_mem_Jc hj_not_other using fun i : Fin p ↦ hj_uniq (c_of i) (hc_mem_N i)
      have hj_inj : Function.Injective j_of := by
        intro i₁ i₂ heq
        by_contra hne
        exact hj_not_other i₁ (c_of i₂) (hc_mem_N i₂) (hc_inj.ne (Ne.symm hne)) (heq ▸ hj_mem_Jc i₂)
      let emb : Fin p ↪ Fin M := ⟨j_of, hj_inj⟩
      choose w_of hw_L u_of hu_B hadj_wu using fun i : Fin p ↦ hB_edge (c_of i)
      have hpath_ex : ∀ i : Fin p, ∃ (v_i : V) (w_P : (⊤ : SimpleGraph V).Walk (u_of i) v_i),
          w_P.IsPath ∧ w_P.toSubgraph ≤ B (c_of i) ∧
          v_i ∈ Vset (j_of i) ∩ (B (c_of i)).verts ∧
          w_P.toSubgraph.verts ∩ (Vset (j_of i) ∩ (B (c_of i)).verts) = {v_i} := by
        intro i
        have hj_in := hj_mem_Jc i
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hj_in
        obtain ⟨P, hP_le, hP_first, hP_last, hP_inter⟩ :=
          exists_first_hit_path (hB_conn (c_of i)) (hu_B i) Set.inter_subset_right hj_in.2
        rcases P with ⟨u', v_i, w_P, hw_P⟩
        change u' = u_of i at hP_first
        subst hP_first
        exact ⟨v_i, w_P, hw_P, hP_le, hP_last, hP_inter⟩
      choose v_leaf w_P hw_P_path hP_le hP_last hP_inter using hpath_ex
      have hw_not_P : ∀ i : Fin p, w_of i ∉ (w_P i).support := by
        intro i hm
        have hm' : w_of i ∈ (B (c_of i)).verts :=
          (hP_le i).1 ((w_P i).mem_verts_toSubgraph.2 hm)
        exact Set.disjoint_left.1 (hB_disj_L (c_of i)) hm' (hw_L i)
      let Q : Fin p → GM01.Path V := fun i ↦
        ⟨w_of i, v_leaf i,
          .cons (hadj_wu i).adj_sub (w_P i),
          (Walk.cons_isPath_iff _ _).2 ⟨hw_P_path i, hw_not_P i⟩⟩
      have hQ_verts : ∀ i, (Q i).toSubgraph.verts = insert (w_of i) (w_P i).toSubgraph.verts := by
        intro i
        ext x
        change x ∈ (Walk.cons (hadj_wu i).adj_sub (w_P i)).toSubgraph.verts ↔ _
        rw [Walk.mem_verts_toSubgraph, Walk.support_cons, List.mem_cons, Set.mem_insert_iff,
          Walk.mem_verts_toSubgraph]
      have hQ_le : ∀ i, (Q i).toSubgraph ≤ G := by
        intro i
        change (Walk.cons (hadj_wu i).adj_sub (w_P i)).toSubgraph ≤ G
        rw [Walk.toSubgraph]
        exact sup_le (subgraphOfAdj_le_of_adj G (hadj_wu i)) ((hP_le i).trans (hB_le (c_of i)))
      let C := L ⊔ ⨆ i : Fin p, (Q i).toSubgraph
      have hC_le : C ≤ G := sup_le hL_le (iSup_le hQ_le)
      have hC_conn : C.Connected := by
        rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
        refine ⟨⟨v, Or.inl hvL⟩, fun {x y} hx hy ↦ ?_⟩
        have hconn_v : ∀ z ∈ C.verts, ∃ q : (⊤ : SimpleGraph V).Walk v z, q.toSubgraph ≤ C := by
          intro z hz
          simp only [C, Subgraph.verts_sup, Subgraph.verts_iSup, Set.mem_union,
            Set.mem_iUnion] at hz
          rcases hz with hzL | ⟨i, hzQ⟩
          · obtain ⟨q, hq⟩ :=
              ((Subgraph.connected_iff_forall_exists_walk_subgraph L).1 hL_conn).2 hvL hzL
            exact ⟨q, hq.trans le_sup_left⟩
          · obtain ⟨q₁, hq₁⟩ :=
              ((Subgraph.connected_iff_forall_exists_walk_subgraph L).1 hL_conn).2 hvL (hw_L i)
            obtain ⟨q₂, hq₂⟩ :=
              ((Subgraph.connected_iff_forall_exists_walk_subgraph (Q i).toSubgraph).1
                (Q i).connected_toSubgraph).2 (Q i).first_mem_verts hzQ
            refine ⟨q₁.append q₂, ?_⟩
            rw [Walk.toSubgraph_append]
            exact sup_le (hq₁.trans le_sup_left)
              (hq₂.trans (le_sup_of_le_right (le_iSup (fun r ↦ (Q r).toSubgraph) i)))
        obtain ⟨qx, hqx⟩ := hconn_v x hx
        obtain ⟨qy, hqy⟩ := hconn_v y hy
        refine ⟨qx.reverse.append qy, ?_⟩
        rw [Walk.toSubgraph_append, Walk.toSubgraph_reverse]
        exact sup_le hqx hqy
      refine Or.inl ⟨C, emb, v_leaf, hC_le, hC_conn, Or.inl hvL, fun i ↦ ?_⟩
      have hvi_Bc : v_leaf i ∈ (B (c_of i)).verts := (hP_last i).2
      have hvi_not_L : v_leaf i ∉ L.verts := Set.disjoint_left.1 (hB_disj_L (c_of i)) hvi_Bc
      have hvi_ne_v : v_leaf i ≠ v := fun heq ↦ hvi_not_L (heq ▸ hvL)
      have hwi_ne_vi : w_of i ≠ v_leaf i := fun heq ↦ hvi_not_L (heq ▸ hw_L i)
      have hleaf_Qi : IsLeafOf (Q i).toSubgraph (v_leaf i) := by
        rw [← GM01.Path.reverse_toSubgraph (Q i)]
        exact Path.isLeafOf_first_of_ne (Q i).reverse hwi_ne_vi.symm
      let R_other := L ⊔ ⨆ r ∈ ({i}ᶜ : Set (Fin p)), (Q r).toSubgraph
      have hC_decomp : C = (Q i).toSubgraph ⊔ R_other := by
        ext x y
        · simp only [C, R_other, Subgraph.verts_sup, Subgraph.verts_iSup, Set.mem_union,
            Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
          refine ⟨?_, ?_⟩
          · rintro (hxL | ⟨r, hxQr⟩)
            · exact Or.inr (Or.inl hxL)
            · by_cases hri : r = i
              · exact Or.inl (hri ▸ hxQr)
              · exact Or.inr (Or.inr ⟨r, hri, hxQr⟩)
          · rintro (hxQi | hxL | ⟨r, _, hxQr⟩)
            · exact Or.inr ⟨i, hxQi⟩
            · exact Or.inl hxL
            · exact Or.inr ⟨r, hxQr⟩
        · simp only [C, R_other, Subgraph.sup_adj, Subgraph.iSup_adj, Set.mem_compl_iff,
            Set.mem_singleton_iff]
          refine ⟨?_, ?_⟩
          · rintro (hL | ⟨r, hQr⟩)
            · exact Or.inr (Or.inl hL)
            · by_cases hri : r = i
              · exact Or.inl (hri ▸ hQr)
              · exact Or.inr (Or.inr ⟨r, hri, hQr⟩)
          · rintro (hQi | hL | ⟨r, _, hQr⟩)
            · exact Or.inr ⟨i, hQi⟩
            · exact Or.inl hL
            · exact Or.inr ⟨r, hQr⟩
      have hB_disj_pair : ∀ r ≠ i, Disjoint (B (c_of i)).verts (B (c_of r)).verts := by
        intro r hne
        rcases (isComponentOf_componentSubgraph H (c_of i)).disjoint_or_eq
          (isComponentOf_componentSubgraph H (c_of r)) with hdisj | heq
        · exact hdisj
        · obtain ⟨z, hz⟩ := (hB_conn (c_of i)).nonempty
          have hverts_eq : (B (c_of i)).verts = (B (c_of r)).verts :=
            congrArg Subgraph.verts heq
          have hz_r : z ∈ (B (c_of r)).verts := hverts_eq ▸ hz
          obtain ⟨z₁, hz₁, rfl⟩ := hz
          obtain ⟨z₂, hz₂, hz_eq⟩ := hz_r
          have hsub_eq : z₁ = z₂ := Subtype.ext hz_eq.symm
          exact absurd (hc_inj (hz₁.symm.trans (hsub_eq ▸ hz₂))) (Ne.symm hne)
      have hvi_not_R : v_leaf i ∉ R_other.verts := by
        simp only [R_other, Subgraph.verts_sup, Subgraph.verts_iSup, Set.mem_union,
          Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro (hxL | ⟨r, hri, hxQr⟩)
        · exact hvi_not_L hxL
        · rw [hQ_verts r, Set.mem_insert_iff] at hxQr
          rcases hxQr with hwi | hxPr
          · exact hvi_not_L (hwi ▸ hw_L r)
          · exact Set.disjoint_left.1 (hB_disj_pair r hri) hvi_Bc ((hP_le r).1 hxPr)
      have hleaf_C : IsLeafOf C (v_leaf i) := by
        rw [hC_decomp]
        exact isLeafOf_sup_of_notMem_right hleaf_Qi hvi_not_R
      have hj_ne_j₀ : j_of i ≠ j₀ := by
        have hj_in := hj_mem_Jc i
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hj_in
        exact hj_in.1
      have hinter_R : Vset (j_of i) ∩ R_other.verts = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hxV, hxR⟩
        simp only [R_other, Subgraph.verts_sup, Subgraph.verts_iSup, Set.mem_union,
          Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff] at hxR
        rcases hxR with hxL | ⟨r, hri, hxQr⟩
        · exact Set.disjoint_left.1 (hL_disj (j_of i) hj_ne_j₀) hxL hxV
        · rw [hQ_verts r, Set.mem_insert_iff] at hxQr
          rcases hxQr with rfl | hxPr
          · exact Set.disjoint_left.1 (hL_disj (j_of i) hj_ne_j₀) (hw_L r) hxV
          · have hxBr : x ∈ (B (c_of r)).verts := (hP_le r).1 hxPr
            have hj_in_r : j_of i ∈ J (c_of r) := by
              simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hj_ne_j₀, x, hxV, hxBr⟩
            exact hj_not_other i (c_of r) (hc_mem_N r) (hc_inj.ne hri) hj_in_r
      have hinter_Qi : Vset (j_of i) ∩ (Q i).toSubgraph.verts = {v_leaf i} := by
        rw [hQ_verts i]
        have hwi_not_V : w_of i ∉ Vset (j_of i) :=
          Set.disjoint_left.1 (hL_disj (j_of i) hj_ne_j₀) (hw_L i)
        have hinter_Pi : Vset (j_of i) ∩ (w_P i).toSubgraph.verts = {v_leaf i} := by
          have hsub : (w_P i).toSubgraph.verts ⊆ (B (c_of i)).verts := (hP_le i).1
          have heq : (w_P i).toSubgraph.verts ∩ (Vset (j_of i) ∩ (B (c_of i)).verts) =
              Vset (j_of i) ∩ (w_P i).toSubgraph.verts := by
            rw [← Set.inter_assoc, Set.inter_comm (w_P i).toSubgraph.verts (Vset (j_of i)),
              Set.inter_assoc, Set.inter_eq_self_of_subset_left hsub]
          exact heq ▸ hP_inter i
        ext x
        simp only [Set.mem_inter_iff, Set.mem_insert_iff]
        rw [← hinter_Pi]
        simp only [Set.mem_inter_iff]
        refine ⟨fun ⟨hxV, hx⟩ ↦ ?_, fun ⟨hxV, hxP⟩ ↦ ⟨hxV, Or.inr hxP⟩⟩
        rcases hx with rfl | hxP
        · exact absurd hxV hwi_not_V
        · exact ⟨hxV, hxP⟩
      have hinter_C : Vset (j_of i) ∩ C.verts = {v_leaf i} := by
        change Vset (j_of i) ∩ (Q i).toSubgraph.verts = {v_leaf i} at hinter_Qi
        rw [hC_decomp, Subgraph.verts_sup, Set.inter_union_distrib_left,
          hinter_Qi, hinter_R, Set.union_empty]
      exact ⟨hvi_ne_v, hleaf_C, hinter_C⟩

/-! ## Theorem (5.2) -/

private lemma le_pow_pred_of_two_le {K q : ℕ} (hK : 2 ≤ K) (hq : 2 ≤ q) :
    q ≤ K ^ (q - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hq
  clear hq
  have hsub : 2 + d - 1 = d + 1 := by omega
  rw [hsub]
  clear hsub
  induction d with
  | zero => simpa using hK
  | succ d ih =>
    rw [pow_succ']
    have h1 : 2 + (d + 1) ≤ 2 * (2 + d) := by omega
    have h2 : 2 * (2 + d) ≤ K * K ^ (d + 1) := Nat.mul_le_mul hK ih
    omega

/-- Graph Minors V, (5.2) (page 101):
"Let $G \in \mathcal{F}_\theta$, and let $p, q \ge 2$ be integers. Let
$n = (\theta^2/2)^{q-1}$, $m = p \binom{n}{q} + \frac{1}{2}\theta^2 \binom{n}{\theta^2/2}$.
Suppose that $((A_1, ..., A_m), (B_1, ..., B_n))$ is an $(m, n)$-mesh in $G$. Then there exists
$I \subseteq \{1, ..., m\}$ and $J \subseteq \{1, ..., n\}$ with $|I| = p$, $|J| = q$, and for each
$i \in I$ a path $P_i$ of $A_i$, such that $((P_i : i \in I), (B_j : j \in J))$ is a
$(p, q)$-mesh." -/
theorem theorem_5_2_simple {G : (⊤ : SimpleGraph V).Subgraph} {θ p q : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    {A : Fin (p * ((θ ^ 2 / 2) ^ (q - 1)).choose q +
      (θ ^ 2 / 2) * ((θ ^ 2 / 2) ^ (q - 1)).choose (θ ^ 2 / 2)) → (⊤ : SimpleGraph V).Subgraph}
    {B : Fin ((θ ^ 2 / 2) ^ (q - 1)) → (⊤ : SimpleGraph V).Subgraph}
    (hmesh : IsMesh G A B) :
    ∃ (embI : Fin p ↪ Fin (p * ((θ ^ 2 / 2) ^ (q - 1)).choose q +
        (θ ^ 2 / 2) * ((θ ^ 2 / 2) ^ (q - 1)).choose (θ ^ 2 / 2)))
      (embJ : Fin q ↪ Fin ((θ ^ 2 / 2) ^ (q - 1)))
      (P : Fin p → GM01.Path V),
      (∀ r, (P r).toSubgraph ≤ A (embI r)) ∧
      IsMesh G (fun r ↦ (P r).toSubgraph) (fun s ↦ B (embJ s)) := by
  classical
  let K := θ ^ 2 / 2
  let n := K ^ (q - 1)
  let m := p * n.choose q + K * n.choose K
  have hK_ge : 18 ≤ K := eighteen_le_half_θ_sq hθ
  have hK_two : 2 ≤ K := by omega
  let V_ij : Fin m → Fin n → Set V := fun i j ↦ (A i).verts ∩ (B j).verts
  let IsStarred : Fin m → Prop := fun i ↦
    ∃ (S : Finset (Fin n)) (C : (⊤ : SimpleGraph V).Subgraph),
      S.card = K ∧ C ≤ A i ∧ C.Connected ∧
      ∀ j ∈ S, ∃ v_j, V_ij i j ∩ C.verts = {v_j} ∧ IsLeafOf C v_j
  let I_star : Finset (Fin m) := Finset.univ.filter IsStarred
  have hI_star_le : I_star.card ≤ K * n.choose K := by
    choose S_of C_of hS_card hC_le hC_conn hC_leaf using
      fun i : I_star ↦ (Finset.mem_filter.1 i.2).2
    let P_K : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard K
    have hP_K_card : P_K.card = n.choose K := by
      simp [P_K, Finset.card_powersetCard]
    have hfiber_lt : ∀ S ∈ P_K,
        (I_star.filter fun i ↦ (if h : i ∈ I_star then S_of ⟨i, h⟩ else ∅) = S).card < K := by
      intro S hS_mem
      by_contra! hge
      obtain ⟨F, hF_sub, hF_card⟩ := Finset.exists_subset_card_eq hge
      let eF : Fin K ≃ F := (Finset.equivFinOfCardEq hF_card).symm
      let embF_fun : Fin K → I_star :=
        fun r ↦ ⟨(eF r).1, (Finset.mem_filter.1 (hF_sub (eF r).2)).1⟩
      have hembF_inj : Function.Injective embF_fun := by
        intro r₁ r₂ heq
        have hval : (eF r₁).1 = (eF r₂).1 := congrArg (fun x : I_star ↦ x.1) heq
        exact eF.injective (Subtype.ext hval)
      let embF : Fin K ↪ I_star := ⟨embF_fun, hembF_inj⟩
      have hS_eq : ∀ r : Fin K, S_of (embF r) = S := by
        intro r
        have hmem := (Finset.mem_filter.1 (hF_sub (eF r).2)).2
        have hi : (eF r).1 ∈ I_star := (Finset.mem_filter.1 (hF_sub (eF r).2)).1
        rw [dite_eq_left hi] at hmem
        exact hmem
      have hS_card_K : S.card = K := (Finset.mem_powersetCard.1 hS_mem).2
      let eS : Fin K ≃ S := (Finset.equivFinOfCardEq hS_card_K).symm
      let A' : Fin K → (⊤ : SimpleGraph V).Subgraph := fun j ↦ B (eS j).1
      let B' : Fin K → (⊤ : SimpleGraph V).Subgraph := fun r ↦ C_of (embF r)
      exact theorem_4_1_leaves hθ heven hG_fin hG A' B'
        (fun j ↦ hmesh.le_right (eS j).1)
        (fun j ↦ hmesh.connected_right (eS j).1)
        (fun j₁ j₂ hne ↦ hmesh.disjoint_right ((Subtype.val_injective.comp eS.injective).ne hne))
        (fun r ↦ (hC_le (embF r)).trans (hmesh.le_left (embF r).1))
        (fun r ↦ hC_conn (embF r))
        (fun r₁ r₂ hne ↦ by
          have hne_val : (embF r₁).1 ≠ (embF r₂).1 :=
            fun heq ↦ hne (embF.injective (Subtype.ext heq))
          exact (hmesh.disjoint_left hne_val).mono (hC_le (embF r₁)).1 (hC_le (embF r₂)).1)
        (fun j r ↦ by
          have hjS : (eS j).1 ∈ S_of (embF r) := by
            rw [hS_eq r]
            exact (eS j).2
          obtain ⟨v_j, hv_inter, hv_leaf⟩ := hC_leaf (embF r) (eS j).1 hjS
          refine ⟨v_j, ?_, hv_leaf⟩
          have hsub : (B' r).verts ⊆ (A (embF r).1).verts := (hC_le (embF r)).1
          have heq : V_ij (embF r).1 (eS j).1 ∩ (B' r).verts = (A' j).verts ∩ (B' r).verts := by
            dsimp [V_ij, A', B']
            rw [Set.inter_comm ((A (embF r).1).verts), Set.inter_assoc,
              Set.inter_eq_self_of_subset_right hsub]
          exact heq ▸ hv_inter)
    have hbi : I_star ⊆ P_K.biUnion fun S ↦
        I_star.filter fun i ↦ (if h : i ∈ I_star then S_of ⟨i, h⟩ else ∅) = S := by
      intro i hi
      rw [Finset.mem_biUnion]
      refine ⟨S_of ⟨i, hi⟩, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, hS_card ⟨i, hi⟩⟩
      · simp [hi]
    have hle_sum : I_star.card ≤ ∑ _S ∈ P_K, (K - 1) := by
      refine (Finset.card_le_card hbi).trans (Finset.card_biUnion_le.trans ?_)
      refine Finset.sum_le_sum fun S hS ↦ ?_
      have := hfiber_lt S hS
      omega
    rw [Finset.sum_const, smul_eq_mul, hP_K_card] at hle_sum
    have hmul : n.choose K * (K - 1) ≤ K * n.choose K := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right _ (by omega)
    exact hle_sum.trans hmul
  have hcompl_card : p * n.choose q ≤ (Finset.univ \ I_star).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    dsimp [m]
    omega
  obtain ⟨I', hI'_sub, hI'_card⟩ := Finset.exists_subset_card_eq hcompl_card
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (by
    have := le_pow_pred_of_two_le hK_two hq
    omega)
  let j₀ : Fin n := ⟨0, hn_pos⟩
  have hpath_ex : ∀ i : I', ∃ (P : GM01.Path V) (S : Finset (Fin n)),
      P.toSubgraph ≤ A i.1 ∧ S.card = q ∧ ∀ j ∈ S, (P.verts ∩ (B j).verts).Nonempty := by
    intro ⟨i, hi'⟩
    have hi_not_in : i ∉ I_star := (Finset.mem_sdiff.1 (hI'_sub hi')).2
    have hi_not_star : ¬ IsStarred i := fun hs ↦
      hi_not_in (Finset.mem_filter.2 ⟨Finset.mem_univ i, hs⟩)
    obtain ⟨v₀, hv₀⟩ := hmesh.meets i j₀
    have hAi_fin : (A i).verts.Finite := hG_fin.subset (hmesh.le_left i).1
    have hV_sub : ∀ j, V_ij i j ⊆ (A i).verts := fun _ ↦ Set.inter_subset_left
    have hV_disj : Pairwise fun j₁ j₂ ↦ Disjoint (V_ij i j₁) (V_ij i j₂) :=
      fun j₁ j₂ hne ↦ (hmesh.disjoint_right hne).mono Set.inter_subset_right Set.inter_subset_right
    have hV_ne : ∀ j, (V_ij i j).Nonempty := fun j ↦ hmesh.meets i j
    rcases theorem_5_1_simple hAi_fin (hmesh.connected_left i) hK_two (V_ij i) hV_sub hV_disj hV_ne
      ⟨j₀, hv₀⟩ with ⟨C, emb, v_leaf, hC_le, hC_conn, _, hleaf⟩ | ⟨P, hP_le, _, hP_card⟩
    · exfalso
      apply hi_not_star
      refine ⟨Finset.univ.map emb, C, by simp, hC_le, hC_conn, ?_⟩
      intro j hj
      rw [Finset.mem_map] at hj
      obtain ⟨r, _, rfl⟩ := hj
      exact ⟨v_leaf r, (hleaf r).2.2, (hleaf r).2.1⟩
    · have hcard_q : (metIndices (V_ij i) P.verts).card = q := by
        rw [hP_card]
        omega
      refine ⟨P, metIndices (V_ij i) P.verts, hP_le, hcard_q, fun j hj ↦ ?_⟩
      simp only [metIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨w, ⟨_, hwB⟩, hwP⟩ := hj
      exact ⟨w, hwP, hwB⟩
  choose P_of J_of hP_le hJ_card hP_meets using hpath_ex
  let P_q : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard q
  have hP_q_card : P_q.card = n.choose q := by
    simp [P_q, Finset.card_powersetCard]
  have hq_le_n : q ≤ n := le_pow_pred_of_two_le hK_two hq
  have hchoose_pos : 0 < n.choose q := Nat.choose_pos hq_le_n
  have hex_J'' : ∃ J'' ∈ P_q,
      p ≤ (I'.filter fun i ↦ (if h : i ∈ I' then J_of ⟨i, h⟩ else ∅) = J'').card := by
    by_contra! hlt
    have hbi : I' ⊆ P_q.biUnion fun S ↦
        I'.filter fun i ↦ (if h : i ∈ I' then J_of ⟨i, h⟩ else ∅) = S := by
      intro i hi
      rw [Finset.mem_biUnion]
      refine ⟨J_of ⟨i, hi⟩, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, hJ_card ⟨i, hi⟩⟩
      · simp [hi]
    have hle_sum : I'.card ≤ ∑ _S ∈ P_q, (p - 1) := by
      refine (Finset.card_le_card hbi).trans (Finset.card_biUnion_le.trans ?_)
      refine Finset.sum_le_sum fun S hS ↦ ?_
      have := hlt S hS
      omega
    rw [Finset.sum_const, smul_eq_mul, hP_q_card, hI'_card] at hle_sum
    have hlt_mul : n.choose q * (p - 1) < p * n.choose q := by
      rw [Nat.mul_comm]
      exact (Nat.mul_lt_mul_right hchoose_pos).2 (by omega)
    omega
  obtain ⟨J'', hJ''_mem, hJ''_fiber⟩ := hex_J''
  obtain ⟨I'', hI''_sub, hI''_card⟩ := Finset.exists_subset_card_eq hJ''_fiber
  let eI : Fin p ≃ I'' := (Finset.equivFinOfCardEq hI''_card).symm
  let embI : Fin p ↪ Fin m :=
    eI.toEmbedding.trans (Function.Embedding.subtype _)
  have hJ''_card : J''.card = q := (Finset.mem_powersetCard.1 hJ''_mem).2
  let eJ : Fin q ≃ J'' := (Finset.equivFinOfCardEq hJ''_card).symm
  let embJ : Fin q ↪ Fin n :=
    eJ.toEmbedding.trans (Function.Embedding.subtype _)
  have hi_in_I' : ∀ r : Fin p, embI r ∈ I' :=
    fun r ↦ (Finset.mem_filter.1 (hI''_sub (eI r).2)).1
  let P_out : Fin p → GM01.Path V := fun r ↦ P_of ⟨embI r, hi_in_I' r⟩
  have hP_out_le : ∀ r, (P_out r).toSubgraph ≤ A (embI r) :=
    fun r ↦ hP_le ⟨embI r, hi_in_I' r⟩
  refine ⟨embI, embJ, P_out, hP_out_le, ?_⟩
  refine
    { le_left := fun r ↦ (hP_out_le r).trans (hmesh.le_left (embI r))
      le_right := fun s ↦ hmesh.le_right (embJ s)
      connected_left := fun r ↦ (P_out r).connected_toSubgraph
      connected_right := fun s ↦ hmesh.connected_right (embJ s)
      disjoint_left := fun r₁ r₂ hne ↦
        (hmesh.disjoint_left (embI.injective.ne hne)).mono (hP_out_le r₁).1 (hP_out_le r₂).1
      disjoint_right := fun s₁ s₂ hne ↦ hmesh.disjoint_right (embJ.injective.ne hne)
      meets := fun r s ↦ by
        have hJ_eq : J_of ⟨embI r, hi_in_I' r⟩ = J'' := by
          have hmem := (Finset.mem_filter.1 (hI''_sub (eI r).2)).2
          have hi : embI r ∈ I' := hi_in_I' r
          change (if h : embI r ∈ I' then J_of ⟨embI r, h⟩ else ∅) = J'' at hmem
          rw [dite_eq_left hi] at hmem
          exact hmem
        have hs_mem : embJ s ∈ J_of ⟨embI r, hi_in_I' r⟩ := by
          rw [hJ_eq]
          exact (eJ s).2
        exact hP_meets ⟨embI r, hi_in_I' r⟩ (embJ s) hs_mem }

/-! ## Theorem (5.3) -/

/-- Graph Minors V, (5.3) (page 102):
"If $G \in \mathcal{F}_\theta$ then $G$ has no $(\theta_5, \theta_6)$-mesh." -/
theorem theorem_5_3_simple
    {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ) :
    ¬ HasMesh G (θ₅ θ) (θ₆ θ) := by
  rintro ⟨A₀, B₀, hmesh₀⟩
  have hmesh_symm : IsMesh G B₀ A₀ := hmesh₀.symm
  -- Step 1: Apply (5.2) with `p = θ₃ θ`, `q = θ₄ θ` to `(B₀, A₀)` (which is a `(θ₆, θ₅)`-mesh).
  obtain ⟨embI₁, embJ₁, P₁, _, hmesh₁⟩ :=
    theorem_5_2_simple hθ heven hG_fin hG (two_le_θ₃ hθ) (two_le_θ₄ hθ) hmesh_symm
  -- Step 2: Apply (5.2) with `p = θ₂ θ`, `q = θ₂ θ` to `((A₀ (embJ₁ s)), (P₁ r))`
  -- (which is a `(θ₄, θ₃)`-mesh).
  obtain ⟨embI₂, embJ₂, C, _, hmesh₂⟩ :=
    theorem_5_2_simple hθ heven hG_fin hG (two_le_θ₂ hθ) (two_le_θ₂ hθ) hmesh₁.symm
  let D : Fin (θ₂ θ) → GM01.Path V := fun s ↦ P₁ (embJ₂ s)
  -- Step 3: Contract every edge of `G` in both some `C i` and some `D j` to obtain a `(θ₂, θ₂)`-web
  -- in a minor `G' ∈ 𝓕_θ`, contradicting (4.6).
  exact not_hasMesh_paths_of_mem_𝓕 hθ heven G.verts.ncard hG_fin le_rfl hG C D
    hmesh₂.le_left hmesh₂.le_right hmesh₂.disjoint_left hmesh₂.disjoint_right hmesh₂.meets

end GraphMinor.GM05
