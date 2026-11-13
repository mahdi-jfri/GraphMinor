module

public import GraphMinor.GM05.Basic
import GraphMinor.GM05.Quoted
import GraphMinor.Menger.SimpleGraph

/-!
# Graph Minors V, Section 3: Grids

This file formalizes Section 3 of N. Robertson and P. D. Seymour,
*Graph Minors. V. Excluding a planar graph*, J. Combin. Theory Ser. B **41** (1986), 92–114
(pages 95–97):

- `theorem_3_2_base`: the base case `k = 2` of (3.2), deduced from Menger's theorem for finite
  simple graphs (`GraphMinor.Menger.exists_disjointPaths`).
- `theorem_3_2_case_1`: Case 1 of the inductive step of (3.2), forming `n` disjoint connected
  subgraphs `C_j ∪ P_j` (`j ∈ J`) meeting all of `V₁, …, V_k`.
- `theorem_3_2_case_2`: Case 2 of the inductive step of (3.2), using a separation `(W₁, W₂)` with
  `W₁ ∩ W₂ = X'` to restrict to `G' = G | (W₁ \ W₂)` and apply the inductive hypothesis.
- `theorem_3_2`: Graph Minors V, (3.2) (page 96).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set GM01

universe u

variable {V : Type u}

/-- A family of `n` pairwise vertex-disjoint connected subgraphs of `G`, each meeting every
`S i`. -/
@[expose]
def HasDisjointConnectedMeeting (G : (⊤ : SimpleGraph V).Subgraph) {k : ℕ}
    (S : Fin k → Set V) (n : ℕ) : Prop :=
  ∃ B : Fin n → (⊤ : SimpleGraph V).Subgraph,
    (∀ j, B j ≤ G) ∧ (∀ j, (B j).Connected) ∧
    Pairwise (fun j j' ↦ Disjoint (B j).verts (B j').verts) ∧
    ∀ i j, ((B j).verts ∩ S i).Nonempty

private lemma hasDisjointConnectedMeeting_zero (G : (⊤ : SimpleGraph V).Subgraph) {k : ℕ}
    (S : Fin k → Set V) : HasDisjointConnectedMeeting G S 0 :=
  ⟨Fin.elim0, fun j ↦ Fin.elim0 j, fun j ↦ Fin.elim0 j,
    fun i ↦ Fin.elim0 i, fun _ j ↦ Fin.elim0 j⟩

private lemma HasDisjointConnectedMeeting.mono {G : (⊤ : SimpleGraph V).Subgraph} {k : ℕ}
    {S : Fin k → Set V} {n m : ℕ} (hnm : n ≤ m) (h : HasDisjointConnectedMeeting G S m) :
    HasDisjointConnectedMeeting G S n := by
  obtain ⟨B, hBG, hBconn, hBdisj, hBmeet⟩ := h
  refine ⟨fun j ↦ B (Fin.castLE hnm j), fun j ↦ hBG _, fun j ↦ hBconn _,
    fun j j' hne ↦ hBdisj ((Fin.castLE_injective hnm).ne hne), fun i j ↦ hBmeet i _⟩

private lemma HasDisjointConnectedMeeting.le_ncard {G : (⊤ : SimpleGraph V).Subgraph}
    (hG_fin : G.verts.Finite) {k : ℕ} {S : Fin k → Set V} {n : ℕ}
    (h : HasDisjointConnectedMeeting G S n) : n ≤ G.verts.ncard := by
  obtain ⟨B, hBG, hBconn, hBdisj, _⟩ := h
  have hex : ∀ j : Fin n, ∃ x : V, x ∈ (B j).verts := fun j ↦ (hBconn j).nonempty
  choose x hx using hex
  have hxG : ∀ j : Fin n, x j ∈ G.verts := fun j ↦ (hBG j).1 (hx j)
  let f : Fin n → ↥G.verts := fun j ↦ ⟨x j, hxG j⟩
  have hf_inj : Function.Injective f := by
    intro j j' heq
    by_contra hne
    have hxj : x j = x j' := congrArg Subtype.val heq
    exact Set.disjoint_left.1 (hBdisj hne) (hx j) (hxj ▸ hx j')
  have : Finite ↥G.verts := hG_fin.to_subtype
  have hle := Nat.card_le_card_of_injective f hf_inj
  rw [Nat.card_fin, Nat.card_coe_set_eq] at hle
  exact hle

/-- Base case `k = 2` of Graph Minors V, (3.2) (page 96): "If $k = 2$ the result follows from Menger's theorem" -/
theorem theorem_3_2_base {G : (⊤ : SimpleGraph V).Subgraph} {θ n : ℕ}
    (hG_fin : G.verts.Finite) (S : Fin 2 → Set V) :
    HasDisjointConnectedMeeting G S n ∨
      (∃ X ⊆ G.verts, X.ncard < α θ 2 n ∧
        ∀ B : (⊤ : SimpleGraph V).Subgraph, B ≤ G → B.Connected →
          (∀ i, (B.verts ∩ S i).Nonempty) → (B.verts ∩ X).Nonempty) := by
  classical
  let K₀ : SimpleGraph ↥G.verts := G.coe
  let A₀ : Set ↥G.verts := Subtype.val ⁻¹' S 0
  let B₀ : Set ↥G.verts := Subtype.val ⁻¹' S 1
  have hfin₀ : Finite ↥G.verts := hG_fin.to_subtype
  by_cases hsep_all : ∀ S₀ : Set ↥G.verts,
      (∀ P : PathFromTo K₀ A₀ B₀, ∃ x ∈ P.walk.support, x ∈ S₀) → n ≤ S₀.ncard
  · left
    obtain ⟨P₀, hP₀_disj⟩ := Menger.exists_disjointPaths K₀ A₀ B₀ hfin₀ n hsep_all
    let B : Fin n → (⊤ : SimpleGraph V).Subgraph := fun j ↦
      ((P₀ j).walk.map G.hom).toSubgraph
    have hB_verts : ∀ (j : Fin n) (v : V),
        v ∈ (B j).verts ↔ ∃ u ∈ (P₀ j).walk.support, u.1 = v := by
      intro j v
      simp only [B, Walk.mem_verts_toSubgraph, Walk.support_map, List.mem_map]
      rfl
    refine ⟨B, ?_, ?_, ?_, ?_⟩
    · intro j
      have hwalk_le : ∀ {x y : ↥G.verts} (w : G.coe.Walk x y),
          (w.map G.hom).toSubgraph ≤ G := by
        intro x y w
        induction w with
        | @nil u =>
          change (Walk.nil : (⊤ : SimpleGraph V).Walk u.1 u.1).toSubgraph ≤ G
          simp [u.2]
        | @cons u v z hadj rest ih =>
          rw [Walk.map_cons, Walk.toSubgraph]
          have hadjG : G.Adj u.1 v.1 := hadj
          exact sup_le (subgraphOfAdj_le_of_adj G hadjG) ih
      exact hwalk_le (P₀ j).walk
    · intro j
      exact Walk.toSubgraph_connected _
    · intro j j' hne
      rw [Set.disjoint_left]
      intro v hvj hvj'
      obtain ⟨u, hu, rfl⟩ := (hB_verts j v).1 hvj
      obtain ⟨u', hu', hu'_eq⟩ := (hB_verts j' u.1).1 hvj'
      have huu' : u = u' := Subtype.ext hu'_eq.symm
      exact Set.disjoint_left.1 (hP₀_disj hne) hu (huu' ▸ hu')
    · intro i j
      fin_cases i
      · refine ⟨(P₀ j).first.1, ?_, (P₀ j).first_mem⟩
        rw [hB_verts]
        exact ⟨(P₀ j).first, Walk.start_mem_support _, rfl⟩
      · refine ⟨(P₀ j).last.1, ?_, (P₀ j).last_mem⟩
        rw [hB_verts]
        exact ⟨(P₀ j).last, Walk.end_mem_support _, rfl⟩
  · right
    push Not at hsep_all
    obtain ⟨S₀, hS₀_sep, hS₀_lt⟩ := hsep_all
    let X : Set V := Subtype.val '' S₀
    have hX_sub : X ⊆ G.verts := by
      rintro _ ⟨u, _, rfl⟩
      exact u.2
    have hX_card : X.ncard < α θ 2 n := by
      rw [α_two, Set.ncard_image_of_injective S₀ Subtype.val_injective]
      omega
    refine ⟨X, hX_sub, hX_card, fun B hBG hBconn hBmeet ↦ ?_⟩
    obtain ⟨a, haB, haS0⟩ := hBmeet 0
    obtain ⟨b, hbB, hbS1⟩ := hBmeet 1
    obtain ⟨p, hp⟩ :=
      ((Subgraph.connected_iff_forall_exists_walk_subgraph B).1 hBconn).2 haB hbB
    have hpG : p.toSubgraph ≤ G := hp.trans hBG
    have hlift : ∀ {u v : V} (q : (⊤ : SimpleGraph V).Walk u v) (hq : q.toSubgraph ≤ G)
        (hu : u ∈ G.verts) (hv : v ∈ G.verts),
        ∃ q₀ : K₀.Walk ⟨u, hu⟩ ⟨v, hv⟩, ∀ z ∈ q₀.support, z.1 ∈ q.toSubgraph.verts := by
      intro u v q
      induction q with
      | nil =>
        intro _ hu _
        refine ⟨.nil, ?_⟩
        simp
      | @cons u w v _ rest ih =>
        intro hq hu hv
        rw [Walk.toSubgraph, sup_le_iff] at hq
        have hadjG : G.Adj u w := hq.1.2 (by simp)
        have hwG : w ∈ G.verts := hadjG.snd_mem
        obtain ⟨q₀, hq₀⟩ := ih hq.2 hwG hv
        have hadj₀ : K₀.Adj ⟨u, hu⟩ ⟨w, hwG⟩ := hadjG
        refine ⟨.cons hadj₀ q₀, ?_⟩
        intro z hz
        rw [Walk.support_cons, List.mem_cons] at hz
        rw [Walk.toSubgraph, Subgraph.verts_sup, Set.mem_union]
        rcases hz with rfl | hz
        · left
          simp [subgraphOfAdj]
        · exact Or.inr (hq₀ z hz)
    obtain ⟨q₀, hq₀⟩ := hlift p hpG (hBG.1 haB) (hBG.1 hbB)
    let P₀ : PathFromTo K₀ A₀ B₀ :=
      ⟨⟨a, hBG.1 haB⟩, ⟨b, hBG.1 hbB⟩, q₀.bypass, q₀.bypass_isPath, haS0, hbS1⟩
    obtain ⟨z, hz_supp, hz_S₀⟩ := hS₀_sep P₀
    have hz_q₀ : z ∈ q₀.support := q₀.support_bypass_subset_support hz_supp
    have hz_B : z.1 ∈ B.verts := hp.1 (hq₀ z hz_q₀)
    exact ⟨z.1, hz_B, z, hz_S₀, rfl⟩

/-- Case 1 of the inductive step of Graph Minors V, (3.2) (page 96):
"There exists $J \subseteq \{1, \dots, N - n\}$ with $|J| = n$ such that for each $j \in J$
there is a path $P_j$ from $C_j$ to $V_k$, and the paths $P_j$ ($j \in J$) are disjoint, and
each has no internal vertex in $V_k \cup \bigcup_{j \in J} V(C_j)$.* In this case (i) is
true, using the subgraphs $C_j \cup P_j$ ($j \in J$)."
-/
theorem theorem_3_2_case_1 {G : (⊤ : SimpleGraph V).Subgraph} {m n M : ℕ}
    {S : Fin (m + 1) → Set V} {C' : Fin M → (⊤ : SimpleGraph V).Subgraph}
    (hC'_le : ∀ j, C' j ≤ G) (hC'_conn : ∀ j, (C' j).Connected)
    (hC'_disj : Pairwise fun j j' ↦ Disjoint (C' j).verts (C' j').verts)
    (hC'_meet : ∀ (i : Fin m) (j : Fin M), ((C' j).verts ∩ S i.castSucc).Nonempty)
    (hC'_avoid : ∀ j : Fin M, Disjoint (C' j).verts (S (Fin.last m)))
    {J : Finset (Fin M)} {P : J → GM01.Path V} (hJ_card : J.card = n)
    (hP_fromTo : ∀ j : J, (P j).IsFromTo G (C' j.1).verts (S (Fin.last m)))
    (hP_disj : Pairwise fun j j' : J ↦ Disjoint (P j).verts (P j').verts)
    (hP_int : ∀ j : J,
      Disjoint (P j).internalVerts (S (Fin.last m) ∪ ⋃ j' ∈ J, (C' j').verts)) :
    HasDisjointConnectedMeeting G S n := by
  let e : Fin n ≃ J := (Finset.equivFinOfCardEq hJ_card).symm
  let B : Fin n → (⊤ : SimpleGraph V).Subgraph := fun l ↦
    C' (e l).1 ⊔ (P (e l)).toSubgraph
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro l
    exact sup_le (hC'_le _) (hP_fromTo (e l)).1
  · intro l
    have hconn₁ := hC'_conn (e l).1
    have hconn₂ := (P (e l)).connected_toSubgraph
    have hfirst_C : (P (e l)).first ∈ (C' (e l).1).verts := (hP_fromTo (e l)).2.1
    have hfirst_P : (P (e l)).first ∈ (P (e l)).toSubgraph.verts := (P (e l)).first_mem_verts
    rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
    refine ⟨⟨(P (e l)).first, Or.inl hfirst_C⟩, fun {u v} hu hv ↦ ?_⟩
    have hreach : ∀ x ∈ (C' (e l).1 ⊔ (P (e l)).toSubgraph).verts,
        ∃ p : (⊤ : SimpleGraph V).Walk (P (e l)).first x,
          p.toSubgraph ≤ C' (e l).1 ⊔ (P (e l)).toSubgraph := by
      rintro x (hxC | hxP)
      · obtain ⟨p, hp⟩ :=
          ((Subgraph.connected_iff_forall_exists_walk_subgraph _).1 hconn₁).2 hfirst_C hxC
        exact ⟨p, hp.trans le_sup_left⟩
      · obtain ⟨p, hp⟩ :=
          ((Subgraph.connected_iff_forall_exists_walk_subgraph _).1 hconn₂).2 hfirst_P hxP
        exact ⟨p, hp.trans le_sup_right⟩
    obtain ⟨pu, hpu⟩ := hreach u hu
    obtain ⟨pv, hpv⟩ := hreach v hv
    refine ⟨pu.reverse.append pv, ?_⟩
    rw [Walk.toSubgraph_append, Walk.toSubgraph_reverse]
    exact sup_le hpu hpv
  · intro l₁ l₂ hne
    have hne_e : e l₁ ≠ e l₂ := e.injective.ne hne
    have hne_val : (e l₁).1 ≠ (e l₂).1 := Subtype.coe_ne_coe.2 hne_e
    have hdisj_P_C : ∀ (a b : J), a ≠ b → Disjoint (P a).verts (C' b.1).verts := by
      intro a b hab
      rw [Set.disjoint_left]
      intro v hvP hvC
      by_cases hv_ends : v ∈ (P a).ends
      · rcases hv_ends with rfl | rfl
        · exact Set.disjoint_left.1 (hC'_disj (Subtype.coe_ne_coe.2 hab))
            (hP_fromTo a).2.1 hvC
        · exact Set.disjoint_left.1 (hC'_avoid b.1) hvC (hP_fromTo a).2.2
      · have hv_int : v ∈ (P a).internalVerts := ⟨hvP, hv_ends⟩
        have hv_union : v ∈ S (Fin.last m) ∪ ⋃ j' ∈ J, (C' j').verts :=
          Or.inr (Set.mem_biUnion b.2 hvC)
        exact Set.disjoint_left.1 (hP_int a) hv_int hv_union
    change Disjoint ((C' (e l₁).1).verts ∪ (P (e l₁)).verts)
      ((C' (e l₂).1).verts ∪ (P (e l₂)).verts)
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    exact ⟨⟨hC'_disj hne_val, (hdisj_P_C (e l₂) (e l₁) hne_e.symm).symm⟩,
      ⟨hdisj_P_C (e l₁) (e l₂) hne_e, hP_disj hne_e⟩⟩
  · intro i l
    induction i using Fin.lastCases with
    | last =>
      refine ⟨(P (e l)).last, Or.inr (P (e l)).last_mem_verts, (hP_fromTo (e l)).2.2⟩
    | cast i₀ =>
      obtain ⟨v, hvC, hvS⟩ := hC'_meet i₀ (e l).1
      exact ⟨v, Or.inl hvC, hvS⟩

/-- Case 2 of the inductive step of Graph Minors V, (3.2) (page 96):
given `X' ⊆ V(G)` and `J ⊆ {1, …, N - n}` with `|X'| + |J| ≤ 2^{n θ⁴}` such that `X'` separates
`V_k` from every `C_j` (`j ∉ J`), the maximality of `N` and the inductive hypothesis on
`G' = G | (W₁ \ W₂)` yield `X = X' ∪ X''` of size `< α(k, n)` meeting every connected subgraph of
`G` that meets all of `V₁, …, V_k`. -/
theorem theorem_3_2_case_2 {G : (⊤ : SimpleGraph V).Subgraph} {θ m n N : ℕ}
    (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ) (hm : 2 ≤ m)
    {S : Fin (m + 1) → Set V} (hS : ∀ i, S i ⊆ G.verts)
    (hN_max : ¬ HasDisjointConnectedMeeting G (fun i : Fin m ↦ S i.castSucc) (N + 1))
    (hnN : n ≤ N)
    {C : Fin N → (⊤ : SimpleGraph V).Subgraph}
    (hC_le : ∀ j, C j ≤ G) (hC_conn : ∀ j, (C j).Connected)
    (hC_disj : Pairwise fun j j' ↦ Disjoint (C j).verts (C j').verts)
    (hC_meet : ∀ (i : Fin m) (j : Fin N), ((C j).verts ∩ S i.castSucc).Nonempty)
    {emb : Fin (N - n) ↪ Fin N}
    {X' : Set V} {J : Finset (Fin (N - n))}
    (hX'_sub : X' ⊆ G.verts) (hXJ_card : X'.ncard + J.card ≤ 2 ^ (n * θ ^ 4))
    (hsep_X' : ∀ j : Fin (N - n), j ∉ J → Separates G X' (S (Fin.last m)) (C (emb j)).verts)
    (ih : ∀ {G' : (⊤ : SimpleGraph V).Subgraph},
      G'.verts.Finite → G' ∈ 𝓕 θ →
      ∀ (S' : Fin m → Set V), (∀ i, S' i ⊆ G'.verts) → ∀ (n' : ℕ),
        HasDisjointConnectedMeeting G' S' n' ∨
          (∃ X'' ⊆ G'.verts, X''.ncard < α θ m n' ∧
            ∀ B : (⊤ : SimpleGraph V).Subgraph, B ≤ G' → B.Connected →
              (∀ i, (B.verts ∩ S' i).Nonempty) → (B.verts ∩ X'').Nonempty)) :
    ∃ X ⊆ G.verts, X.ncard < α θ (m + 1) n ∧
      ∀ B : (⊤ : SimpleGraph V).Subgraph, B ≤ G → B.Connected →
        (∀ i, (B.verts ∩ S i).Nonempty) → (B.verts ∩ X).Nonempty := by
  classical
  let U : Set V := ⋃ j ∈ Finset.univ \ J, (C (emb j)).verts
  have hU_sub : U ⊆ G.verts := by
    rintro v ⟨_, ⟨j, rfl⟩, _, ⟨_, rfl⟩, hv⟩
    exact (hC_le (emb j)).1 hv
  have hsep_U : Separates G X' (S (Fin.last m)) U := by
    intro P ⟨hPG, hPfirst, hPlast⟩ havoid
    obtain ⟨_, ⟨j, rfl⟩, _, ⟨hj, rfl⟩, hlast_j⟩ := hPlast
    have hj_notJ : j ∉ J := (Finset.mem_sdiff.1 hj).2
    exact hsep_X' j hj_notJ P ⟨hPG, hPfirst, hlast_j⟩ havoid
  obtain ⟨W₁, W₂, hsepW, hW_inter, hVk_W₁, hU_W₂⟩ :=
    exists_isSeparation_of_separates hX'_sub (hS (Fin.last m)) hU_sub hsep_U
  let W : Set V := W₁ \ W₂
  have hW_sub : W ⊆ G.verts := Set.sdiff_subset.trans hsepW.subset_left
  let G' : (⊤ : SimpleGraph V).Subgraph := G.induce W
  have hG'_le : G' ≤ G := ⟨hW_sub, fun _ _ h ↦ h.2.2⟩
  have hG'_fin : G'.verts.Finite := hG_fin.subset hW_sub
  have hG'_mem : G' ∈ 𝓕 θ := mem_𝓕_of_le hG'_le hG
  let S' : Fin m → Set V := fun i ↦ S i.castSucc ∩ W
  have hS'_sub : ∀ i, S' i ⊆ G'.verts := fun _ _ h ↦ h.2
  let n' : ℕ := 2 ^ (n * θ ^ 4) + n + 1
  have hnot_G' : ¬ HasDisjointConnectedMeeting G' S' n' := by
    intro hG'_has
    have hJn_le : J.card + n + 1 ≤ n' := by
      dsimp [n']
      generalize 2 ^ (n * θ ^ 4) = B at hXJ_card ⊢
      omega
    obtain ⟨D, hDG', hDconn, hDdisj, hDmeet⟩ := hG'_has.mono hJn_le
    let K : Finset (Fin (N - n)) := Finset.univ \ J
    have hK_card : K.card = N - n - J.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ J), Finset.card_univ, Fintype.card_fin]
    have hJ_le : J.card ≤ N - n := by
      have := Finset.card_le_univ J
      rwa [Fintype.card_fin] at this
    have hsum : (J.card + n + 1) + K.card = N + 1 := by omega
    let eK : Fin K.card ≃ K := (Finset.equivFin K).symm
    let C_comb : Fin ((J.card + n + 1) + K.card) → (⊤ : SimpleGraph V).Subgraph :=
      Fin.addCases D (fun r ↦ C (emb (eK r).1))
    have hC_K_disj_W : ∀ r : Fin K.card, Disjoint (C (emb (eK r).1)).verts W := by
      intro r
      have hsub_W₂ : (C (emb (eK r).1)).verts ⊆ W₂ := by
        intro v hv
        exact hU_W₂ (Set.mem_biUnion (eK r).2 hv)
      rw [Set.disjoint_left]
      intro v hvC hvW
      exact hvW.2 (hsub_W₂ hvC)
    have hcomb : HasDisjointConnectedMeeting G (fun i : Fin m ↦ S i.castSucc)
        ((J.card + n + 1) + K.card) := by
      refine ⟨C_comb, ?_, ?_, ?_, ?_⟩
      · intro l
        induction l using Fin.addCases with
        | left l₁ =>
          simp only [C_comb, Fin.addCases_left]
          exact (hDG' l₁).trans hG'_le
        | right l₂ =>
          simp only [C_comb, Fin.addCases_right]
          exact hC_le _
      · intro l
        induction l using Fin.addCases with
        | left l₁ =>
          simp only [C_comb, Fin.addCases_left]
          exact hDconn l₁
        | right l₂ =>
          simp only [C_comb, Fin.addCases_right]
          exact hC_conn _
      · intro l₁ l₂ hne
        induction l₁ using Fin.addCases with
        | left a₁ =>
          induction l₂ using Fin.addCases with
          | left a₂ =>
            simp only [C_comb, Fin.addCases_left]
            exact hDdisj (fun h ↦ hne (congrArg (Fin.castAdd K.card) h))
          | right b₂ =>
            simp only [C_comb, Fin.addCases_left, Fin.addCases_right]
            exact Disjoint.mono_left (hDG' a₁).1 (hC_K_disj_W b₂).symm
        | right b₁ =>
          induction l₂ using Fin.addCases with
          | left a₂ =>
            simp only [C_comb, Fin.addCases_left, Fin.addCases_right]
            exact Disjoint.mono_right (hDG' a₂).1 (hC_K_disj_W b₁)
          | right b₂ =>
            simp only [C_comb, Fin.addCases_right]
            have hne_b : b₁ ≠ b₂ := fun h ↦ hne (congrArg (Fin.natAdd (J.card + n + 1)) h)
            have hne_emb : emb (eK b₁).1 ≠ emb (eK b₂).1 :=
              emb.injective.ne (Subtype.coe_ne_coe.2 (eK.injective.ne hne_b))
            exact hC_disj hne_emb
      · intro i l
        induction l using Fin.addCases with
        | left a =>
          simp only [C_comb, Fin.addCases_left]
          obtain ⟨v, hvD, hvS, _⟩ := hDmeet i a
          exact ⟨v, hvD, hvS⟩
        | right b =>
          simp only [C_comb, Fin.addCases_right]
          exact hC_meet i _
    exact hN_max (hsum ▸ hcomb)
  rcases ih hG'_fin hG'_mem S' hS'_sub n' with hG'_has | ⟨X'', hX''_sub, hX''_card, hX''_meet⟩
  · exact False.elim (hnot_G' hG'_has)
  · refine ⟨X' ∪ X'', Set.union_subset hX'_sub (hX''_sub.trans hW_sub), ?_, ?_⟩
    · have hX'_fin : X'.Finite := hG_fin.subset hX'_sub
      have hX''_fin : X''.Finite := hG'_fin.subset hX''_sub
      have hunion_le : (X' ∪ X'').ncard ≤ X'.ncard + X''.ncard :=
        Set.ncard_union_le X' X''
      rw [α_succ_of_two_le θ hm n]
      dsimp [n'] at hX''_card
      generalize 2 ^ (n * θ ^ 4) = B at hXJ_card hX''_card ⊢
      omega
    · intro B hBG hBconn hBmeet
      by_cases hBX' : (B.verts ∩ X').Nonempty
      · obtain ⟨x, hxB, hxX'⟩ := hBX'
        exact ⟨x, hxB, Or.inl hxX'⟩
      · have hdisj_X' : Disjoint B.verts (W₁ ∩ W₂) := by
          rw [hW_inter, Set.disjoint_iff_inter_eq_empty]
          exact Set.not_nonempty_iff_eq_empty.1 hBX'
        have hmeet_W₁ : (B.verts ∩ W₁).Nonempty := by
          obtain ⟨v, hvB, hvVk⟩ := hBmeet (Fin.last m)
          exact ⟨v, hvB, hVk_W₁ hvVk⟩
        have hB_le_G' : B ≤ G' :=
          hsepW.le_induce_diff_of_preconnected hBG hBconn.preconnected hdisj_X' hmeet_W₁
        have hB_meet_S' : ∀ i : Fin m, (B.verts ∩ S' i).Nonempty := by
          intro i
          obtain ⟨v, hvB, hvS⟩ := hBmeet i.castSucc
          exact ⟨v, hvB, hvS, hB_le_G'.1 hvB⟩
        obtain ⟨x, hxB, hxX''⟩ := hX''_meet B hB_le_G' hBconn hB_meet_S'
        exact ⟨x, hxB, Or.inr hxX''⟩

/-- Graph Minors V, (3.2) (page 96):
"Let $G \in \mathcal{F}_\theta$, and let $V_1, \dots, V_k \subseteq V(G)$, where $k \ge 2$.
Let $n \ge 0$ be an integer. Then at least one of the following is true:* (i) *there are
disjoint connected subgraphs $B_1, \dots, B_n$ of $G$ such that each $B_j$ meets each $V_i$
($1 \le i \le k, 1 \le j \le n$)* (ii) *there exists $X \subseteq V(G)$ with $|X| <
\alpha(k, n)$ such that every connected subgraph of $G$ which meets all of $V_1, \dots, V_k$
also meets $X$." -/
theorem theorem_3_2_simple {G : (⊤ : SimpleGraph V).Subgraph} {θ k n : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (hk : 2 ≤ k) (S : Fin k → Set V) (hS : ∀ i, S i ⊆ G.verts) :
    HasDisjointConnectedMeeting G S n ∨
      (∃ X ⊆ G.verts, X.ncard < α θ k n ∧
        ∀ B : (⊤ : SimpleGraph V).Subgraph, B ≤ G → B.Connected →
          (∀ i, (B.verts ∩ S i).Nonempty) → (B.verts ∩ X).Nonempty) := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d generalizing G n with
  | zero =>
    exact theorem_3_2_base hG_fin S
  | succ d ih =>
    let m : ℕ := 2 + d
    have hm : 2 ≤ m := Nat.le_add_right 2 d
    let SInit : Fin m → Set V := fun i ↦ S i.castSucc
    have hSInit : ∀ i, SInit i ⊆ G.verts := fun i ↦ hS i.castSucc
    have hex_not : ∃ M : ℕ, ¬ HasDisjointConnectedMeeting G SInit (M + 1) :=
      ⟨G.verts.ncard, fun h ↦ by
        have := h.le_ncard hG_fin
        omega⟩
    let N : ℕ := Nat.find hex_not
    have hN_max : ¬ HasDisjointConnectedMeeting G SInit (N + 1) := Nat.find_spec hex_not
    have hN_has : HasDisjointConnectedMeeting G SInit N := by
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · rw [hN0]
        exact hasDisjointConnectedMeeting_zero G SInit
      · have hlt : N - 1 < N := Nat.sub_lt hNpos (by decide)
        have hnot_not := Nat.find_min hex_not hlt
        rw [not_not, Nat.sub_add_cancel hNpos] at hnot_not
        exact hnot_not
    by_cases hnN : n ≤ N
    · obtain ⟨C, hC_le, hC_conn, hC_disj, hC_meet⟩ := hN_has
      let Good : Finset (Fin N) :=
        Finset.univ.filter fun j ↦ ((C j).verts ∩ S (Fin.last m)).Nonempty
      let Bad : Finset (Fin N) :=
        Finset.univ.filter fun j ↦ ¬ ((C j).verts ∩ S (Fin.last m)).Nonempty
      by_cases hGood : n ≤ Good.card
      · left
        let eG : Fin Good.card ≃ Good := (Finset.equivFin Good).symm
        let idx : Fin n ↪ Fin N :=
          (Fin.castLEEmb hGood).trans (eG.toEmbedding.trans (Function.Embedding.subtype _))
        refine ⟨fun l ↦ C (idx l), fun l ↦ hC_le _, fun l ↦ hC_conn _,
          fun l₁ l₂ hne ↦ hC_disj (idx.injective.ne hne), fun i l ↦ ?_⟩
        induction i using Fin.lastCases with
        | last =>
          have hmem : idx l ∈ Good := (eG (Fin.castLE hGood l)).2
          exact (Finset.mem_filter.1 hmem).2
        | cast i₀ =>
          exact hC_meet i₀ (idx l)
      · have hcard_sum : Good.card + Bad.card = N := by
          have := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin N)))
            (fun j ↦ ((C j).verts ∩ S (Fin.last m)).Nonempty)
          simpa [Good, Bad] using this
        have hBad : N - n ≤ Bad.card := by omega
        let eB : Fin Bad.card ≃ Bad := (Finset.equivFin Bad).symm
        let emb : Fin (N - n) ↪ Fin N :=
          (Fin.castLEEmb hBad).trans (eB.toEmbedding.trans (Function.Embedding.subtype _))
        have hemb_avoid : ∀ j : Fin (N - n), Disjoint (C (emb j)).verts (S (Fin.last m)) := by
          intro j
          have hmem : emb j ∈ Bad := (eB (Fin.castLE hBad j)).2
          have hnot_nonempty := (Finset.mem_filter.1 hmem).2
          rw [Set.disjoint_iff_inter_eq_empty]
          exact Set.not_nonempty_iff_eq_empty.1 hnot_nonempty
        let C' : Fin (N - n) → (⊤ : SimpleGraph V).Subgraph := fun j ↦ C (emb j)
        have hC'_le : ∀ j, C' j ≤ G := fun j ↦ hC_le (emb j)
        have hC'_conn : ∀ j, (C' j).Connected := fun j ↦ hC_conn (emb j)
        have hC'_disj : Pairwise fun j j' ↦ Disjoint (C' j).verts (C' j').verts :=
          fun j j' hne ↦ hC_disj (emb.injective.ne hne)
        have hC'_meet : ∀ (i : Fin m) (j : Fin (N - n)),
            ((C' j).verts ∩ S i.castSucc).Nonempty := fun i j ↦ hC_meet i (emb j)
        rcases theorem_3_1_simple hθ heven hG_fin hG C' hC'_le hC'_conn hC'_disj
            (S (Fin.last m)) (hS (Fin.last m)) n with
          ⟨J, P, hJ_card, hP_fromTo, hP_disj, hP_int⟩ |
          ⟨X', J, hX'_sub, hXJ_card, hsep_X'⟩
        · exact Or.inl (theorem_3_2_case_1 hC'_le hC'_conn hC'_disj hC'_meet hemb_avoid
            hJ_card hP_fromTo hP_disj hP_int)
        · exact Or.inr (theorem_3_2_case_2 hG_fin hG hm hS hN_max hnN hC_le hC_conn
            hC_disj hC_meet hX'_sub hXJ_card hsep_X' (fun hfin' hmem' S' hS' _ ↦
              ih hfin' hmem' S' hS'))
    · right
      have hnot_n : ¬ HasDisjointConnectedMeeting G SInit n := by
        intro hn_has
        have hN1_le_n : N + 1 ≤ n := by omega
        exact hN_max (hn_has.mono hN1_le_n)
      rcases ih hG_fin hG SInit hSInit with hn_has | ⟨X, hX_sub, hX_card, hX_meet⟩
      · exact False.elim (hnot_n hn_has)
      · refine ⟨X, hX_sub, lt_of_lt_of_le hX_card (α_le_α_succ θ m n),
          fun B hBG hBconn hBmeet ↦ hX_meet B hBG hBconn (fun i ↦ hBmeet i.castSucc)⟩

end GraphMinor.GM05
