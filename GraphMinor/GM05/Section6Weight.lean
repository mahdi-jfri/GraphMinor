module

public import GraphMinor.GM05.Defs
import GraphMinor.GM05.Basic
import GraphMinor.GM05.Section5Aux
import GraphMinor.GM05.Section6Bipolar

/-!
# Graph Minors V, Section 6 (Part 2): Weighted Vertex Separators (Theorem (6.2))

This file proves Theorem (6.2) of Robertson and Seymour, *Graph Minors. V. Excluding a Planar
Graph*, J. Combin. Theory Ser. B 41 (1986), 92–114 (pages 103–104):
given a finite connected graph `G`, a vertex weight function `w : V → ℕ`, and `0 < k` with
`k ≤ (w(V(G)) + 2) / 3`, either `G` has two vertex-disjoint connected induced subgraphs each of
weight at least `k`, or `G` has a vertex `v` such that every component of `G \ v` has weight less
than `k` (and not both).
-/

namespace GraphMinor.GM05

open SimpleGraph

variable {V : Type*}

public section

/-! ## Statement of Conditions (i) and (ii) of (6.2) -/

/-- Condition (i) of Theorem (6.2) (page 103):
"there are disjoint subsets $V_1$, $V_2$ of $V(G)$ such that $G|V_1$, $G|V_2$ are both
connected and $w(V_1), w(V_2) \ge k$" -/
@[expose]
def Cond62_i (G : (⊤ : SimpleGraph V).Subgraph) (w : V → ℕ) (k : ℕ) : Prop :=
  ∃ V₁ V₂ : Set V, V₁ ⊆ G.verts ∧ V₂ ⊆ G.verts ∧ Disjoint V₁ V₂ ∧
    (G.induce V₁).Connected ∧ (G.induce V₂).Connected ∧
    k ≤ weightSum w V₁ ∧ k ≤ weightSum w V₂

/-- Condition (ii) of Theorem (6.2) (page 103):
"there is a vertex $v$ of $G$ such that $w(V(C)) < k$ for every component $C$ of $G \setminus
v$." -/
@[expose]
def Cond62_ii (G : (⊤ : SimpleGraph V).Subgraph) (w : V → ℕ) (k : ℕ) : Prop :=
  ∃ v ∈ G.verts, ∀ C : (⊤ : SimpleGraph V).Subgraph,
    IsComponentOf C (G.deleteVerts {v}) → weightSum w C.verts < k

/-! ## Helper Lemmas on Weights and Induced Subgraphs -/

private lemma nonempty_of_weightSum_pos {w : V → ℕ} {X : Set V} (hpos : 0 < weightSum w X) :
    X.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  subst h
  simp at hpos

private lemma connected_induce_of_preconnected_of_weightSum_pos
    {G : (⊤ : SimpleGraph V).Subgraph} {w : V → ℕ} {X : Set V}
    (hpre : (G.induce X).Preconnected) (hpos : 0 < weightSum w X) :
    (G.induce X).Connected := by
  obtain ⟨x, hx⟩ := nonempty_of_weightSum_pos hpos
  rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
  exact ⟨⟨x, hx⟩, (Subgraph.preconnected_iff_forall_exists_walk_subgraph _).1 hpre⟩

private lemma induce_le_deleteVerts_singleton {G : (⊤ : SimpleGraph V).Subgraph}
    {X : Set V} {v : V} (hX : X ⊆ G.verts) (hv : v ∉ X) :
    G.induce X ≤ G.deleteVerts {v} := by
  rw [Subgraph.deleteVerts]
  refine ⟨fun x hx ↦ ⟨hX hx, fun hxv ↦ hv (Set.mem_singleton_iff.1 hxv ▸ hx)⟩, ?_⟩
  intro x y hadj
  exact ⟨⟨hX hadj.1, fun hxv ↦ hv (Set.mem_singleton_iff.1 hxv ▸ hadj.1)⟩,
    ⟨hX hadj.2.1, fun hyv ↦ hv (Set.mem_singleton_iff.1 hyv ▸ hadj.2.1)⟩, hadj.2.2⟩

/-- Not both (i) and (ii) of (6.2) can hold ("Clearly not both (i) and (ii) hold", page 103). -/
lemma not_cond62_i_and_ii {G : (⊤ : SimpleGraph V).Subgraph} (hG_fin : G.verts.Finite)
    (w : V → ℕ) (k : ℕ) :
    ¬ (Cond62_i G w k ∧ Cond62_ii G w k) := by
  rintro ⟨⟨V₁, V₂, hV₁G, hV₂G, hdisj, hconn₁, hconn₂, hw₁, hw₂⟩, ⟨v, _, hcomp⟩⟩
  have hcheck : ∀ {U : Set V}, U ⊆ G.verts → v ∉ U → (G.induce U).Connected →
      k ≤ weightSum w U → False := by
    intro U hUG hvU hconnU hwU
    have hle : G.induce U ≤ G.deleteVerts {v} := induce_le_deleteVerts_singleton hUG hvU
    obtain ⟨u₀, hu₀U⟩ := hconnU.nonempty
    let H := G.deleteVerts {v}
    let c := H.coe.connectedComponentMk ⟨u₀, hle.1 hu₀U⟩
    have hle_comp : G.induce U ≤ componentSubgraph H c :=
      le_componentSubgraph_of_preconnected hle hconnU.preconnected hu₀U
    have hcomp_c : IsComponentOf (componentSubgraph H c) H :=
      isComponentOf_componentSubgraph H c
    have hlt : weightSum w (componentSubgraph H c).verts < k := hcomp _ hcomp_c
    have hC_fin : (componentSubgraph H c).verts.Finite :=
      hG_fin.subset ((componentSubgraph_le H c).trans Subgraph.deleteVerts_le).1
    have hle_w : weightSum w U ≤ weightSum w (componentSubgraph H c).verts :=
      weightSum_mono w hC_fin hle_comp.1
    omega
  by_cases hv₁ : v ∈ V₁
  · have hv₂ : v ∉ V₂ := Set.disjoint_left.1 hdisj hv₁
    exact hcheck hV₂G hv₂ hconn₂ hw₂
  · exact hcheck hV₁G hv₁ hconn₁ hw₁

/-! ## Case 1 of Theorem (6.2): `G` is Not 2-Connected -/

/-- If `C₁` is a component of `G.deleteVerts {u}`, then `(insert u C₁.verts, G.verts \ C₁.verts)` is
a separation of `G`. -/
private lemma isSeparation_component_deleteVerts_singleton {G C₁ : (⊤ : SimpleGraph V).Subgraph}
    {u : V} (huG : u ∈ G.verts) (hC₁ : IsComponentOf C₁ (G.deleteVerts {u})) :
    IsSeparation G (insert u C₁.verts) (G.verts \ C₁.verts) := by
  have hC₁_sub : C₁.verts ⊆ G.verts :=
    (hC₁.le.trans Subgraph.deleteVerts_le).1
  have hu_notC₁ : u ∉ C₁.verts := fun huC₁ ↦ (hC₁.le.1 huC₁).2 (Set.mem_singleton u)
  refine ⟨Set.insert_subset huG hC₁_sub, Set.sdiff_subset, ?_, ?_⟩
  · ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rintro ((rfl | hxC₁) | ⟨hxG, _⟩)
      · exact huG
      · exact hC₁_sub hxC₁
      · exact hxG
    · intro hxG
      by_cases hxC₁ : x ∈ C₁.verts
      · exact Or.inl (Or.inr hxC₁)
      · exact Or.inr ⟨hxG, hxC₁⟩
  · intro x y hx hy hadjG
    have hxu : x ≠ u := fun h ↦ hx.2 ⟨h ▸ huG, h ▸ hu_notC₁⟩
    have hxC₁ : x ∈ C₁.verts :=
      (Set.mem_insert_iff.1 hx.1).resolve_left hxu
    have hyG : y ∈ G.verts := hy.1.1
    have hy_notC₁ : y ∉ C₁.verts := hy.1.2
    have hyu : y ≠ u := fun h ↦ hy.2 (Set.mem_insert_iff.2 (Or.inl h))
    let H := G.deleteVerts {u}
    have hxH : x ∈ H.verts := hC₁.le.1 hxC₁
    have hyH : y ∈ H.verts := ⟨hyG, hyu⟩
    have hadjH : H.Adj x y := ⟨hxH, hyH, hadjG⟩
    obtain ⟨c₁, rfl⟩ := isComponentOf_iff_exists_connectedComponent.1 hC₁
    obtain ⟨⟨x', hx'⟩, hx'_c₁, hxx'⟩ := hxC₁
    subst hxx'
    have hy_c₁ : H.coe.connectedComponentMk ⟨y, hyH⟩ = c₁ := by
      rw [← hx'_c₁]
      exact ConnectedComponent.eq.2 ⟨.cons hadjH.symm .nil⟩
    exact hy_notC₁ ⟨⟨y, hyH⟩, hy_c₁, rfl⟩

/-- If `(A, B)` is a separation of `G` with `A ∩ B ⊆ {u}` and `u ∈ A`, then any walk `w` in `G` from
`x ∈ A` to `u` has a subwalk from `x` to `u` contained in `G.induce A`. -/
private lemma exists_walk_induce_of_isSeparation_inter_singleton
    {G : (⊤ : SimpleGraph V).Subgraph} {A B : Set V} {u x y : V}
    (hsep : IsSeparation G A B) (hinter : A ∩ B ⊆ {u})
    (w : (⊤ : SimpleGraph V).Walk x y) (hwG : w.toSubgraph ≤ G)
    (hxA : x ∈ A) (hyu : y = u) :
    ∃ p : (⊤ : SimpleGraph V).Walk x u,
      p.toSubgraph ≤ w.toSubgraph ∧ p.toSubgraph ≤ G.induce A := by
  induction w with
  | @nil a =>
    subst hyu
    exact ⟨.nil, le_rfl, by simp [hxA]⟩
  | @cons a d y hadj rest ih =>
    by_cases hau : a = u
    · subst hau
      refine ⟨.nil, ?_, by simp [hxA]⟩
      have ha_mem : a ∈ (Walk.cons hadj rest).toSubgraph.verts := by simp
      exact ⟨fun z hz ↦ by simp at hz; subst hz; exact ha_mem, fun z₁ z₂ h ↦ by simp at h⟩
    · rw [Walk.toSubgraph, sup_le_iff] at hwG
      have hadjG : G.Adj a d := hwG.1.2 (by simp)
      have ha_notB : a ∉ B := fun haB ↦ hau (Set.mem_singleton_iff.1 (hinter ⟨hxA, haB⟩))
      have hdA : d ∈ A := by
        have hdG : d ∈ G.verts := hadjG.snd_mem
        rw [← hsep.union_eq] at hdG
        rcases hdG with hdA | hdB
        · exact hdA
        · by_cases hdA : d ∈ A
          · exact hdA
          · exact absurd hadjG (hsep.not_adj ⟨hxA, ha_notB⟩ ⟨hdB, hdA⟩)
      obtain ⟨p, hp_sub, hp_ind⟩ := ih hwG.2 hdA hyu
      have hadj_ind : (G.induce A).Adj a d := ⟨hxA, hdA, hadjG⟩
      refine ⟨.cons hadj p, ?_, ?_⟩
      · rw [Walk.toSubgraph, Walk.toSubgraph]
        exact sup_le_sup_left hp_sub _
      · rw [Walk.toSubgraph]
        exact sup_le (subgraphOfAdj_le_of_adj _ hadj_ind) hp_ind

/-- If `(A, B)` is a separation of a connected graph `G` with `A ∩ B ⊆ {u}` and `u ∈ A`, then
`(G.induce A).Connected`. -/
private lemma connected_induce_of_isSeparation_inter_singleton
    {G : (⊤ : SimpleGraph V).Subgraph} {A B : Set V} {u : V}
    (hG_conn : G.Connected) (hsep : IsSeparation G A B) (huA : u ∈ A)
    (hinter : A ∩ B ⊆ {u}) :
    (G.induce A).Connected := by
  rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
  have huG : u ∈ G.verts := hsep.subset_left huA
  refine ⟨⟨u, huA⟩, fun {x y} hx hy ↦ ?_⟩
  obtain ⟨wx, hwx⟩ :=
    ((Subgraph.connected_iff_forall_exists_walk_subgraph G).1 hG_conn).2
      (hsep.subset_left hx) huG
  obtain ⟨wy, hwy⟩ :=
    ((Subgraph.connected_iff_forall_exists_walk_subgraph G).1 hG_conn).2
      (hsep.subset_left hy) huG
  obtain ⟨px, _, hpx⟩ :=
    exists_walk_induce_of_isSeparation_inter_singleton hsep hinter wx hwx hx rfl
  obtain ⟨py, _, hpy⟩ :=
    exists_walk_induce_of_isSeparation_inter_singleton hsep hinter wy hwy hy rfl
  refine ⟨px.append py.reverse, ?_⟩
  rw [Walk.toSubgraph_append, Walk.toSubgraph_reverse]
  exact sup_le hpx hpy

private lemma connected_induce_union_of_inter_nonempty {G : (⊤ : SimpleGraph V).Subgraph}
    {A B : Set V} (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    (hinter : (A ∩ B).Nonempty) :
    (G.induce (A ∪ B)).Connected := by
  have hsup_conn : (G.induce A ⊔ G.induce B).Connected :=
    connected_sup_of_inter_nonempty hA hB hinter
  have hle : G.induce A ⊔ G.induce B ≤ G.induce (A ∪ B) := by
    refine sup_le ?_ ?_
    · exact ⟨Set.subset_union_left, fun x y h ↦
        ⟨Set.subset_union_left h.1, Set.subset_union_left h.2.1, h.2.2⟩⟩
    · exact ⟨Set.subset_union_right, fun x y h ↦
        ⟨Set.subset_union_right h.1, Set.subset_union_right h.2.1, h.2.2⟩⟩
  rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
  obtain ⟨v₀, hv₀⟩ := hsup_conn.nonempty
  refine ⟨⟨v₀, hle.1 hv₀⟩, fun {x y} hx hy ↦ ?_⟩
  have hx' : x ∈ (G.induce A ⊔ G.induce B).verts := hx
  have hy' : y ∈ (G.induce A ⊔ G.induce B).verts := hy
  obtain ⟨p, hp⟩ :=
    ((Subgraph.connected_iff_forall_exists_walk_subgraph _).1 hsup_conn).2 hx' hy'
  exact ⟨p, hp.trans hle⟩

/-- Case 1 of Theorem (6.2) (page 103): when `G` is connected but not 2-connected, Theorem (6.2)
reduces to a smaller induced subgraph `G₁ = G | ({u} ∪ V₁)` with modified weight `w₁`. -/
private lemma theorem_6_2_not_twoConnected {G : (⊤ : SimpleGraph V).Subgraph} {k : ℕ}
    (ih : ∀ {G' : (⊤ : SimpleGraph V).Subgraph} (w' : V → ℕ),
      G'.verts.Finite → G'.verts.ncard < G.verts.ncard → G'.Connected →
      k ≤ (weightSum w' G'.verts + 2) / 3 → Cond62_i G' w' k ∨ Cond62_ii G' w' k)
    (hG_fin : G.verts.Finite) (hG_conn : G.Connected) (w : V → ℕ)
    (hk_le : k ≤ (weightSum w G.verts + 2) / 3)
    (hnot2 : ¬ IsTwoConnected G) :
    Cond62_i G w k ∨ Cond62_ii G w k := by
  classical
  have hex_u : ∃ u ∈ G.verts, ¬ (G.deleteVerts {u}).Preconnected := by
    by_contra! hall
    exact hnot2 ⟨hG_conn, hall⟩
  obtain ⟨u, huG, hnot_pre⟩ := hex_u
  let H := G.deleteVerts {u}
  by_cases hall_lt : ∀ C : (⊤ : SimpleGraph V).Subgraph,
      IsComponentOf C H → weightSum w C.verts < k
  · exact Or.inr ⟨u, huG, hall_lt⟩
  · push Not at hall_lt
    obtain ⟨C₁, hC₁_comp, hC₁_ge⟩ := hall_lt
    let V₁ := C₁.verts
    let R := G.verts \ V₁
    have hC₁_H : C₁ ≤ H := hC₁_comp.le
    have hV₁_H : V₁ ⊆ H.verts := hC₁_H.1
    have hV₁_G : V₁ ⊆ G.verts := (hC₁_H.trans Subgraph.deleteVerts_le).1
    have hu_notV₁ : u ∉ V₁ := fun huV₁ ↦ (hV₁_H huV₁).2 (Set.mem_singleton u)
    have huR : u ∈ R := ⟨huG, hu_notV₁⟩
    have hsep : IsSeparation G (insert u V₁) R :=
      isSeparation_component_deleteVerts_singleton huG hC₁_comp
    have hinter_sub : (insert u V₁) ∩ R ⊆ {u} := by
      rintro x ⟨rfl | hxV₁, _, hxnotV₁⟩
      · exact Set.mem_singleton x
      · exact absurd hxV₁ hxnotV₁
    have hG₁_conn : (G.induce (insert u V₁)).Connected :=
      connected_induce_of_isSeparation_inter_singleton hG_conn hsep
        (Set.mem_insert u V₁) hinter_sub
    have hR_conn : (G.induce R).Connected :=
      connected_induce_of_isSeparation_inter_singleton hG_conn hsep.symm
        huR (by rw [Set.inter_comm]; exact hinter_sub)
    have hex_outside : ∃ z₀ ∈ H.verts, z₀ ∉ V₁ := by
      by_contra! hsub
      apply hnot_pre
      rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
      intro x y hx hy
      obtain ⟨p, hp⟩ :=
        ((Subgraph.connected_iff_forall_exists_walk_subgraph C₁).1 hC₁_comp.connected).2
          (hsub x hx) (hsub y hy)
      exact ⟨p, hp.trans hC₁_H⟩
    obtain ⟨z₀, hz₀H, hz₀_notV₁⟩ := hex_outside
    have hz₀G : z₀ ∈ G.verts := hz₀H.1
    have hz₀_ne_u : z₀ ≠ u := hz₀H.2
    let G₁ := G.induce (insert u V₁)
    have hG₁_fin : G₁.verts.Finite := hG_fin.subset hsep.subset_left
    have hG₁_lt : G₁.verts.ncard < G.verts.ncard := by
      apply Set.ncard_lt_ncard _ hG_fin
      refine ⟨hsep.subset_left, fun hG_sub ↦ ?_⟩
      rcases Set.mem_insert_iff.1 (hG_sub hz₀G) with rfl | hz₀V₁
      · exact hz₀_ne_u rfl
      · exact hz₀_notV₁ hz₀V₁
    let w₁ : V → ℕ := fun x ↦ if x = u then weightSum w R else w x
    have hw₁_V₁ : ∀ X ⊆ V₁, weightSum w₁ X = weightSum w X := by
      intro X hX
      have hX_fin : X.Finite := hG_fin.subset (hX.trans hV₁_G)
      rw [weightSum_eq_sum w₁ hX_fin, weightSum_eq_sum w hX_fin]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      have hxu : x ≠ u := fun h ↦ hu_notV₁ (h ▸ hX (hX_fin.mem_toFinset.1 hx))
      simp [w₁, hxu]
    have hw₁_insert : ∀ X ⊆ V₁, weightSum w₁ (insert u X) = weightSum w (X ∪ R) := by
      intro X hX
      have hX_fin : X.Finite := hG_fin.subset (hX.trans hV₁_G)
      have hR_fin : R.Finite := hG_fin.subset Set.sdiff_subset
      have hu_notX : u ∉ X := fun huX ↦ hu_notV₁ (hX huX)
      have hdisj_uX : Disjoint ({u} : Set V) X := Set.disjoint_singleton_left.2 hu_notX
      have hdisj_XR : Disjoint X R :=
        Set.disjoint_left.2 fun x hxX hxR ↦ hxR.2 (hX hxX)
      have hins_eq : insert u X = {u} ∪ X := Set.singleton_union.symm
      rw [hins_eq, weightSum_union_disjoint w₁ (Set.finite_singleton u) hX_fin hdisj_uX,
        weightSum_singleton, hw₁_V₁ X hX, weightSum_union_disjoint w hX_fin hR_fin hdisj_XR]
      simp [w₁, Nat.add_comm]
    have hw₁_total : weightSum w₁ G₁.verts = weightSum w G.verts := by
      change weightSum w₁ (insert u V₁) = weightSum w G.verts
      rw [hw₁_insert V₁ Set.Subset.rfl]
      congr 1
      exact Set.union_sdiff_cancel hV₁_G
    have hk_le₁ : k ≤ (weightSum w₁ G₁.verts + 2) / 3 := by
      rwa [hw₁_total]
    rcases ih w₁ hG₁_fin hG₁_lt hG₁_conn hk_le₁ with h1 | h2
    · obtain ⟨U₁, U₂, hU₁_sub, hU₂_sub, hdisj_U, hU₁_conn, hU₂_conn, hwU₁, hwU₂⟩ := h1
      have hind_eq : ∀ U ⊆ G₁.verts, G₁.induce U = G.induce U := by
        intro U hU
        ext x y
        · rfl
        · simp only [Subgraph.induce_adj]
          exact ⟨fun ⟨hx, hy, _, _, hadj⟩ ↦ ⟨hx, hy, hadj⟩,
            fun ⟨hx, hy, hadj⟩ ↦ ⟨hx, hy, hU hx, hU hy, hadj⟩⟩
      rw [hind_eq U₁ hU₁_sub] at hU₁_conn
      rw [hind_eq U₂ hU₂_sub] at hU₂_conn
      have hexpand : ∀ {A B : Set V}, A ⊆ insert u V₁ → B ⊆ insert u V₁ → Disjoint A B →
          u ∈ A → (G.induce A).Connected → (G.induce B).Connected →
          k ≤ weightSum w₁ A → k ≤ weightSum w₁ B → Cond62_i G w k := by
        intro A B hA hB hdisjAB huA hconnA hconnB hwA hwB
        have hu_notB : u ∉ B := Set.disjoint_left.1 hdisjAB huA
        have hB_V₁ : B ⊆ V₁ := fun x hxB ↦
          (Set.mem_insert_iff.1 (hB hxB)).resolve_left (fun hxu ↦ hu_notB (hxu ▸ hxB))
        have hA_diff_V₁ : A \ {u} ⊆ V₁ := fun x hx ↦
          (Set.mem_insert_iff.1 (hA hx.1)).resolve_left hx.2
        refine ⟨A ∪ R, B, Set.union_subset (hA.trans hsep.subset_left) Set.sdiff_subset,
          hB_V₁.trans hV₁_G, ?_, ?_, hconnB, ?_, ?_⟩
        · rw [Set.disjoint_left]
          rintro x (hxA | hxR) hxB
          · exact Set.disjoint_left.1 hdisjAB hxA hxB
          · exact hxR.2 (hB_V₁ hxB)
        · exact connected_induce_union_of_inter_nonempty hconnA hR_conn ⟨u, huA, huR⟩
        · have hA_eq : insert u (A \ {u}) = A := Set.insert_sdiff_self_of_mem huA
          have hAR_eq : (A \ {u}) ∪ R = A ∪ R := by
            ext x
            simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
            refine ⟨?_, ?_⟩
            · rintro (⟨hxA, _⟩ | hxR)
              · exact Or.inl hxA
              · exact Or.inr hxR
            · rintro (hxA | hxR)
              · by_cases hxu : x = u
                · exact Or.inr (hxu ▸ huR)
                · exact Or.inl ⟨hxA, hxu⟩
              · exact Or.inr hxR
          have hw_eq := hw₁_insert (A \ {u}) hA_diff_V₁
          rw [hA_eq, hAR_eq] at hw_eq
          omega
        · rw [← hw₁_V₁ B hB_V₁]
          exact hwB
      by_cases huU₁ : u ∈ U₁
      · exact Or.inl (hexpand hU₁_sub hU₂_sub hdisj_U huU₁ hU₁_conn hU₂_conn hwU₁ hwU₂)
      · by_cases huU₂ : u ∈ U₂
        · obtain ⟨W₁, W₂, hW₁, hW₂, hdW, hcW₁, hcW₂, hwW₁, hwW₂⟩ :=
            hexpand hU₂_sub hU₁_sub hdisj_U.symm huU₂ hU₂_conn hU₁_conn hwU₂ hwU₁
          exact Or.inl ⟨W₂, W₁, hW₂, hW₁, hdW.symm, hcW₂, hcW₁, hwW₂, hwW₁⟩
        · have hU₁_V₁ : U₁ ⊆ V₁ := fun x hx ↦
            (Set.mem_insert_iff.1 (hU₁_sub hx)).resolve_left (fun hxu ↦ huU₁ (hxu ▸ hx))
          have hU₂_V₁ : U₂ ⊆ V₁ := fun x hx ↦
            (Set.mem_insert_iff.1 (hU₂_sub hx)).resolve_left (fun hxu ↦ huU₂ (hxu ▸ hx))
          refine Or.inl ⟨U₁, U₂, hU₁_V₁.trans hV₁_G, hU₂_V₁.trans hV₁_G, hdisj_U,
            hU₁_conn, hU₂_conn, ?_, ?_⟩
          · rwa [← hw₁_V₁ U₁ hU₁_V₁]
          · rwa [← hw₁_V₁ U₂ hU₂_V₁]
    · obtain ⟨v, hvG₁, hv_comp⟩ := h2
      have hvu : v ≠ u := by
        intro hvu
        subst hvu
        have hC₁_sub_G₁u : C₁ ≤ G₁.deleteVerts {v} := by
          refine ⟨fun x hx ↦ ⟨Set.mem_insert_of_mem v hx, (hV₁_H hx).2⟩, ?_⟩
          intro x y hadj
          exact ⟨⟨Set.mem_insert_of_mem v hadj.fst_mem, (hV₁_H hadj.fst_mem).2⟩,
            ⟨Set.mem_insert_of_mem v hadj.snd_mem, (hV₁_H hadj.snd_mem).2⟩,
            Set.mem_insert_of_mem v hadj.fst_mem,
            Set.mem_insert_of_mem v hadj.snd_mem,
            (hC₁_H.trans Subgraph.deleteVerts_le).2 hadj⟩
        obtain ⟨x₀, hx₀C₁⟩ := hC₁_comp.connected.nonempty
        let c₀ := (G₁.deleteVerts {v}).coe.connectedComponentMk ⟨x₀, hC₁_sub_G₁u.1 hx₀C₁⟩
        have hle_c₀ :=
          le_componentSubgraph_of_preconnected hC₁_sub_G₁u hC₁_comp.connected.preconnected hx₀C₁
        have hlt_c₀ := hv_comp _ (isComponentOf_componentSubgraph (G₁.deleteVerts {v}) c₀)
        have hfin_c₀ : (componentSubgraph (G₁.deleteVerts {v}) c₀).verts.Finite :=
          hG₁_fin.subset ((componentSubgraph_le _ c₀).trans Subgraph.deleteVerts_le).1
        have hle_w := weightSum_mono w₁ hfin_c₀ hle_c₀.1
        rw [hw₁_V₁ V₁ Set.Subset.rfl] at hle_w
        exact absurd (hC₁_ge.trans hle_w) (not_le_of_gt hlt_c₀)
      have hvV₁ : v ∈ V₁ := (Set.mem_insert_iff.1 hvG₁).resolve_left hvu
      have hvG : v ∈ G.verts := hV₁_G hvV₁
      refine Or.inr ⟨v, hvG, fun C hC ↦ ?_⟩
      have hG₁v_le_Gv : G₁.deleteVerts {v} ≤ G.deleteVerts {v} := by
        refine ⟨fun x hx ↦ ⟨hsep.subset_left hx.1, hx.2⟩, ?_⟩
        intro x y hadj
        exact ⟨⟨hsep.subset_left hadj.1.1, hadj.1.2⟩,
          ⟨hsep.subset_left hadj.2.1.1, hadj.2.1.2⟩, hadj.2.2.2.2⟩
      by_cases huC : u ∈ C.verts
      · have hu_G₁v : u ∈ (G₁.deleteVerts {v}).verts :=
          ⟨Set.mem_insert u V₁, Ne.symm hvu⟩
        let c_u := (G₁.deleteVerts {v}).coe.connectedComponentMk ⟨u, hu_G₁v⟩
        let C_u := componentSubgraph (G₁.deleteVerts {v}) c_u
        have hCu_comp : IsComponentOf C_u (G₁.deleteVerts {v}) :=
          isComponentOf_componentSubgraph (G₁.deleteVerts {v}) c_u
        have hCu_lt : weightSum w₁ C_u.verts < k := hv_comp C_u hCu_comp
        have hu_Cu : u ∈ C_u.verts := ⟨⟨u, hu_G₁v⟩, rfl, rfl⟩
        have hC_sub : C.verts ⊆ (C_u.verts \ {u}) ∪ R := by
          intro x hxC
          by_cases hxR : x ∈ R
          · exact Or.inr hxR
          · left
            have hxG : x ∈ G.verts := (hC.le.trans Subgraph.deleteVerts_le).1 hxC
            have hxV₁ : x ∈ V₁ := by
              by_contra hxnotV₁
              exact hxR ⟨hxG, hxnotV₁⟩
            have hxu : x ≠ u := fun h ↦ hxR (h ▸ huR)
            obtain ⟨w_xu, hw_xu⟩ :=
              ((Subgraph.connected_iff_forall_exists_walk_subgraph C).1 hC.connected).2 hxC huC
            obtain ⟨p, hp_sub_w, hp_ind⟩ :=
              exists_walk_induce_of_isSeparation_inter_singleton hsep hinter_sub w_xu
                (hw_xu.trans (hC.le.trans Subgraph.deleteVerts_le))
                (Set.mem_insert_of_mem u hxV₁) rfl
            have hp_C : p.toSubgraph ≤ C := hp_sub_w.trans hw_xu
            have hp_G₁v : p.toSubgraph ≤ G₁.deleteVerts {v} := by
              refine ⟨fun z hzp ↦ ⟨hp_ind.1 hzp, (hC.le.1 (hp_C.1 hzp)).2⟩, ?_⟩
              intro a b hadj
              exact ⟨⟨hp_ind.1 hadj.fst_mem, (hC.le.1 (hp_C.1 hadj.fst_mem)).2⟩,
                ⟨hp_ind.1 hadj.snd_mem, (hC.le.1 (hp_C.1 hadj.snd_mem)).2⟩,
                hp_ind.2 hadj⟩
            have hp_Cu :=
              le_componentSubgraph_of_preconnected hp_G₁v p.toSubgraph_connected.preconnected
                (by simp : u ∈ p.toSubgraph.verts)
            have hx_Cu : x ∈ C_u.verts := hp_Cu.1 (by simp : x ∈ p.toSubgraph.verts)
            exact ⟨hx_Cu, hxu⟩
        have hCu_diff_V₁ : C_u.verts \ {u} ⊆ V₁ := by
          intro x hx
          have hx_in : x ∈ insert u V₁ :=
            ((hCu_comp.le.trans Subgraph.deleteVerts_le).1 hx.1)
          exact (Set.mem_insert_iff.1 hx_in).resolve_left hx.2
        have hw_Cu : weightSum w ((C_u.verts \ {u}) ∪ R) = weightSum w₁ C_u.verts := by
          have := hw₁_insert (C_u.verts \ {u}) hCu_diff_V₁
          rw [Set.insert_sdiff_self_of_mem hu_Cu] at this
          exact this.symm
        have hfin_union : ((C_u.verts \ {u}) ∪ R).Finite :=
          hG_fin.subset (Set.union_subset (hCu_diff_V₁.trans hV₁_G) Set.sdiff_subset)
        have hle_w := weightSum_mono w hfin_union hC_sub
        omega
      · have hR_Gv : G.induce R ≤ G.deleteVerts {v} :=
          induce_le_deleteVerts_singleton Set.sdiff_subset (fun hvR ↦ hvR.2 hvV₁)
        have hC_disj_R : Disjoint C.verts R := by
          rw [Set.disjoint_left]
          intro x hxC hxR
          have hR_le_C : G.induce R ≤ C := by
            let c_x := (G.deleteVerts {v}).coe.connectedComponentMk ⟨x, hC.le.1 hxC⟩
            have hC_eq : C = componentSubgraph (G.deleteVerts {v}) c_x := by
              have hle := le_componentSubgraph_of_preconnected hC.le hC.connected.preconnected hxC
              exact (hC.eq_of_le hle (componentSubgraph_le _ c_x)
                (connected_componentSubgraph _ c_x)).symm
            rw [hC_eq]
            exact le_componentSubgraph_of_preconnected hR_Gv hR_conn.preconnected hxR
          exact huC (hR_le_C.1 huR)
        have hC_V₁ : C.verts ⊆ V₁ := by
          intro x hxC
          have hxG : x ∈ G.verts := (hC.le.trans Subgraph.deleteVerts_le).1 hxC
          by_contra hxnotV₁
          exact Set.disjoint_left.1 hC_disj_R hxC ⟨hxG, hxnotV₁⟩
        have hC_G₁v : C ≤ G₁.deleteVerts {v} := by
          refine ⟨fun x hxC ↦ ⟨Set.mem_insert_of_mem u (hC_V₁ hxC), (hC.le.1 hxC).2⟩, ?_⟩
          intro x y hadj
          exact ⟨⟨Set.mem_insert_of_mem u (hC_V₁ hadj.fst_mem), (hC.le.1 hadj.fst_mem).2⟩,
            ⟨Set.mem_insert_of_mem u (hC_V₁ hadj.snd_mem), (hC.le.1 hadj.snd_mem).2⟩,
            Set.mem_insert_of_mem u (hC_V₁ hadj.fst_mem),
            Set.mem_insert_of_mem u (hC_V₁ hadj.snd_mem),
            (hC.le.trans Subgraph.deleteVerts_le).2 hadj⟩
        obtain ⟨x₀, hx₀C⟩ := hC.connected.nonempty
        let c₀ := (G₁.deleteVerts {v}).coe.connectedComponentMk ⟨x₀, hC_G₁v.1 hx₀C⟩
        let C₀ := componentSubgraph (G₁.deleteVerts {v}) c₀
        have hC_le_C₀ : C ≤ C₀ :=
          le_componentSubgraph_of_preconnected hC_G₁v hC.connected.preconnected hx₀C
        have hC₀_Gv : C₀ ≤ G.deleteVerts {v} := (componentSubgraph_le _ c₀).trans hG₁v_le_Gv
        have hC₀_eq_C : C₀ = C :=
          hC.eq_of_le hC_le_C₀ hC₀_Gv (connected_componentSubgraph _ c₀)
        have hC_comp_G₁v : IsComponentOf C (G₁.deleteVerts {v}) :=
          hC₀_eq_C ▸ isComponentOf_componentSubgraph (G₁.deleteVerts {v}) c₀
        have hlt_w₁ : weightSum w₁ C.verts < k := hv_comp C hC_comp_G₁v
        rwa [hw₁_V₁ C.verts hC_V₁] at hlt_w₁

/-! ## Case 2 of Theorem (6.2): `G` is 2-Connected -/

/-- Case 2 of Theorem (6.2) (pages 103–104): when `G` is 2-connected, apply Theorem (6.1) to get a
bipolar enumeration `v₁, …, vₙ` and choose minimal `i` with `∑_{j ≤ i} w(v_j) ≥ k`. -/
private lemma theorem_6_2_twoConnected {G : (⊤ : SimpleGraph V).Subgraph} (hG_fin : G.verts.Finite)
    (w : V → ℕ) {k : ℕ} (hk_pos : 0 < k) (hk_le : k ≤ (weightSum w G.verts + 2) / 3)
    (hG2 : IsTwoConnected G) :
    Cond62_i G w k ∨ Cond62_ii G w k := by
  classical
  obtain ⟨v, hv_inj, hv_range, hv_bipolar⟩ := theorem_6_1_simple hG_fin hG2
  let n := G.verts.ncard
  let LSet : ℕ → Set V := fun i ↦ {x | ∃ j : Fin n, j.1 < i ∧ v j = x}
  let RSet : ℕ → Set V := fun i ↦ {x | ∃ j : Fin n, i ≤ j.1 ∧ v j = x}
  have hL_sub : ∀ i, LSet i ⊆ G.verts := by
    rintro i _ ⟨j, _, rfl⟩
    rw [← hv_range]
    exact Set.mem_range_self j
  have hR_sub : ∀ i, RSet i ⊆ G.verts := by
    rintro i _ ⟨j, _, rfl⟩
    rw [← hv_range]
    exact Set.mem_range_self j
  have hLR_disj : ∀ i, Disjoint (LSet i) (RSet i) := by
    intro i
    rw [Set.disjoint_left]
    rintro _ ⟨j₁, hj₁, rfl⟩ ⟨j₂, hj₂, heq⟩
    have := hv_inj heq
    subst this
    omega
  have hLR_union : ∀ i, LSet i ∪ RSet i = G.verts := by
    intro i
    rw [← hv_range]
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_range, LSet, RSet]
    refine ⟨?_, ?_⟩
    · rintro (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) <;> exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      by_cases hj : j.1 < i
      · exact Or.inl ⟨j, hj, rfl⟩
      · exact Or.inr ⟨j, by omega, rfl⟩
  have hLR_sum : ∀ i, weightSum w (LSet i) + weightSum w (RSet i) = weightSum w G.verts := by
    intro i
    rw [← weightSum_union_disjoint w (hG_fin.subset (hL_sub i)) (hG_fin.subset (hR_sub i))
      (hLR_disj i), hLR_union i]
  have hL_zero : LSet 0 = ∅ := by
    ext x
    simp [LSet]
  have hL_n : LSet n = G.verts := by
    have hR_n : RSet n = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and, RSet]
      intro j hj
      omega
    have := hLR_union n
    rwa [hR_n, Set.union_empty] at this
  have hex_i : ∃ i : ℕ, i ≤ n ∧ k ≤ weightSum w (LSet i) := by
    refine ⟨n, le_rfl, ?_⟩
    rw [hL_n]
    omega
  let i := Nat.find hex_i
  have hi_spec : i ≤ n ∧ k ≤ weightSum w (LSet i) := Nat.find_spec hex_i
  have hi_le : i ≤ n := hi_spec.1
  have hi_ge_k : k ≤ weightSum w (LSet i) := hi_spec.2
  have hi_pos : 0 < i := by
    by_contra hi0
    have hi_eq : i = 0 := by omega
    have h0 := hi_ge_k
    rw [hi_eq, hL_zero, weightSum_empty] at h0
    omega
  by_cases hR_ge : k ≤ weightSum w (RSet i)
  · left
    have hpre := hv_bipolar i hi_le
    refine ⟨LSet i, RSet i, hL_sub i, hR_sub i, hLR_disj i,
      connected_induce_of_preconnected_of_weightSum_pos hpre.1 (lt_of_lt_of_le hk_pos hi_ge_k),
      connected_induce_of_preconnected_of_weightSum_pos hpre.2 (lt_of_lt_of_le hk_pos hR_ge),
      hi_ge_k, hR_ge⟩
  · push Not at hR_ge
    have hi_pred_lt : weightSum w (LSet (i - 1)) < k := by
      by_contra! hge
      exact Nat.find_min hex_i (by omega : i - 1 < i) ⟨by omega, hge⟩
    let j₀ : Fin n := ⟨i - 1, by omega⟩
    let u := v j₀
    have huG : u ∈ G.verts := by
      rw [← hv_range]
      exact Set.mem_range_self j₀
    have hL_succ : LSet i = insert u (LSet (i - 1)) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, LSet, u]
      refine ⟨?_, ?_⟩
      · rintro ⟨j, hj, rfl⟩
        by_cases hjeq : j.1 = i - 1
        · left
          congr 1
          exact Fin.ext hjeq
        · right
          exact ⟨j, by omega, rfl⟩
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨j₀, by dsimp [j₀]; omega, rfl⟩
        · exact ⟨j, by omega, rfl⟩
    have hu_not_pred : u ∉ LSet (i - 1) := by
      rintro ⟨j, hj, heq⟩
      have := hv_inj heq
      subst this
      simp [j₀] at hj
    have hw_Li : weightSum w (LSet i) = w u + weightSum w (LSet (i - 1)) := by
      rw [hL_succ]
      have hdisj : Disjoint ({u} : Set V) (LSet (i - 1)) :=
        Set.disjoint_singleton_left.2 hu_not_pred
      have h_eq : insert u (LSet (i - 1)) = {u} ∪ LSet (i - 1) := Set.singleton_union.symm
      rw [h_eq, weightSum_union_disjoint w (Set.finite_singleton u)
        (hG_fin.subset (hL_sub (i - 1))) hdisj, weightSum_singleton]
    have hw_total :
        weightSum w G.verts = w u + weightSum w (LSet (i - 1)) + weightSum w (RSet i) := by
      rw [← hLR_sum i, hw_Li]
    have hwu_ge : k ≤ w u := by omega
    by_cases hrest_ge : k ≤ weightSum w (G.verts \ {u})
    · left
      have hpre_del : (G.induce (G.verts \ {u})).Preconnected := by
        have hdel_eq : G.induce (G.verts \ {u}) = G.deleteVerts {u} := by
          ext x y
          · rfl
          · simp [Subgraph.deleteVerts]
        rw [hdel_eq]
        exact hG2.deleteVerts_preconnected u huG
      have hconn_u : (G.induce {u}).Connected := by
        rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
        refine ⟨⟨u, Set.mem_singleton u⟩, fun {x y} hx hy ↦ ?_⟩
        rw [Subgraph.induce_verts, Set.mem_singleton_iff] at hx hy
        subst hx hy
        exact ⟨.nil, by simp⟩
      refine ⟨{u}, G.verts \ {u}, Set.singleton_subset_iff.2 huG, Set.sdiff_subset,
        Set.disjoint_singleton_left.2 (fun h ↦ h.2 rfl), hconn_u,
        connected_induce_of_preconnected_of_weightSum_pos hpre_del (lt_of_lt_of_le hk_pos hrest_ge),
        by simpa using hwu_ge, hrest_ge⟩
    · push Not at hrest_ge
      right
      refine ⟨u, huG, fun C hC ↦ ?_⟩
      have hC_sub : C.verts ⊆ G.verts \ {u} := hC.le.1
      have hle_w := weightSum_mono w (hG_fin.subset Set.sdiff_subset) hC_sub
      omega

/-! ## Theorem (6.2) -/

/-- At least one of (i) or (ii) of Theorem (6.2) holds. -/
lemma cond62_i_or_ii {G : (⊤ : SimpleGraph V).Subgraph} (hG_fin : G.verts.Finite)
    (hG_conn : G.Connected) (w : V → ℕ) {k : ℕ} (hk_pos : 0 < k)
    (hk_le : k ≤ (weightSum w G.verts + 2) / 3) :
    Cond62_i G w k ∨ Cond62_ii G w k := by
  have hmain : ∀ (n : ℕ) (G : (⊤ : SimpleGraph V).Subgraph) (w : V → ℕ),
      G.verts.Finite → G.verts.ncard ≤ n → G.Connected →
      k ≤ (weightSum w G.verts + 2) / 3 → Cond62_i G w k ∨ Cond62_ii G w k := by
    intro n
    induction n with
    | zero =>
      intro G _ hfin hcard hconn _
      obtain ⟨v₀, hv₀⟩ := hconn.nonempty
      have hpos : 0 < G.verts.ncard := (Set.ncard_pos hfin).2 ⟨v₀, hv₀⟩
      omega
    | succ n ih =>
      intro G w hfin hcard hconn hkle
      by_cases h2 : IsTwoConnected G
      · exact theorem_6_2_twoConnected hfin w hk_pos hkle h2
      · exact theorem_6_2_not_twoConnected
          (fun {G'} w' hfin' hlt' hconn' hkle' ↦ ih G' w' hfin' (by omega) hconn' hkle')
          hfin hconn w hkle h2
  exact hmain G.verts.ncard G w hG_fin le_rfl hG_conn hk_le

/-- Graph Minors V, (6.2) (page 103):
"Let $G$ be a connected graph, let $w \colon V(G) \to \mathbf{Z}^+$ be some function, and let
$k > 0$ be an integer with $k \le (w(V(G)) + 2)/3$. Then exactly one of the following is
true:* (i) *there are disjoint subsets $V_1$, $V_2$ of $V(G)$ such that $G|V_1$, $G|V_2$ are
both connected and $w(V_1), w(V_2) \ge k$;* (ii) *there is a vertex $v$ of $G$ such that
$w(V(C)) < k$ for every component $C$ of $G \setminus v$." -/
theorem theorem_6_2_simple {G : (⊤ : SimpleGraph V).Subgraph} (hG_fin : G.verts.Finite)
    (hG_conn : G.Connected) (w : V → ℕ) {k : ℕ} (hk_pos : 0 < k)
    (hk_le : k ≤ (weightSum w G.verts + 2) / 3) :
    (Cond62_i G w k ∨ Cond62_ii G w k) ∧ ¬ (Cond62_i G w k ∧ Cond62_ii G w k) :=
  ⟨cond62_i_or_ii hG_fin hG_conn w hk_pos hk_le, not_cond62_i_and_ii hG_fin w k⟩

end

end GraphMinor.GM05
