module

public import GraphMinor.GM05.Section5

/-!
# Graph Minors V, (6.1): Bipolar Numbering of 2-Connected Graphs

This file formalizes (6.1) (page 103) of Robertson and Seymour, *Graph Minors. V. Excluding a
planar graph*, J. Combin. Theory Ser. B 41 (1986) 92–114:

- `theorem_6_1`, (6.1): If `G` is a 2-connected graph with `n` vertices, we may enumerate its
  vertices as `v₁, …, vₙ` in such a way that for `0 ≤ i ≤ n`, `G | {v₁, …, vᵢ}` and
  `G | {v_{i+1}, …, vₙ}` are both connected (preconnected when empty).

The proof builds a duplicate-free list `L` of vertices of `G` in which every vertex after the first
has a neighbor to its left (`IsLeftConnectedList G L`) and every vertex before the last has a
neighbor to its right (`IsLeftConnectedList G L.reverse`). Starting from a single edge `[s, t]`, as
long as `L` does not yet contain all vertices of `G`, 2-connectivity of `G` provides a path in a
component `C` of `G \ L` whose endpoints are adjacent to two distinct vertices `x₁ ≠ x₂` of `L`;
inserting this path into `L` between `x₁` and `x₂` preserves both properties and increases the
length of `L`.
-/

@[expose] public section

namespace GraphMinor.GM05

open SimpleGraph Graph Set Relation GM01

variable {V : Type*}

/-! ## Left-Connected Vertex Lists -/

/-- `IsLeftConnectedList G L` means that every vertex in `L` after the first is adjacent in `G` to
some vertex appearing earlier in `L`. -/
def IsLeftConnectedList (G : (⊤ : SimpleGraph V).Subgraph) (L : List V) : Prop :=
  ∀ L₁ x L₂, L = L₁ ++ x :: L₂ → L₁ ≠ [] → ∃ y ∈ L₁, G.Adj y x

private lemma isLeftConnectedList_nil (G : (⊤ : SimpleGraph V).Subgraph) :
    IsLeftConnectedList G [] := by
  intro L₁ x L₂ h _
  cases L₁ <;> simp at h

private lemma isLeftConnectedList_singleton (G : (⊤ : SimpleGraph V).Subgraph) (v : V) :
    IsLeftConnectedList G [v] := by
  intro L₁ x L₂ h hne
  rcases L₁ with _ | ⟨a, L₁⟩
  · exact absurd rfl hne
  · simp at h

private lemma isLeftConnectedList_pair {G : (⊤ : SimpleGraph V).Subgraph} {s t : V}
    (hadj : G.Adj s t) : IsLeftConnectedList G [s, t] := by
  intro L₁ x L₂ h hne
  rcases L₁ with _ | ⟨a, _ | ⟨b, L₁⟩⟩
  · exact absurd rfl hne
  · simp only [List.singleton_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl, _⟩ := h
    exact ⟨s, by simp, hadj⟩
  · simp at h

private lemma isLeftConnectedList_prefix {G : (⊤ : SimpleGraph V).Subgraph} {L₁ L₂ : List V}
    (h : IsLeftConnectedList G (L₁ ++ L₂)) : IsLeftConnectedList G L₁ := by
  intro A x B heq hne
  have hfull : L₁ ++ L₂ = A ++ x :: (B ++ L₂) := by
    rw [heq, List.append_assoc, List.cons_append]
  exact h A x (B ++ L₂) hfull hne

/-- Any list `L` in `G.verts` satisfying `IsLeftConnectedList G L` induces a preconnected subgraph
of `G`. -/
lemma preconnected_induce_of_isLeftConnectedList {G : (⊤ : SimpleGraph V).Subgraph} {L : List V}
    (hG : ∀ x ∈ L, x ∈ G.verts) (h : IsLeftConnectedList G L) :
    (G.induce {x | x ∈ L}).Preconnected := by
  induction L using List.reverseRecOn with
  | nil =>
    rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
    intro u v hu
    simp at hu
  | append_singleton L₁ z ih =>
    rcases L₁ with _ | ⟨a, L₁'⟩
    · simp only [List.nil_append]
      rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
      intro u v hu hv
      simp only [Subgraph.induce_verts, Set.mem_ofPred_eq, List.mem_singleton] at hu hv
      subst hu hv
      refine ⟨.nil, ?_⟩
      simp
    · have hL₁_ne : a :: L₁' ≠ [] := List.cons_ne_nil a L₁'
      have hG₁ : ∀ x ∈ a :: L₁', x ∈ G.verts :=
        fun x hx ↦ hG x (List.mem_append_left [z] hx)
      have hleft₁ : IsLeftConnectedList G (a :: L₁') := isLeftConnectedList_prefix h
      have hpre₁ : (G.induce {x | x ∈ a :: L₁'}).Preconnected := ih hG₁ hleft₁
      obtain ⟨y, hy_mem, hadj_yz⟩ := h (a :: L₁') z [] rfl hL₁_ne
      have hadj_ind : (G.induce {x | x ∈ a :: L₁' ++ [z]}).Adj y z :=
        ⟨List.mem_append_left [z] hy_mem, by simp, hadj_yz⟩
      have hle_left : G.induce {x | x ∈ a :: L₁'} ≤ G.induce {x | x ∈ a :: L₁' ++ [z]} :=
        ⟨fun x hx ↦ List.mem_append_left [z] hx,
         fun x w hxw ↦ ⟨List.mem_append_left [z] hxw.1, List.mem_append_left [z] hxw.2.1, hxw.2.2⟩⟩
      rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
      intro u v hu hv
      have ha_mem₁ : a ∈ (G.induce {x | x ∈ a :: L₁'}).verts := by simp
      have h_to_a : ∀ w ∈ (G.induce {x | x ∈ a :: L₁' ++ [z]}).verts,
          ∃ p : (⊤ : SimpleGraph V).Walk a w,
            p.toSubgraph ≤ G.induce {x | x ∈ a :: L₁' ++ [z]} := by
        intro w hw
        simp only [Subgraph.induce_verts, Set.mem_ofPred_eq, List.mem_append,
          List.mem_singleton] at hw
        rcases hw with hw₁ | rfl
        · obtain ⟨p, hp⟩ :=
            (Subgraph.preconnected_iff_forall_exists_walk_subgraph _).1 hpre₁ ha_mem₁ hw₁
          exact ⟨p, hp.trans hle_left⟩
        · obtain ⟨p, hp⟩ :=
            (Subgraph.preconnected_iff_forall_exists_walk_subgraph _).1 hpre₁ ha_mem₁ hy_mem
          refine ⟨p.append (.cons hadj_ind.adj_sub .nil), ?_⟩
          rw [Walk.toSubgraph_append, Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
          exact sup_le (hp.trans hle_left)
            (subgraphOfAdj_le_of_adj _ hadj_ind)
      obtain ⟨pu, hpu⟩ := h_to_a u hu
      obtain ⟨pv, hpv⟩ := h_to_a v hv
      refine ⟨pu.reverse.append pv, ?_⟩
      rw [Walk.toSubgraph_append, Walk.toSubgraph_reverse]
      exact sup_le hpu hpv

/-- Every vertex in `q.support` is either the start vertex `u₁` (when `P₁ = []`) or is adjacent in
`G` to a preceding vertex in `q.support`. -/
private lemma walk_support_left_adj {G : (⊤ : SimpleGraph V).Subgraph} {u₁ u₂ : V}
    (q : (⊤ : SimpleGraph V).Walk u₁ u₂) (hqG : q.toSubgraph ≤ G)
    {P₁ : List V} {x : V} {P₂ : List V} (heq : q.support = P₁ ++ x :: P₂) :
    (P₁ = [] ∧ x = u₁) ∨ ∃ y ∈ P₁, G.Adj y x := by
  induction q generalizing P₁ with
  | nil =>
    rcases P₁ with _ | ⟨a, P₁'⟩
    · simp only [Walk.support_nil, List.nil_append, List.cons.injEq] at heq
      exact Or.inl ⟨rfl, heq.1.symm⟩
    · simp only [Walk.support_nil, List.cons_append, List.cons.injEq] at heq
      exact absurd heq.2.symm (List.append_ne_nil_of_right_ne_nil P₁' (List.cons_ne_nil x P₂))
  | @cons a c u₂ hadj rest ih =>
    rw [Walk.toSubgraph, sup_le_iff] at hqG
    have hadjG : G.Adj a c := hqG.1.2 (by simp)
    rcases P₁ with _ | ⟨b, P₁'⟩
    · simp only [Walk.support_cons, List.nil_append, List.cons.injEq] at heq
      exact Or.inl ⟨rfl, heq.1.symm⟩
    · simp only [Walk.support_cons, List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, heq_rest⟩ := heq
      rcases ih hqG.2 heq_rest with ⟨rfl, rfl⟩ | ⟨y, hy, hadj_yx⟩
      · exact Or.inr ⟨a, by simp, hadjG⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem a hy, hadj_yx⟩

/-- Inserting the support of a walk `q : Walk u₁ u₂` in `G` between `A` and `B`, where `u₁` is
adjacent in `G` to some vertex of `A`, preserves `IsLeftConnectedList`. -/
lemma isLeftConnectedList_insert_walk {G : (⊤ : SimpleGraph V).Subgraph} {A B : List V}
    {u₁ u₂ : V} (q : (⊤ : SimpleGraph V).Walk u₁ u₂) (hqG : q.toSubgraph ≤ G)
    (hleft : IsLeftConnectedList G (A ++ B))
    (hx₁ : ∃ x₁ ∈ A, G.Adj x₁ u₁) :
    IsLeftConnectedList G (A ++ q.support ++ B) := by
  intro L₁ x L₂ heq hL₁_ne
  rw [List.append_assoc] at heq
  rcases List.append_eq_append_iff.1 heq with ⟨P', hL₁_eq, hqB_eq⟩ | ⟨A', hA_eq, hrest_eq⟩
  · rcases List.append_eq_append_iff.1 hqB_eq with ⟨B₁, hP'_eq, hB_eq⟩ | ⟨P₂, hq_eq, hL₂_eq⟩
    · have hAB : A ++ B = (A ++ B₁) ++ x :: L₂ := by
        rw [hB_eq, List.append_assoc]
      obtain ⟨x₁, hx₁A, _⟩ := hx₁
      have hAB₁_ne : A ++ B₁ ≠ [] := List.ne_nil_of_mem (List.mem_append_left _ hx₁A)
      obtain ⟨y, hy, hadj_yx⟩ := hleft (A ++ B₁) x L₂ hAB hAB₁_ne
      refine ⟨y, ?_, hadj_yx⟩
      rw [hL₁_eq, hP'_eq]
      rcases List.mem_append.1 hy with hyA | hyB₁
      · exact List.mem_append_left _ hyA
      · exact List.mem_append_right _ (List.mem_append_right _ hyB₁)
    · rcases P₂ with _ | ⟨z, P₂'⟩
      · simp only [List.append_nil] at hq_eq
        simp only [List.nil_append] at hL₂_eq
        obtain ⟨x₁, hx₁A, _⟩ := hx₁
        have hA_ne : A ≠ [] := List.ne_nil_of_mem hx₁A
        have hAB : A ++ B = A ++ x :: L₂ := by rw [← hL₂_eq]
        obtain ⟨y, hyA, hadj_yx⟩ := hleft A x L₂ hAB hA_ne
        exact ⟨y, by rw [hL₁_eq]; exact List.mem_append_left _ hyA, hadj_yx⟩
      · simp only [List.cons_append, List.cons.injEq] at hL₂_eq
        obtain ⟨rfl, _⟩ := hL₂_eq
        rcases walk_support_left_adj q hqG hq_eq with ⟨rfl, rfl⟩ | ⟨y, hyP', hadj_yx⟩
        · obtain ⟨x₁, hx₁A, hadj₁⟩ := hx₁
          exact ⟨x₁, by rw [hL₁_eq]; simpa using hx₁A, hadj₁⟩
        · exact ⟨y, by rw [hL₁_eq]; exact List.mem_append_right _ hyP', hadj_yx⟩
  · rcases A' with _ | ⟨z, A''⟩
    · simp only [List.append_nil] at hA_eq
      subst hA_eq
      simp only [List.nil_append] at hrest_eq
      have hxu₁ : x = u₁ := by
        cases q with
        | nil =>
          simp only [Walk.support_nil, List.singleton_append, List.cons.injEq] at hrest_eq
          exact hrest_eq.1
        | cons _ _ =>
          simp only [Walk.support_cons, List.cons_append, List.cons.injEq] at hrest_eq
          exact hrest_eq.1
      subst hxu₁
      exact hx₁
    · simp only [List.cons_append, List.cons.injEq] at hrest_eq
      obtain ⟨rfl, _⟩ := hrest_eq
      have hAB : A ++ B = L₁ ++ x :: (A'' ++ B) := by
        rw [hA_eq, List.append_assoc, List.cons_append]
      exact hleft L₁ x (A'' ++ B) hAB hL₁_ne

/-! ## Ear Insertion in a 2-Connected Graph -/

/-- Any list `L` containing two distinct elements `x₁ ≠ x₂` can be split as `L = A ++ B` with one of
`x₁, x₂` in `A` and the other in `B`. -/
private lemma exists_split_of_mem_ne {L : List V} {x₁ x₂ : V}
    (hx₁ : x₁ ∈ L) (hx₂ : x₂ ∈ L) (hne : x₁ ≠ x₂) :
    ∃ A B : List V, L = A ++ B ∧ ((x₁ ∈ A ∧ x₂ ∈ B) ∨ (x₂ ∈ A ∧ x₁ ∈ B)) := by
  induction L with
  | nil => nomatch hx₁
  | cons a rest ih =>
    by_cases ha₁ : a = x₁
    · subst ha₁
      have hx₂_rest : x₂ ∈ rest := (List.mem_cons.1 hx₂).resolve_left hne.symm
      exact ⟨[a], rest, rfl, Or.inl ⟨by simp, hx₂_rest⟩⟩
    · by_cases ha₂ : a = x₂
      · subst ha₂
        have hx₁_rest : x₁ ∈ rest := (List.mem_cons.1 hx₁).resolve_left hne
        exact ⟨[a], rest, rfl, Or.inr ⟨by simp, hx₁_rest⟩⟩
      · have hx₁_rest : x₁ ∈ rest := (List.mem_cons.1 hx₁).resolve_left (Ne.symm ha₁)
        have hx₂_rest : x₂ ∈ rest := (List.mem_cons.1 hx₂).resolve_left (Ne.symm ha₂)
        obtain ⟨A', B', hrest, hmem⟩ := ih hx₁_rest hx₂_rest
        refine ⟨a :: A', B', by simp [hrest], ?_⟩
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨List.mem_cons_of_mem a h1, h2⟩
        · exact Or.inr ⟨List.mem_cons_of_mem a h1, h2⟩

/-- Along a walk in `G.deleteVerts {x₁}` from `z ∈ (componentSubgraph (G.deleteVerts S) c).verts`
to `y ∈ S \ {x₁}`, there is an edge of `G` between `(componentSubgraph (G.deleteVerts S) c).verts`
and `S \ {x₁}`. -/
private lemma exists_adj_second_attachment {G : (⊤ : SimpleGraph V).Subgraph} {S : Set V}
    {x₁ : V} (c : (G.deleteVerts S).coe.ConnectedComponent)
    {z y : V} (w : (⊤ : SimpleGraph V).Walk z y) (hw : w.toSubgraph ≤ G.deleteVerts {x₁})
    (hz : z ∈ (componentSubgraph (G.deleteVerts S) c).verts) (hy : y ∈ S \ {x₁}) :
    ∃ x₂ ∈ S, x₂ ≠ x₁ ∧ ∃ u₂ ∈ (componentSubgraph (G.deleteVerts S) c).verts, G.Adj x₂ u₂ := by
  induction w with
  | @nil z =>
    obtain ⟨⟨z', hz'⟩, _, rfl⟩ := hz
    exact absurd hy.1 hz'.2
  | @cons a b y hadj rest ih =>
    rw [Walk.toSubgraph, sup_le_iff] at hw
    have hadj₁ : (G.deleteVerts {x₁}).Adj a b := hw.1.2 (by simp)
    have hadjG : G.Adj a b := (Subgraph.deleteVerts_le : G.deleteVerts {x₁} ≤ G).2 hadj₁
    have hb_ne_x₁ : b ≠ x₁ := by
      have hb_mem : b ∈ (G.deleteVerts {x₁}).verts := hadj₁.snd_mem
      simpa using hb_mem.2
    by_cases hbS : b ∈ S
    · exact ⟨b, hbS, hb_ne_x₁, a, hz, hadjG.symm⟩
    · have hbH : b ∈ (G.deleteVerts S).verts := ⟨hadjG.snd_mem, hbS⟩
      obtain ⟨⟨a', ha'H⟩, ha'c, rfl⟩ := hz
      have hadj_coe : (G.deleteVerts S).coe.Adj ⟨a', ha'H⟩ ⟨b, hbH⟩ :=
        ⟨ha'H, hbH, hadjG⟩
      have hbc : (G.deleteVerts S).coe.connectedComponentMk ⟨b, hbH⟩ = c := by
        rw [← ha'c]
        exact ConnectedComponent.eq.2 ⟨.cons hadj_coe.symm .nil⟩
      have hb_comp : b ∈ (componentSubgraph (G.deleteVerts S) c).verts :=
        ⟨⟨b, hbH⟩, hbc, rfl⟩
      exact ih hw.2 hb_comp hy

/-- Along a walk in `G` from `z ∈ (componentSubgraph (G.deleteVerts S) c).verts` to `y ∈ S`, there
is an edge of `G` between `S` and `(componentSubgraph (G.deleteVerts S) c).verts`. -/
private lemma exists_adj_first_attachment {G : (⊤ : SimpleGraph V).Subgraph} {S : Set V}
    (c : (G.deleteVerts S).coe.ConnectedComponent)
    {z y : V} (w : (⊤ : SimpleGraph V).Walk z y) (hw : w.toSubgraph ≤ G)
    (hz : z ∈ (componentSubgraph (G.deleteVerts S) c).verts) (hy : y ∈ S) :
    ∃ x₁ ∈ S, ∃ u₁ ∈ (componentSubgraph (G.deleteVerts S) c).verts, G.Adj x₁ u₁ := by
  induction w with
  | @nil z =>
    obtain ⟨⟨z', hz'⟩, _, rfl⟩ := hz
    exact absurd hy hz'.2
  | @cons a b y hadj rest ih =>
    rw [Walk.toSubgraph, sup_le_iff] at hw
    have hadjG : G.Adj a b := hw.1.2 (by simp)
    by_cases hbS : b ∈ S
    · exact ⟨b, hbS, a, hz, hadjG.symm⟩
    · have hbH : b ∈ (G.deleteVerts S).verts := ⟨hadjG.snd_mem, hbS⟩
      obtain ⟨⟨a', ha'H⟩, ha'c, rfl⟩ := hz
      have hadj_coe : (G.deleteVerts S).coe.Adj ⟨a', ha'H⟩ ⟨b, hbH⟩ :=
        ⟨ha'H, hbH, hadjG⟩
      have hbc : (G.deleteVerts S).coe.connectedComponentMk ⟨b, hbH⟩ = c := by
        rw [← ha'c]
        exact ConnectedComponent.eq.2 ⟨.cons hadj_coe.symm .nil⟩
      have hb_comp : b ∈ (componentSubgraph (G.deleteVerts S) c).verts :=
        ⟨⟨b, hbH⟩, hbc, rfl⟩
      exact ih hw.2 hb_comp hy

/-- `IsBipolarList G L` packages the invariants of our partial bipolar vertex list `L`. -/
structure IsBipolarList (G : (⊤ : SimpleGraph V).Subgraph) (L : List V) : Prop where
  nodup : L.Nodup
  subset_verts : ∀ x ∈ L, x ∈ G.verts
  left_conn : IsLeftConnectedList G L
  right_conn : IsLeftConnectedList G L.reverse

/-- If `G` is 2-connected and `L` is a bipolar list of length `≥ 2` that does not yet contain a
vertex `v₀ ∈ G.verts`, then `L` can be extended to a strictly longer bipolar list `L'`. -/
private lemma exists_longer_bipolarList {G : (⊤ : SimpleGraph V).Subgraph}
    (hG2 : IsTwoConnected G) {L : List V} (hL : IsBipolarList G L)
    (hlen : 2 ≤ L.length) {v₀ : V} (hv₀G : v₀ ∈ G.verts) (hv₀L : v₀ ∉ L) :
    ∃ L' : List V, IsBipolarList G L' ∧ L.length < L'.length := by
  let S : Set V := {x | x ∈ L}
  have hv₀H : v₀ ∈ (G.deleteVerts S).verts := ⟨hv₀G, hv₀L⟩
  let c := (G.deleteVerts S).coe.connectedComponentMk ⟨v₀, hv₀H⟩
  let C := componentSubgraph (G.deleteVerts S) c
  have hC_le_H : C ≤ G.deleteVerts S := componentSubgraph_le (G.deleteVerts S) c
  have hC_le : C ≤ G := hC_le_H.trans Subgraph.deleteVerts_le
  have hC_conn : C.Connected := connected_componentSubgraph (G.deleteVerts S) c
  have hv₀C : v₀ ∈ C.verts := ⟨⟨v₀, hv₀H⟩, rfl, rfl⟩
  rcases L with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp at hlen
  · simp at hlen
  · obtain ⟨w₁, hw₁⟩ :=
      ((Subgraph.connected_iff_forall_exists_walk_subgraph G).1 hG2.connected).2
        hv₀G (hL.subset_verts a (by simp))
    obtain ⟨x₁, hx₁S, u₁, hu₁C, hadj₁⟩ :=
      exists_adj_first_attachment c w₁ hw₁ hv₀C (by simp [S])
    have hab_ne : a ≠ b := fun h ↦ (List.nodup_cons.1 hL.nodup).1 (h ▸ List.mem_cons_self)
    have hex_other : ∃ z ∈ a :: b :: rest, z ≠ x₁ := by
      by_cases hx₁a : x₁ = a
      · exact ⟨b, by simp, hx₁a ▸ hab_ne.symm⟩
      · exact ⟨a, by simp, Ne.symm hx₁a⟩
    obtain ⟨z, hzL, hz_ne⟩ := hex_other
    have hu₁_G₁ : u₁ ∈ (G.deleteVerts {x₁}).verts :=
      ⟨hC_le.1 hu₁C, fun h ↦ (hC_le_H.1 hu₁C).2 ((Set.mem_singleton_iff.1 h) ▸ hx₁S)⟩
    have hz_G₁ : z ∈ (G.deleteVerts {x₁}).verts :=
      ⟨hL.subset_verts z hzL, hz_ne⟩
    have hpre₁ := hG2.deleteVerts_preconnected x₁ (hL.subset_verts x₁ hx₁S)
    obtain ⟨w₂, hw₂⟩ :=
      (Subgraph.preconnected_iff_forall_exists_walk_subgraph (G.deleteVerts {x₁})).1
        hpre₁ hu₁_G₁ hz_G₁
    obtain ⟨x₂, hx₂S, hx₂_ne_x₁, u₂, hu₂C, hadj₂⟩ :=
      exists_adj_second_attachment c w₂ hw₂ hu₁C ⟨hzL, hz_ne⟩
    obtain ⟨A, B, hAB, hsplit⟩ := exists_split_of_mem_ne hx₁S hx₂S hx₂_ne_x₁.symm
    have hinsert : ∀ {y₁ y₂ w_start w_end : V},
        y₁ ∈ A → y₂ ∈ B → w_start ∈ C.verts → w_end ∈ C.verts →
        G.Adj y₁ w_start → G.Adj y₂ w_end →
        ∃ L' : List V, IsBipolarList G L' ∧ (a :: b :: rest).length < L'.length := by
      intro y₁ y₂ w_start w_end hy₁A hy₂B hwsC hweC hadj_s hadj_e
      obtain ⟨w_C, hw_C⟩ :=
        ((Subgraph.connected_iff_forall_exists_walk_subgraph C).1 hC_conn).2 hwsC hweC
      let P_C : GM01.Path V := GM01.Path.ofWalk w_C
      have hPC_le_C : P_C.walk.toSubgraph ≤ C :=
        (GM01.Path.ofWalk_toSubgraph_le w_C).trans hw_C
      have hPC_le_G : P_C.walk.toSubgraph ≤ G := hPC_le_C.trans hC_le
      let L' := A ++ P_C.walk.support ++ B
      have hPC_disj : ∀ x ∈ P_C.walk.support, x ∉ a :: b :: rest := by
        intro x hx
        have hxC : x ∈ C.verts := hPC_le_C.1 (P_C.walk.mem_verts_toSubgraph.2 hx)
        exact (hC_le_H.1 hxC).2
      have hnodup' : L'.Nodup := by
        have hAB_nodup : (A ++ B).Nodup := hAB ▸ hL.nodup
        rw [List.nodup_append] at hAB_nodup
        obtain ⟨hA_nd, hB_nd, hAB_disj⟩ := hAB_nodup
        dsimp [L']
        rw [List.append_assoc, List.nodup_append]
        refine ⟨hA_nd, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨P_C.isPath.support_nodup, hB_nd, ?_⟩
          intro x hxP y hyB hxy
          subst hxy
          exact hPC_disj x hxP (hAB ▸ List.mem_append_right A hyB)
        · intro x hxA y hyPB hxy
          subst hxy
          rcases List.mem_append.1 hyPB with hxP | hxB
          · exact hPC_disj x hxP (hAB ▸ List.mem_append_left B hxA)
          · exact hAB_disj x hxA x hxB rfl
      have hsub' : ∀ x ∈ L', x ∈ G.verts := by
        intro x hx
        dsimp [L'] at hx
        rcases List.mem_append.1 hx with hxAP | hxB
        · rcases List.mem_append.1 hxAP with hxA | hxP
          · exact hL.subset_verts x (hAB ▸ List.mem_append_left B hxA)
          · exact hPC_le_G.1 (P_C.walk.mem_verts_toSubgraph.2 hxP)
        · exact hL.subset_verts x (hAB ▸ List.mem_append_right A hxB)
      have hleft' : IsLeftConnectedList G L' :=
        isLeftConnectedList_insert_walk P_C.walk hPC_le_G (hAB ▸ hL.left_conn)
          ⟨y₁, hy₁A, hadj_s⟩
      have hright' : IsLeftConnectedList G L'.reverse := by
        have hrev_eq : L'.reverse = B.reverse ++ P_C.walk.reverse.support ++ A.reverse := by
          simp [L', Walk.support_reverse, List.append_assoc]
        rw [hrev_eq]
        have hrev_AB : B.reverse ++ A.reverse = (a :: b :: rest).reverse := by
          rw [hAB, List.reverse_append]
        have hPC_rev_le : P_C.walk.reverse.toSubgraph ≤ G := by
          rw [Walk.toSubgraph_reverse]
          exact hPC_le_G
        exact isLeftConnectedList_insert_walk P_C.walk.reverse hPC_rev_le
          (hrev_AB ▸ hL.right_conn) ⟨y₂, List.mem_reverse.2 hy₂B, hadj_e⟩
      have hlen' : (a :: b :: rest).length < L'.length := by
        have hpos : 0 < P_C.walk.support.length :=
          List.length_pos_of_mem P_C.walk.start_mem_support
        have hAB_len : (a :: b :: rest).length = A.length + B.length := by
          rw [hAB, List.length_append]
        change (a :: b :: rest).length < (A ++ P_C.walk.support ++ B).length
        rw [List.length_append, List.length_append, hAB_len]
        omega
      exact ⟨L', ⟨hnodup', hsub', hleft', hright'⟩, hlen'⟩
    rcases hsplit with ⟨hx₁A, hx₂B⟩ | ⟨hx₂A, hx₁B⟩
    · exact hinsert hx₁A hx₂B hu₁C hu₂C hadj₁ hadj₂
    · exact hinsert hx₂A hx₁B hu₂C hu₁C hadj₂ hadj₁

private lemma ncard_mem_list_eq_length [DecidableEq V] {L : List V} (hnd : L.Nodup) :
    {x | x ∈ L}.ncard = L.length := by
  have h1 : {x | x ∈ L} = (L.toFinset : Set V) := by
    ext x
    simp
  rw [h1, Set.ncard_coe_finset, List.card_toFinset, List.dedup_eq_self.2 hnd]

/-- Every finite 2-connected graph `G` has a complete bipolar list `L` with `{x | x ∈ L} = G.verts`. -/
lemma exists_full_bipolarList {G : (⊤ : SimpleGraph V).Subgraph} (hG_fin : G.verts.Finite)
    (hG2 : IsTwoConnected G) :
    ∃ L : List V, IsBipolarList G L ∧ {x | x ∈ L} = G.verts := by
  classical
  by_cases hcard : G.verts.ncard ≤ 1
  · obtain ⟨v₀, hv₀G⟩ := hG2.connected.nonempty
    have heq_single : G.verts = {v₀} := by
      obtain ⟨u, hu⟩ := (Set.ncard_le_one_iff_eq hG_fin).1 hcard |> fun h ↦
        h.resolve_left (Set.nonempty_iff_ne_empty.1 ⟨v₀, hv₀G⟩)
      have hv₀u : v₀ = u := Set.mem_singleton_iff.1 (hu ▸ hv₀G)
      exact hv₀u ▸ hu
    refine ⟨[v₀], ⟨List.nodup_singleton v₀, ?_, isLeftConnectedList_singleton G v₀,
      isLeftConnectedList_singleton G v₀⟩, ?_⟩
    · intro x hx
      rw [List.mem_singleton] at hx
      exact hx ▸ hv₀G
    · ext x
      simp [heq_single]
  · push Not at hcard
    obtain ⟨s, hsG⟩ := hG2.connected.nonempty
    have hex_t : ∃ t ∈ G.verts, t ≠ s := by
      by_contra! hall
      have hsub : G.verts ⊆ {s} := fun x hx ↦ Set.mem_singleton_iff.2 (hall x hx)
      have hle1 : G.verts.ncard ≤ 1 :=
        (Set.ncard_le_ncard hsub (Set.finite_singleton s)).trans (by simp)
      omega
    obtain ⟨t₀, ht₀G, ht₀_ne⟩ := hex_t
    obtain ⟨w, hw⟩ :=
      ((Subgraph.connected_iff_forall_exists_walk_subgraph G).1 hG2.connected).2 hsG ht₀G
    have hex_adj : ∃ t, G.Adj s t := by
      cases w with
      | nil => exact absurd rfl ht₀_ne
      | @cons _ t _ _ _ =>
        rw [Walk.toSubgraph, sup_le_iff] at hw
        exact ⟨t, hw.1.2 (by simp)⟩
    obtain ⟨t, hadj_st⟩ := hex_adj
    have hL₀ : IsBipolarList G [s, t] :=
      { nodup := by simp [hadj_st.ne]
        subset_verts := by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hadj_st.fst_mem
          · exact hadj_st.snd_mem
        left_conn := isLeftConnectedList_pair hadj_st
        right_conn := isLeftConnectedList_pair hadj_st.symm }
    have hstep : ∀ k : ℕ, ∃ L : List V,
        IsBipolarList G L ∧ 2 ≤ L.length ∧ (G.verts.ncard - L.length ≤ G.verts.ncard - 2 - k) := by
      intro k
      induction k with
      | zero => exact ⟨[s, t], hL₀, le_rfl, by simp⟩
      | succ k ih =>
        obtain ⟨L, hL, hlen, hrem⟩ := ih
        by_cases hfull : ∀ v ∈ G.verts, v ∈ L
        · refine ⟨L, hL, hlen, ?_⟩
          have hsub : G.verts ⊆ {x | x ∈ L} := hfull
          have hcard_le : G.verts.ncard ≤ L.length := by
            have := Set.ncard_le_ncard hsub (List.finite_toSet L)
            rwa [ncard_mem_list_eq_length hL.nodup] at this
          omega
        · push Not at hfull
          obtain ⟨v₀, hv₀G, hv₀L⟩ := hfull
          obtain ⟨L', hL', hlen_lt⟩ := exists_longer_bipolarList hG2 hL hlen hv₀G hv₀L
          exact ⟨L', hL', by omega, by omega⟩
    obtain ⟨L, hL, _, hrem⟩ := hstep (G.verts.ncard - 2)
    have hlen_ge : G.verts.ncard ≤ L.length := by omega
    have hset_eq : {x | x ∈ L} = G.verts := by
      have hsub : {x | x ∈ L} ⊆ G.verts := hL.subset_verts
      have hcard_ge : G.verts.ncard ≤ {x | x ∈ L}.ncard := by
        rwa [ncard_mem_list_eq_length hL.nodup]
      exact Set.eq_of_subset_of_ncard_le hsub hcard_ge hG_fin
    exact ⟨L, hL, hset_eq⟩

/-! ## Theorem (6.1) -/

/-- Graph Minors V, (6.1) (page 103):
"If $G$ is a 2-connected graph with $n$ vertices, we may enumerate its vertices as $v_1, ...,
v_n$ in such a way that for $0 \le i \le n$, $G|\{v_1, ..., v_i\}$, $G|\{v_{i+1}, ...,
v_n\}$ are both connected." -/
theorem theorem_6_1_simple {G : (⊤ : SimpleGraph V).Subgraph} (hG_fin : G.verts.Finite)
    (hG2 : IsTwoConnected G) :
    ∃ v : Fin G.verts.ncard → V,
      Function.Injective v ∧
      Set.range v = G.verts ∧
      ∀ i : ℕ, i ≤ G.verts.ncard →
        (G.induce {x | ∃ j : Fin G.verts.ncard, j.1 < i ∧ v j = x}).Preconnected ∧
        (G.induce {x | ∃ j : Fin G.verts.ncard, i ≤ j.1 ∧ v j = x}).Preconnected := by
  classical
  obtain ⟨L, hL, hset_eq⟩ := exists_full_bipolarList hG_fin hG2
  have hlen : L.length = G.verts.ncard := by
    rw [← ncard_mem_list_eq_length hL.nodup, hset_eq]
  let v : Fin G.verts.ncard → V := fun j ↦ L.get (j.cast hlen.symm)
  have hv_inj : Function.Injective v := by
    intro j₁ j₂ heq
    have hidx := (List.Nodup.get_inj_iff hL.nodup).1 heq
    have hval : (j₁.cast hlen.symm).1 = (j₂.cast hlen.symm).1 := congrArg Fin.val hidx
    exact Fin.ext hval
  have hv_range : Set.range v = G.verts := by
    ext x
    have hmem : x ∈ G.verts ↔ x ∈ L := by
      rw [← hset_eq]
      rfl
    rw [hmem]
    simp only [Set.mem_range, v]
    refine ⟨?_, ?_⟩
    · rintro ⟨j, rfl⟩
      exact List.get_mem L _
    · intro hx
      obtain ⟨k, hk⟩ := List.mem_iff_get.1 hx
      exact ⟨k.cast hlen, hk⟩
  refine ⟨v, hv_inj, hv_range, fun i hi ↦ ⟨?_, ?_⟩⟩
  · have htake_eq :
        {x | ∃ j : Fin G.verts.ncard, j.1 < i ∧ v j = x} = {x | x ∈ L.take i} := by
      ext x
      simp only [Set.mem_ofPred_eq, List.mem_take_iff_getElem, v]
      refine ⟨?_, ?_⟩
      · rintro ⟨j, hj_lt, rfl⟩
        exact ⟨j.1, by omega, by simp⟩
      · rintro ⟨k, hk_lt, rfl⟩
        have hk_i : k < i := lt_of_lt_of_le hk_lt (min_le_left i L.length)
        have hk_n : k < G.verts.ncard := by
          have := lt_of_lt_of_le hk_lt (min_le_right i L.length)
          omega
        exact ⟨⟨k, hk_n⟩, hk_i, by simp⟩
    rw [htake_eq]
    have hsplit : L = L.take i ++ L.drop i := (List.take_append_drop i L).symm
    have hleft_take : IsLeftConnectedList G (L.take i) :=
      isLeftConnectedList_prefix (hsplit ▸ hL.left_conn)
    have hsub_take : ∀ x ∈ L.take i, x ∈ G.verts :=
      fun x hx ↦ hL.subset_verts x (List.mem_of_mem_take hx)
    exact preconnected_induce_of_isLeftConnectedList hsub_take hleft_take
  · have hdrop_eq :
        {x | ∃ j : Fin G.verts.ncard, i ≤ j.1 ∧ v j = x} = {x | x ∈ (L.drop i).reverse} := by
      ext x
      simp only [Set.mem_ofPred_eq, List.mem_reverse, List.mem_drop_iff_getElem, v]
      refine ⟨?_, ?_⟩
      · rintro ⟨j, hj_ge, rfl⟩
        refine ⟨j.1 - i, by omega, ?_⟩
        have hidx : i + (j.1 - i) = j.1 := by omega
        simp [hidx]
      · rintro ⟨k, hk_lt, rfl⟩
        have hik_n : i + k < G.verts.ncard := by omega
        have hik_ge : i ≤ (⟨i + k, hik_n⟩ : Fin G.verts.ncard).1 := Nat.le_add_right i k
        exact ⟨⟨i + k, hik_n⟩, hik_ge, by simp⟩
    rw [hdrop_eq]
    have hsplit_rev : L.reverse = (L.drop i).reverse ++ (L.take i).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    have hleft_drop : IsLeftConnectedList G (L.drop i).reverse :=
      isLeftConnectedList_prefix (hsplit_rev ▸ hL.right_conn)
    have hsub_drop : ∀ x ∈ (L.drop i).reverse, x ∈ G.verts :=
      fun x hx ↦ hL.subset_verts x (List.mem_of_mem_drop (List.mem_reverse.1 hx))
    exact preconnected_induce_of_isLeftConnectedList hsub_drop hleft_drop

end GraphMinor.GM05
