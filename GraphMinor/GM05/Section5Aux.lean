module

public import GraphMinor.GM05.Section4

/-!
# Auxiliary Lemmas for Graph Minors V, Section 5

This file proves the path-truncation, first-hit path, and single-edge contraction lemmas used in the
proofs of (5.1), (5.2), and (5.3) in `GraphMinor.GM05.Section5`:

- `exists_first_hit_path`: given a walk in `B` from `u` to a vertex of `S`, there is a path `P` in
  `B` starting at `u` and ending in `S` whose only vertex in `S` is `P.last`.
- `exists_prefix_path_meeting_card_eq`: given a path `P` in `G` starting at `v ∈ ⋃ j, V j` where
  the sets `V j` are pairwise disjoint, if `P` meets at least `k ≥ 1` of the sets `V j`, then some
  prefix path `P'` of `P` starting at `v` meets *exactly* `k` of the sets `V j`.
- `contractEdge`, `contractEdge_mem_𝓕`, `contractPath`, and `not_hasMesh_paths_of_mem_𝓕`:
  contracting shared edges between two families of disjoint paths in `G ∈ 𝓕_θ` to reduce a
  `(θ₂, θ₂)`-mesh of paths to a `(θ₂, θ₂)`-web, contradicting (4.6).
-/

@[expose] public section

namespace GraphMinor.GM05

open SimpleGraph Graph Set Relation GM01

universe u
variable {V : Type u}

/-! ## First-Hit Paths and Prefix Truncation for (5.1) -/

/-- By induction on a path-walk `w` from `u` to `z ∈ S`, there is a prefix path-walk from `u` to
some `v ∈ S` whose support meets `S` only at `v`. -/
private lemma exists_first_hit_walk (S : Set V) {u z : V} (w : (⊤ : SimpleGraph V).Walk u z)
    (hw : w.IsPath) (hz : z ∈ S) :
    ∃ v ∈ S, ∃ q : (⊤ : SimpleGraph V).Walk u v,
      q.IsPath ∧ q.toSubgraph ≤ w.toSubgraph ∧ {x | x ∈ q.support} ∩ S = {v} := by
  induction w with
  | @nil u =>
    refine ⟨u, hz, .nil, Walk.IsPath.nil, le_rfl, ?_⟩
    ext x
    simp only [Walk.support_nil, List.mem_singleton, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h ▸ hz⟩⟩
  | @cons a b c hadj rest ih =>
    by_cases ha : a ∈ S
    · refine ⟨a, ha, .nil, Walk.IsPath.nil, ?_, ?_⟩
      · simp
      · ext x
        simp only [Walk.support_nil, List.mem_singleton, Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_singleton_iff]
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h ▸ ha⟩⟩
    · rw [Walk.cons_isPath_iff] at hw
      obtain ⟨v, hvS, q, hq_path, hq_le, hq_inter⟩ := ih hw.1 hz
      have ha_not_q : a ∉ q.support := fun h ↦
        hw.2 (rest.mem_verts_toSubgraph.1 (hq_le.1 (q.mem_verts_toSubgraph.2 h)))
      refine ⟨v, hvS, .cons hadj q, (Walk.cons_isPath_iff hadj q).2 ⟨hq_path, ha_not_q⟩, ?_, ?_⟩
      · rw [Walk.toSubgraph, Walk.toSubgraph]
        exact sup_le_sup_left hq_le _
      · ext x
        simp only [Walk.support_cons, List.mem_cons, Set.mem_inter_iff, Set.mem_ofPred_eq]
        rw [← hq_inter]
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        refine ⟨fun ⟨hx, hxS⟩ ↦ ?_, fun ⟨hx, hxS⟩ ↦ ⟨Or.inr hx, hxS⟩⟩
        rcases hx with rfl | hx
        · exact absurd hxS ha
        · exact ⟨hx, hxS⟩

/-- Given a connected subgraph `B`, a vertex `u ∈ B.verts`, and a nonempty subset `S ⊆ B.verts`,
there is a path `P` in `B` starting at `u` and ending in `S` such that `P.verts ∩ S = {P.last}`. -/
lemma exists_first_hit_path {B : (⊤ : SimpleGraph V).Subgraph} (hB : B.Connected)
    {u : V} (hu : u ∈ B.verts) {S : Set V} (hS_sub : S ⊆ B.verts) (hS_ne : S.Nonempty) :
    ∃ P : GM01.Path V, P.toSubgraph ≤ B ∧ P.first = u ∧ P.last ∈ S ∧ P.verts ∩ S = {P.last} := by
  obtain ⟨z, hzS⟩ := hS_ne
  obtain ⟨w, hwB⟩ := ((Subgraph.connected_iff_forall_exists_walk_subgraph B).1 hB).2 hu (hS_sub hzS)
  let P₀ : GM01.Path V := GM01.Path.ofWalk w
  have hP₀_le : P₀.toSubgraph ≤ w.toSubgraph := GM01.Path.ofWalk_toSubgraph_le w
  obtain ⟨v, hvS, q, hq_path, hq_le, hq_inter⟩ :=
    exists_first_hit_walk S P₀.walk P₀.isPath hzS
  let P : GM01.Path V := ⟨u, v, q, hq_path⟩
  have hP_verts : P.verts = {x | x ∈ q.support} := by
    ext x
    exact q.mem_verts_toSubgraph
  exact ⟨P, hq_le.trans (hP₀_le.trans hwB), rfl, hvS, hP_verts ▸ hq_inter⟩

/-- The `Finset` of indices `j : Fin M` whose set `V j` meets `X`. -/
noncomputable def metIndices {M : ℕ} (Vset : Fin M → Set V) (X : Set V) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter fun j ↦ (Vset j ∩ X).Nonempty

private lemma metIndices_mono {M : ℕ} (Vset : Fin M → Set V) {X Y : Set V} (hXY : X ⊆ Y) :
    metIndices Vset X ⊆ metIndices Vset Y := by
  classical
  intro j hj
  simp only [metIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.mono (Set.inter_subset_inter_right _ hXY)

private lemma card_metIndices_insert_le {M : ℕ} {Vset : Fin M → Set V}
    (hdisj : Pairwise fun j₁ j₂ ↦ Disjoint (Vset j₁) (Vset j₂)) (x : V) (X : Set V) :
    (metIndices Vset (insert x X)).card ≤ (metIndices Vset X).card + 1 := by
  classical
  by_cases hx : ∃ j₀ : Fin M, x ∈ Vset j₀
  · obtain ⟨j₀, hj₀⟩ := hx
    have hsub : metIndices Vset (insert x X) ⊆ insert j₀ (metIndices Vset X) := by
      intro j hj
      simp only [metIndices, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert] at hj ⊢
      obtain ⟨w, hwV, hwX⟩ := hj
      rcases Set.mem_insert_iff.1 hwX with rfl | hwX
      · left
        by_contra hne
        exact Set.disjoint_left.1 (hdisj hne) hwV hj₀
      · exact Or.inr ⟨w, hwV, hwX⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  · push Not at hx
    have heq : metIndices Vset (insert x X) = metIndices Vset X := by
      ext j
      simp only [metIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun ⟨w, hwV, hwX⟩ ↦ ?_, fun ⟨w, hwV, hwX⟩ ↦ ⟨w, hwV, Set.mem_insert_of_mem x hwX⟩⟩
      rcases Set.mem_insert_iff.1 hwX with rfl | hwX
      · exact absurd hwV (hx j)
      · exact ⟨w, hwV, hwX⟩
    rw [heq]
    omega

private lemma card_metIndices_singleton_eq_one {M : ℕ} {Vset : Fin M → Set V}
    (hdisj : Pairwise fun j₁ j₂ ↦ Disjoint (Vset j₁) (Vset j₂))
    {v : V} {j₀ : Fin M} (hv : v ∈ Vset j₀) :
    (metIndices Vset {v}).card = 1 := by
  classical
  have heq : metIndices Vset {v} = {j₀} := by
    ext j
    simp only [metIndices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨w, hwV, hwv⟩ ↦ ?_, fun h ↦ ⟨v, h ▸ hv, Set.mem_singleton v⟩⟩
    rw [Set.mem_singleton_iff] at hwv
    subst hwv
    by_contra hne
    exact Set.disjoint_left.1 (hdisj hne) hwV hv
  rw [heq, Finset.card_singleton]

private lemma exists_prefix_path_of_rev_walk {M : ℕ} {Vset : Fin M → Set V}
    (hdisj : Pairwise fun j₁ j₂ ↦ Disjoint (Vset j₁) (Vset j₂))
    {j₀ : Fin M} {k : ℕ} (hk_pos : 1 ≤ k)
    {u v : V} (rev : (⊤ : SimpleGraph V).Walk u v)
    (hv : v ∈ Vset j₀) (hrev : rev.IsPath)
    (hk : k ≤ (metIndices Vset rev.toSubgraph.verts).card) :
    ∃ P' : GM01.Path V, P'.toSubgraph ≤ rev.toSubgraph ∧ P'.first = v ∧
      (metIndices Vset P'.verts).card = k := by
  induction rev with
  | @nil v =>
    have hverts : (Walk.nil : (⊤ : SimpleGraph V).Walk v v).toSubgraph.verts = {v} := by simp
    have hcard1 :
        (metIndices Vset (Walk.nil : (⊤ : SimpleGraph V).Walk v v).toSubgraph.verts).card = 1 := by
      rw [hverts]
      exact card_metIndices_singleton_eq_one hdisj hv
    have hk1 : k = 1 := by omega
    subst hk1
    refine ⟨GM01.Path.singleton v, le_rfl, rfl, ?_⟩
    simpa [GM01.Path.singleton_verts] using card_metIndices_singleton_eq_one hdisj hv
  | @cons a b v hadj rest ih =>
    by_cases heq : (metIndices Vset (Walk.cons hadj rest).toSubgraph.verts).card = k
    · let P₀ : GM01.Path V := ⟨a, v, .cons hadj rest, hrev⟩
      refine ⟨P₀.reverse, ?_, rfl, ?_⟩
      · exact le_of_eq (GM01.Path.reverse_toSubgraph P₀)
      · rw [GM01.Path.reverse_verts]
        exact heq
    · rw [Walk.cons_isPath_iff] at hrev
      have hverts_cons :
          (Walk.cons hadj rest).toSubgraph.verts = insert a rest.toSubgraph.verts := by
        ext x
        rw [Walk.mem_verts_toSubgraph, Walk.support_cons, List.mem_cons, Set.mem_insert_iff,
          Walk.mem_verts_toSubgraph]
      have hle_ins :
          (metIndices Vset (Walk.cons hadj rest).toSubgraph.verts).card ≤
            (metIndices Vset rest.toSubgraph.verts).card + 1 := by
        rw [hverts_cons]
        exact card_metIndices_insert_le hdisj a rest.toSubgraph.verts
      have hk_rest : k ≤ (metIndices Vset rest.toSubgraph.verts).card := by omega
      obtain ⟨P', hle, hfirst', hcard⟩ := ih hv hrev.1 hk_rest
      refine ⟨P', hle.trans ?_, hfirst', hcard⟩
      rw [Walk.toSubgraph]
      exact le_sup_right

/-- Given a path `P` in `G` starting at `v ∈ Vset j₀` where `Vset` is a family of pairwise disjoint
sets, if `1 ≤ k ≤ (metIndices Vset P.verts).card`, then there is a path `P'` in `G` starting at `v`
with `P'.toSubgraph ≤ P.toSubgraph` and `(metIndices Vset P'.verts).card = k`. -/
lemma exists_prefix_path_meeting_card_eq {M : ℕ} {Vset : Fin M → Set V}
    (hdisj : Pairwise fun j₁ j₂ ↦ Disjoint (Vset j₁) (Vset j₂))
    {v : V} {j₀ : Fin M} (hv : v ∈ Vset j₀)
    (P : GM01.Path V) (hfirst : P.first = v)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_le : k ≤ (metIndices Vset P.verts).card) :
    ∃ P' : GM01.Path V, P'.toSubgraph ≤ P.toSubgraph ∧ P'.first = v ∧
      (metIndices Vset P'.verts).card = k := by
  have hfirst_mem : P.first ∈ Vset j₀ := hfirst ▸ hv
  have hverts : P.reverse.walk.toSubgraph.verts = P.verts := GM01.Path.reverse_verts P
  have hk_rev : k ≤ (metIndices Vset P.reverse.walk.toSubgraph.verts).card := by
    rwa [hverts]
  obtain ⟨P', hle, hfirst', hcard⟩ :=
    exists_prefix_path_of_rev_walk hdisj hk_pos P.reverse.walk hfirst_mem P.reverse.isPath hk_rev
  have hsub : P.reverse.walk.toSubgraph = P.toSubgraph := GM01.Path.reverse_toSubgraph P
  exact ⟨P', hle.trans (le_of_eq hsub), hfirst'.trans hfirst, hcard⟩

/-! ## Single-Edge Contraction for (5.3) -/

/-- The vertex map identifying `v` with `u` and leaving all other vertices fixed. -/
def contractMap [DecidableEq V] (u v : V) (x : V) : V :=
  if x = v then u else x

@[simp]
private lemma contractMap_self [DecidableEq V] (u v : V) : contractMap u v v = u := by
  simp [contractMap]

@[simp]
private lemma contractMap_u [DecidableEq V] (u v : V) : contractMap u v u = u := by
  by_cases h : u = v <;> simp [contractMap, h]

private lemma contractMap_of_ne [DecidableEq V] {u v x : V} (hx : x ≠ v) :
    contractMap u v x = x := by
  simp [contractMap, hx]

/-- The subgraph of `⊤` obtained from `G` by contracting the edge `uv` into `u` (removing `v`). -/
def contractEdge [DecidableEq V] (G : (⊤ : SimpleGraph V).Subgraph) (u v : V) :
    (⊤ : SimpleGraph V).Subgraph where
  verts := G.verts \ {v}
  Adj x y := x ∈ G.verts \ {v} ∧ y ∈ G.verts \ {v} ∧ x ≠ y ∧
    ∃ a b, contractMap u v a = x ∧ contractMap u v b = y ∧ G.Adj a b
  adj_sub h := h.2.2.1
  edge_vert h := h.1
  symm := ⟨fun _ _ ⟨hx, hy, hne, a, b, ha, hb, hab⟩ ↦
    ⟨hy, hx, hne.symm, b, a, hb, ha, hab.symm⟩⟩

private lemma contractMap_mem_verts [DecidableEq V] {G : (⊤ : SimpleGraph V).Subgraph}
    {u v x : V} (hu : u ∈ G.verts) (hne : u ≠ v) (hx : x ∈ G.verts) :
    contractMap u v x ∈ (contractEdge G u v).verts := by
  by_cases hxv : x = v
  · subst hxv
    rw [contractMap_self]
    exact ⟨hu, hne⟩
  · rw [contractMap_of_ne hxv]
    exact ⟨hx, hxv⟩

/-- If `G ∈ 𝓕_θ` and `G.Adj u v`, then `contractEdge G u v ∈ 𝓕_θ`. -/
lemma contractEdge_mem_𝓕 [DecidableEq V] {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ) {u v : V} (hadj : G.Adj u v) :
    contractEdge G u v ∈ 𝓕 θ := by
  have hu : u ∈ G.verts := hadj.fst_mem
  have hv : v ∈ G.verts := hadj.snd_mem
  have hne : u ≠ v := hadj.ne
  let G' := contractEdge G u v
  have hG'_fin : G'.verts.Finite := hG_fin.subset (by intro x hx; exact hx.1)
  let K : V → (⊤ : SimpleGraph V).Subgraph := fun w ↦
    if w = u then (⊤ : SimpleGraph V).subgraphOfAdj hadj.adj_sub
    else (GM01.Path.singleton w).toSubgraph
  have hK_verts : ∀ w ∈ G'.verts, (K w).verts = {x ∈ G.verts | contractMap u v x = w} := by
    intro w hw
    by_cases hwu : w = u
    · subst hwu
      ext x
      simp only [K, ↓reduceIte, subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_ofPred_eq, contractMap]
      refine ⟨?_, ?_⟩
      · rintro (rfl | rfl)
        · exact ⟨hu, ite_eq_right hne⟩
        · exact ⟨hv, ite_eq_left rfl⟩
      · rintro ⟨_, hmap⟩
        split_ifs at hmap with hxv
        · exact Or.inr hxv
        · exact Or.inl hmap
    · ext x
      have hverts_single : ((GM01.Path.singleton w).toSubgraph).verts = {w} :=
        GM01.Path.singleton_verts w
      dsimp [K]
      rw [ite_eq_right hwu, hverts_single]
      simp only [Set.mem_singleton_iff, contractMap]
      refine ⟨?_, ?_⟩
      · rintro rfl
        exact ⟨hw.1, ite_eq_right hw.2⟩
      · rintro ⟨_, hmap⟩
        split_ifs at hmap with hxv
        · exact absurd hmap.symm hwu
        · exact hmap
  have hminor : IsIsoMinor (toGraph G') (toGraph G) := by
    refine isIsoMinor_toGraph_of_connected_subgraphs hG'_fin hG_fin K ?_ ?_ ?_ ?_
    · intro w hw
      dsimp [K]
      split_ifs with hwu
      · exact subgraphOfAdj_le_of_adj G hadj
      · change (Walk.nil : (⊤ : SimpleGraph V).Walk w w).toSubgraph ≤ G
        simp [hw.1]
    · intro w _
      dsimp [K]
      split_ifs with hwu
      · rw [← Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
        exact (Walk.cons hadj.adj_sub .nil).toSubgraph_connected
      · exact (GM01.Path.singleton w).connected_toSubgraph
    · intro w₁ hw₁ w₂ hw₂ hne_w
      rw [hK_verts w₁ hw₁, hK_verts w₂ hw₂, Set.disjoint_left]
      rintro x ⟨_, rfl⟩ ⟨_, heq⟩
      exact hne_w heq
    · intro w₁ w₂ hadj'
      obtain ⟨hw₁, hw₂, _, a, b, ha, hb, hab⟩ := hadj'
      refine ⟨a, ?_, b, ?_, hab⟩
      · rw [hK_verts w₁ hw₁]
        exact ⟨hab.fst_mem, ha⟩
      · rw [hK_verts w₂ hw₂]
        exact ⟨hab.snd_mem, hb⟩
  exact mem_𝓕_of_isIsoMinor hminor hG

/-- Contracting an edge `(u, v)` along a walk `w` by skipping any step whose endpoints map to the
same vertex under `contractMap u v`. -/
def contractWalk [DecidableEq V] (u v : V) :
    ∀ {a b : V}, (⊤ : SimpleGraph V).Walk a b →
      (⊤ : SimpleGraph V).Walk (contractMap u v a) (contractMap u v b)
  | _, _, .nil => .nil
  | a, _, @Walk.cons _ _ _ c _ _ rest =>
    if h : contractMap u v a = contractMap u v c then
      h ▸ contractWalk u v rest
    else
      .cons h (contractWalk u v rest)

private lemma mem_support_contractWalk_iff [DecidableEq V] (u v : V) {a b : V}
    (w : (⊤ : SimpleGraph V).Walk a b) (z : V) :
    z ∈ (contractWalk u v w).support ↔ ∃ x ∈ w.support, contractMap u v x = z := by
  induction w with
  | nil => simp [contractWalk, eq_comm]
  | @cons a c b hadj rest ih =>
    dsimp [contractWalk]
    split_ifs with h
    · have hmem_eq : ∀ {x y : V} (heq : x = y) (p : (⊤ : SimpleGraph V).Walk y (contractMap u v b)),
          z ∈ (heq ▸ p : (⊤ : SimpleGraph V).Walk x (contractMap u v b)).support ↔ z ∈ p.support := by
        rintro x _ rfl p
        rfl
      rw [hmem_eq h, ih]
      simp only [List.mem_cons]
      refine ⟨fun ⟨x, hx, hxz⟩ ↦ ⟨x, Or.inr hx, hxz⟩, ?_⟩
      rintro ⟨x, rfl | hx, hxz⟩
      · exact ⟨c, rest.start_mem_support, h.symm.trans hxz⟩
      · exact ⟨x, hx, hxz⟩
    · rw [Walk.support_cons, List.mem_cons, ih]
      simp only [List.mem_cons]
      refine ⟨?_, ?_⟩
      · rintro (rfl | ⟨x, hx, hxz⟩)
        · exact ⟨a, Or.inl rfl, rfl⟩
        · exact ⟨x, Or.inr hx, hxz⟩
      · rintro ⟨x, rfl | hx, hxz⟩
        · exact Or.inl hxz.symm
        · exact Or.inr ⟨x, hx, hxz⟩

private lemma contractWalk_toSubgraph_le [DecidableEq V] {G : (⊤ : SimpleGraph V).Subgraph}
    {u v : V} (hadj_uv : G.Adj u v) {a b : V} (w : (⊤ : SimpleGraph V).Walk a b)
    (hw : w.toSubgraph ≤ G) :
    (contractWalk u v w).toSubgraph ≤ contractEdge G u v := by
  have hu : u ∈ G.verts := hadj_uv.fst_mem
  have hne : u ≠ v := hadj_uv.ne
  induction w with
  | @nil a =>
    have haG : a ∈ G.verts := hw.1 (by simp)
    have ha' : contractMap u v a ∈ (contractEdge G u v).verts :=
      contractMap_mem_verts hu hne haG
    simp [contractWalk, ha']
  | @cons a c b hadj rest ih =>
    rw [Walk.toSubgraph, sup_le_iff] at hw
    have hadjG : G.Adj a c := hw.1.2 (by simp)
    dsimp [contractWalk]
    split_ifs with h
    · have hsub_eq : ∀ {x y : V} (heq : x = y) (p : (⊤ : SimpleGraph V).Walk y (contractMap u v b)),
          (heq ▸ p : (⊤ : SimpleGraph V).Walk x (contractMap u v b)).toSubgraph = p.toSubgraph := by
        rintro x _ rfl p
        rfl
      rw [hsub_eq h]
      exact ih hw.2
    · rw [Walk.toSubgraph]
      refine sup_le ?_ (ih hw.2)
      refine subgraphOfAdj_le_of_adj (contractEdge G u v) ?_
      exact ⟨contractMap_mem_verts hu hne hadjG.fst_mem,
        contractMap_mem_verts hu hne hadjG.snd_mem, h, a, c, rfl, rfl, hadjG⟩

private lemma contractMap_eq_iff [DecidableEq V] {u v x y : V} :
    contractMap u v x = contractMap u v y ↔ x = y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  dsimp [contractMap]
  by_cases hxv : x = v <;> by_cases hyv : y = v
  · simp [hxv, hyv]
  · simp only [ite_eq_left hxv, ite_eq_right hyv]
    refine ⟨fun h ↦ Or.inr (Or.inr ⟨hxv, h.symm⟩), ?_⟩
    rintro (rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact absurd hxv hyv
    · exact absurd rfl hyv
    · rfl
  · simp only [ite_eq_right hxv, ite_eq_left hyv]
    refine ⟨fun h ↦ Or.inr (Or.inl ⟨h, hyv⟩), ?_⟩
    rintro (rfl | ⟨rfl, _⟩ | ⟨rfl, _⟩)
    · exact absurd hyv hxv
    · rfl
    · exact absurd rfl hxv
  · simp only [ite_eq_right hxv, ite_eq_right hyv]
    refine ⟨fun h ↦ Or.inl h, ?_⟩
    rintro (rfl | ⟨_, rfl⟩ | ⟨rfl, _⟩)
    · rfl
    · exact absurd rfl hyv
    · exact absurd rfl hxv

lemma isPath_contractWalk [DecidableEq V] {u v : V} (hne_uv : u ≠ v)
    {a b : V} (w : (⊤ : SimpleGraph V).Walk a b) (hw : w.IsPath)
    (hcond : v ∉ w.support ∨ u ∉ w.support ∨ w.toSubgraph.Adj u v) :
    (contractWalk u v w).IsPath := by
  induction w with
  | nil => exact Walk.IsPath.nil
  | @cons a c b hadj rest ih =>
    rw [Walk.cons_isPath_iff] at hw
    dsimp [contractWalk]
    split_ifs with h
    · have hpair : (a = u ∧ c = v) ∨ (a = v ∧ c = u) := by
        rcases contractMap_eq_iff.1 h with rfl | h1 | h2
        · exact absurd rfl hadj.ne
        · exact Or.inl h1
        · exact Or.inr h2
      have hcond' : v ∉ rest.support ∨ u ∉ rest.support ∨ rest.toSubgraph.Adj u v := by
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl hw.2)
        · exact Or.inl hw.2
      have hpath := ih hw.1 hcond'
      have hpath_eq : ∀ {x y : V} (heq : x = y) (p : (⊤ : SimpleGraph V).Walk y (contractMap u v b)),
          (heq ▸ p : (⊤ : SimpleGraph V).Walk x (contractMap u v b)).IsPath ↔ p.IsPath := by
        rintro x _ rfl p
        rfl
      exact (hpath_eq h _).2 hpath
    · rw [Walk.cons_isPath_iff]
      have hcond_rest :
          (v ∉ rest.support ∨ u ∉ rest.support ∨ rest.toSubgraph.Adj u v) ∧
            contractMap u v a ∉ (contractWalk u v rest).support := by
        rcases hcond with hv_not | hu_not | hadj_w
        · have hv_rest : v ∉ rest.support := fun hm ↦ hv_not (List.mem_cons_of_mem a hm)
          have ha_ne_v : a ≠ v := fun heq ↦ hv_not (heq ▸ by simp)
          refine ⟨Or.inl hv_rest, ?_⟩
          rw [mem_support_contractWalk_iff]
          rintro ⟨x, hx, hxz⟩
          have hx_ne_v : x ≠ v := fun heq ↦ hv_rest (heq ▸ hx)
          rw [contractMap_of_ne ha_ne_v, contractMap_of_ne hx_ne_v] at hxz
          exact hw.2 (hxz ▸ hx)
        · have hu_rest : u ∉ rest.support := fun hm ↦ hu_not (List.mem_cons_of_mem a hm)
          have ha_ne_u : a ≠ u := fun heq ↦ hu_not (heq ▸ by simp)
          refine ⟨Or.inr (Or.inl hu_rest), ?_⟩
          rw [mem_support_contractWalk_iff]
          rintro ⟨x, hx, hxz⟩
          have hx_ne_u : x ≠ u := fun heq ↦ hu_rest (heq ▸ hx)
          rcases contractMap_eq_iff.1 hxz with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hw.2 hx
          · exact hx_ne_u rfl
          · exact ha_ne_u rfl
        · rw [Walk.toSubgraph, Subgraph.sup_adj, subgraphOfAdj_adj] at hadj_w
          rcases hadj_w with hac_eq | hadj_rest
          · exfalso
            apply h
            rcases Sym2.eq_iff.1 hac_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
          · have hu_mem : u ∈ rest.support :=
              rest.mem_verts_toSubgraph.1 hadj_rest.fst_mem
            have hv_mem : v ∈ rest.support :=
              rest.mem_verts_toSubgraph.1 hadj_rest.snd_mem
            have ha_ne_u : a ≠ u := fun heq ↦ hw.2 (heq ▸ hu_mem)
            have ha_ne_v : a ≠ v := fun heq ↦ hw.2 (heq ▸ hv_mem)
            refine ⟨Or.inr (Or.inr hadj_rest), ?_⟩
            rw [mem_support_contractWalk_iff]
            rintro ⟨x, hx, hxz⟩
            rcases contractMap_eq_iff.1 hxz with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hw.2 hx
            · exact ha_ne_v rfl
            · exact ha_ne_u rfl
      exact ⟨ih hw.1 hcond_rest.1, hcond_rest.2⟩

/-- Contracting an edge `(u, v)` along a path `P` satisfying `v ∉ P.verts ∨ u ∉ P.verts ∨
P.toSubgraph.Adj u v`. -/
def contractPath [DecidableEq V] {u v : V} (hne_uv : u ≠ v) (P : GM01.Path V)
    (hcond : v ∉ P.verts ∨ u ∉ P.verts ∨ P.toSubgraph.Adj u v) : GM01.Path V where
  first := contractMap u v P.first
  last := contractMap u v P.last
  walk := contractWalk u v P.walk
  isPath := isPath_contractWalk hne_uv P.walk P.isPath (by
    rcases hcond with h1 | h2 | h3
    · exact Or.inl ((GM01.Path.mem_verts_iff P).not.1 h1)
    · exact Or.inr (Or.inl ((GM01.Path.mem_verts_iff P).not.1 h2))
    · exact Or.inr (Or.inr h3))

private lemma verts_contractPath [DecidableEq V] {u v : V} (hne_uv : u ≠ v) (P : GM01.Path V)
    (hcond : v ∉ P.verts ∨ u ∉ P.verts ∨ P.toSubgraph.Adj u v) :
    (contractPath hne_uv P hcond).verts = contractMap u v '' P.verts := by
  ext z
  rw [GM01.Path.mem_verts_iff, contractPath, mem_support_contractWalk_iff]
  simp [GM01.Path.mem_verts_iff]

/-- If `G ∈ 𝓕_θ` has two families of pairwise vertex-disjoint paths `C : Fin (θ₂ θ) → GM01.Path V`
and `D : Fin (θ₂ θ) → GM01.Path V` such that every `C i` meets every `D j`, then we obtain a
contradiction by contracting shared edges one by one until `(C, D)` becomes a `(θ₂, θ₂)`-web,
contradicting (4.6). -/
theorem not_hasMesh_paths_of_mem_𝓕
    {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) :
    ∀ (N : ℕ) {G : (⊤ : SimpleGraph V).Subgraph},
      G.verts.Finite → G.verts.ncard ≤ N → G ∈ 𝓕 θ →
      ∀ (C D : Fin (θ₂ θ) → GM01.Path V),
        (∀ i, (C i).toSubgraph ≤ G) →
        (∀ j, (D j).toSubgraph ≤ G) →
        (Pairwise fun i i' ↦ Disjoint (C i).verts (C i').verts) →
        (Pairwise fun j j' ↦ Disjoint (D j).verts (D j').verts) →
        (∀ i j, ((C i).verts ∩ (D j).verts).Nonempty) →
        False := by
  classical
  intro N
  induction N with
  | zero =>
    intro G hG_fin hcard hG C D hC_le hD_le hC_disj hD_disj hmeets
    have hweb : IsWeb G C D :=
      { isIn_left := hC_le
        isIn_right := hD_le
        disjoint_left := hC_disj
        disjoint_right := hD_disj
        meets := hmeets
        edge_disjoint := fun i j ↦ by
          rw [Set.disjoint_left]
          rintro ⟨u, v⟩ huvC _
          have huG : u ∈ G.verts := (hC_le i).1 ((C i).toSubgraph.edge_vert huvC)
          have hempty : G.verts = ∅ := (Set.ncard_eq_zero hG_fin).1 (by omega)
          rw [hempty] at huG
          exact huG }
    exact theorem_4_6_simple hθ heven hG_fin hG ⟨C, D, hweb⟩
  | succ N ih =>
    intro G hG_fin hcard hG C D hC_le hD_le hC_disj hD_disj hmeets
    by_cases hedisj : ∀ i j, Disjoint (C i).toSubgraph.edgeSet (D j).toSubgraph.edgeSet
    · have hweb : IsWeb G C D :=
        { isIn_left := hC_le
          isIn_right := hD_le
          disjoint_left := hC_disj
          disjoint_right := hD_disj
          meets := hmeets
          edge_disjoint := hedisj }
      exact theorem_4_6_simple hθ heven hG_fin hG ⟨C, D, hweb⟩
    · push Not at hedisj
      obtain ⟨i₀, j₀, hnot_disj⟩ := hedisj
      rw [Set.not_disjoint_iff] at hnot_disj
      obtain ⟨⟨u, v⟩, huvC, huvD⟩ := hnot_disj
      have hadjC : (C i₀).toSubgraph.Adj u v := huvC
      have hadjD : (D j₀).toSubgraph.Adj u v := huvD
      have hadjG : G.Adj u v := (hC_le i₀).2 hadjC
      have hne_uv : u ≠ v := hadjG.ne
      have huC : u ∈ (C i₀).verts := hadjC.fst_mem
      have hvC : v ∈ (C i₀).verts := hadjC.snd_mem
      have huD : u ∈ (D j₀).verts := hadjD.fst_mem
      have hvD : v ∈ (D j₀).verts := hadjD.snd_mem
      let G' := contractEdge G u v
      have hG'_fin : G'.verts.Finite := hG_fin.subset (by intro x hx; exact hx.1)
      have hG'_card : G'.verts.ncard ≤ N := by
        have hlt : (G.verts \ {v}).ncard < G.verts.ncard :=
          Set.ncard_sdiff_singleton_lt_of_mem hadjG.snd_mem hG_fin
        change (G.verts \ {v}).ncard ≤ N
        omega
      have hG'_mem : G' ∈ 𝓕 θ := contractEdge_mem_𝓕 hG_fin hG hadjG
      have hcondC : ∀ i, v ∉ (C i).verts ∨ u ∉ (C i).verts ∨ (C i).toSubgraph.Adj u v := by
        intro i
        by_cases hi : i = i₀
        · subst hi
          exact Or.inr (Or.inr hadjC)
        · exact Or.inl (fun hv ↦ Set.disjoint_left.1 (hC_disj hi) hv hvC)
      have hcondD : ∀ j, v ∉ (D j).verts ∨ u ∉ (D j).verts ∨ (D j).toSubgraph.Adj u v := by
        intro j
        by_cases hj : j = j₀
        · subst hj
          exact Or.inr (Or.inr hadjD)
        · exact Or.inl (fun hv ↦ Set.disjoint_left.1 (hD_disj hj) hv hvD)
      let C' : Fin (θ₂ θ) → GM01.Path V := fun i ↦ contractPath hne_uv (C i) (hcondC i)
      let D' : Fin (θ₂ θ) → GM01.Path V := fun j ↦ contractPath hne_uv (D j) (hcondD j)
      refine ih hG'_fin hG'_card hG'_mem C' D' ?_ ?_ ?_ ?_ ?_
      · intro i
        exact contractWalk_toSubgraph_le hadjG (C i).walk (hC_le i)
      · intro j
        exact contractWalk_toSubgraph_le hadjG (D j).walk (hD_le j)
      · intro i₁ i₂ hne_i
        rw [verts_contractPath, verts_contractPath, Set.disjoint_left]
        rintro _ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, heq⟩
        rcases contractMap_eq_iff.1 heq.symm with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Set.disjoint_left.1 (hC_disj hne_i) hx₁ hx₂
        · have hi₁ : i₁ = i₀ := by
            by_contra hne1
            exact Set.disjoint_left.1 (hC_disj hne1) hx₁ huC
          have hi₂ : i₂ = i₀ := by
            by_contra hne2
            exact Set.disjoint_left.1 (hC_disj hne2) hx₂ hvC
          exact hne_i (hi₁.trans hi₂.symm)
        · have hi₁ : i₁ = i₀ := by
            by_contra hne1
            exact Set.disjoint_left.1 (hC_disj hne1) hx₁ hvC
          have hi₂ : i₂ = i₀ := by
            by_contra hne2
            exact Set.disjoint_left.1 (hC_disj hne2) hx₂ huC
          exact hne_i (hi₁.trans hi₂.symm)
      · intro j₁ j₂ hne_j
        rw [verts_contractPath, verts_contractPath, Set.disjoint_left]
        rintro _ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, heq⟩
        rcases contractMap_eq_iff.1 heq.symm with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Set.disjoint_left.1 (hD_disj hne_j) hx₁ hx₂
        · have hj₁ : j₁ = j₀ := by
            by_contra hne1
            exact Set.disjoint_left.1 (hD_disj hne1) hx₁ huD
          have hj₂ : j₂ = j₀ := by
            by_contra hne2
            exact Set.disjoint_left.1 (hD_disj hne2) hx₂ hvD
          exact hne_j (hj₁.trans hj₂.symm)
        · have hj₁ : j₁ = j₀ := by
            by_contra hne1
            exact Set.disjoint_left.1 (hD_disj hne1) hx₁ hvD
          have hj₂ : j₂ = j₀ := by
            by_contra hne2
            exact Set.disjoint_left.1 (hD_disj hne2) hx₂ huD
          exact hne_j (hj₁.trans hj₂.symm)
      · intro i j
        obtain ⟨w, hwC, hwD⟩ := hmeets i j
        rw [verts_contractPath, verts_contractPath]
        exact ⟨contractMap u v w, ⟨w, hwC, rfl⟩, ⟨w, hwD, rfl⟩⟩

/-! ## Additional Helpers for Section 5 -/

theorem IsMesh.symm {G : (⊤ : SimpleGraph V).Subgraph} {m n : ℕ}
    {A : Fin m → (⊤ : SimpleGraph V).Subgraph} {B : Fin n → (⊤ : SimpleGraph V).Subgraph}
    (h : IsMesh G A B) : IsMesh G B A where
  le_left := h.le_right
  le_right := h.le_left
  connected_left := h.connected_right
  connected_right := h.connected_left
  disjoint_left := h.disjoint_right
  disjoint_right := h.disjoint_left
  meets j i := Set.inter_comm (A i).verts (B j).verts ▸ h.meets i j

lemma connected_sup_of_inter_nonempty {A B : (⊤ : SimpleGraph V).Subgraph}
    (hA : A.Connected) (hB : B.Connected) (h : (A.verts ∩ B.verts).Nonempty) :
    (A ⊔ B).Connected := by
  obtain ⟨z, hzA, hzB⟩ := h
  rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
  refine ⟨⟨z, Or.inl hzA⟩, fun {x y} hx hy ↦ ?_⟩
  have h_to_z : ∀ w ∈ (A ⊔ B).verts, ∃ p : (⊤ : SimpleGraph V).Walk w z, p.toSubgraph ≤ A ⊔ B := by
    rintro w (hwA | hwB)
    · obtain ⟨p, hp⟩ := ((Subgraph.connected_iff_forall_exists_walk_subgraph A).1 hA).2 hwA hzA
      exact ⟨p, hp.trans le_sup_left⟩
    · obtain ⟨p, hp⟩ := ((Subgraph.connected_iff_forall_exists_walk_subgraph B).1 hB).2 hwB hzB
      exact ⟨p, hp.trans le_sup_right⟩
  obtain ⟨px, hpx⟩ := h_to_z x hx
  obtain ⟨py, hpy⟩ := h_to_z y hy
  refine ⟨px.append py.reverse, ?_⟩
  rw [Walk.toSubgraph_append, Walk.toSubgraph_reverse]
  exact sup_le hpx hpy

private lemma exists_two_adj_of_internal_isPath' {x y z : V}
    (w : (⊤ : SimpleGraph V).Walk x y) (hw : w.IsPath)
    {H : (⊤ : SimpleGraph V).Subgraph} (hle : w.toSubgraph ≤ H)
    (hz : z ∈ w.support) (hzx : z ≠ x) (hzy : z ≠ y) :
    ∃ a b : V, a ≠ b ∧ H.Adj z a ∧ H.Adj z b := by
  induction w with
  | nil =>
    rw [Walk.support_nil, List.mem_singleton] at hz
    exact absurd hz hzx
  | @cons x x' y hadj rest ih =>
    rw [Walk.cons_isPath_iff] at hw
    rw [Walk.toSubgraph, sup_le_iff] at hle
    have hadj₁ : H.Adj x x' := hle.1.2 (by simp)
    rw [Walk.support_cons, List.mem_cons] at hz
    have hz_rest : z ∈ rest.support := hz.resolve_left hzx
    by_cases hzx' : z = x'
    · subst hzx'
      cases rest with
      | nil => exact absurd rfl hzy
      | @cons _ x'' y hadj₂ rest₂ =>
        rw [Walk.toSubgraph, sup_le_iff] at hle
        have hadj₂H : H.Adj z x'' := hle.2.1.2 (by simp)
        have hx''_mem : x'' ∈ (Walk.cons hadj₂ rest₂).support := by simp
        have hne : x ≠ x'' := fun h ↦ hw.2 (h ▸ hx''_mem)
        exact ⟨x, x'', hne, hadj₁.symm, hadj₂H⟩
    · exact ih hw.1 hle.2 hz_rest hzx' hzy

private lemma connected_deleteVerts_of_subsingleton_neighborSet'
    {H : (⊤ : SimpleGraph V).Subgraph} (hH : H.Connected) (L : Set V)
    (hne : (H.verts \ L).Nonempty)
    (hL : ∀ v ∈ L, v ∈ H.verts → (H.neighborSet v).Subsingleton) :
    (H.deleteVerts L).Connected := by
  rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
  refine ⟨by simpa using hne, fun {u v} hu hv ↦ ?_⟩
  simp only [Subgraph.deleteVerts_verts, Set.mem_sdiff] at hu hv
  obtain ⟨P, hPH, rfl, rfl⟩ := exists_path_of_preconnected hH.preconnected hu.1 hv.1
  refine ⟨P.walk, ?_⟩
  have hP_verts : P.verts ⊆ H.verts \ L := by
    intro z hzP
    refine ⟨hPH.1 hzP, fun hzL ↦ ?_⟩
    have hzx : z ≠ P.first := fun h ↦ hu.2 (h ▸ hzL)
    have hzy : z ≠ P.last := fun h ↦ hv.2 (h ▸ hzL)
    obtain ⟨a, b, hab, hadja, hadjb⟩ :=
      exists_two_adj_of_internal_isPath' P.walk P.isPath hPH (P.mem_verts_iff.1 hzP) hzx hzy
    exact hab (hL z hzL (hPH.1 hzP) hadja hadjb)
  refine ⟨hP_verts, fun a b hab ↦ ?_⟩
  have ha : a ∈ P.verts := P.walk.toSubgraph.edge_vert hab
  have hb : b ∈ P.verts := P.walk.toSubgraph.edge_vert hab.symm
  simp only [Subgraph.deleteVerts_adj]
  exact ⟨(hP_verts ha).1, (hP_verts ha).2, (hP_verts hb).1, (hP_verts hb).2, hPH.2 hab⟩

private lemma exists_unique_adj_of_isLeafOf' {H : (⊤ : SimpleGraph V).Subgraph}
    {v : V} (hleaf : IsLeafOf H v) :
    ∃ u ∈ H.verts, H.Adj v u ∧ ∀ w, H.Adj v w ↔ w = u := by
  obtain ⟨u, hu_eq⟩ := Set.ncard_eq_one.1 hleaf.2
  have hu_mem : u ∈ H.neighborSet v := hu_eq ▸ Set.mem_singleton u
  have hadj : H.Adj v u := (H.mem_neighborSet v u).1 hu_mem
  refine ⟨u, H.edge_vert hadj.symm, hadj, fun w ↦ ?_⟩
  rw [← H.mem_neighborSet v w, hu_eq, Set.mem_singleton_iff]

private lemma verts_subset_pair_of_unique_neighbors' {H : (⊤ : SimpleGraph V).Subgraph}
    (hH : H.Connected) {v u : V} (hv : v ∈ H.verts)
    (hvu : ∀ w, H.Adj v w ↔ w = u) (huv : ∀ w, H.Adj u w ↔ w = v) :
    H.verts ⊆ {v, u} := by
  intro z hz
  obtain ⟨p, hp⟩ := ((Subgraph.connected_iff_forall_exists_walk_subgraph H).1 hH).2 hv hz
  have haux : ∀ {a b : V} (q : (⊤ : SimpleGraph V).Walk a b),
      q.toSubgraph ≤ H → a ∈ ({v, u} : Set V) → b ∈ ({v, u} : Set V) := by
    intro a b q hq ha
    induction q with
    | nil => exact ha
    | @cons a c b _ rest ih =>
      rw [Walk.toSubgraph, sup_le_iff] at hq
      have hadj : H.Adj a c := hq.1.2 (by simp)
      have hc : c ∈ ({v, u} : Set V) := by
        rcases ha with rfl | rfl
        · exact Or.inr ((hvu c).1 hadj)
        · exact Or.inl ((huv c).1 hadj)
      exact ih hq.2 hc
  exact haux p hp (Or.inl rfl)

/-- Corollary of (4.1) used in the proof of (5.2) (page 102): if `A₁, …, A_{θ²/2}` are pairwise
disjoint connected subgraphs of `G ∈ 𝓕_θ` and `B₁, …, B_{θ²/2}` are pairwise disjoint connected
subgraphs of `G` such that each `V(A_i) ∩ V(B_j)` consists of a single vertex `v_{ij}` of valency 1
in `B_j`, then deleting the leaves `{v_{ij} : i}` from each `B_j` contradicts (4.1). -/
theorem theorem_4_1_leaves {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (A B : Fin (θ ^ 2 / 2) → (⊤ : SimpleGraph V).Subgraph)
    (hA_le : ∀ i, A i ≤ G) (hA_conn : ∀ i, (A i).Connected)
    (hA_disj : Pairwise fun i i' ↦ Disjoint (A i).verts (A i').verts)
    (hB_le : ∀ j, B j ≤ G) (hB_conn : ∀ j, (B j).Connected)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (hAB : ∀ i j, ∃ v, (A i).verts ∩ (B j).verts = {v} ∧ IsLeafOf (B j) v) :
    False := by
  classical
  let m := θ ^ 2 / 2
  have hm_ge : 18 ≤ m := eighteen_le_half_θ_sq hθ
  choose v hv_inter hv_leaf using hAB
  have hv_mem_A : ∀ i j, v i j ∈ (A i).verts := by
    intro i j
    have : v i j ∈ (A i).verts ∩ (B j).verts := by
      rw [hv_inter i j]
      exact Set.mem_singleton _
    exact this.1
  have hv_mem_B : ∀ i j, v i j ∈ (B j).verts := fun i j ↦ (hv_leaf i j).1
  have hv_inj : ∀ j, Function.Injective (fun i : Fin m ↦ v i j) := by
    intro j i₁ i₂ heq
    by_contra hne
    have hmem₂ : v i₁ j ∈ (A i₂).verts := by
      change (fun i ↦ v i j) i₁ ∈ (A i₂).verts
      rw [heq]
      exact hv_mem_A i₂ j
    exact Set.disjoint_left.1 (hA_disj hne) (hv_mem_A i₁ j) hmem₂
  let S : Fin m → Set V := fun j ↦ Set.range (fun i : Fin m ↦ v i j)
  have hS_sub : ∀ j, S j ⊆ (B j).verts := by
    rintro j _ ⟨i, rfl⟩
    exact hv_mem_B i j
  choose u hu_mem_B huv_adj huv_uniq using fun i j ↦ exists_unique_adj_of_isLeafOf' (hv_leaf i j)
  have hu_not_S : ∀ i j, u i j ∉ S j := by
    rintro i j ⟨i', hi'⟩
    have hi'_eq : v i' j = u i j := hi'
    have hsub : (B j).verts ⊆ {v i j, u i j} := by
      apply verts_subset_pair_of_unique_neighbors' (hB_conn j) (hv_mem_B i j) (huv_uniq i j)
      intro w
      rw [← hi'_eq, huv_uniq i' j w]
      have h1 : (B j).Adj (v i' j) (v i j) := by
        rw [hi'_eq]
        exact (huv_adj i j).symm
      have h2 : v i j = u i' j := (huv_uniq i' j (v i j)).1 h1
      rw [h2]
    have hS_card : (S j).ncard = m := by
      dsimp [S]
      rw [Set.ncard_range_of_injective (hv_inj j), Nat.card_fin]
    have hpair_le : ({v i j, u i j} : Set V).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by simp)
    have hle2 : (S j).ncard ≤ 2 :=
      (Set.ncard_le_ncard ((hS_sub j).trans hsub) (Set.toFinite _)).trans hpair_le
    omega
  let B' : Fin m → (⊤ : SimpleGraph V).Subgraph := fun j ↦ (B j).deleteVerts (S j)
  have hB'_le : ∀ j, B' j ≤ G := fun j ↦ Subgraph.deleteVerts_le.trans (hB_le j)
  have hB'_conn : ∀ j, (B' j).Connected := by
    intro j
    apply connected_deleteVerts_of_subsingleton_neighborSet' (hB_conn j) (S j)
    · exact ⟨u ⟨0, by omega⟩ j, hu_mem_B ⟨0, by omega⟩ j, hu_not_S ⟨0, by omega⟩ j⟩
    · rintro x ⟨i, rfl⟩ _ y hy z hz
      rw [(B j).mem_neighborSet (v i j), huv_uniq i j] at hy hz
      exact hy.trans hz.symm
  have hB'_disj : Pairwise fun j₁ j₂ ↦ Disjoint (B' j₁).verts (B' j₂).verts :=
    fun j₁ j₂ hne ↦ (hB_disj hne).mono Subgraph.deleteVerts_le.1 Subgraph.deleteVerts_le.1
  have hAB'_disj : ∀ i j, Disjoint (A i).verts (B' j).verts := by
    intro i j
    rw [Set.disjoint_left]
    rintro x hxA ⟨hxB, hxnotS⟩
    have hxv : x = v i j := by
      have : x ∈ (A i).verts ∩ (B j).verts := ⟨hxA, hxB⟩
      rwa [hv_inter i j, Set.mem_singleton_iff] at this
    exact hxnotS ⟨i, hxv.symm⟩
  have hAB'_adj : ∀ i j, ∃ x ∈ (A i).verts, ∃ y ∈ (B' j).verts, G.Adj x y := by
    intro i j
    exact ⟨v i j, hv_mem_A i j, u i j, ⟨hu_mem_B i j, hu_not_S i j⟩, (hB_le j).2 (huv_adj i j)⟩
  have hlt := theorem_4_1_simple heven hG_fin hG A B' hA_le hB'_le hA_conn hB'_conn
    hA_disj hB'_disj hAB'_disj hAB'_adj
  omega

end GraphMinor.GM05
