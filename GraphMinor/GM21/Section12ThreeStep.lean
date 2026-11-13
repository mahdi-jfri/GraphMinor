module

public import GraphMinor.GM21.Section12ThreeCount
public import GraphMinor.GM21.Section12ThreeTwo

/-!
# Graph Minors XXI, (12.3): step (3) and the proof

Step (3) of the proof of (12.3): the components of `T \ N(T)` are paths, and putting them one after
another gives a path `P`. With the bags `W(t)` for `t ∈ V(P)`, made smaller by deleting the set `Z`
of the vertices of the bags at `N(T)`, this is a path-decomposition of `G \ Z`.

We order `V(T) \ N(T)` so that each component of `T \ N(T)` comes in one block, in its order along
the path (`exists_order`). Instead of deleting `Z` and adding it back afterwards, we add to every
bag `W(t)` the union `W(N(T))` of the bags at `N(T)`; this gives the path-decomposition of `G` of
width `≤ w' + |Z|` that the paper's last sentence speaks of (`pathWidthLE21_of_treeDecomp`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## An order of `V(T) \ N(T)` -/

section Order

variable {κ : Type*} [Fintype κ] {T : SimpleGraph κ}

/-- Every nonempty set `S` of vertices of a tree has a vertex with at most one neighbour in `S`:
take a vertex of `S` farthest from a fixed vertex `r` of `S`. -/
theorem exists_end (hT : T.IsTree) {S : Set κ} (hS : S.Nonempty) :
    ∃ v ∈ S, (T.neighborSet v ∩ S).ncard ≤ 1 := by
  classical
  obtain ⟨r, hr⟩ := hS
  obtain ⟨y, hyS, hymax⟩ := (toFinite S).toFinset.exists_max_image
    (fun y ↦ {x | Thomas.OnTreePath T r y x}.ncard) ⟨r, (toFinite S).mem_toFinset.2 hr⟩
  rw [Finite.mem_toFinset] at hyS
  -- Every neighbour of `y` in `S` is on the path from `y` to `r`.
  have key : ∀ z, z ∈ T.neighborSet y ∩ S → Thomas.OnTreePath T y r z := by
    rintro z ⟨hyz, hzS⟩
    rcases Thomas.onTreePath_adj_dichotomy hT hyz r with ⟨h1, -⟩ | ⟨h1, -⟩
    · exfalso
      have := hymax z ((toFinite S).mem_toFinset.2 hzS)
      refine absurd this (not_le.2 (ncard_lt_ncard
        ⟨fun x hx ↦ Thomas.onTreePath_trans_left hT h1 hx, fun hsub ↦ hyz.ne ?_⟩ (toFinite _)))
      exact (Thomas.onTreePath_antisymm hT (hsub (Thomas.onTreePath_right T r z)) h1).symm
    · exact Thomas.onTreePath_symm h1
  exact ⟨y, hyS, (ncard_le_one_iff (toFinite _)).2 fun ha hb ↦
    eq_of_adj_of_onTreePath hT ha.1 hb.1 (key _ ha) (key _ hb)⟩

/-- The order property: if the path of `T` between `σ i` and `σ k` lies in `S`, then every `σ j`
with `i ≤ j ≤ k` is on it. -/
def IsGoodOrder (T : SimpleGraph κ) (S : Set κ) {M : ℕ} (σ : Fin M → κ) : Prop :=
  ∀ i j k : Fin M, i ≤ j → j ≤ k → (∀ x, Thomas.OnTreePath T (σ i) (σ k) x → x ∈ S) →
    Thomas.OnTreePath T (σ i) (σ k) (σ j)

/-- If `v` is on the path between `a` and `b`, and is neither of them, then `v` has two neighbours
on this path. -/
theorem exists_two_adj_of_onTreePath (hT : T.IsTree) {a b v : κ}
    (hv : Thomas.OnTreePath T a b v) (hva : v ≠ a) (hvb : v ≠ b) :
    ∃ z₁ z₂, z₁ ≠ z₂ ∧ T.Adj v z₁ ∧ T.Adj v z₂ ∧ Thomas.OnTreePath T a b z₁ ∧
      Thomas.OnTreePath T a b z₂ := by
  obtain ⟨z₁, h₁, hz₁⟩ := exists_adj_onTreePath hT hva
  obtain ⟨z₂, h₂, hz₂⟩ := exists_adj_onTreePath hT hvb
  refine ⟨z₁, z₂, ?_, h₁, h₂, Thomas.onTreePath_trans_left hT hv (Thomas.onTreePath_symm hz₁),
    Thomas.onTreePath_trans_right hT hv hz₂⟩
  rintro rfl
  exact h₁.ne (Thomas.onTreePath_inter_eq_of_onTreePath hT hv (Thomas.onTreePath_symm hz₁) hz₂).symm

/-- **The order of step (3).** Let `S` be a set of `n + 1` vertices of a tree, each with at most two
neighbours in `S`, and let `v ∈ S` have at most one neighbour in `S`. Then `S` can be listed as
`σ 0 = v, σ 1, …, σ n` with the order property. We list `v` first, and then the rest, starting from
the neighbour of `v` in `S` if there is one. -/
theorem exists_order (hT : T.IsTree) : ∀ (n : ℕ) (S : Set κ), S.ncard = n + 1 →
    (∀ x ∈ S, (T.neighborSet x ∩ S).ncard ≤ 2) → ∀ v ∈ S, (T.neighborSet v ∩ S).ncard ≤ 1 →
    ∃ σ : Fin (n + 1) → κ, σ 0 = v ∧ Function.Injective σ ∧ (∀ i, σ i ∈ S) ∧
      IsGoodOrder T S σ := by
  classical
  intro n
  induction n with
  | zero =>
    intro S hS _ v hv _
    obtain ⟨a, rfl⟩ := ncard_eq_one.1 hS
    obtain rfl : v = a := hv
    refine ⟨fun _ ↦ v, rfl, fun i j _ ↦ Fin.ext (by have := i.2; have := j.2; omega), fun _ ↦ rfl, ?_⟩
    intro i j k _ _ _
    exact Thomas.onTreePath_left T _ _
  | succ n ih =>
    intro S hS hdeg v hv hv1
    set S' := S \ {v}
    have hS' : S'.ncard = n + 1 := by
      rw [ncard_sdiff_singleton_of_mem hv, hS]; rfl
    have hdeg' : ∀ x ∈ S', (T.neighborSet x ∩ S').ncard ≤ 2 := fun x hx ↦
      (ncard_le_ncard (inter_subset_inter_right _ sdiff_subset) (toFinite _)).trans (hdeg x hx.1)
    -- The vertex `u` that comes after `v`.
    obtain ⟨u, huS', hu1, hvu⟩ : ∃ u ∈ S', (T.neighborSet u ∩ S').ncard ≤ 1 ∧
        ∀ z, T.Adj v z → z ∈ S → z = u := by
      by_cases hn : ∃ z, T.Adj v z ∧ z ∈ S
      · obtain ⟨z, hvz, hzS⟩ := hn
        refine ⟨z, ⟨hzS, hvz.ne'⟩, ?_, fun z' hvz' hz'S ↦
          (ncard_le_one_iff (toFinite _)).1 hv1 ⟨hvz', hz'S⟩ ⟨hvz, hzS⟩⟩
        have hsub : T.neighborSet z ∩ S' ⊆ (T.neighborSet z ∩ S) \ {v} :=
          fun x hx ↦ ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩
        have hvmem : v ∈ T.neighborSet z ∩ S := ⟨hvz.symm, hv⟩
        have := ncard_le_ncard hsub (toFinite _)
        rw [ncard_sdiff_singleton_of_mem hvmem] at this
        have := hdeg z hzS
        omega
      · push Not at hn
        have hne : S'.Nonempty := by
          rw [← ncard_pos (toFinite _), hS']; omega
        obtain ⟨u, hu, hu1⟩ := exists_end hT hne
        exact ⟨u, hu, hu1, fun z hz hzS ↦ absurd hzS (hn z hz)⟩
    obtain ⟨σ', hσ'0, hσ'inj, hσ'S, hσ'good⟩ := ih S' hS' hdeg' u huS' hu1
    have hvσ' : ∀ i, σ' i ≠ v := fun i h ↦ (hσ'S i).2 h
    refine ⟨Fin.cons v σ', rfl, ?_, ?_, ?_⟩
    · exact Fin.cons_injective_iff.2 ⟨fun ⟨i, h⟩ ↦ hvσ' i h, hσ'inj⟩
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · exact hv
      · exact (hσ'S i).1
    -- The order property.
    intro i j k hij hjk hpath
    -- A path in `S` that avoids `v` lies in `S'`.
    have hS'of : ∀ a b, (∀ x, Thomas.OnTreePath T a b x → x ∈ S) → a ≠ v → b ≠ v →
        ∀ x, Thomas.OnTreePath T a b x → x ∈ S' := by
      intro a b hab hav hbv x hx
      refine ⟨hab x hx, fun hxv ↦ ?_⟩
      rw [mem_singleton_iff] at hxv
      subst hxv
      obtain ⟨z₁, z₂, hz, h₁, h₂, hz₁, hz₂⟩ := exists_two_adj_of_onTreePath hT hx hav.symm hbv.symm
      exact hz ((ncard_le_one_iff (toFinite _)).1 hv1 ⟨h₁, hab _ hz₁⟩ ⟨h₂, hab _ hz₂⟩)
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
      · obtain rfl : j = 0 := le_antisymm hjk hij
        exact Thomas.onTreePath_left T _ _
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · exact Thomas.onTreePath_left T _ _
      simp only [Fin.cons_zero, Fin.cons_succ] at hpath ⊢
      -- The path from `v` to `σ' k` starts with `u`.
      obtain ⟨z, hvz, hz⟩ := exists_adj_onTreePath hT (hvσ' k).symm
      obtain rfl := hvu z hvz (hpath z hz)
      rw [← hσ'0] at hz
      have hpath' := hS'of (σ' 0) (σ' k)
        (fun x hx ↦ hpath x (Thomas.onTreePath_trans_right hT hz hx)) (hvσ' 0) (hvσ' k)
      exact Thomas.onTreePath_trans_right hT hz
        (hσ'good 0 j k (Fin.zero_le _) (Fin.succ_le_succ_iff.1 hjk) hpath')
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 (ne_of_gt (lt_of_lt_of_le (Fin.succ_pos i) hij))
      obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 (ne_of_gt (lt_of_lt_of_le (Fin.succ_pos j) hjk))
      simp only [Fin.cons_succ] at hpath ⊢
      exact hσ'good i j k (Fin.succ_le_succ_iff.1 hij) (Fin.succ_le_succ_iff.1 hjk)
        (hS'of _ _ hpath (hvσ' i) (hvσ' k))

end Order

/-! ## The path-decomposition -/

section PathDecomp

/-- In `pathGraph L`, a vertex on the path between `a` and `b` lies between them. -/
theorem between_of_onTreePath_pathGraph {L : ℕ} {a b c : Fin L}
    (h : Thomas.OnTreePath (pathGraph L) a b c) :
    (a.1 ≤ c.1 ∧ c.1 ≤ b.1) ∨ (b.1 ≤ c.1 ∧ c.1 ≤ a.1) := by
  rw [Thomas.onTreePath_iff_forall_walk] at h
  rcases le_total a.1 b.1 with hab | hba
  · obtain ⟨p, hp⟩ := exists_bounded_walk_pathGraph a b hab
    exact Or.inl (hp c (h p))
  · obtain ⟨p, hp⟩ := exists_bounded_walk_pathGraph b a hba
    exact Or.inr (hp c (by simpa using h p.reverse))

/-- `pathGraph (M + 1)` is a path. -/
theorem isPathTree_pathGraph (M : ℕ) : IsPathTree (pathGraph (M + 1)) := by
  refine ⟨isTree_pathGraph M, fun i ↦ ?_⟩
  refine (ncard_le_ncard_of_injOn (fun j : Fin (M + 1) ↦ j.1) (t := {i.1 - 1, i.1 + 1}) ?_
    Fin.val_injective.injOn (toFinite _)).trans ((ncard_insert_le _ _).trans (by simp))
  intro j hj
  rw [mem_neighborSet, pathGraph_adj] at hj
  simp only [mem_insert_iff, mem_singleton_iff]
  omega

/-- **Step (3) of the proof of (12.3).** A tree-decomposition of width `≤ w` whose tree has maximum
degree `≤ 3` gives a path-decomposition of width `≤ w + |N(T)| (w + 1)`. The path runs through the
vertices of `T` not in `N(T)`, in the order of `exists_order`, and the bag at `t` is `W(t)` together
with all bags at `N(T)`. -/
theorem pathWidthLE21_of_treeDecomp {κ : Type} [Fintype κ] {G : Hypergraph α β}
    {T : SimpleGraph κ} {W : κ → Hypergraph α β} (h : IsTreeDecomp21 G T W) {w : ℕ}
    (hw : ∀ t, (W t).vertexSet.ncard ≤ w + 1) (hdeg : ∀ t, (T.neighborSet t).ncard ≤ 3) :
    PathWidthLE21 G (w + (branchSet T).ncard * (w + 1)) := by
  classical
  have hT := h.isTree
  set N := branchSet T with hN_def
  set S : Set κ := Nᶜ with hS_def
  have hS2 : ∀ x ∈ S, (T.neighborSet x ∩ S).ncard ≤ 2 := fun x hx ↦ by
    have h1 := ncard_le_ncard (inter_subset_left : T.neighborSet x ∩ S ⊆ _) (toFinite _)
    have h2 := hdeg x
    have h3 : (T.neighborSet x).ncard ≠ 3 := hx
    omega
  have hSne : S.Nonempty := by
    obtain ⟨v, -, hv⟩ := exists_end hT (S := univ) ⟨hT.connected.nonempty.some, mem_univ _⟩
    refine ⟨v, fun hvN ↦ ?_⟩
    rw [inter_univ] at hv
    have : (T.neighborSet v).ncard = 3 := hvN
    omega
  obtain ⟨v, hvS, hv1⟩ := exists_end hT hSne
  obtain ⟨n, hn⟩ : ∃ n, S.ncard = n + 1 :=
    ⟨S.ncard - 1, by have := (ncard_pos (toFinite _)).2 hSne; omega⟩
  obtain ⟨σ, -, hinj, hσS, hgood⟩ := exists_order hT n S hn hS2 v hvS hv1
  have hsurj : ∀ t ∈ S, ∃ i, σ i = t := by
    have hsub : range σ ⊆ S := range_subset_iff.2 hσS
    have heq : range σ = S := eq_of_subset_of_ncard_le hsub
      (by rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin, hn])
      (toFinite _)
    intro t ht
    rw [← heq] at ht
    exact ht
  set Z := bagUnion W (· ∈ N) with hZ_def
  have hZG : Z ≤ G := GM10.biUnion_le_of_le fun t _ ↦ h.le t
  set U : Fin (n + 1) → Hypergraph α β := fun i ↦ W (σ i) ∪ Z with hU_def
  have hUG : ∀ i, U i ≤ G := fun i ↦ GM10.union_le (h.le _) hZG
  -- Between `σ i` and `σ k` on `P`: what two bags share is in the bag between, or in `W(N(T))`.
  have hkey : ∀ i j k : Fin (n + 1), ((i ≤ j ∧ j ≤ k) ∨ (k ≤ j ∧ j ≤ i)) →
      ∀ Q : κ → Prop, (∀ s s' t, Thomas.OnTreePath T s s' t → Q s → Q s' → Q t) →
      Q (σ i) → Q (σ k) → Q (σ j) ∨ ∃ t ∈ N, Q t := by
    intro i j k hjb Q hQ hi hk
    by_cases hp : ∀ x, Thomas.OnTreePath T (σ i) (σ k) x → x ∈ S
    · left
      rcases hjb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hQ _ _ _ (hgood i j k h1 h2 hp) hi hk
      · exact hQ _ _ _ (hgood k j i h1 h2 fun x hx ↦ hp x (Thomas.onTreePath_symm hx)) hk hi
    · right
      push Not at hp
      obtain ⟨x, hx, hxN⟩ := hp
      exact ⟨x, by simpa [hS_def] using hxN, hQ _ _ _ hx hi hk⟩
  have hQv : ∀ y : α, ∀ s s' t, Thomas.OnTreePath T s s' t → y ∈ (W s).vertexSet →
      y ∈ (W s').vertexSet → y ∈ (W t).vertexSet := fun y s s' t hst h1 h2 ↦
    (h.inter_le hst).vertexSet_subset ⟨h1, h2⟩
  have hQe : ∀ e : β, ∀ s s' t, Thomas.OnTreePath T s s' t → e ∈ (W s).edgeSet →
      e ∈ (W s').edgeSet → e ∈ (W t).edgeSet := fun e s s' t hst h1 h2 ↦
    (h.inter_le hst).edgeSet_subset ⟨h1, h2⟩
  refine ⟨Fin (n + 1), inferInstance, pathGraph (n + 1), U,
    ⟨isTree_pathGraph n, hUG, ?_, ?_⟩, isPathTree_pathGraph n, ?_⟩
  · -- Every vertex and edge of `G` is in some bag.
    refine le_antisymm (GM10.biUnion_le_of_le fun i _ ↦ hUG i) ?_
    have hG : ∀ (x : α), x ∈ G.vertexSet → ∃ t, x ∈ (W t).vertexSet := fun x hx ↦ by
      rw [← h.biUnion_eq] at hx
      simpa [Hypergraph.biUnion] using hx
    have hGe : ∀ (e : β), e ∈ G.edgeSet → ∃ t, e ∈ (W t).edgeSet := fun e he ↦ by
      rw [← h.biUnion_eq] at he
      simpa [Hypergraph.biUnion] using he
    refine le_of_subset_of_le le_rfl (GM10.biUnion_le_of_le fun i _ ↦ hUG i) ?_ ?_
    · intro x hx
      obtain ⟨t, hxt⟩ := hG x hx
      simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion]
      by_cases htN : t ∈ N
      · exact ⟨0, Or.inr (mem_bagUnion_vertexSet.2 ⟨t, htN, hxt⟩)⟩
      · obtain ⟨i, rfl⟩ := hsurj t htN
        exact ⟨i, Or.inl hxt⟩
    · intro e he
      obtain ⟨t, het⟩ := hGe e he
      simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion]
      by_cases htN : t ∈ N
      · exact ⟨0, Or.inr (mem_bagUnion_edgeSet.2 ⟨t, htN, het⟩)⟩
      · obtain ⟨i, rfl⟩ := hsurj t htN
        exact ⟨i, Or.inl het⟩
  · -- The bags along `P` have the tree-decomposition property.
    intro i j k hp
    have hjb : (i ≤ j ∧ j ≤ k) ∨ (k ≤ j ∧ j ≤ i) := by
      rcases between_of_onTreePath_pathGraph hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Fin.le_iff_val_le_val.2 h1, Fin.le_iff_val_le_val.2 h2⟩
      · exact Or.inr ⟨Fin.le_iff_val_le_val.2 h1, Fin.le_iff_val_le_val.2 h2⟩
    refine le_of_subset_of_le (GM10.inter_le (hUG i) (hUG k)) (hUG j) ?_ ?_
    · rintro y ⟨hyi | hyi, hyk | hyk⟩
      · rcases hkey i j k hjb _ (hQv y) hyi hyk with h' | ⟨t, htN, hyt⟩
        · exact Or.inl h'
        · exact Or.inr (mem_bagUnion_vertexSet.2 ⟨t, htN, hyt⟩)
      all_goals exact Or.inr ‹_›
    · rintro e ⟨hei | hei, hek | hek⟩
      · rcases hkey i j k hjb _ (hQe e) hei hek with h' | ⟨t, htN, het⟩
        · exact Or.inl h'
        · exact Or.inr (mem_bagUnion_edgeSet.2 ⟨t, htN, het⟩)
      all_goals exact Or.inr ‹_›
  · -- The width.
    intro i
    have hZV : Z.vertexSet ⊆ ⋃ t : N, (W t).vertexSet := fun y hy ↦ by
      obtain ⟨t, htN, hyt⟩ := mem_bagUnion_vertexSet.1 hy
      exact mem_iUnion.2 ⟨⟨t, htN⟩, hyt⟩
    have hZn : Z.vertexSet.ncard ≤ N.ncard * (w + 1) := by
      refine (ncard_le_ncard hZV (finite_iUnion fun t : N ↦ (W t.1).vertexSet_finite)).trans ((ncard_iUnion_le_of_fintype _).trans ?_)
      refine (Finset.sum_le_sum fun t _ ↦ hw t.1).trans ?_
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq]
    have := (ncard_union_le (W (σ i)).vertexSet Z.vertexSet).trans
      (Nat.add_le_add (hw (σ i)) hZn)
    change (W (σ i) ∪ Z).vertexSet.ncard ≤ _
    change ((W (σ i)).vertexSet ∪ Z.vertexSet).ncard ≤ _
    omega

/-- A tree-decomposition can be made into one with no edge in two bags, with the same vertex
sets and smaller edge sets: each edge stays in one bag that contains it. -/
theorem exists_trim {ι : Type*} [Fintype ι] {G : Hypergraph α β} {T : SimpleGraph ι}
    {W : ι → Hypergraph α β} (h : IsTreeDecomp21 G T W) :
    ∃ W' : ι → Hypergraph α β, GM10.IsTreeDecomposition G T W' ∧
      (∀ t, (W' t).vertexSet = (W t).vertexSet) ∧ ∀ t, (W' t).edgeSet ⊆ (W t).edgeSet := by
  classical
  have t₀ : ι := h.isTree.connected.nonempty.some
  let c : β → ι := fun e ↦ if he : ∃ t, e ∈ (W t).edgeSet then he.choose else t₀
  have hc : ∀ e t, e ∈ (W t).edgeSet → e ∈ (W (c e)).edgeSet := fun e t het ↦ by
    have he : ∃ t, e ∈ (W t).edgeSet := ⟨t, het⟩
    simp only [c, he, dite_true]
    exact he.choose_spec
  let W' : ι → Hypergraph α β := fun t ↦
    { vertexSet := (W t).vertexSet
      edgeSet := {e ∈ (W t).edgeSet | c e = t}
      Inc := fun e x ↦ (W t).Inc e x ∧ c e = t
      vertex_mem_of_inc := fun _ _ hx ↦ (W t).vertex_mem_of_inc hx.1
      edge_mem_of_inc := fun _ _ hx ↦ ⟨(W t).edge_mem_of_inc hx.1, hx.2⟩
      vertexSet_finite := (W t).vertexSet_finite
      edgeSet_finite := (W t).edgeSet_finite.subset fun _ he ↦ he.1 }
  have hW'W : ∀ t, W' t ≤ W t := fun t ↦
    ⟨subset_rfl, fun _ he ↦ he.1, fun e he ↦ by
      ext x
      simp only [ends, mem_ofPred_eq, W']
      exact ⟨fun hx ↦ ⟨hx, he.2⟩, fun hx ↦ hx.1⟩⟩
  have hW'G : ∀ t, W' t ≤ G := fun t ↦ (hW'W t).trans (h.le t)
  refine ⟨W', ⟨h.isTree, hW'G, ?_, ?_, ?_⟩, fun _ ↦ rfl, fun _ _ he ↦ he.1⟩
  · refine le_antisymm (GM10.biUnion_le_of_le fun t _ ↦ hW'G t) ?_
    refine le_of_subset_of_le le_rfl (GM10.biUnion_le_of_le fun t _ ↦ hW'G t) ?_ ?_
    · intro x hx
      rw [← h.biUnion_eq] at hx
      simpa [Hypergraph.biUnion, W'] using hx
    · intro e he
      rw [← h.biUnion_eq] at he
      simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion] at he ⊢
      obtain ⟨t, het⟩ := he
      exact ⟨c e, hc e t het, rfl⟩
  · intro t t' htt'
    refine eq_empty_of_forall_notMem fun e ⟨he, he'⟩ ↦ htt' ?_
    exact he.2.symm.trans he'.2
  · intro t t' t'' hp
    refine le_of_subset_of_le (GM10.inter_le (hW'G t) (hW'G t'')) (hW'G t') ?_ ?_
    · rintro x ⟨hx, hx'⟩
      exact (h.inter_le hp).vertexSet_subset ⟨hx, hx'⟩
    · rintro e ⟨⟨he, hce⟩, ⟨he', hce'⟩⟩
      obtain rfl : t = t'' := hce.symm.trans hce'
      obtain rfl : t' = t := (Thomas.onTreePath_self T t t').1 hp
      exact ⟨he, hce⟩

/-- **Graph Minors XXI, (12.3)**, in the form used by `theorem_12_3`. -/
theorem theorem_12_3_proof (p : ℕ) :
    ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph →
      HasVitalPLinkage G p → PathWidthLE21 G w := by
  obtain ⟨w', hw'⟩ := Final.hypergraph_treeWidthPlusOne_le_of_hasVitalPLinkage.{u, v} p
  obtain ⟨n, hn⟩ := exists_isSixBound.{u, v} p (w' + 1)
  refine ⟨w' + 2 ^ n * (w' + 1), ?_⟩
  intro α β G hG ⟨L, hL⟩
  classical
  have htw := hw' G hG ⟨L, hL⟩
  -- Choose `(T, W)` with `|N(T)|` smallest.
  have hQ : ∃ N, ∃ (κ : Type) (_ : Fintype κ) (T : SimpleGraph κ) (W : κ → Hypergraph α β),
      IsGoodDecomp G w' T W ∧ (branchSet T).ncard = N := by
    obtain ⟨κ, _, T, W, h1, h2, h3, h4⟩ := exists_good_treeDecomposition hG htw
    exact ⟨_, κ, inferInstance, T, W, ⟨h1.isTreeDecomp21, h2, h3, h4⟩, rfl⟩
  obtain ⟨κ, _, T, W, ⟨h, hlink, hw, hdeg⟩, hcard⟩ := Nat.find_spec hQ
  have hmin : ∀ (κ' : Type) (_ : Fintype κ') (T' : SimpleGraph κ') (W' : κ' → Hypergraph α β),
      IsGoodDecomp G w' T' W' → (branchSet T).ncard ≤ (branchSet T').ncard :=
    fun κ' _ T' W' hg ↦ hcard ▸ Nat.find_min' hQ ⟨κ', inferInstance, T', W', hg, rfl⟩
  -- Make it a decomposition with no edge in two bags; the vertex sets stay the same.
  obtain ⟨W₀, hTD, hV, -⟩ := exists_trim h
  have hE : ∀ {u v : κ}, T.Adj u v → treeEdgeSet T W₀ u v = treeEdgeSet T W u v := fun huv ↦ by
    rw [hTD.isTreeDecomp21.treeEdgeSet_eq huv, h.treeEdgeSet_eq huv, hV, hV]
  have hlink₀ : IsLinkedTreeDecomp G T W₀ := by
    intro a₁ b₁ a₂ b₂ h₁ h₂ hb₁ ha₂ k hk₁ hk₂ hpath
    rw [hE h₁] at hk₁
    rw [hE h₂] at hk₂
    rw [hE h₁, hE h₂]
    exact hlink h₁ h₂ hb₁ ha₂ k hk₁ hk₂ fun s s' hss ↦ hE hss.1 ▸ hpath hss
  have hw₀ : ∀ t, (W₀ t).vertexSet.ncard ≤ w' + 1 := fun t ↦ hV t ▸ hw t
  -- Claim (2), and the bound on `|N(T)|`.
  have h2 := claim_12_3_two hG hTD hlink₀ hw₀ hdeg hmin hL hn
  have hN := ncard_branchSet_le h.isTree hdeg h2
  -- Step (3).
  obtain ⟨κ', _, P, U, hP, hPP, hU⟩ := pathWidthLE21_of_treeDecomp h hw hdeg
  refine ⟨κ', inferInstance, P, U, hP, hPP, fun t ↦ (hU t).trans ?_⟩
  have := Nat.mul_le_mul_right (w' + 1) hN
  omega

end PathDecomp

end GM21
end GraphMinor
