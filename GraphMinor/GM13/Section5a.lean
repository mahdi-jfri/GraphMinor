module

public import GraphMinor.GM13.Section2
public import Mathlib.Combinatorics.Hall.Finite

/-!
# Graph Minors XIII, Section 5 (Part A): (5.1), (5.2), and the Base Case of (5.3)

This file formalizes N. Robertson and P. D. Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110, Section 5 (pages 78–82):

- `theorem_5_1` ((5.1), page 78)
- `theorem_5_2` ((5.2), page 79)
- `theorem_5_3_base_matching` (Claims (3) and (4) of (5.3), pages 81–82)
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface

universe u v w

variable {α : Type u} {β : Type v}

/-- Helper: if `A` and `B` are finite sets with `A.ncard + 2 * B.ncard ≤ C.ncard` and `C.Finite`,
there is an injective function `A ⊕ (B × Bool) → C`. -/
lemma exists_inj_sum_prod_bool {α₁ α₂ α₃ : Type*} {A : Set α₁} {B : Set α₂} {C : Set α₃}
    (hA : A.Finite) (hB : B.Finite) (hC : C.Finite)
    (hcard : A.ncard + 2 * B.ncard ≤ C.ncard) :
    ∃ emb : A ⊕ (B × Bool) → C, Function.Injective emb := by
  have _ : Fintype A := hA.fintype
  have _ : Fintype B := hB.fintype
  have _ : Fintype C := hC.fintype
  have hcardA : Fintype.card A = A.ncard := (Nat.card_eq_fintype_card).symm.trans (ncard_def A).symm
  have hcardB : Fintype.card B = B.ncard := (Nat.card_eq_fintype_card).symm.trans (ncard_def B).symm
  have hcardC : Fintype.card C = C.ncard := (Nat.card_eq_fintype_card).symm.trans (ncard_def C).symm
  have hcardDom : Fintype.card (A ⊕ (B × Bool)) ≤ Fintype.card C := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, hcardA, hcardB, hcardC]
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcardDom
  exact ⟨f, f.injective⟩

/-- **Graph Minors XIII, (5.1)** (page 78):
"Let $G$ be a digraph with $|V(G)| \ge 2\xi + 3\delta$, and let $Z \subseteq V(G)$ with
$|Z| = \xi$. Suppose that $u, v \in Z$, for all distinct $u, v \in V$ that are non-adjacent in $G$.
Then the $\delta$-folio of $G$ relative to $Z$ is generic." -/
theorem theorem_5_1_proof [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ δ : ℕ}
    (hfin : G.vertexSet.Finite) (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard = ξ)
    (hVcard : 2 * ξ + 3 * δ ≤ G.vertexSet.ncard)
    (hadj : ∀ ⦃u v : α⦄, u ∈ G.vertexSet → v ∈ G.vertexSet → u ≠ v →
      ¬ G.toGraph.Adj u v → u ∈ Z ∧ v ∈ Z) :
    IsGenericDeltaFolioRel G δ Z := by
  have hZfin : Z.Finite := hfin.subset hZ
  refine ⟨hZ, hZfin, fun k v hv hinj hrange => ⟨hinj, fun H hHfin hHdet => ?_⟩⟩
  refine ⟨⟨hHfin, ?_⟩, hHdet⟩
  -- Following the paper's proof on page 78:
  have hk_eq : k = ξ := by
    have h1 : (Set.range v).ncard = k := by
      rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hrange, hZcard] at h1
    exact h1.symm
  have hHE_le : H.digraph.edgeSet.ncard ≤ δ :=
    le_trans (le_max_left _ _) hHdet
  have hHVdiff_le : (H.digraph.vertexSet \ Set.range H.roots).ncard ≤ δ :=
    le_trans (le_max_right _ _) hHdet
  have hHroots_le : (Set.range H.roots).ncard ≤ ξ := by
    have hle : (Set.range H.roots).ncard ≤ (Set.univ : Set (Fin k)).ncard := by
      rw [← Set.image_univ]
      exact ncard_image_le (Set.finite_univ)
    rw [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
    omega
  have hHV_le : H.digraph.vertexSet.ncard ≤ ξ + δ := by
    have hunion : H.digraph.vertexSet ⊆
        (H.digraph.vertexSet \ Set.range H.roots) ∪ Set.range H.roots := by
      intro x hx
      by_cases hxr : x ∈ Set.range H.roots
      · exact Or.inr hxr
      · exact Or.inl ⟨hx, hxr⟩
    have h1 : H.digraph.vertexSet.ncard ≤
        ((H.digraph.vertexSet \ Set.range H.roots) ∪ Set.range H.roots).ncard :=
      ncard_le_ncard hunion ((hHfin.finite_V.sdiff).union (Set.finite_range _))
    have h2 : ((H.digraph.vertexSet \ Set.range H.roots) ∪ Set.range H.roots).ncard ≤
        (H.digraph.vertexSet \ Set.range H.roots).ncard + (Set.range H.roots).ncard :=
      ncard_union_le _ _
    omega
  have hGZdiff_card : ξ + 3 * δ ≤ (G.vertexSet \ Z).ncard := by
    have h1 : (G.vertexSet \ Z).ncard + Z.ncard = G.vertexSet.ncard :=
      ncard_sdiff_add_ncard_of_subset hZ hfin
    omega
  have hDom_le : H.digraph.vertexSet.ncard + 2 * H.digraph.edgeSet.ncard ≤ (G.vertexSet \ Z).ncard := by
    omega
  obtain ⟨emb, hemb⟩ := exists_inj_sum_prod_bool hHfin.finite_V hHfin.finite_E hfin.sdiff hDom_le
  -- For each `u ∈ V(H)`, `x_u = emb (inl u) ∈ V(G) \ Z`
  let xOf (u : H.digraph.vertexSet) : α := (emb (Sum.inl u)).1
  have hxOf_mem (u : H.digraph.vertexSet) : xOf u ∈ G.vertexSet \ Z := (emb (Sum.inl u)).2
  -- For each `e ∈ E(H)`, `p_e = emb (inr (e, true))` and `q_e = emb (inr (e, false))`
  let pOf (e : H.digraph.edgeSet) : α := (emb (Sum.inr (e, true))).1
  let qOf (e : H.digraph.edgeSet) : α := (emb (Sum.inr (e, false))).1
  have hpOf_mem (e : H.digraph.edgeSet) : pOf e ∈ G.vertexSet \ Z := (emb (Sum.inr (e, true))).2
  have hqOf_mem (e : H.digraph.edgeSet) : qOf e ∈ G.vertexSet \ Z := (emb (Sum.inr (e, false))).2
  have hpq_ne (e : H.digraph.edgeSet) : pOf e ≠ qOf e := by
    intro heq
    have hsub : emb (Sum.inr (e, true)) = emb (Sum.inr (e, false)) := Subtype.ext heq
    have hinr := hemb hsub
    injection hinr with hprod
    injection hprod with _ hbool
    exact Bool.noConfusion hbool
  have hpq_adj (e : H.digraph.edgeSet) : G.toGraph.Adj (pOf e) (qOf e) := by
    by_contra hnot
    have hZboth := hadj (hpOf_mem e).1 (hqOf_mem e).1 (hpq_ne e) hnot
    exact (hpOf_mem e).2 hZboth.1
  -- Choose a non-loop edge `ϕ(e)` linking `pOf e` and `qOf e`
  let eChoice (e : H.digraph.edgeSet) :
      {f : β // f ∈ G.edgeSet ∧
        ((G.head f = pOf e ∧ G.tail f = qOf e) ∨ (G.head f = qOf e ∧ G.tail f = pOf e))} :=
    Classical.indefiniteDescription _ (by
      rcases hpq_adj e with ⟨f, hf⟩
      exact ⟨f, hf.1, hf.2⟩)
  let eMap (e : ℕ) : β :=
    if he : e ∈ H.digraph.edgeSet then (eChoice ⟨e, he⟩).1 else Classical.arbitrary β
  -- Head `s_e` and tail `t_e` of `ϕ(e)`
  let sOf (e : H.digraph.edgeSet) : α := G.head (eChoice e).1
  let tOf (e : H.digraph.edgeSet) : α := G.tail (eChoice e).1
  have hsOf_eq (e : H.digraph.edgeSet) : sOf e = pOf e ∨ sOf e = qOf e := by
    rcases (eChoice e).2.2 with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have htOf_eq (e : H.digraph.edgeSet) : tOf e = pOf e ∨ tOf e = qOf e := by
    rcases (eChoice e).2.2 with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact Or.inr h2
    · exact Or.inl h2
  have hst_pair (e : H.digraph.edgeSet) :
      ({sOf e, tOf e} : Set α) = {pOf e, qOf e} := by
    rcases (eChoice e).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · dsimp [sOf, tOf]; rw [h1, h2]
    · dsimp [sOf, tOf]; rw [h1, h2, Set.pair_comm]
  -- Define `X_u` and `W_u` for each `u ∈ V(H)`
  let XSet (u : ℕ) : Set α :=
    (if hu : u ∈ H.digraph.vertexSet then {xOf ⟨u, hu⟩} else ∅) ∪
      {z : α | ∃ i : Fin k, H.roots i = u ∧ v i = z}
  let WSet (u : ℕ) : Set α :=
    XSet u ∪
      {z : α | ∃ e : H.digraph.edgeSet, H.digraph.head e.1 = u ∧ sOf e = z} ∪
      {z : α | ∃ e : H.digraph.edgeSet, H.digraph.tail e.1 = u ∧ tOf e = z}
  let usedEdges : Set β := eMap '' H.digraph.edgeSet
  let vMap (u : ℕ) : Digraph α β :=
    G.subdigraphOf (WSet u) (G.edgeSet \ usedEdges)
  refine ⟨vMap, eMap, ?_⟩
  have hW_sub (u : ℕ) (hu : u ∈ H.digraph.vertexSet) : WSet u ⊆ G.vertexSet := by
    rintro z ((hzX | ⟨e, _, rfl⟩) | ⟨e, _, rfl⟩)
    · rcases hzX with hzx | ⟨i, _, rfl⟩
      · simp only [hu, ↓reduceDIte, mem_singleton_iff] at hzx
        subst hzx
        exact (hxOf_mem ⟨u, hu⟩).1
      · exact hv i
    · exact G.head_mem (eChoice e).2.1
    · exact G.tail_mem (eChoice e).2.1
  have hvMap_V (u : ℕ) (hu : u ∈ H.digraph.vertexSet) :
      (vMap u).vertexSet = WSet u := by
    exact inter_eq_self_of_subset_right (hW_sub u hu)
  have hx_not_in_st (u : H.digraph.vertexSet) (e : H.digraph.edgeSet) :
      xOf u ∉ ({sOf e, tOf e} : Set α) := by
    rw [hst_pair e]
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro h
      have hsub : emb (Sum.inl u) = emb (Sum.inr (e, true)) := Subtype.ext h
      have hinj' := hemb hsub
      nomatch hinj'
    · intro h
      have hsub : emb (Sum.inl u) = emb (Sum.inr (e, false)) := Subtype.ext h
      have hinj' := hemb hsub
      nomatch hinj'
  have hst_disj (e e' : H.digraph.edgeSet) (hne : e ≠ e') :
      Disjoint ({sOf e, tOf e} : Set α) ({sOf e', tOf e'} : Set α) := by
    rw [hst_pair e, hst_pair e', Set.disjoint_iff]
    rintro z ⟨hz1, hz2⟩
    rcases hz1 with rfl | rfl <;> rcases hz2 with h | h
    · have hsub : emb (Sum.inr (e, true)) = emb (Sum.inr (e', true)) := Subtype.ext h
      have hinj' := hemb hsub
      injection hinj' with hp; injection hp with he_eq _; exact hne he_eq
    · have hsub : emb (Sum.inr (e, true)) = emb (Sum.inr (e', false)) := Subtype.ext h
      have hinj' := hemb hsub
      injection hinj' with hp; injection hp with he_eq _; exact hne he_eq
    · have hsub : emb (Sum.inr (e, false)) = emb (Sum.inr (e', true)) := Subtype.ext h
      have hinj' := hemb hsub
      injection hinj' with hp; injection hp with he_eq _; exact hne he_eq
    · have hsub : emb (Sum.inr (e, false)) = emb (Sum.inr (e', false)) := Subtype.ext h
      have hinj' := hemb hsub
      injection hinj' with hp; injection hp with he_eq _; exact hne he_eq
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- sub_of_mem
    intro u _
    exact Digraph.subdigraphOf_isSubdigraph _ _ _
  · -- connected_of_mem
    intro u hu
    have hx_mem : xOf ⟨u, hu⟩ ∈ (vMap u).vertexSet := by
      rw [hvMap_V u hu]
      left; left; left
      simp only [hu, ↓reduceDIte, mem_singleton_iff]
    have hadj_x : ∀ w ∈ (vMap u).vertexSet, Nonempty (GraphWalk (vMap u).toGraph (xOf ⟨u, hu⟩) w) := by
      intro w hw
      by_cases hwx : w = xOf ⟨u, hu⟩
      · subst hwx
        exact ⟨.nil hx_mem⟩
      · have hwG : w ∈ G.vertexSet := hW_sub u hu ((hvMap_V u hu) ▸ hw)
        have hxG : xOf ⟨u, hu⟩ ∈ G.vertexSet := (hxOf_mem ⟨u, hu⟩).1
        have hxNotZ : xOf ⟨u, hu⟩ ∉ Z := (hxOf_mem ⟨u, hu⟩).2
        have hadjG : G.toGraph.Adj (xOf ⟨u, hu⟩) w := by
          by_contra hnot
          exact hxNotZ (hadj hxG hwG (Ne.symm hwx) hnot).1
        rcases hadjG with ⟨f, hfE, hflink⟩
        have hf_not_used : f ∉ usedEdges := by
          rintro ⟨e', he'H, rfl⟩
          have he'eq : eMap e' = (eChoice ⟨e', he'H⟩).1 := by
            dsimp [eMap]; simp only [he'H, ↓reduceDIte]
          rw [he'eq] at hflink
          have hx_in_st : xOf ⟨u, hu⟩ ∈ ({sOf ⟨e', he'H⟩, tOf ⟨e', he'H⟩} : Set α) := by
            rcases hflink with ⟨h1, _⟩ | ⟨_, h1⟩
            · exact Or.inl h1.symm
            · exact Or.inr h1.symm
          exact hx_not_in_st ⟨u, hu⟩ ⟨e', he'H⟩ hx_in_st
        have hflink_vMap : (vMap u).toGraph.IsLink f (xOf ⟨u, hu⟩) w := by
          have hwW : w ∈ WSet u := (hvMap_V u hu) ▸ hw
          have hxW : xOf ⟨u, hu⟩ ∈ WSet u := (hvMap_V u hu) ▸ hx_mem
          rcases hflink with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨⟨⟨hfE, hfE, hf_not_used⟩, h1.symm ▸ hxW, h2.symm ▸ hwW⟩, Or.inl ⟨h1, h2⟩⟩
          · exact ⟨⟨⟨hfE, hfE, hf_not_used⟩, h1.symm ▸ hwW, h2.symm ▸ hxW⟩, Or.inr ⟨h1, h2⟩⟩
        exact ⟨.cons hflink_vMap (.nil hw)⟩
    refine ⟨⟨xOf ⟨u, hu⟩, hx_mem⟩, fun w₁ hw₁ w₂ hw₂ => ?_⟩
    rcases hadj_x w₁ hw₁ with ⟨W₁⟩
    rcases hadj_x w₂ hw₂ with ⟨W₂⟩
    exact ⟨GraphWalk.append (GraphWalk.reverse W₁) W₂⟩
  · -- disjoint_of_ne
    intro u₁ u₂ hu₁ hu₂ hne
    rw [hvMap_V u₁ hu₁, hvMap_V u₂ hu₂, Set.disjoint_iff]
    rintro z ⟨hz₁, hz₂⟩
    have hz₁_cases : z = xOf ⟨u₁, hu₁⟩ ∨ (∃ i : Fin k, H.roots i = u₁ ∧ v i = z) ∨
        (∃ e : H.digraph.edgeSet, (H.digraph.head e.1 = u₁ ∧ sOf e = z) ∨
          (H.digraph.tail e.1 = u₁ ∧ tOf e = z)) := by
      rcases hz₁ with ((hzx | hzr) | ⟨e, hh, rfl⟩) | ⟨e, ht, rfl⟩
      · simp only [hu₁, ↓reduceDIte, mem_singleton_iff] at hzx
        exact Or.inl hzx
      · exact Or.inr (Or.inl hzr)
      · exact Or.inr (Or.inr ⟨e, Or.inl ⟨hh, rfl⟩⟩)
      · exact Or.inr (Or.inr ⟨e, Or.inr ⟨ht, rfl⟩⟩)
    have hz₂_cases : z = xOf ⟨u₂, hu₂⟩ ∨ (∃ i : Fin k, H.roots i = u₂ ∧ v i = z) ∨
        (∃ e : H.digraph.edgeSet, (H.digraph.head e.1 = u₂ ∧ sOf e = z) ∨
          (H.digraph.tail e.1 = u₂ ∧ tOf e = z)) := by
      rcases hz₂ with ((hzx | hzr) | ⟨e, hh, rfl⟩) | ⟨e, ht, rfl⟩
      · simp only [hu₂, ↓reduceDIte, mem_singleton_iff] at hzx
        exact Or.inl hzx
      · exact Or.inr (Or.inl hzr)
      · exact Or.inr (Or.inr ⟨e, Or.inl ⟨hh, rfl⟩⟩)
      · exact Or.inr (Or.inr ⟨e, Or.inr ⟨ht, rfl⟩⟩)
    rcases hz₁_cases with rfl | ⟨i₁, hr₁, rfl⟩ | ⟨e₁, he₁⟩
    · rcases hz₂_cases with h | ⟨i₂, _, hv₂⟩ | ⟨e₂, ⟨_, hs₂⟩ | ⟨_, ht₂⟩⟩
      · have hsub : emb (Sum.inl ⟨u₁, hu₁⟩) = emb (Sum.inl ⟨u₂, hu₂⟩) := Subtype.ext h
        have hinj' := hemb hsub
        injection hinj' with hu_eq
        exact hne (congrArg Subtype.val hu_eq)
      · apply (hxOf_mem ⟨u₁, hu₁⟩).2
        rw [← hrange]
        exact ⟨i₂, hv₂⟩
      · exact hx_not_in_st ⟨u₁, hu₁⟩ e₂ (Or.inl hs₂.symm)
      · exact hx_not_in_st ⟨u₁, hu₁⟩ e₂ (Or.inr ht₂.symm)
    · rcases hz₂_cases with h | ⟨i₂, hr₂, hv₂⟩ | ⟨e₂, ⟨_, hs₂⟩ | ⟨_, ht₂⟩⟩
      · apply (hxOf_mem ⟨u₂, hu₂⟩).2
        rw [← hrange, ← h]
        exact ⟨i₁, rfl⟩
      · have hi_eq : i₁ = i₂ := hinj hv₂.symm
        subst hi_eq
        exact hne (hr₁.symm.trans hr₂)
      · have hsZ : sOf e₂ ∉ Z := by
          rcases hsOf_eq e₂ with h | h <;> rw [h]
          · exact (hpOf_mem e₂).2
          · exact (hqOf_mem e₂).2
        apply hsZ
        rw [hs₂, ← hrange]
        exact ⟨i₁, rfl⟩
      · have htZ : tOf e₂ ∉ Z := by
          rcases htOf_eq e₂ with h | h <;> rw [h]
          · exact (hpOf_mem e₂).2
          · exact (hqOf_mem e₂).2
        apply htZ
        rw [ht₂, ← hrange]
        exact ⟨i₁, rfl⟩
    · rcases hz₂_cases with h | ⟨i₂, _, hv₂⟩ | ⟨e₂, he₂⟩
      · rcases he₁ with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact hx_not_in_st ⟨u₂, hu₂⟩ e₁ (Or.inl h.symm)
        · exact hx_not_in_st ⟨u₂, hu₂⟩ e₁ (Or.inr h.symm)
      · rcases he₁ with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · have hsZ : sOf e₁ ∉ Z := by
            rcases hsOf_eq e₁ with h | h <;> rw [h]
            · exact (hpOf_mem e₁).2
            · exact (hqOf_mem e₁).2
          apply hsZ
          rw [← hv₂, ← hrange]
          exact ⟨i₂, rfl⟩
        · have htZ : tOf e₁ ∉ Z := by
            rcases htOf_eq e₁ with h | h <;> rw [h]
            · exact (hpOf_mem e₁).2
            · exact (hqOf_mem e₁).2
          apply htZ
          rw [← hv₂, ← hrange]
          exact ⟨i₂, rfl⟩
      · by_cases he_eq : e₁ = e₂
        · subst he_eq
          have hst_ne : sOf e₁ ≠ tOf e₁ := by
            intro hst
            rcases (eChoice e₁).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact hpq_ne e₁ (h1.symm.trans (hst.trans h2))
            · exact hpq_ne e₁ (h2.symm.trans (hst.symm.trans h1))
          rcases he₁ with ⟨hh₁, rfl⟩ | ⟨ht₁, rfl⟩ <;> rcases he₂ with ⟨hh₂, hs₂⟩ | ⟨ht₂, ht₂_eq⟩
          · exact hne (hh₁.symm.trans hh₂)
          · exact hst_ne ht₂_eq.symm
          · exact hst_ne hs₂
          · exact hne (ht₁.symm.trans ht₂)
        · have hmem₁ : z ∈ ({sOf e₁, tOf e₁} : Set α) := by
            rcases he₁ with ⟨_, rfl⟩ | ⟨_, rfl⟩
            · exact Or.inl rfl
            · exact Or.inr rfl
          have hmem₂ : z ∈ ({sOf e₂, tOf e₂} : Set α) := by
            rcases he₂ with ⟨_, hs₂⟩ | ⟨_, ht₂⟩
            · exact Or.inl hs₂.symm
            · exact Or.inr ht₂.symm
          exact Set.disjoint_iff.mp (hst_disj e₁ e₂ he_eq) ⟨hmem₁, hmem₂⟩
  · -- edge_mem
    intro e he
    dsimp [eMap]
    simp only [he, ↓reduceDIte]
    exact (eChoice ⟨e, he⟩).2.1
  · -- head_tail_mem
    intro e he
    have heMap : eMap e = (eChoice ⟨e, he⟩).1 := by
      dsimp [eMap]; simp only [he, ↓reduceDIte]
    rw [heMap]
    constructor
    · rw [hvMap_V (H.digraph.head e) (H.digraph.head_mem he)]
      left; right
      exact ⟨⟨e, he⟩, rfl, rfl⟩
    · rw [hvMap_V (H.digraph.tail e) (H.digraph.tail_mem he)]
      right
      exact ⟨⟨e, he⟩, rfl, rfl⟩
  · -- loop_not_mem
    intro e he _ hmem
    exact hmem.1.2.2 ⟨e, he, rfl⟩
  · -- eMap_injOn
    intro e₁ he₁ e₂ he₂ heq
    by_contra hne
    have hne_sub : (⟨e₁, he₁⟩ : H.digraph.edgeSet) ≠ ⟨e₂, he₂⟩ := fun h => hne (congrArg Subtype.val h)
    have he₁Map : eMap e₁ = (eChoice ⟨e₁, he₁⟩).1 := by
      dsimp [eMap]; simp only [he₁, ↓reduceDIte]
    have he₂Map : eMap e₂ = (eChoice ⟨e₂, he₂⟩).1 := by
      dsimp [eMap]; simp only [he₂, ↓reduceDIte]
    have hf_eq : (eChoice ⟨e₁, he₁⟩).1 = (eChoice ⟨e₂, he₂⟩).1 :=
      he₁Map.symm.trans (heq.trans he₂Map)
    have hs_eq : sOf ⟨e₁, he₁⟩ = sOf ⟨e₂, he₂⟩ := congrArg G.head hf_eq
    exact Set.disjoint_iff.mp (hst_disj ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ hne_sub)
      ⟨Or.inl rfl, Or.inl hs_eq⟩
  · -- root_mem
    intro i
    rw [hvMap_V (H.roots i) (H.roots_mem i)]
    left; left; right
    exact ⟨i, rfl, rfl⟩

/-- Lift a walk in the contracted graph `G'` (whose vertices are indices `i < k` representing
mutually vertex-disjoint connected subdigraphs `sub i` of `G`) to a walk in `G`. -/
lemma lift_contracted_walk {k : ℕ} {G : Digraph α β} {sub : Fin k → Digraph α β}
    (hconn : ∀ i, (sub i).IsConnected)
    {G' : Digraph ℕ β}
    (hE'_ends : ∀ ⦃e : β⦄, e ∈ G'.edgeSet →
      ∃ (i j : Fin k), G'.head e = i.1 ∧ G'.tail e = j.1 ∧
        e ∈ G.edgeSet ∧ G.head e ∈ (sub i).vertexSet ∧ G.tail e ∈ (sub j).vertexSet)
    {M' : Digraph ℕ β} (hM' : M'.IsSubdigraph G')
    {M : Digraph α β}
    (hME_sub : ∀ (i : Fin k), i.1 ∈ M'.vertexSet → (sub i).IsSubdigraph M)
    (hME_edge : ∀ ⦃e : β⦄, e ∈ M'.edgeSet → e ∈ M.edgeSet)
    (hM_subG : M.IsSubdigraph G)
    {a b : ℕ} (W' : GraphWalk M'.toGraph a b) :
    ∀ (ia ib : Fin k), ia.1 = a → ib.1 = b →
      ∀ x ∈ (sub ia).vertexSet, ∀ y ∈ (sub ib).vertexSet,
        Nonempty (GraphWalk M.toGraph x y) := by
  induction W' with
  | nil ha =>
    intro ia ib hia hib x hx y hy
    have hi_eq : ia = ib := Fin.ext (hia.trans hib.symm)
    subst hi_eq
    rcases (hconn ia).2 x hx y hy with ⟨W₀⟩
    exact ⟨(hME_sub ia (hia ▸ ha)).mapWalk W₀⟩
  | @cons u v w e hlink rest ih =>
    intro ia ic hia hic x hx z hz
    have huM' : u ∈ M'.vertexSet := M'.toGraph.left_mem_of_isLink hlink
    have hvM' : v ∈ M'.vertexSet := M'.toGraph.left_mem_of_isLink hlink.symm
    have heM' : e ∈ M'.edgeSet := hlink.1
    have heG' : e ∈ G'.edgeSet := hM'.edgeSet_subset heM'
    obtain ⟨ihead, itail, hhead', htail', heG, hheadG, htailG⟩ := hE'_ends heG'
    have hheadM' : M'.head e = ihead.1 := (hM'.head_eq heM').trans hhead'
    have htailM' : M'.tail e = itail.1 := (hM'.tail_eq heM').trans htail'
    have heM : e ∈ M.edgeSet := hME_edge heM'
    rcases hlink.2 with ⟨hu_eq, hv_eq⟩ | ⟨hu_eq, hv_eq⟩
    · -- `M'.head e = u` and `M'.tail e = v`
      have hia_eq : ia = ihead := Fin.ext (hia.trans (hu_eq.symm.trans hheadM'))
      subst hia_eq
      have hib_val : itail.1 = v := htailM'.symm.trans hv_eq
      rcases (hconn ia).2 x hx (G.head e) hheadG with ⟨W₁⟩
      have hW₁' : GraphWalk M.toGraph x (G.head e) :=
        (hME_sub ia (hia ▸ huM')).mapWalk W₁
      have hlinkM : M.toGraph.IsLink e (G.head e) (G.tail e) :=
        ⟨heM, Or.inl ⟨hM_subG.head_eq heM, hM_subG.tail_eq heM⟩⟩
      rcases ih itail ic hib_val hic (G.tail e) htailG z hz with ⟨W₂⟩
      exact ⟨GraphWalk.append hW₁' (.cons hlinkM W₂)⟩
    · -- `M'.head e = v` and `M'.tail e = u`
      have hia_eq : ia = itail := Fin.ext (hia.trans (hv_eq.symm.trans htailM'))
      subst hia_eq
      have hib_val : ihead.1 = v := hheadM'.symm.trans hu_eq
      rcases (hconn ia).2 x hx (G.tail e) htailG with ⟨W₁⟩
      have hW₁' : GraphWalk M.toGraph x (G.tail e) :=
        (hME_sub ia (hia ▸ huM')).mapWalk W₁
      have hlinkM : M.toGraph.IsLink e (G.tail e) (G.head e) :=
        ⟨heM, Or.inr ⟨hM_subG.head_eq heM, hM_subG.tail_eq heM⟩⟩
      rcases ih ihead ic hib_val hic (G.head e) hheadG z hz with ⟨W₂⟩
      exact ⟨GraphWalk.append hW₁' (.cons hlinkM W₂)⟩

/-- **Graph Minors XIII, (5.2)** (pages 78–79):
"*Let $G$ be a digraph, let $Z \subseteq V(G)$ with $|Z| = \xi$, and let $k = 2\xi + 3\delta$.
Suppose that there are $k$ non-null connected subgraphs $G_1, \dots, G_k$ of $G$, mutually
vertex-disjoint, such that*

(i) *$|Z \cap V(G_i)| = 1$ ($1 \le i \le \xi$), and (hence) $Z \cap V(G_i) = \emptyset$ ($\xi + 1
\le i \le k$)*
…
(ii) *for $1 \le i < j \le k$, if there is no edge of $G$ between $G_i$ and $G_j$ then $i, j \le
\xi$.*

*Then the $\delta$-folio of $G$ relative to $Z$ is generic.*" -/
theorem theorem_5_2_proof [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ δ k : ℕ}
    (hZ : Z ⊆ G.vertexSet) (hZfin : Z.Finite) (hZcard : Z.ncard = ξ)
    (hk : k = 2 * ξ + 3 * δ)
    {sub : Fin k → Digraph α β}
    (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hconn : ∀ i : Fin k, (sub i).IsConnected)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hZi : ∀ i : Fin k, i.1 < ξ → (Z ∩ (sub i).vertexSet).ncard = 1)
    (hZempty : ∀ i : Fin k, ξ ≤ i.1 → Z ∩ (sub i).vertexSet = ∅)
    (hadj : ∀ i j : Fin k, i < j → ¬ G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet →
      i.1 < ξ ∧ j.1 < ξ) :
    IsGenericDeltaFolioRel G δ Z := by
  -- Follow the paper's proof on page 79: contract each `G_i` to a vertex `i < k` of `G'`.
  have hξ_le_k : ξ ≤ k := by omega
  -- Every vertex belongs to at most one `sub i`
  have hsub_unique : ∀ ⦃x : α⦄ ⦃i j : Fin k⦄,
      x ∈ (sub i).vertexSet → x ∈ (sub j).vertexSet → i = j := by
    intro x i j hxi hxj
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) hxi hxj
  -- Define the contracted digraph `G' : Digraph ℕ β` on `{0, ..., k - 1}`
  let E' : Set β :=
    {e ∈ G.edgeSet | ∃ i j : Fin k, i ≠ j ∧
      G.head e ∈ (sub i).vertexSet ∧ G.tail e ∈ (sub j).vertexSet}
  let head' (e : β) : ℕ :=
    if h : ∃ i : Fin k, G.head e ∈ (sub i).vertexSet then (Classical.choose h).1 else 0
  let tail' (e : β) : ℕ :=
    if h : ∃ j : Fin k, G.tail e ∈ (sub j).vertexSet then (Classical.choose h).1 else 0
  have hhead'_eq : ∀ ⦃e : β⦄ ⦃i : Fin k⦄, G.head e ∈ (sub i).vertexSet → head' e = i.1 := by
    intro e i hi
    have hex : ∃ i' : Fin k, G.head e ∈ (sub i').vertexSet := ⟨i, hi⟩
    dsimp [head']
    simp only [hex, ↓reduceDIte]
    exact congrArg Fin.val (hsub_unique (Classical.choose_spec hex) hi)
  have htail'_eq : ∀ ⦃e : β⦄ ⦃j : Fin k⦄, G.tail e ∈ (sub j).vertexSet → tail' e = j.1 := by
    intro e j hj
    have hex : ∃ j' : Fin k, G.tail e ∈ (sub j').vertexSet := ⟨j, hj⟩
    dsimp [tail']
    simp only [hex, ↓reduceDIte]
    exact congrArg Fin.val (hsub_unique (Classical.choose_spec hex) hj)
  let G' : Digraph ℕ β := {
    vertexSet := {n : ℕ | n < k}
    edgeSet := E'
    head := head'
    tail := tail'
    head_mem := fun e he => by
      rcases he.2 with ⟨i, _, _, hi, _⟩
      show head' e < k
      rw [hhead'_eq hi]
      exact i.2
    tail_mem := fun e he => by
      rcases he.2 with ⟨_, j, _, _, hj⟩
      show tail' e < k
      rw [htail'_eq hj]
      exact j.2
  }
  let Z' : Set ℕ := {n : ℕ | n < ξ}
  have hG'fin : G'.vertexSet.Finite := Set.finite_lt_nat k
  have hZ'sub : Z' ⊆ G'.vertexSet := fun n hn => lt_of_lt_of_le hn hξ_le_k
  have hG'card : G'.vertexSet.ncard = k := by
    have heq : G'.vertexSet = Set.range (Fin.val : Fin k → ℕ) := by
      ext n
      exact ⟨fun hn => ⟨⟨n, hn⟩, rfl⟩, by rintro ⟨i, rfl⟩; exact i.2⟩
    rw [heq, ncard_range_of_injective Fin.val_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hZ'card : Z'.ncard = ξ := by
    have heq : Z' = Set.range (Fin.val : Fin ξ → ℕ) := by
      ext n
      exact ⟨fun hn => ⟨⟨n, hn⟩, rfl⟩, by rintro ⟨i, rfl⟩; exact i.2⟩
    rw [heq, ncard_range_of_injective Fin.val_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hG'Vcard : 2 * ξ + 3 * δ ≤ G'.vertexSet.ncard := by omega
  have hG'adj : ∀ ⦃u v : ℕ⦄, u ∈ G'.vertexSet → v ∈ G'.vertexSet → u ≠ v →
      ¬ G'.toGraph.Adj u v → u ∈ Z' ∧ v ∈ Z' := by
    intro u v hu hv hne hnotAdj
    let iu : Fin k := ⟨u, hu⟩
    let iv : Fin k := ⟨v, hv⟩
    have huv_ne : iu ≠ iv := fun h => hne (congrArg Fin.val h)
    have hnoEdge : ¬ G.HasEdgeBetween (sub iu).vertexSet (sub iv).vertexSet := by
      rintro ⟨e, heG, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · apply hnotAdj
        refine ⟨e, ⟨heG, iu, iv, huv_ne, h1, h2⟩, Or.inl ⟨hhead'_eq h1, htail'_eq h2⟩⟩
      · apply hnotAdj
        refine ⟨e, ⟨heG, iv, iu, huv_ne.symm, h1, h2⟩, Or.inr ⟨hhead'_eq h1, htail'_eq h2⟩⟩
    rcases lt_or_gt_of_ne huv_ne with hlt | hgt
    · exact hadj iu iv hlt hnoEdge
    · have hnoEdge' : ¬ G.HasEdgeBetween (sub iv).vertexSet (sub iu).vertexSet := by
        rintro ⟨e, heG, h⟩
        exact hnoEdge ⟨e, heG, h.symm⟩
      exact (hadj iv iu hgt hnoEdge').symm
  -- Apply (5.1) to `G'` and `Z'`
  have hGen' : IsGenericDeltaFolioRel G' δ Z' :=
    theorem_5_1_proof hG'fin hZ'sub hZ'card hG'Vcard hG'adj
  -- Each `i < ξ` has a unique vertex `zOf i ∈ Z ∩ V(G_i)`
  have hz_exists : ∀ (i : Fin k), i.1 < ξ → ∃ z, Z ∩ (sub i).vertexSet = {z} :=
    fun i hi => ncard_eq_one.mp (hZi i hi)
  -- The union of `Z ∩ V(G_i)` over `i < ξ` equals `Z`
  have hZ_union : (⋃ i : Fin k, Z ∩ (sub i).vertexSet) = Z := by
    have hunion_sub : (⋃ i : Fin k, Z ∩ (sub i).vertexSet) ⊆ Z :=
      iUnion_subset (fun _ => inter_subset_left)
    have hcard_eq : (⋃ i : Fin k, Z ∩ (sub i).vertexSet).ncard = Z.ncard := by
      let f (i : Fin ξ) : α :=
        Classical.choose (hz_exists ⟨i.1, lt_of_lt_of_le i.2 hξ_le_k⟩ i.2)
      have hf_mem (i : Fin ξ) :
          f i ∈ Z ∩ (sub ⟨i.1, lt_of_lt_of_le i.2 hξ_le_k⟩).vertexSet := by
        have hspec := Classical.choose_spec (hz_exists ⟨i.1, lt_of_lt_of_le i.2 hξ_le_k⟩ i.2)
        rw [hspec]
        exact mem_singleton _
      have hf_inj : Function.Injective f := by
        intro i₁ i₂ heq
        have h1 := (hf_mem i₁).2
        have h2 : f i₁ ∈ (sub ⟨i₂.1, lt_of_lt_of_le i₂.2 hξ_le_k⟩).vertexSet := heq ▸ (hf_mem i₂).2
        have hfin_eq := hsub_unique h1 h2
        have hval_eq : i₁.1 = i₂.1 := congrArg (Fin.val : Fin k → ℕ) hfin_eq
        exact Fin.ext hval_eq
      have hrange_sub : Set.range f ⊆ (⋃ i : Fin k, Z ∩ (sub i).vertexSet) := by
        rintro x ⟨i, rfl⟩
        exact mem_iUnion.mpr ⟨⟨i.1, lt_of_lt_of_le i.2 hξ_le_k⟩, hf_mem i⟩
      have hle1 : ξ ≤ (⋃ i : Fin k, Z ∩ (sub i).vertexSet).ncard := by
        have hrcard : (Set.range f).ncard = ξ := by
          rw [ncard_range_of_injective hf_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
        rw [← hrcard]
        exact ncard_le_ncard hrange_sub (hZfin.subset hunion_sub)
      have hle2 : (⋃ i : Fin k, Z ∩ (sub i).vertexSet).ncard ≤ Z.ncard :=
        ncard_le_ncard hunion_sub hZfin
      omega
    exact eq_of_subset_of_ncard_le hunion_sub (ge_of_eq hcard_eq) hZfin
  refine ⟨hZ, hZfin, fun k₀ v hv hinj hrange => ⟨hinj, fun H hHfin hHdet => ?_⟩⟩
  -- Map each root `r : Fin k₀` to the unique `i : Fin k` with `v r ∈ (sub i).vertexSet`
  have hvr_in_sub (r : Fin k₀) : ∃ i : Fin k, v r ∈ Z ∩ (sub i).vertexSet := by
    have hvrZ : v r ∈ Z := hrange ▸ ⟨r, rfl⟩
    rw [← hZ_union, mem_iUnion] at hvrZ
    exact hvrZ
  let idxOf (r : Fin k₀) : Fin k := Classical.choose (hvr_in_sub r)
  have hidx_mem (r : Fin k₀) : v r ∈ Z ∩ (sub (idxOf r)).vertexSet :=
    Classical.choose_spec (hvr_in_sub r)
  have hidx_lt_ξ (r : Fin k₀) : (idxOf r).1 < ξ := by
    by_contra hge
    have hemp := hZempty (idxOf r) (le_of_not_gt hge)
    have hmem := hidx_mem r
    rw [hemp] at hmem
    exact hmem
  let v' (r : Fin k₀) : ℕ := (idxOf r).1
  have hv'G' (r : Fin k₀) : v' r ∈ G'.vertexSet := (idxOf r).2
  have hv'_inj : Function.Injective v' := by
    intro r₁ r₂ heq
    have hidx_eq : idxOf r₁ = idxOf r₂ := Fin.ext heq
    have hspec := Classical.choose_spec (hz_exists (idxOf r₁) (hidx_lt_ξ r₁))
    have hm₁ : v r₁ ∈ ({Classical.choose (hz_exists (idxOf r₁) (hidx_lt_ξ r₁))} : Set α) :=
      hspec ▸ hidx_mem r₁
    have hm₂ : v r₂ ∈ ({Classical.choose (hz_exists (idxOf r₁) (hidx_lt_ξ r₁))} : Set α) :=
      hspec ▸ (hidx_eq ▸ hidx_mem r₂)
    exact hinj (hm₁.trans hm₂.symm)
  have hv'_range : Set.range v' = Z' := by
    have hsub' : Set.range v' ⊆ Z' := by
      rintro n ⟨r, rfl⟩
      exact hidx_lt_ξ r
    have hk₀_eq : k₀ = ξ := by
      have h1 : (Set.range v).ncard = k₀ := by
        rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [hrange, hZcard] at h1
      exact h1.symm
    have hrcard : (Set.range v').ncard = Z'.ncard := by
      rw [ncard_range_of_injective hv'_inj, Nat.card_eq_fintype_card, Fintype.card_fin, hk₀_eq, hZ'card]
    exact eq_of_subset_of_ncard_le hsub' (ge_of_eq hrcard) (hG'fin.subset hZ'sub)
  -- Obtain a rooted model `(vMap', eMap')` of `H` in `(G', v')`
  have hIn' : (RootedDigraph.mk G' v' hv'G').InDeltaFolio δ H :=
    (hGen'.2.2 k₀ v' hv'G' hv'_inj hv'_range).2 H hHfin hHdet
  rcases hIn'.1.2 with ⟨vMap', eMap', hM'⟩
  -- Lift `(vMap', eMap')` to `(vMap, eMap')` in `G`
  let liftV (u : ℕ) : Set α :=
    ⋃ (i : Fin k) (_ : i.1 ∈ (vMap' u).vertexSet), (sub i).vertexSet
  let liftE (u : ℕ) : Set β :=
    (vMap' u).edgeSet ∪ ⋃ (i : Fin k) (_ : i.1 ∈ (vMap' u).vertexSet), (sub i).edgeSet
  let vMap (u : ℕ) : Digraph α β := G.subdigraphOf (liftV u) (liftE u)
  refine ⟨⟨hHfin, vMap, eMap', ?_⟩, hHdet⟩
  have hliftV_sub (u : ℕ) : liftV u ⊆ G.vertexSet := by
    rintro x ⟨_, ⟨i, rfl⟩, _, ⟨_, rfl⟩, hx⟩
    exact (hsub i).vertexSet_subset hx
  have hvMap_V (u : ℕ) : (vMap u).vertexSet = liftV u :=
    inter_eq_self_of_subset_right (hliftV_sub u)
  have hE'_ends : ∀ ⦃e : β⦄, e ∈ G'.edgeSet →
      ∃ (i j : Fin k), G'.head e = i.1 ∧ G'.tail e = j.1 ∧
        e ∈ G.edgeSet ∧ G.head e ∈ (sub i).vertexSet ∧ G.tail e ∈ (sub j).vertexSet := by
    intro e he
    rcases he.2 with ⟨i, j, _, hi, hj⟩
    exact ⟨i, j, hhead'_eq hi, htail'_eq hj, he.1, hi, hj⟩
  have hsub_isSub (u : ℕ) (i : Fin k)
      (hi : i.1 ∈ (vMap' u).vertexSet) : (sub i).IsSubdigraph (vMap u) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [hvMap_V u]
      exact mem_biUnion hi hx
    · intro e heSub
      have heG : e ∈ G.edgeSet := (hsub i).edgeSet_subset heSub
      have hhead_mem : G.head e ∈ liftV u :=
        mem_biUnion hi ((hsub i).head_eq heSub ▸ (sub i).head_mem heSub)
      have htail_mem : G.tail e ∈ liftV u :=
        mem_biUnion hi ((hsub i).tail_eq heSub ▸ (sub i).tail_mem heSub)
      exact ⟨⟨heG, Or.inr (mem_biUnion hi heSub)⟩, hhead_mem, htail_mem⟩
    · intro e heSub
      exact (hsub i).head_eq heSub
    · intro e heSub
      exact (hsub i).tail_eq heSub
  have hM'_edge_mem (u : ℕ) (hu : u ∈ H.digraph.vertexSet) ⦃e : β⦄
      (he : e ∈ (vMap' u).edgeSet) : e ∈ (vMap u).edgeSet := by
    have hsubM' := hM'.sub_of_mem hu
    have heG' : e ∈ G'.edgeSet := hsubM'.edgeSet_subset he
    obtain ⟨i, j, hhead', htail', heG, hi, hj⟩ := hE'_ends heG'
    have hi_mem : i.1 ∈ (vMap' u).vertexSet := by
      rw [← hhead', ← hsubM'.head_eq he]
      exact (vMap' u).head_mem he
    have hj_mem : j.1 ∈ (vMap' u).vertexSet := by
      rw [← htail', ← hsubM'.tail_eq he]
      exact (vMap' u).tail_mem he
    exact ⟨⟨heG, Or.inl he⟩, mem_biUnion hi_mem hi, mem_biUnion hj_mem hj⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- sub_of_mem
    intro u _
    exact Digraph.subdigraphOf_isSubdigraph _ _ _
  · -- connected_of_mem
    intro u hu
    have hconn' := hM'.connected_of_mem hu
    have hsubM' := hM'.sub_of_mem hu
    rcases hconn'.1 with ⟨n₀, hn₀⟩
    have hn₀_lt : n₀ < k := hsubM'.vertexSet_subset hn₀
    rcases (hconn ⟨n₀, hn₀_lt⟩).1 with ⟨x₀, hx₀⟩
    refine ⟨⟨x₀, ?_⟩, fun x hx y hy => ?_⟩
    · rw [hvMap_V u]
      exact mem_biUnion hn₀ hx₀
    · rw [hvMap_V u] at hx hy
      rcases mem_iUnion₂.mp hx with ⟨ia, hia, hxa⟩
      rcases mem_iUnion₂.mp hy with ⟨ib, hib, hyb⟩
      rcases hconn'.2 ia.1 hia ib.1 hib with ⟨W'⟩
      exact lift_contracted_walk hconn hE'_ends hsubM'
        (hsub_isSub u) (hM'_edge_mem u hu)
        (Digraph.subdigraphOf_isSubdigraph _ _ _) W' ia ib rfl rfl x hxa y hyb
  · -- disjoint_of_ne
    intro u₁ u₂ hu₁ hu₂ hne
    rw [hvMap_V u₁, hvMap_V u₂, Set.disjoint_iff]
    rintro x ⟨hx₁, hx₂⟩
    rcases mem_iUnion₂.mp hx₁ with ⟨i₁, hi₁, hxi₁⟩
    rcases mem_iUnion₂.mp hx₂ with ⟨i₂, hi₂, hxi₂⟩
    have hi_eq : i₁ = i₂ := hsub_unique hxi₁ hxi₂
    subst hi_eq
    exact Set.disjoint_left.mp (hM'.disjoint_of_ne hu₁ hu₂ hne) hi₁ hi₂
  · -- edge_mem
    intro e he
    exact (hM'.edge_mem he).1
  · -- head_tail_mem
    intro e he
    have heG' := hM'.edge_mem he
    obtain ⟨i, j, hhead', htail', _, hi, hj⟩ := hE'_ends heG'
    have hht' := hM'.head_tail_mem he
    change G'.head (eMap' e) ∈ _ ∧ G'.tail (eMap' e) ∈ _ at hht'
    rw [hhead', htail'] at hht'
    rw [hvMap_V (H.digraph.head e), hvMap_V (H.digraph.tail e)]
    exact ⟨mem_biUnion hht'.1 hi, mem_biUnion hht'.2 hj⟩
  · -- loop_not_mem
    intro e he hloop hmem
    have heG' := hM'.edge_mem he
    rcases heG'.2 with ⟨i, j, hij_ne, hi, hj⟩
    rcases hmem.1.2 with he_vMap' | he_sub
    · exact hM'.loop_not_mem he hloop he_vMap'
    · rcases mem_iUnion₂.mp he_sub with ⟨m, _, hem⟩
      have hhead_m : G.head (eMap' e) ∈ (sub m).vertexSet :=
        (hsub m).head_eq hem ▸ (sub m).head_mem hem
      have htail_m : G.tail (eMap' e) ∈ (sub m).vertexSet :=
        (hsub m).tail_eq hem ▸ (sub m).tail_mem hem
      have him : i = m := hsub_unique hi hhead_m
      have hjm : j = m := hsub_unique hj htail_m
      exact hij_ne (him.trans hjm.symm)
  · -- eMap_injOn
    exact hM'.eMap_injOn
  · -- root_mem
    intro r
    rw [hvMap_V (H.roots r)]
    exact mem_biUnion (hM'.root_mem r) (hidx_mem r).2


/-- Given a single vertex `x ∈ G.vertexSet`, the 1-vertex edgeless subdigraph `{x}` of `G`. -/
def Digraph.singletonSub (G : Digraph α β) (x : α) : Digraph α β :=
  G.subdigraphOf {x} ∅

lemma Digraph.singletonSub_vertexSet {G : Digraph α β} {x : α} (hx : x ∈ G.vertexSet) :
    (G.singletonSub x).vertexSet = {x} :=
  inter_eq_self_of_subset_right (singleton_subset_iff.mpr hx)

lemma Digraph.singletonSub_isSubdigraph (G : Digraph α β) (x : α) :
    (G.singletonSub x).IsSubdigraph G :=
  Digraph.subdigraphOf_isSubdigraph G {x} ∅

lemma Digraph.singletonSub_isConnected {G : Digraph α β} {x : α} (hx : x ∈ G.vertexSet) :
    (G.singletonSub x).IsConnected := by
  have hV := G.singletonSub_vertexSet hx
  refine ⟨⟨x, hV ▸ mem_singleton x⟩, fun u hu v hv => ?_⟩
  have hu' : u = x := by rw [hV, mem_singleton_iff] at hu; exact hu
  have hv' : v = x := by rw [hV, mem_singleton_iff] at hv; exact hv
  subst hu' hv'
  exact ⟨.nil hu⟩

/-- Given an edge `e ∈ G.edgeSet` linking `x` and `y`, the subdigraph of `G` with vertex set
`{x, y}` and edge set `{e}`. -/
def Digraph.edgeSub (G : Digraph α β) (x y : α) (e : β) : Digraph α β :=
  G.subdigraphOf {x, y} {e}

lemma Digraph.edgeSub_vertexSet {G : Digraph α β} {x y : α} {e : β}
    (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet) :
    (G.edgeSub x y e).vertexSet = {x, y} := by
  apply inter_eq_self_of_subset_right
  rintro z (rfl | rfl) <;> assumption

lemma Digraph.edgeSub_isSubdigraph (G : Digraph α β) (x y : α) (e : β) :
    (G.edgeSub x y e).IsSubdigraph G :=
  Digraph.subdigraphOf_isSubdigraph G {x, y} {e}

lemma Digraph.edgeSub_isConnected {G : Digraph α β} {x y : α} {e : β}
    (hlink : G.toGraph.IsLink e x y) :
    (G.edgeSub x y e).IsConnected := by
  have hx : x ∈ G.vertexSet := G.toGraph.left_mem_of_isLink hlink
  have hy : y ∈ G.vertexSet := G.toGraph.left_mem_of_isLink hlink.symm
  have hV : (G.edgeSub x y e).vertexSet = {x, y} := G.edgeSub_vertexSet hx hy
  have hx_mem : x ∈ (G.edgeSub x y e).vertexSet := hV ▸ Or.inl rfl
  have hy_mem : y ∈ (G.edgeSub x y e).vertexSet := hV ▸ Or.inr rfl
  have he_mem : e ∈ (G.edgeSub x y e).edgeSet := by
    refine ⟨⟨hlink.1, rfl⟩, ?_, ?_⟩
    · rcases hlink.2 with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · rcases hlink.2 with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact Or.inr h2
      · exact Or.inl h2
  have hlink_sub : (G.edgeSub x y e).toGraph.IsLink e x y := ⟨he_mem, hlink.2⟩
  have hwalk_xy : ∀ u ∈ (G.edgeSub x y e).vertexSet,
      Nonempty (GraphWalk (G.edgeSub x y e).toGraph x u) := by
    intro u hu
    have hu' : u = x ∨ u = y := by rw [hV] at hu; exact hu
    rcases hu' with rfl | rfl
    · exact ⟨.nil hx_mem⟩
    · exact ⟨.cons hlink_sub (.nil hy_mem)⟩
  refine ⟨⟨x, hx_mem⟩, fun u hu v hv => ?_⟩
  rcases hwalk_xy u hu with ⟨Wu⟩
  rcases hwalk_xy v hv with ⟨Wv⟩
  exact ⟨GraphWalk.append (GraphWalk.reverse Wu) Wv⟩

/-- If a subdigraph `H` has no edges (`H.edgeSet = ∅`), any walk in `H.toGraph` has equal endpoints. -/
lemma GraphWalk.eq_of_edgeSet_empty {H : Digraph α β} (hE : H.edgeSet = ∅)
    {u v : α} (W : GraphWalk H.toGraph u v) : u = v := by
  cases W with
  | nil _ => rfl
  | @cons _ _ _ e hlink _ =>
    have he : e ∈ H.edgeSet := hlink.1
    rw [hE] at he
    exact False.elim he

/-- Base case (Claims (3) and (4) of Graph Minors XIII, (5.3), pages 81–82):
when every edge of `G` is between distinct `sub i` and `sub j` and `G.vertexSet = ⋃ i, (sub i).vertexSet`,
Hall's Marriage Theorem yields a matching `M` between `Y = ⋃_{|V(G_i)| ≥ 2} V(G_i) ⊆ Z` and
`X = V(G) \ Z`, from which `H₁, …, H_κ` are constructed. -/
theorem theorem_5_3_base_matching {G : Digraph α β} {Z : Set α} {ξ k : ℕ}
    (hfin : G.IsFinite)
    (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard = ξ)
    (hk : (3 * ξ) / 2 ≤ k)
    {sub : Fin k → Digraph α β}
    (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hi : ∀ i : Fin k, (sub i).IsConnected ∨
      ((sub i).vertexSet.Nonempty ∧
        ∀ u ∈ (sub i).vertexSet, ∃ z ∈ Z ∩ (sub i).vertexSet,
          Nonempty (GraphWalk (sub i).toGraph u z)))
    (hii : ∀ i j : Fin k, i < j →
      (((sub i).vertexSet ∩ Z).Nonempty ∧ ((sub j).vertexSet ∩ Z).Nonempty) ∨
        G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hiii : ∀ (i : Fin k) (A B : Digraph α β),
      G.IsSeparation A B → Z ⊆ A.vertexSet → (G.interSub A (sub i)).IsNull →
      ξ ≤ Digraph.separationOrder A B)
    (hedges_between : ∀ e ∈ G.edgeSet, ∃ i j : Fin k, i ≠ j ∧
      G.head e ∈ (sub i).vertexSet ∧ G.tail e ∈ (sub j).vertexSet)
    (hV_union : (⋃ i : Fin k, (sub i).vertexSet) = G.vertexSet) :
    ∃ (μ : ℕ) (_ : μ ≤ ξ) (H : Fin (k - (ξ - μ) / 2) → Digraph α β),
      (∀ i, (H i).IsSubdigraph G) ∧
      (∀ i, (H i).IsConnected) ∧
      Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) ∧
      (∀ i : Fin (k - (ξ - μ) / 2),
        (i.1 < ξ → ((H i).vertexSet ∩ Z).ncard = 1) ∧
        (ξ ≤ i.1 → (H i).vertexSet ∩ Z = ∅)) ∧
      (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
        ¬ G.HasEdgeBetween (H i).vertexSet (H j).vertexSet → i.1 < μ ∧ j.1 < μ) := by
  have hsub_unique : ∀ ⦃x : α⦄ ⦃i j : Fin k⦄,
      x ∈ (sub i).vertexSet → x ∈ (sub j).vertexSet → i = j := by
    intro x i j hxi hxj
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) hxi hxj
  -- Each `sub i` has no edges, since every edge of `G` has ends in distinct `sub i₁ ≠ sub i₂`.
  have hsub_edge_empty (i : Fin k) : (sub i).edgeSet = ∅ := by
    ext e
    simp only [mem_empty_iff_false, iff_false]
    intro he
    have heG : e ∈ G.edgeSet := (hsub i).edgeSet_subset he
    rcases hedges_between e heG with ⟨i₁, i₂, hne, h1, h2⟩
    have hh : G.head e ∈ (sub i).vertexSet := (hsub i).head_eq he ▸ (sub i).head_mem he
    have ht : G.tail e ∈ (sub i).vertexSet := (hsub i).tail_eq he ▸ (sub i).tail_mem he
    exact hne ((hsub_unique h1 hh).trans (hsub_unique ht h2))
  -- Each `sub i` is non-empty, and either `ncard = 1` or `(sub i).vertexSet ⊆ Z`.
  have hsub_nonempty (i : Fin k) : (sub i).vertexSet.Nonempty := by
    rcases hi i with hconn | ⟨hne, _⟩
    · exact hconn.1
    · exact hne
  have hsub_fin (i : Fin k) : (sub i).vertexSet.Finite :=
    hfin.finite_V.subset (hsub i).vertexSet_subset
  have hsub_one_or_subZ (i : Fin k) :
      (sub i).vertexSet.ncard = 1 ∨ (sub i).vertexSet ⊆ Z := by
    rcases hi i with hconn | ⟨_, hwalk⟩
    · left
      rcases hconn.1 with ⟨x₀, hx₀⟩
      have heq : (sub i).vertexSet = {x₀} := by
        ext u
        refine ⟨fun hu => ?_, fun h => h.symm ▸ hx₀⟩
        rcases hconn.2 u hu x₀ hx₀ with ⟨W⟩
        exact GraphWalk.eq_of_edgeSet_empty (hsub_edge_empty i) W
      rw [heq, ncard_singleton]
    · right
      intro u hu
      rcases hwalk u hu with ⟨z, hz, ⟨W⟩⟩
      have huz : u = z := GraphWalk.eq_of_edgeSet_empty (hsub_edge_empty i) W
      exact huz ▸ hz.1
  -- Claim (3) (page 81): define `X = V(G) \ Z` and `Y = ⋃_{|V(G_i)| ≥ 2} V(G_i)`.
  let X : Set α := G.vertexSet \ Z
  let Y : Set α := ⋃ (i : Fin k) (_ : 2 ≤ (sub i).vertexSet.ncard), (sub i).vertexSet
  have hXfin : X.Finite := hfin.finite_V.sdiff
  have hZfin : Z.Finite := hfin.finite_V.subset hZ
  have hY_sub_Z : Y ⊆ Z := by
    rintro y ⟨_, ⟨i, rfl⟩, _, ⟨hi2, rfl⟩, hy⟩
    rcases hsub_one_or_subZ i with h1 | hsubZ
    · omega
    · exact hsubZ hy
  have hYfin : Y.Finite := hZfin.subset hY_sub_Z
  -- Every vertex `u ∈ G.vertexSet \ Y` belongs to a singleton `(sub i).vertexSet = {u}`.
  have hsingleton_of_not_Y : ∀ ⦃u : α⦄, u ∈ G.vertexSet → u ∉ Y →
      ∃ i : Fin k, (sub i).vertexSet = {u} := by
    intro u huG huNotY
    rw [← hV_union, mem_iUnion] at huG
    rcases huG with ⟨i, hui⟩
    have hcard_le1 : (sub i).vertexSet.ncard ≤ 1 := by
      by_contra hgt
      have hge2 : 2 ≤ (sub i).vertexSet.ncard := by omega
      exact huNotY (mem_biUnion hge2 hui)
    have hcard_ge1 : 1 ≤ (sub i).vertexSet.ncard :=
      (ncard_pos (hsub_fin i)).mpr ⟨u, hui⟩
    have hcard1 : (sub i).vertexSet.ncard = 1 := le_antisymm hcard_le1 hcard_ge1
    rcases ncard_eq_one.mp hcard1 with ⟨w, hw⟩
    have huw : u = w := by rw [hw] at hui; exact hui
    subst huw
    exact ⟨i, hw⟩
  -- Every `x ∈ X` is adjacent in `G` to every `w ∈ (X \ {x}) ∪ (Z \ Y)`.
  have hadj_X : ∀ ⦃x w : α⦄, x ∈ X → w ∈ X ∪ (Z \ Y) → x ≠ w → G.toGraph.Adj x w := by
    intro x w hx hw hne
    have hxNotY : x ∉ Y := fun hxY => hx.2 (hY_sub_Z hxY)
    have hwG : w ∈ G.vertexSet := by
      rcases hw with hwX | hwZ
      · exact hwX.1
      · exact hZ hwZ.1
    have hwNotY : w ∉ Y := by
      rcases hw with hwX | hwZ
      · exact fun hwY => hwX.2 (hY_sub_Z hwY)
      · exact hwZ.2
    obtain ⟨ix, hix⟩ := hsingleton_of_not_Y hx.1 hxNotY
    obtain ⟨iw, hiw⟩ := hsingleton_of_not_Y hwG hwNotY
    have hix_ne : ix ≠ iw := by
      intro heq
      subst heq
      have hxw : x ∈ ({w} : Set α) := hiw ▸ (hix ▸ mem_singleton x)
      exact hne hxw
    have hx_no_Z : ¬ ((sub ix).vertexSet ∩ Z).Nonempty := by
      rw [hix]
      rintro ⟨z, rfl, hzZ⟩
      exact hx.2 hzZ
    have hEdge : G.HasEdgeBetween (sub ix).vertexSet (sub iw).vertexSet := by
      rcases lt_or_gt_of_ne hix_ne with hlt | hgt
      · rcases hii ix iw hlt with ⟨h1, _⟩ | hE
        · exact False.elim (hx_no_Z h1)
        · exact hE
      · rcases hii iw ix hgt with ⟨_, h2⟩ | ⟨e, he, h⟩
        · exact False.elim (hx_no_Z h2)
        · exact ⟨e, he, h.symm⟩
    rcases hEdge with ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · rw [hix, mem_singleton_iff] at h1
      rw [hiw, mem_singleton_iff] at h2
      exact ⟨e, he, Or.inl ⟨h1, h2⟩⟩
    · rw [hix, mem_singleton_iff] at h2
      rw [hiw, mem_singleton_iff] at h1
      exact ⟨e, he, Or.inr ⟨h1, h2⟩⟩
  -- Cardinality bound of Claim (3): `X.ncard + (Z \ Y).ncard + Y.ncard / 2 ≥ k`.
  have hcard_claim3 : k ≤ X.ncard + (Z \ Y).ncard + Y.ncard / 2 := by
    let S1 : Finset (Fin k) := Finset.univ.filter (fun i => (sub i).vertexSet.ncard = 1)
    let S2 : Finset (Fin k) := Finset.univ.filter (fun i => 2 ≤ (sub i).vertexSet.ncard)
    have hS12_card : S1.card + S2.card = k := by
      have hdisj_S : Disjoint S1 S2 := by
        rw [Finset.disjoint_filter]
        intro i _ h1 h2; omega
      have hunion_S : S1 ∪ S2 = Finset.univ := by
        ext i
        simp only [S1, S2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        have hpos : 1 ≤ (sub i).vertexSet.ncard := (ncard_pos (hsub_fin i)).mpr (hsub_nonempty i)
        exact (lt_or_eq_of_le hpos).symm.imp Eq.symm id
      have h := Finset.card_union_of_disjoint hdisj_S
      rw [hunion_S, Finset.card_univ, Fintype.card_fin] at h
      exact h.symm
    -- `X ∪ (Z \ Y) = ⋃ i ∈ S1, (sub i).vertexSet`
    have hXZ_eq : X ∪ (Z \ Y) = ⋃ i ∈ S1, (sub i).vertexSet := by
      ext u
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, mem_iUnion, exists_prop]
      constructor
      · intro hu
        have huG : u ∈ G.vertexSet := hu.elim (fun h => h.1) (fun h => hZ h.1)
        have huNotY : u ∉ Y := hu.elim (fun h hY => h.2 (hY_sub_Z hY)) (fun h => h.2)
        obtain ⟨i, hi⟩ := hsingleton_of_not_Y huG huNotY
        exact ⟨i, by rw [hi, ncard_singleton], hi ▸ mem_singleton u⟩
      · rintro ⟨i, hi1, hui⟩
        have huG : u ∈ G.vertexSet := (hsub i).vertexSet_subset hui
        have huNotY : u ∉ Y := by
          rintro ⟨_, ⟨j, rfl⟩, _, ⟨hj2, rfl⟩, huj⟩
          have hij : i = j := hsub_unique hui huj
          subst hij; omega
        by_cases huZ : u ∈ Z
        · exact Or.inr ⟨huZ, huNotY⟩
        · exact Or.inl ⟨huG, huZ⟩
    -- Map `i ∈ S1` to the unique vertex of `(sub i).vertexSet` in `X ∪ (Z \ Y)`
    have hS1_le : S1.card ≤ X.ncard + (Z \ Y).ncard := by
      have hdisj_XZ : Disjoint X (Z \ Y) :=
        disjoint_iff_inter_eq_empty.mpr (by ext u; simp [X]; tauto)
      rw [← ncard_union_eq hdisj_XZ hXfin hZfin.sdiff, hXZ_eq]
      -- Each `(sub i).vertexSet` (`i ∈ S1`) has 1 element and they are disjoint
      let pick1 (i : S1) : α := (hsub_nonempty i.1).some
      have hpick1_mem (i : S1) : pick1 i ∈ (sub i.1).vertexSet := (hsub_nonempty i.1).some_mem
      have hpick1_inj : Function.Injective pick1 := by
        intro i₁ i₂ heq
        exact Subtype.ext (hsub_unique (hpick1_mem i₁) (heq ▸ hpick1_mem i₂))
      have hrange_sub : Set.range pick1 ⊆ ⋃ i ∈ S1, (sub i).vertexSet := by
        rintro u ⟨i, rfl⟩
        exact mem_biUnion i.2 (hpick1_mem i)
      have hcard_rng : (Set.range pick1).ncard = S1.card := by
        rw [ncard_range_of_injective hpick1_inj, Nat.card_eq_fintype_card, Fintype.card_coe]
      rw [← hcard_rng]
      exact ncard_le_ncard hrange_sub (hfin.finite_V.subset (by
        rintro u ⟨_, ⟨i, rfl⟩, _, ⟨_, rfl⟩, hui⟩
        exact (hsub i).vertexSet_subset hui))
    -- For `i ∈ S2`, `(sub i).vertexSet` has `≥ 2` elements in `Y`, so `2 * S2.card ≤ Y.ncard`
    have hS2_le : 2 * S2.card ≤ Y.ncard := by
      -- Embed `S2 × Bool` injectively into `Y`
      have htwo (i : S2) : ∃ a b : α, a ∈ (sub i.1).vertexSet ∧ b ∈ (sub i.1).vertexSet ∧ a ≠ b := by
        have hi2 : 1 < (sub i.1).vertexSet.ncard := by
          have hm := i.2
          simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and] at hm
          omega
        rcases ( one_lt_ncard_iff (hsub_fin i.1) ).mp hi2 with ⟨a, b, ha, hb, hab⟩
        exact ⟨a, b, ha, hb, hab⟩
      let pairOf (i : S2) := Classical.indefiniteDescription _ (htwo i)
      let f2 : S2 × Bool → Y := fun ⟨i, b⟩ =>
        if b then ⟨(pairOf i).1, mem_biUnion (by
            have hm := i.2; simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and] at hm; exact hm)
          (Classical.choose_spec (pairOf i).2).1⟩
        else ⟨(Classical.choose (pairOf i).2), mem_biUnion (by
            have hm := i.2; simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and] at hm; exact hm)
          (Classical.choose_spec (pairOf i).2).2.1⟩
      have hf2_inj : Function.Injective f2 := by
        rintro ⟨i₁, b₁⟩ ⟨i₂, b₂⟩ heq
        have hval : (f2 ⟨i₁, b₁⟩).1 = (f2 ⟨i₂, b₂⟩).1 := congrArg Subtype.val heq
        have hmem₁ : (f2 ⟨i₁, b₁⟩).1 ∈ (sub i₁.1).vertexSet := by
          cases b₁
          · exact (Classical.choose_spec (pairOf i₁).2).2.1
          · exact (Classical.choose_spec (pairOf i₁).2).1
        have hmem₂ : (f2 ⟨i₂, b₂⟩).1 ∈ (sub i₂.1).vertexSet := by
          cases b₂
          · exact (Classical.choose_spec (pairOf i₂).2).2.1
          · exact (Classical.choose_spec (pairOf i₂).2).1
        have hi_eq : i₁ = i₂ := Subtype.ext (hsub_unique hmem₁ (hval ▸ hmem₂))
        subst hi_eq
        cases b₁ <;> cases b₂
        · rfl
        · exfalso
          exact (Classical.choose_spec (pairOf i₁).2).2.2 hval.symm
        · exfalso
          exact (Classical.choose_spec (pairOf i₁).2).2.2 hval
        · rfl
      have _ : Fintype Y := hYfin.fintype
      have hcard_dom : Fintype.card (S2 × Bool) ≤ Fintype.card Y :=
        Fintype.card_le_of_injective f2 hf2_inj
      have hY_card : Fintype.card Y = Y.ncard :=
        (Nat.card_eq_fintype_card).symm.trans (Nat.card_coe_set_eq Y)
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, hY_card] at hcard_dom
      omega
    omega
  have hZY_add_Y : (Z \ Y).ncard + Y.ncard = ξ := by
    rw [ncard_sdiff_add_ncard_of_subset hY_sub_Z hZfin, hZcard]
  have hY_le_X : Y.ncard ≤ X.ncard := by omega
  -- Claim (4) (page 81): Hall's condition holds from `Y` to `X`.
  have _ : Fintype Y := hYfin.fintype
  have _ : Fintype X := hXfin.fintype
  let N_hall (y : Y) : Finset X :=
    Finset.univ.filter (fun x : X => G.toGraph.Adj x.1 y.1)
  have hHall_cond : ∀ s : Finset Y, s.card ≤ (s.biUnion N_hall).card := by
    intro s
    by_contra hlt
    rw [not_le] at hlt
    let Y' : Set α := Subtype.val '' (s : Set Y)
    let X' : Set α := Subtype.val '' ((s.biUnion N_hall : Finset X) : Set X)
    have hY'_sub_Y : Y' ⊆ Y := by rintro _ ⟨y, _, rfl⟩; exact y.2
    have hY'_sub_Z : Y' ⊆ Z := hY'_sub_Y.trans hY_sub_Z
    have hX'_sub_X : X' ⊆ X := by rintro _ ⟨x, _, rfl⟩; exact x.2
    have hY'card : Y'.ncard = s.card := by
      rw [ncard_image_of_injective _ Subtype.val_injective, ncard_coe_finset]
    have hX'card : X'.ncard = (s.biUnion N_hall).card := by
      rw [ncard_image_of_injective _ Subtype.val_injective, ncard_coe_finset]
    have hY'_le_Y : Y'.ncard ≤ Y.ncard := ncard_le_ncard hY'_sub_Y hYfin
    have hX'_lt_X : X'.ncard < X.ncard := by omega
    have hX_diff_nonempty : (X \ X').Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hemp
      have hle := ncard_le_ncard hemp (hXfin.subset hX'_sub_X)
      omega
    rcases hX_diff_nonempty with ⟨x₀, hx₀X, hx₀NotX'⟩
    have hx₀NotY : x₀ ∉ Y := fun h => hx₀X.2 (hY_sub_Z h)
    obtain ⟨i₀, hi₀⟩ := hsingleton_of_not_Y hx₀X.1 hx₀NotY
    -- Construct the separation `(A, B)` of `G` with `V(A) = Z ∪ X'` and `V(B) = V(G) \ Y'`
    let A : Digraph α β := G.induce (Z ∪ X')
    let B : Digraph α β := G.subdigraphOf (G.vertexSet \ Y') (G.edgeSet \ A.edgeSet)
    have hAV : A.vertexSet = Z ∪ X' :=
      inter_eq_self_of_subset_right (union_subset hZ (hX'_sub_X.trans sdiff_subset))
    have hBV : B.vertexSet = G.vertexSet \ Y' :=
      inter_eq_self_of_subset_right sdiff_subset
    -- Every edge of `G` not in `A` has neither end in `Y'`
    have hEdge_no_Y' : ∀ e ∈ G.edgeSet, e ∉ A.edgeSet →
        G.head e ∉ Y' ∧ G.tail e ∉ Y' := by
      intro e heG heNotA
      rcases hedges_between e heG with ⟨i₁, i₂, hne, h1, h2⟩
      have hends_adj : G.toGraph.Adj (G.tail e) (G.head e) :=
        ⟨e, heG, Or.inr ⟨rfl, rfl⟩⟩
      constructor
      · rintro ⟨y, hys, hy_eq⟩
        apply heNotA
        refine ⟨heG, Or.inl (hY'_sub_Z ⟨y, hys, hy_eq⟩), ?_⟩
        by_cases htZ : G.tail e ∈ Z
        · exact Or.inl htZ
        · right
          have htX : G.tail e ∈ X := ⟨G.tail_mem heG, htZ⟩
          refine ⟨⟨G.tail e, htX⟩, ?_, rfl⟩
          rw [Finset.mem_coe, Finset.mem_biUnion]
          refine ⟨y, hys, ?_⟩
          simp only [N_hall, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hy_eq]
          exact hends_adj
      · rintro ⟨y, hys, hy_eq⟩
        apply heNotA
        refine ⟨heG, ?_, Or.inl (hY'_sub_Z ⟨y, hys, hy_eq⟩)⟩
        by_cases hhZ : G.head e ∈ Z
        · exact Or.inl hhZ
        · right
          have hhX : G.head e ∈ X := ⟨G.head_mem heG, hhZ⟩
          refine ⟨⟨G.head e, hhX⟩, ?_, rfl⟩
          rw [Finset.mem_coe, Finset.mem_biUnion]
          refine ⟨y, hys, ?_⟩
          simp only [N_hall, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hy_eq]
          exact hends_adj.symm
    have hsep : G.IsSeparation A B := {
      sub_left := Digraph.induce_isSubdigraph G (Z ∪ X')
      sub_right := Digraph.subdigraphOf_isSubdigraph G (G.vertexSet \ Y') (G.edgeSet \ A.edgeSet)
      vertexSet_union := by
        rw [hAV, hBV]
        ext u
        simp only [mem_union, mem_sdiff]
        exact ⟨fun h => h.elim (fun h1 => h1.elim (fun hZ' => hZ hZ') (fun hX' => (hX'_sub_X hX').1))
          (fun h2 => h2.1),
          fun huG => by
            by_cases huY' : u ∈ Y'
            · exact Or.inl (Or.inl (hY'_sub_Z huY'))
            · exact Or.inr ⟨huG, huY'⟩⟩
      edgeSet_union := by
        ext e
        simp only [mem_union]
        refine ⟨fun h => h.elim (fun heA => heA.1) (fun heB => heB.1.1), fun heG => ?_⟩
        by_cases heA : e ∈ A.edgeSet
        · exact Or.inl heA
        · have hnoY' := hEdge_no_Y' e heG heA
          exact Or.inr ⟨⟨heG, heG, heA⟩, ⟨G.head_mem heG, hnoY'.1⟩, ⟨G.tail_mem heG, hnoY'.2⟩⟩
      edgeSet_disjoint :=
        disjoint_iff_inter_eq_empty.mpr (by
          ext e
          simp only [B, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq, mem_sdiff,
            mem_empty_iff_false, iff_false]
          tauto)
    }
    have hZA : Z ⊆ A.vertexSet := by rw [hAV]; exact subset_union_left
    have hAnull : (G.interSub A (sub i₀)).IsNull := by
      refine ⟨?_, ?_⟩
      · ext u
        simp only [Digraph.interSub, Digraph.subdigraphOf, hAV, hi₀, mem_inter_iff, mem_union,
          mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
        intro _ hx₀ZX' rfl
        rcases hx₀ZX' with hx₀Z | hx₀X'
        · exact hx₀X.2 hx₀Z
        · exact hx₀NotX' hx₀X'
      · ext e
        simp only [Digraph.interSub, Digraph.subdigraphOf, hsub_edge_empty i₀, inter_empty,
          mem_inter_iff, mem_empty_iff_false, false_and, mem_ofPred_eq, iff_self]
    have hord_ge : ξ ≤ Digraph.separationOrder A B := hiii i₀ A B hsep hZA hAnull
    have hAB_eq : A.vertexSet ∩ B.vertexSet = (Z \ Y') ∪ X' := by
      rw [hAV, hBV]
      ext u
      simp only [mem_inter_iff, mem_union, mem_sdiff]
      constructor
      · rintro ⟨huZ | huX', huG, huNotY'⟩
        · exact Or.inl ⟨huZ, huNotY'⟩
        · exact Or.inr huX'
      · rintro (⟨huZ, huNotY'⟩ | huX')
        · exact ⟨Or.inl huZ, hZ huZ, huNotY'⟩
        · exact ⟨Or.inr huX', (hX'_sub_X huX').1, fun huY' => (hX'_sub_X huX').2 (hY'_sub_Z huY')⟩
    have hord_le : Digraph.separationOrder A B ≤ (Z \ Y').ncard + X'.ncard := by
      unfold Digraph.separationOrder
      rw [hAB_eq]
      exact ncard_union_le (Z \ Y') X'
    have hZY'_card : (Z \ Y').ncard + Y'.ncard = ξ := by
      rw [ncard_sdiff_add_ncard_of_subset hY'_sub_Z hZfin, hZcard]
    omega
  -- By Hall's theorem, there is an injection `m : Y → X` with `m y ∈ N_hall y` for all `y : Y`.
  obtain ⟨m, hm_inj, hm_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' N_hall).mp hHall_cond
  have hm_adj (y : Y) : G.toGraph.Adj (m y).1 y.1 := by
    have h := hm_mem y
    simp only [N_hall, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  let edgeForY (y : Y) : {e : β // G.toGraph.IsLink e y.1 (m y).1} :=
    Classical.indefiniteDescription _ (hm_adj y).symm
  -- Define `μ = (Z \ Y).ncard` and `κ = k - (ξ - μ) / 2`.
  let μ : ℕ := (Z \ Y).ncard
  have hμ_le_ξ : μ ≤ ξ := by omega
  have hξ_sub_μ : ξ - μ = Y.ncard := by omega
  let κ : ℕ := k - (ξ - μ) / 2
  -- Enumerate `Z \ Y`, `Y`, and `X \ range m`
  let ZdiffY : Set α := Z \ Y
  have hZdiffY_fin : ZdiffY.Finite := hZfin.sdiff
  have _ : Fintype ZdiffY := hZdiffY_fin.fintype
  have hZdiffY_card : Fintype.card ZdiffY = μ :=
    (Nat.card_eq_fintype_card).symm.trans (Nat.card_coe_set_eq ZdiffY)
  let equivZdiffY : Fin μ ≃ ZdiffY :=
    (finCongr hZdiffY_card.symm).trans (Fintype.equivFin ZdiffY).symm
  have hY_card_eq : Fintype.card Y = ξ - μ :=
    ((Nat.card_eq_fintype_card).symm.trans (Nat.card_coe_set_eq Y)).trans hξ_sub_μ.symm
  let equivY : Fin (ξ - μ) ≃ Y :=
    (finCongr hY_card_eq.symm).trans (Fintype.equivFin Y).symm
  let Xrem : Set α := X \ (Subtype.val '' Set.range m)
  have hXrem_fin : Xrem.Finite := hXfin.sdiff
  have _ : Fintype Xrem := hXrem_fin.fintype
  have hm_sub : Subtype.val '' Set.range m ⊆ X := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩; exact (m y).2
  have hm_range_card : (Subtype.val '' Set.range m).ncard = Y.ncard := by
    rw [ncard_image_of_injective _ Subtype.val_injective, ncard_range_of_injective hm_inj]
    exact Nat.card_coe_set_eq Y
  have hXrem_card_ge : κ - ξ ≤ Fintype.card Xrem := by
    have hXrem_c : Fintype.card Xrem = (X \ (Subtype.val '' Set.range m)).ncard :=
      (Nat.card_eq_fintype_card).symm.trans (Nat.card_coe_set_eq Xrem)
    rw [hXrem_c]
    have h1 := ncard_sdiff_add_ncard_of_subset hm_sub hXfin
    have hμ_def : μ = (Z \ Y).ncard := rfl
    have hκ_def : κ = k - (ξ - μ) / 2 := rfl
    omega
  obtain ⟨embXrem⟩ := Function.Embedding.nonempty_of_card_le
    (by rw [Fintype.card_fin]; exact hXrem_card_ge : Fintype.card (Fin (κ - ξ)) ≤ Fintype.card Xrem)
  -- Construct `H : Fin κ → Digraph α β`
  let H (r : Fin κ) : Digraph α β :=
    if hr1 : r.1 < μ then
      G.singletonSub (equivZdiffY ⟨r.1, hr1⟩).1
    else if hr2 : r.1 < ξ then
      let y := equivY ⟨r.1 - μ, by omega⟩
      G.edgeSub y.1 (m y).1 (edgeForY y).1
    else
      G.singletonSub (embXrem ⟨r.1 - ξ, by omega⟩).1
  have hH_disj : Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) := by
    have hV_H (r : Fin κ) :
        (if hr1 : r.1 < μ then (H r).vertexSet = {(equivZdiffY ⟨r.1, hr1⟩).1}
         else if hr2 : r.1 < ξ then
           let y := equivY ⟨r.1 - μ, by omega⟩
           (H r).vertexSet = {y.1, (m y).1}
         else (H r).vertexSet = {(embXrem ⟨r.1 - ξ, by omega⟩).1}) := by
      dsimp [H]
      split_ifs with hr1 hr2
      · exact G.singletonSub_vertexSet (hZ (equivZdiffY ⟨r.1, hr1⟩).2.1)
      · let y := equivY ⟨r.1 - μ, by omega⟩
        exact G.edgeSub_vertexSet (hZ (hY_sub_Z y.2)) (m y).2.1
      · exact G.singletonSub_vertexSet (embXrem ⟨r.1 - ξ, by omega⟩).2.1.1
    intro r₁ r₂ hne
    have hV1 := hV_H r₁
    have hV2 := hV_H r₂
    split_ifs at hV1 with hr1_1 hr1_2 <;> split_ifs at hV2 with hr2_1 hr2_2 <;>
      rw [hV1, hV2, Set.disjoint_iff] <;> rintro u ⟨hu1, hu2⟩
    · -- both `< μ`
      rw [mem_singleton_iff] at hu1 hu2
      have heq := equivZdiffY.injective (Subtype.ext (hu1.symm.trans hu2))
      have hval : r₁.1 = r₂.1 := congrArg (@Fin.val μ) heq
      exact hne (Fin.ext hval)
    · -- `r₁ < μ`, `μ ≤ r₂ < ξ`
      let y₂ := equivY ⟨r₂.1 - μ, by omega⟩
      rw [mem_singleton_iff] at hu1
      rcases hu2 with rfl | rfl
      · exact (equivZdiffY ⟨r₁.1, hr1_1⟩).2.2 (hu1 ▸ y₂.2)
      · exact (m y₂).2.2 (hu1 ▸ (equivZdiffY ⟨r₁.1, hr1_1⟩).2.1)
    · -- `r₁ < μ`, `ξ ≤ r₂`
      rw [mem_singleton_iff] at hu1 hu2
      exact (embXrem ⟨r₂.1 - ξ, by omega⟩).2.1.2 (hu2 ▸ hu1 ▸ (equivZdiffY ⟨r₁.1, hr1_1⟩).2.1)
    · -- `μ ≤ r₁ < ξ`, `r₂ < μ`
      let y₁ := equivY ⟨r₁.1 - μ, by omega⟩
      rw [mem_singleton_iff] at hu2
      rcases hu1 with rfl | rfl
      · exact (equivZdiffY ⟨r₂.1, hr2_1⟩).2.2 (hu2.symm ▸ y₁.2)
      · exact (m y₁).2.2 (hu2.symm ▸ (equivZdiffY ⟨r₂.1, hr2_1⟩).2.1)
    · -- both in `[μ, ξ)`
      let y₁ := equivY ⟨r₁.1 - μ, by omega⟩
      let y₂ := equivY ⟨r₂.1 - μ, by omega⟩
      have hy_ne : y₁ ≠ y₂ := by
        intro hy_eq
        have hfin_eq := equivY.injective hy_eq
        have hval_eq : r₁.1 - μ = r₂.1 - μ := congrArg Fin.val hfin_eq
        exact hne (Fin.ext (by omega))
      rcases hu1 with rfl | rfl <;> rcases hu2 with h | h
      · exact hy_ne (Subtype.ext h)
      · exact (m y₂).2.2 (h ▸ hY_sub_Z y₁.2)
      · exact (m y₁).2.2 (h.symm ▸ hY_sub_Z y₂.2)
      · exact hy_ne (hm_inj (Subtype.ext h))
    · -- `μ ≤ r₁ < ξ`, `ξ ≤ r₂`
      let y₁ := equivY ⟨r₁.1 - μ, by omega⟩
      rw [mem_singleton_iff] at hu2
      rcases hu1 with rfl | rfl
      · exact (embXrem ⟨r₂.1 - ξ, by omega⟩).2.1.2 (hu2 ▸ hY_sub_Z y₁.2)
      · exact (embXrem ⟨r₂.1 - ξ, by omega⟩).2.2 ⟨m y₁, ⟨y₁, rfl⟩, hu2⟩
    · -- `ξ ≤ r₁`, `r₂ < μ`
      rw [mem_singleton_iff] at hu1 hu2
      exact (embXrem ⟨r₁.1 - ξ, by omega⟩).2.1.2 (hu1 ▸ hu2.symm ▸ (equivZdiffY ⟨r₂.1, hr2_1⟩).2.1)
    · -- `ξ ≤ r₁`, `μ ≤ r₂ < ξ`
      let y₂ := equivY ⟨r₂.1 - μ, by omega⟩
      rw [mem_singleton_iff] at hu1
      rcases hu2 with rfl | rfl
      · exact (embXrem ⟨r₁.1 - ξ, by omega⟩).2.1.2 (hu1.symm ▸ hY_sub_Z y₂.2)
      · exact (embXrem ⟨r₁.1 - ξ, by omega⟩).2.2 ⟨m y₂, ⟨y₂, rfl⟩, hu1⟩
    · -- both `≥ ξ`
      rw [mem_singleton_iff] at hu1 hu2
      have heq := embXrem.injective (Subtype.ext (hu1.symm.trans hu2))
      have hval_eq : r₁.1 - ξ = r₂.1 - ξ := congrArg Fin.val heq
      exact hne (Fin.ext (by omega))
  refine ⟨μ, hμ_le_ξ, H, ?_, ?_, hH_disj, ?_, ?_⟩
  · -- `IsSubdigraph`
    intro r
    dsimp [H]
    split_ifs with hr1 hr2
    · exact G.singletonSub_isSubdigraph _
    · exact G.edgeSub_isSubdigraph _ _ _
    · exact G.singletonSub_isSubdigraph _
  · -- `IsConnected`
    intro r
    dsimp [H]
    split_ifs with hr1 hr2
    · exact G.singletonSub_isConnected (hZ (equivZdiffY ⟨r.1, hr1⟩).2.1)
    · let y := equivY ⟨r.1 - μ, by omega⟩
      exact G.edgeSub_isConnected (edgeForY y).2
    · exact G.singletonSub_isConnected (embXrem ⟨r.1 - ξ, by omega⟩).2.1.1
  · -- Condition (a)
    intro r
    constructor
    · intro hr_lt_ξ
      dsimp [H]
      split_ifs with hr1
      · rw [G.singletonSub_vertexSet (hZ (equivZdiffY ⟨r.1, hr1⟩).2.1)]
        have h_inter : ({(equivZdiffY ⟨r.1, hr1⟩).1} : Set α) ∩ Z = {(equivZdiffY ⟨r.1, hr1⟩).1} :=
          inter_eq_self_of_subset_left (singleton_subset_iff.mpr (equivZdiffY ⟨r.1, hr1⟩).2.1)
        rw [h_inter, ncard_singleton]
      · let y := equivY ⟨r.1 - μ, by omega⟩
        rw [G.edgeSub_vertexSet (hZ (hY_sub_Z y.2)) (m y).2.1]
        have h_inter : ({y.1, (m y).1} : Set α) ∩ Z = {y.1} := by
          ext u
          simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
          refine ⟨?_, fun h => ⟨Or.inl h, h.symm ▸ hY_sub_Z y.2⟩⟩
          rintro ⟨rfl | rfl, huZ⟩
          · rfl
          · exact False.elim ((m y).2.2 huZ)
        rw [h_inter, ncard_singleton]
    · intro hr_ge_ξ
      have hnot1 : ¬ r.1 < μ := by omega
      have hnot2 : ¬ r.1 < ξ := by omega
      dsimp [H]
      simp only [hnot1, hnot2, ↓reduceDIte]
      rw [G.singletonSub_vertexSet (embXrem ⟨r.1 - ξ, by omega⟩).2.1.1]
      ext u
      simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
      rintro rfl huZ
      exact (embXrem ⟨r.1 - ξ, by omega⟩).2.1.2 huZ
  · -- Condition (b)
    intro r₁ r₂ hlt hnoEdge
    by_contra hnot
    have hr2_ge_μ : μ ≤ r₂.1 := by omega
    have hr2_X : ∃ x₂ ∈ (H r₂).vertexSet, x₂ ∈ X := by
      dsimp [H]
      have hnot1 : ¬ r₂.1 < μ := by omega
      simp only [hnot1, ↓reduceDIte]
      split_ifs with hr2_lt_ξ
      · let y₂ := equivY ⟨r₂.1 - μ, by omega⟩
        refine ⟨(m y₂).1, ?_, (m y₂).2⟩
        rw [G.edgeSub_vertexSet (hZ (hY_sub_Z y₂.2)) (m y₂).2.1]
        exact Or.inr rfl
      · refine ⟨(embXrem ⟨r₂.1 - ξ, by omega⟩).1, ?_, (embXrem ⟨r₂.1 - ξ, by omega⟩).2.1⟩
        rw [G.singletonSub_vertexSet (embXrem ⟨r₂.1 - ξ, by omega⟩).2.1.1]
        exact mem_singleton _
    have hr1_XZY : ∃ w₁ ∈ (H r₁).vertexSet, w₁ ∈ X ∪ (Z \ Y) := by
      dsimp [H]
      split_ifs with hr1_1 hr1_2
      · refine ⟨(equivZdiffY ⟨r₁.1, hr1_1⟩).1, ?_, Or.inr (equivZdiffY ⟨r₁.1, hr1_1⟩).2⟩
        rw [G.singletonSub_vertexSet (hZ (equivZdiffY ⟨r₁.1, hr1_1⟩).2.1)]
        exact mem_singleton _
      · let y₁ := equivY ⟨r₁.1 - μ, by omega⟩
        refine ⟨(m y₁).1, ?_, Or.inl (m y₁).2⟩
        rw [G.edgeSub_vertexSet (hZ (hY_sub_Z y₁.2)) (m y₁).2.1]
        exact Or.inr rfl
      · refine ⟨(embXrem ⟨r₁.1 - ξ, by omega⟩).1, ?_, Or.inl (embXrem ⟨r₁.1 - ξ, by omega⟩).2.1⟩
        rw [G.singletonSub_vertexSet (embXrem ⟨r₁.1 - ξ, by omega⟩).2.1.1]
        exact mem_singleton _
    rcases hr2_X with ⟨x₂, hx₂H, hx₂X⟩
    rcases hr1_XZY with ⟨w₁, hw₁H, hw₁XZY⟩
    have hxw_ne : x₂ ≠ w₁ := by
      rintro rfl
      exact Set.disjoint_left.mp (hH_disj (ne_of_lt hlt)) hw₁H hx₂H
    rcases hadj_X hx₂X hw₁XZY hxw_ne with ⟨e, heG, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact hnoEdge ⟨e, heG, Or.inr ⟨h1.symm ▸ hx₂H, h2.symm ▸ hw₁H⟩⟩
    · exact hnoEdge ⟨e, heG, Or.inl ⟨h1.symm ▸ hw₁H, h2.symm ▸ hx₂H⟩⟩

end GraphMinor.GM13
