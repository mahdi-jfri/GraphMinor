module

public import GraphMinor.GM21.VertexSplitting

/-!
# Nested Separations and Vital Linkages: Graph Minors XXI, (2.5), (2.6), (2.7)

Proves Graph Minors XXI, `(2.5)`, `(2.6)`, and `(2.7)` on nested sequences of separations of
bounded order and vital `p`-linkages.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Hypergraph GraphMinor.GM10 GraphMinor.GM17

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. Transfer linkages between two separators -/

/-- If `S` is a finite family of pairwise disjoint sets with `S.ncard = k`, `X` is a finite set with
`X.ncard = k`, and every `P ∈ S` meets `X`, then every `x ∈ X` belongs to some `P ∈ S` and every
`P ∈ S` meets `X` in a unique element. -/
lemma disjoint_family_unique_inter_of_ncard_eq {S : Set (Set α)} {X : Set α} {k : ℕ}
    (hS_fin : S.Finite) (hX_fin : X.Finite)
    (hdisj : ∀ P₁ ∈ S, ∀ P₂ ∈ S, P₁ ≠ P₂ → Disjoint P₁ P₂)
    (hS_card : S.ncard = k) (hX_card : X.ncard = k)
    (hmeets : ∀ P ∈ S, ∃ x ∈ X, x ∈ P) :
    (∀ x ∈ X, ∃ P ∈ S, x ∈ P) ∧
    (∀ P ∈ S, ∀ x₁ ∈ P ∩ X, ∀ x₂ ∈ P ∩ X, x₁ = x₂) := by
  classical
  rcases eq_empty_or_nonempty X with rfl | ⟨x₀, _⟩
  · have hk0 : k = 0 := by rw [← hX_card, ncard_empty]
    have hS_emp : S = ∅ := (ncard_eq_zero hS_fin).mp (by omega)
    subst hS_emp
    simp
  · let f : Set α → α := fun P => if h : P ∈ S then Classical.choose (hmeets P h) else x₀
    have hf_mem : ∀ P ∈ S, f P ∈ X ∧ f P ∈ P := by
      intro P hP
      have h_eq : f P = Classical.choose (hmeets P hP) := by
        dsimp [f]
        split_ifs
        rfl
      rw [h_eq]
      exact Classical.choose_spec (hmeets P hP)
    have hf_inj : InjOn f S := by
      intro P₁ hP₁ P₂ hP₂ heq
      by_contra hne
      have h1 := (hf_mem P₁ hP₁).2
      have h2 := heq ▸ (hf_mem P₂ hP₂).2
      exact Set.disjoint_left.mp (hdisj P₁ hP₁ P₂ hP₂ hne) h1 h2
    have hf_sub : f '' S ⊆ X := by
      rintro x ⟨P, hP, rfl⟩
      exact (hf_mem P hP).1
    have hf_bij : BijOn f S (f '' S) := hf_inj.bijOn_image
    have hf_eq : f '' S = X := by
      apply eq_of_subset_of_ncard_le hf_sub _ hX_fin
      rw [← hf_bij.ncard_eq, hS_card, hX_card]
    refine ⟨?_, ?_⟩
    · intro x hx
      have hx_im : x ∈ f '' S := hf_eq.symm ▸ hx
      rcases hx_im with ⟨P, hP, rfl⟩
      exact ⟨P, hP, (hf_mem P hP).2⟩
    · intro P hP x₁ hx₁ x₂ hx₂
      suffices ∀ x ∈ P ∩ X, x = f P by
        rw [this x₁ hx₁, this x₂ hx₂]
      intro x ⟨hxP, hxX⟩
      have hx_im : x ∈ f '' S := hf_eq.symm ▸ hxX
      rcases hx_im with ⟨Q, hQ, rfl⟩
      have hQP : Q = P := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisj Q hQ P hP hne) (hf_mem Q hQ).2 hxP
      rw [hQP]

/-- A linkage `M` in `B ∩ A'` with `k` components, each with one end in `V(A ∩ B)` and the other
in `V(A' ∩ B')` (hypothesis (ii) of Graph Minors XXI, (2.5), (2.6), (2.7)). -/
def IsTransferLinkage (A B A' B' M : Hypergraph α β) (k : ℕ) : Prop :=
  IsLinkage (B ∩ A') M ∧
  (linkagePattern M).ncard = k ∧
  ∀ P ∈ linkagePattern M, ∃ u ∈ (A ∩ B).vertexSet, ∃ w ∈ (A' ∩ B').vertexSet, P = {u, w}

/-- If `M ≤ G` has 2-ended edges, maximum degree at most `2`, and every vertex of `M` can reach in
`M.skeleton` some vertex of degree at most `1` in `M`, then `M` is a linkage in `G`. -/
lemma isLinkage_of_deg_le_two_of_reachable_deg_le_one {G M : Hypergraph α β}
    (hle : M ≤ G)
    (hloop : ∀ e ∈ M.edgeSet, (M.ends e).ncard = 2)
    (hdeg2 : ∀ v ∈ M.vertexSet, (incidentEdges M v).ncard ≤ 2)
    (hreach : ∀ v ∈ M.vertexSet,
      ∃ w ∈ M.vertexSet, M.skeleton.Reachable v w ∧ (incidentEdges M w).ncard ≤ 1) :
    IsLinkage G M := by
  apply isLinkage_of_deg_le_two_of_exists_deg_one hle hloop hdeg2
  intro H hHM ⟨e₀, he₀⟩
  by_contra! hno1
  have hinc_eq_of_mem : ∀ x : α, (∃ e ∈ H.edgeSet, M.Inc e x) →
      (incidentEdges M x).ncard = 2 ∧ incidentEdges H x = incidentEdges M x := by
    rintro x ⟨e, heH, hincM⟩
    have hincH : H.Inc e x := (inc_iff_of_le hHM heH).2 hincM
    have hxH : x ∈ H.vertexSet := H.vertex_mem_of_inc hincH
    have he_in : e ∈ incidentEdges H x := ⟨heH, hincH⟩
    have hpos : 1 ≤ (incidentEdges H x).ncard :=
      Nat.succ_le_of_lt ((ncard_pos (H.edgeSet_finite.subset fun _ h => h.1)).mpr ⟨e, he_in⟩)
    have hne1 : (incidentEdges H x).ncard ≠ 1 := hno1 x hxH
    have hsub : incidentEdges H x ⊆ incidentEdges M x := incidentEdges_subset_of_le hHM x
    have hle_M : (incidentEdges H x).ncard ≤ (incidentEdges M x).ncard :=
      ncard_le_ncard hsub (M.edgeSet_finite.subset fun _ h => h.1)
    have hle2 : (incidentEdges M x).ncard ≤ 2 := hdeg2 x (M.vertex_mem_of_inc hincM)
    have hcard_H : (incidentEdges H x).ncard = 2 := by omega
    have hcard_M : (incidentEdges M x).ncard = 2 := by omega
    refine ⟨hcard_M, eq_of_subset_of_ncard_le hsub (by omega)
      (M.edgeSet_finite.subset fun _ h => h.1)⟩
  have hclosed : ∀ x y : α, M.skeleton.Reachable x y →
      (∃ e ∈ H.edgeSet, M.Inc e x) → (∃ e ∈ H.edgeSet, M.Inc e y) := by
    intro x y hr
    rcases hr with ⟨p⟩
    induction p with
    | nil => exact id
    | cons hadj _ ih =>
      intro hx
      obtain ⟨_, hinc_eq⟩ := hinc_eq_of_mem _ hx
      obtain ⟨_, e, hinc1, hinc2⟩ := hadj
      have he_in_M : e ∈ incidentEdges M _ := ⟨M.edge_mem_of_inc hinc1, hinc1⟩
      rw [← hinc_eq] at he_in_M
      exact ih ⟨e, he_in_M.1, hinc2⟩
  have he₀M : e₀ ∈ M.edgeSet := hHM.edgeSet_subset he₀
  have h2_ends : (M.ends e₀).Nonempty :=
    nonempty_of_ncard_ne_zero (by rw [hloop e₀ he₀M]; omega)
  obtain ⟨v₀, hv₀_inc⟩ := h2_ends
  have hv₀M : v₀ ∈ M.vertexSet := M.vertex_mem_of_inc hv₀_inc
  obtain ⟨w, _, hrw, hw_le1⟩ := hreach v₀ hv₀M
  have hw_ex : ∃ e ∈ H.edgeSet, M.Inc e w := hclosed v₀ w hrw ⟨e₀, he₀, hv₀_inc⟩
  have hw_eq2 : (incidentEdges M w).ncard = 2 := (hinc_eq_of_mem w hw_ex).1
  omega

/-- Every vertex in a linkage `L` can reach some terminal of `L` in `L.skeleton`. -/
lemma IsLinkage.exists_reachable_terminal {G L : Hypergraph α β}
    (hL : IsLinkage G L) {v : α} (hv : v ∈ L.vertexSet) :
    ∃ z ∈ terminals L, L.skeleton.Reachable v z := by
  let C := reachableComponent L v
  have hC : IsComponentOf L C := isComponentOf_reachableComponent hL.2.1 hv
  have hP : terminals L ∩ C.vertexSet ∈ linkagePattern L := ⟨C, hC, rfl⟩
  rcases hL.mem_linkagePattern_structure hP with
    ⟨z, hz, hz_eq, _⟩ | ⟨z, hz, _, _, _, hz_eq, _, _⟩
  · have hz_in : z ∈ terminals L ∩ C.vertexSet := by rw [hz_eq]; exact rfl
    exact ⟨z, hz, hz_in.2.2⟩
  · have hz_in : z ∈ terminals L ∩ C.vertexSet := by rw [hz_eq]; exact Or.inl rfl
    exact ⟨z, hz, hz_in.2.2⟩

/-- An indexed transfer linkage between `(A ∩ B).vertexSet = range u` and
`(A' ∩ B').vertexSet = range w` with pattern `{{u t, w t} | t : Fin k}`. -/
structure IsIndexedTransferLinkage (A B A' B' M : Hypergraph α β) {k : ℕ}
    (u w : Fin k → α) : Prop where
  isLinkage : IsLinkage (B ∩ A') M
  inj_left : Function.Injective u
  range_left : Set.range u = (A ∩ B).vertexSet
  inj_right : Function.Injective w
  range_right : Set.range w = (A' ∩ B').vertexSet
  pattern_ncard : (linkagePattern M).ncard = k
  pattern_eq : linkagePattern M = Set.range (fun t : Fin k => ({u t, w t} : Set α))

/-- Every `linkagePattern M` is finite. -/
lemma linkagePattern_finite (M : Hypergraph α β) : (linkagePattern M).Finite := by
  have hsub : linkagePattern M ⊆ powerset M.vertexSet := by
    rintro P ⟨C, hC, rfl⟩ x hx
    exact hC.1.vertexSet_subset hx.2
  exact M.vertexSet_finite.powerset.subset hsub

/-- If `IsTransferLinkage A B A' B' M k`, `(A ∩ B).vertexSet.ncard = k`,
`(A' ∩ B').vertexSet.ncard = k`, and `u : Fin k → α` is an injective enumeration of
`(A ∩ B).vertexSet`, then there exists an injective enumeration `w : Fin k → α` of
`(A' ∩ B').vertexSet` such that `IsIndexedTransferLinkage A B A' B' M u w`. -/
lemma exists_next_numbering_of_isTransferLinkage {A B A' B' M : Hypergraph α β} {k : ℕ}
    (hM : IsTransferLinkage A B A' B' M k)
    (hord : (A ∩ B).vertexSet.ncard = k)
    (hord' : (A' ∩ B').vertexSet.ncard = k)
    {u : Fin k → α} (hu_inj : Function.Injective u)
    (hu_range : Set.range u = (A ∩ B).vertexSet) :
    ∃ w : Fin k → α, IsIndexedTransferLinkage A B A' B' M u w := by
  classical
  rcases hM with ⟨hM_link, hM_card, hM_blocks⟩
  have hS_fin : (linkagePattern M).Finite := linkagePattern_finite M
  have hAB_fin : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
  have hA'B'_fin : (A' ∩ B').vertexSet.Finite := (A' ∩ B').vertexSet_finite
  have hdisj : ∀ P₁ ∈ linkagePattern M, ∀ P₂ ∈ linkagePattern M, P₁ ≠ P₂ → Disjoint P₁ P₂ :=
    fun _ h₁ _ h₂ hne => hM_link.disjoint_of_mem_linkagePattern h₁ h₂ hne
  have hmeets_left : ∀ P ∈ linkagePattern M, ∃ x ∈ (A ∩ B).vertexSet, x ∈ P := by
    intro P hP
    obtain ⟨x, hx, y, _, rfl⟩ := hM_blocks P hP
    exact ⟨x, hx, Or.inl rfl⟩
  have hmeets_right : ∀ P ∈ linkagePattern M, ∃ y ∈ (A' ∩ B').vertexSet, y ∈ P := by
    intro P hP
    obtain ⟨x, _, y, hy, rfl⟩ := hM_blocks P hP
    exact ⟨y, hy, Or.inr rfl⟩
  obtain ⟨hsurj_left, huniq_left⟩ :=
    disjoint_family_unique_inter_of_ncard_eq hS_fin hAB_fin hdisj hM_card hord hmeets_left
  obtain ⟨hsurj_right, huniq_right⟩ :=
    disjoint_family_unique_inter_of_ncard_eq hS_fin hA'B'_fin hdisj hM_card hord' hmeets_right
  have hu_mem : ∀ t : Fin k, u t ∈ (A ∩ B).vertexSet := by
    intro t; rw [← hu_range]; exact mem_range_self t
  have hex_w : ∀ t : Fin k, ∃ y ∈ (A' ∩ B').vertexSet, {u t, y} ∈ linkagePattern M := by
    intro t
    obtain ⟨P, hP, hutP⟩ := hsurj_left (u t) (hu_mem t)
    obtain ⟨x, hx, y, hy, hP_eq⟩ := hM_blocks P hP
    have hx_eq : x = u t :=
      huniq_left P hP x ⟨hP_eq ▸ Or.inl rfl, hx⟩ (u t) ⟨hutP, hu_mem t⟩
    refine ⟨y, hy, ?_⟩
    rwa [← hx_eq, ← hP_eq]
  let w : Fin k → α := fun t => Classical.choose (hex_w t)
  have hw_spec : ∀ t : Fin k, w t ∈ (A' ∩ B').vertexSet ∧ {u t, w t} ∈ linkagePattern M :=
    fun t => Classical.choose_spec (hex_w t)
  have hw_inj : Function.Injective w := by
    intro t₁ t₂ hw_eq
    have hP₁ := (hw_spec t₁).2
    have hP₂ := (hw_spec t₂).2
    have h_same_block : ({u t₁, w t₁} : Set α) = {u t₂, w t₂} := by
      by_contra hne
      have hw₁_mem : w t₁ ∈ ({u t₁, w t₁} : Set α) := Or.inr rfl
      have hw₂_mem : w t₁ ∈ ({u t₂, w t₂} : Set α) := hw_eq ▸ Or.inr rfl
      exact Set.disjoint_left.mp (hdisj _ hP₁ _ hP₂ hne) hw₁_mem hw₂_mem
    have hu_eq : u t₁ = u t₂ := by
      apply huniq_left {u t₁, w t₁} hP₁ (u t₁) ⟨Or.inl rfl, hu_mem t₁⟩ (u t₂)
      exact ⟨h_same_block ▸ Or.inl rfl, hu_mem t₂⟩
    exact hu_inj hu_eq
  have hw_range : Set.range w = (A' ∩ B').vertexSet := by
    apply eq_of_subset_of_ncard_le _ _ hA'B'_fin
    · rintro y ⟨t, rfl⟩
      exact (hw_spec t).1
    · rw [ncard_range_of_injective hw_inj, Nat.card_eq_fintype_card, Fintype.card_fin, hord']
  have hpat_eq : linkagePattern M = Set.range (fun t : Fin k => ({u t, w t} : Set α)) := by
    apply Subset.antisymm
    · intro P hP
      obtain ⟨x, hx, y, hy, hP_eq⟩ := hM_blocks P hP
      have hx_r : x ∈ Set.range u := hu_range.symm ▸ hx
      rcases hx_r with ⟨t, rfl⟩
      have hP_eq_t : P = {u t, w t} := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisj P hP _ (hw_spec t).2 hne)
          (hP_eq ▸ Or.inl rfl) (Or.inl rfl)
      exact ⟨t, hP_eq_t.symm⟩
    · rintro P ⟨t, rfl⟩
      exact (hw_spec t).2
  exact ⟨w, hM_link, hu_inj, hu_range, hw_inj, hw_range, hM_card, hpat_eq⟩

/-- Basic structural properties of an indexed transfer linkage `IsIndexedTransferLinkage A B A' B' M u w`. -/
lemma IsIndexedTransferLinkage.props {A B A' B' M : Hypergraph α β} {k : ℕ}
    {u w : Fin k → α} (hM : IsIndexedTransferLinkage A B A' B' M u w) :
    terminals M = (A ∩ B).vertexSet ∪ (A' ∩ B').vertexSet ∧
    (∀ t₁ t₂ : Fin k, ({u t₁, w t₁} : Set α) = {u t₂, w t₂} → t₁ = t₂) ∧
    (∀ t : Fin k, u t ∈ (A' ∩ B').vertexSet → u t = w t) ∧
    (∀ t : Fin k, w t ∈ (A ∩ B).vertexSet → u t = w t) ∧
    (∀ t₁ t₂ : Fin k, u t₁ = w t₂ → t₁ = t₂ ∧ u t₁ = w t₁) ∧
    (∀ t : Fin k, u t = w t → (incidentEdges M (u t)).ncard = 0) ∧
    (∀ t : Fin k, u t ≠ w t →
      (incidentEdges M (u t)).ncard = 1 ∧
      (incidentEdges M (w t)).ncard = 1 ∧
      M.skeleton.Reachable (u t) (w t)) := by
  have hterm : terminals M = (A ∩ B).vertexSet ∪ (A' ∩ B').vertexSet := by
    rw [hM.isLinkage.terminals_eq_sUnion_linkagePattern, hM.pattern_eq,
      ← hM.range_left, ← hM.range_right]
    ext x
    simp only [mem_sUnion, mem_range, exists_exists_eq_and, mem_insert_iff, mem_singleton_iff,
      mem_union]
    exact ⟨fun ⟨t, h⟩ => h.elim (fun h1 => Or.inl ⟨t, h1.symm⟩) (fun h2 => Or.inr ⟨t, h2.symm⟩),
      fun h => h.elim (fun ⟨t, h1⟩ => ⟨t, Or.inl h1.symm⟩) (fun ⟨t, h2⟩ => ⟨t, Or.inr h2.symm⟩)⟩
  have hS_fin : (linkagePattern M).Finite := linkagePattern_finite M
  have hAB_fin : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
  have hA'B'_fin : (A' ∩ B').vertexSet.Finite := (A' ∩ B').vertexSet_finite
  have hdisj : ∀ P₁ ∈ linkagePattern M, ∀ P₂ ∈ linkagePattern M, P₁ ≠ P₂ → Disjoint P₁ P₂ :=
    fun _ h₁ _ h₂ hne => hM.isLinkage.disjoint_of_mem_linkagePattern h₁ h₂ hne
  have hpat_t : ∀ t : Fin k, ({u t, w t} : Set α) ∈ linkagePattern M := by
    intro t; rw [hM.pattern_eq]; exact mem_range_self t
  have hu_mem : ∀ t : Fin k, u t ∈ (A ∩ B).vertexSet := by
    intro t; rw [← hM.range_left]; exact mem_range_self t
  have hw_mem : ∀ t : Fin k, w t ∈ (A' ∩ B').vertexSet := by
    intro t; rw [← hM.range_right]; exact mem_range_self t
  have hord : (A ∩ B).vertexSet.ncard = k := by
    rw [← hM.range_left, ncard_range_of_injective hM.inj_left,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hord' : (A' ∩ B').vertexSet.ncard = k := by
    rw [← hM.range_right, ncard_range_of_injective hM.inj_right,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hmeets_left : ∀ P ∈ linkagePattern M, ∃ x ∈ (A ∩ B).vertexSet, x ∈ P := by
    intro P hP
    rw [hM.pattern_eq] at hP
    rcases hP with ⟨t, rfl⟩
    exact ⟨u t, hu_mem t, Or.inl rfl⟩
  have hmeets_right : ∀ P ∈ linkagePattern M, ∃ y ∈ (A' ∩ B').vertexSet, y ∈ P := by
    intro P hP
    rw [hM.pattern_eq] at hP
    rcases hP with ⟨t, rfl⟩
    exact ⟨w t, hw_mem t, Or.inr rfl⟩
  obtain ⟨_, huniq_left⟩ :=
    disjoint_family_unique_inter_of_ncard_eq hS_fin hAB_fin hdisj hM.pattern_ncard hord hmeets_left
  obtain ⟨_, huniq_right⟩ :=
    disjoint_family_unique_inter_of_ncard_eq hS_fin hA'B'_fin hdisj hM.pattern_ncard hord' hmeets_right
  have hblock_inj : ∀ t₁ t₂ : Fin k, ({u t₁, w t₁} : Set α) = {u t₂, w t₂} → t₁ = t₂ := by
    intro t₁ t₂ heq
    apply hM.inj_left
    exact huniq_left {u t₁, w t₁} (hpat_t t₁)
      (u t₁) ⟨Or.inl rfl, hu_mem t₁⟩
      (u t₂) ⟨heq ▸ Or.inl rfl, hu_mem t₂⟩
  have hu_in_right : ∀ t : Fin k, u t ∈ (A' ∩ B').vertexSet → u t = w t := by
    intro t hu_right
    exact huniq_right {u t, w t} (hpat_t t)
      (u t) ⟨Or.inl rfl, hu_right⟩
      (w t) ⟨Or.inr rfl, hw_mem t⟩
  have hw_in_left : ∀ t : Fin k, w t ∈ (A ∩ B).vertexSet → u t = w t := by
    intro t hw_left
    exact huniq_left {u t, w t} (hpat_t t)
      (u t) ⟨Or.inl rfl, hu_mem t⟩
      (w t) ⟨Or.inr rfl, hw_left⟩
  have hu_eq_w : ∀ t₁ t₂ : Fin k, u t₁ = w t₂ → t₁ = t₂ ∧ u t₁ = w t₁ := by
    intro t₁ t₂ heq
    have hu_w1 : u t₁ = w t₁ := hu_in_right t₁ (heq ▸ hw_mem t₂)
    have hw_eq : w t₁ = w t₂ := hu_w1.symm.trans heq
    exact ⟨hM.inj_right hw_eq, hu_w1⟩
  have hdeg0 : ∀ t : Fin k, u t = w t → (incidentEdges M (u t)).ncard = 0 := by
    intro t heq
    have hP : ({u t} : Set α) ∈ linkagePattern M := by
      have hP' := hpat_t t
      rwa [← heq, pair_eq_singleton] at hP'
    have hut_M : u t ∈ M.vertexSet := by
      have : u t ∈ terminals M := by rw [hterm]; exact Or.inl (hu_mem t)
      exact this.1
    exact (hM.isLinkage.ncard_incidentEdges_eq_zero_iff hut_M).mpr hP
  have hdeg1 : ∀ t : Fin k, u t ≠ w t →
      (incidentEdges M (u t)).ncard = 1 ∧
      (incidentEdges M (w t)).ncard = 1 ∧
      M.skeleton.Reachable (u t) (w t) := by
    intro t hne
    have hP := hpat_t t
    have hut_term : u t ∈ terminals M := by rw [hterm]; exact Or.inl (hu_mem t)
    have hwt_term : w t ∈ terminals M := by rw [hterm]; exact Or.inr (hw_mem t)
    have hreach : M.skeleton.Reachable (u t) (w t) :=
      (hM.isLinkage.pair_mem_linkagePattern_iff hut_term hwt_term hne).mp hP
    rcases hM.isLinkage.mem_linkagePattern_structure hP with
      ⟨z, _, hz_eq, _⟩ | ⟨x, _, y, _, _, hxy_eq, hx1, hy1⟩
    · exfalso
      have : ({u t, w t} : Set α).ncard = ({z} : Set α).ncard := by rw [hz_eq]
      rw [ncard_pair hne, ncard_singleton] at this
      omega
    · have hut_xy : u t ∈ ({x, y} : Set α) := by rw [← hxy_eq]; exact Or.inl rfl
      have hwt_xy : w t ∈ ({x, y} : Set α) := by rw [← hxy_eq]; exact Or.inr rfl
      refine ⟨?_, ?_, hreach⟩
      · rcases hut_xy with rfl | rfl
        · exact hx1
        · exact hy1
      · rcases hwt_xy with rfl | rfl
        · exact hx1
        · exact hy1
  exact ⟨hterm, hblock_inj, hu_in_right, hw_in_left, hu_eq_w, hdeg0, hdeg1⟩

/-- If `A₁ ≤ A₂` and `B₁ ≤ B₂`, then `A₁ ∩ B₁ ≤ A₂ ∩ B₂`. -/
lemma inter_le_inter_of_le {A₁ A₂ B₁ B₂ : Hypergraph α β}
    (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂) : A₁ ∩ B₁ ≤ A₂ ∩ B₂ where
  vertexSet_subset := fun _ h => ⟨hA.vertexSet_subset h.1, hB.vertexSet_subset h.2⟩
  edgeSet_subset := fun _ h => ⟨hA.edgeSet_subset h.1, hB.edgeSet_subset h.2⟩
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, mem_ofPred_eq, inter_inc]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(inc_iff_of_le hA he.1).2 h1, (inc_iff_of_le hB he.2).2 h2⟩,
      fun ⟨h1, h2⟩ => ⟨inc_of_le hA h1, inc_of_le hB h2⟩⟩

/-- Gluing two adjacent indexed transfer linkages `M₁` (in `B₁ ∩ A₂`) and `M₂` (in `B₂ ∩ A₃`)
along the middle separator `(A₂, B₂)` yields an indexed transfer linkage `M₁ ∪ M₂` in `B₁ ∩ A₃`. -/
lemma union_isIndexedTransferLinkage {G A₁ B₁ A₂ B₂ A₃ B₃ M₁ M₂ : Hypergraph α β} {k : ℕ}
    {u₁ u₂ u₃ : Fin k → α}
    (_hsep₁ : G.IsSeparation A₁ B₁)
    (hsep₂ : G.IsSeparation A₂ B₂)
    (_hsep₃ : G.IsSeparation A₃ B₃)
    (hA₁₂ : A₁ ≤ A₂) (hA₂₃ : A₂ ≤ A₃)
    (hB₂₁ : B₂ ≤ B₁) (hB₃₂ : B₃ ≤ B₂)
    (hM₁ : IsIndexedTransferLinkage A₁ B₁ A₂ B₂ M₁ u₁ u₂)
    (hM₂ : IsIndexedTransferLinkage A₂ B₂ A₃ B₃ M₂ u₂ u₃) :
    IsIndexedTransferLinkage A₁ B₁ A₃ B₃ (M₁ ∪ M₂) u₁ u₃ := by
  obtain ⟨hterm₁, hbinj₁, hu₁_right, hu₂_left, hu₁₂_eq, hdeg0₁, hdeg1₁⟩ := hM₁.props
  obtain ⟨hterm₂, hbinj₂, hu₂_right, hu₃_left, hu₂₃_eq, hdeg0₂, hdeg1₂⟩ := hM₂.props
  have hB₁A₂_le : B₁ ∩ A₂ ≤ B₁ ∩ A₃ := inter_le_inter_of_le (le_refl B₁) hA₂₃
  have hB₂A₃_le : B₂ ∩ A₃ ≤ B₁ ∩ A₃ := inter_le_inter_of_le hB₂₁ (le_refl A₃)
  have hM₁_le : M₁ ≤ B₁ ∩ A₃ := le_trans hM₁.isLinkage.1 hB₁A₂_le
  have hM₂_le : M₂ ≤ B₁ ∩ A₃ := le_trans hM₂.isLinkage.1 hB₂A₃_le
  have hM_le : M₁ ∪ M₂ ≤ B₁ ∩ A₃ := union_le hM₁_le hM₂_le
  have hM₁_sub_M : M₁ ≤ M₁ ∪ M₂ := le_union_left hM₁_le hM₂_le
  have hM₂_sub_M : M₂ ≤ M₁ ∪ M₂ := le_union_right hM₁_le hM₂_le
  have hdisj_A₂B₂ : Disjoint A₂.edgeSet B₂.edgeSet :=
    Set.disjoint_left.mpr fun _ heA heB => hsep₂.notMem_edgeSet_right heA heB
  have hdisj_M : Disjoint M₁.edgeSet M₂.edgeSet :=
    hdisj_A₂B₂.mono
      (fun _ he => (hM₁.isLinkage.1.edgeSet_subset he).2)
      (fun _ he => (hM₂.isLinkage.1.edgeSet_subset he).1)
  have hloop_M : ∀ e ∈ (M₁ ∪ M₂).edgeSet, ((M₁ ∪ M₂).ends e).ncard = 2 :=
    ends_ncard_union_of_disjoint hdisj_M
      (fun e he => hM₁.isLinkage.ends_ncard_eq_two he)
      (fun e he => hM₂.isLinkage.ends_ncard_eq_two he)
  have hu₁_mem : ∀ t : Fin k, u₁ t ∈ (A₁ ∩ B₁).vertexSet := by
    intro t; rw [← hM₁.range_left]; exact mem_range_self t
  have hu₂_mem : ∀ t : Fin k, u₂ t ∈ (A₂ ∩ B₂).vertexSet := by
    intro t; rw [← hM₁.range_right]; exact mem_range_self t
  have hu₃_mem : ∀ t : Fin k, u₃ t ∈ (A₃ ∩ B₃).vertexSet := by
    intro t; rw [← hM₂.range_right]; exact mem_range_self t
  have hv_inter : M₁.vertexSet ∩ M₂.vertexSet = (A₂ ∩ B₂).vertexSet := by
    apply Subset.antisymm
    · rintro x ⟨hx₁, hx₂⟩
      exact ⟨(hM₁.isLinkage.1.vertexSet_subset hx₁).2, (hM₂.isLinkage.1.vertexSet_subset hx₂).1⟩
    · intro x hx
      have hx₁ : x ∈ terminals M₁ := by rw [hterm₁]; exact Or.inr hx
      have hx₂ : x ∈ terminals M₂ := by rw [hterm₂]; exact Or.inl hx
      exact ⟨hx₁.1, hx₂.1⟩
  have hsep_inter_sub : (A₁ ∩ B₁).vertexSet ∩ (A₃ ∩ B₃).vertexSet ⊆ (A₂ ∩ B₂).vertexSet := by
    rintro x ⟨⟨hxA₁, _⟩, ⟨_, hxB₃⟩⟩
    exact ⟨hA₁₂.vertexSet_subset hxA₁, hB₃₂.vertexSet_subset hxB₃⟩
  have hu₁_in_3 : ∀ t : Fin k, u₁ t ∈ (A₃ ∩ B₃).vertexSet → u₁ t = u₂ t ∧ u₂ t = u₃ t := by
    intro t hu₁3
    have hu₁2 : u₁ t ∈ (A₂ ∩ B₂).vertexSet := hsep_inter_sub ⟨hu₁_mem t, hu₁3⟩
    have heq₁₂ : u₁ t = u₂ t := hu₁_right t hu₁2
    have hu₂3 : u₂ t ∈ (A₃ ∩ B₃).vertexSet := heq₁₂ ▸ hu₁3
    exact ⟨heq₁₂, hu₂_right t hu₂3⟩
  have hu₃_in_1 : ∀ t : Fin k, u₃ t ∈ (A₁ ∩ B₁).vertexSet → u₁ t = u₂ t ∧ u₂ t = u₃ t := by
    intro t hu₃1
    have hu₃2 : u₃ t ∈ (A₂ ∩ B₂).vertexSet := hsep_inter_sub ⟨hu₃1, hu₃_mem t⟩
    have heq₂₃ : u₂ t = u₃ t := hu₃_left t hu₃2
    have hu₂1 : u₂ t ∈ (A₁ ∩ B₁).vertexSet := heq₂₃.symm ▸ hu₃1
    exact ⟨hu₂_left t hu₂1, heq₂₃⟩
  -- Degree formulas in M₁ ∪ M₂
  have hdeg_u₁ : ∀ t : Fin k,
      (u₁ t = u₃ t → (incidentEdges (M₁ ∪ M₂) (u₁ t)).ncard = 0) ∧
      (u₁ t ≠ u₃ t → (incidentEdges (M₁ ∪ M₂) (u₁ t)).ncard = 1) := by
    intro t
    have hsplit := ncard_incidentEdges_union_of_disjoint hdisj_M (u₁ t)
    constructor
    · intro heq₁₃
      obtain ⟨heq₁₂, heq₂₃⟩ := hu₁_in_3 t (heq₁₃ ▸ hu₃_mem t)
      rw [hsplit, hdeg0₁ t heq₁₂, heq₁₂, hdeg0₂ t heq₂₃]
    · intro hne₁₃
      by_cases heq₁₂ : u₁ t = u₂ t
      · have hne₂₃ : u₂ t ≠ u₃ t := fun h => hne₁₃ (heq₁₂.trans h)
        rw [hsplit, hdeg0₁ t heq₁₂, heq₁₂, (hdeg1₂ t hne₂₃).1, zero_add]
      · have hu₁_not_2 : u₁ t ∉ (A₂ ∩ B₂).vertexSet := fun h => heq₁₂ (hu₁_right t h)
        have hu₁_not_M₂ : u₁ t ∉ M₂.vertexSet := fun hM₂v => by
          have hu₁_M₁ : u₁ t ∈ M₁.vertexSet := by
            have : u₁ t ∈ terminals M₁ := by rw [hterm₁]; exact Or.inl (hu₁_mem t)
            exact this.1
          have : u₁ t ∈ M₁.vertexSet ∩ M₂.vertexSet := ⟨hu₁_M₁, hM₂v⟩
          rw [hv_inter] at this
          exact hu₁_not_2 this
        rw [hsplit, (hdeg1₁ t heq₁₂).1, incidentEdges_eq_empty_of_notMem hu₁_not_M₂,
          ncard_empty, add_zero]
  have hdeg_u₃ : ∀ t : Fin k, u₁ t ≠ u₃ t → (incidentEdges (M₁ ∪ M₂) (u₃ t)).ncard = 1 := by
    intro t hne₁₃
    have hsplit := ncard_incidentEdges_union_of_disjoint hdisj_M (u₃ t)
    by_cases heq₂₃ : u₂ t = u₃ t
    · have hne₁₂ : u₁ t ≠ u₂ t := fun h => hne₁₃ (h.trans heq₂₃)
      have h0₂ : (incidentEdges M₂ (u₃ t)).ncard = 0 := by rw [← heq₂₃]; exact hdeg0₂ t heq₂₃
      rw [hsplit, ← heq₂₃, (hdeg1₁ t hne₁₂).2.1, heq₂₃, h0₂, add_zero]
    · have hu₃_not_2 : u₃ t ∉ (A₂ ∩ B₂).vertexSet := fun h => heq₂₃ (hu₃_left t h)
      have hu₃_not_M₁ : u₃ t ∉ M₁.vertexSet := fun hM₁v => by
        have hu₃_M₂ : u₃ t ∈ M₂.vertexSet := by
          have : u₃ t ∈ terminals M₂ := by rw [hterm₂]; exact Or.inr (hu₃_mem t)
          exact this.1
        have : u₃ t ∈ M₁.vertexSet ∩ M₂.vertexSet := ⟨hM₁v, hu₃_M₂⟩
        rw [hv_inter] at this
        exact hu₃_not_2 this
      rw [hsplit, incidentEdges_eq_empty_of_notMem hu₃_not_M₁, ncard_empty,
        (hdeg1₂ t heq₂₃).2.1, zero_add]
  have hdeg_internal : ∀ v ∈ (M₁ ∪ M₂).vertexSet,
      v ∉ (A₁ ∩ B₁).vertexSet ∪ (A₃ ∩ B₃).vertexSet →
      (incidentEdges (M₁ ∪ M₂) v).ncard = 2 := by
    intro v hvM hv_not
    have hsplit := ncard_incidentEdges_union_of_disjoint hdisj_M v
    have hv_not_1 : v ∉ (A₁ ∩ B₁).vertexSet := fun h => hv_not (Or.inl h)
    have hv_not_3 : v ∉ (A₃ ∩ B₃).vertexSet := fun h => hv_not (Or.inr h)
    by_cases hv_2 : v ∈ (A₂ ∩ B₂).vertexSet
    · have hv_r : v ∈ Set.range u₂ := hM₁.range_right.symm ▸ hv_2
      rcases hv_r with ⟨t, rfl⟩
      have hne₁₂ : u₁ t ≠ u₂ t := fun h => hv_not_1 (h ▸ hu₁_mem t)
      have hne₂₃ : u₂ t ≠ u₃ t := fun h => hv_not_3 (h.symm ▸ hu₃_mem t)
      rw [hsplit, (hdeg1₁ t hne₁₂).2.1, (hdeg1₂ t hne₂₃).1]
    · rcases hvM with hvM₁ | hvM₂
      · have hv_not_M₂ : v ∉ M₂.vertexSet := fun hM₂v => by
          have : v ∈ M₁.vertexSet ∩ M₂.vertexSet := ⟨hvM₁, hM₂v⟩
          rw [hv_inter] at this
          exact hv_2 this
        have hv_not_term₁ : v ∉ terminals M₁ := by
          rw [hterm₁]; exact fun h => h.elim hv_not_1 hv_2
        rw [hsplit, (hM₁.isLinkage.notMem_terminals_iff hvM₁).mp hv_not_term₁,
          incidentEdges_eq_empty_of_notMem hv_not_M₂, ncard_empty, add_zero]
      · have hv_not_M₁ : v ∉ M₁.vertexSet := fun hM₁v => by
          have : v ∈ M₁.vertexSet ∩ M₂.vertexSet := ⟨hM₁v, hvM₂⟩
          rw [hv_inter] at this
          exact hv_2 this
        have hv_not_term₂ : v ∉ terminals M₂ := by
          rw [hterm₂]; exact fun h => h.elim hv_2 hv_not_3
        rw [hsplit, incidentEdges_eq_empty_of_notMem hv_not_M₁, ncard_empty,
          (hM₂.isLinkage.notMem_terminals_iff hvM₂).mp hv_not_term₂, zero_add]
  have hdeg2_M : ∀ v ∈ (M₁ ∪ M₂).vertexSet, (incidentEdges (M₁ ∪ M₂) v).ncard ≤ 2 := by
    intro v hvM
    by_cases hv : v ∈ (A₁ ∩ B₁).vertexSet ∪ (A₃ ∩ B₃).vertexSet
    · rcases hv with hv₁ | hv₃
      · rw [← hM₁.range_left] at hv₁
        rcases hv₁ with ⟨t, rfl⟩
        by_cases heq : u₁ t = u₃ t
        · rw [(hdeg_u₁ t).1 heq]; omega
        · rw [(hdeg_u₁ t).2 heq]; omega
      · rw [← hM₂.range_right] at hv₃
        rcases hv₃ with ⟨t, rfl⟩
        by_cases heq : u₁ t = u₃ t
        · rw [← heq, (hdeg_u₁ t).1 heq]; omega
        · rw [hdeg_u₃ t heq]; omega
    · rw [hdeg_internal v hvM hv]
  have hreach_12 : ∀ t : Fin k, (M₁ ∪ M₂).skeleton.Reachable (u₁ t) (u₂ t) := by
    intro t
    by_cases heq : u₁ t = u₂ t
    · rw [heq]
    · exact reachable_of_le hM₁_sub_M (hdeg1₁ t heq).2.2
  have hreach_23 : ∀ t : Fin k, (M₁ ∪ M₂).skeleton.Reachable (u₂ t) (u₃ t) := by
    intro t
    by_cases heq : u₂ t = u₃ t
    · rw [heq]
    · exact reachable_of_le hM₂_sub_M (hdeg1₂ t heq).2.2
  have hreach_13 : ∀ t : Fin k, (M₁ ∪ M₂).skeleton.Reachable (u₁ t) (u₃ t) :=
    fun t => (hreach_12 t).trans (hreach_23 t)
  have hu₁_M : ∀ t : Fin k, u₁ t ∈ (M₁ ∪ M₂).vertexSet := by
    intro t
    left
    have : u₁ t ∈ terminals M₁ := by rw [hterm₁]; exact Or.inl (hu₁_mem t)
    exact this.1
  have hu₃_M : ∀ t : Fin k, u₃ t ∈ (M₁ ∪ M₂).vertexSet := by
    intro t
    right
    have : u₃ t ∈ terminals M₂ := by rw [hterm₂]; exact Or.inr (hu₃_mem t)
    exact this.1
  have hreach_M : ∀ v ∈ (M₁ ∪ M₂).vertexSet,
      ∃ w ∈ (M₁ ∪ M₂).vertexSet, (M₁ ∪ M₂).skeleton.Reachable v w ∧
        (incidentEdges (M₁ ∪ M₂) w).ncard ≤ 1 := by
    intro v hvM
    have hu₁_le1 : ∀ t : Fin k, (incidentEdges (M₁ ∪ M₂) (u₁ t)).ncard ≤ 1 := by
      intro t
      by_cases heq : u₁ t = u₃ t
      · rw [(hdeg_u₁ t).1 heq]; omega
      · rw [(hdeg_u₁ t).2 heq]
    rcases hvM with hvM₁ | hvM₂
    · obtain ⟨z, hz_term₁, hrvz⟩ := hM₁.isLinkage.exists_reachable_terminal hvM₁
      have hrvz_M : (M₁ ∪ M₂).skeleton.Reachable v z := reachable_of_le hM₁_sub_M hrvz
      rw [hterm₁, ← hM₁.range_left, ← hM₁.range_right] at hz_term₁
      rcases hz_term₁ with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨u₁ t, hu₁_M t, hrvz_M, hu₁_le1 t⟩
      · exact ⟨u₁ t, hu₁_M t, hrvz_M.trans (hreach_12 t).symm, hu₁_le1 t⟩
    · obtain ⟨z, hz_term₂, hrvz⟩ := hM₂.isLinkage.exists_reachable_terminal hvM₂
      have hrvz_M : (M₁ ∪ M₂).skeleton.Reachable v z := reachable_of_le hM₂_sub_M hrvz
      rw [hterm₂, ← hM₂.range_left, ← hM₂.range_right] at hz_term₂
      rcases hz_term₂ with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨u₁ t, hu₁_M t, hrvz_M.trans (hreach_12 t).symm, hu₁_le1 t⟩
      · exact ⟨u₁ t, hu₁_M t, hrvz_M.trans (hreach_13 t).symm, hu₁_le1 t⟩
  have hM_link : IsLinkage (B₁ ∩ A₃) (M₁ ∪ M₂) :=
    isLinkage_of_deg_le_two_of_reachable_deg_le_one hM_le hloop_M hdeg2_M hreach_M
  have hterm_M : terminals (M₁ ∪ M₂) = (A₁ ∩ B₁).vertexSet ∪ (A₃ ∩ B₃).vertexSet := by
    ext v
    constructor
    · intro hv_term
      by_contra hv_not
      have h2 := hdeg_internal v hv_term.1 hv_not
      exact (hM_link.notMem_terminals_iff hv_term.1).mpr h2 hv_term
    · intro hv_in
      rcases hv_in with hv₁ | hv₃
      · rw [← hM₁.range_left] at hv₁
        rcases hv₁ with ⟨t, rfl⟩
        rw [hM_link.mem_terminals_iff]
        refine ⟨hu₁_M t, ?_⟩
        by_cases heq : u₁ t = u₃ t
        · rw [(hdeg_u₁ t).1 heq]; omega
        · rw [(hdeg_u₁ t).2 heq]
      · rw [← hM₂.range_right] at hv₃
        rcases hv₃ with ⟨t, rfl⟩
        rw [hM_link.mem_terminals_iff]
        refine ⟨hu₃_M t, ?_⟩
        by_cases heq : u₁ t = u₃ t
        · rw [← heq, (hdeg_u₁ t).1 heq]; omega
        · rw [hdeg_u₃ t heq]
  have hpat_mem : ∀ t : Fin k, ({u₁ t, u₃ t} : Set α) ∈ linkagePattern (M₁ ∪ M₂) := by
    intro t
    by_cases heq : u₁ t = u₃ t
    · rw [← heq, pair_eq_singleton]
      exact (hM_link.ncard_incidentEdges_eq_zero_iff (hu₁_M t)).mp ((hdeg_u₁ t).1 heq)
    · have hu₁_t : u₁ t ∈ terminals (M₁ ∪ M₂) := by rw [hterm_M]; exact Or.inl (hu₁_mem t)
      have hu₃_t : u₃ t ∈ terminals (M₁ ∪ M₂) := by rw [hterm_M]; exact Or.inr (hu₃_mem t)
      exact (hM_link.pair_mem_linkagePattern_iff hu₁_t hu₃_t heq).mpr (hreach_13 t)
  have hpat_eq : linkagePattern (M₁ ∪ M₂) = Set.range (fun t : Fin k => ({u₁ t, u₃ t} : Set α)) := by
    apply Subset.antisymm
    · intro P hP
      have hP_ne : P.Nonempty := by
        rcases hM_link.mem_linkagePattern_structure hP with
          ⟨z, _, rfl, _⟩ | ⟨z, _, _, _, _, rfl, _, _⟩
        · exact ⟨z, rfl⟩
        · exact ⟨z, Or.inl rfl⟩
      obtain ⟨x, hxP⟩ := hP_ne
      have hx_term : x ∈ terminals (M₁ ∪ M₂) := by
        rw [hM_link.terminals_eq_sUnion_linkagePattern]
        exact ⟨P, hP, hxP⟩
      rw [hterm_M, ← hM₁.range_left, ← hM₂.range_right] at hx_term
      have hex_t : ∃ t : Fin k, x ∈ ({u₁ t, u₃ t} : Set α) := by
        rcases hx_term with ⟨t, rfl⟩ | ⟨t, rfl⟩
        · exact ⟨t, Or.inl rfl⟩
        · exact ⟨t, Or.inr rfl⟩
      obtain ⟨t, hxt⟩ := hex_t
      have hP_eq_t : P = {u₁ t, u₃ t} := by
        by_contra hne
        exact Set.disjoint_left.mp
          (hM_link.disjoint_of_mem_linkagePattern hP (hpat_mem t) hne) hxP hxt
      exact ⟨t, hP_eq_t.symm⟩
    · rintro P ⟨t, rfl⟩
      exact hpat_mem t
  have hbinj_M : ∀ t₁ t₂ : Fin k, ({u₁ t₁, u₃ t₁} : Set α) = {u₁ t₂, u₃ t₂} → t₁ = t₂ := by
    intro t₁ t₂ heq
    have hu₁_in : u₁ t₁ ∈ ({u₁ t₂, u₃ t₂} : Set α) := by rw [← heq]; exact Or.inl rfl
    rcases hu₁_in with h1 | h2
    · exact hM₁.inj_left h1
    · obtain ⟨heq₁₂, heq₂₃⟩ := hu₁_in_3 t₁ (h2 ▸ hu₃_mem t₂)
      have hu₃_eq : u₃ t₁ = u₃ t₂ := heq₂₃.symm.trans (heq₁₂.symm.trans h2)
      exact hM₂.inj_right hu₃_eq
  have hpat_ncard : (linkagePattern (M₁ ∪ M₂)).ncard = k := by
    rw [hpat_eq, ncard_range_of_injective hbinj_M,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  exact ⟨hM_link, hM₁.inj_left, hM₁.range_left, hM₂.inj_right, hM₂.range_right,
    hpat_ncard, hpat_eq⟩

/-- Intersecting the glued transfer linkage `M₁ ∪ M₂` with `B₁ ∩ A₂` recovers `M₁`. -/
lemma union_inter_left_eq_of_isIndexedTransferLinkage
    {G A₁ B₁ A₂ B₂ A₃ B₃ M₁ M₂ : Hypergraph α β} {k : ℕ} {u₁ u₂ u₃ : Fin k → α}
    (hsep₂ : G.IsSeparation A₂ B₂)
    (hA₂₃ : A₂ ≤ A₃) (hB₂₁ : B₂ ≤ B₁)
    (hM₁ : IsIndexedTransferLinkage A₁ B₁ A₂ B₂ M₁ u₁ u₂)
    (hM₂ : IsIndexedTransferLinkage A₂ B₂ A₃ B₃ M₂ u₂ u₃) :
    (M₁ ∪ M₂) ∩ (B₁ ∩ A₂) = M₁ := by
  have hB₁A₂_le : B₁ ∩ A₂ ≤ B₁ ∩ A₃ := inter_le_inter_of_le (le_refl B₁) hA₂₃
  have hB₂A₃_le : B₂ ∩ A₃ ≤ B₁ ∩ A₃ := inter_le_inter_of_le hB₂₁ (le_refl A₃)
  have hM_le : M₁ ∪ M₂ ≤ B₁ ∩ A₃ :=
    union_le (le_trans hM₁.isLinkage.1 hB₁A₂_le) (le_trans hM₂.isLinkage.1 hB₂A₃_le)
  have hinter_le : (M₁ ∪ M₂) ∩ (B₁ ∩ A₂) ≤ B₁ ∩ A₂ :=
    inter_le_right hM_le hB₁A₂_le
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hinter_le hM₁.isLinkage.1
  · ext v
    simp only [inter_vertexSet, union_vertexSet, mem_inter_iff, mem_union]
    constructor
    · rintro ⟨hv₁ | hv₂, hvB₁, hvA₂⟩
      · exact hv₁
      · have hv_A₂B₂ : v ∈ (A₂ ∩ B₂).vertexSet :=
          ⟨hvA₂, (hM₂.isLinkage.1.vertexSet_subset hv₂).1⟩
        have hv_term₁ : v ∈ terminals M₁ := by
          rw [hM₁.props.1]; exact Or.inr hv_A₂B₂
        exact hv_term₁.1
    · intro hv₁
      exact ⟨Or.inl hv₁, hM₁.isLinkage.1.vertexSet_subset hv₁⟩
  · ext e
    simp only [inter_edgeSet, union_edgeSet, mem_inter_iff, mem_union]
    constructor
    · rintro ⟨he₁ | he₂, heB₁, heA₂⟩
      · exact he₁
      · exfalso
        exact hsep₂.notMem_edgeSet_right heA₂ (hM₂.isLinkage.1.edgeSet_subset he₂).1
    · intro he₁
      exact ⟨Or.inl he₁, hM₁.isLinkage.1.edgeSet_subset he₁⟩

/-! ## 2. Iterated separator numbering and interval transfer linkages -/

/-- Any finite set `X : Set α` with `X.ncard = k` admits an injective enumeration `u : Fin k → α`
with `Set.range u = X`. -/
lemma exists_injective_range_of_ncard_eq {X : Set α} {k : ℕ}
    (hX_fin : X.Finite) (hX_card : X.ncard = k) :
    ∃ u : Fin k → α, Function.Injective u ∧ Set.range u = X := by
  classical
  have : Fintype X := hX_fin.fintype
  have hcard : Fintype.card X = Fintype.card (Fin k) := by
    rw [← Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hX_card
  let e : Fin k ≃ X := (Fintype.equivOfCardEq hcard).symm
  refine ⟨fun t => (e t).1, ?_, ?_⟩
  · intro t₁ t₂ heq
    exact e.injective (Subtype.ext heq)
  · ext x
    simp only [mem_range]
    exact ⟨fun ⟨t, ht⟩ => ht ▸ (e t).2, fun hx => ⟨e.symm ⟨x, hx⟩, by simp⟩⟩

/-- Given a sequence of separations `(A r, B r)` (`r : Fin (m + 1)`) of order `k` and transfer
linkages `M r` (`r : Fin m`), we can number the vertices of `(A r ∩ B r).vertexSet` as
`v r : Fin k → α` so that every `M r` is an indexed transfer linkage between `v r.castSucc`
and `v r.succ`. -/
lemma exists_indexed_sequence_of_isTransferLinkage
    {k : ℕ} :
    ∀ {m : ℕ} {A B : Fin (m + 1) → Hypergraph α β} {M : Fin m → Hypergraph α β},
      (∀ r : Fin (m + 1), (A r ∩ B r).vertexSet.ncard = k) →
      (∀ r : Fin m, IsTransferLinkage (A r.castSucc) (B r.castSucc) (A r.succ) (B r.succ) (M r) k) →
      ∃ v : Fin (m + 1) → Fin k → α,
        (∀ r : Fin (m + 1), Function.Injective (v r) ∧ Set.range (v r) = (A r ∩ B r).vertexSet) ∧
        (∀ r : Fin m,
          IsIndexedTransferLinkage (A r.castSucc) (B r.castSucc) (A r.succ) (B r.succ)
            (M r) (v r.castSucc) (v r.succ))
  | 0, A, B, _, hord, _ => by
    obtain ⟨u₀, hu₀_inj, hu₀_range⟩ :=
      exists_injective_range_of_ncard_eq (A 0 ∩ B 0).vertexSet_finite (hord 0)
    refine ⟨fun _ => u₀, fun r => ?_, fun r => Fin.elim0 r⟩
    have hr0 : r = 0 := by ext; omega
    rw [hr0]
    exact ⟨hu₀_inj, hu₀_range⟩
  | m + 1, A, B, M, hord, hM => by
    obtain ⟨v₀, hv₀_props, hv₀_M⟩ :=
      exists_indexed_sequence_of_isTransferLinkage
        (A := fun r => A r.castSucc) (B := fun r => B r.castSucc)
        (M := fun r => M r.castSucc)
        (fun r => hord r.castSucc)
        (fun r => hM r.castSucc)
    let r_last : Fin (m + 1) := Fin.last m
    obtain ⟨w, hw_M⟩ :=
      exists_next_numbering_of_isTransferLinkage (hM r_last)
        (hord r_last.castSucc) (hord r_last.succ)
        (hv₀_props r_last).1 (hv₀_props r_last).2
    let v : Fin (m + 2) → Fin k → α := fun r =>
      if h : r.1 < m + 1 then v₀ ⟨r.1, h⟩ else w
    have hv_cast : ∀ r : Fin (m + 1), v r.castSucc = v₀ r := by
      intro r
      dsimp [v]
      split_ifs with h
      · rfl
      · exact absurd r.2 h
    have hv_last : v (Fin.last (m + 1)) = w := by
      dsimp [v]
      split_ifs with h
      · exfalso; exact Nat.lt_irrefl (m + 1) h
      · rfl
    refine ⟨v, ?_, ?_⟩
    · intro r
      refine Fin.lastCases ?_ ?_ r
      · rw [hv_last]
        exact ⟨hw_M.inj_right, hw_M.range_right⟩
      · intro r₀
        rw [hv_cast r₀]
        exact hv₀_props r₀
    · intro r
      refine Fin.lastCases ?_ ?_ r
      · change IsIndexedTransferLinkage _ _ _ _ (M r_last) (v r_last.castSucc) (v (Fin.last (m + 1)))
        rw [hv_cast r_last, hv_last]
        exact hw_M
      · intro r₀
        rw [hv_cast r₀.castSucc]
        have h_succ : r₀.castSucc.succ = r₀.succ.castSucc := by ext; rfl
        rw [h_succ, hv_cast r₀.succ]
        exact hv₀_M r₀

/-- For any `i < j` in `Fin (m + 1)`, gluing the transfer linkages `M r` for `i ≤ r < j` produces
an indexed transfer linkage `M_ij` between `(A i, B i)` and `(A j, B j)` whose intersection with
`B i ∩ A (i + 1)` is `M i`. -/
lemma exists_interval_isIndexedTransferLinkage
    {G : Hypergraph α β} {k m : ℕ}
    {A B : Fin (m + 1) → Hypergraph α β} {M : Fin m → Hypergraph α β}
    {v : Fin (m + 1) → Fin k → α}
    (hsep : ∀ r : Fin (m + 1), G.IsSeparation (A r) (B r))
    (hA_mono : ∀ r₁ r₂ : Fin (m + 1), r₁ ≤ r₂ → A r₁ ≤ A r₂)
    (hB_anti : ∀ r₁ r₂ : Fin (m + 1), r₁ ≤ r₂ → B r₂ ≤ B r₁)
    (hvM : ∀ r : Fin m,
      IsIndexedTransferLinkage (A r.castSucc) (B r.castSucc) (A r.succ) (B r.succ)
        (M r) (v r.castSucc) (v r.succ)) :
    ∀ (d : ℕ) (i j : Fin (m + 1)) (hij : i < j),
      j.1 - i.1 = d →
      let r₀ : Fin m := ⟨i.1, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.2)⟩
      ∃ M_ij : Hypergraph α β,
        IsIndexedTransferLinkage (A i) (B i) (A j) (B j) M_ij (v i) (v j) ∧
        M_ij ∩ (B r₀.castSucc ∩ A r₀.succ) = M r₀ := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro i j hij hd r₀
    have hi_eq : r₀.castSucc = i := by ext; rfl
    by_cases hstep : i.1 + 1 = j.1
    · have hj_eq : r₀.succ = j := by ext; exact hstep
      refine ⟨M r₀, ?_, ?_⟩
      · rw [← hi_eq, ← hj_eq]
        exact hvM r₀
      · exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq
          (inter_le_left (hvM r₀).isLinkage.1 le_rfl) le_rfl
          (inter_eq_self_of_subset_left (hvM r₀).isLinkage.1.vertexSet_subset)
          (inter_eq_self_of_subset_left (hvM r₀).isLinkage.1.edgeSet_subset)
    · have hij' : r₀.succ < j := by
        change i.1 + 1 < j.1
        omega
      have hd' : j.1 - (r₀.succ).1 < d := by
        change j.1 - (i.1 + 1) < d
        omega
      obtain ⟨M', hM'_idx, _⟩ := ih (j.1 - (r₀.succ).1) hd' r₀.succ j hij' rfl
      refine ⟨M r₀ ∪ M', ?_, ?_⟩
      · rw [← hi_eq]
        exact union_isIndexedTransferLinkage
          (hsep r₀.castSucc) (hsep r₀.succ) (hsep j)
          (hA_mono r₀.castSucc r₀.succ (by change i.1 ≤ i.1 + 1; omega))
          (hA_mono r₀.succ j (le_of_lt hij'))
          (hB_anti r₀.castSucc r₀.succ (by change i.1 ≤ i.1 + 1; omega))
          (hB_anti r₀.succ j (le_of_lt hij'))
          (hvM r₀) hM'_idx
      · exact union_inter_left_eq_of_isIndexedTransferLinkage
          (hsep r₀.succ)
          (hA_mono r₀.succ j (le_of_lt hij'))
          (hB_anti r₀.castSucc r₀.succ (by change i.1 ≤ i.1 + 1; omega))
          (hvM r₀) hM'_idx

/-! ## 3. Separator profiles and deterministic single-pair rerouting -/

/-- If `P ∈ S`, `u ∈ P`, and `LB.skeleton.Reachable u v`, then
`(patternSubgraph LB S).skeleton.Reachable u v`. -/
lemma reachable_patternSubgraph_of_mem {LB : Hypergraph α β} {S : Set (Set α)}
    {P : Set α} {u v : α} (hP : P ∈ S) (huP : u ∈ P)
    (hr : LB.skeleton.Reachable u v) :
    (patternSubgraph LB S).skeleton.Reachable u v := by
  have hwalk : ∀ x y : α, LB.skeleton.Walk x y → y ∈ P →
      (patternSubgraph LB S).skeleton.Reachable x y := by
    intro x y p
    induction p with
    | nil =>
      intro _
      exact SimpleGraph.Reachable.refl _
    | @cons x y z hadj p ih =>
      intro hzP
      have hr_zy : LB.skeleton.Reachable z y := ⟨p.reverse⟩
      obtain ⟨hxy, e, hinc_x, hinc_y⟩ := hadj
      have hadj_PS : (patternSubgraph LB S).skeleton.Adj x y :=
        ⟨hxy, e,
          ⟨hinc_x, P, hP, z, hzP, y, hinc_y, hr_zy⟩,
          ⟨hinc_y, P, hP, z, hzP, y, hinc_y, hr_zy⟩⟩
      exact (SimpleGraph.Adj.reachable hadj_PS).trans (ih hzP)
  rcases hr.symm with ⟨p⟩
  exact (hwalk v u p huP).symm

/-- If `H₁ ≤ G`, `H₂ ≤ G`, and `H₁.edgeSet ⊆ H₂.edgeSet`, then reachability in `H₁.skeleton`
implies reachability in `H₂.skeleton`. -/
lemma reachable_of_edgeSet_subset_of_le {G H₁ H₂ : Hypergraph α β}
    (hH₁ : H₁ ≤ G) (hH₂ : H₂ ≤ G) (hE : H₁.edgeSet ⊆ H₂.edgeSet)
    {x y : α} (hr : H₁.skeleton.Reachable x y) :
    H₂.skeleton.Reachable x y := by
  rcases hr with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨hne, e, hinc1, hinc2⟩ := hadj
    have he₂ : e ∈ H₂.edgeSet := hE (H₁.edge_mem_of_inc hinc1)
    have hadj₂ : H₂.skeleton.Adj _ _ :=
      ⟨hne, e,
        (inc_iff_of_le hH₂ he₂).2 (inc_of_le hH₁ hinc1),
        (inc_iff_of_le hH₂ he₂).2 (inc_of_le hH₁ hinc2)⟩
    exact (SimpleGraph.Adj.reachable hadj₂).trans ih

/-- If `H₁ ≤ G`, `H₂ ≤ G`, `N ≤ G`, `N.edgeSet = H₁.edgeSet ∪ H₂.edgeSet`, and
`Disjoint H₁.edgeSet H₂.edgeSet`, then for every vertex `z`,
`incidentEdges N z = incidentEdges H₁ z ∪ incidentEdges H₂ z` and
`(incidentEdges N z).ncard = (incidentEdges H₁ z).ncard + (incidentEdges H₂ z).ncard`. -/
lemma ncard_incidentEdges_of_edgeSet_union {G H₁ H₂ N : Hypergraph α β}
    (hH₁ : H₁ ≤ G) (hH₂ : H₂ ≤ G) (hN : N ≤ G)
    (hE : N.edgeSet = H₁.edgeSet ∪ H₂.edgeSet)
    (hdisj : Disjoint H₁.edgeSet H₂.edgeSet) (z : α) :
    incidentEdges N z = incidentEdges H₁ z ∪ incidentEdges H₂ z ∧
    (incidentEdges N z).ncard = (incidentEdges H₁ z).ncard + (incidentEdges H₂ z).ncard := by
  have heq : incidentEdges N z = incidentEdges H₁ z ∪ incidentEdges H₂ z := by
    ext e
    simp only [incidentEdges, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨heN, hincN⟩
      have hincG : G.Inc e z := inc_of_le hN hincN
      rw [hE] at heN
      rcases heN with he₁ | he₂
      · exact Or.inl ⟨he₁, (inc_iff_of_le hH₁ he₁).2 hincG⟩
      · exact Or.inr ⟨he₂, (inc_iff_of_le hH₂ he₂).2 hincG⟩
    · rintro (⟨he₁, hinc₁⟩ | ⟨he₂, hinc₂⟩)
      · have heN : e ∈ N.edgeSet := by rw [hE]; exact Or.inl he₁
        exact ⟨heN, (inc_iff_of_le hN heN).2 (inc_of_le hH₁ hinc₁)⟩
      · have heN : e ∈ N.edgeSet := by rw [hE]; exact Or.inr he₂
        exact ⟨heN, (inc_iff_of_le hN heN).2 (inc_of_le hH₂ hinc₂)⟩
  refine ⟨heq, ?_⟩
  rw [heq]
  exact ncard_union_eq
    (hdisj.mono (fun _ h => h.1) (fun _ h => h.1))
    (H₁.edgeSet_finite.subset fun _ h => h.1)
    (H₂.edgeSet_finite.subset fun _ h => h.1)

/-- The shifted integer `c_i + q = |V(A_i) ∩ Z| + q - |V(B_i) ∩ Z| ∈ {0, ..., 2q}` from Claim (1)
of Graph Minors XXI, (2.5) (page 3 of the preprint). -/
noncomputable def terminalBalance {q : ℕ} (Z : Set α) (hZ_fin : Z.Finite) (hZ_le : Z.ncard ≤ q)
    (A B : Hypergraph α β) : Fin (2 * q + 1) :=
  ⟨(A.vertexSet ∩ Z).ncard + q - (B.vertexSet ∩ Z).ncard, by
    have hA : (A.vertexSet ∩ Z).ncard ≤ q :=
      (ncard_le_ncard inter_subset_right hZ_fin).trans hZ_le
    omega⟩

/-- **Claim (1)** of the proof of Graph Minors XXI, (2.5) (page 3 of the preprint):
if `A₁ ≤ A₂`, `B₂ ≤ B₁`, and `c_1 = c_2` (`|V(A₁) ∩ Z| - |V(B₁) ∩ Z| = |V(A₂) ∩ Z| - |V(B₂) ∩ Z|`),
then `V(A₁) ∩ Z = V(A₂) ∩ Z` and `V(B₁) ∩ Z = V(B₂) ∩ Z`. -/
lemma lemma_2_5_claim_1 {q : ℕ} {Z : Set α} (hZ_fin : Z.Finite) (hZ_le : Z.ncard ≤ q)
    {A₁ B₁ A₂ B₂ : Hypergraph α β}
    (hA₁₂ : A₁ ≤ A₂) (hB₂₁ : B₂ ≤ B₁)
    (hc : terminalBalance Z hZ_fin hZ_le A₁ B₁ = terminalBalance Z hZ_fin hZ_le A₂ B₂) :
    A₁.vertexSet ∩ Z = A₂.vertexSet ∩ Z ∧ B₁.vertexSet ∩ Z = B₂.vertexSet ∩ Z := by
  have hAZ_sub : A₁.vertexSet ∩ Z ⊆ A₂.vertexSet ∩ Z :=
    inter_subset_inter_left Z hA₁₂.vertexSet_subset
  have hBZ_sub : B₂.vertexSet ∩ Z ⊆ B₁.vertexSet ∩ Z :=
    inter_subset_inter_left Z hB₂₁.vertexSet_subset
  have hAZ₂_fin : (A₂.vertexSet ∩ Z).Finite := hZ_fin.subset inter_subset_right
  have hBZ₁_fin : (B₁.vertexSet ∩ Z).Finite := hZ_fin.subset inter_subset_right
  have hA_le : (A₁.vertexSet ∩ Z).ncard ≤ (A₂.vertexSet ∩ Z).ncard :=
    ncard_le_ncard hAZ_sub hAZ₂_fin
  have hB_le : (B₂.vertexSet ∩ Z).ncard ≤ (B₁.vertexSet ∩ Z).ncard :=
    ncard_le_ncard hBZ_sub hBZ₁_fin
  have hB₁_le_q : (B₁.vertexSet ∩ Z).ncard ≤ q :=
    (ncard_le_ncard inter_subset_right hZ_fin).trans hZ_le
  have hB₂_le_q : (B₂.vertexSet ∩ Z).ncard ≤ q :=
    (ncard_le_ncard inter_subset_right hZ_fin).trans hZ_le
  have hc_val : (A₁.vertexSet ∩ Z).ncard + q - (B₁.vertexSet ∩ Z).ncard =
      (A₂.vertexSet ∩ Z).ncard + q - (B₂.vertexSet ∩ Z).ncard :=
    congrArg Fin.val hc
  refine ⟨eq_of_subset_of_ncard_le hAZ_sub (by omega) hAZ₂_fin,
    (eq_of_subset_of_ncard_le hBZ_sub (by omega) hBZ₁_fin).symm⟩

/-- The set of partitions of subsets of `Z₀` in which each block has cardinality `1` or `2`
(Graph Minors XXI, proof of (2.5), page 4 of the preprint). -/
def SubPartitions12 (Z₀ : Set α) : Set (Set (Set α)) :=
  {π : Set (Set α) |
    (∀ P ∈ π, P ⊆ Z₀ ∧ (P.ncard = 1 ∨ P.ncard = 2)) ∧
    ∀ P₁ ∈ π, ∀ P₂ ∈ π, P₁ ≠ P₂ → Disjoint P₁ P₂}

/-- For a finite set `Z₀`, `SubPartitions12 Z₀` is finite. -/
lemma subPartitions12_finite {Z₀ : Set α} (hZ₀_fin : Z₀.Finite) :
    (SubPartitions12 Z₀).Finite := by
  refine hZ₀_fin.powerset.powerset.subset ?_
  intro π hπ P hP
  exact (hπ.1 P hP).1

/-- If `Z₀` is finite with `Z₀.ncard ≤ N`, there are at most `(N + 1) ^ (2 * N)` partitions of a
subset of `Z₀` in which each block has cardinality `1` or `2` (Graph Minors XXI, proof of (2.5),
page 4 of the preprint). -/
lemma subPartitions12_ncard_le {Z₀ : Set α} {N : ℕ}
    (hZ₀_fin : Z₀.Finite) (hZ₀_le : Z₀.ncard ≤ N) :
    (SubPartitions12 Z₀).ncard ≤ (N + 1) ^ (2 * N) := by
  classical
  have : Fintype Z₀ := hZ₀_fin.fintype
  have : Fintype (SubPartitions12 Z₀) := (subPartitions12_finite hZ₀_fin).fintype
  have hcard_Z₀ : Fintype.card Z₀ ≤ N := by
    rw [← Nat.card_eq_fintype_card]
    exact hZ₀_le
  let partner : SubPartitions12 Z₀ → (Z₀ → Option Z₀) := fun π x =>
    if h : ∃ y : Z₀, ({x.1, y.1} : Set α) ∈ π.1 then some (Classical.choose h) else none
  have hpartner_inj : Function.Injective partner := by
    intro π₁ π₂ h_eq
    ext P
    suffices ∀ (ρ₁ ρ₂ : SubPartitions12 Z₀), partner ρ₁ = partner ρ₂ → ρ₁.1 ⊆ ρ₂.1 from
      ⟨fun hP => this π₁ π₂ h_eq hP, fun hP => this π₂ π₁ h_eq.symm hP⟩
    intro ρ₁ ρ₂ hρ P hP
    obtain ⟨hP_sub, hP_card⟩ := ρ₁.2.1 P hP
    have hex_pair : ∃ x ∈ Z₀, ∃ y ∈ Z₀, P = {x, y} := by
      rcases hP_card with h1 | h2
      · obtain ⟨x, rfl⟩ := ncard_eq_one.mp h1
        have hx : x ∈ Z₀ := hP_sub (mem_singleton x)
        exact ⟨x, hx, x, hx, (pair_eq_singleton x).symm⟩
      · obtain ⟨x, y, _, rfl⟩ := ncard_eq_two.mp h2
        exact ⟨x, hP_sub (Or.inl rfl), y, hP_sub (Or.inr rfl), rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hex_pair
    let x' : Z₀ := ⟨x, hx⟩
    have hex₁ : ∃ z : Z₀, ({x'.1, z.1} : Set α) ∈ ρ₁.1 := ⟨⟨y, hy⟩, hP⟩
    let z := Classical.choose hex₁
    have hz_mem₁ : ({x, z.1} : Set α) ∈ ρ₁.1 := Classical.choose_spec hex₁
    have hp₁ : partner ρ₁ x' = some z := by
      dsimp [partner]
      split_ifs
      rfl
    have hp₂ : partner ρ₂ x' = some z := (congrFun hρ x').symm.trans hp₁
    have hz_mem₂ : ({x, z.1} : Set α) ∈ ρ₂.1 := by
      dsimp [partner] at hp₂
      split_ifs at hp₂ with hex₂
      · injection hp₂ with hz_eq
        exact hz_eq ▸ Classical.choose_spec hex₂
    have hP_eq_xz : ({x, y} : Set α) = {x, z.1} := by
      by_contra hne
      exact Set.disjoint_left.mp (ρ₁.2.2 _ hP _ hz_mem₁ hne) (Or.inl rfl) (Or.inl rfl)
    exact hP_eq_xz.symm ▸ hz_mem₂
  have hle_map : Fintype.card (SubPartitions12 Z₀) ≤ Fintype.card (Z₀ → Option Z₀) :=
    Fintype.card_le_of_injective partner hpartner_inj
  change Nat.card (SubPartitions12 Z₀) ≤ (N + 1) ^ (2 * N)
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (SubPartitions12 Z₀)
      ≤ Fintype.card (Z₀ → Option Z₀) := hle_map
    _ = (Fintype.card Z₀ + 1) ^ Fintype.card Z₀ := by
      rw [Fintype.card_fun, Fintype.card_option]
    _ ≤ (N + 1) ^ Fintype.card Z₀ := Nat.pow_le_pow_left (by omega) _
    _ ≤ (N + 1) ^ (2 * N) := Nat.pow_le_pow_right (by omega) (by omega)

open Classical in
/-- Map sending `u₁ t ↦ u₂ t` for `t : Fin k` and fixing all `x ∉ Set.range u₁`. -/
noncomputable def separatorBijection {k : ℕ} (u₁ u₂ : Fin k → α) (x : α) : α :=
  if h : ∃ t : Fin k, u₁ t = x then u₂ (Classical.choose h) else x

/-- `separatorBijection u₁ u₂` maps `u₁ t` to `u₂ t` when `u₁` is injective. -/
lemma separatorBijection_apply_u {k : ℕ} {u₁ u₂ : Fin k → α}
    (hu₁_inj : Function.Injective u₁) (t : Fin k) :
    separatorBijection u₁ u₂ (u₁ t) = u₂ t := by
  dsimp [separatorBijection]
  split_ifs with hex
  · exact congrArg u₂ (hu₁_inj (Classical.choose_spec hex))
  · exact (hex ⟨t, rfl⟩).elim

/-- `separatorBijection u₁ u₂` fixes every vertex outside `Set.range u₁`. -/
lemma separatorBijection_apply_of_notMem_range {k : ℕ} {u₁ u₂ : Fin k → α}
    {x : α} (hx : x ∉ Set.range u₁) :
    separatorBijection u₁ u₂ x = x := by
  dsimp [separatorBijection]
  split_ifs with hex
  · exact (hx hex).elim
  · rfl

/-- The set `Z_i = V(A_i ∩ B_i) ∪ (Z ∩ V(B_i))` from the proof of Graph Minors XXI, (2.5)
(page 3 of the preprint). -/
def rightTerminalSet (Z : Set α) (A B : Hypergraph α β) : Set α :=
  (A ∩ B).vertexSet ∪ (Z ∩ B.vertexSet)

/-- By (2.2), `rightTerminalSet Z A B` contains every terminal of `L ∩ B` whenever
`terminals L ⊆ Z`. -/
lemma terminals_inter_subset_rightTerminalSet {G L A B : Hypergraph α β} {Z : Set α}
    (hL : IsLinkage G L) (hZ_sub : terminals L ⊆ Z) (hsep : G.IsSeparation A B) :
    terminals (L ∩ B) ⊆ rightTerminalSet Z A B := by
  intro x hx
  have hxL : x ∈ L.vertexSet := hx.1.1
  have hxB : x ∈ B.vertexSet := hx.1.2
  by_cases hxA : x ∈ A.vertexSet
  · exact Or.inl ⟨hxA, hxB⟩
  · right
    refine ⟨hZ_sub ⟨hxL, ?_⟩, hxB⟩
    have hLB_le : L ∩ B ≤ L := inter_le_left hL.1 hsep.right_le
    rw [hL.vertexDegree_eq_ncard_incidentEdges_of_le le_rfl x]
    have hdeg_LB := hx.2
    rw [hL.vertexDegree_eq_ncard_incidentEdges_of_le hLB_le x] at hdeg_LB
    have hinc_eq : incidentEdges L x = incidentEdges (L ∩ B) x := by
      ext e
      simp only [incidentEdges, mem_ofPred_eq, inter_edgeSet, inter_inc]
      refine ⟨fun ⟨heL, hincL⟩ => ?_, fun ⟨⟨heL, _⟩, hincL, _⟩ => ⟨heL, hincL⟩⟩
      have heG : e ∈ G.edgeSet := hL.1.edgeSet_subset heL
      have hincG : G.Inc e x := inc_of_le hL.1 hincL
      have heAB : e ∈ A.edgeSet ∪ B.edgeSet := by rwa [hsep.edgeSet_union]
      have heB : e ∈ B.edgeSet := heAB.resolve_left fun heA =>
        hxA (A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le heA).2 hincG))
      exact ⟨⟨heL, heB⟩, hincL, (inc_iff_of_le hsep.right_le heB).2 hincG⟩
    rwa [hinc_eq]

/-- When `A₀ ≤ Aᵢ` and `Bᵢ ≤ B₀`, the map `φᵢ = separatorBijection uᵢ u₀` maps
`Zᵢ = rightTerminalSet Z Aᵢ Bᵢ` injectively into `Z₀ = rightTerminalSet Z A₀ B₀` and sends
`linkagePattern (L ∩ Bᵢ)` into `SubPartitions12 Z₀` (Graph Minors XXI, proof of (2.5), page 4 of the
preprint). -/
lemma separatorBijection_mapsTo_and_injOn {G L A₀ B₀ Aᵢ Bᵢ : Hypergraph α β} {Z : Set α} {k : ℕ}
    {u₀ uᵢ : Fin k → α}
    (hL : IsLinkage G L) (hZ_sub : terminals L ⊆ Z)
    (hsepᵢ : G.IsSeparation Aᵢ Bᵢ)
    (hA₀ᵢ : A₀ ≤ Aᵢ) (hBᵢ₀ : Bᵢ ≤ B₀)
    (hu₀_inj : Function.Injective u₀) (hu₀_range : Set.range u₀ = (A₀ ∩ B₀).vertexSet)
    (huᵢ_inj : Function.Injective uᵢ) (huᵢ_range : Set.range uᵢ = (Aᵢ ∩ Bᵢ).vertexSet) :
    let φᵢ := separatorBijection uᵢ u₀
    let Z₀ := rightTerminalSet Z A₀ B₀
    let Zᵢ := rightTerminalSet Z Aᵢ Bᵢ
    MapsTo φᵢ Zᵢ Z₀ ∧
    InjOn φᵢ Zᵢ ∧
    (Set.image φᵢ) '' (linkagePattern (L ∩ Bᵢ)) ∈ SubPartitions12 Z₀ := by
  intro φᵢ Z₀ Zᵢ
  have hφ_u : ∀ t : Fin k, φᵢ (uᵢ t) = u₀ t :=
    fun t => separatorBijection_apply_u huᵢ_inj t
  have hφ_in_AB₀ : ∀ x ∈ (Aᵢ ∩ Bᵢ).vertexSet, φᵢ x ∈ (A₀ ∩ B₀).vertexSet := by
    intro x hx
    rw [← huᵢ_range] at hx
    rcases hx with ⟨t, rfl⟩
    rw [hφ_u t, ← hu₀_range]
    exact mem_range_self t
  have hφ_not_ABᵢ : ∀ x ∉ (Aᵢ ∩ Bᵢ).vertexSet, φᵢ x = x := by
    intro x hx
    exact separatorBijection_apply_of_notMem_range (huᵢ_range.symm ▸ hx)
  have hmaps : MapsTo φᵢ Zᵢ Z₀ := by
    intro x hx
    by_cases hx_AB : x ∈ (Aᵢ ∩ Bᵢ).vertexSet
    · exact Or.inl (hφ_in_AB₀ x hx_AB)
    · rw [hφ_not_ABᵢ x hx_AB]
      rcases hx with hx_AB' | ⟨hxZ, hxBᵢ⟩
      · exact (hx_AB hx_AB').elim
      · exact Or.inr ⟨hxZ, hBᵢ₀.vertexSet_subset hxBᵢ⟩
  have hφ_mem_Aᵢ_iff : ∀ x ∈ Zᵢ, φᵢ x ∈ Aᵢ.vertexSet ↔ x ∈ (Aᵢ ∩ Bᵢ).vertexSet := by
    intro x hx
    by_cases hx_AB : x ∈ (Aᵢ ∩ Bᵢ).vertexSet
    · refine ⟨fun _ => hx_AB, fun _ => ?_⟩
      exact hA₀ᵢ.vertexSet_subset (hφ_in_AB₀ x hx_AB).1
    · rw [hφ_not_ABᵢ x hx_AB]
      have hxBᵢ : x ∈ Bᵢ.vertexSet := by
        rcases hx with h1 | h2
        · exact h1.2
        · exact h2.2
      exact ⟨fun hxAᵢ => (hx_AB ⟨hxAᵢ, hxBᵢ⟩).elim, fun h => (hx_AB h).elim⟩
  have hinj : InjOn φᵢ Zᵢ := by
    intro x hx y hy heq
    have hiff : x ∈ (Aᵢ ∩ Bᵢ).vertexSet ↔ y ∈ (Aᵢ ∩ Bᵢ).vertexSet := by
      rw [← hφ_mem_Aᵢ_iff x hx, ← hφ_mem_Aᵢ_iff y hy, heq]
    by_cases hx_AB : x ∈ (Aᵢ ∩ Bᵢ).vertexSet
    · have hy_AB : y ∈ (Aᵢ ∩ Bᵢ).vertexSet := hiff.mp hx_AB
      rw [← huᵢ_range] at hx_AB hy_AB
      rcases hx_AB with ⟨s, rfl⟩
      rcases hy_AB with ⟨t, rfl⟩
      rw [hφ_u s, hφ_u t] at heq
      exact congrArg uᵢ (hu₀_inj heq)
    · have hy_AB : y ∉ (Aᵢ ∩ Bᵢ).vertexSet := mt hiff.mpr hx_AB
      rwa [hφ_not_ABᵢ x hx_AB, hφ_not_ABᵢ y hy_AB] at heq
  refine ⟨hmaps, hinj, ?_⟩
  have hLᵢ : IsLinkage Bᵢ (L ∩ Bᵢ) :=
    isLinkage_of_le hL (inter_le_left hL.1 hsepᵢ.right_le) (inter_le_right hL.1 hsepᵢ.right_le)
  have hterm_sub : terminals (L ∩ Bᵢ) ⊆ Zᵢ :=
    terminals_inter_subset_rightTerminalSet hL hZ_sub hsepᵢ
  have hP_sub_Zᵢ : ∀ P ∈ linkagePattern (L ∩ Bᵢ), P ⊆ Zᵢ := by
    rintro P ⟨C, _, rfl⟩
    exact Subset.trans inter_subset_left hterm_sub
  refine ⟨?_, ?_⟩
  · rintro Q ⟨P, hP, rfl⟩
    have hPZᵢ : P ⊆ Zᵢ := hP_sub_Zᵢ P hP
    have hcard_eq : (φᵢ '' P).ncard = P.ncard := (hinj.mono hPZᵢ).ncard_image
    refine ⟨image_subset_iff.mpr (Subset.trans hPZᵢ hmaps), ?_⟩
    rw [hcard_eq]
    rcases hLᵢ.mem_linkagePattern_structure hP with
      ⟨a, _, rfl, _⟩ | ⟨a, _, b, _, hab, rfl, _, _⟩
    · exact Or.inl (ncard_singleton a)
    · exact Or.inr (ncard_pair hab)
  · rintro Q₁ ⟨P₁, hP₁, rfl⟩ Q₂ ⟨P₂, hP₂, rfl⟩ hne
    have hP_ne : P₁ ≠ P₂ := fun h => hne (h ▸ rfl)
    have hdisj : Disjoint P₁ P₂ := hLᵢ.disjoint_of_mem_linkagePattern hP₁ hP₂ hP_ne
    rw [Set.disjoint_left]
    rintro z ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, heq⟩
    have hx_eq : x₁ = x₂ := hinj (hP_sub_Zᵢ P₁ hP₁ hx₁) (hP_sub_Zᵢ P₂ hP₂ hx₂) heq.symm
    exact Set.disjoint_left.mp hdisj hx₁ (hx_eq ▸ hx₂)

/-- **Claim (2)** of the proof of Graph Minors XXI, (2.5) (page 4 of the preprint) and its
structural consequences for `ψ = separatorBijection u₁ u₂`: if `V(A₁) ∩ Z = V(A₂) ∩ Z`,
`V(B₁) ∩ Z = V(B₂) ∩ Z`, and `φ₁(π₁) = φ₂(π₂)`, then for `1 ≤ t ≤ k` the degree of `v_i^t` in
`L_i` equals the degree of `v_j^t` in `L_j`, if one of `v_i^t, v_j^t` is in `Z` then `v_i^t = v_j^t`,
and `ψ` preserves terminal degrees and component reachability between `L₁` and `L₂`. -/
lemma lemma_2_5_claim_2 {G L A₀ B₀ A₁ B₁ A₂ B₂ M : Hypergraph α β} {Z : Set α} {k : ℕ}
    {u₀ u₁ u₂ : Fin k → α}
    (hL : IsVitalLinkage G L)
    (hZ_sub : terminals L ⊆ Z)
    (hsep₁ : G.IsSeparation A₁ B₁)
    (hsep₂ : G.IsSeparation A₂ B₂)
    (hA₀₁ : A₀ ≤ A₁) (hB₁₀ : B₁ ≤ B₀)
    (hA₀₂ : A₀ ≤ A₂) (hB₂₀ : B₂ ≤ B₀)
    (hu₀_inj : Function.Injective u₀) (hu₀_range : Set.range u₀ = (A₀ ∩ B₀).vertexSet)
    (hM : IsIndexedTransferLinkage A₁ B₁ A₂ B₂ M u₁ u₂)
    (hZA : A₁.vertexSet ∩ Z = A₂.vertexSet ∩ Z)
    (hZB : B₁.vertexSet ∩ Z = B₂.vertexSet ∩ Z)
    (hpat_phi :
      (Set.image (separatorBijection u₁ u₀)) '' (linkagePattern (L ∩ B₁)) =
      (Set.image (separatorBijection u₂ u₀)) '' (linkagePattern (L ∩ B₂))) :
    let L₁ := L ∩ B₁
    let L₂ := L ∩ B₂
    let ψ := separatorBijection u₁ u₂
    (∀ z ∈ Z, z ∈ A₁.vertexSet ↔ z ∈ A₂.vertexSet) ∧
    (∀ z ∈ Z, z ∈ B₁.vertexSet ↔ z ∈ B₂.vertexSet) ∧
    (∀ t : Fin k, (u₁ t ∈ Z → u₁ t = u₂ t) ∧ (u₂ t ∈ Z → u₁ t = u₂ t)) ∧
    (∀ t : Fin k, (incidentEdges L₁ (u₁ t)).ncard = (incidentEdges L₂ (u₂ t)).ncard) ∧
    (∀ t : Fin k, ψ (u₁ t) = u₂ t) ∧
    (∀ x : α, x ∉ (A₁ ∩ B₁).vertexSet → ψ x = x) ∧
    (∀ x ∈ terminals L₁, (incidentEdges L₁ x).ncard = (incidentEdges L₂ (ψ x)).ncard) ∧
    (∀ x₁ ∈ terminals L₁, ∀ x₂ ∈ terminals L₁,
      x₁ ≠ x₂ → L₁.skeleton.Reachable x₁ x₂ →
        ψ x₁ ≠ ψ x₂ ∧ L₂.skeleton.Reachable (ψ x₁) (ψ x₂)) := by
  intro L₁ L₂ ψ
  let φ₁ := separatorBijection u₁ u₀
  let φ₂ := separatorBijection u₂ u₀
  let Z₁ := rightTerminalSet Z A₁ B₁
  let Z₂ := rightTerminalSet Z A₂ B₂
  have hL₁ : IsLinkage B₁ L₁ :=
    isLinkage_of_le hL.1 (inter_le_left hL.1.1 hsep₁.right_le) (inter_le_right hL.1.1 hsep₁.right_le)
  have hL₂ : IsLinkage B₂ L₂ :=
    isLinkage_of_le hL.1 (inter_le_left hL.1.1 hsep₂.right_le) (inter_le_right hL.1.1 hsep₂.right_le)
  obtain ⟨_, _, hu₁_right, hu₂_left, _, _, _⟩ := hM.props
  have hinj₁ : InjOn φ₁ Z₁ :=
    (separatorBijection_mapsTo_and_injOn hL.1 hZ_sub hsep₁ hA₀₁ hB₁₀
      hu₀_inj hu₀_range hM.inj_left hM.range_left).2.1
  have hinj₂ : InjOn φ₂ Z₂ :=
    (separatorBijection_mapsTo_and_injOn hL.1 hZ_sub hsep₂ hA₀₂ hB₂₀
      hu₀_inj hu₀_range hM.inj_right hM.range_right).2.1
  have hZ_A : ∀ z ∈ Z, z ∈ A₁.vertexSet ↔ z ∈ A₂.vertexSet := by
    intro z hz
    have hiff := Set.ext_iff.mp hZA z
    simpa [hz] using hiff
  have hZ_B : ∀ z ∈ Z, z ∈ B₁.vertexSet ↔ z ∈ B₂.vertexSet := by
    intro z hz
    have hiff := Set.ext_iff.mp hZB z
    simpa [hz] using hiff
  have hu₁_mem : ∀ t : Fin k, u₁ t ∈ (A₁ ∩ B₁).vertexSet := by
    intro t; rw [← hM.range_left]; exact mem_range_self t
  have hu₂_mem : ∀ t : Fin k, u₂ t ∈ (A₂ ∩ B₂).vertexSet := by
    intro t; rw [← hM.range_right]; exact mem_range_self t
  have hZ_u : ∀ t : Fin k, (u₁ t ∈ Z → u₁ t = u₂ t) ∧ (u₂ t ∈ Z → u₁ t = u₂ t) := by
    intro t
    constructor
    · intro hu₁Z
      have hA₂ : u₁ t ∈ A₂.vertexSet := (hZ_A (u₁ t) hu₁Z).mp (hu₁_mem t).1
      have hB₂ : u₁ t ∈ B₂.vertexSet := (hZ_B (u₁ t) hu₁Z).mp (hu₁_mem t).2
      exact hu₁_right t ⟨hA₂, hB₂⟩
    · intro hu₂Z
      have hA₁ : u₂ t ∈ A₁.vertexSet := (hZ_A (u₂ t) hu₂Z).mpr (hu₂_mem t).1
      have hB₁ : u₂ t ∈ B₁.vertexSet := (hZ_B (u₂ t) hu₂Z).mpr (hu₂_mem t).2
      exact hu₂_left t ⟨hA₁, hB₁⟩
  have hψ_u : ∀ t : Fin k, ψ (u₁ t) = u₂ t :=
    fun t => separatorBijection_apply_u hM.inj_left t
  have hψ_other : ∀ x : α, x ∉ (A₁ ∩ B₁).vertexSet → ψ x = x :=
    fun x hx => separatorBijection_apply_of_notMem_range (hM.range_left.symm ▸ hx)
  have hψ_Z₁ : ∀ x ∈ Z₁, ψ x ∈ Z₂ ∧ φ₂ (ψ x) = φ₁ x := by
    intro x hx
    by_cases hx_AB : x ∈ (A₁ ∩ B₁).vertexSet
    · rw [← hM.range_left] at hx_AB
      rcases hx_AB with ⟨t, rfl⟩
      rw [hψ_u t]
      refine ⟨Or.inl (hu₂_mem t), ?_⟩
      change separatorBijection u₂ u₀ (u₂ t) = separatorBijection u₁ u₀ (u₁ t)
      rw [separatorBijection_apply_u hM.inj_right t, separatorBijection_apply_u hM.inj_left t]
    · have hx_ZB₁ : x ∈ Z ∩ B₁.vertexSet := hx.resolve_left hx_AB
      have hx_notA₁ : x ∉ A₁.vertexSet := fun hA₁ => hx_AB ⟨hA₁, hx_ZB₁.2⟩
      have hx_notA₂ : x ∉ A₂.vertexSet := mt (hZ_A x hx_ZB₁.1).mpr hx_notA₁
      have hx_B₂ : x ∈ B₂.vertexSet := (hZ_B x hx_ZB₁.1).mp hx_ZB₁.2
      have hx_notAB₂ : x ∉ (A₂ ∩ B₂).vertexSet := fun h => hx_notA₂ h.1
      rw [hψ_other x hx_AB]
      refine ⟨Or.inr ⟨hx_ZB₁.1, hx_B₂⟩, ?_⟩
      change separatorBijection u₂ u₀ x = separatorBijection u₁ u₀ x
      rw [separatorBijection_apply_of_notMem_range (hM.range_right.symm ▸ hx_notAB₂),
          separatorBijection_apply_of_notMem_range (hM.range_left.symm ▸ hx_AB)]
  have hinj_ψ : InjOn ψ Z₁ := by
    intro x hx y hy heq
    apply hinj₁ hx hy
    rw [← (hψ_Z₁ x hx).2, ← (hψ_Z₁ y hy).2, heq]
  have hterm₁_sub : terminals L₁ ⊆ Z₁ :=
    terminals_inter_subset_rightTerminalSet hL.1 hZ_sub hsep₁
  have hterm₂_sub : terminals L₂ ⊆ Z₂ :=
    terminals_inter_subset_rightTerminalSet hL.1 hZ_sub hsep₂
  have hP₁_sub : ∀ P ∈ linkagePattern L₁, P ⊆ Z₁ := by
    rintro P ⟨C, _, rfl⟩
    exact Subset.trans inter_subset_left hterm₁_sub
  have hP₂_sub : ∀ Q ∈ linkagePattern L₂, Q ⊆ Z₂ := by
    rintro Q ⟨C, _, rfl⟩
    exact Subset.trans inter_subset_left hterm₂_sub
  have hφ_image_eq : ∀ {P : Set α}, P ⊆ Z₁ → φ₂ '' (ψ '' P) = φ₁ '' P := by
    intro P hP
    rw [← image_comp]
    exact image_congr fun x hx => (hψ_Z₁ x (hP hx)).2
  have hpat_phi' : (Set.image φ₁) '' (linkagePattern L₁) = (Set.image φ₂) '' (linkagePattern L₂) :=
    hpat_phi
  have hpat_iff : ∀ {P : Set α}, P ⊆ Z₁ →
      (ψ '' P ∈ linkagePattern L₂ ↔ P ∈ linkagePattern L₁) := by
    intro P hP
    have hψP_sub : ψ '' P ⊆ Z₂ := by
      rintro y ⟨x, hx, rfl⟩
      exact (hψ_Z₁ x (hP hx)).1
    constructor
    · intro hmem₂
      have him : φ₁ '' P ∈ (Set.image φ₁) '' (linkagePattern L₁) := by
        rw [hpat_phi', ← hφ_image_eq hP]
        exact ⟨ψ '' P, hmem₂, rfl⟩
      rcases him with ⟨P', hP', heq⟩
      have hPP' : P' = P := (hinj₁.image_eq_image_iff (hP₁_sub P' hP') hP).mp heq
      exact hPP' ▸ hP'
    · intro hmem₁
      have him : φ₂ '' (ψ '' P) ∈ (Set.image φ₂) '' (linkagePattern L₂) := by
        rw [hφ_image_eq hP, ← hpat_phi']
        exact ⟨P, hmem₁, rfl⟩
      rcases him with ⟨Q, hQ, heq⟩
      have hQ_eq : Q = ψ '' P := (hinj₂.image_eq_image_iff (hP₂_sub Q hQ) hψP_sub).mp heq
      exact hQ_eq ▸ hQ
  have hterm_iff : ∀ {x : α}, x ∈ Z₁ → (x ∈ terminals L₁ ↔ ψ x ∈ terminals L₂) := by
    intro x hx
    rw [hL₁.terminals_eq_sUnion_linkagePattern, hL₂.terminals_eq_sUnion_linkagePattern,
      mem_sUnion, mem_sUnion]
    constructor
    · rintro ⟨P, hP, hxP⟩
      exact ⟨ψ '' P, (hpat_iff (hP₁_sub P hP)).mpr hP, mem_image_of_mem ψ hxP⟩
    · rintro ⟨Q, hQ, hψx⟩
      have him : φ₂ '' Q ∈ (Set.image φ₁) '' (linkagePattern L₁) := by
        rw [hpat_phi']
        exact ⟨Q, hQ, rfl⟩
      rcases him with ⟨P, hP, heq⟩
      have hP_sub : P ⊆ Z₁ := hP₁_sub P hP
      have hψP_sub : ψ '' P ⊆ Z₂ := by
        rintro y ⟨w, hw, rfl⟩
        exact (hψ_Z₁ w (hP_sub hw)).1
      have hQ_eq : ψ '' P = Q :=
        (hinj₂.image_eq_image_iff hψP_sub (hP₂_sub Q hQ)).mp ((hφ_image_eq hP_sub).trans heq)
      rw [← hQ_eq] at hψx
      rcases hψx with ⟨w, hwP, hw_eq⟩
      have hwx : w = x := hinj_ψ (hP_sub hwP) hx hw_eq
      exact ⟨P, hP, hwx ▸ hwP⟩
  have hdeg_eq_of_mem_Z₁ : ∀ {x : α}, x ∈ Z₁ → x ∈ L₁.vertexSet → ψ x ∈ L₂.vertexSet →
      (incidentEdges L₁ x).ncard = (incidentEdges L₂ (ψ x)).ncard := by
    intro x hxZ₁ hxL₁ hψL₂
    by_cases hterm : x ∈ terminals L₁
    · have hψ_term : ψ x ∈ terminals L₂ := (hterm_iff hxZ₁).mp hterm
      have hsing_iff : ({x} : Set α) ∈ linkagePattern L₁ ↔ ({ψ x} : Set α) ∈ linkagePattern L₂ := by
        have hsub : ({x} : Set α) ⊆ Z₁ := singleton_subset_iff.mpr hxZ₁
        have h := (hpat_iff hsub).symm
        rwa [image_singleton] at h
      by_cases h0 : ({x} : Set α) ∈ linkagePattern L₁
      · have h0' : ({ψ x} : Set α) ∈ linkagePattern L₂ := hsing_iff.mp h0
        rw [(hL₁.ncard_incidentEdges_eq_zero_iff hxL₁).mpr h0,
            (hL₂.ncard_incidentEdges_eq_zero_iff hψL₂).mpr h0']
      · have h0' : ({ψ x} : Set α) ∉ linkagePattern L₂ := mt hsing_iff.mpr h0
        rw [(hL₁.ncard_incidentEdges_eq_one_iff hterm).mpr h0,
            (hL₂.ncard_incidentEdges_eq_one_iff hψ_term).mpr h0']
    · have hψ_not_term : ψ x ∉ terminals L₂ := mt (hterm_iff hxZ₁).mpr hterm
      rw [(hL₁.notMem_terminals_iff hxL₁).mp hterm,
          (hL₂.notMem_terminals_iff hψL₂).mp hψ_not_term]
  have hu_deg : ∀ t : Fin k, (incidentEdges L₁ (u₁ t)).ncard = (incidentEdges L₂ (u₂ t)).ncard := by
    intro t
    have hu₁_Z₁ : u₁ t ∈ Z₁ := Or.inl (hu₁_mem t)
    have hu₁_L₁ : u₁ t ∈ L₁.vertexSet := by
      refine ⟨?_, (hu₁_mem t).2⟩
      rw [hL.2.1]
      exact hsep₁.right_le.vertexSet_subset (hu₁_mem t).2
    have hu₂_L₂ : ψ (u₁ t) ∈ L₂.vertexSet := by
      rw [hψ_u t]
      refine ⟨?_, (hu₂_mem t).2⟩
      rw [hL.2.1]
      exact hsep₂.right_le.vertexSet_subset (hu₂_mem t).2
    have hdeg := hdeg_eq_of_mem_Z₁ hu₁_Z₁ hu₁_L₁ hu₂_L₂
    rwa [hψ_u t] at hdeg
  have hψ_deg : ∀ x ∈ terminals L₁,
      (incidentEdges L₁ x).ncard = (incidentEdges L₂ (ψ x)).ncard := by
    intro x hx
    have hxZ₁ : x ∈ Z₁ := hterm₁_sub hx
    have hψ_term : ψ x ∈ terminals L₂ := (hterm_iff hxZ₁).mp hx
    exact hdeg_eq_of_mem_Z₁ hxZ₁ hx.1 hψ_term.1
  have hψ_reach : ∀ x₁ ∈ terminals L₁, ∀ x₂ ∈ terminals L₁,
      x₁ ≠ x₂ → L₁.skeleton.Reachable x₁ x₂ →
        ψ x₁ ≠ ψ x₂ ∧ L₂.skeleton.Reachable (ψ x₁) (ψ x₂) := by
    intro x₁ hx₁ x₂ hx₂ hne hr₁
    have hx₁Z₁ : x₁ ∈ Z₁ := hterm₁_sub hx₁
    have hx₂Z₁ : x₂ ∈ Z₁ := hterm₁_sub hx₂
    have hψ_ne : ψ x₁ ≠ ψ x₂ := fun h => hne (hinj_ψ hx₁Z₁ hx₂Z₁ h)
    have hψ₁_term : ψ x₁ ∈ terminals L₂ := (hterm_iff hx₁Z₁).mp hx₁
    have hψ₂_term : ψ x₂ ∈ terminals L₂ := (hterm_iff hx₂Z₁).mp hx₂
    have hpair₁ : ({x₁, x₂} : Set α) ∈ linkagePattern L₁ :=
      (hL₁.pair_mem_linkagePattern_iff hx₁ hx₂ hne).mpr hr₁
    have hpair_sub : ({x₁, x₂} : Set α) ⊆ Z₁ := by
      rintro z (rfl | rfl)
      · exact hx₁Z₁
      · exact hx₂Z₁
    have hpair₂ : ({ψ x₁, ψ x₂} : Set α) ∈ linkagePattern L₂ := by
      have h := (hpat_iff hpair_sub).mpr hpair₁
      rwa [image_pair] at h
    exact ⟨hψ_ne, (hL₂.pair_mem_linkagePattern_iff hψ₁_term hψ₂_term hψ_ne).mp hpair₂⟩
  exact ⟨hZ_A, hZ_B, hZ_u, hu_deg, hψ_u, hψ_other, hψ_deg, hψ_reach⟩

/-- Deterministic single-pair rerouting lemma (Claims (3)–(7) of Graph Minors XXI, (2.5),
pages 4–6 of the preprint): if `L` is a vital linkage in `G`, `terminals L ⊆ Z`, `(A₁, B₁)` and
`(A₂, B₂)` are separations of `G` with `A₀ ≤ A₁ ≤ A₂` and `B₂ ≤ B₁ ≤ B₀`, `M` is an indexed transfer
linkage between `u₁` and `u₂`, `V(A₁) ∩ Z = V(A₂) ∩ Z`, `V(B₁) ∩ Z = V(B₂) ∩ Z`, and
`φ₁(π₁) = φ₂(π₂)`, then `L ∩ B₁ ∩ A₂ = M`. The printed proof writes $L \cap B_j \cap A_i$ and
$L \cap B_{i+1} \cap A_i$ where $L \cap B_i \cap A_j$ and $L \cap B_i \cap A_{i+1}$ are meant, and
"Since $V(L) \setminus V(G)$" where $V(L) = V(G)$ is meant. Lean uses the corrected forms (see the
correction to the proof of (2.5) in `corrections/GM21.md`). -/
lemma eq_transfer_of_claim_2 {G L A₀ B₀ A₁ B₁ A₂ B₂ M : Hypergraph α β} {Z : Set α} {k : ℕ}
    {u₀ u₁ u₂ : Fin k → α}
    (hL : IsVitalLinkage G L)
    (hZ_sub : terminals L ⊆ Z)
    (hsep₁ : G.IsSeparation A₁ B₁)
    (hsep₂ : G.IsSeparation A₂ B₂)
    (hA₀₁ : A₀ ≤ A₁) (hB₁₀ : B₁ ≤ B₀)
    (hA₀₂ : A₀ ≤ A₂) (hB₂₀ : B₂ ≤ B₀)
    (hA₁₂ : A₁ ≤ A₂) (hB₂₁ : B₂ ≤ B₁)
    (hu₀_inj : Function.Injective u₀) (hu₀_range : Set.range u₀ = (A₀ ∩ B₀).vertexSet)
    (hM : IsIndexedTransferLinkage A₁ B₁ A₂ B₂ M u₁ u₂)
    (hZA : A₁.vertexSet ∩ Z = A₂.vertexSet ∩ Z)
    (hZB : B₁.vertexSet ∩ Z = B₂.vertexSet ∩ Z)
    (hpat_phi :
      (Set.image (separatorBijection u₁ u₀)) '' (linkagePattern (L ∩ B₁)) =
      (Set.image (separatorBijection u₂ u₀)) '' (linkagePattern (L ∩ B₂))) :
    L ∩ B₁ ∩ A₂ = M := by
  let L₁ := L ∩ B₁
  let L₂ := L ∩ B₂
  let ψ := separatorBijection u₁ u₂
  have hL₁_vital : IsVitalLinkage B₁ L₁ := isVitalLinkage_inter_right_of_isSeparation hL hsep₁
  have hL₁ : IsLinkage B₁ L₁ := hL₁_vital.1
  have hL₂_vital : IsVitalLinkage B₂ L₂ := isVitalLinkage_inter_right_of_isSeparation hL hsep₂
  have hL₂ : IsLinkage B₂ L₂ := hL₂_vital.1
  obtain ⟨htermM, hbinjM, hu₁_right, hu₂_left, hu₁₂_eq, hdeg0M, hdeg1M⟩ := hM.props
  obtain ⟨hZ_A, hZ_B, hZ_u, hu_deg, hψ_u, hψ_other, hψ_deg, hψ_reach⟩ :=
    lemma_2_5_claim_2 hL hZ_sub hsep₁ hsep₂ hA₀₁ hB₁₀ hA₀₂ hB₂₀ hu₀_inj hu₀_range
      hM hZA hZB hpat_phi
  have hu₁_mem : ∀ t : Fin k, u₁ t ∈ (A₁ ∩ B₁).vertexSet := by
    intro t; rw [← hM.range_left]; exact mem_range_self t
  have hu₂_mem : ∀ t : Fin k, u₂ t ∈ (A₂ ∩ B₂).vertexSet := by
    intro t; rw [← hM.range_right]; exact mem_range_self t
  -- Helper: for any `x ∉ A_r.vertexSet`, `incidentEdges (L ∩ B_r) x = incidentEdges L x`
  have hinc_LB_eq_L : ∀ {A B : Hypergraph α β}, G.IsSeparation A B →
      ∀ x : α, x ∉ A.vertexSet → incidentEdges (L ∩ B) x = incidentEdges L x := by
    intro A B hsep x hx_notA
    ext e
    simp only [incidentEdges, mem_ofPred_eq, inter_edgeSet, inter_inc]
    refine ⟨fun ⟨⟨heL, _⟩, hincL, _⟩ => ⟨heL, hincL⟩, fun ⟨heL, hincL⟩ => ?_⟩
    have heG : e ∈ G.edgeSet := hL.1.1.edgeSet_subset heL
    have hincG : G.Inc e x := inc_of_le hL.1.1 hincL
    have heAB : e ∈ A.edgeSet ∪ B.edgeSet := by rwa [hsep.edgeSet_union]
    have heB : e ∈ B.edgeSet := heAB.resolve_left fun heA =>
      hx_notA (A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le heA).2 hincG))
    exact ⟨⟨heL, heB⟩, hincL, (inc_iff_of_le hsep.right_le heB).2 hincG⟩
  -- Define T, S_T, and Mstar
  let T : Set (Fin k) := {t : Fin k | u₁ t = u₂ t ∨ (incidentEdges L₁ (u₁ t)).ncard = 1}
  let S_T : Set (Set α) := {P : Set α | ∃ t ∈ T, u₁ t ≠ u₂ t ∧ P = {u₁ t, u₂ t}}
  let Mstar := patternSubgraph M S_T
  have hS_T_sub : S_T ⊆ linkagePattern M := by
    rintro P ⟨t, _, _, rfl⟩
    rw [hM.pattern_eq]
    exact mem_range_self t
  have hS_T_two : ∀ P ∈ S_T, P.ncard = 2 := by
    rintro P ⟨t, _, hne, rfl⟩
    exact ncard_pair hne
  obtain ⟨hMstar_le_M, hMstar_deg1, hMstar_deg02⟩ :=
    patternSubgraph_deg_props hM.isLinkage hS_T_sub hS_T_two
  obtain ⟨hMstar_term_props, _, _⟩ :=
    patternSubgraph_incidentEdges_props hM.isLinkage hS_T_sub hS_T_two
  have hMstar_term0 : ∀ z ∈ terminals M, z ∉ ⋃₀ S_T → (incidentEdges Mstar z).ncard = 0 := by
    intro z hz hnot
    exact (hMstar_term_props z hz).2 (by simpa [mem_sUnion] using hnot)
  have hu₁_ST : ∀ t : Fin k, u₁ t ∈ ⋃₀ S_T ↔ t ∈ T ∧ u₁ t ≠ u₂ t := by
    intro t
    simp only [mem_sUnion, S_T, mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨s, hsT, hne_s, rfl⟩, hu₁_in⟩
      rcases hu₁_in with h1 | h2
      · have hts : t = s := hM.inj_left h1
        subst hts; exact ⟨hsT, hne_s⟩
      · obtain ⟨hts, heq⟩ := hu₁₂_eq t s h2
        subst hts; exact (hne_s heq).elim
    · rintro ⟨htT, hne⟩
      exact ⟨{u₁ t, u₂ t}, ⟨t, htT, hne, rfl⟩, Or.inl rfl⟩
  have hu₂_ST : ∀ t : Fin k, u₂ t ∈ ⋃₀ S_T ↔ t ∈ T ∧ u₁ t ≠ u₂ t := by
    intro t
    simp only [mem_sUnion, S_T, mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨s, hsT, hne_s, rfl⟩, hu₂_in⟩
      rcases hu₂_in with h1 | h2
      · obtain ⟨hst, heq⟩ := hu₁₂_eq s t h1.symm
        subst hst; exact (hne_s heq).elim
      · have hts : t = s := hM.inj_right h2
        subst hts; exact ⟨hsT, hne_s⟩
    · rintro ⟨htT, hne⟩
      exact ⟨{u₁ t, u₂ t}, ⟨t, htT, hne, rfl⟩, Or.inr rfl⟩
  -- Define N ≤ B₁
  let N : Hypergraph α β :=
    { vertexSet := {v ∈ B₁.vertexSet |
        (∃ e ∈ Mstar.edgeSet ∪ L₂.edgeSet, B₁.Inc e v) ∨ v ∈ terminals L₁}
      edgeSet := Mstar.edgeSet ∪ L₂.edgeSet
      Inc := fun e v => e ∈ Mstar.edgeSet ∪ L₂.edgeSet ∧ B₁.Inc e v
      vertex_mem_of_inc := fun _ _ h => ⟨B₁.vertex_mem_of_inc h.2, Or.inl ⟨_, h.1, h.2⟩⟩
      edge_mem_of_inc := fun _ _ h => h.1
      vertexSet_finite := B₁.vertexSet_finite.subset fun _ h => h.1
      edgeSet_finite := Mstar.edgeSet_finite.union L₂.edgeSet_finite }
  have hB₁A₂_le_B₁ : B₁ ∩ A₂ ≤ B₁ := inter_le_left hsep₁.right_le hsep₂.left_le
  have hM_le_B₁ : M ≤ B₁ := le_trans hM.isLinkage.1 hB₁A₂_le_B₁
  have hMstar_le_B₁ : Mstar ≤ B₁ := le_trans hMstar_le_M hM_le_B₁
  have hL₂_le_B₁ : L₂ ≤ B₁ := le_trans hL₂.1 hB₂₁
  have hN_le_B₁ : N ≤ B₁ :=
    { vertexSet_subset := fun _ h => h.1
      edgeSet_subset := union_subset hMstar_le_B₁.edgeSet_subset hL₂_le_B₁.edgeSet_subset
      ends_eq := fun e he => by
        ext v
        simp only [Hypergraph.ends, mem_ofPred_eq, N]
        exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩ }
  have hdisj_A₂B₂ : Disjoint A₂.edgeSet B₂.edgeSet :=
    Set.disjoint_left.mpr fun _ heA heB => hsep₂.notMem_edgeSet_right heA heB
  have hdisj_ML₂ : Disjoint Mstar.edgeSet L₂.edgeSet :=
    hdisj_A₂B₂.mono
      (fun _ he => (hM.isLinkage.1.edgeSet_subset (hMstar_le_M.edgeSet_subset he)).2)
      (fun _ he => (hL₂.1.edgeSet_subset he))
  have hN_split : ∀ z : α,
      (incidentEdges N z).ncard = (incidentEdges Mstar z).ncard + (incidentEdges L₂ z).ncard :=
    fun z => (ncard_incidentEdges_of_edgeSet_union hMstar_le_B₁ hL₂_le_B₁ hN_le_B₁ rfl hdisj_ML₂ z).2
  have hN_loop : ∀ e ∈ N.edgeSet, (N.ends e).ncard = 2 := by
    rintro e (heM | heL₂)
    · rw [← hN_le_B₁.ends_eq e (Or.inl heM), hM_le_B₁.ends_eq e (hMstar_le_M.edgeSet_subset heM)]
      exact hM.isLinkage.ends_ncard_eq_two (hMstar_le_M.edgeSet_subset heM)
    · rw [← hN_le_B₁.ends_eq e (Or.inr heL₂), hL₂_le_B₁.ends_eq e heL₂]
      exact hL₂.ends_ncard_eq_two heL₂
  -- Degree of N at z ∈ terminals L₁
  have hdeg_termL₁ : ∀ z ∈ terminals L₁,
      (incidentEdges N z).ncard = (incidentEdges L₁ z).ncard := by
    intro z hz
    rw [hN_split z]
    by_cases hz_AB₁ : z ∈ (A₁ ∩ B₁).vertexSet
    · rw [← hM.range_left] at hz_AB₁
      rcases hz_AB₁ with ⟨t, rfl⟩
      have hu₁_termM : u₁ t ∈ terminals M := by rw [htermM]; exact Or.inl (hu₁_mem t)
      by_cases heq : u₁ t = u₂ t
      · have hnot_ST : u₁ t ∉ ⋃₀ S_T := by rw [hu₁_ST]; exact fun h => h.2 heq
        rw [hMstar_term0 (u₁ t) hu₁_termM hnot_ST, zero_add]
        change (incidentEdges (L ∩ B₂) (u₁ t)).ncard = (incidentEdges (L ∩ B₁) (u₁ t)).ncard
        rw [heq, ← hu_deg t, heq]
      · have hu₁_not_B₂ : u₁ t ∉ B₂.vertexSet := fun hB₂ =>
          heq (hu₁_right t ⟨hA₁₂.vertexSet_subset (hu₁_mem t).1, hB₂⟩)
        have hu₁_not_L₂ : u₁ t ∉ L₂.vertexSet :=
          fun h => hu₁_not_B₂ (hL₂.1.vertexSet_subset h)
        rw [incidentEdges_eq_empty_of_notMem hu₁_not_L₂, ncard_empty, add_zero]
        have hle1 : (incidentEdges L₁ (u₁ t)).ncard ≤ 1 := (hL₁.mem_terminals_iff.mp hz).2
        by_cases h1 : (incidentEdges L₁ (u₁ t)).ncard = 1
        · have htT : t ∈ T := Or.inr h1
          rw [(hMstar_deg1 (u₁ t)).mpr ((hu₁_ST t).mpr ⟨htT, heq⟩), h1]
        · have h0 : (incidentEdges L₁ (u₁ t)).ncard = 0 := by omega
          have hnotT : t ∉ T := fun h => h.elim heq h1
          have hnot_ST : u₁ t ∉ ⋃₀ S_T := fun h => hnotT ((hu₁_ST t).mp h).1
          rw [hMstar_term0 (u₁ t) hu₁_termM hnot_ST, h0]
    · have hzB₁ : z ∈ B₁.vertexSet := hz.1.2
      have hz_notA₁ : z ∉ A₁.vertexSet := fun hA₁ => hz_AB₁ ⟨hA₁, hzB₁⟩
      have hinc₁ := hinc_LB_eq_L hsep₁ z hz_notA₁
      have hz_termL : z ∈ terminals L := by
        rw [hL.1.mem_terminals_iff]
        refine ⟨hz.1.1, ?_⟩
        rw [← hinc₁]
        exact (hL₁.mem_terminals_iff.mp hz).2
      have hzZ : z ∈ Z := hZ_sub hz_termL
      have hz_notA₂ : z ∉ A₂.vertexSet := mt (hZ_A z hzZ).mpr hz_notA₁
      have hz_notM : z ∉ Mstar.vertexSet := fun h =>
        hz_notA₂ (hM.isLinkage.1.vertexSet_subset (hMstar_le_M.vertexSet_subset h)).2
      rw [incidentEdges_eq_empty_of_notMem hz_notM, ncard_empty, zero_add,
        hinc_LB_eq_L hsep₂ z hz_notA₂, hinc₁]
  -- Degree of N at z ∈ N.vertexSet \ terminals L₁
  have hdeg_internalN : ∀ z ∈ N.vertexSet, z ∉ terminals L₁ →
      (incidentEdges N z).ncard = 2 := by
    intro z hzN hz_not_term
    have hex_e : ∃ e ∈ Mstar.edgeSet ∪ L₂.edgeSet, B₁.Inc e z :=
      hzN.2.resolve_right hz_not_term
    obtain ⟨e₀, he₀, hinc₀⟩ := hex_e
    have he₀_in : e₀ ∈ incidentEdges N z := ⟨he₀, he₀, hinc₀⟩
    have hN_pos : 1 ≤ (incidentEdges N z).ncard :=
      Nat.succ_le_of_lt ((ncard_pos (N.edgeSet_finite.subset fun _ h => h.1)).mpr ⟨e₀, he₀_in⟩)
    rw [hN_split z] at hN_pos ⊢
    by_cases hz_AB₂ : z ∈ (A₂ ∩ B₂).vertexSet
    · rw [← hM.range_right] at hz_AB₂
      rcases hz_AB₂ with ⟨t, rfl⟩
      have hu₂_termM : u₂ t ∈ terminals M := by rw [htermM]; exact Or.inr (hu₂_mem t)
      have hu₁_L₁ : u₁ t ∈ L₁.vertexSet := by
        rw [hL₁_vital.2.1]; exact (hu₁_mem t).2
      have hle2_u₁ : (incidentEdges L₁ (u₁ t)).ncard ≤ 2 := hL₁.ncard_incidentEdges_le_two (u₁ t)
      by_cases heq : u₁ t = u₂ t
      · have hnot_ST : u₂ t ∉ ⋃₀ S_T := by rw [hu₂_ST]; exact fun h => h.2 heq
        have h2_u₁ : (incidentEdges L₁ (u₁ t)).ncard = 2 :=
          (hL₁.notMem_terminals_iff hu₁_L₁).mp (heq ▸ hz_not_term)
        rw [hMstar_term0 (u₂ t) hu₂_termM hnot_ST, ← hu_deg t, h2_u₁, zero_add]
      · by_cases h1 : (incidentEdges L₁ (u₁ t)).ncard = 1
        · have htT : t ∈ T := Or.inr h1
          rw [(hMstar_deg1 (u₂ t)).mpr ((hu₂_ST t).mpr ⟨htT, heq⟩), ← hu_deg t, h1]
        · have hnotT : t ∉ T := fun h => h.elim heq h1
          have hnot_ST : u₂ t ∉ ⋃₀ S_T := fun h => hnotT ((hu₂_ST t).mp h).1
          have h0_M : (incidentEdges Mstar (u₂ t)).ncard = 0 :=
            hMstar_term0 (u₂ t) hu₂_termM hnot_ST
          rw [h0_M, zero_add] at hN_pos ⊢
          have hpos_u₁ : 1 ≤ (incidentEdges L₁ (u₁ t)).ncard := by
            change 1 ≤ (incidentEdges (L ∩ B₁) (u₁ t)).ncard
            rw [hu_deg t]
            exact hN_pos
          have h2_u₁ : (incidentEdges L₁ (u₁ t)).ncard = 2 := by omega
          exact (hu_deg t).symm.trans h2_u₁
    · rcases he₀ with he₀M | he₀L₂
      · have hincM : Mstar.Inc e₀ z := (inc_iff_of_le hMstar_le_B₁ he₀M).2 hinc₀
        have hzM : z ∈ M.vertexSet := hMstar_le_M.vertexSet_subset (Mstar.vertex_mem_of_inc hincM)
        have hzA₂ : z ∈ A₂.vertexSet := (hM.isLinkage.1.vertexSet_subset hzM).2
        have hz_notB₂ : z ∉ B₂.vertexSet := fun hB₂ => hz_AB₂ ⟨hzA₂, hB₂⟩
        have hz_notL₂ : z ∉ L₂.vertexSet := fun h => hz_notB₂ (hL₂.1.vertexSet_subset h)
        have h0_L₂ : (incidentEdges L₂ z).ncard = 0 := by
          rw [incidentEdges_eq_empty_of_notMem hz_notL₂, ncard_empty]
        have hnot_ST : z ∉ ⋃₀ S_T := by
          rintro ⟨P, ⟨t, htT, hne, rfl⟩, hzP⟩
          rcases hzP with rfl | rfl
          · have h1_u₁ : (incidentEdges L₁ (u₁ t)).ncard = 1 := htT.resolve_left hne
            have hu₁_L₁ : u₁ t ∈ L₁.vertexSet := by rw [hL₁_vital.2.1]; exact (hu₁_mem t).2
            exact hz_not_term (hL₁.mem_terminals_iff.mpr ⟨hu₁_L₁, by omega⟩)
          · exact hz_AB₂ (hu₂_mem t)
        have h02 : (incidentEdges Mstar z).ncard = 0 ∨ (incidentEdges Mstar z).ncard = 2 :=
          hMstar_deg02 z hnot_ST
        rcases h02 with h0 | h2 <;> omega
      · have hincL₂ : L₂.Inc e₀ z := (inc_iff_of_le hL₂_le_B₁ he₀L₂).2 hinc₀
        have hzB₂ : z ∈ B₂.vertexSet := hL₂.1.vertexSet_subset (L₂.vertex_mem_of_inc hincL₂)
        have hz_notA₂ : z ∉ A₂.vertexSet := fun hA₂ => hz_AB₂ ⟨hA₂, hzB₂⟩
        have hz_notA₁ : z ∉ A₁.vertexSet := fun hA₁ => hz_notA₂ (hA₁₂.vertexSet_subset hA₁)
        have hz_notM : z ∉ Mstar.vertexSet := fun h =>
          hz_notA₂ (hM.isLinkage.1.vertexSet_subset (hMstar_le_M.vertexSet_subset h)).2
        have h0_M : (incidentEdges Mstar z).ncard = 0 := by
          rw [incidentEdges_eq_empty_of_notMem hz_notM, ncard_empty]
        have hzL₁ : z ∈ L₁.vertexSet := by rw [hL₁_vital.2.1]; exact hzN.1
        have h2_L₁ : (incidentEdges L₁ z).ncard = 2 :=
          (hL₁.notMem_terminals_iff hzL₁).mp hz_not_term
        rw [h0_M, zero_add, hinc_LB_eq_L hsep₂ z hz_notA₂,
          ← hinc_LB_eq_L hsep₁ z hz_notA₁, h2_L₁]
  have hdeg2_N : ∀ z ∈ N.vertexSet, (incidentEdges N z).ncard ≤ 2 := by
    intro z hzN
    by_cases hz : z ∈ terminals L₁
    · rw [hdeg_termL₁ z hz]
      exact hL₁.ncard_incidentEdges_le_two z
    · rw [hdeg_internalN z hzN hz]
  -- Reachability in N
  have hreach_Mstar_N : ∀ {x y : α}, Mstar.skeleton.Reachable x y → N.skeleton.Reachable x y :=
    fun hr => reachable_of_edgeSet_subset_of_le hMstar_le_B₁ hN_le_B₁ subset_union_left hr
  have hreach_L₂_N : ∀ {x y : α}, L₂.skeleton.Reachable x y → N.skeleton.Reachable x y :=
    fun hr => reachable_of_edgeSet_subset_of_le hL₂_le_B₁ hN_le_B₁ subset_union_right hr
  have hreach_T : ∀ t ∈ T, N.skeleton.Reachable (u₁ t) (u₂ t) := by
    intro t htT
    by_cases heq : u₁ t = u₂ t
    · rw [heq]
    · exact hreach_Mstar_N (reachable_patternSubgraph_of_mem
        ⟨t, htT, heq, rfl⟩ (Or.inl rfl) (hdeg1M t heq).2.2)
  have htermL₁_in_N : terminals L₁ ⊆ N.vertexSet :=
    fun _ hz => ⟨hz.1.2, Or.inr hz⟩
  have hreach_N : ∀ v ∈ N.vertexSet,
      ∃ w ∈ N.vertexSet, N.skeleton.Reachable v w ∧ (incidentEdges N w).ncard ≤ 1 := by
    intro v hvN
    have hterm_le1 : ∀ w ∈ terminals L₁,
        w ∈ N.vertexSet ∧ (incidentEdges N w).ncard ≤ 1 := fun w hw => by
      refine ⟨htermL₁_in_N hw, ?_⟩
      rw [hdeg_termL₁ w hw]
      exact (hL₁.mem_terminals_iff.mp hw).2
    rcases hvN.2 with ⟨e₀, he₀M | he₀L₂, hinc₀⟩ | hv_term
    · have hincM : Mstar.Inc e₀ v := (inc_iff_of_le hMstar_le_B₁ he₀M).2 hinc₀
      have hvM : v ∈ Mstar.vertexSet := Mstar.vertex_mem_of_inc hincM
      rcases hvM.2 with ⟨P, ⟨t, htT, hne, rfl⟩, u, huP, hruv⟩
      have hr_vu : N.skeleton.Reachable v u :=
        (hreach_Mstar_N (reachable_patternSubgraph_of_mem ⟨t, htT, hne, rfl⟩ huP hruv)).symm
      have h1_u₁ : (incidentEdges L₁ (u₁ t)).ncard = 1 := htT.resolve_left hne
      have hu₁_L₁ : u₁ t ∈ L₁.vertexSet := by rw [hL₁_vital.2.1]; exact (hu₁_mem t).2
      have hu₁_term : u₁ t ∈ terminals L₁ := hL₁.mem_terminals_iff.mpr ⟨hu₁_L₁, by omega⟩
      rcases huP with rfl | rfl
      · exact ⟨u₁ t, (hterm_le1 (u₁ t) hu₁_term).1, hr_vu, (hterm_le1 (u₁ t) hu₁_term).2⟩
      · exact ⟨u₁ t, (hterm_le1 (u₁ t) hu₁_term).1,
          hr_vu.trans (hreach_T t htT).symm, (hterm_le1 (u₁ t) hu₁_term).2⟩
    · have hincL₂ : L₂.Inc e₀ v := (inc_iff_of_le hL₂_le_B₁ he₀L₂).2 hinc₀
      have hvL₂ : v ∈ L₂.vertexSet := L₂.vertex_mem_of_inc hincL₂
      let C₂ := reachableComponent L₂ v
      have hC₂_comp : IsComponentOf L₂ C₂ := isComponentOf_reachableComponent hL₂.2.1 hvL₂
      have hC₂_path : IsPathGraph C₂ := hL₂.2.2 C₂ hC₂_comp
      have hC₂_ne : C₂.edgeSet.Nonempty := ⟨e₀, he₀L₂, v, hincL₂, SimpleGraph.Reachable.refl v⟩
      obtain ⟨a, haC₂, _, _, _, htermC₂_ab, ha1_C₂, _, _⟩ :=
        isPathGraph_of_edgeSet_nonempty hC₂_path hC₂_ne
      have ha1_L₂ : (incidentEdges L₂ a).ncard = 1 := by
        rw [← incidentEdges_component_eq hL₂.2.1 hC₂_comp haC₂]; exact ha1_C₂
      have hr_va : N.skeleton.Reachable v a := hreach_L₂_N haC₂.2
      by_cases ha_AB₂ : a ∈ (A₂ ∩ B₂).vertexSet
      · rw [← hM.range_right] at ha_AB₂
        rcases ha_AB₂ with ⟨t, rfl⟩
        have h1_u₁ : (incidentEdges L₁ (u₁ t)).ncard = 1 := by rw [hu_deg t]; exact ha1_L₂
        have htT : t ∈ T := Or.inr h1_u₁
        have hu₁_L₁ : u₁ t ∈ L₁.vertexSet := by rw [hL₁_vital.2.1]; exact (hu₁_mem t).2
        have hu₁_term : u₁ t ∈ terminals L₁ := hL₁.mem_terminals_iff.mpr ⟨hu₁_L₁, by omega⟩
        exact ⟨u₁ t, (hterm_le1 (u₁ t) hu₁_term).1,
          hr_va.trans (hreach_T t htT).symm, (hterm_le1 (u₁ t) hu₁_term).2⟩
      · have haB₂ : a ∈ B₂.vertexSet := hL₂.1.vertexSet_subset haC₂.1
        have ha_notA₂ : a ∉ A₂.vertexSet := fun hA₂ => ha_AB₂ ⟨hA₂, haB₂⟩
        have ha_notA₁ : a ∉ A₁.vertexSet := fun hA₁ => ha_notA₂ (hA₁₂.vertexSet_subset hA₁)
        have ha_termL : a ∈ terminals L := by
          rw [hL.1.mem_terminals_iff]
          refine ⟨haC₂.1.1, ?_⟩
          rw [← hinc_LB_eq_L hsep₂ a ha_notA₂, ha1_L₂]
        have haZ : a ∈ Z := hZ_sub ha_termL
        have haB₁ : a ∈ B₁.vertexSet := (hZ_B a haZ).mpr haB₂
        have haL₁ : a ∈ L₁.vertexSet := ⟨haC₂.1.1, haB₁⟩
        have ha_termL₁ : a ∈ terminals L₁ := by
          rw [hL₁.mem_terminals_iff]
          refine ⟨haL₁, ?_⟩
          rw [hinc_LB_eq_L hsep₁ a ha_notA₁, ← hinc_LB_eq_L hsep₂ a ha_notA₂, ha1_L₂]
        exact ⟨a, (hterm_le1 a ha_termL₁).1, hr_va, (hterm_le1 a ha_termL₁).2⟩
    · exact ⟨v, (hterm_le1 v hv_term).1, SimpleGraph.Reachable.refl v, (hterm_le1 v hv_term).2⟩
  -- Claim (3): N is a linkage in B₁ with terminals N = terminals L₁
  have hN_link : IsLinkage B₁ N :=
    isLinkage_of_deg_le_two_of_reachable_deg_le_one hN_le_B₁ hN_loop hdeg2_N hreach_N
  have hterm_N : terminals N = terminals L₁ := by
    ext z
    constructor
    · intro hzN
      by_contra hz_not
      have h2 := hdeg_internalN z hzN.1 hz_not
      exact (hN_link.notMem_terminals_iff hzN.1).mpr h2 hzN
    · intro hzL₁
      rw [hN_link.mem_terminals_iff]
      refine ⟨htermL₁_in_N hzL₁, ?_⟩
      rw [hdeg_termL₁ z hzL₁]
      exact (hL₁.mem_terminals_iff.mp hzL₁).2
  -- Claim (4): linkagePattern N = linkagePattern L₁
  have hreach_ψ : ∀ x ∈ terminals L₁,
      (incidentEdges L₁ x).ncard = 1 → N.skeleton.Reachable x (ψ x) := by
    intro x hx hx1
    dsimp [ψ]
    by_cases hx_AB₁ : x ∈ (A₁ ∩ B₁).vertexSet
    · rw [← hM.range_left] at hx_AB₁
      rcases hx_AB₁ with ⟨t, rfl⟩
      rw [hψ_u t]
      exact hreach_T t (Or.inr hx1)
    · rw [hψ_other x hx_AB₁]
  have hpat_N : linkagePattern N = linkagePattern L₁ := by
    symm
    apply linkagePattern_eq_of_subset hL₁ hN_link hterm_N.subset
    intro P hPL₁
    rcases hL₁.mem_linkagePattern_structure hPL₁ with
      ⟨x, hxL₁, rfl, hx0⟩ | ⟨x₁, hx₁L₁, x₂, hx₂L₁, hne, rfl, hx₁1, hx₂1⟩
    · have hxN : x ∈ N.vertexSet := (htermL₁_in_N hxL₁)
      rw [← hdeg_termL₁ x hxL₁] at hx0
      exact (hN_link.ncard_incidentEdges_eq_zero_iff hxN).mp hx0
    · have hr₁ : L₁.skeleton.Reachable x₁ x₂ :=
        (hL₁.pair_mem_linkagePattern_iff hx₁L₁ hx₂L₁ hne).mp hPL₁
      have hr₂ : L₂.skeleton.Reachable (ψ x₁) (ψ x₂) :=
        (hψ_reach x₁ hx₁L₁ x₂ hx₂L₁ hne hr₁).2
      have hrN : N.skeleton.Reachable x₁ x₂ :=
        (hreach_ψ x₁ hx₁L₁ hx₁1).trans
          ((hreach_L₂_N hr₂).trans (hreach_ψ x₂ hx₂L₁ hx₂1).symm)
      exact (hN_link.pair_mem_linkagePattern_iff
        (hterm_N.symm ▸ hx₁L₁) (hterm_N.symm ▸ hx₂L₁) hne).mpr hrN
  -- By vitality of L₁ in B₁, N = L₁!
  have hN_eq_L₁ : N = L₁ := hL₁_vital.2.2 N hN_link hpat_N
  have hL₁_split : ∀ z : α,
      (incidentEdges L₁ z).ncard = (incidentEdges Mstar z).ncard + (incidentEdges L₂ z).ncard := by
    intro z; rw [← hN_eq_L₁]; exact hN_split z
  -- Claim (6): T = univ
  have hT_univ : ∀ t : Fin k, t ∈ T := by
    intro t
    by_contra ht_not
    have hne : u₁ t ≠ u₂ t := fun h => ht_not (Or.inl h)
    have hne1 : (incidentEdges L₁ (u₁ t)).ncard ≠ 1 := fun h => ht_not (Or.inr h)
    have hu₁_not_ST : u₁ t ∉ ⋃₀ S_T := fun h => ht_not ((hu₁_ST t).mp h).1
    have hu₂_not_ST : u₂ t ∉ ⋃₀ S_T := fun h => ht_not ((hu₂_ST t).mp h).1
    have hu₁_termM : u₁ t ∈ terminals M := by rw [htermM]; exact Or.inl (hu₁_mem t)
    have hu₂_termM : u₂ t ∈ terminals M := by rw [htermM]; exact Or.inr (hu₂_mem t)
    have h0_M_u₁ : (incidentEdges Mstar (u₁ t)).ncard = 0 :=
      hMstar_term0 (u₁ t) hu₁_termM hu₁_not_ST
    have h0_M_u₂ : (incidentEdges Mstar (u₂ t)).ncard = 0 :=
      hMstar_term0 (u₂ t) hu₂_termM hu₂_not_ST
    have hu₁_not_B₂ : u₁ t ∉ B₂.vertexSet := fun hB₂ =>
      hne (hu₁_right t ⟨hA₁₂.vertexSet_subset (hu₁_mem t).1, hB₂⟩)
    have hu₁_not_L₂ : u₁ t ∉ L₂.vertexSet := fun h => hu₁_not_B₂ (hL₂.1.vertexSet_subset h)
    have h0_L₂_u₁ : (incidentEdges L₂ (u₁ t)).ncard = 0 := by
      rw [incidentEdges_eq_empty_of_notMem hu₁_not_L₂, ncard_empty]
    have h0_L₁_u₁ : (incidentEdges L₁ (u₁ t)).ncard = 0 := by
      rw [hL₁_split (u₁ t), h0_M_u₁, h0_L₂_u₁]
    have h0_L₂_u₂ : (incidentEdges L₂ (u₂ t)).ncard = 0 := by
      rw [← hu_deg t]; exact h0_L₁_u₁
    have h0_L₁_u₂ : (incidentEdges L₁ (u₂ t)).ncard = 0 := by
      rw [hL₁_split (u₂ t), h0_M_u₂, h0_L₂_u₂]
    have hu₂_not_A₁ : u₂ t ∉ A₁.vertexSet := fun hA₁ =>
      hne (hu₂_left t ⟨hA₁, hB₂₁.vertexSet_subset (hu₂_mem t).2⟩)
    have h0_L_u₂ : (incidentEdges L (u₂ t)).ncard = 0 := by
      rw [← hinc_LB_eq_L hsep₁ (u₂ t) hu₂_not_A₁]; exact h0_L₁_u₂
    have hu₂_L : u₂ t ∈ L.vertexSet := by
      rw [hL.2.1]; exact hsep₂.right_le.vertexSet_subset (hu₂_mem t).2
    have hu₂_termL : u₂ t ∈ terminals L := hL.1.mem_terminals_iff.mpr ⟨hu₂_L, by omega⟩
    exact hne ((hZ_u t).2 (hZ_sub hu₂_termL))
  -- From Claim (6), Mstar.edgeSet = M.edgeSet
  have hMstar_E_eq : Mstar.edgeSet = M.edgeSet := by
    apply Subset.antisymm hMstar_le_M.edgeSet_subset
    intro e heM
    obtain ⟨v, hinc_ev⟩ := (hM.isLinkage.2.1 e heM).1
    have hvM : v ∈ M.vertexSet := M.vertex_mem_of_inc hinc_ev
    obtain ⟨z, hz_termM, hrvz⟩ := hM.isLinkage.exists_reachable_terminal hvM
    have hne : v ≠ z ∨ v = z := ne_or_eq v z
    have hP_mem : terminals M ∩ (reachableComponent M z).vertexSet ∈ linkagePattern M :=
      ⟨reachableComponent M z, isComponentOf_reachableComponent hM.isLinkage.2.1 hz_termM.1, rfl⟩
    have he_in_C : e ∈ (reachableComponent M z).edgeSet :=
      ⟨heM, v, hinc_ev, hrvz.symm⟩
    have hP_eq := hM.pattern_eq ▸ hP_mem
    rcases hP_eq with ⟨t, ht_eq⟩
    change {u₁ t, u₂ t} = terminals M ∩ (reachableComponent M z).vertexSet at ht_eq
    have hne_t : u₁ t ≠ u₂ t := by
      intro heq
      have h0 := hdeg0M t heq
      have hu₁_in_C : u₁ t ∈ (reachableComponent M z).vertexSet := by
        have : u₁ t ∈ terminals M ∩ (reachableComponent M z).vertexSet := by
          rw [← ht_eq]; exact Or.inl rfl
        exact this.2
      have hC_eq : reachableComponent M z = reachableComponent M (u₁ t) :=
        eq_reachableComponent_of_isComponentOf hM.isLinkage.2.1
          (isComponentOf_reachableComponent hM.isLinkage.2.1 hz_termM.1) hu₁_in_C
      rw [hC_eq] at he_in_C
      obtain ⟨w, hinc_w, hr_u₁w⟩ := he_in_C.2
      rcases hr_u₁w with ⟨p⟩
      cases p with
      | nil =>
        have : e ∈ incidentEdges M (u₁ t) := ⟨heM, hinc_w⟩
        have hpos : 1 ≤ (incidentEdges M (u₁ t)).ncard :=
          Nat.succ_le_of_lt ((ncard_pos (M.edgeSet_finite.subset fun _ h => h.1)).mpr ⟨e, this⟩)
        omega
      | cons hadj _ =>
        obtain ⟨_, e', hinc_u₁, _⟩ := hadj
        have : e' ∈ incidentEdges M (u₁ t) := ⟨M.edge_mem_of_inc hinc_u₁, hinc_u₁⟩
        have hpos : 1 ≤ (incidentEdges M (u₁ t)).ncard :=
          Nat.succ_le_of_lt ((ncard_pos (M.edgeSet_finite.subset fun _ h => h.1)).mpr ⟨e', this⟩)
        omega
    have hP_ST : ({u₁ t, u₂ t} : Set α) ∈ S_T := ⟨t, hT_univ t, hne_t, rfl⟩
    have hz_in_P : z ∈ ({u₁ t, u₂ t} : Set α) := by
      rw [ht_eq]
      exact ⟨hz_termM, self_mem_reachableComponent hz_termM.1⟩
    exact ⟨heM, {u₁ t, u₂ t}, hP_ST, z, hz_in_P, v, hinc_ev, hrvz.symm⟩
  -- Deduce (L ∩ B₁ ∩ A₂).edgeSet = M.edgeSet and (L ∩ B₁ ∩ A₂).vertexSet = M.vertexSet
  have hE_L₁ : L₁.edgeSet = M.edgeSet ∪ L₂.edgeSet := by
    rw [← hMstar_E_eq, ← hN_eq_L₁]
  have hE_eq : (L ∩ B₁ ∩ A₂).edgeSet = M.edgeSet := by
    change (L₁ ∩ A₂).edgeSet = M.edgeSet
    rw [inter_edgeSet, hE_L₁]
    ext e
    simp only [mem_inter_iff, mem_union]
    constructor
    · rintro ⟨heM | heL₂, heA₂⟩
      · exact heM
      · exfalso
        exact hsep₂.notMem_edgeSet_right heA₂ (hL₂.1.edgeSet_subset heL₂)
    · intro heM
      exact ⟨Or.inl heM, (hM.isLinkage.1.edgeSet_subset heM).2⟩
  have hV_eq : (L ∩ B₁ ∩ A₂).vertexSet = M.vertexSet := by
    apply Subset.antisymm
    · rintro v ⟨⟨_, hvB₁⟩, hvA₂⟩
      by_cases hv_termM : v ∈ (A₁ ∩ B₁).vertexSet ∪ (A₂ ∩ B₂).vertexSet
      · rw [← htermM] at hv_termM
        exact hv_termM.1
      · have hv_notA₁ : v ∉ A₁.vertexSet := fun hA₁ => hv_termM (Or.inl ⟨hA₁, hvB₁⟩)
        have hv_notB₂ : v ∉ B₂.vertexSet := fun hB₂ => hv_termM (Or.inr ⟨hvA₂, hB₂⟩)
        have hv_notZ : v ∉ Z := fun hvZ => hv_notA₁ ((hZ_A v hvZ).mpr hvA₂)
        have hv_not_termL : v ∉ terminals L := fun h => hv_notZ (hZ_sub h)
        have hvL : v ∈ L.vertexSet := by
          rw [hL.2.1]; exact hsep₁.right_le.vertexSet_subset hvB₁
        have h2_L : (incidentEdges L v).ncard = 2 :=
          (hL.1.notMem_terminals_iff hvL).mp hv_not_termL
        have h2_L₁ : (incidentEdges L₁ v).ncard = 2 := by
          rw [hinc_LB_eq_L hsep₁ v hv_notA₁]; exact h2_L
        have hv_notL₂ : v ∉ L₂.vertexSet := fun h => hv_notB₂ (hL₂.1.vertexSet_subset h)
        have h0_L₂ : (incidentEdges L₂ v).ncard = 0 := by
          rw [incidentEdges_eq_empty_of_notMem hv_notL₂, ncard_empty]
        have h2_Mstar : (incidentEdges Mstar v).ncard = 2 := by
          have := hL₁_split v
          omega
        obtain ⟨e₀, _, _, he₀⟩ := ncard_eq_two.mp h2_Mstar
        have he₀_mem : e₀ ∈ incidentEdges Mstar v := by rw [he₀]; exact Or.inl rfl
        exact hMstar_le_M.vertexSet_subset (Mstar.vertex_mem_of_inc he₀_mem.2)
    · intro v hvM
      have hv_B₁A₂ := hM.isLinkage.1.vertexSet_subset hvM
      have hvL : v ∈ L.vertexSet := by
        rw [hL.2.1]; exact hsep₁.right_le.vertexSet_subset hv_B₁A₂.1
      exact ⟨⟨hvL, hv_B₁A₂.1⟩, hv_B₁A₂.2⟩
  have hLBA_le : L ∩ B₁ ∩ A₂ ≤ B₁ ∩ A₂ :=
    inter_le_inter_of_le (inter_le_right hL.1.1 hsep₁.right_le) le_rfl
  exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq hLBA_le hM.isLinkage.1 hV_eq hE_eq

/-! ## 4. Pigeonhole and bounded-order nested separations ((2.5), (2.6), (2.7)) -/

/-- If `L ≤ G`, `B₁ ≤ G`, `A₂ ≤ G`, `A₁' ≤ A₂`, and `(L ∩ B₁ ∩ A₂) ∩ (B₁ ∩ A₁') = M₀`,
then `L ∩ B₁ ∩ A₁' = M₀`. -/
lemma inter_subinterval_eq {G L B₁ A₂ A₁' M₀ : Hypergraph α β}
    (hL : L ≤ G) (hB₁ : B₁ ≤ G) (hA₂ : A₂ ≤ G) (hA₁' : A₁' ≤ A₂)
    (hM₀ : (L ∩ B₁ ∩ A₂) ∩ (B₁ ∩ A₁') = M₀) :
    L ∩ B₁ ∩ A₁' = M₀ := by
  rw [← hM₀]
  have hA₁'G : A₁' ≤ G := le_trans hA₁' hA₂
  have hLB₁ : L ∩ B₁ ≤ G := le_trans (inter_le_left hL hB₁) hL
  have hLB₁A₂ : L ∩ B₁ ∩ A₂ ≤ G := le_trans (inter_le_left hLB₁ hA₂) hLB₁
  have hB₁A₁' : B₁ ∩ A₁' ≤ G := le_trans (inter_le_left hB₁ hA₁'G) hB₁
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (le_trans (inter_le_left hLB₁ hA₁'G) hLB₁)
    (le_trans (inter_le_left hLB₁A₂ hB₁A₁') hLB₁A₂) ?_ ?_
  · ext v
    simp only [inter_vertexSet, mem_inter_iff]
    exact ⟨fun ⟨⟨hvL, hvB₁⟩, hvA₁'⟩ => ⟨⟨⟨hvL, hvB₁⟩, hA₁'.vertexSet_subset hvA₁'⟩, hvB₁, hvA₁'⟩,
      fun ⟨⟨⟨hvL, hvB₁⟩, _⟩, _, hvA₁'⟩ => ⟨⟨hvL, hvB₁⟩, hvA₁'⟩⟩
  · ext e
    simp only [inter_edgeSet, mem_inter_iff]
    exact ⟨fun ⟨⟨heL, heB₁⟩, heA₁'⟩ => ⟨⟨⟨heL, heB₁⟩, hA₁'.edgeSet_subset heA₁'⟩, heB₁, heA₁'⟩,
      fun ⟨⟨⟨heL, heB₁⟩, _⟩, _, heA₁'⟩ => ⟨⟨heL, heB₁⟩, heA₁'⟩⟩

/-- Single-linkage constant-order nested separation theorem (Graph Minors XXI, (2.5),
pages 3–6 of the preprint): for `m = (2 * p + 1) * (p + k + 1) ^ (2 * (p + k))` (so `n = m + 1`),
given a vital `p`-linkage `L` in `G` and `m + 1` nested separations `(A r, B r)` of constant order
`k` connected by transfer linkages `M r`, there exists `r : Fin m` such that
`L ∩ B r ∩ A (r + 1) = M r`. -/
theorem vital_linkage_constant_order_nested_separations {p k : ℕ}
    {G L : Hypergraph α β}
    {A B : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k)) + 1) → Hypergraph α β}
    {M : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k))) → Hypergraph α β}
    (hL : IsVitalPLinkage G L p)
    (hsep : ∀ r : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k)) + 1),
      G.IsSeparation (A r) (B r) ∧ separationOrder (A r) (B r) = k)
    (hmono : ∀ r₁ r₂ : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k)) + 1),
      r₁ < r₂ → A r₁ ≤ A r₂ ∧ B r₂ ≤ B r₁)
    (hM : ∀ r : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k))),
      IsTransferLinkage (A r.castSucc) (B r.castSucc) (A r.succ) (B r.succ) (M r) k) :
    ∃ r : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k))),
      L ∩ B r.castSucc ∩ A r.succ = M r := by
  classical
  let m := (2 * p + 1) * (p + k + 1) ^ (2 * (p + k))
  let Z : Set α := terminals L
  have hZ_fin : Z.Finite := L.vertexSet_finite.subset fun _ h => h.1
  have hZ_le : Z.ncard ≤ p := hL.2.2
  obtain ⟨v, hv, hvM⟩ := exists_indexed_sequence_of_isTransferLinkage (fun r => (hsep r).2) hM
  have hA_le : ∀ a b : Fin (m + 1), a ≤ b → A a ≤ A b := by
    intro a b hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (hmono a b hlt).1
  have hB_le : ∀ a b : Fin (m + 1), a ≤ b → B b ≤ B a := by
    intro a b hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (hmono a b hlt).2
  let Z₀ : Set α := rightTerminalSet Z (A 0) (B 0)
  have hZ₀_fin : Z₀.Finite :=
    (A 0 ∩ B 0).vertexSet_finite.union (hZ_fin.subset inter_subset_left)
  have hZ₀_le : Z₀.ncard ≤ p + k := by
    have h1 : Z₀.ncard ≤ (A 0 ∩ B 0).vertexSet.ncard + (Z ∩ (B 0).vertexSet).ncard :=
      ncard_union_le _ _
    have h2 : (A 0 ∩ B 0).vertexSet.ncard = k := (hsep 0).2
    have h3 : (Z ∩ (B 0).vertexSet).ncard ≤ p :=
      (ncard_le_ncard inter_subset_left hZ_fin).trans hZ_le
    omega
  have : Fintype (SubPartitions12 Z₀) := (subPartitions12_finite hZ₀_fin).fintype
  have hcard_P : Fintype.card (SubPartitions12 Z₀) ≤ (p + k + 1) ^ (2 * (p + k)) := by
    rw [← Nat.card_eq_fintype_card]
    exact subPartitions12_ncard_le hZ₀_fin hZ₀_le
  have hφ_mem : ∀ r : Fin (m + 1),
      (Set.image (separatorBijection (v r) (v 0))) '' (linkagePattern (L ∩ B r)) ∈
        SubPartitions12 Z₀ := fun r =>
    (separatorBijection_mapsTo_and_injOn hL.1.1 Subset.rfl (hsep r).1
      (hA_le 0 r (Fin.zero_le r)) (hB_le 0 r (Fin.zero_le r))
      (hv 0).1 (hv 0).2 (hv r).1 (hv r).2).2.2
  let key : Fin (m + 1) → Fin (2 * p + 1) × SubPartitions12 Z₀ :=
    fun r => (terminalBalance Z hZ_fin hZ_le (A r) (B r), ⟨_, hφ_mem r⟩)
  have hcard_lt : Fintype.card (Fin (2 * p + 1) × SubPartitions12 Z₀) <
      Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have hle : (2 * p + 1) * Fintype.card (SubPartitions12 Z₀) ≤ m :=
      Nat.mul_le_mul_left (2 * p + 1) hcard_P
    omega
  obtain ⟨r₁, r₂, hr_ne, hkey_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt key hcard_lt
  have hex_lt : ∃ i j : Fin (m + 1), i < j ∧ key i = key j := by
    rcases lt_or_gt_of_ne hr_ne with hij | hji
    · exact ⟨r₁, r₂, hij, hkey_eq⟩
    · exact ⟨r₂, r₁, hji, hkey_eq.symm⟩
  obtain ⟨i, j, hij, hkey_ij⟩ := hex_lt
  have hc_ij : terminalBalance Z hZ_fin hZ_le (A i) (B i) =
      terminalBalance Z hZ_fin hZ_le (A j) (B j) :=
    congrArg Prod.fst hkey_ij
  have hpat_ij :
      (Set.image (separatorBijection (v i) (v 0))) '' (linkagePattern (L ∩ B i)) =
      (Set.image (separatorBijection (v j) (v 0))) '' (linkagePattern (L ∩ B j)) :=
    congrArg (Subtype.val ∘ Prod.snd) hkey_ij
  obtain ⟨hZA, hZB⟩ := lemma_2_5_claim_1 hZ_fin hZ_le (hmono i j hij).1 (hmono i j hij).2 hc_ij
  let r₀ : Fin m := ⟨i.1, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.2)⟩
  have hi_eq : r₀.castSucc = i := by ext; rfl
  have hsucc_le : r₀.succ ≤ j := hij
  obtain ⟨M_ij, hM_ij_idx, hM_ij_inter⟩ :=
    exists_interval_isIndexedTransferLinkage (fun r => (hsep r).1) hA_le hB_le hvM
      (j.1 - i.1) i j hij rfl
  have hL_ij : L ∩ B i ∩ A j = M_ij :=
    eq_transfer_of_claim_2 hL.1 Subset.rfl (hsep i).1 (hsep j).1
      (hA_le 0 i (Fin.zero_le i)) (hB_le 0 i (Fin.zero_le i))
      (hA_le 0 j (Fin.zero_le j)) (hB_le 0 j (Fin.zero_le j))
      (hmono i j hij).1 (hmono i j hij).2 (hv 0).1 (hv 0).2
      hM_ij_idx hZA hZB hpat_ij
  refine ⟨r₀, ?_⟩
  rw [hi_eq] at hM_ij_inter ⊢
  exact inter_subinterval_eq hL.1.1.1 (hsep i).1.right_le (hsep j).1.left_le
    (hA_le r₀.succ j hsucc_le) (hL_ij.symm ▸ hM_ij_inter)

/-- Two-linkage constant-order nested separation theorem (simultaneous version of Graph Minors XXI,
(2.5), used in the proof of (2.7), page 8 of the preprint): for
`m = (4 * p + 1) * (2 * p + k + 1) ^ (2 * (2 * p + k)) * (2 * p + k + 1) ^ (2 * (2 * p + k))`,
given two vital `p`-linkages `L, L'` in `G` and `m + 1` nested separations `(A r, B r)` of constant
order `k` connected by transfer linkages `M r`, there exists `r : Fin m` such that
`L ∩ B r ∩ A (r + 1) = M r` and `L' ∩ B r ∩ A (r + 1) = M r`. -/
theorem vital_linkages_constant_order_nested_separations {p k : ℕ}
    {G L L' : Hypergraph α β}
    {A B : Fin ((4 * p + 1) * (2 * p + k + 1) ^ (2 * (2 * p + k)) *
      (2 * p + k + 1) ^ (2 * (2 * p + k)) + 1) → Hypergraph α β}
    {M : Fin ((4 * p + 1) * (2 * p + k + 1) ^ (2 * (2 * p + k)) *
      (2 * p + k + 1) ^ (2 * (2 * p + k))) → Hypergraph α β}
    (hL : IsVitalPLinkage G L p)
    (hL' : IsVitalPLinkage G L' p)
    (hsep : ∀ r : Fin ((4 * p + 1) * (2 * p + k + 1) ^ (2 * (2 * p + k)) *
      (2 * p + k + 1) ^ (2 * (2 * p + k)) + 1),
      G.IsSeparation (A r) (B r) ∧ separationOrder (A r) (B r) = k)
    (hmono : ∀ r₁ r₂ : Fin ((4 * p + 1) * (2 * p + k + 1) ^ (2 * (2 * p + k)) *
      (2 * p + k + 1) ^ (2 * (2 * p + k)) + 1),
      r₁ < r₂ → A r₁ ≤ A r₂ ∧ B r₂ ≤ B r₁)
    (hM : ∀ r : Fin ((4 * p + 1) * (2 * p + k + 1) ^ (2 * (2 * p + k)) *
      (2 * p + k + 1) ^ (2 * (2 * p + k))),
      IsTransferLinkage (A r.castSucc) (B r.castSucc) (A r.succ) (B r.succ) (M r) k) :
    ∃ r : Fin ((4 * p + 1) * (2 * p + k + 1) ^ (2 * (2 * p + k)) *
      (2 * p + k + 1) ^ (2 * (2 * p + k))),
      L ∩ B r.castSucc ∩ A r.succ = M r ∧
      L' ∩ B r.castSucc ∩ A r.succ = M r := by
  classical
  let m := (4 * p + 1) * (2 * p + k + 1) ^ (2 * (2 * p + k)) *
    (2 * p + k + 1) ^ (2 * (2 * p + k))
  let Z : Set α := terminals L ∪ terminals L'
  have hZ_fin : Z.Finite :=
    (L.vertexSet_finite.subset fun _ h => h.1).union
      (L'.vertexSet_finite.subset fun _ h => h.1)
  have hZ_le : Z.ncard ≤ 2 * p := by
    have h1 : Z.ncard ≤ (terminals L).ncard + (terminals L').ncard := ncard_union_le _ _
    have h2 : (terminals L).ncard ≤ p := hL.2.2
    have h3 : (terminals L').ncard ≤ p := hL'.2.2
    omega
  obtain ⟨v, hv, hvM⟩ := exists_indexed_sequence_of_isTransferLinkage (fun r => (hsep r).2) hM
  have hA_le : ∀ a b : Fin (m + 1), a ≤ b → A a ≤ A b := by
    intro a b hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (hmono a b hlt).1
  have hB_le : ∀ a b : Fin (m + 1), a ≤ b → B b ≤ B a := by
    intro a b hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (hmono a b hlt).2
  let Z₀ : Set α := rightTerminalSet Z (A 0) (B 0)
  have hZ₀_fin : Z₀.Finite :=
    (A 0 ∩ B 0).vertexSet_finite.union (hZ_fin.subset inter_subset_left)
  have hZ₀_le : Z₀.ncard ≤ 2 * p + k := by
    have h1 : Z₀.ncard ≤ (A 0 ∩ B 0).vertexSet.ncard + (Z ∩ (B 0).vertexSet).ncard :=
      ncard_union_le _ _
    have h2 : (A 0 ∩ B 0).vertexSet.ncard = k := (hsep 0).2
    have h3 : (Z ∩ (B 0).vertexSet).ncard ≤ 2 * p :=
      (ncard_le_ncard inter_subset_left hZ_fin).trans hZ_le
    omega
  have : Fintype (SubPartitions12 Z₀) := (subPartitions12_finite hZ₀_fin).fintype
  have hcard_P : Fintype.card (SubPartitions12 Z₀) ≤ (2 * p + k + 1) ^ (2 * (2 * p + k)) := by
    rw [← Nat.card_eq_fintype_card]
    exact subPartitions12_ncard_le hZ₀_fin hZ₀_le
  have hφ_mem : ∀ r : Fin (m + 1),
      (Set.image (separatorBijection (v r) (v 0))) '' (linkagePattern (L ∩ B r)) ∈
        SubPartitions12 Z₀ := fun r =>
    (separatorBijection_mapsTo_and_injOn hL.1.1 subset_union_left (hsep r).1
      (hA_le 0 r (Fin.zero_le r)) (hB_le 0 r (Fin.zero_le r))
      (hv 0).1 (hv 0).2 (hv r).1 (hv r).2).2.2
  have hφ'_mem : ∀ r : Fin (m + 1),
      (Set.image (separatorBijection (v r) (v 0))) '' (linkagePattern (L' ∩ B r)) ∈
        SubPartitions12 Z₀ := fun r =>
    (separatorBijection_mapsTo_and_injOn hL'.1.1 subset_union_right (hsep r).1
      (hA_le 0 r (Fin.zero_le r)) (hB_le 0 r (Fin.zero_le r))
      (hv 0).1 (hv 0).2 (hv r).1 (hv r).2).2.2
  let key : Fin (m + 1) → Fin (2 * (2 * p) + 1) × SubPartitions12 Z₀ × SubPartitions12 Z₀ :=
    fun r => (terminalBalance Z hZ_fin hZ_le (A r) (B r), ⟨_, hφ_mem r⟩, ⟨_, hφ'_mem r⟩)
  have hcard_lt : Fintype.card (Fin (2 * (2 * p) + 1) × SubPartitions12 Z₀ × SubPartitions12 Z₀) <
      Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have h2 : 2 * (2 * p) + 1 = 4 * p + 1 := by omega
    rw [h2, ← Nat.mul_assoc]
    have hle1 : (4 * p + 1) * Fintype.card (SubPartitions12 Z₀) ≤
        (4 * p + 1) * (2 * p + k + 1) ^ (2 * (2 * p + k)) :=
      Nat.mul_le_mul_left (4 * p + 1) hcard_P
    have hle2 : (4 * p + 1) * Fintype.card (SubPartitions12 Z₀) * Fintype.card (SubPartitions12 Z₀) ≤ m :=
      Nat.mul_le_mul hle1 hcard_P
    omega
  obtain ⟨r₁, r₂, hr_ne, hkey_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt key hcard_lt
  have hex_lt : ∃ i j : Fin (m + 1), i < j ∧ key i = key j := by
    rcases lt_or_gt_of_ne hr_ne with hij | hji
    · exact ⟨r₁, r₂, hij, hkey_eq⟩
    · exact ⟨r₂, r₁, hji, hkey_eq.symm⟩
  obtain ⟨i, j, hij, hkey_ij⟩ := hex_lt
  have hc_ij : terminalBalance Z hZ_fin hZ_le (A i) (B i) =
      terminalBalance Z hZ_fin hZ_le (A j) (B j) :=
    congrArg Prod.fst hkey_ij
  have hpat_ij :
      (Set.image (separatorBijection (v i) (v 0))) '' (linkagePattern (L ∩ B i)) =
      (Set.image (separatorBijection (v j) (v 0))) '' (linkagePattern (L ∩ B j)) :=
    congrArg (Subtype.val ∘ Prod.fst ∘ Prod.snd) hkey_ij
  have hpat'_ij :
      (Set.image (separatorBijection (v i) (v 0))) '' (linkagePattern (L' ∩ B i)) =
      (Set.image (separatorBijection (v j) (v 0))) '' (linkagePattern (L' ∩ B j)) :=
    congrArg (Subtype.val ∘ Prod.snd ∘ Prod.snd) hkey_ij
  obtain ⟨hZA, hZB⟩ := lemma_2_5_claim_1 hZ_fin hZ_le (hmono i j hij).1 (hmono i j hij).2 hc_ij
  let r₀ : Fin m := ⟨i.1, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.2)⟩
  have hi_eq : r₀.castSucc = i := by ext; rfl
  have hsucc_le : r₀.succ ≤ j := hij
  obtain ⟨M_ij, hM_ij_idx, hM_ij_inter⟩ :=
    exists_interval_isIndexedTransferLinkage (fun r => (hsep r).1) hA_le hB_le hvM
      (j.1 - i.1) i j hij rfl
  have hL_ij : L ∩ B i ∩ A j = M_ij :=
    eq_transfer_of_claim_2 hL.1 subset_union_left (hsep i).1 (hsep j).1
      (hA_le 0 i (Fin.zero_le i)) (hB_le 0 i (Fin.zero_le i))
      (hA_le 0 j (Fin.zero_le j)) (hB_le 0 j (Fin.zero_le j))
      (hmono i j hij).1 (hmono i j hij).2 (hv 0).1 (hv 0).2
      hM_ij_idx hZA hZB hpat_ij
  have hL'_ij : L' ∩ B i ∩ A j = M_ij :=
    eq_transfer_of_claim_2 hL'.1 subset_union_right (hsep i).1 (hsep j).1
      (hA_le 0 i (Fin.zero_le i)) (hB_le 0 i (Fin.zero_le i))
      (hA_le 0 j (Fin.zero_le j)) (hB_le 0 j (Fin.zero_le j))
      (hmono i j hij).1 (hmono i j hij).2 (hv 0).1 (hv 0).2
      hM_ij_idx hZA hZB hpat'_ij
  refine ⟨r₀, ?_, ?_⟩
  · rw [hi_eq] at hM_ij_inter ⊢
    exact inter_subinterval_eq hL.1.1.1 (hsep i).1.right_le (hsep j).1.left_le
      (hA_le r₀.succ j hsucc_le) (hL_ij.symm ▸ hM_ij_inter)
  · rw [hi_eq] at hM_ij_inter ⊢
    exact inter_subinterval_eq hL'.1.1.1 (hsep i).1.right_le (hsep j).1.left_le
      (hA_le r₀.succ j hsucc_le) (hL'_ij.symm ▸ hM_ij_inter)

/-- Combinatorial subsequence extraction lemma for Graph Minors XXI, (2.6) and (2.7) (page 8 of the
preprint): for any function `f : ℕ → ℕ` with `1 ≤ f k'` for all `k'`, and any `gap, k₀ : ℕ`, there
exists `len ≥ 2` such that in any sequence `d : ℕ → ℕ` satisfying `k₀ ≤ d i ≤ k₀ + gap` on
`[a, a + len)`, there exist `k' ∈ [k₀, k₀ + gap]` and a strictly increasing sequence
`φ : Fin (f k' + 1) → ℕ` in `[a, a + len)` on which `d` equals `k'` and strictly exceeds `k'`
between consecutive terms. -/
lemma exists_monotone_interval_of_le_add (f : ℕ → ℕ) (hf : ∀ k', 1 ≤ f k') :
    ∀ (gap k₀ : ℕ), ∃ len : ℕ, 2 ≤ len ∧
      ∀ (d : ℕ → ℕ) (a : ℕ),
        (∀ i : ℕ, a ≤ i → i < a + len → k₀ ≤ d i ∧ d i ≤ k₀ + gap) →
        ∃ k' : ℕ, k₀ ≤ k' ∧ k' ≤ k₀ + gap ∧
          ∃ φ : Fin (f k' + 1) → ℕ,
            StrictMono φ ∧
            (∀ r : Fin (f k' + 1), a ≤ φ r ∧ φ r < a + len ∧ d (φ r) = k') ∧
            (∀ r : Fin (f k'), ∀ j : ℕ, φ r.castSucc < j → j < φ r.succ → k' < d j) := by
  intro gap
  induction gap with
  | zero =>
    intro k₀
    have hfk : 1 ≤ f k₀ := hf k₀
    refine ⟨f k₀ + 1, by omega, fun d a hd => ?_⟩
    refine ⟨k₀, le_rfl, le_rfl, fun r => a + r.1, ?_, ?_, ?_⟩
    · intro r₁ r₂ hlt
      change a + r₁.1 < a + r₂.1
      omega
    · intro r
      dsimp
      have hr := hd (a + r.1) (by omega) (by omega)
      exact ⟨by omega, by omega, by omega⟩
    · intro r j hj₁ hj₂
      change a + r.1 < j at hj₁
      change j < a + (r.1 + 1) at hj₂
      omega
  | succ gap ih =>
    intro k₀
    obtain ⟨L, hL2, hL⟩ := ih (k₀ + 1)
    let M := f k₀
    have hM1 : 1 ≤ M := hf k₀
    have hlen2 : 2 ≤ (M + 1) * L := by
      have : 2 * 2 ≤ (M + 1) * L := Nat.mul_le_mul (by omega) hL2
      omega
    refine ⟨(M + 1) * L, hlen2, fun d a hd => ?_⟩
    by_cases hsub : ∃ b : ℕ, a ≤ b ∧ b + L ≤ a + (M + 1) * L ∧
        ∀ i : ℕ, b ≤ i → i < b + L → d i ≠ k₀
    · rcases hsub with ⟨b, hab, hb_len, hne_k₀⟩
      have hd' : ∀ i : ℕ, b ≤ i → i < b + L → k₀ + 1 ≤ d i ∧ d i ≤ (k₀ + 1) + gap := by
        intro i hbi hiL
        have hdi := hd i (by omega) (by omega)
        have hne := hne_k₀ i hbi hiL
        omega
      obtain ⟨k', hk'₁, hk'₂, φ, hφ_mono, hφ_in, hφ_gt⟩ := hL d b hd'
      refine ⟨k', by omega, by omega, φ, hφ_mono, fun r => ?_, hφ_gt⟩
      obtain ⟨h1, h2, h3⟩ := hφ_in r
      exact ⟨by omega, by omega, h3⟩
    · have hex : ∀ b : ℕ, a ≤ b → b + L ≤ a + (M + 1) * L →
          ∃ i : ℕ, b ≤ i ∧ i < b + L ∧ d i = k₀ := by
        intro b hab hb_len
        by_contra hno
        apply hsub
        exact ⟨b, hab, hb_len, fun i hbi hiL hdi => hno ⟨i, hbi, hiL, hdi⟩⟩
      classical
      let next (b : ℕ) : ℕ :=
        if h : ∃ i : ℕ, b ≤ i ∧ i < b + L ∧ d i = k₀ then Nat.find h else b
      have hnext_props : ∀ b : ℕ, a ≤ b → b + L ≤ a + (M + 1) * L →
          b ≤ next b ∧ next b < b + L ∧ d (next b) = k₀ ∧
          (∀ j : ℕ, b ≤ j → j < next b → d j ≠ k₀) := by
        intro b hab hb_len
        have h := hex b hab hb_len
        have hnext_eq : next b = Nat.find h := by simp [next, h]
        obtain ⟨h1, h2, h3⟩ := Nat.find_spec h
        refine ⟨hnext_eq ▸ h1, hnext_eq ▸ h2, hnext_eq ▸ h3, fun j hbj hj_lt hdj => ?_⟩
        rw [hnext_eq] at hj_lt
        exact Nat.find_min h hj_lt ⟨hbj, lt_trans hj_lt h2, hdj⟩
      let ψ : ℕ → ℕ := fun r => Nat.rec (next a) (fun _ prev => next (prev + 1)) r
      have hψ_step : ∀ r : ℕ, ψ (r + 1) = next (ψ r + 1) := fun _ => rfl
      have hψ_props : ∀ r : ℕ, r ≤ M →
          a ≤ ψ r ∧ ψ r < a + (r + 1) * L ∧ d (ψ r) = k₀ := by
        intro r
        induction r with
        | zero =>
          intro _
          have h1L : a + L ≤ a + (M + 1) * L := by
            have : 1 * L ≤ (M + 1) * L := Nat.mul_le_mul_right L (by omega)
            omega
          have h0 := hnext_props a le_rfl h1L
          change a ≤ next a ∧ next a < a + 1 * L ∧ d (next a) = k₀
          exact ⟨h0.1, by simpa using h0.2.1, h0.2.2.1⟩
        | succ r ihr =>
          intro hrM
          obtain ⟨h1, h2, _⟩ := ihr (by omega)
          have hb_len : (ψ r + 1) + L ≤ a + (M + 1) * L := by
            have hmul : (r + 1) * L + L ≤ (M + 1) * L := by
              have : (r + 2) * L ≤ (M + 1) * L := Nat.mul_le_mul_right L (by omega)
              have heq : (r + 2) * L = (r + 1) * L + L := by ring
              omega
            omega
          have hn := hnext_props (ψ r + 1) (by omega) hb_len
          rw [hψ_step r]
          have heq : (r + 1 + 1) * L = (r + 1) * L + L := by ring
          exact ⟨by omega, by omega, hn.2.2.1⟩
      have hψ_lt : ∀ r : ℕ, r < M →
          ψ r < ψ (r + 1) ∧ ∀ j : ℕ, ψ r < j → j < ψ (r + 1) → k₀ < d j := by
        intro r hrM
        obtain ⟨h1, h2, _⟩ := hψ_props r (by omega)
        have hmul : (r + 1) * L + L ≤ (M + 1) * L := by
          have : (r + 2) * L ≤ (M + 1) * L := Nat.mul_le_mul_right L (by omega)
          have heq : (r + 2) * L = (r + 1) * L + L := by ring
          omega
        have hb_len : (ψ r + 1) + L ≤ a + (M + 1) * L := by omega
        have hn := hnext_props (ψ r + 1) (by omega) hb_len
        rw [hψ_step r]
        refine ⟨by omega, fun j hj₁ hj₂ => ?_⟩
        have hne := hn.2.2.2 j (by omega) hj₂
        have hj_lt_len : j < a + (M + 1) * L := by omega
        have hdj := (hd j (by omega) hj_lt_len).1
        omega
      have hψ_mono : StrictMono (fun r : Fin (M + 1) => ψ r.1) := by
        refine Fin.strictMono_iff_lt_succ.mpr fun r => ?_
        exact (hψ_lt r.1 r.2).1
      refine ⟨k₀, le_rfl, by omega, fun r => ψ r.1, hψ_mono, fun r => ?_,
        fun r j hj₁ hj₂ => (hψ_lt r.1 r.2).2 j hj₁ hj₂⟩
      dsimp
      obtain ⟨h1, h2, h3⟩ := hψ_props r.1 (by omega)
      have : (r.1 + 1) * L ≤ (M + 1) * L := Nat.mul_le_mul_right L (by omega)
      exact ⟨h1, by omega, h3⟩

/-- Bounded-order nested separation theorem for a single vital `p`-linkage (Graph Minors XXI, (2.6),
pages 6–7 of the preprint): proved by applying `vital_linkage_constant_order_nested_separations`
((2.5)) to the subsequence of separations of equal minimum order `k'` extracted by
`exists_monotone_interval_of_le_add` with `f k' = (2 * p + 1) * (p + k' + 1) ^ (2 * (p + k'))`. -/
theorem vital_linkage_bounded_order_nested_separations (p k : ℕ) :
    ∃ n : ℕ, 2 ≤ n ∧
      ∀ {α : Type u} {β : Type v} (G L : Hypergraph α β)
        (A B : Fin n → Hypergraph α β)
        (M : Fin n → Fin n → Hypergraph α β),
        IsVitalPLinkage G L p →
        (∀ i : Fin n, G.IsSeparation (A i) (B i) ∧ separationOrder (A i) (B i) ≤ k) →
        (∀ i j : Fin n, i < j → A i ≤ A j ∧ B j ≤ B i) →
        (∀ i i' : Fin n, i < i' →
          separationOrder (A i) (B i) = separationOrder (A i') (B i') →
          (∀ j : Fin n, i < j → j < i' →
            separationOrder (A i) (B i) < separationOrder (A j) (B j)) →
          IsTransferLinkage (A i) (B i) (A i') (B i') (M i i') (separationOrder (A i) (B i))) →
        ∃ i i' : Fin n, i < i' ∧
          separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
          (∀ j : Fin n, i < j → j < i' →
            separationOrder (A i) (B i) < separationOrder (A j) (B j)) ∧
          L ∩ B i ∩ A i' = M i i' := by
  let f : ℕ → ℕ := fun k' => (2 * p + 1) * (p + k' + 1) ^ (2 * (p + k'))
  have hf : ∀ k', 1 ≤ f k' := fun k' =>
    Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  obtain ⟨n, hn2, hn⟩ := exists_monotone_interval_of_le_add f hf k 0
  refine ⟨n, hn2, fun {α β} G L A B M hL hsep hmono hM => ?_⟩
  let d : ℕ → ℕ := fun i => if h : i < n then separationOrder (A ⟨i, h⟩) (B ⟨i, h⟩) else 0
  have hd : ∀ i : ℕ, 0 ≤ i → i < 0 + n → 0 ≤ d i ∧ d i ≤ 0 + k := by
    intro i _ hi
    have hin : i < n := by omega
    simp only [d, hin, dite_true, zero_le, zero_add]
    exact ⟨trivial, (hsep ⟨i, hin⟩).2⟩
  obtain ⟨k', _, _, φ₀, hφ₀_mono, hφ₀_in, hφ₀_gt⟩ := hn d 0 hd
  let φ : Fin (f k' + 1) → Fin n :=
    fun r => ⟨φ₀ r, by have := (hφ₀_in r).2.1; omega⟩
  have hφ_mono : StrictMono φ := fun r₁ r₂ hlt => hφ₀_mono hlt
  have hφ_ord : ∀ r : Fin (f k' + 1),
      separationOrder (A (φ r)) (B (φ r)) = k' := by
    intro r
    have hlt : φ₀ r < n := by have := (hφ₀_in r).2.1; omega
    have hval := (hφ₀_in r).2.2
    simpa [d, hlt, φ] using hval
  have hφ_between : ∀ r : Fin (f k'), ∀ j : Fin n,
      φ r.castSucc < j → j < φ r.succ →
      separationOrder (A (φ r.castSucc)) (B (φ r.castSucc)) < separationOrder (A j) (B j) := by
    intro r j hj₁ hj₂
    rw [hφ_ord r.castSucc]
    have hgt := hφ₀_gt r j.1 hj₁ hj₂
    simpa [d, j.2] using hgt
  have hsep' : ∀ r : Fin (f k' + 1),
      G.IsSeparation (A (φ r)) (B (φ r)) ∧ separationOrder (A (φ r)) (B (φ r)) = k' :=
    fun r => ⟨(hsep (φ r)).1, hφ_ord r⟩
  have hmono' : ∀ r₁ r₂ : Fin (f k' + 1),
      r₁ < r₂ → A (φ r₁) ≤ A (φ r₂) ∧ B (φ r₂) ≤ B (φ r₁) :=
    fun r₁ r₂ hlt => hmono (φ r₁) (φ r₂) (hφ_mono hlt)
  have hM' : ∀ r : Fin (f k'),
      IsTransferLinkage (A (φ r.castSucc)) (B (φ r.castSucc))
        (A (φ r.succ)) (B (φ r.succ)) (M (φ r.castSucc) (φ r.succ)) k' := by
    intro r
    have hlt : φ r.castSucc < φ r.succ := hφ_mono Fin.castSucc_lt_succ
    have heq_ord : separationOrder (A (φ r.castSucc)) (B (φ r.castSucc)) =
        separationOrder (A (φ r.succ)) (B (φ r.succ)) := by
      rw [hφ_ord, hφ_ord]
    have htr := hM (φ r.castSucc) (φ r.succ) hlt heq_ord (hφ_between r)
    rwa [hφ_ord r.castSucc] at htr
  obtain ⟨r, hrL⟩ :=
    vital_linkage_constant_order_nested_separations hL hsep' hmono' hM'
  refine ⟨φ r.castSucc, φ r.succ, hφ_mono Fin.castSucc_lt_succ, ?_, hφ_between r, hrL⟩
  rw [hφ_ord, hφ_ord]

/-- Bounded-order nested separation theorem for two vital `p`-linkages (Graph Minors XXI, (2.7),
page 8 of the preprint): for all `p, k : ℕ` there exists `n ≥ 2` such that for any two vital
`p`-linkages `L, L'` in `G` and `n` nested separations `(A i, B i)` of order `≤ k` with transfer
linkages `M i i'` between consecutive equal-minimum-order separations, there exist `i < i'` as in
(2.6)(ii) such that `L ∩ B i ∩ A i' = M i i'` and `L' ∩ B i ∩ A i' = M i i'`. -/
theorem vital_linkages_bounded_order_nested_separations (p k : ℕ) :
    ∃ n : ℕ, 2 ≤ n ∧
      ∀ (G L L' : Hypergraph α β)
        (A B : Fin n → Hypergraph α β)
        (M : Fin n → Fin n → Hypergraph α β),
        IsVitalPLinkage G L p →
        IsVitalPLinkage G L' p →
        (∀ i : Fin n, G.IsSeparation (A i) (B i) ∧ separationOrder (A i) (B i) ≤ k) →
        (∀ i j : Fin n, i < j → A i ≤ A j ∧ B j ≤ B i) →
        (∀ i i' : Fin n, i < i' →
          separationOrder (A i) (B i) = separationOrder (A i') (B i') →
          (∀ j : Fin n, i < j → j < i' →
            separationOrder (A i) (B i) < separationOrder (A j) (B j)) →
          IsTransferLinkage (A i) (B i) (A i') (B i') (M i i') (separationOrder (A i) (B i))) →
        ∃ i i' : Fin n, i < i' ∧
          separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
          (∀ j : Fin n, i < j → j < i' →
            separationOrder (A i) (B i) < separationOrder (A j) (B j)) ∧
          L ∩ B i ∩ A i' = M i i' ∧
          L' ∩ B i ∩ A i' = M i i' := by
  let f : ℕ → ℕ := fun k' =>
    (4 * p + 1) * (2 * p + k' + 1) ^ (2 * (2 * p + k')) *
      (2 * p + k' + 1) ^ (2 * (2 * p + k'))
  have hf : ∀ k', 1 ≤ f k' := fun k' =>
    Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
  obtain ⟨n, hn2, hn⟩ := exists_monotone_interval_of_le_add f hf k 0
  refine ⟨n, hn2, fun G L L' A B M hL hL' hsep hmono hM => ?_⟩
  let d : ℕ → ℕ := fun i => if h : i < n then separationOrder (A ⟨i, h⟩) (B ⟨i, h⟩) else 0
  have hd : ∀ i : ℕ, 0 ≤ i → i < 0 + n → 0 ≤ d i ∧ d i ≤ 0 + k := by
    intro i _ hi
    have hin : i < n := by omega
    simp only [d, hin, dite_true, zero_le, zero_add]
    exact ⟨trivial, (hsep ⟨i, hin⟩).2⟩
  obtain ⟨k', _, _, φ₀, hφ₀_mono, hφ₀_in, hφ₀_gt⟩ := hn d 0 hd
  let φ : Fin (f k' + 1) → Fin n :=
    fun r => ⟨φ₀ r, by have := (hφ₀_in r).2.1; omega⟩
  have hφ_mono : StrictMono φ := fun r₁ r₂ hlt => hφ₀_mono hlt
  have hφ_ord : ∀ r : Fin (f k' + 1),
      separationOrder (A (φ r)) (B (φ r)) = k' := by
    intro r
    have hlt : φ₀ r < n := by have := (hφ₀_in r).2.1; omega
    have hval := (hφ₀_in r).2.2
    simpa [d, hlt, φ] using hval
  have hφ_between : ∀ r : Fin (f k'), ∀ j : Fin n,
      φ r.castSucc < j → j < φ r.succ →
      separationOrder (A (φ r.castSucc)) (B (φ r.castSucc)) < separationOrder (A j) (B j) := by
    intro r j hj₁ hj₂
    rw [hφ_ord r.castSucc]
    have hgt := hφ₀_gt r j.1 hj₁ hj₂
    simpa [d, j.2] using hgt
  have hsep' : ∀ r : Fin (f k' + 1),
      G.IsSeparation (A (φ r)) (B (φ r)) ∧ separationOrder (A (φ r)) (B (φ r)) = k' :=
    fun r => ⟨(hsep (φ r)).1, hφ_ord r⟩
  have hmono' : ∀ r₁ r₂ : Fin (f k' + 1),
      r₁ < r₂ → A (φ r₁) ≤ A (φ r₂) ∧ B (φ r₂) ≤ B (φ r₁) :=
    fun r₁ r₂ hlt => hmono (φ r₁) (φ r₂) (hφ_mono hlt)
  have hM' : ∀ r : Fin (f k'),
      IsTransferLinkage (A (φ r.castSucc)) (B (φ r.castSucc))
        (A (φ r.succ)) (B (φ r.succ)) (M (φ r.castSucc) (φ r.succ)) k' := by
    intro r
    have hlt : φ r.castSucc < φ r.succ := hφ_mono Fin.castSucc_lt_succ
    have heq_ord : separationOrder (A (φ r.castSucc)) (B (φ r.castSucc)) =
        separationOrder (A (φ r.succ)) (B (φ r.succ)) := by
      rw [hφ_ord, hφ_ord]
    have htr := hM (φ r.castSucc) (φ r.succ) hlt heq_ord (hφ_between r)
    rwa [hφ_ord r.castSucc] at htr
  obtain ⟨r, hrL, hrL'⟩ :=
    vital_linkages_constant_order_nested_separations hL hL' hsep' hmono' hM'
  refine ⟨φ r.castSucc, φ r.succ, hφ_mono Fin.castSucc_lt_succ, ?_, hφ_between r, hrL, hrL'⟩
  rw [hφ_ord, hφ_ord]

end GM21
end GraphMinor
