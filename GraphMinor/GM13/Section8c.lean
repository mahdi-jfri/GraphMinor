module

public import GraphMinor.GM13.Section8b

/-!
# Graph Minors XIII, Section 8 (Part 3): Auxiliary 3-Connected Core Society for (8.6)

This file constructs the auxiliary society `auxCoreSociety hC hv₀` used to prove that
`coreDivision S C` is a rural division of `S` when `S` has no cross and `C` is a 4-linked core of
`S` (Graph Minors XIII, Section 8, (8.6), pages 96–97), and proves via `GM09.theorem_2_3` and
`GM09.theorem_2_4` that `auxCoreSociety hC hv₀` is a rural society.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Classical Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
  GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v} {β' : Type*}

/-! ## Total Boundary of `coreDivision S C` -/

/-- For each `B ∈ coreDivision S C`, `V(B) ∩ V(C) = divBoundary S B`. -/
theorem inter_core_eq_divBoundary_of_mem_coreDivision {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {B : Graph α β} (hB : B ∈ coreDivision S C) :
    V(B) ∩ V(C) = divBoundary S B := by
  obtain ⟨X, ⟨A₀, hA₀_raw, rfl⟩, rfl⟩ := hB
  have hbd_eq :
      divBoundary S (subgraphSUnion S.G
        {A ∈ coreRawDivision S C | divBoundary S A = divBoundary S A₀}) =
      divBoundary S A₀ :=
    lemma_8_6_claim_3 hC ⟨A₀, hA₀_raw, rfl⟩
  rw [hbd_eq]
  ext v
  simp only [vertexSet_subgraphSUnion, mem_inter_iff, mem_iUnion, exists_prop]
  refine ⟨fun ⟨⟨A, ⟨hA_raw, hA_bd⟩, hvA⟩, hvC⟩ => ?_,
    fun hv => ⟨⟨A₀, ⟨hA₀_raw, rfl⟩, hv.1⟩, ((lemma_8_6_claim_2 hC hA₀_raw).symm ▸ hv).2⟩⟩
  rw [← hA_bd, ← lemma_8_6_claim_2 hC hA_raw]
  exact ⟨hvA, hvC⟩

/-- For a 4-linked core `C` of `S`, `divTotalBoundary S (coreDivision S C) = V(C)`. -/
theorem divTotalBoundary_coreDivision_eq {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) :
    divTotalBoundary S (coreDivision S C) = V(C) := by
  have hdiv := isSocietyDivision_coreDivision hC
  refine subset_antisymm ?_ ?_
  · rintro v hv
    obtain ⟨B, hB, hvB⟩ := mem_iUnion₂.mp hv
    exact (boundary_isClique_in_core hC hB).1 hvB
  · intro v hvC
    have hvG : v ∈ V(S.G) := hC.isCore.isTrisecting.subset_V hvC
    rw [← hdiv.sUnion_eq, vertexSet_subgraphSUnion] at hvG
    obtain ⟨B, hB, hvB⟩ := mem_iUnion₂.mp hvG
    have hv_bd : v ∈ divBoundary S B := by
      rw [← inter_core_eq_divBoundary_of_mem_coreDivision hC hB]
      exact ⟨hvB, hvC⟩
    exact mem_iUnion₂.mpr ⟨B, hB, hv_bd⟩

theorem divTotalBoundary_union_bar_coreDivision_eq {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) :
    divTotalBoundary S (coreDivision S C) ∪ S.Ω.bar = V(C) := by
  rw [divTotalBoundary_coreDivision_eq hC,
    union_eq_self_of_subset_right hC.isCore.isTrisecting.bar_subset]

/-! ## Auxiliary 3-Connected Core Graph and Society -/

/-- For `A ∈ coreDivision S C` with `(divBoundary S A).ncard ≤ 1`, the vertex of `V(C)` at which
the loop representing `A` is placed in `auxCoreGraph`. -/
noncomputable def loopVertex (S : Society α β) (v₀ : α) (A : Graph α β) : α :=
  if h : (divBoundary S A).Nonempty then h.some else v₀

theorem loopVertex_mem_core {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C))
    {A : Graph α β} (hA : A ∈ coreDivision S C) :
    loopVertex S v₀ A ∈ V(C) := by
  dsimp [loopVertex]
  split_ifs with hne
  · exact (boundary_isClique_in_core hC hA).1 hne.some_mem
  · exact hv₀

theorem divBoundary_eq_singleton_loopVertex {S : Society α β} (v₀ : α)
    {A : Graph α β} (hcard : (divBoundary S A).ncard = 1) :
    divBoundary S A = {loopVertex S v₀ A} := by
  obtain ⟨v, hv⟩ := ncard_eq_one.mp hcard
  have hne : (divBoundary S A).Nonempty := by rw [hv]; exact singleton_nonempty v
  have hmem : loopVertex S v₀ A ∈ divBoundary S A := by
    simp only [loopVertex, hne, ↓reduceDIte]
    exact hne.some_mem
  rw [hv] at hmem ⊢
  rw [mem_singleton_iff.mp hmem]

/-- The edge type of `auxCoreGraph`:
- `Sum.inl e` for `e ∈ E(C)`,
- `Sum.inr (Sum.inl (A, u))` for `A ∈ coreDivision S C` with `|∂A| = 3` and `u ∈ ∂A`,
- `Sum.inr (Sum.inr A)` for `A ∈ coreDivision S C` with `|∂A| ≤ 1`. -/
abbrev AuxCoreEdge (α : Type u) (β : Type v) (β' : Type*) : Type _ :=
  β' ⊕ ((Graph α β × α) ⊕ Graph α β)

/-- The auxiliary graph obtained from the 4-linked core `C` by adding a vertex `Sum.inl A` joined
to `Sum.inr '' ∂A` for each `A ∈ coreDivision S C` with `|∂A| = 3`, and a loop at
`Sum.inr (loopVertex S v₀ A)` for each `A ∈ coreDivision S C` with `|∂A| ≤ 1`. -/
noncomputable def auxCoreGraph {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C)) :
    Graph (Graph α β ⊕ α) (AuxCoreEdge α β β') where
  vertexSet :=
    (Sum.inl '' {A ∈ coreDivision S C | (divBoundary S A).ncard = 3}) ∪
    (Sum.inr '' V(C))
  edgeSet :=
    (Sum.inl '' E(C)) ∪
    (Sum.inr '' (Sum.inl '' {p : Graph α β × α |
      p.1 ∈ coreDivision S C ∧ (divBoundary S p.1).ncard = 3 ∧ p.2 ∈ divBoundary S p.1})) ∪
    (Sum.inr '' (Sum.inr '' {A ∈ coreDivision S C | (divBoundary S A).ncard ≤ 1}))
  IsLink c x y :=
    match c with
    | Sum.inl e =>
      ∃ u v : α, C.IsLink e u v ∧ x = Sum.inr u ∧ y = Sum.inr v
    | Sum.inr (Sum.inl p) =>
      p.1 ∈ coreDivision S C ∧ (divBoundary S p.1).ncard = 3 ∧ p.2 ∈ divBoundary S p.1 ∧
        ((x = Sum.inl p.1 ∧ y = Sum.inr p.2) ∨ (x = Sum.inr p.2 ∧ y = Sum.inl p.1))
    | Sum.inr (Sum.inr A) =>
      A ∈ coreDivision S C ∧ (divBoundary S A).ncard ≤ 1 ∧
        x = Sum.inr (loopVertex S v₀ A) ∧ y = Sum.inr (loopVertex S v₀ A)
  isLink_symm c _ := by
    cases c with
    | inl e =>
      exact ⟨fun x y ⟨u, v, hl, hx, hy⟩ => ⟨v, u, hl.symm, hy, hx⟩⟩
    | inr c' =>
      cases c' with
      | inl p =>
        exact ⟨fun x y ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4.symm.imp
          (fun ⟨hx, hy⟩ => ⟨hy, hx⟩) (fun ⟨hx, hy⟩ => ⟨hy, hx⟩)⟩⟩
      | inr A =>
        exact ⟨fun x y ⟨h1, h2, hx, hy⟩ => ⟨h1, h2, hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink c x y z w h1 h2 := by
    cases c with
    | inl e =>
      obtain ⟨u₁, v₁, hl₁, rfl, rfl⟩ := h1
      obtain ⟨u₂, v₂, hl₂, rfl, rfl⟩ := h2
      rcases C.eq_or_eq_of_isLink_of_isLink hl₁ hl₂ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    | inr c' =>
      cases c' with
      | inl p =>
        rcases h1.2.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases h2.2.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
      | inr A =>
        rw [h1.2.2.1, h2.2.2.1]
        exact Or.inl rfl
  edge_mem_iff_exists_isLink c := by
    cases c with
    | inl e =>
      simp only [mem_union, mem_image, Sum.inl.injEq, exists_eq_right, reduceCtorEq,
        and_false, exists_false, or_false]
      exact ⟨fun he => by
        obtain ⟨u, v, hl⟩ := C.exists_isLink_of_mem_edgeSet he
        exact ⟨Sum.inr u, Sum.inr v, u, v, hl, rfl, rfl⟩,
        fun ⟨_, _, u, v, hl, _, _⟩ => hl.edge_mem⟩
    | inr c' =>
      cases c' with
      | inl p =>
        simp only [mem_union, mem_image, reduceCtorEq, and_false, exists_false, Sum.inr.injEq,
          Sum.inl.injEq, exists_eq_right, false_or, or_false, mem_ofPred_eq]
        exact ⟨fun ⟨h1, h2, h3⟩ =>
          ⟨Sum.inl p.1, Sum.inr p.2, h1, h2, h3, Or.inl ⟨rfl, rfl⟩⟩,
          fun ⟨_, _, h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩⟩
      | inr A =>
        simp only [mem_union, mem_image, reduceCtorEq, and_false, exists_false, Sum.inr.injEq,
          exists_eq_right, false_or, mem_ofPred_eq]
        exact ⟨fun ⟨h1, h2⟩ =>
          ⟨Sum.inr (loopVertex S v₀ A), Sum.inr (loopVertex S v₀ A), h1, h2, rfl, rfl⟩,
          fun ⟨_, _, h1, h2, _, _⟩ => ⟨h1, h2⟩⟩
  left_mem_of_isLink c x y h := by
    cases c with
    | inl e =>
      obtain ⟨u, v, hl, rfl, _⟩ := h
      exact Or.inr ⟨u, hl.left_mem, rfl⟩
    | inr c' =>
      cases c' with
      | inl p =>
        rcases h.2.2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact Or.inl ⟨p.1, ⟨h.1, h.2.1⟩, rfl⟩
        · exact Or.inr ⟨p.2, (boundary_isClique_in_core hC h.1).1 h.2.2.1, rfl⟩
      | inr A =>
        rw [h.2.2.1]
        exact Or.inr ⟨loopVertex S v₀ A, loopVertex_mem_core hC hv₀ h.1, rfl⟩

/-- The auxiliary society `(auxCoreGraph hC hv₀, liftCyclicPermInr S.Ω)`. -/
noncomputable def auxCoreSociety {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C)) :
    Society (Graph α β ⊕ α) (AuxCoreEdge α β β') where
  G := auxCoreGraph hC hv₀
  Ω := liftCyclicPermInr S.Ω
  finite_V := by
    have hdiv := isSocietyDivision_coreDivision hC
    have hfin_C : V(C).Finite := S.finite_V.subset hC.isCore.isTrisecting.subset_V
    exact ((hdiv.finite.subset (sep_subset _ _)).image Sum.inl).union (hfin_C.image Sum.inr)
  finite_E := by
    have hdiv := isSocietyDivision_coreDivision hC
    have hfin_C : V(C).Finite := S.finite_V.subset hC.isCore.isTrisecting.subset_V
    have hfin_p : {p : Graph α β × α |
        p.1 ∈ coreDivision S C ∧ (divBoundary S p.1).ncard = 3 ∧ p.2 ∈ divBoundary S p.1}.Finite := by
      refine (hdiv.finite.prod hfin_C).subset ?_
      rintro ⟨A, u⟩ ⟨hA, _, hu⟩
      exact ⟨hA, (boundary_isClique_in_core hC hA).1 hu⟩
    have hfin_A : {A ∈ coreDivision S C | (divBoundary S A).ncard ≤ 1}.Finite :=
      hdiv.finite.subset (sep_subset _ _)
    exact ((hC.isCore.finite_E.image Sum.inl).union ((hfin_p.image Sum.inl).image Sum.inr)).union
      ((hfin_A.image Sum.inr).image Sum.inr)
  bar_subset := by
    rintro _ ⟨v, hv, rfl⟩
    exact Or.inr ⟨v, hC.isCore.isTrisecting.bar_subset hv, rfl⟩

/-! ## Separations of Order `≤ 3` in `auxCoreSociety` -/

/-- In any separation `(G₁, G₂)` of `auxCoreGraph hC hv₀` of order `≤ 3` with
`(liftCyclicPermInr S.Ω).bar ⊆ V(G₂)`, we have `Sum.inr '' V(C) ⊆ V(G₂)`, and for every
`A ∈ coreDivision S C` with `(divBoundary S A).ncard = 3` and `Sum.inl A ∈ V(G₁) \ V(G₂)`,
`Sum.inr '' (divBoundary S A) ⊆ V(G₁) ∩ V(G₂)`. -/
theorem inr_subset_of_separation_le_three {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C))
    {G₁ G₂ : Graph (Graph α β ⊕ α) (AuxCoreEdge α β β')}
    (hsep : IsGraphSeparation (auxCoreGraph hC hv₀) G₁ G₂)
    (hbar : (liftCyclicPermInr S.Ω).bar ⊆ V(G₂))
    (hord : (V(G₁) ∩ V(G₂)).ncard ≤ 3) :
    Sum.inr '' V(C) ⊆ V(G₂) ∧
      ∀ A ∈ coreDivision S C, (divBoundary S A).ncard = 3 →
        Sum.inl A ∈ V(G₁) \ V(G₂) →
        Sum.inr '' (divBoundary S A) ⊆ V(G₁) ∩ V(G₂) := by
  let V₁_C : Set α := {u ∈ V(C) | Sum.inr u ∈ V(G₁)}
  let V₂_C : Set α := {u ∈ V(C) | Sum.inr u ∈ V(G₂)}
  let E₁_C : Set β' := {e ∈ E(C) | (Sum.inl e : AuxCoreEdge α β β') ∈ E(G₁)}
  let E₂_C : Set β' := {e ∈ E(C) | (Sum.inl e : AuxCoreEdge α β β') ∈ E(G₂)}
  let C₁ : Graph α β' := (C.induce V₁_C).restrict E₁_C
  let C₂ : Graph α β' := (C.induce V₂_C).restrict E₂_C
  have hC₁_le : C₁ ≤ C := restrict_le.trans (C.induce_le (sep_subset _ _))
  have hC₂_le : C₂ ≤ C := restrict_le.trans (C.induce_le (sep_subset _ _))
  have hE₁_eq : E(C₁) = E₁_C := by
    change E((C.induce V₁_C).restrict E₁_C) = E₁_C
    rw [edgeSet_restrict, inter_eq_right]
    rintro e ⟨heC, he₁⟩
    obtain ⟨u, w, hlink⟩ := C.exists_isLink_of_mem_edgeSet heC
    have hl_aux : (auxCoreGraph hC hv₀).IsLink (Sum.inl e) (Sum.inr u) (Sum.inr w) :=
      ⟨u, w, hlink, rfl, rfl⟩
    have hl₁ := (hsep.1.isLink_iff he₁).mpr hl_aux
    exact ⟨u, w, hlink, ⟨hlink.left_mem, hl₁.left_mem⟩, ⟨hlink.right_mem, hl₁.right_mem⟩⟩
  have hE₂_eq : E(C₂) = E₂_C := by
    change E((C.induce V₂_C).restrict E₂_C) = E₂_C
    rw [edgeSet_restrict, inter_eq_right]
    rintro e ⟨heC, he₂⟩
    obtain ⟨u, w, hlink⟩ := C.exists_isLink_of_mem_edgeSet heC
    have hl_aux : (auxCoreGraph hC hv₀).IsLink (Sum.inl e) (Sum.inr u) (Sum.inr w) :=
      ⟨u, w, hlink, rfl, rfl⟩
    have hl₂ := (hsep.2.1.isLink_iff he₂).mpr hl_aux
    exact ⟨u, w, hlink, ⟨hlink.left_mem, hl₂.left_mem⟩, ⟨hlink.right_mem, hl₂.right_mem⟩⟩
  have hsep_C : IsGraphSeparation C C₁ C₂ := by
    refine ⟨hC₁_le, hC₂_le, ?_, ?_, ?_⟩
    · refine subset_antisymm (union_subset hC₁_le.vertexSet_mono hC₂_le.vertexSet_mono)
        fun u huC => ?_
      have hu_aux : (Sum.inr u : Graph α β ⊕ α) ∈ V(auxCoreGraph hC hv₀) :=
        Or.inr ⟨u, huC, rfl⟩
      rcases (hsep.2.2.1 ▸ hu_aux : Sum.inr u ∈ V(G₁) ∪ V(G₂)) with hu₁ | hu₂
      · exact Or.inl ⟨huC, hu₁⟩
      · exact Or.inr ⟨huC, hu₂⟩
    · rw [hE₁_eq, hE₂_eq]
      refine subset_antisymm (union_subset (sep_subset _ _) (sep_subset _ _)) fun e heC => ?_
      have he_aux : (Sum.inl e : AuxCoreEdge α β β') ∈ E(auxCoreGraph hC hv₀) :=
        Or.inl (Or.inl ⟨e, heC, rfl⟩)
      rcases (hsep.2.2.2.1 ▸ he_aux : (Sum.inl e : AuxCoreEdge α β β') ∈ E(G₁) ∪ E(G₂)) with
        he₁ | he₂
      · exact Or.inl ⟨heC, he₁⟩
      · exact Or.inr ⟨heC, he₂⟩
    · rw [hE₁_eq, hE₂_eq, disjoint_left]
      intro e he₁ he₂
      exact disjoint_left.mp hsep.2.2.2.2 he₁.2 he₂.2
  have hbar_C₂ : S.Ω.bar ⊆ V(C₂) := fun u hu =>
    ⟨hC.isCore.isTrisecting.bar_subset hu, hbar ⟨u, hu, rfl⟩⟩
  have hfin_G : V(auxCoreGraph hC hv₀).Finite := (auxCoreSociety hC hv₀).finite_V
  have hfin_inter : (V(G₁) ∩ V(G₂)).Finite :=
    hfin_G.subset (inter_subset_left.trans hsep.1.vertexSet_mono)
  have hsub_inter : Sum.inr '' (V(C₁) ∩ V(C₂)) ⊆ V(G₁) ∩ V(G₂) := by
    rintro _ ⟨u, ⟨hu₁, hu₂⟩, rfl⟩
    exact ⟨hu₁.2, hu₂.2⟩
  have hord_C : (V(C₁) ∩ V(C₂)).ncard ≤ 3 := by
    have hcard_img : (Sum.inr '' (V(C₁) ∩ V(C₂)) : Set (Graph α β ⊕ α)).ncard =
        (V(C₁) ∩ V(C₂)).ncard :=
      ncard_image_of_injective _ Sum.inr_injective
    rw [← hcard_img]
    exact (ncard_le_ncard hsub_inter hfin_inter).trans hord
  have hinr_sub : Sum.inr '' V(C) ⊆ V(G₂) := by
    rintro _ ⟨u, huC, rfl⟩
    by_contra hu_not_G₂
    have hu_G₁ : Sum.inr u ∈ V(G₁) := by
      have hu_aux : (Sum.inr u : Graph α β ⊕ α) ∈ V(auxCoreGraph hC hv₀) :=
        Or.inr ⟨u, huC, rfl⟩
      rcases (hsep.2.2.1 ▸ hu_aux : Sum.inr u ∈ V(G₁) ∪ V(G₂)) with h1 | h2
      · exact h1
      · exact (hu_not_G₂ h2).elim
    exact (hC.fourLinked u huC).2 C₁ C₂ hsep_C hord_C hbar_C₂
      ⟨⟨huC, hu_G₁⟩, fun h => hu_not_G₂ h.2⟩
  refine ⟨hinr_sub, fun A hA hcard3 hA_in => ?_⟩
  rintro _ ⟨u, hu_bd, rfl⟩
  have huC : u ∈ V(C) := (boundary_isClique_in_core hC hA).1 hu_bd
  have hu_G₂ : Sum.inr u ∈ V(G₂) := hinr_sub ⟨u, huC, rfl⟩
  refine ⟨?_, hu_G₂⟩
  let c : AuxCoreEdge α β β' := Sum.inr (Sum.inl (A, u))
  have hl_aux : (auxCoreGraph hC hv₀).IsLink c (Sum.inl A) (Sum.inr u) :=
    ⟨hA, hcard3, hu_bd, Or.inl ⟨rfl, rfl⟩⟩
  have hc_mem : c ∈ E(auxCoreGraph hC hv₀) := hl_aux.edge_mem
  rcases (hsep.2.2.2.1 ▸ hc_mem : c ∈ E(G₁) ∪ E(G₂)) with hc₁ | hc₂
  · exact ((hsep.1.isLink_iff hc₁).mpr hl_aux).right_mem
  · exact (hA_in.2 (((hsep.2.1.isLink_iff hc₂).mpr hl_aux).left_mem)).elim

/-- `auxCoreSociety hC hv₀` is 3-connected (`IsKConnected 3`). -/
theorem isKConnected_auxCoreSociety {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C)) :
    (auxCoreSociety hC hv₀).IsKConnected 3 := by
  intro k hk G₁ G₂ ⟨⟨hsep, hbar⟩, hord, hne⟩
  have hord3 : (V(G₁) ∩ V(G₂)).ncard ≤ 3 := by omega
  obtain ⟨hinr_sub, hA_inter⟩ := inr_subset_of_separation_le_three hC hv₀ hsep hbar hord3
  have hV_sub : V(auxCoreGraph hC hv₀) ⊆ V(G₂) := by
    rintro x (⟨A, ⟨hA, hcard3⟩, rfl⟩ | hx_inr)
    · by_contra hA_not_G₂
      have hA_G₁ : Sum.inl A ∈ V(G₁) := by
        have hA_aux : (Sum.inl A : Graph α β ⊕ α) ∈ V(auxCoreGraph hC hv₀) :=
          Or.inl ⟨A, ⟨hA, hcard3⟩, rfl⟩
        rcases (hsep.2.2.1 ▸ hA_aux : Sum.inl A ∈ V(G₁) ∪ V(G₂)) with h1 | h2
        · exact h1
        · exact (hA_not_G₂ h2).elim
      have hsub := hA_inter A hA hcard3 ⟨hA_G₁, hA_not_G₂⟩
      have hfin_G : V(auxCoreGraph hC hv₀).Finite := (auxCoreSociety hC hv₀).finite_V
      have hfin_inter : (V(G₁) ∩ V(G₂)).Finite :=
        hfin_G.subset (inter_subset_left.trans hsep.1.vertexSet_mono)
      have hcard_img : (Sum.inr '' (divBoundary S A) : Set (Graph α β ⊕ α)).ncard = 3 := by
        rw [ncard_image_of_injective _ Sum.inr_injective, hcard3]
      have hle := ncard_le_ncard hsub hfin_inter
      omega
    · exact hinr_sub hx_inr
  exact hne (subset_antisymm hsep.2.1.vertexSet_mono hV_sub)

/-! ## Absence of Crosses and Tripods in `auxCoreSociety` -/

theorem liftCyclicPermInr_isClockwiseSeq {γ : Type*} {Ω : CyclicPerm α} {L : List α}
    (hcw : (liftCyclicPermInr (γ := γ) Ω).IsClockwiseSeq (L.map Sum.inr)) :
    Ω.IsClockwiseSeq L := by
  have hiter : ∀ (n : ℕ) (x : α),
      ((liftCyclicPermInr (γ := γ) Ω).toFun^[n]) (Sum.inr x) = Sum.inr ((Ω.toFun^[n]) x) := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rfl
  obtain ⟨hnodup, hbar, hhit⟩ := hcw
  refine ⟨(List.nodup_map_iff Sum.inr_injective).mp hnodup,
    fun v hv => ?_, fun i hi => ?_⟩
  · obtain ⟨x, hx, h⟩ := hbar (Sum.inr v) (List.mem_map_of_mem hv)
    exact (Sum.inr.inj h) ▸ hx
  · have hi' : i < (L.map (Sum.inr : α → γ ⊕ α)).length := by simp [hi]
    obtain ⟨k, hk_pos, hk_eq, _, hk_min⟩ := hhit i hi'
    simp only [List.length_map, List.getElem_map] at hk_eq hk_min
    refine ⟨k, hk_pos, Sum.inr.inj (by rw [← hiter, hk_eq]), by simp, fun j hj1 hj2 hj_mem => ?_⟩
    apply hk_min j hj1 hj2
    rw [hiter]
    exact List.mem_map_of_mem hj_mem

theorem liftCyclicPermInr_crosses {γ : Type*} {Ω : CyclicPerm α} {p₁ p₂ q₁ q₂ : α}
    (hcr : (liftCyclicPermInr (γ := γ) Ω).Crosses
      (Sum.inr p₁) (Sum.inr p₂) (Sum.inr q₁) (Sum.inr q₂)) :
    Ω.Crosses p₁ p₂ q₁ q₂ :=
  hcr.imp
    (fun h => liftCyclicPermInr_isClockwiseSeq (L := [p₁, q₁, p₂, q₂]) h)
    (fun h => liftCyclicPermInr_isClockwiseSeq (L := [q₂, p₂, q₁, p₁]) h)

/-- Every walk in `auxCoreGraph hC hv₀` ending at `Sum.inr y` shortcuts to a walk in `C` whose
vertices `w` all satisfy `Sum.inr w ∈ W.support` (or equal the starting boundary vertex if the
walk starts at `Sum.inl A`). -/
theorem shortcut_walk_auxCoreGraph {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C))
    {z₁ z₂ : Graph α β ⊕ α} (W : GraphWalk (auxCoreGraph hC hv₀) z₁ z₂) :
    (∀ x y : α, z₁ = Sum.inr x → z₂ = Sum.inr y →
      ∃ W_C : GraphWalk C x y, ∀ w ∈ W_C.support, Sum.inr w ∈ W.support) ∧
    (∀ (A : Graph α β) (y : α), A ∈ coreDivision S C →
      z₁ = Sum.inl A → z₂ = Sum.inr y →
      ∀ x ∈ divBoundary S A,
        ∃ W_C : GraphWalk C x y, ∀ w ∈ W_C.support, w = x ∨ Sum.inr w ∈ W.support) := by
  induction W with
  | @nil z hz =>
    refine ⟨fun x y hx hy => ?_, fun A y _ hA hy => ?_⟩
    · subst hx
      obtain rfl : x = y := Sum.inr.inj hy
      have hxC : x ∈ V(C) := by
        rcases hz with ⟨_, _, h⟩ | ⟨u, huC, h⟩
        · exact nomatch h
        · exact (Sum.inr.inj h) ▸ huC
      refine ⟨.nil hxC, fun w hw => ?_⟩
      simp only [GraphWalk.support_nil, List.mem_singleton] at hw ⊢
      exact congrArg Sum.inr hw
    · exact nomatch (hA.symm.trans hy)
  | @cons z₁ z_mid z₂ c hl rest ih =>
    refine ⟨fun x y hx hy => ?_, fun A y hA_mem hA hy x hx_bd => ?_⟩
    · subst hx
      cases c with
      | inl e =>
        obtain ⟨u, v, hlC, hx_u, hmid_v⟩ := hl
        obtain rfl : x = u := Sum.inr.inj hx_u
        obtain ⟨W_rest, hW_rest⟩ := ih.1 v y hmid_v hy
        refine ⟨.cons hlC W_rest, fun w hw => ?_⟩
        rcases List.mem_cons.mp hw with rfl | hw_rest
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hW_rest w hw_rest)
      | inr c' =>
        cases c' with
        | inl p =>
          obtain ⟨hpA, _, hp_bd, ⟨h1, _⟩ | ⟨hx_p, hmid_A⟩⟩ := hl
          · exact nomatch h1
          · obtain rfl : x = p.2 := Sum.inr.inj hx_p
            obtain ⟨W_rest, hW_rest⟩ := ih.2 p.1 y hpA hmid_A hy p.2 hp_bd
            refine ⟨W_rest, fun w hw => ?_⟩
            rcases hW_rest w hw with rfl | hw_rest
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ hw_rest
        | inr A =>
          obtain ⟨_, _, hx_loop, hmid_loop⟩ := hl
          have hmid_x : z_mid = Sum.inr x := hmid_loop.trans hx_loop.symm
          obtain ⟨W_rest, hW_rest⟩ := ih.1 x y hmid_x hy
          exact ⟨W_rest, fun w hw => List.mem_cons_of_mem _ (hW_rest w hw)⟩
    · subst hA
      cases c with
      | inl e =>
        obtain ⟨_, _, _, h1, _⟩ := hl
        exact nomatch h1
      | inr c' =>
        cases c' with
        | inl p =>
          obtain ⟨hpA, _, hp_bd, ⟨hA_p, hmid_p⟩ | ⟨h1, _⟩⟩ := hl
          · obtain rfl : A = p.1 := Sum.inl.inj hA_p
            obtain ⟨W_rest, hW_rest⟩ := ih.1 p.2 y hmid_p hy
            by_cases hxp : x = p.2
            · subst hxp
              refine ⟨W_rest, fun w hw => Or.inr (List.mem_cons_of_mem _ (hW_rest w hw))⟩
            · obtain ⟨e_C, hlC⟩ :=
                (boundary_isClique_in_core hC hA_mem).2 x hx_bd p.2 hp_bd hxp
              refine ⟨.cons hlC W_rest, fun w hw => ?_⟩
              rcases List.mem_cons.mp hw with rfl | hw_rest
              · exact Or.inl rfl
              · exact Or.inr (List.mem_cons_of_mem _ (hW_rest w hw_rest))
          · exact nomatch h1
        | inr A' =>
          obtain ⟨_, _, h1, _⟩ := hl
          exact nomatch h1

/-- If `S` has no cross and `C` is a 4-linked core of `S`, then `auxCoreSociety hC hv₀` has no
cross. -/
theorem not_hasCross_auxCoreSociety {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C))
    (hnocross : ¬ HasCross S) :
    ¬ ∃ Q₁ Q₂ : Graph (Graph α β ⊕ α) (AuxCoreEdge α β β'),
      (auxCoreSociety hC hv₀).IsCross Q₁ Q₂ := by
  rintro ⟨Q₁, Q₂, hdisj, p₁, p₂, q₁, q₂, hQ₁, hQ₂, hcr⟩
  obtain ⟨a₁, ha₁, rfl⟩ : p₁ ∈ Sum.inr '' S.Ω.bar := hQ₁.2.2.1
  obtain ⟨a₂, ha₂, rfl⟩ : p₂ ∈ Sum.inr '' S.Ω.bar := hQ₁.2.2.2
  obtain ⟨b₁, hb₁, rfl⟩ : q₁ ∈ Sum.inr '' S.Ω.bar := hQ₂.2.2.1
  obtain ⟨b₂, hb₂, rfl⟩ : q₂ ∈ Sum.inr '' S.Ω.bar := hQ₂.2.2.2
  have hcr_S : S.Ω.Crosses a₁ a₂ b₁ b₂ := liftCyclicPermInr_crosses hcr
  obtain ⟨W₁, hW₁_supp⟩ := hQ₁.1.exists_walk_in Subset.rfl
  obtain ⟨W₂, hW₂_supp⟩ := hQ₂.1.exists_walk_in Subset.rfl
  obtain ⟨W_C₁, hWC₁⟩ := (shortcut_walk_auxCoreGraph hC hv₀ W₁).1 a₁ a₂ rfl rfl
  obtain ⟨W_C₂, hWC₂⟩ := (shortcut_walk_auxCoreGraph hC hv₀ W₂).1 b₁ b₂ rfl rfl
  let U₁ : Set α := {w | w ∈ W_C₁.support}
  let U₂ : Set α := {w | w ∈ W_C₂.support}
  have hdisj_U : Disjoint U₁ U₂ := by
    rw [disjoint_left]
    intro w hw₁ hw₂
    exact disjoint_left.mp hdisj
      (hW₁_supp (hWC₁ w hw₁))
      (hW₂_supp (hWC₂ w hw₂))
  have hcross_CS : HasCross (coreSociety S C hC.isCore) :=
    (coreSociety S C hC.isCore).exists_isCross_of_disjoint_walks
      ha₁ ha₂ hb₁ hb₂ hcr_S hdisj_U ⟨W_C₁, Subset.rfl⟩ ⟨W_C₂, Subset.rfl⟩
  exact hnocross ((theorem_8_4_proof hC.isCore).mpr hcross_CS)

/-- If `S` has no cross and `C` is a 4-linked core of `S`, then `auxCoreSociety hC hv₀` has no
tripod. -/
theorem not_exists_isTripod_auxCoreSociety {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C))
    (hnocross : ¬ HasCross S) :
    ¬ ∃ T₁ T₂ T₃ : Graph (Graph α β ⊕ α) (AuxCoreEdge α β β'),
      (auxCoreSociety hC hv₀).IsTripod T₁ T₂ T₃ := by
  rintro ⟨T₁, T₂, T₃, htripod⟩
  rcases GraphMinor.GM09.theorem_2_3_proof (auxCoreSociety hC hv₀) htripod with hcr | ⟨G₁, G₂, hint_sep, _⟩
  · exact not_hasCross_auxCoreSociety hC hv₀ hnocross hcr
  · obtain ⟨⟨⟨hsep, hbar⟩, hord, _⟩, hV₂_add_2⟩ := hint_sep
    obtain ⟨hinr_sub, hA_inter⟩ := inr_subset_of_separation_le_three hC hv₀ hsep hbar hord
    have hdiv := isSocietyDivision_coreDivision hC
    have hfin_G : V(auxCoreGraph hC hv₀).Finite := (auxCoreSociety hC hv₀).finite_V
    have hfin_inter : (V(G₁) ∩ V(G₂)).Finite :=
      hfin_G.subset (inter_subset_left.trans hsep.1.vertexSet_mono)
    have hdiff_sub : (V(auxCoreGraph hC hv₀) \ V(G₂)).Subsingleton := by
      rintro x ⟨hx_G, hx_not_G₂⟩ y ⟨hy_G, hy_not_G₂⟩
      have hx_G₁ : x ∈ V(G₁) :=
        (hsep.2.2.1 ▸ hx_G : x ∈ V(G₁) ∪ V(G₂)).resolve_right hx_not_G₂
      have hy_G₁ : y ∈ V(G₁) :=
        (hsep.2.2.1 ▸ hy_G : y ∈ V(G₁) ∪ V(G₂)).resolve_right hy_not_G₂
      rcases hx_G with ⟨A₁, ⟨hA₁, hcard₁⟩, rfl⟩ | hx_inr
      · rcases hy_G with ⟨A₂, ⟨hA₂, hcard₂⟩, rfl⟩ | hy_inr
        · have hsub₁ := hA_inter A₁ hA₁ hcard₁ ⟨hx_G₁, hx_not_G₂⟩
          have hsub₂ := hA_inter A₂ hA₂ hcard₂ ⟨hy_G₁, hy_not_G₂⟩
          have hcard_img₁ : (Sum.inr '' (divBoundary S A₁) : Set (Graph α β ⊕ α)).ncard = 3 := by
            rw [ncard_image_of_injective _ Sum.inr_injective, hcard₁]
          have hcard_img₂ : (Sum.inr '' (divBoundary S A₂) : Set (Graph α β ⊕ α)).ncard = 3 := by
            rw [ncard_image_of_injective _ Sum.inr_injective, hcard₂]
          have heq₁ : Sum.inr '' (divBoundary S A₁) = V(G₁) ∩ V(G₂) :=
            eq_of_subset_of_ncard_le hsub₁ (by omega) hfin_inter
          have heq₂ : Sum.inr '' (divBoundary S A₂) = V(G₁) ∩ V(G₂) :=
            eq_of_subset_of_ncard_le hsub₂ (by omega) hfin_inter
          have hbd_eq : divBoundary S A₁ = divBoundary S A₂ :=
            Sum.inr_injective.image_injective (heq₁.trans heq₂.symm)
          exact congrArg Sum.inl (hdiv.boundary_injOn hA₁ hA₂ hbd_eq)
        · exact (hy_not_G₂ (hinr_sub hy_inr)).elim
      · exact (hx_not_G₂ (hinr_sub hx_inr)).elim
    have hdiff_le : (V(auxCoreGraph hC hv₀) \ V(G₂)).ncard ≤ 1 := by
      rcases hdiff_sub.eq_empty_or_singleton with h | ⟨z, h⟩ <;> simp [h]
    dsimp [auxCoreSociety] at hsep hV₂_add_2
    have hadd := ncard_sdiff_add_ncard_of_subset hsep.2.1.vertexSet_mono hfin_G
    omega

/-- **Rurality of the auxiliary core society**: if `S` has no cross and `C` is a 4-linked core of
`S` with `v₀ ∈ V(C)`, then `auxCoreSociety hC hv₀` is a rural society. -/
theorem isRuralSociety_auxCoreSociety {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C))
    (hnocross : ¬ HasCross S) :
    (auxCoreSociety hC hv₀).IsRuralSociety :=
  GraphMinor.GM09.theorem_2_4_proof (auxCoreSociety hC hv₀)
    (isKConnected_auxCoreSociety hC hv₀)
    (not_hasCross_auxCoreSociety hC hv₀ hnocross)
    (not_exists_isTripod_auxCoreSociety hC hv₀ hnocross)

end GraphMinor.GM13
