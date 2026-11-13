module

public import GraphMinor.GM22.Section8b3
public import GraphMinor.GM11.Regions

/-!
# Graph Minors XXII, Section 8 (Part b: Claims 5 and 6 of Theorem 8.3)

This file re-exports Claims (1)–(4) from `Section8b1`–`Section8b3` and proves Claims (5) and (6)
of the proof of Theorem (8.3) from:
Robertson and Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
Journal of Combinatorial Theory, Series B 102 (2012), 530–563 (pages 560–561).
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM19

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]

/-! ## Claim (5) of Theorem 8.3 -/

/-- **Claim (5) of Theorem (8.3)** (Graph Minors XXII, Section 8, page 560):
"(5) For each $A \in \mathcal{A}$, $D(A) = ins(\text{bd}(D(A)))$." -/
theorem lemma_8_3_claim_5
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Surface.Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 4 ≤ ord)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀)
    (hbd_Δ₀ : subBd Δ₀ ∩ Γ.U = PiSet)
    {D : Graph α β → Set S}
    (hD : ∀ A ∈ 𝒜, IsClosedDisc (D A) ∧ D A ⊆ Δ₀)
    (hD_norm : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.U ⊆ Γ.V)
    (hD_bdV : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)}) :
    ∀ A ∈ 𝒜,
      IsTangleIns Γ T (subBd (D A)) (D A) ∧
      ∀ Δ : Set S, IsTangleIns Γ T (subBd (D A)) Δ → Δ = D A := by
  intro A hA
  obtain ⟨hS_closed, _⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  let F : Set S := subBd (D A)
  have hF_eq_discBd : F = discBd (D A) :=
    GM14.IsClosedDisc.subBd_eq_discBd hS_closed (hD A hA).1
  have hF_oarc : IsOArc F := hF_eq_discBd ▸ (hD A hA).1.isOArc_discBd
  have hF_sub_Δ₀ : F ⊆ Δ₀ :=
    (GM14.Whitney.subBd_subset_of subset_rfl (hD A hA).1.isClosed).trans (hD A hA).2
  have hFV_sub_pre : F ∩ Γ.V ⊆ ιV ⁻¹' Set.range (πA A) := by
    rw [hD_bdV A hA]
    exact fun _ hv => hv.2
  have hFV_card_le : (F ∩ Γ.V).ncard ≤ 3 := by
    have hsub_img : ιV '' (F ∩ Γ.V) ⊆ Set.range (πA A) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hFV_sub_pre hv
    have h1 : (F ∩ Γ.V).ncard = (ιV '' (F ∩ Γ.V)).ncard :=
      (Set.ncard_image_of_injective (F ∩ Γ.V) ιV.injective).symm
    have h2 : (ιV '' (F ∩ Γ.V)).ncard ≤ (Set.range (πA A)).ncard :=
      Set.ncard_le_ncard hsub_img (Set.finite_range (πA A))
    have h3 : (Set.range (πA A)).ncard ≤ πLen A :=
      (Set.image_univ.symm ▸ Set.ncard_image_le finite_univ).trans (by simp)
    have h4 : πLen A ≤ 3 := (h83.hyp_vii A hA).1
    omega
  have hFV_lt_ord : (F ∩ Γ.V).ncard < ord := by omega
  obtain ⟨Δ₁, Δ₂, _, _, _, _, _, _, _, _, hcap, _, hcl21, _, hbd₀_Δ₂, h_either, h_uniq₁⟩ :=
    sphere_oArc_discs_in_Δ₀ h83.hyp_i.1 hΔ₀ hF_sub_Δ₀ hF_oarc
  have hΔ₁_eq : Δ₁ = D A := (h_uniq₁ (D A) (hD A hA).2 (hD A hA).1 rfl).symm
  subst hΔ₁_eq
  -- Show `¬ IsTangleIns Γ T F Δ₂` using hypothesis (iv).
  have h_not_ins₂ : ¬ IsTangleIns Γ T F Δ₂ := by
    rintro ⟨_, _, hmem_T⟩
    let A_hyp := (PaintingOrDrawing.drawing Γ).inter Δ₂
    let B_hyp := (PaintingOrDrawing.drawing Γ).interOutside Δ₂
    have hA_V : A_hyp.vertexSet = Γ.V ∩ Δ₂ := rfl
    have hB_V : B_hyp.vertexSet = Γ.V ∩ closure (univ \ Δ₂) := rfl
    have hinter_V : A_hyp.vertexSet ∩ B_hyp.vertexSet = F ∩ Γ.V := by
      rw [hA_V, hB_V, hcl21]
      ext v
      simp only [mem_inter_iff]
      have hcap' : D A ∩ Δ₂ = F := hcap
      constructor
      · rintro ⟨⟨hvV, hv₂⟩, ⟨_, hv₁⟩⟩
        exact ⟨hcap' ▸ ⟨hv₁, hv₂⟩, hvV⟩
      · rintro ⟨hvF, hvV⟩
        have hv₁₂ : v ∈ D A ∩ Δ₂ := hcap'.symm ▸ hvF
        exact ⟨⟨hvV, hv₁₂.2⟩, ⟨hvV, hv₁₂.1⟩⟩
    have hord_AB : separationOrder A_hyp B_hyp ≤ 3 := by
      change (A_hyp.vertexSet ∩ B_hyp.vertexSet).ncard ≤ 3
      rw [hinter_V]
      exact hFV_card_le
    have hPi_sub_A : PiSet ⊆ A_hyp.vertexSet := by
      intro p hp
      have hpV : p ∈ Γ.V := h83.hyp_ii.1.1 (h83.hyp_iii.1 hp)
      have hp_bd₀ : p ∈ subBd Δ₀ := (hbd_Δ₀.symm ▸ hp).1
      exact ⟨hpV, hbd₀_Δ₂ hp_bd₀⟩
    exact h83.hyp_iv.2.2 A_hyp B_hyp hmem_T hord_AB hPi_sub_A
  -- By respectfulness of `T`, some `Δ` satisfies `IsTangleIns Γ T F Δ`.
  have h_resp := h83.hyp_iv.2.1.1.2.2.2 F hF_oarc (hD_norm A hA) hFV_lt_ord
  obtain ⟨Δ_ins, hΔ_ins⟩ := h_resp
  have h_uniq_all : ∀ Δ : Set S, IsTangleIns Γ T F Δ → Δ = D A := by
    intro Δ hΔ
    rcases h_either Δ hΔ.1 hΔ.2.1 with h1 | h2
    · exact h1
    · exact False.elim (h_not_ins₂ (h2 ▸ hΔ))
  have hDA_ins : IsTangleIns Γ T F (D A) := h_uniq_all Δ_ins hΔ_ins ▸ hΔ_ins
  exact ⟨hDA_ins, h_uniq_all⟩

/-! ## Helper Lemmas for Claim (6) of Theorem 8.3 -/

/-- If `C ⊆ D` is an `O`-arc, `v ∈ C ∩ Γ.V`, and `C ∩ Γ.U` is finite, then there exists a region
`r ∈ Γ.R` such that `v ∈ subBd r` and `(r ∩ D).Nonempty`. -/
theorem exists_region_incident_of_mem_oArc_of_finite
    (hS : IsClosedSurface S) {Γ : Surface.Drawing S} {D C : Set S} {v : S}
    (hCD : C ⊆ D) (hC : IsOArc C) (hvC : v ∈ C) (hvV : v ∈ Γ.V) (hfin : (C ∩ Γ.U).Finite) :
    ∃ r ∈ Γ.R, v ∈ subBd r ∧ (r ∩ D).Nonempty := by
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  have ⟨φ⟩ := hC
  let u₀ : Circle := φ.symm ⟨v, hvC⟩
  have hu₀ : (φ u₀).1 = v := by simp [u₀]
  have hne : (-u₀ : Circle) ≠ u₀ := by
    intro h
    have h1 : (-u₀ : ℂ) = (u₀ : ℂ) := congrArg Subtype.val h
    have h2 : (u₀ : ℂ) = 0 := by linear_combination -h1 / 2
    have h3 : ‖(u₀ : ℂ)‖ = 1 := Circle.norm_coe u₀
    simp [h2] at h3
  let y : S := (φ (-u₀)).1
  have hyC : y ∈ C := (φ (-u₀)).2
  have hvy : v ≠ y := fun h => hne (φ.injective (Subtype.ext (hu₀.trans h |>.symm)))
  obtain ⟨L, _, hL, _, hL_union, _⟩ := IsOArc.lines hC hvC hyC hvy
  have hL_sub_C : L ⊆ C := hL_union ▸ subset_union_left
  obtain ⟨f, hf0, _⟩ := hL
  let g : unitInterval → S := fun t => (f t).1
  have hg_cont : Continuous g := continuous_subtype_val.comp f.continuous
  let F_bad : Set S := (C ∩ Γ.U) \ {v}
  have hF_closed : IsClosed F_bad := (hfin.sdiff).isClosed
  have h0_open : IsOpen (g ⁻¹' F_badᶜ) := hF_closed.isOpen_compl.preimage hg_cont
  have h0_mem : (0 : unitInterval) ∈ g ⁻¹' F_badᶜ := by
    change (f 0).1 ∉ (C ∩ Γ.U) \ {v}
    rw [hf0]
    exact fun h => h.2 rfl
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp h0_open 0 h0_mem
  let ε_val : ℝ := min (δ / 2) (1 / 2)
  have hε_pos : 0 < ε_val := lt_min (half_pos hδ_pos) (by norm_num)
  have hε_le : ε_val ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let ε : unitInterval := ⟨ε_val, le_of_lt hε_pos, hε_le⟩
  have hε_gt0 : (0 : unitInterval) < ε := hε_pos
  let A₀ : Set S := g '' Ioc (0 : unitInterval) ε
  have hA₀_sub_C : A₀ ⊆ C := by
    rintro _ ⟨t, _, rfl⟩
    exact hL_sub_C (f t).2
  have hA₀_disj_U : Disjoint A₀ Γ.U := by
    rw [disjoint_left]
    rintro _ ⟨t, ⟨ht0, htε⟩, rfl⟩ hxU
    have ht_ball : t ∈ Metric.ball (0 : unitInterval) δ := by
      rw [Metric.mem_ball, Subtype.dist_eq, Icc.coe_zero, Real.dist_0_eq_abs,
        abs_of_pos ht0]
      have h1 : (t : ℝ) ≤ δ / 2 := (Subtype.coe_le_coe.mpr htε).trans (min_le_left _ _)
      linarith
    have hnot_bad : g t ∉ F_bad := hball ht_ball
    have hne_v : g t ≠ v := by
      intro heq
      have ht_eq : t = 0 := f.injective (Subtype.ext (heq.trans hf0.symm))
      exact (ne_of_gt ht0) ht_eq
    exact hnot_bad ⟨⟨hA₀_sub_C ⟨t, ⟨ht0, htε⟩, rfl⟩, hxU⟩, hne_v⟩
  have hA₀_pre : IsPreconnected A₀ := isPreconnected_Ioc.image g hg_cont.continuousOn
  have hgε_A₀ : g ε ∈ A₀ := ⟨ε, ⟨hε_gt0, le_rfl⟩, rfl⟩
  have hgε_notU : g ε ∉ Γ.U := disjoint_left.mp hA₀_disj_U hgε_A₀
  obtain ⟨r, hr, hgε_r⟩ := GM11.exists_region_of_notMem hgε_notU
  have hA₀_sub_r : A₀ ⊆ r := GM11.subset_region hr hA₀_pre hA₀_disj_U hgε_A₀ hgε_r
  have hv_cl_A₀ : v ∈ closure A₀ := by
    have h0_cl : (0 : unitInterval) ∈ closure (Ioc (0 : unitInterval) ε) := by
      rw [closure_Ioc (ne_of_lt hε_gt0)]
      exact left_mem_Icc.mpr (le_of_lt hε_gt0)
    have hmem : g 0 ∈ closure A₀ := map_mem_closure hg_cont h0_cl (fun t ht => ⟨t, ht, rfl⟩)
    exact hf0 ▸ hmem
  have hv_cl_r : v ∈ closure r := closure_mono hA₀_sub_r hv_cl_A₀
  have hv_not_r : v ∉ r := fun hvr => GM11.region_subset hr hvr (Γ.V_subset_U hvV)
  have hv_subBd : v ∈ subBd r := by
    rw [GM11.subBd_eq_frontier, frontier, (GM11.region_isOpen hr).interior_eq]
    exact ⟨hv_cl_r, hv_not_r⟩
  exact ⟨r, hr, hv_subBd, ⟨g ε, hA₀_sub_r hgε_A₀, hCD (hA₀_sub_C hgε_A₀)⟩⟩

/-- Under `h83.hyp_v`, any simple walk in `G \ W` from `v ∈ V(J) \ W` to `u ∈ V(J) \ W` whose
support contains no vertex of `ιV '' C₀.V` except possibly `v` lies in `J \ W`. -/
theorem exists_walk_in_J_deleteVerts_W
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Surface.Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    {v u : α} (W₀ : GraphWalk (R_G.G.toGraph.deleteVerts W) v u) (hs₀ : W₀.IsSimple)
    (hvJ : v ∈ V(J) \ W) (huJ : u ∈ V(J) \ W)
    (hno_C₀ : ∀ y ∈ W₀.support, y ≠ v → y ∉ ιV '' C₀.V) :
    ∃ W_J : GraphWalk (J.deleteVerts W) v u, W_J.support = W₀.support := by
  let G := R_G.G.toGraph
  let X₀ := (ιV '' C₀.V) ∪ W
  let G' := G.deleteVerts X₀
  have hVJ_eq : V(J) = W ∪ (ιV '' Γ.V) ∪
      ⋃ C ∈ {C ∈ graphComponents G' | (V(C) ∩ (ιV '' Γ.V)).Nonempty}, V(C) := by
    have h := congrArg Graph.vertexSet h83.hyp_v.2
    rwa [vertexSet_induce] at h
  -- Any link in `G'` with right endpoint in `V(J)` has left endpoint in `V(J)`.
  have hstep_G' : ∀ {e x y}, G'.IsLink e x y → y ∈ V(J) → x ∈ V(J) := by
    intro e x y hlk hyJ
    have hyG' : y ∈ V(G') := hlk.right_mem
    have hy_del : y ∈ V(G) \ X₀ := by
      rw [← vertexSet_deleteVerts]
      exact hyG'
    have hy_not_W : y ∉ W := fun hW => hy_del.2 (Or.inr hW)
    let C := compOf G' y
    have hC_comp : C ∈ graphComponents G' := isGraphComponent_compOf hyG'
    have hyC : y ∈ V(C) := self_mem_reachSet hyG'
    have hxC : x ∈ V(C) := (hC_comp.mem_iff_of_isLink hlk).mpr hyC
    have hy_cases : y ∈ (ιV '' Γ.V) ∨
        ∃ C' ∈ graphComponents G', (V(C') ∩ (ιV '' Γ.V)).Nonempty ∧ y ∈ V(C') := by
      have hyJ' := hVJ_eq ▸ hyJ
      rcases hyJ' with (hyW | hyΓ) | hyU
      · exact False.elim (hy_not_W hyW)
      · exact Or.inl hyΓ
      · obtain ⟨C', ⟨hC'_comp, hC'_ne⟩, hyC'⟩ := mem_iUnion₂.mp hyU
        exact Or.inr ⟨C', hC'_comp, hC'_ne, hyC'⟩
    have hC_ne : (V(C) ∩ (ιV '' Γ.V)).Nonempty := by
      rcases hy_cases with hyΓ | ⟨C', hC'_comp, hC'_ne, hyC'⟩
      · exact ⟨y, hyC, hyΓ⟩
      · have hCC' : C = C' := hC_comp.eq_of_mem_mem hC'_comp hyC hyC'
        exact hCC' ▸ hC'_ne
    rw [hVJ_eq]
    exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC_comp, hC_ne⟩, hxC⟩)
  -- Any walk in `G \ W` ending at `u' ∈ V(J) \ W` that avoids `ιV '' C₀.V` entirely lies in `V(J) \ W`.
  have hwalk_avoid_C₀ : ∀ {z u' : α} (W_sub : GraphWalk (G.deleteVerts W) z u'),
      u' ∈ V(J) \ W → (∀ y ∈ W_sub.support, y ∉ ιV '' C₀.V) →
      ∀ y ∈ W_sub.support, y ∈ V(J) \ W := by
    intro z u' W_sub hu'J havoid
    induction W_sub with
    | nil _ =>
      intro y hy
      simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at hy
      exact hy ▸ hu'J
    | @cons a b c e hlk rest ih =>
      have hrest_avoid : ∀ y ∈ rest.support, y ∉ ιV '' C₀.V :=
        fun y hy => havoid y (List.mem_cons_of_mem a hy)
      have hrest_J := ih hu'J hrest_avoid
      have hbJ : b ∈ V(J) \ W := hrest_J b rest.start_mem_support
      have ha_not_C₀ : a ∉ ιV '' C₀.V := havoid a List.mem_cons_self
      have hb_not_C₀ : b ∉ ιV '' C₀.V := hrest_avoid b rest.start_mem_support
      have hlk_G : G.IsLink e a b := hlk.mono Graph.deleteVerts_le
      have ha_del : a ∈ V(G) \ W := by
        rw [← vertexSet_deleteVerts]
        exact hlk.left_mem
      have ha_not_W : a ∉ W := ha_del.2
      have hlk_G' : G'.IsLink e a b := by
        rw [deleteVerts_isLink]
        exact ⟨hlk_G, fun h => h.elim ha_not_C₀ ha_not_W, fun h => h.elim hb_not_C₀ hbJ.2⟩
      have haJ : a ∈ V(J) := hstep_G' hlk_G' hbJ.1
      intro y hy
      simp only [GraphWalk.support, List.mem_cons] at hy
      rcases hy with rfl | hy'
      · exact ⟨haJ, ha_not_W⟩
      · exact hrest_J y hy'
  have hall_J : ∀ y ∈ W₀.support, y ∈ V(J) \ W := by
    rcases W₀ with _ | ⟨hlk, rest⟩
    · intro y hy
      simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at hy
      exact hy ▸ hvJ
    · rename_i b e
      have ha_not_rest : v ∉ rest.support := (List.nodup_cons.mp hs₀).1
      have hrest_avoid : ∀ y ∈ rest.support, y ∉ ιV '' C₀.V :=
        fun y hy => hno_C₀ y (List.mem_cons_of_mem v hy) (fun hya => ha_not_rest (hya ▸ hy))
      have hrest_J := hwalk_avoid_C₀ rest huJ hrest_avoid
      intro y hy
      simp only [GraphWalk.support, List.mem_cons] at hy
      rcases hy with rfl | hy'
      · exact hvJ
      · exact hrest_J y hy'
  -- Transfer `W₀` to `J.deleteVerts W` since `J` is an induced subgraph of `G`.
  have htransfer : ∀ {x y : α} (W_sub : GraphWalk (G.deleteVerts W) x y),
      (∀ z ∈ W_sub.support, z ∈ V(J) \ W) →
      ∃ W_J : GraphWalk (J.deleteVerts W) x y, W_J.support = W_sub.support := by
    intro x y W_sub hsub
    induction W_sub with
    | @nil u_nil _ =>
      have hx : u_nil ∈ V(J.deleteVerts W) := by
        rw [vertexSet_deleteVerts]
        exact hsub u_nil (by simp [GraphWalk.support])
      exact ⟨.nil hx, rfl⟩
    | @cons a b c e hlk rest ih =>
      obtain ⟨W_rest, hsupp_rest⟩ := ih (fun z hz => hsub z (List.mem_cons_of_mem a hz))
      have ha : a ∈ V(J) \ W := hsub a List.mem_cons_self
      have hb : b ∈ V(J) \ W := hsub b (List.mem_cons_of_mem a rest.start_mem_support)
      have hlk' := hlk
      rw [deleteVerts_isLink] at hlk'
      obtain ⟨hlk_G, haW, hbW⟩ := hlk'
      have haJ : a ∈ V(J) := ha.1
      have hbJ : b ∈ V(J) := hb.1
      have hlk_J : J.IsLink e a b := by
        rw [h83.hyp_v.2] at haJ hbJ ⊢
        rw [vertexSet_induce] at haJ hbJ
        rw [induce_isLink]
        exact ⟨hlk_G, haJ, hbJ⟩
      have hlk_JW : (J.deleteVerts W).IsLink e a b := by
        rw [deleteVerts_isLink]
        exact ⟨hlk_J, haW, hbW⟩
      exact ⟨.cons hlk_JW W_rest, by simp [GraphWalk.support, hsupp_rest]⟩
  exact htransfer W₀ hall_J

/-- For `B' ∈ 𝒜` and distinct `z₁, z₂ ∈ Set.range (πA B')` with `α_map z₁ ∈ r` (`r ∈ Γ.R`),
there is an arc of `subBd (D B')` between `α_map z₁` and `α_map z₂` avoiding `Γ.U \ {α_map z₂}`,
so `α_map z₂ ∈ r` if `α_map z₂ ∉ Γ.U` and `α_map z₂ ∈ subBd r` if `α_map z₂ ∈ Γ.U`. -/
theorem step_region_along_bd_of_piece
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Surface.Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    {α_map : α → S} {D : Graph α β → Set S}
    (hα_ΓV : ∀ v ∈ Γ.V, ιV v ∈ Z → α_map (ιV v) = v)
    (hinj : InjOn α_map Z)
    (hD : ∀ A ∈ 𝒜, IsClosedDisc (D A))
    (hα_bdA : ∀ A ∈ 𝒜, ∀ v ∈ Set.range (πA A), α_map v ∈ subBd (D A))
    (hD_bdU : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.U = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)})
    {B' : Graph α β} (hB' : B' ∈ 𝒜)
    {z₁ z₂ : α} (hz₁ : z₁ ∈ Set.range (πA B')) (hz₂ : z₂ ∈ Set.range (πA B')) (hz₁₂ : z₁ ≠ z₂)
    {r : Set S} (hr : r ∈ Γ.R) (hz₁_r : α_map z₁ ∈ r) :
    α_map z₂ ∈ closure r ∧ (α_map z₂ ∉ Γ.U → α_map z₂ ∈ r) ∧
      (α_map z₂ ∈ Γ.U → α_map z₂ ∈ subBd r) := by
  obtain ⟨hS_closed, _⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS_closed
  have hπ_eq_Z : Set.range (πA B') = Z ∩ V(B') := (h83.hyp_vii B' hB').2.2
  have hz₁_Z : z₁ ∈ Z := (hπ_eq_Z ▸ hz₁).1
  have hz₂_Z : z₂ ∈ Z := (hπ_eq_Z ▸ hz₂).1
  have hα₁₂ : α_map z₁ ≠ α_map z₂ := fun h => hz₁₂ (hinj hz₁_Z hz₂_Z h)
  have hbd_eq : subBd (D B') = discBd (D B') :=
    GM14.IsClosedDisc.subBd_eq_discBd hS_closed (hD B' hB')
  have hz₁_bd : α_map z₁ ∈ discBd (D B') := hbd_eq ▸ hα_bdA B' hB' z₁ hz₁
  have hz₂_bd : α_map z₂ ∈ discBd (D B') := hbd_eq ▸ hα_bdA B' hB' z₂ hz₂
  have hz₁_notU : α_map z₁ ∉ Γ.U := GM11.region_subset hr hz₁_r
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hJ_union, hJ_inter⟩ :=
    (hD B' hB').isOArc_discBd.lines hz₁_bd hz₂_bd hα₁₂
  -- At least one of `J₁, J₂` meets `Γ.U` only inside `{α_map z₂}` (by pigeonhole on `πLen B' ≤ 3`).
  have hex_J' : ∃ J' : Set S,
      IsLineWithEnds J' (α_map z₁) (α_map z₂) ∧ J' ⊆ discBd (D B') ∧ J' ∩ Γ.U ⊆ {α_map z₂} := by
    by_cases h1 : J₁ ∩ Γ.U ⊆ {α_map z₂}
    · exact ⟨J₁, hJ₁, hJ_union ▸ subset_union_left, h1⟩
    · refine ⟨J₂, hJ₂, hJ_union ▸ subset_union_right, ?_⟩
      by_contra h2
      obtain ⟨p₁, ⟨hp₁_J₁, hp₁_U⟩, hp₁_ne₂⟩ := not_subset.mp h1
      obtain ⟨p₂, ⟨hp₂_J₂, hp₂_U⟩, hp₂_ne₂⟩ := not_subset.mp h2
      rw [mem_singleton_iff] at hp₁_ne₂ hp₂_ne₂
      change p₁ ≠ α_map z₂ at hp₁_ne₂
      change p₂ ≠ α_map z₂ at hp₂_ne₂
      have hp₁_ne₁ : p₁ ≠ α_map z₁ := fun h => hz₁_notU (h ▸ hp₁_U)
      have hp₂_ne₁ : p₂ ≠ α_map z₁ := fun h => hz₁_notU (h ▸ hp₂_U)
      have hp₁_ne_p₂ : p₁ ≠ p₂ := fun h => by
        have hp₁_inter : p₁ ∈ J₁ ∩ J₂ := ⟨hp₁_J₁, h ▸ hp₂_J₂⟩
        rw [hJ_inter] at hp₁_inter
        exact hp₁_inter.elim hp₁_ne₁ hp₁_ne₂
      have hp₁_bdU : p₁ ∈ subBd (D B') ∩ Γ.U :=
        ⟨hbd_eq.symm ▸ (hJ_union ▸ Or.inl hp₁_J₁), hp₁_U⟩
      have hp₂_bdU : p₂ ∈ subBd (D B') ∩ Γ.U :=
        ⟨hbd_eq.symm ▸ (hJ_union ▸ Or.inr hp₂_J₂), hp₂_U⟩
      rw [hD_bdU B' hB'] at hp₁_bdU hp₂_bdU
      have hp₁_α : α_map (ιV p₁) = p₁ := hα_ΓV p₁ hp₁_bdU.1 (hπ_eq_Z ▸ hp₁_bdU.2).1
      have hp₂_α : α_map (ιV p₂) = p₂ := hα_ΓV p₂ hp₂_bdU.1 (hπ_eq_Z ▸ hp₂_bdU.2).1
      obtain ⟨a₁, ha₁⟩ := hz₁
      obtain ⟨a₂, ha₂⟩ := hz₂
      obtain ⟨b₁, hb₁⟩ := hp₁_bdU.2
      obtain ⟨b₂, hb₂⟩ := hp₂_bdU.2
      have ha₁₂ : a₁.1 ≠ a₂.1 := fun h => hz₁₂ (ha₁.symm.trans (congrArg (πA B') (Fin.ext h) |>.trans ha₂))
      have hb₁₂ : b₁.1 ≠ b₂.1 := fun h => hp₁_ne_p₂ (by rw [← hp₁_α, ← hp₂_α, ← hb₁, ← hb₂, Fin.ext h])
      have hab₁₁ : a₁.1 ≠ b₁.1 := fun h => hp₁_ne₁.symm (by rw [← hp₁_α, ← hb₁, ← ha₁, Fin.ext h])
      have hab₁₂ : a₁.1 ≠ b₂.1 := fun h => hp₂_ne₁.symm (by rw [← hp₂_α, ← hb₂, ← ha₁, Fin.ext h])
      have hab₂₁ : a₂.1 ≠ b₁.1 := fun h => hp₁_ne₂.symm (by rw [← hp₁_α, ← hb₁, ← ha₂, Fin.ext h])
      have hab₂₂ : a₂.1 ≠ b₂.1 := fun h => hp₂_ne₂.symm (by rw [← hp₂_α, ← hb₂, ← ha₂, Fin.ext h])
      have hlen_le : πLen B' ≤ 3 := (h83.hyp_vii B' hB').1
      have := a₁.2; have := a₂.2; have := b₁.2; have := b₂.2
      omega
  obtain ⟨J', hJ'_line, _, hJ'_U⟩ := hex_J'
  have hJ'_symm : IsLineWithEnds J' (α_map z₂) (α_map z₁) := GM11.IsLineWithEnds.symm hJ'_line
  have hJ'_pre : IsPreconnected (J' \ {α_map z₂}) := GM11.IsLineWithEnds.isPreconnected_sdiff hJ'_symm
  have hJ'_disj : Disjoint (J' \ {α_map z₂}) Γ.U := by
    rw [disjoint_left]
    intro x ⟨hxJ', hx_ne⟩ hxU
    exact hx_ne (hJ'_U ⟨hxJ', hxU⟩)
  have hz₁_mem : α_map z₁ ∈ J' \ {α_map z₂} :=
    ⟨GM11.IsLineWithEnds.left_mem hJ'_line, hα₁₂⟩
  have hJ'_sub_r : J' \ {α_map z₂} ⊆ r :=
    GM11.subset_region hr hJ'_pre hJ'_disj hz₁_mem hz₁_r
  have hz₂_cl : α_map z₂ ∈ closure r :=
    closure_mono hJ'_sub_r (GM11.IsLineWithEnds.mem_closure_sdiff hJ'_symm)
  refine ⟨hz₂_cl, ?_, ?_⟩
  · intro hz₂_notU
    exact (GM11.closure_region_subset hr hz₂_cl).resolve_right hz₂_notU
  · intro hz₂_U
    have hz₂_not_r : α_map z₂ ∉ r := fun h => GM11.region_subset hr h hz₂_U
    rw [GM11.subBd_eq_frontier, frontier, (GM11.region_isOpen hr).interior_eq]
    exact ⟨hz₂_cl, hz₂_not_r⟩

/-- If `B' ∈ 𝒜`, `z₁ ∈ Set.range (πA B')` with `α_map z₁ ∈ r` (`r ∈ Γ.R`), and
`v ∈ (Γ.interSet (D B')).V \ subBd (D B')`, then `v ∈ subBd r`. -/
theorem incident_of_rigid_disc_piece
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Surface.Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 4 ≤ ord)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀)
    (hbd_Δ₀ : subBd Δ₀ ∩ Γ.U = PiSet)
    {α_map : α → S} {D : Graph α β → Set S}
    (hα_ΓU : ∀ v ∈ Z, α_map v ∈ Γ.U ↔ v ∈ ιV '' Γ.V)
    (hD : ∀ A ∈ 𝒜, IsClosedDisc (D A) ∧ D A ⊆ Δ₀)
    (hD_norm : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.U ⊆ Γ.V)
    (hα_bdA : ∀ A ∈ 𝒜, ∀ v ∈ Set.range (πA A), α_map v ∈ subBd (D A))
    (hD_bdV : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)})
    {B' : Graph α β} (hB' : B' ∈ 𝒜)
    {z₁ : α} (hz₁ : z₁ ∈ Set.range (πA B'))
    {r : Set S} (hr : r ∈ Γ.R) (hz₁_r : α_map z₁ ∈ r)
    {v : S} (hv : v ∈ (Γ.interSet (D B')).V \ subBd (D B')) :
    v ∈ subBd r := by
  obtain ⟨hS_closed, _⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS_closed
  have hπ_eq_Z : Set.range (πA B') = Z ∩ V(B') := (h83.hyp_vii B' hB').2.2
  have hz₁_Z : z₁ ∈ Z := (hπ_eq_Z ▸ hz₁).1
  have hz₁_notU : α_map z₁ ∉ Γ.U := GM11.region_subset hr hz₁_r
  have hz₁_not_ΓV : z₁ ∉ ιV '' Γ.V := fun h => hz₁_notU ((hα_ΓU z₁ hz₁_Z).mpr h)
  let F : Set S := subBd (D B')
  have hF_eq_discBd : F = discBd (D B') :=
    GM14.IsClosedDisc.subBd_eq_discBd hS_closed (hD B' hB').1
  have hF_oarc : IsOArc F := hF_eq_discBd ▸ (hD B' hB').1.isOArc_discBd
  have hF_sub_Δ₀ : F ⊆ Δ₀ :=
    (GM14.Whitney.subBd_subset_of subset_rfl (hD B' hB').1.isClosed).trans (hD B' hB').2
  -- Show `(F ∩ Γ.V).ncard ≤ 2` since `z₁ ∈ Set.range (πA B') \ (ιV '' Γ.V)`.
  have hFV_card : (F ∩ Γ.V).ncard ≤ 2 := by
    have hsub_diff : ιV '' (F ∩ Γ.V) ⊆ Set.range (πA B') \ {z₁} := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' : w ∈ {v ∈ Γ.V | ιV v ∈ Set.range (πA B')} := hD_bdV B' hB' ▸ hw
      refine ⟨hw'.2, fun heq => hz₁_not_ΓV (heq ▸ ⟨w, hw'.1, rfl⟩)⟩
    have h1 : (F ∩ Γ.V).ncard = (ιV '' (F ∩ Γ.V)).ncard :=
      (Set.ncard_image_of_injective (F ∩ Γ.V) ιV.injective).symm
    have h2 : (ιV '' (F ∩ Γ.V)).ncard ≤ (Set.range (πA B') \ {z₁}).ncard :=
      Set.ncard_le_ncard hsub_diff ((Set.finite_range (πA B')).sdiff)
    have h3 : (Set.range (πA B') \ {z₁}).ncard + 1 = (Set.range (πA B')).ncard :=
      Set.ncard_sdiff_singleton_add_one hz₁ (Set.finite_range (πA B'))
    have h4 : (Set.range (πA B')).ncard ≤ πLen B' :=
      (Set.image_univ.symm ▸ Set.ncard_image_le finite_univ).trans (by simp)
    have h5 : πLen B' ≤ 3 := (h83.hyp_vii B' hB').1
    omega
  have hPi_bd : PiSet ⊆ subBd Δ₀ := fun p hp => (hbd_Δ₀.symm ▸ hp).1
  have hRigid := isRigidIn_Δ₀_8_3 h83 hord hΔ₀ hPi_bd F hF_sub_Δ₀ hF_oarc (hD_norm B' hB') hFV_card
  obtain ⟨Δ₁, hΔ₁_sub, hΔ₁_disc, hΔ₁_bd, hRigid_cases⟩ := hRigid
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_uniq₁⟩ :=
    sphere_oArc_discs_in_Δ₀ h83.hyp_i.1 hΔ₀ hF_sub_Δ₀ hF_oarc
  have hΔ₁_eq : Δ₁ = D B' :=
    (h_uniq₁ Δ₁ hΔ₁_sub hΔ₁_disc hΔ₁_bd).trans
      (h_uniq₁ (D B') (hD B' hB').2 (hD B' hB').1 rfl).symm
  subst hΔ₁_eq
  let H := Γ.interSet (D B')
  obtain ⟨hH_V, hH_U⟩ := interSet_V_and_U (hD B' hB').1.isClosed (hD_norm B' hB')
  rcases hRigid_cases with hU_sub_F | ⟨x, y, hxy, hFV_eq, W_P, hs_P, hVP, hEP⟩
  · have hv_VD : v ∈ Γ.V ∩ D B' := hH_V ▸ hv.1
    exact False.elim (hv.2 (hU_sub_F ⟨hv_VD.2, Γ.V_subset_U hv_VD.1⟩))
  · let P_draw := GM11.walkDrawing H W_P
    have hP_path : P_draw.IsPathBetween x y := GM11.walkDrawing_isPathBetween H hs_P
    have hP_line : IsLineWithEnds P_draw.U x y := GM11.isLine_of_isPathBetween hP_path hxy
    have hPU_eq_HU : P_draw.U = H.U := by
      rw [P_draw.U_eq, H.U_eq, GM11.walkDrawing_V, GM11.walkDrawing_E, ← hVP, ← hEP]
    have hHU_line : IsLineWithEnds H.U x y := hPU_eq_HU ▸ hP_line
    have hHU_sub : H.U ⊆ D B' := hH_U ▸ inter_subset_right
    have hHU_bd : H.U ∩ discBd (D B') = {x, y} := by
      rw [← hF_eq_discBd, hH_U]
      have : (Γ.U ∩ D B') ∩ F = F ∩ Γ.U := by
        have hF_sub : F ⊆ D B' := GM14.Whitney.subBd_subset_of subset_rfl (hD B' hB').1.isClosed
        ext w
        simp only [mem_inter_iff]
        exact ⟨fun ⟨⟨hwU, _⟩, hwF⟩ => ⟨hwF, hwU⟩, fun ⟨hwF, hwU⟩ => ⟨⟨hwU, hF_sub hwF⟩, hwF⟩⟩
      rw [this, ← hFV_eq]
      exact Subset.antisymm (fun w hw => ⟨hw.1, hD_norm B' hB' hw⟩)
        (fun w hw => ⟨hw.1, Γ.V_subset_U hw.2⟩)
    obtain ⟨E₁, E₂, hE₁, hE₂, hE_union, hE_inter, hE₁_int, hE₂_int, _, _, _⟩ :=
      disc_iArc_split_subdiscs (hD B' hB').1 hHU_line hHU_sub hxy hHU_bd
    have hz₁_DB' : α_map z₁ ∈ D B' :=
      GM14.Whitney.subBd_subset_of subset_rfl (hD B' hB').1.isClosed (hα_bdA B' hB' z₁ hz₁)
    have hex_E : ∃ E_idx : Set S,
        IsClosedDisc E_idx ∧ E_idx ⊆ D B' ∧ H.U ⊆ E_idx ∧
        E_idx \ discBd E_idx ⊆ (D B' \ discBd (D B')) \ H.U ∧ α_map z₁ ∈ E_idx := by
      rcases (hE_union ▸ hz₁_DB' : α_map z₁ ∈ E₁ ∪ E₂) with h1 | h2
      · exact ⟨E₁, hE₁, hE_union ▸ subset_union_left, hE_inter ▸ inter_subset_left, hE₁_int, h1⟩
      · exact ⟨E₂, hE₂, hE_union ▸ subset_union_right, hE_inter ▸ inter_subset_right, hE₂_int, h2⟩
    obtain ⟨E_idx, hE_disc, hE_sub, hHU_E, hE_int, hz₁_E⟩ := hex_E
    have hHU_bdE : H.U ⊆ discBd E_idx := by
      intro w hw
      by_contra hw_not_bd
      exact (hE_int ⟨hHU_E hw, hw_not_bd⟩).2 hw
    have hE_pre : IsPreconnected (E_idx \ H.U) :=
      isPreconnected_disc_sdiff_of_subset_discBd hE_disc hHU_bdE
    have hE_disj : Disjoint (E_idx \ H.U) Γ.U := by
      rw [disjoint_left]
      intro w ⟨hwE, hw_not_HU⟩ hwU
      exact hw_not_HU (hH_U.symm ▸ ⟨hwU, hE_sub hwE⟩)
    have hz₁_not_HU : α_map z₁ ∉ H.U := fun h => hz₁_notU (hH_U ▸ h).1
    have hE_sub_r : E_idx \ H.U ⊆ r :=
      GM11.subset_region hr hE_pre hE_disj ⟨hz₁_E, hz₁_not_HU⟩ hz₁_r
    have hv_E : v ∈ E_idx := hHU_E (H.V_subset_U hv.1)
    have hv_cl_r : v ∈ closure r :=
      closure_mono hE_sub_r (subset_closure_disc_sdiff_of_subset_discBd hE_disc hHU_bdE hv_E)
    have hv_V : v ∈ Γ.V := (hH_V ▸ hv.1).1
    have hv_not_r : v ∉ r := fun h => GM11.region_subset hr h (Γ.V_subset_U hv_V)
    rw [GM11.subBd_eq_frontier, frontier, (GM11.region_isOpen hr).interior_eq]
    exact ⟨hv_cl_r, hv_not_r⟩

/-! ## Claim (6) of Theorem 8.3 -/

/-- **Claim (6) of Theorem (8.3)** (Graph Minors XXII, Section 8, page 561):
"(6) For each $A \in \mathcal{A}$, there is a region of $\Gamma$ incident with $v(A)$ having
non-empty intersection with $D(A)$." -/
theorem lemma_8_3_claim_6
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Surface.Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 4 ≤ ord)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀)
    (hbd_Δ₀ : subBd Δ₀ ∩ Γ.U = PiSet)
    {α_map : α → S} {D : Graph α β → Set S}
    (hα_ΓV : ∀ v ∈ Γ.V, ιV v ∈ Z → α_map (ιV v) = v)
    (hα_ΓU : ∀ v ∈ Z, α_map v ∈ Γ.U ↔ v ∈ ιV '' Γ.V)
    (hinj : InjOn α_map Z)
    (hD : ∀ A ∈ 𝒜, IsClosedDisc (D A) ∧ D A ⊆ Δ₀)
    (hD_norm : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.U ⊆ Γ.V)
    (hα_bdA : ∀ A ∈ 𝒜, ∀ v ∈ Set.range (πA A), α_map v ∈ subBd (D A))
    (hD_props : ∀ A ∈ 𝒜,
      subBd (D A) ∩ Γ.U = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} ∧
      subBd (D A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} ∧
      (Γ.interSet (D A)).V = {v ∈ Γ.V | ιV v ∈ V(A)} ∧
      (Γ.interSet (D A)).E = {e ∈ Γ.E | ιE e ∈ E(A)} ∧
      (Γ.interSet (D A)).toEmbeddedGraph ιV ιE = (Γ.toEmbeddedGraph ιV ιE) ⊓ A) :
    ∀ A ∈ 𝒜, ∃ r ∈ Γ.R, vA A ∈ subBd r ∧ (r ∩ D A).Nonempty := by
  intro A hA
  obtain ⟨hS_closed, _⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have hπ_eq_Z : ∀ B' ∈ 𝒜, Set.range (πA B') = Z ∩ V(B') :=
    fun B' hB' => (h83.hyp_vii B' hB').2.2
  obtain ⟨hvA_V, u, hu_ZA, P, hP_path, hP_inter_ΓV⟩ := h83.hyp_xi A hA
  -- Case 1: `ιV (vA A) ∈ Z ∩ V(A)`.
  by_cases hvA_ZA : ιV (vA A) ∈ Z ∩ V(A)
  · have hvA_range : ιV (vA A) ∈ Set.range (πA A) := (hπ_eq_Z A hA).symm ▸ hvA_ZA
    have hvA_bd : vA A ∈ subBd (D A) := by
      have h1 := hα_bdA A hA (ιV (vA A)) hvA_range
      rwa [hα_ΓV (vA A) hvA_V hvA_ZA.1] at h1
    have hbd_eq : subBd (D A) = discBd (D A) :=
      GM14.IsClosedDisc.subBd_eq_discBd hS_closed (hD A hA).1
    have hC_oarc : IsOArc (subBd (D A)) := hbd_eq ▸ (hD A hA).1.isOArc_discBd
    have hfin_U : (subBd (D A) ∩ Γ.U).Finite := by
      rw [(hD_props A hA).1]
      exact (Γ.finite_V).subset (fun _ hv => hv.1)
    exact exists_region_incident_of_mem_oArc_of_finite hS_closed
      (GM14.Whitney.subBd_subset_of subset_rfl (hD A hA).1.isClosed) hC_oarc hvA_bd hvA_V hfin_U
  -- Case 2: `ιV (vA A) ∉ Z ∩ V(A)`.
  have hv_ne_u : ιV (vA A) ≠ u := fun h => hvA_ZA (h ▸ hu_ZA)
  obtain ⟨hle_P, W₀, hs₀, hVP, _⟩ := hP_path
  let W_G : GraphWalk (R_G.G.toGraph.deleteVerts W) (ιV (vA A)) u := W₀.mono hle_P
  have hsupp_G : W_G.support = W₀.support := W₀.support_mono hle_P
  have hs_G : W_G.IsSimple := by
    change W_G.support.Nodup
    rw [hsupp_G]
    exact hs₀
  have hsupp_in_VP : ∀ y ∈ W_G.support, y ∈ V(P) := by
    intro y hy
    rw [hVP, mem_ofPred_eq, ← hsupp_G]
    exact hy
  have hno_ΓV : ∀ y ∈ W_G.support, y ≠ ιV (vA A) → y ∉ ιV '' Γ.V := by
    intro y hy hne hyΓ
    have hy_in : y ∈ V(P) ∩ (ιV '' Γ.V) := ⟨hsupp_in_VP y hy, hyΓ⟩
    rw [hP_inter_ΓV, mem_singleton_iff] at hy_in
    exact hne hy_in
  have hno_C₀ : ∀ y ∈ W_G.support, y ≠ ιV (vA A) → y ∉ ιV '' C₀.V :=
    fun y hy hne hyC₀ => hno_ΓV y hy hne (image_mono h83.hyp_ii.1.1 hyC₀)
  have hvA_J : ιV (vA A) ∈ V(J) \ W := by
    rw [← vertexSet_deleteVerts]
    exact (Γ_le_J_8_3 h83).1.vertexSet_mono ⟨vA A, hvA_V, rfl⟩
  have hu_J : u ∈ V(J) \ W := h83.hyp_vi.1 hu_ZA.1
  obtain ⟨W_J, hsupp_J⟩ := exists_walk_in_J_deleteVerts_W h83 W_G hs_G hvA_J hu_J hno_C₀
  have hs_J : W_J.IsSimple := by
    change W_J.support.Nodup
    rw [hsupp_J]
    exact hs_G
  -- Split `W_J` at its first hit `z_first ∈ Z`.
  obtain ⟨z_first, W₁, W₂, hWJ_eq, hW₁_simp, hW₂_simp, hv_ne_zf, hzf_cases, hW₁_int, _⟩ :=
    exists_first_hit_on_simpleWalk W_J hs_J hv_ne_u (Z := Z)
  have hzf_Z : z_first ∈ Z := hzf_cases.elim (fun h => h ▸ hu_ZA.1) id
  have hmem_append_left : ∀ {x y z : α} (Wa : GraphWalk (J.deleteVerts W) x y)
      (Wb : GraphWalk (J.deleteVerts W) y z) {q : α},
      q ∈ Wa.support → q ∈ (Wa.append Wb).support := by
    intro x y z Wa Wb q hq
    induction Wa with
    | nil _ =>
      simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      exact Wb.start_mem_support
    | @cons a b c e hlk rest ih =>
      simp only [GraphWalk.support, List.mem_cons] at hq
      rcases hq with rfl | hq'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih Wb hq')
  have hmem_append_right : ∀ {x y z : α} (Wa : GraphWalk (J.deleteVerts W) x y)
      (Wb : GraphWalk (J.deleteVerts W) y z) {q : α},
      q ∈ Wb.support → q ∈ (Wa.append Wb).support := by
    intro x y z Wa Wb q hq
    induction Wa with
    | nil _ => exact hq
    | @cons a b c e hlk rest ih => exact List.mem_cons_of_mem a (ih Wb hq)
  have hW₁_sub : ∀ y ∈ W₁.support, y ∈ W_G.support := by
    intro y hy
    rw [← hsupp_J, hWJ_eq]
    exact hmem_append_left W₁ W₂ hy
  have hW₂_sub : ∀ y ∈ W₂.support, y ∈ W_G.support := by
    intro y hy
    rw [← hsupp_J, hWJ_eq]
    exact hmem_append_right W₁ W₂ hy
  -- Since `W_J = W₁.append W₂` is simple and `ιV (vA A) ≠ z_first`, `ιV (vA A) ∉ W₂.support`.
  have hv_not_W₂ : ιV (vA A) ∉ W₂.support := by
    rcases W₁ with _ | ⟨hlk, rest⟩
    · exact False.elim (hv_ne_zf rfl)
    · have h_eq : W_J.support = ιV (vA A) :: (rest.append W₂).support := by
        rw [hWJ_eq]
        rfl
      have hnodup : (ιV (vA A) :: (rest.append W₂).support).Nodup := h_eq ▸ hs_J
      intro hmem
      exact (List.nodup_cons.mp hnodup).1 (hmem_append_right rest W₂ hmem)
  -- Define the region `r ∈ Γ.R` containing `α_map u ∈ subBd (D A) \ Γ.U`.
  have hu_not_ΓV : u ∉ ιV '' Γ.V :=
    hno_ΓV u (hW₂_sub u W₂.end_mem_support) hv_ne_u.symm
  have hu_notU : α_map u ∉ Γ.U := fun h => hu_not_ΓV ((hα_ΓU u hu_ZA.1).mp h)
  obtain ⟨r, hr, hu_r⟩ := GM11.exists_region_of_notMem hu_notU
  have hu_DA : α_map u ∈ D A :=
    GM14.Whitney.subBd_subset_of subset_rfl (hD A hA).1.isClosed
      (hα_bdA A hA u ((hπ_eq_Z A hA).symm ▸ hu_ZA))
  have hr_DA_ne : (r ∩ D A).Nonempty := ⟨α_map u, hu_r, hu_DA⟩
  -- Walk along the valid chain of `W₂` (from `z_first` to `u`) to show `α_map z_first ∈ r`.
  have hZdiv : IsZDivision J (Z ∪ W) 𝒜 := h83.hyp_vi.2.2.1
  have hex_vc := exists_validChain_of_walk (S_verts := {y | y ∈ W₂.support} ∩ Z)
    hZdiv W₂ hW₂_simp hzf_Z hu_ZA.1 (fun y hy hyZ => ⟨hy, hyZ⟩)
  obtain ⟨k, z, A_seq, hvc, hz_inj, _⟩ := exists_minimal_validChain hex_vc
  have hz_notU : ∀ m ≤ k, α_map (z m) ∉ Γ.U := by
    intro m hm hU
    obtain ⟨hz_W₂, hz_Z⟩ := hvc.2.2.1 m hm
    have hz_ΓV : z m ∈ ιV '' Γ.V := (hα_ΓU (z m) hz_Z).mp hU
    exact hno_ΓV (z m) (hW₂_sub (z m) hz_W₂) (fun heq => hv_not_W₂ (heq ▸ hz_W₂)) hz_ΓV
  have hzf_r : α_map z_first ∈ r := by
    have hchain_r : ∀ d ≤ k, α_map (z (k - d)) ∈ r := by
      intro d hd
      induction d with
      | zero =>
        rw [Nat.sub_zero, hvc.2.1]
        exact hu_r
      | succ d' ih =>
        have hd'_le : d' ≤ k := by omega
        have h_prev : α_map (z (k - d')) ∈ r := ih hd'_le
        have hm_lt : k - (d' + 1) < k := by omega
        have hm_succ : k - (d' + 1) + 1 = k - d' := by omega
        obtain ⟨hAm, hzm_Am, hzm1_Am⟩ := hvc.2.2.2 (k - (d' + 1)) hm_lt
        rw [hm_succ] at hzm1_Am
        have hne_z : z (k - d') ≠ z (k - (d' + 1)) := fun heq => by
          have := hz_inj (k - d') (by omega) (k - (d' + 1)) (by omega) heq
          omega
        have hstep := step_region_along_bd_of_piece h83 hα_ΓV hinj
          (fun B' hB' => (hD B' hB').1) hα_bdA (fun B' hB' => (hD_props B' hB').1)
          hAm ((hπ_eq_Z _ hAm).symm ▸ hzm1_Am) ((hπ_eq_Z _ hAm).symm ▸ hzm_Am)
          hne_z hr h_prev
        exact hstep.2.1 (hz_notU (k - (d' + 1)) (by omega))
    have h0 := hchain_r k le_rfl
    rwa [Nat.sub_self, hvc.1] at h0
  -- Now `W₁` goes from `ιV (vA A)` to `z_first` with no internal vertices in `Z`, so it lies in a single piece `A₁ ∈ 𝒜`.
  obtain ⟨A₁, hA₁, hW₁_V, _⟩ := walk_in_single_piece_of_notMem_Z hZdiv W₁ hW₁_simp hv_ne_zf hW₁_int
  have hv_A₁ : ιV (vA A) ∈ V(A₁) := hW₁_V (ιV (vA A)) W₁.start_mem_support
  have hzf_A₁ : z_first ∈ Set.range (πA A₁) :=
    (hπ_eq_Z A₁ hA₁).symm ▸ ⟨hzf_Z, hW₁_V z_first W₁.end_mem_support⟩
  -- Subcase 2a: `ιV (vA A) ∈ Z`.
  by_cases hv_Z : ιV (vA A) ∈ Z
  · have hv_range₁ : ιV (vA A) ∈ Set.range (πA A₁) :=
      (hπ_eq_Z A₁ hA₁).symm ▸ ⟨hv_Z, hv_A₁⟩
    have hstep := step_region_along_bd_of_piece h83 hα_ΓV hinj
      (fun B' hB' => (hD B' hB').1) hα_bdA (fun B' hB' => (hD_props B' hB').1)
      hA₁ hzf_A₁ hv_range₁ hv_ne_zf.symm hr hzf_r
    have hα_v : α_map (ιV (vA A)) = vA A := hα_ΓV (vA A) hvA_V hv_Z
    have hv_subBd : vA A ∈ subBd r :=
      hα_v ▸ hstep.2.2 (hα_v.symm ▸ Γ.V_subset_U hvA_V)
    exact ⟨r, hr, hv_subBd, hr_DA_ne⟩
  -- Subcase 2b: `ιV (vA A) ∉ Z`.
  · have hv_interV : vA A ∈ (Γ.interSet (D A₁)).V := by
      rw [(hD_props A₁ hA₁).2.2.1]
      exact ⟨hvA_V, hv_A₁⟩
    have hv_not_bd₁ : vA A ∉ subBd (D A₁) := by
      intro hbd
      have hmem : vA A ∈ subBd (D A₁) ∩ Γ.V := ⟨hbd, hvA_V⟩
      rw [(hD_props A₁ hA₁).2.1] at hmem
      exact hv_Z ((hπ_eq_Z A₁ hA₁) ▸ hmem.2).1
    have hv_subBd : vA A ∈ subBd r :=
      incident_of_rigid_disc_piece h83 hord hΔ₀ hbd_Δ₀ hα_ΓU hD hD_norm hα_bdA
        (fun B' hB' => (hD_props B' hB').2.1) hA₁ hzf_A₁ hr hzf_r ⟨hv_interV, hv_not_bd₁⟩
    exact ⟨r, hr, hv_subBd, hr_DA_ne⟩

end GraphMinor.GM22
