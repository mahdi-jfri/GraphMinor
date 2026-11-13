module

public import GraphMinor.GM03.Section2j
public import GraphMinor.GM03.Section2k
public import GraphMinor.GM03.Section2l
public import GraphMinor.Surface.DiscArcs
public import GraphMinor.GM11.RegionCount
public import GraphMinor.GM11.PerimeterWalk
public import GraphMinor.GM11.CollarCut

/-!
# Graph Minors III, Section 2m: Collar Sublevels, Edge Truncation, and Partial-Shell Setup

This file develops the topological collar-sublevel, edge-truncation, and partial-shell invariants
used in `Section2n` to complete the proof of `(2.3)` (page 55) of N. Robertson and P. D. Seymour,
*Graph Minors. III. Planar Tree-Width*, J. Combin. Theory Ser. B **36** (1984), 49–64:
1. `exists_small_collar_height` and `collar_sublevel_isClosedDisc`: thickening a closed nonempty
   preconnected set `X ⊆ interior Δ_out` along a surface collar `h : C(Circle × 𝕀, S)` produces a
   closed disc `K_ε = X ∪ h(Circle × [0, ε])` inside `interior Δ_out` with `discBd K_ε = h(Circle × {ε})`;
2. `exists_edge_arc` and `truncate_arc_at_closedDisc`: parameterizing simple drawing edges as arcs
   and truncating them at their last exit from `K_ε`;
3. `runsAlongOn_support_times`, `shellVerts`, `shellGraph`, and `ShellStepInv`: extracting parameter
   times along a perimeter walk and defining the outward partial-shell induction invariant.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Topology Filter
open Graph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11

local notation "𝕀" => unitInterval

universe u v

/-! ## 1. Collar Sublevel Closed Disc -/

section CollarDisc

/-- Given a collar `h : C(Circle × 𝕀, S)` whose bottom `h(Circle × {0})` lies in `X ⊆ U` (`U` open),
there exists `0 < ε < 1` such that `X ∪ h(Circle × [0, ε]) ⊆ U`. -/
theorem exists_small_collar_height {S : Type*} [TopologicalSpace S] [T2Space S]
    (h : C(Circle × 𝕀, S)) {X U : Set S} (hU : IsOpen U) (hXU : X ⊆ U)
    (hbot : ∀ z : Circle, h (z, 0) ∈ X) :
    ∃ ε : 𝕀, (0 : 𝕀) < ε ∧ ε < 1 ∧ X ∪ h '' {p | p.2 ≤ ε} ⊆ U := by
  let K_bad : Set (Circle × 𝕀) := h ⁻¹' Uᶜ
  have hK_comp : IsCompact K_bad := (hU.isClosed_compl.preimage h.continuous).isCompact
  by_cases hK : K_bad.Nonempty
  · obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
      hK_comp.exists_isMinOn hK (continuous_subtype_val.comp continuous_snd).continuousOn
    have hp₀_pos : (0 : ℝ) < (p₀.2 : ℝ) := by
      rcases eq_or_lt_of_le (unitInterval.nonneg p₀.2) with h0 | hpos
      · have hp_eq : p₀ = (p₀.1, 0) := Prod.ext rfl (Subtype.ext h0.symm)
        exact (hp₀_mem (hp_eq ▸ hXU (hbot p₀.1))).elim
      · exact hpos
    let r : ℝ := min ((p₀.2 : ℝ) / 2) (1 / 2)
    have hr0 : 0 < r := by dsimp only [r]; positivity
    have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hr_lt : r < (p₀.2 : ℝ) :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let ε : 𝕀 := ⟨r, hr0.le, hr1.le⟩
    refine ⟨ε, hr0, hr1, union_subset hXU ?_⟩
    rintro _ ⟨p, hp_le, rfl⟩
    by_contra hp_not
    have hmin : (p₀.2 : ℝ) ≤ (p.2 : ℝ) := isMinOn_iff.mp hp₀_min p hp_not
    have hle' : (p.2 : ℝ) ≤ r := hp_le
    linarith
  · let ε : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩
    refine ⟨ε, show (0 : ℝ) < 1 / 2 by norm_num, show (1 / 2 : ℝ) < 1 by norm_num,
      union_subset hXU ?_⟩
    rintro _ ⟨p, _, rfl⟩
    by_contra hp_not
    exact hK ⟨p, hp_not⟩

/-- On a connected closed surface `S`, if `X ⊆ interior Δ_out` is closed, nonempty, and
preconnected, and `h : C(Circle × 𝕀, S)` is a collar around `X` with `0 < ε < 1` and
`K = X ∪ h(Circle × [0, ε]) ⊆ interior Δ_out`, then `K` is a closed disc with boundary
`h(Circle × {ε})` and `X ⊆ interior K`. -/
theorem collar_sublevel_isClosedDisc {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Δ_out X : Set S} (hΔ_out : IsClosedDisc Δ_out)
    (hX_ne : X.Nonempty) (hX_cl : IsClosed X) (hX_pre : IsPreconnected X)
    (h : C(Circle × 𝕀, S))
    (hinj : InjOn h {p | 0 < p.2})
    (hoff : ∀ p : Circle × 𝕀, 0 < p.2 → h p ∉ X)
    (hbot : ∀ z : Circle, h (z, 0) ∈ X)
    (hop : IsOpen (X ∪ h '' {p | p.2 < 1}))
    {ε : 𝕀} (hε0 : (0 : 𝕀) < ε) (hε1 : ε < 1)
    (hsub_out : X ∪ h '' {p | p.2 ≤ ε} ⊆ interior Δ_out) :
    let K := X ∪ h '' {p | p.2 ≤ ε}
    IsClosedDisc K ∧
      discBd K = range (fun z : Circle => h (z, ε)) ∧
      K ⊆ Δ_out \ discBd Δ_out ∧
      X ⊆ interior K ∧
      ∃ φ_ε : Circle ≃ₜ discBd K, ∀ z : Circle, (φ_ε z).1 = h (z, ε) := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let K : Set S := X ∪ h '' {p | p.2 ≤ ε}
  let F : Set S := range (fun z : Circle => h (z, ε))
  have hF_sub_K : F ⊆ K := by
    rintro _ ⟨z, rfl⟩
    exact Or.inr ⟨(z, ε), show (z, ε).2 ≤ ε from le_rfl, rfl⟩
  have hK_sub_diff : K ⊆ Δ_out \ discBd Δ_out := by
    rw [show Δ_out \ discBd Δ_out = discInt Δ_out from rfl,
      discInt_eq_interior_of_isClosedDisc hS hΔ_out]
    exact hsub_out
  have hF_sub_out : F ⊆ Δ_out := hF_sub_K.trans (hK_sub_diff.trans sdiff_subset)
  -- Build `φ_F : Circle ≃ₜ F`
  let f_ε : Circle → F := fun z => ⟨h (z, ε), ⟨z, rfl⟩⟩
  have hf_cont : Continuous f_ε :=
    Continuous.subtype_mk (h.continuous.comp (Continuous.prodMk_left ε)) _
  have hf_bij : Bijective f_ε := by
    refine ⟨fun z₁ z₂ heq => ?_, fun ⟨_, z, rfl⟩ => ⟨z, rfl⟩⟩
    have h1 : (z₁, ε) = (z₂, ε) := hinj hε0 hε0 (congrArg Subtype.val heq)
    exact Prod.mk.inj h1 |>.1
  let φ_F : Circle ≃ₜ F :=
    hf_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f_ε hf_bij)
  have hFO : IsOArc F := ⟨φ_F⟩
  obtain ⟨Δ_ε, ⟨hΔε_sub_out, hΔε_disc, hΔε_bd, _, hΔε_disj_bd, _⟩, _⟩ :=
    disc_oArc Δ_out F hΔ_out hF_sub_out hFO
  have hΔε_sub_diff : Δ_ε ⊆ Δ_out \ discBd Δ_out := by
    intro x hx
    refine ⟨hΔε_sub_out hx, fun hx_bd => ?_⟩
    by_cases hxF : x ∈ F
    · exact (hK_sub_diff (hF_sub_K hxF)).2 hx_bd
    · exact Set.disjoint_left.mp hΔε_disj_bd ⟨hx, hxF⟩ hx_bd
  have hfr_Δε : frontier Δ_ε = F :=
    (GM11.IsClosedDisc.frontier_eq_discBd hS hΔε_disc).trans hΔε_bd
  -- Show `W_in = X ∪ h(Circle × [0, ε))` is preconnected and disjoint from `F`
  let W_in : Set S := X ∪ h '' {p | p.2 < ε}
  have hWin_pre : IsPreconnected W_in := by
    intro U V hU hV hcov hWU hWV
    by_contra hdisj
    have hseg : ∀ p : Circle × 𝕀, p.2 < ε →
        (h p ∈ U → h (p.1, 0) ∈ U) ∧ (h p ∈ V → h (p.1, 0) ∈ V) := by
      intro p hp
      let seg : 𝕀 → S := fun s => h (p.1, ⟨s.1 * p.2.1,
        mul_nonneg s.2.1 p.2.2.1,
        (mul_le_of_le_one_left p.2.2.1 s.2.2).trans p.2.2.2⟩)
      have hseg_cont : Continuous seg :=
        h.continuous.comp (continuous_const.prodMk
          (Continuous.subtype_mk (continuous_subtype_val.mul continuous_const) _))
      have hseg_sub : range seg ⊆ W_in := by
        rintro _ ⟨s, rfl⟩
        refine Or.inr ⟨_, ?_, rfl⟩
        change s.1 * p.2.1 < ε.1
        have hp' : p.2.1 < ε.1 := hp
        nlinarith [s.2.1, s.2.2, p.2.2.1]
      have hseg0 : seg 0 = h (p.1, 0) := by
        dsimp only [seg]; congr 2; exact Subtype.ext (by simp)
      have hseg1 : seg 1 = h p := by
        dsimp only [seg]; congr 1; exact Prod.ext rfl (Subtype.ext (one_mul _))
      have hseg_pre : IsPreconnected (range seg) := isPreconnected_range hseg_cont
      have h0_mem : h (p.1, 0) ∈ U ∪ V := hcov (Or.inl (hbot p.1))
      constructor
      · intro hpU
        rcases h0_mem with h0U | h0V
        · exact h0U
        · exfalso
          obtain ⟨w, hw_rg, hwUV⟩ := hseg_pre U V hU hV (hseg_sub.trans hcov)
            ⟨h p, ⟨1, hseg1⟩, hpU⟩ ⟨h (p.1, 0), ⟨0, hseg0⟩, h0V⟩
          exact hdisj ⟨w, hseg_sub hw_rg, hwUV⟩
      · intro hpV
        rcases h0_mem with h0U | h0V
        · exfalso
          obtain ⟨w, hw_rg, hwUV⟩ := hseg_pre U V hU hV (hseg_sub.trans hcov)
            ⟨h (p.1, 0), ⟨0, hseg0⟩, h0U⟩ ⟨h p, ⟨1, hseg1⟩, hpV⟩
          exact hdisj ⟨w, hseg_sub hw_rg, hwUV⟩
        · exact h0V
    have hXU : (X ∩ U).Nonempty := by
      obtain ⟨y, hyW, hyU⟩ := hWU
      rcases hyW with hyX | ⟨p, hp, rfl⟩
      · exact ⟨y, hyX, hyU⟩
      · exact ⟨h (p.1, 0), hbot p.1, (hseg p hp).1 hyU⟩
    have hXV : (X ∩ V).Nonempty := by
      obtain ⟨y, hyW, hyV⟩ := hWV
      rcases hyW with hyX | ⟨p, hp, rfl⟩
      · exact ⟨y, hyX, hyV⟩
      · exact ⟨h (p.1, 0), hbot p.1, (hseg p hp).2 hyV⟩
    obtain ⟨w, hwX, hwUV⟩ := hX_pre U V hU hV (subset_union_left.trans hcov) hXU hXV
    exact hdisj ⟨w, Or.inl hwX, hwUV⟩
  have hdisj_Win_F : Disjoint W_in F := by
    rw [Set.disjoint_left]
    rintro _ (hyX | ⟨p, hp_lt, rfl⟩) ⟨z, heq⟩
    · change h (z, ε) = _ at heq
      exact hoff (z, ε) hε0 (heq.symm ▸ hyX)
    · change h (z, ε) = h p at heq
      rcases eq_or_lt_of_le (unitInterval.nonneg p.2) with hp0 | hp_pos
      · have hp_eq : p = (p.1, 0) := Prod.ext rfl (Subtype.ext hp0.symm)
        exact hoff (z, ε) hε0 (heq.symm ▸ hp_eq ▸ hbot p.1)
      · have hpz : p = (z, ε) := hinj hp_pos hε0 heq.symm
        exact (ne_of_lt hp_lt) (congrArg Prod.snd hpz)
  -- Rule out `Disjoint W_in Δ_ε` using connectedness of `S` and `discBd Δ_out ≠ ∅`
  have hWin_sub_Δε : W_in ⊆ Δ_ε := by
    rcases GM11.subset_or_disjoint_of_frontier hΔε_disc.isClosed hWin_pre
        (hfr_Δε.symm ▸ hdisj_Win_F) with hsub | hdisj_WΔ
    · exact hsub
    · exfalso
      let B_plus : Set (Circle × 𝕀) := univ ×ˢ Ioo ε 1
      have hBp_pre : IsPreconnected (h '' B_plus) :=
        (isPreconnected_univ.prod isPreconnected_Ioo).image h h.continuous.continuousOn
      have hdisj_Bp_F : Disjoint (h '' B_plus) F := by
        rw [Set.disjoint_left]
        rintro _ ⟨p, ⟨-, hp_gt, _⟩, rfl⟩ ⟨z, heq⟩
        have hpz : p = (z, ε) := hinj (lt_trans hε0 hp_gt) hε0 heq.symm
        exact (ne_of_gt hp_gt) (congrArg Prod.snd hpz)
      have hBp_meets_int : (h '' B_plus ∩ interior Δ_ε).Nonempty := by
        have hy₀_bd : h (1, ε) ∈ discBd Δ_ε := hΔε_bd.symm ▸ ⟨1, rfl⟩
        have hy₀_cl : h (1, ε) ∈ closure (interior Δ_ε) := by
          rw [← discInt_eq_interior_of_isClosedDisc hS hΔε_disc]
          exact hΔε_disc.subset_closure_discInt (GM11.discBd_subset Δ_ε hy₀_bd)
        have hy₀_op : h (1, ε) ∈ X ∪ h '' {p | p.2 < 1} := Or.inr ⟨(1, ε), hε1, rfl⟩
        obtain ⟨w, hw_op, hw_int⟩ := mem_closure_iff.mp hy₀_cl _ hop hy₀_op
        have hw_not_F : w ∉ F := by
          rw [← hΔε_bd]
          have hw_di : w ∈ discInt Δ_ε :=
            (discInt_eq_interior_of_isClosedDisc hS hΔε_disc).symm ▸ hw_int
          exact hw_di.2
        have hw_not_W : w ∉ W_in := fun hwW =>
          Set.disjoint_left.mp hdisj_WΔ hwW (interior_subset hw_int)
        rcases hw_op with hwX | ⟨p, hp_lt1, rfl⟩
        · exact (hw_not_W (Or.inl hwX)).elim
        · have hp_ge : ε ≤ p.2 := not_lt.mp fun hlt => hw_not_W (Or.inr ⟨p, hlt, rfl⟩)
          have hp_ne : p.2 ≠ ε := fun heq =>
            hw_not_F ⟨p.1, congrArg h (Prod.ext rfl heq.symm)⟩
          exact ⟨h p, ⟨p, ⟨mem_univ _, lt_of_le_of_ne hp_ge hp_ne.symm, hp_lt1⟩, rfl⟩, hw_int⟩
      have hBp_sub_Δε : h '' B_plus ⊆ Δ_ε := by
        rcases GM11.subset_or_disjoint_of_frontier hΔε_disc.isClosed hBp_pre
            (hfr_Δε.symm ▸ hdisj_Bp_F) with hsub | hdisj_Bp
        · exact hsub
        · obtain ⟨w, hwBp, hw_int⟩ := hBp_meets_int
          exact (Set.disjoint_left.mp hdisj_Bp hwBp (interior_subset hw_int)).elim
      let U_all : Set S := (X ∪ h '' {p | p.2 < 1}) ∪ interior Δ_ε
      let K_all : Set S := K ∪ Δ_ε
      have hUK_eq : U_all = K_all := by
        refine Subset.antisymm ?_ ?_
        · rintro y ((hyX | ⟨p, hp1, rfl⟩) | hy_int)
          · exact Or.inl (Or.inl hyX)
          · by_cases hle : p.2 ≤ ε
            · exact Or.inl (Or.inr ⟨p, hle, rfl⟩)
            · exact Or.inr (hBp_sub_Δε ⟨p, ⟨mem_univ _, not_le.mp hle, hp1⟩, rfl⟩)
          · exact Or.inr (interior_subset hy_int)
        · rintro y ((hyX | ⟨p, hp_le, rfl⟩) | hyΔ)
          · exact Or.inl (Or.inl hyX)
          · exact Or.inl (Or.inr ⟨p, lt_of_le_of_lt hp_le hε1, rfl⟩)
          · by_cases hyF : y ∈ F
            · obtain ⟨z, rfl⟩ := hyF
              exact Or.inl (Or.inr ⟨(z, ε), hε1, rfl⟩)
            · have hy_int : y ∈ interior Δ_ε := by
                rw [← discInt_eq_interior_of_isClosedDisc hS hΔε_disc]
                exact ⟨hyΔ, hΔε_bd.symm ▸ hyF⟩
              exact Or.inr hy_int
      have hK_cl : IsClosed K :=
        hX_cl.union (((isClosed_le continuous_snd continuous_const).isCompact.image
          h.continuous).isClosed)
      have hKall_clopen : IsClopen K_all :=
        ⟨hK_cl.union hΔε_disc.isClosed, hUK_eq ▸ (hop.union isOpen_interior)⟩
      have hKall_ne : K_all.Nonempty := hX_ne.mono (subset_union_left.trans subset_union_left)
      have hKall_univ : K_all = univ := hKall_clopen.eq_univ hKall_ne
      have huniv_sub : (univ : Set S) ⊆ Δ_out \ discBd Δ_out :=
        hKall_univ ▸ union_subset hK_sub_diff hΔε_sub_diff
      obtain ⟨φ_bd⟩ := hΔ_out.isOArc_discBd
      exact (huniv_sub (mem_univ (φ_bd 1).1)).2 (φ_bd 1).2
  have hK_sub_Δε : K ⊆ Δ_ε := by
    rintro y (hyX | ⟨p, hp_le, rfl⟩)
    · exact hWin_sub_Δε (Or.inl hyX)
    · rcases eq_or_lt_of_le (show p.2 ≤ ε from hp_le) with heq | hlt
      · exact GM11.discBd_subset Δ_ε
          (hΔε_bd.symm ▸ ⟨p.1, congrArg h (Prod.ext rfl heq.symm)⟩)
      · exact hWin_sub_Δε (Or.inr ⟨p, hlt, rfl⟩)
  -- Show `W_in` is open and `Δ_ε ⊆ K`
  have hWin_eq_sdiff : W_in = (X ∪ h '' {p | p.2 < 1}) \ (h '' {p | ε ≤ p.2}) := by
    ext y
    constructor
    · rintro (hyX | ⟨p, hp_lt, rfl⟩)
      · refine ⟨Or.inl hyX, ?_⟩
        rintro ⟨q, hq_ge, hqy⟩
        exact hoff q (lt_of_lt_of_le hε0 hq_ge) (hqy ▸ hyX)
      · refine ⟨Or.inr ⟨p, lt_trans hp_lt hε1, rfl⟩, ?_⟩
        rintro ⟨q, hq_ge, hqp⟩
        rcases eq_or_lt_of_le (unitInterval.nonneg p.2) with hp0 | hp_pos
        · have hp_eq : p = (p.1, 0) := Prod.ext rfl (Subtype.ext hp0.symm)
          exact hoff q (lt_of_lt_of_le hε0 hq_ge) (hqp ▸ hp_eq ▸ hbot p.1)
        · have hqe : q = p := hinj (lt_of_lt_of_le hε0 hq_ge) hp_pos hqp
          exact not_lt_of_ge (show ε ≤ p.2 from hqe ▸ hq_ge) hp_lt
    · rintro ⟨hyX | ⟨p, _, rfl⟩, hnot_ge⟩
      · exact Or.inl hyX
      · exact Or.inr ⟨p, show p.2 < ε from not_le.mp fun hge => hnot_ge ⟨p, hge, rfl⟩, rfl⟩
  have hWin_open : IsOpen W_in := by
    rw [hWin_eq_sdiff]
    exact hop.sdiff (((isClosed_le continuous_const continuous_snd).isCompact.image
      h.continuous).isClosed)
  have hK_cl : IsClosed K :=
    hX_cl.union (((isClosed_le continuous_snd continuous_const).isCompact.image
      h.continuous).isClosed)
  have hint_pre : IsPreconnected (interior Δ_ε) := by
    rw [← discInt_eq_interior_of_isClosedDisc hS hΔε_disc]
    exact hΔε_disc.isPreconnected_discInt
  have hint_cov : interior Δ_ε ⊆ W_in ∪ Kᶜ := by
    intro y hy_int
    by_cases hyK : y ∈ K
    · refine Or.inl ?_
      rcases hyK with hyX | ⟨p, hp_le, rfl⟩
      · exact Or.inl hyX
      · rcases eq_or_lt_of_le (show p.2 ≤ ε from hp_le) with heq | hlt
        · exfalso
          have hp_eq : (p.1, ε) = p := Prod.ext rfl heq.symm
          have hy_int' : h (p.1, ε) ∈ interior Δ_ε := hp_eq.symm ▸ hy_int
          have hy_di : h (p.1, ε) ∈ discInt Δ_ε :=
            (discInt_eq_interior_of_isClosedDisc hS hΔε_disc).symm ▸ hy_int'
          exact hy_di.2 (hΔε_bd.symm ▸ ⟨p.1, rfl⟩)
        · exact Or.inr ⟨p, hlt, rfl⟩
    · exact Or.inr hyK
  have hWin_sub_K : W_in ⊆ K := by
    rintro y (hyX | ⟨p, hp_lt, rfl⟩)
    · exact Or.inl hyX
    · exact Or.inr ⟨p, le_of_lt (show p.2 < ε from hp_lt), rfl⟩
  have hdisj_WKc : Disjoint W_in Kᶜ :=
    Set.disjoint_left.mpr fun _ hyW hyKc => hyKc (hWin_sub_K hyW)
  obtain ⟨x₀, hx₀⟩ := hX_ne
  have hx₀_int : x₀ ∈ interior Δ_ε := by
    rw [← discInt_eq_interior_of_isClosedDisc hS hΔε_disc]
    exact ⟨hWin_sub_Δε (Or.inl hx₀),
      hΔε_bd.symm ▸ fun hxF => Set.disjoint_left.mp hdisj_Win_F (Or.inl hx₀) hxF⟩
  have hint_sub_W : interior Δ_ε ⊆ W_in := by
    rcases hint_pre.subset_or_subset hWin_open hK_cl.isOpen_compl hdisj_WKc hint_cov with
      hsub | hsub_c
    · exact hsub
    · exact (hsub_c hx₀_int (Or.inl hx₀)).elim
  have hΔε_sub_K : Δ_ε ⊆ K := by
    intro y hyΔ
    by_cases hyF : y ∈ F
    · exact hF_sub_K hyF
    · have hy_int : y ∈ interior Δ_ε := by
        rw [← discInt_eq_interior_of_isClosedDisc hS hΔε_disc]
        exact ⟨hyΔ, hΔε_bd.symm ▸ hyF⟩
      exact hWin_sub_K (hint_sub_W hy_int)
  have hK_eq : K = Δ_ε := Subset.antisymm hK_sub_Δε hΔε_sub_K
  have hbdK : discBd K = F := (congrArg discBd hK_eq).trans hΔε_bd
  have hK_disc : IsClosedDisc K := hK_eq.symm ▸ hΔε_disc
  refine ⟨hK_disc, hbdK, hK_sub_diff,
    (subset_union_left (t := h '' {p | p.2 < ε})).trans (interior_maximal hWin_sub_K hWin_open),
    φ_F.trans (Homeomorph.setCongr hbdK.symm), fun _ => rfl⟩

end CollarDisc

/-! ## 2. Edge Arc Parameterization and Closed-Disc Truncation -/

section EdgeTruncation

/-- Parameterize any non-loop edge `D.toGraph.IsLink e u v` (`u ≠ v`) by a continuous injective arc
`ψ : 𝕀 → S` from `u` to `v` with `ψ '' Ioo 0 1 = e`. -/
theorem exists_edge_arc {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Drawing S} {e : Set S} {u v : S} (hl : D.toGraph.IsLink e u v) (huv : u ≠ v) :
    ∃ ψ : 𝕀 → S, Continuous ψ ∧ Injective ψ ∧ ψ 0 = u ∧ ψ 1 = v ∧ ψ '' Ioo 0 1 = e := by
  rcases D.edge_cond e hl.1 with ⟨a, b, _, hcap, hline⟩ | ⟨a, hcap, _⟩
  · obtain ⟨φ, hφ0, hφ1⟩ := hline
    have hpair : ({a, b} : Set S) = {u, v} := hcap.symm.trans hl.2.2.2
    have he_diff : closure e \ {u, v} = e := by
      have h1 := D.closure_diff_V hl.1
      refine Subset.antisymm (fun x ⟨hx_cl, hx_uv⟩ => ?_) (fun x hxe => ?_)
      · exact h1.subset ⟨hx_cl, fun hxV => hx_uv (hl.2.2.2 ▸ ⟨hx_cl, hxV⟩)⟩
      · exact ⟨subset_closure hxe, fun hx_uv => (hl.1.2.1 hxe).2 (hl.2.2.2 ▸ hx_uv).2⟩
    have hu_ab : u ∈ ({a, b} : Set S) := hpair.symm ▸ mem_insert u {v}
    rcases mem_insert_iff.mp hu_ab with rfl | hu_b
    · have hv_ab : v ∈ ({u, b} : Set S) := hpair.symm ▸ mem_insert_of_mem u (mem_singleton v)
      have hvb : v = b := (mem_insert_iff.mp hv_ab).resolve_left huv.symm
      subst hvb
      let ψ : 𝕀 → S := fun t => (φ t).1
      have hψ_cont : Continuous ψ := continuous_subtype_val.comp φ.continuous
      have hψ_inj : Injective ψ := fun s t h => φ.injective (Subtype.ext h)
      refine ⟨ψ, hψ_cont, hψ_inj, hφ0, hφ1, ?_⟩
      rw [← he_diff]
      ext x
      constructor
      · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
        refine ⟨(φ t).2, ?_⟩
        rintro (hx0 | hx1)
        · exact (ne_of_gt ht0) (hψ_inj (hx0.trans hφ0.symm))
        · exact (ne_of_lt ht1) (hψ_inj ((mem_singleton_iff.mp hx1).trans hφ1.symm))
      · rintro ⟨hx_cl, hx_uv⟩
        obtain ⟨t, ht⟩ := φ.surjective ⟨x, hx_cl⟩
        have hψt : ψ t = x := congrArg Subtype.val ht
        have ht0 : (0 : 𝕀) < t := lt_of_le_of_ne (unitInterval.nonneg t) fun h =>
          hx_uv (Or.inl (hψt.symm.trans (h ▸ hφ0)))
        have ht1 : t < 1 := lt_of_le_of_ne (unitInterval.le_one t) fun h =>
          hx_uv (Or.inr (mem_singleton_iff.mpr (hψt.symm.trans (h ▸ hφ1))))
        exact ⟨t, ⟨ht0, ht1⟩, hψt⟩
    · have hub : u = b := mem_singleton_iff.mp hu_b
      have hav : a = v := by
        have ha_uv : a ∈ ({u, v} : Set S) := hpair ▸ mem_insert a {b}
        rcases mem_insert_iff.mp ha_uv with hau | hav'
        · exfalso
          have hv_ab : v ∈ ({a, b} : Set S) :=
            hpair.symm ▸ mem_insert_of_mem u (mem_singleton v)
          rcases mem_insert_iff.mp hv_ab with hva | hvb
          · exact huv (hau.symm.trans hva.symm)
          · exact huv (hub.trans hvb.symm)
        · exact mem_singleton_iff.mp hav'
      let rev : 𝕀 → 𝕀 := fun t => ⟨1 - t.1, sub_nonneg.mpr t.2.2, sub_le_self 1 t.2.1⟩
      have hrev_cont : Continuous rev :=
        Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _
      have hrev_inv : Involutive rev := fun t => Subtype.ext (by dsimp only [rev]; ring)
      let ψ : 𝕀 → S := fun t => (φ (rev t)).1
      have hψ_cont : Continuous ψ := continuous_subtype_val.comp (φ.continuous.comp hrev_cont)
      have hψ_inj : Injective ψ := fun s t h => hrev_inv.injective (φ.injective (Subtype.ext h))
      have hψ0 : ψ 0 = u := by
        have hr0 : rev 0 = 1 := Subtype.ext (by dsimp only [rev]; simp)
        change (φ (rev 0)).1 = u; rw [hr0, hφ1, hub]
      have hψ1 : ψ 1 = v := by
        have hr1 : rev 1 = 0 := Subtype.ext (by dsimp only [rev]; simp)
        change (φ (rev 1)).1 = v; rw [hr1, hφ0, hav]
      refine ⟨ψ, hψ_cont, hψ_inj, hψ0, hψ1, ?_⟩
      rw [← he_diff]
      ext x
      constructor
      · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
        refine ⟨(φ (rev t)).2, ?_⟩
        rintro (hx0 | hx1)
        · exact (ne_of_gt ht0) (hψ_inj (hx0.trans hψ0.symm))
        · exact (ne_of_lt ht1) (hψ_inj ((mem_singleton_iff.mp hx1).trans hψ1.symm))
      · rintro ⟨hx_cl, hx_uv⟩
        obtain ⟨s, hs⟩ := φ.surjective ⟨x, hx_cl⟩
        let t := rev s
        have hψt : ψ t = x := by
          change (φ (rev (rev s))).1 = x; rw [hrev_inv s]; exact congrArg Subtype.val hs
        have ht0 : (0 : 𝕀) < t := lt_of_le_of_ne (unitInterval.nonneg t) fun h =>
          hx_uv (Or.inl (hψt.symm.trans (h ▸ hψ0)))
        have ht1 : t < 1 := lt_of_le_of_ne (unitInterval.le_one t) fun h =>
          hx_uv (Or.inr (mem_singleton_iff.mpr (hψt.symm.trans (h ▸ hψ1))))
        exact ⟨t, ⟨ht0, ht1⟩, hψt⟩
  · exfalso
    have hpair : ({u, v} : Set S) = {a} := hl.2.2.2.symm.trans hcap
    have hu_a : u = a := mem_singleton_iff.mp (hpair ▸ mem_insert u {v})
    have hv_a : v = a := mem_singleton_iff.mp (hpair ▸ mem_insert_of_mem u (mem_singleton v))
    exact huv (hu_a.trans hv_a.symm)

/-- Truncate an arc `ψ : 𝕀 → S` starting in `interior Δ_in` and ending on `discBd Δ_out` (with
`ψ(0, 1) ⊆ interior Δ_out` and `Δ_in ⊆ Δ_out \ discBd Δ_out`) at its last exit time `t₀` from
`Δ_in`, yielding an arc `γ : 𝕀 → S` from `ψ t₀ ∈ discBd Δ_in` to `ψ 1` whose open interior lies in
`interior Δ_out \ Δ_in`. -/
theorem truncate_arc_at_closedDisc {S : Type} [TopologicalSpace S] (hS : IsClosedSurface S)
    {Δ_in Δ_out : Set S} (hΔ_in : IsClosedDisc Δ_in)
    {ψ : 𝕀 → S} (hψ_cont : Continuous ψ) (hψ_inj : Injective ψ)
    (h0 : ψ 0 ∈ interior Δ_in) (h1 : ψ 1 ∈ discBd Δ_out)
    (hin : Δ_in ⊆ Δ_out \ discBd Δ_out)
    (hopen : ∀ t : 𝕀, (0 : 𝕀) < t → t < 1 → ψ t ∈ interior Δ_out) :
    ∃ (t₀ : 𝕀) (γ : 𝕀 → S),
      (0 : 𝕀) < t₀ ∧ t₀ < 1 ∧
      γ 0 = ψ t₀ ∧ γ 0 ∈ discBd Δ_in ∧ γ 1 = ψ 1 ∧
      Continuous γ ∧ Injective γ ∧
      (∀ s : 𝕀, (0 : 𝕀) < s → s < 1 → γ s ∈ interior Δ_out \ Δ_in) ∧
      γ '' Ioo 0 1 ⊆ ψ '' Ioo 0 1 := by
  have : T2Space S := hS.2.1
  let ψR : ℝ → S := fun r => ψ (projIcc 0 1 zero_le_one r)
  have hψR_cont : Continuous ψR := hψ_cont.comp continuous_projIcc
  let A : Set ℝ := ψR ⁻¹' Δ_in ∩ Icc 0 1
  have hA_cl : IsClosed A := (hΔ_in.isClosed.preimage hψR_cont).inter isClosed_Icc
  have h0_A : (0 : ℝ) ∈ A := by
    refine ⟨?_, left_mem_Icc.mpr zero_le_one⟩
    change ψ (projIcc 0 1 zero_le_one 0) ∈ Δ_in
    rw [projIcc_left]
    exact interior_subset h0
  have hA_bdd : BddAbove A := ⟨1, fun _ hr => hr.2.2⟩
  let r₀ : ℝ := sSup A
  have hr₀_mem : r₀ ∈ A := hA_cl.csSup_mem ⟨0, h0_A⟩ hA_bdd
  let t₀ : 𝕀 := ⟨r₀, hr₀_mem.2.1, hr₀_mem.2.2⟩
  have hproj_t₀ : projIcc 0 1 zero_le_one r₀ = t₀ := projIcc_of_mem zero_le_one hr₀_mem.2
  have hψ_t₀_in : ψ t₀ ∈ Δ_in := hproj_t₀ ▸ hr₀_mem.1
  have ht₀_lt1 : t₀ < 1 := by
    refine lt_of_le_of_ne (unitInterval.le_one t₀) fun h_eq => ?_
    exact (hin (h_eq ▸ hψ_t₀_in)).2 h1
  have ht₀_pos : (0 : 𝕀) < t₀ := by
    obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
      GM11.exists_small ((isOpen_interior.preimage hψ_cont).mem_nhds h0)
    have hδ_A : (δ : ℝ) ∈ A := by
      refine ⟨?_, δ.2⟩
      change ψ (projIcc 0 1 zero_le_one δ.1) ∈ Δ_in
      rw [projIcc_val zero_le_one δ]
      exact interior_subset (hδ_sub δ le_rfl)
    exact lt_of_lt_of_le hδ_pos (show (δ : ℝ) ≤ r₀ from le_csSup hA_bdd hδ_A)
  have hψ_t₀_not_int : ψ t₀ ∉ interior Δ_in := by
    intro hint
    have hop_R : IsOpen (ψR ⁻¹' interior Δ_in) := isOpen_interior.preimage hψR_cont
    have hr₀_op : r₀ ∈ ψR ⁻¹' interior Δ_in := by
      change ψ (projIcc 0 1 zero_le_one r₀) ∈ interior Δ_in
      rwa [hproj_t₀]
    obtain ⟨η, hη_pos, hball⟩ := Metric.isOpen_iff.mp hop_R r₀ hr₀_op
    have hr₀_lt1 : r₀ < 1 := ht₀_lt1
    let r' : ℝ := min (r₀ + η / 2) ((r₀ + 1) / 2)
    have hr'_gt : r₀ < r' := lt_min (by linarith) (by linarith)
    have hr'_le1 : r' ≤ 1 := (min_le_right _ _).trans (by linarith)
    have hr'_dist : dist r' r₀ < η := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hr'_gt)]
      have : r' ≤ r₀ + η / 2 := min_le_left _ _
      linarith
    have hr'_in : ψR r' ∈ Δ_in := interior_subset (show ψR r' ∈ interior Δ_in from hball hr'_dist)
    have hr'_A : r' ∈ A := ⟨hr'_in, le_trans hr₀_mem.2.1 hr'_gt.le, hr'_le1⟩
    exact not_lt_of_ge (le_csSup hA_bdd hr'_A) hr'_gt
  have hψ_t₀_bd : ψ t₀ ∈ discBd Δ_in := by
    by_contra hnot_bd
    have hdi : ψ t₀ ∈ discInt Δ_in := ⟨hψ_t₀_in, hnot_bd⟩
    rw [discInt_eq_interior_of_isClosedDisc hS hΔ_in] at hdi
    exact hψ_t₀_not_int hdi
  let aff : 𝕀 → 𝕀 := fun s =>
    ⟨r₀ + s.1 * (1 - r₀),
      add_nonneg hr₀_mem.2.1 (mul_nonneg s.2.1 (sub_nonneg.mpr hr₀_mem.2.2)),
      by nlinarith [s.2.2, hr₀_mem.2.1, hr₀_mem.2.2]⟩
  have haff_cont : Continuous aff :=
    Continuous.subtype_mk (continuous_const.add (continuous_subtype_val.mul continuous_const)) _
  have haff_inj : Injective aff := by
    intro s₁ s₂ heq
    have h1 := congrArg Subtype.val heq
    dsimp only [aff] at h1
    have hpos : 0 < 1 - r₀ := sub_pos.mpr ht₀_lt1
    exact Subtype.ext (mul_right_cancel₀ hpos.ne' (add_left_cancel h1))
  let γ : 𝕀 → S := fun s => ψ (aff s)
  have hγ0 : γ 0 = ψ t₀ := by
    dsimp only [γ, aff]; congr 1; exact Subtype.ext (by simp [t₀])
  have hγ1 : γ 1 = ψ 1 := by
    dsimp only [γ, aff]; congr 1; exact Subtype.ext (by simp)
  refine ⟨t₀, γ, ht₀_pos, ht₀_lt1, hγ0, hγ0 ▸ hψ_t₀_bd, hγ1,
    hψ_cont.comp haff_cont, hψ_inj.comp haff_inj, ?_, ?_⟩
  · intro s hs0 hs1
    have hs0' : (0 : ℝ) < s.1 := hs0
    have hs1' : s.1 < 1 := hs1
    have hr₀_lt1 : r₀ < 1 := ht₀_lt1
    have hgt : t₀ < aff s := show r₀ < r₀ + s.1 * (1 - r₀) by nlinarith
    have hlt1 : aff s < 1 := show r₀ + s.1 * (1 - r₀) < 1 by nlinarith
    refine ⟨hopen (aff s) (lt_trans ht₀_pos hgt) hlt1, fun h_in => ?_⟩
    have h_mem_A : (aff s : ℝ) ∈ A := ⟨by
      change ψ (projIcc 0 1 zero_le_one (aff s).1) ∈ Δ_in
      rw [projIcc_val zero_le_one (aff s)]
      exact h_in, (aff s).2⟩
    exact not_lt_of_ge (le_csSup hA_bdd h_mem_A) (show r₀ < (aff s : ℝ) from hgt)
  · rintro _ ⟨s, ⟨hs0, hs1⟩, rfl⟩
    have hs0' : (0 : ℝ) < s.1 := hs0
    have hs1' : s.1 < 1 := hs1
    have hr₀_lt1 : r₀ < 1 := ht₀_lt1
    have hgt : t₀ < aff s := show r₀ < r₀ + s.1 * (1 - r₀) by nlinarith
    have hlt1 : aff s < 1 := show r₀ + s.1 * (1 - r₀) < 1 by nlinarith
    exact ⟨aff s, ⟨lt_trans ht₀_pos hgt, hlt1⟩, rfl⟩

end EdgeTruncation

/-! ## 3. Tour Support Times and Partial-Shell Induction Invariant -/

section ShellGluing

theorem graphWalk_support_length {α β : Type*} {G : Graph α β} {u v : α} (W : GraphWalk G u v) :
    W.support.length = W.length + 1 := by
  induction W with
  | nil _ => rfl
  | cons _ rest ih => simp [GraphWalk.support, GraphWalk.length, ih]

theorem graphWalk_to_reflTransGen {α β : Type*} {G : Graph α β} {u v : α}
    (W : GraphWalk G u v) : Relation.ReflTransGen G.Adj u v := by
  induction W with
  | nil _ => exact Relation.ReflTransGen.refl
  | cons hl rest ih => exact Relation.ReflTransGen.head ⟨_, hl⟩ ih

/-- Extract strictly increasing parameter times `τ : Fin W.support.length → ℝ` from
`RunsAlongOn Γ φ a b W`. -/
theorem runsAlongOn_support_times {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {φ : ℝ → S} {a b : ℝ} {u v : S} {W : GraphWalk Γ.toGraph u v}
    (hR : RunsAlongOn Γ φ a b W) :
    ∃ τ : Fin W.support.length → ℝ,
      StrictMono τ ∧
      τ ⟨0, List.length_pos_of_ne_nil W.support_ne_nil⟩ = a ∧
      τ ⟨W.support.length - 1,
        Nat.sub_lt (List.length_pos_of_ne_nil W.support_ne_nil) zero_lt_one⟩ = b ∧
      (∀ k : Fin W.support.length, φ (τ k) = W.support[k]) ∧
      (∀ (k : ℕ) (hk : k + 1 < W.support.length),
        φ '' Ioo (τ ⟨k, Nat.lt_of_succ_lt hk⟩) (τ ⟨k + 1, hk⟩) ∈ Γ.E) := by
  induction W generalizing a with
  | nil _ =>
    obtain ⟨hab, hφa⟩ := hR
    refine ⟨fun _ => a, fun i j hij => by
      have := i.2; have := j.2; simp [GraphWalk.support] at this; omega,
      rfl, hab, fun k => ?_, fun k hk => ?_⟩
    · rcases k with ⟨k_val, hk_lt⟩
      obtain rfl : k_val = 0 := by simp [GraphWalk.support] at hk_lt; omega
      simpa [GraphWalk.support] using hφa
    · simp [GraphWalk.support] at hk
  | @cons u w _ e hl rest ih =>
    obtain ⟨c, hac, hφa, _, hφ_eq, hR_rest⟩ := hR
    obtain ⟨τ', hτ'_mono, hτ'0, hτ'_last, hτ'_sup, hτ'_edge⟩ := ih hR_rest
    have hrest_pos : 0 < rest.support.length := List.length_pos_of_ne_nil rest.support_ne_nil
    let τ : Fin (GraphWalk.cons hl rest).support.length → ℝ := fun k =>
      if hk : k.1 = 0 then a
      else τ' ⟨k.1 - 1, by have := k.2; simp [GraphWalk.support] at this; omega⟩
    refine ⟨τ, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      have hij' := Fin.lt_def.mp hij
      dsimp only [τ]
      split_ifs with hi hj hj
      · omega
      · have hj_lt : j.1 - 1 < rest.support.length := by
          have := j.2; simp [GraphWalk.support] at this; omega
        have h0_le : τ' ⟨0, hrest_pos⟩ ≤ τ' ⟨j.1 - 1, hj_lt⟩ :=
          hτ'_mono.monotone (Fin.le_def.mpr (Nat.zero_le _))
        linarith [hac, hτ'0]
      · omega
      · exact hτ'_mono (Fin.lt_def.mpr (by dsimp only; omega))
    · dsimp only [τ]; simp
    · dsimp only [τ]
      have hne0 : (GraphWalk.cons hl rest).support.length - 1 ≠ 0 := by
        simpa [GraphWalk.support] using hrest_pos.ne'
      simp only [hne0, ↓reduceDIte]
      convert hτ'_last using 2
      apply Fin.ext; simp [GraphWalk.support]
    · rintro ⟨_ | k', hk_lt⟩
      · dsimp only [τ]; simp [GraphWalk.support, hφa]
      · dsimp only [τ]
        simpa [GraphWalk.support] using hτ'_sup ⟨k', by simp [GraphWalk.support] at hk_lt; omega⟩
    · intro k hk
      rcases k with _ | k'
      · have h0 : τ ⟨0, Nat.lt_of_succ_lt hk⟩ = a := by dsimp only [τ]; simp
        have h1 : τ ⟨1, hk⟩ = c := by
          dsimp only [τ]; simp only [Nat.one_ne_zero, ↓reduceDIte]
          simpa using hτ'0
        rw [h0, h1, hφ_eq]
        exact hl.1
      · have hk'_lt : k' + 1 < rest.support.length := by
          simp [GraphWalk.support] at hk; omega
        have hA : τ ⟨k' + 1, Nat.lt_of_succ_lt hk⟩ = τ' ⟨k', Nat.lt_of_succ_lt hk'_lt⟩ := by
          dsimp only [τ]; simp
        have hB : τ ⟨k' + 2, hk⟩ = τ' ⟨k' + 1, hk'_lt⟩ := by
          dsimp only [τ]; simp
        rw [hA, hB]
        exact hτ'_edge k' hk'_lt

/-- Induced partial-shell vertex set at outward step `k` (`0 ≤ k < d`): inner vertices plus the
innermost `k + 1` shell circuits `C_{d-1}, …, C_{d-1-k}`. -/
def shellVerts {S : Type} [TopologicalSpace S] [T2Space S]
    (D : Drawing S) (d : ℕ) (C : Fin d → Drawing S) (k : ℕ) : Set S :=
  (innerDraw D d C).V ∪ ⋃ (j : Fin d) (_ : d - 1 - k ≤ j.1), (C j).V

/-- Induced partial-shell graph at outward step `k`. -/
def shellGraph {S : Type} [TopologicalSpace S] [T2Space S]
    (D : Drawing S) (d : ℕ) (C : Fin d → Drawing S) (k : ℕ) : Graph S (Set S) :=
  D.toGraph.induce (shellVerts D d C k)

theorem shellVerts_subset_V {S : Type} [TopologicalSpace S] [T2Space S]
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (hSh : ShellDiscData D d C Δ) (k : ℕ) :
    shellVerts D d C k ⊆ D.V :=
  union_subset (innerDraw_spec D d C).1.1 (iUnion₂_subset fun j _ => (hSh.isSubdrawing j).1)

theorem shellGraph_le {S : Type} [TopologicalSpace S] [T2Space S]
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (hSh : ShellDiscData D d C Δ) (k : ℕ) :
    shellGraph D d C k ≤ D.toGraph :=
  Graph.induce_le (shellVerts_subset_V hSh k)

/-- Outward shell induction invariant at step `k < d`. -/
def ShellStepInv {S : Type} [TopologicalSpace S] [T2Space S]
    (D : Drawing S) (d : ℕ) (C : Fin d → Drawing S) (k : ℕ) (hk : k < d) : Prop :=
  let j_cur : Fin d := ⟨d - 1 - k, by omega⟩
  ∃ (cyc : CircuitCycle (C j_cur).toGraph (C j_cur).V.ncard)
    (φ : Circle ≃ₜ (C j_cur).U)
    (θ_v : Fin (C j_cur).V.ncard → ℝ)
    (lam : ℕ),
    StrictMono θ_v ∧
    (∀ t, θ_v t ∈ Ico 0 (2 * Real.pi)) ∧
    (∀ t, (φ (Circle.exp (θ_v t))).1 = cyc.u t) ∧
    (∀ θ ∈ Ico 0 (2 * Real.pi), (φ (Circle.exp θ)).1 ∈ (C j_cur).V → ∃ t, θ = θ_v t) ∧
    HasCyclicModel (shellGraph D d C k) (C j_cur).toGraph cyc (k + 1) lam

end ShellGluing

end GraphMinor.GM03
