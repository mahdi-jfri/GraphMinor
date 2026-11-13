module

public import GraphMinor.GM03.Section2e
import GraphMinor.GM11.RadialExists
import GraphMinor.GM11.Section81
import GraphMinor.GM11.NiceStatements
import GraphMinor.GM11.SphereRegion
import GraphMinor.GM11.Theorem75
import GraphMinor.GM11.Separate

/-!
# Graph Minors III, Claim (2) and Inductive Completion of `(2.2)`

This file completes the proof of **Graph Minors III, (2.2)** (pages 52–54) of
N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64:
- `lemma_2_2_claim_2`: Claim `(2)` of `(2.2)` (page 53), adding a collar chord across a repeated
  perimeter vertex when `B = perimDraw (innerDraw D d' C) R_N` is connected (`|B.V| ≥ 3`) and not a
  circuit.
- `exists_surfaceDShell_circuit`: combining condition `(v)` (`|E(H)|` maximum), Claim `(1)`, and
  Claim `(2)` so that `perimDraw (innerDraw D' d' C) R_N'` is a circuit.
- `exists_surfaceDShell_step`: subdividing chords of the new perimeter circuit `C_{d'}` to extend
  a `SurfaceDShell` of depth `d' < d` to depth `d' + 1`.
- `exists_dShell_le`: the full inductive construction of a `d'`-shell for all `d' ≤ d`, eliminating
  `hShellStep`.
-/

@[expose] public section

namespace GraphMinor.GM03

open Function Topology Classical Filter unitInterval
open Graph SimpleGraph Set
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11
open GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22

universe u v

variable {α : Type u} {β : Type v}

/-- A subgraph of a simple graph is simple. -/
theorem Simple.mono {G H : Graph α β} (hG : G.Simple) (hle : H ≤ G) : H.Simple where
  not_isLoopAt e x hloop := hG.not_isLoopAt e x (Graph.IsLink.mono hle hloop)
  eq_of_isLink _ _ _ _ hl₁ hl₂ :=
    hG.eq_of_isLink (Graph.IsLink.mono hle hl₁) (Graph.IsLink.mono hle hl₂)

section ShellStep

variable {S : Type} [TopologicalSpace S]

/-- **Claim (2) of (2.2)** (Graph Minors III, Section 2, page 53):
"(2) *$C_{d'}$ is a circuit.*"
If `d' < d`, `SurfaceDShell D r₀ d' C Δ`, `HasAtMostOneOuterEdge D d' C`, `D.toGraph.Simple`,
`HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem) d`,
`R_N ∈ (innerDraw D d' C).R`, `r₀ ⊆ R_N`, `3 ≤ (perimDraw (innerDraw D d' C) R_N).V.ncard`,
`IsGraphConnected (perimDraw (innerDraw D d' C) R_N).toGraph`, and
`¬ (perimDraw (innerDraw D d' C) R_N).IsCircuit`, then an edge can be added inside a region
`q ∈ D.R` (`q ⊆ R_N`) between the two neighbours along the perimeter walk of a repeated vertex
so that all inductive invariants hold and `|(innerDraw D' d' C).E| = |(innerDraw D d' C).E| + 1`. -/
theorem lemma_2_2_claim_2 [ConnectedSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {r₀ R_N : Set S} {d d' : ℕ}
    {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hd'd : d' < d)
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hOuter : HasAtMostOneOuterEdge D d' C)
    (hSimple : D.toGraph.Simple)
    (hrad : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem) d)
    (hRN : R_N ∈ (innerDraw D d' C).R) (hr₀_sub : r₀ ⊆ R_N)
    (hcard3 : 3 ≤ (perimDraw (innerDraw D d' C) R_N).V.ncard)
    (hConn : IsGraphConnected (perimDraw (innerDraw D d' C) R_N).toGraph)
    (hNotCirc : ¬ (perimDraw (innerDraw D d' C) R_N).IsCircuit) :
    ∃ (D' : Drawing S) (r₀' R_N' : Set S) (hr₀' : r₀' ∈ D'.R),
      SurfaceDShell D' r₀' d' C Δ ∧
      HasAtMostOneOuterEdge D' d' C ∧
      D'.toGraph.Simple ∧
      IsIsoMinor D.toGraph D'.toGraph ∧
      HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d ∧
      R_N' ∈ (innerDraw D' d' C).R ∧
      r₀' ⊆ R_N' ∧
      3 ≤ (perimDraw (innerDraw D' d' C) R_N').V.ncard ∧
      (innerDraw D' d' C).V = (innerDraw D d' C).V ∧
      (innerDraw D' d' C).E.ncard = (innerDraw D d' C).E.ncard + 1 := by
  let N := innerDraw D d' C
  let B := perimDraw N R_N
  obtain ⟨hNs, hNV, hNE, _⟩ := innerDraw_spec D d' C
  obtain ⟨hBs, hBV, hBE, hBU_fr, hB_le_N⟩ := perimDraw_spec hS hRN
  have hBDs : B.IsSubdrawing D := ⟨hBs.1.trans hNs.1, fun e he => hNs.2 (hBs.2 he)⟩
  obtain ⟨hBE_ne, hB_two⟩ := isTwoCell_and_E_nonempty_of_connected hS hSph hConn hcard3
  obtain ⟨Γ', htwo_B, hpre_B, hmax_B⟩ := GM11.exists_radialDrawing hS hB_two
  have hrad_B : GM11.PreRad (PaintingOrDrawing.drawing B) Γ' := ⟨htwo_B, hpre_B⟩
  have hRN_B : R_N ∈ B.R := region_mem_perimDraw hS hRN
  have hB_loop := noLoop_of_simple_subdrawing hSimple hBDs
  obtain ⟨n, v₀, a₀, s₀, P₀, ε₀, h₀, hc₀⟩ :=
    GM11.exists_hub_collar hrad_B hS hmax_B hSph hBE_ne hB_loop hRN_B
  obtain ⟨i, j, hij, hj_lt, hv_ij⟩ :=
    exists_repeated_vertex_of_not_isCircuit hS hRN hSimple hBDs hcard3 hNotCirc hc₀
  have hi_lt : i < n := hij.trans hj_lt
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hc₀.pos
  have hv₀_bot : ∀ k < n, h₀ (GM11.circlePt ((k : ℝ) / n), 0) = v₀ k := by
    intro k hk
    simpa [GM11.circlePt] using (hc₀.bottom k hk 0).trans (hc₀.ε_zero k)
  have hzi_ne_zj : GM11.circlePt ((i : ℝ) / n) ≠ GM11.circlePt ((j : ℝ) / n) := by
    intro heq
    have hi_Ico : (i : ℝ) / n ∈ Ico (0 : ℝ) (0 + 1) :=
      ⟨by positivity, by
        rw [zero_add, div_lt_iff₀ hn_pos]
        linarith [show (i : ℝ) < n by exact_mod_cast hi_lt]⟩
    have hj_Ico : (j : ℝ) / n ∈ Ico (0 : ℝ) (0 + 1) :=
      ⟨by positivity, by
        rw [zero_add, div_lt_iff₀ hn_pos]
        linarith [show (j : ℝ) < n by exact_mod_cast hj_lt]⟩
    have hdiv := GM11.circlePt_injOn hi_Ico hj_Ico heq
    have : (i : ℝ) = j := (div_left_inj' hn_pos.ne').mp hdiv
    exact hij.ne (Nat.cast_injective this)
  have hgood_ex : ∃ i₀ j₀, i₀ < n ∧ j₀ < n ∧ i₀ ≠ j₀ ∧ v₀ i₀ = v₀ j₀ ∧
      (GM11.circlePt ((i₀ : ℝ) / n), (0 : I)) ∉
        closure {p : Circle × I | 0 < p.2 ∧ h₀ p ∈ D.U} := by
    by_cases hbad_i :
        (GM11.circlePt ((i : ℝ) / n), (0 : I)) ∈
          closure {p : Circle × I | 0 < p.2 ∧ h₀ p ∈ D.U}
    · refine ⟨j, i, hj_lt, hi_lt, hij.ne', hv_ij.symm, fun hbad_j => hzi_ne_zj ?_⟩
      exact (bad_collar_vertex_subsingleton hS hShell hOuter hSimple hRN hc₀).2
        (v₀ i) (hc₀.vertex i) ⟨hv₀_bot i hi_lt, hbad_i⟩
        ⟨(hv₀_bot j hj_lt).trans hv_ij.symm, hbad_j⟩
    · exact ⟨i, j, hi_lt, hj_lt, hij.ne, hv_ij, hbad_i⟩
  obtain ⟨i₀, j₀, hi₀_lt, hj₀_lt, hij₀_ne, hv_i₀j₀, hgood_i₀⟩ := hgood_ex
  let k_shift : ℕ := i₀ + n - 1
  obtain ⟨h, hc, hh_eq⟩ := isHubCollar_shift_iter hc₀ k_shift
  let v := fun m => v₀ (m + k_shift)
  let a := fun m => a₀ (m + k_shift)
  let s := fun m => s₀ (m + k_shift)
  let P := fun m => P₀ (m + k_shift)
  let ε := fun m => ε₀ (m + k_shift)
  change IsHubCollar B Γ' (GM11.radialUnion hrad_B) R_N n v a s P ε h at hc
  have hv1_eq : v 1 = v₀ i₀ := by
    change v₀ (1 + k_shift) = v₀ i₀
    have : 1 + k_shift = i₀ + n := by omega
    rw [this, hc₀.per_v]
  let j₁ : ℕ := (j₀ + n - i₀ + 1) % n
  have hj₁_lt : j₁ < n := Nat.mod_lt _ hc.pos
  have hj₁_mod : (j₁ + k_shift) % n = j₀ := by
    have hsum : j₀ + n - i₀ + 1 + k_shift = j₀ + 2 * n := by omega
    calc (j₁ + k_shift) % n
      _ = (j₀ + n - i₀ + 1 + k_shift) % n := Nat.mod_add_mod _ _ _
      _ = (j₀ + n * 2) % n := by rw [hsum, mul_comm]
      _ = j₀ % n := Nat.add_mul_mod_self_left j₀ n 2
      _ = j₀ := Nat.mod_eq_of_lt hj₀_lt
  have hv_j₁ : v j₁ = v 1 := by
    rw [hv1_eq, hv_i₀j₀]
    change v₀ (j₁ + k_shift) = v₀ j₀
    rw [← IsHubCollar.mod_eq hc₀.per_v (j₁ + k_shift), hj₁_mod]
  have hj₁_ne1 : j₁ ≠ 1 := by
    intro h1
    apply hij₀_ne
    have h1_mod : (1 + k_shift) % n = i₀ := by
      have : 1 + k_shift = i₀ + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi₀_lt]
    rw [← h1_mod, ← h1, hj₁_mod]
  have hj₁_ge3 : 3 ≤ j₁ := by
    by_contra hlt3
    interval_cases j₁
    · exact hc.ne 0 hv_j₁
    · exact hj₁_ne1 rfl
    · exact hc.ne 1 hv_j₁.symm
  have hGood : (GM11.circlePt (1 / (n : ℝ)), (0 : I)) ∉
      closure {p : Circle × I | 0 < p.2 ∧ h p ∈ D.U} := by
    intro hbad
    let rot : Circle × I → Circle × I :=
      fun p => (p.1 * Circle.exp (2 * Real.pi * ((k_shift : ℝ) / n)), p.2)
    have hrot_cont : Continuous rot :=
      (continuous_fst.mul continuous_const).prodMk continuous_snd
    have hrot_map : rot '' {p : Circle × I | 0 < p.2 ∧ h p ∈ D.U} ⊆
        {q : Circle × I | 0 < q.2 ∧ h₀ q ∈ D.U} := by
      rintro _ ⟨p, ⟨hp_pos, hp_DU⟩, rfl⟩
      refine ⟨hp_pos, ?_⟩
      rw [← hh_eq p.1 p.2]
      exact hp_DU
    have hrot_1n : rot (GM11.circlePt (1 / (n : ℝ)), 0) =
        (GM11.circlePt ((i₀ : ℝ) / n), 0) := by
      ext : 1
      · change Circle.exp (2 * Real.pi * (1 / (n : ℝ))) *
          Circle.exp (2 * Real.pi * ((k_shift : ℝ) / n)) =
          Circle.exp (2 * Real.pi * ((i₀ : ℝ) / n))
        rw [← Circle.exp_add]
        have hk_eq : (1 : ℝ) + (k_shift : ℝ) = (i₀ : ℝ) + (n : ℝ) := by
          exact_mod_cast (show 1 + k_shift = i₀ + n by omega)
        have harg : 2 * Real.pi * (1 / (n : ℝ)) + 2 * Real.pi * ((k_shift : ℝ) / n) =
            2 * Real.pi * ((i₀ : ℝ) / n) + 2 * Real.pi := by
          calc 2 * Real.pi * (1 / (n : ℝ)) + 2 * Real.pi * ((k_shift : ℝ) / n)
            _ = 2 * Real.pi * ((1 + (k_shift : ℝ)) / n) := by ring
            _ = 2 * Real.pi * (((i₀ : ℝ) + n) / n) := by rw [hk_eq]
            _ = 2 * Real.pi * ((i₀ : ℝ) / n + n / n) := by ring
            _ = 2 * Real.pi * ((i₀ : ℝ) / n + 1) := by rw [div_self hn_pos.ne']
            _ = 2 * Real.pi * ((i₀ : ℝ) / n) + 2 * Real.pi := by ring
        rw [harg, Circle.exp_add, Circle.exp_two_pi, mul_one]
      · rfl
    have hmem_i₀ := closure_mono hrot_map
      (image_closure_subset_closure_image hrot_cont ⟨_, hbad, hrot_1n⟩)
    exact hgood_i₀ hmem_i₀
  let N₁ := compSubdraw N (v 1)
  have hv1_NV : v 1 ∈ N.V := hBs.1 (hc.vertex 1)
  obtain ⟨hN₁s, _, hN₁V, _, hN₁E, _, hv1_N₁V, _, _, hN₁_pre⟩ := compSubdraw_spec N hv1_NV
  have hX_pc : IsPathConnected N₁.U := isPathConnected_compSubdraw_U N hv1_NV
  have hX_ne_univ : N₁.U ≠ univ := by
    obtain ⟨x₀, hx₀⟩ := GM11.region_nonempty hRN
    intro huniv
    exact GM11.region_subset hRN hx₀ (hN₁s.U_subset (huniv ▸ mem_univ x₀))
  obtain ⟨A, hA_disc, hX_sub_A⟩ :=
    GM11.exists_openDisc_of_sphere hS hSph N₁.isClosed_U hN₁_pre hX_ne_univ
  have hBV_sub_N₁V : B.V ⊆ N₁.V := by
    have hwalk_le : ∀ {u w : S}, GraphWalk B.toGraph u w → Nonempty (GraphWalk N.toGraph u w) := by
      intro u w W
      induction W with
      | nil hu => exact ⟨GraphWalk.nil (hB_le_N.1 hu)⟩
      | cons hl _ ih =>
        obtain ⟨W'⟩ := ih
        exact ⟨GraphWalk.cons (hB_le_N.2 hl) W'⟩
    rw [hN₁V]
    intro u hu
    obtain ⟨W_B⟩ := hConn.2 (v 1) (hc.vertex 1) u hu
    exact ⟨hBs.1 hu, hwalk_le W_B⟩
  have hBU_sub_X : B.U ⊆ N₁.U := by
    rw [B.U_eq]
    refine union_subset (hBV_sub_N₁V.trans N₁.V_subset_U) (iUnion₂_subset fun e heB => ?_)
    have he_N₁ : e ∈ N₁.E := by
      rw [hN₁E]
      refine ⟨hBs.2 heB, ?_⟩
      rw [← hBs.closure_inter_V heB, ← hN₁V]
      exact inter_subset_right.trans hBV_sub_N₁V
    exact N₁.closure_subset_U he_N₁
  have hbot_X : ∀ z : Circle, h (z, 0) ∈ N₁.U := by
    intro z
    apply hBU_sub_X
    change (perimDraw N R_N).U _
    rw [hBU_fr, ← hc.range_bottom]
    exact mem_range_self z
  have hoff_X : ∀ p : Circle × I, 0 < p.2 → h p ∉ N₁.U :=
    fun p hp hx => GM11.region_subset hRN (hc.mem_r p hp) (hN₁s.U_subset hx)
  have h_s1 : h (GM11.circlePt (1 / (n : ℝ)), 0) = v 1 := by
    simpa [GM11.circlePt] using (hc.bottom 1 (by omega) 0).trans (hc.ε_zero 1)
  have h_s2 : h (GM11.circlePt (2 / (n : ℝ)), 0) = v 2 := by
    simpa [GM11.circlePt] using (hc.bottom 2 (by omega) 0).trans (hc.ε_zero 2)
  have h_s3 : h (GM11.circlePt ((j₁ : ℝ) / n), 0) = v 1 := by
    simpa [GM11.circlePt, hv_j₁] using (hc.bottom j₁ hj₁_lt 0).trans (hc.ε_zero j₁)
  have h_s4 : h (GM11.circlePt (1 : ℝ), 0) = v 0 := by
    have h10 : GM11.circlePt (1 : ℝ) = GM11.circlePt ((0 : ℝ) / n) := by
      simp [GM11.circlePt, Circle.exp_two_pi]
    rw [h10]
    simpa [GM11.circlePt] using (hc.bottom 0 hc.pos 0).trans (hc.ε_zero 0)
  have hs₁₂ : (1 : ℝ) / n ≤ 2 / n := (div_le_div_iff_of_pos_right hn_pos).mpr (by norm_num)
  have hs₂₃ : (2 : ℝ) / n ≤ (j₁ : ℝ) / n :=
    (div_le_div_iff_of_pos_right hn_pos).mpr (by exact_mod_cast (by omega : 2 ≤ j₁))
  have hs₃₄ : (j₁ : ℝ) / n ≤ 1 := by
    rw [div_le_iff₀ hn_pos]
    linarith [show (j₁ : ℝ) ≤ n by exact_mod_cast hj₁_lt.le]
  have hs₄₁ : (1 : ℝ) ≤ 1 / n + 1 := by linarith [div_pos zero_lt_one hn_pos]
  have hv1_sub_X : ({v 1} : Set S) ⊆ N₁.U :=
    singleton_subset_iff.mpr (N₁.V_subset_U hv1_N₁V)
  have hv02 : v 0 ≠ v 2 := by
    intro heq
    have hv2_sub_X : ({v 2} : Set S) ⊆ N₁.U :=
      singleton_subset_iff.mpr (N₁.V_subset_U (hBV_sub_N₁V (hc.vertex 2)))
    obtain ⟨w, hw1, hw2⟩ :=
      GM11.theorem_8_1_proof hS hA_disc hX_sub_A hX_pc hc.injOn hoff_X hbot_X
        hs₁₂ hs₂₃ hs₃₄ hs₄₁
        (isPathConnected_singleton (v 1)) (isPathConnected_singleton (v 2))
        hv1_sub_X hv2_sub_X h_s1 h_s3 h_s2 (h_s4.trans heq)
    rw [mem_singleton_iff] at hw1 hw2
    exact hc.ne 1 (hw1.symm.trans hw2)
  have hnotAdj : ¬ D.toGraph.Adj (v 0) (v 2) := by
    rintro ⟨e, hl⟩
    have he_N₁ : e ∈ N₁.E := by
      rw [hN₁E]
      have he_N : e ∈ N.E := by
        rw [hNE]
        refine ⟨hl.1, ?_⟩
        rw [hl.2.2.2, ← hNV]
        rintro x (rfl | rfl)
        · exact hBs.1 (hc.vertex 0)
        · exact hBs.1 (hc.vertex 2)
      refine ⟨he_N, ?_⟩
      rw [hNs.closure_inter_V he_N, hl.2.2.2, ← hN₁V]
      rintro x (rfl | rfl)
      · exact hBV_sub_N₁V (hc.vertex 0)
      · exact hBV_sub_N₁V (hc.vertex 2)
    have hcl_pc : IsPathConnected (closure e) := GM11.isPathConnected_closure_edge he_N₁
    have hcl_sub_X : closure e ⊆ N₁.U := N₁.closure_subset_U he_N₁
    have hv0_cle : v 0 ∈ closure e :=
      (hl.2.2.2.symm ▸ mem_insert (v 0) {v 2} : v 0 ∈ closure e ∩ D.V).1
    have hv2_cle : v 2 ∈ closure e :=
      (hl.2.2.2.symm ▸ mem_insert_of_mem (v 0) rfl : v 2 ∈ closure e ∩ D.V).1
    obtain ⟨w, hw1, hwe⟩ :=
      GM11.theorem_8_1_proof hS hA_disc hX_sub_A hX_pc hc.injOn hoff_X hbot_X
        hs₁₂ hs₂₃ hs₃₄ hs₄₁
        (isPathConnected_singleton (v 1)) hcl_pc
        hv1_sub_X hcl_sub_X h_s1 h_s3
        (h_s2.symm ▸ hv2_cle) (h_s4.symm ▸ hv0_cle)
    rw [mem_singleton_iff] at hw1
    subst hw1
    have hv1_DV : v 1 ∈ D.V := hNs.1 hv1_NV
    have hv1_cap : v 1 ∈ ({v 0, v 2} : Set S) := hl.2.2.2 ▸ ⟨hwe, hv1_DV⟩
    rcases hv1_cap with h0 | h2
    · exact hc.ne 0 h0.symm
    · exact hc.ne 1 (mem_singleton_iff.mp h2)
  obtain ⟨K, q, hK, hq, hKq, hq_RN, hq_int, R_N', hRN', hRN'_sub, hRN_sdiff_sub, hPV_sub⟩ :=
    exists_collar_chord_of_good_corner hS hShell hOuter hSimple hRN hc
      hj₁_ge3 hj₁_lt hv_j₁ hGood hv02
  have hv₀_D : v 0 ∈ D.V := hNs.1 (hBs.1 (hc.vertex 0))
  have hv₂_D : v 2 ∈ D.V := hNs.1 (hBs.1 (hc.vertex 2))
  let D' := D.glue (GM11.lineDrawing hK hv02)
    (lineDrawing_meet_of_subset_region hq hv₀_D hv₂_D hK hv02 hKq)
  obtain ⟨r₀', hr₀', hOut⟩ :=
    addChordInRegion_spec hS hSph hd'd hShell hOuter hSimple hrad hRN hr₀_sub hcard3
      hq hq_RN hq_int (hc.vertex 0) (hc.vertex 2) hv02 hnotAdj hK hKq hv₀_D hv₂_D
      hRN' hRN'_sub hRN_sdiff_sub hPV_sub
  exact ⟨D', r₀', R_N', hr₀', hOut⟩

/-- In a simple drawing `N`, the number of edges is at most `|N.V|^2`. -/
theorem ncard_E_le_sq_of_simple [T2Space S] {N : Drawing S} (hSimple : N.toGraph.Simple) :
    N.E.ncard ≤ N.V.ncard * N.V.ncard := by
  have hEnds : ∀ e : N.E, ∃ p : S × S, p.1 ≠ p.2 ∧ closure e.1 ∩ N.V = {p.1, p.2} := by
    intro ⟨e, he⟩
    obtain ⟨u, v, huv, hcap⟩ := noLoop_of_simple_subdrawing hSimple ⟨Subset.rfl, Subset.rfl⟩ e he
    exact ⟨(u, v), huv, hcap⟩
  rcases N.E.eq_empty_or_nonempty with hE0 | ⟨e₀, he₀⟩
  · rw [hE0, ncard_empty]
    exact Nat.zero_le _
  · obtain ⟨u₀, _, _, hcap₀⟩ := noLoop_of_simple_subdrawing hSimple ⟨Subset.rfl, Subset.rfl⟩ e₀ he₀
    let ψ : Set S → S × S := fun e =>
      if he : e ∈ N.E then (hEnds ⟨e, he⟩).choose else (u₀, u₀)
    have hψ_mem : ∀ e ∈ N.E, ψ e ∈ N.V ×ˢ N.V := by
      intro e he
      have hψ_eq : ψ e = (hEnds ⟨e, he⟩).choose := by dsimp only [ψ]; simp only [he, ↓reduceDIte]
      have hcap := (hEnds ⟨e, he⟩).choose_spec.2
      rw [hψ_eq]
      set q := (hEnds ⟨e, he⟩).choose
      have h1 : q.1 ∈ closure e ∩ N.V := hcap.symm ▸ mem_insert q.1 {q.2}
      have h2 : q.2 ∈ closure e ∩ N.V := hcap.symm ▸ mem_insert_of_mem q.1 rfl
      exact ⟨h1.2, h2.2⟩
    have hψ_inj : InjOn ψ N.E := by
      intro e₁ he₁ e₂ he₂ heq
      have h1 : ψ e₁ = (hEnds ⟨e₁, he₁⟩).choose := by dsimp only [ψ]; simp only [he₁, ↓reduceDIte]
      have h2 : ψ e₂ = (hEnds ⟨e₂, he₂⟩).choose := by dsimp only [ψ]; simp only [he₂, ↓reduceDIte]
      rw [h1, h2] at heq
      have hcap₁ := (hEnds ⟨e₁, he₁⟩).choose_spec.2
      have hcap₂ := (hEnds ⟨e₂, he₂⟩).choose_spec.2
      set p := (hEnds ⟨e₁, he₁⟩).choose
      have hp1 : p.1 ∈ N.V := (hcap₁.symm ▸ mem_insert p.1 {p.2} : p.1 ∈ closure e₁ ∩ N.V).2
      have hp2 : p.2 ∈ N.V := (hcap₁.symm ▸ mem_insert_of_mem p.1 rfl : p.2 ∈ closure e₁ ∩ N.V).2
      have hcap₂' : closure e₂ ∩ N.V = {p.1, p.2} := by
        rw [hcap₂, ← heq]
      exact hSimple.eq_of_isLink ⟨he₁, hp1, hp2, hcap₁⟩ ⟨he₂, hp1, hp2, hcap₂'⟩
    have hfin_prod : (N.V ×ˢ N.V).Finite := N.finite_V.prod N.finite_V
    calc N.E.ncard
      _ ≤ (N.V ×ˢ N.V).ncard := ncard_le_ncard_of_injOn ψ hψ_mem hψ_inj hfin_prod
      _ = N.V.ncard * N.V.ncard := ncard_prod

/-- Condition **(v)** + Claims **(1)** and **(2)** of `(2.2)` (page 53):
starting from `D` satisfying `SurfaceDShell`, `HasAtMostOneOuterEdge`, and `3 ≤ |B.V|`, repeatedly
adding chords in `R_N` (keeping `N.V` fixed and increasing `|N.E|` by `1` at each step while `N`
remains simple) produces a drawing `D'` whose perimeter `perimDraw (innerDraw D' d' C) R_N'` is a
circuit. -/
theorem exists_surfaceDShell_circuit [ConnectedSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {r₀ R_N : Set S} {d d' : ℕ}
    {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hd'd : d' < d)
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hOuter : HasAtMostOneOuterEdge D d' C)
    (hSimple : D.toGraph.Simple)
    (hrad : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem) d)
    (hRN : R_N ∈ (innerDraw D d' C).R) (hr₀_sub : r₀ ⊆ R_N)
    (hcard3 : 3 ≤ (perimDraw (innerDraw D d' C) R_N).V.ncard) :
    ∃ (D' : Drawing S) (r₀' R_N' : Set S) (hr₀' : r₀' ∈ D'.R),
      SurfaceDShell D' r₀' d' C Δ ∧
      HasAtMostOneOuterEdge D' d' C ∧
      D'.toGraph.Simple ∧
      IsIsoMinor D.toGraph D'.toGraph ∧
      HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d ∧
      R_N' ∈ (innerDraw D' d' C).R ∧
      r₀' ⊆ R_N' ∧
      (perimDraw (innerDraw D' d' C) R_N').IsCircuit := by
  have h_aux : ∀ (rem : ℕ) (D₁ : Drawing S) (r₀₁ R_N₁ : Set S),
      ∀ (hSh₁ : SurfaceDShell D₁ r₀₁ d' C Δ),
        HasAtMostOneOuterEdge D₁ d' C →
        D₁.toGraph.Simple →
        HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D₁ r₀₁ hSh₁.r₀_mem) d →
        R_N₁ ∈ (innerDraw D₁ d' C).R →
        r₀₁ ⊆ R_N₁ →
        3 ≤ (perimDraw (innerDraw D₁ d' C) R_N₁).V.ncard →
        (innerDraw D₁ d' C).V.ncard * (innerDraw D₁ d' C).V.ncard + 1 -
          (innerDraw D₁ d' C).E.ncard ≤ rem →
        ∃ (D' : Drawing S) (r₀' R_N' : Set S) (hr₀' : r₀' ∈ D'.R),
          SurfaceDShell D' r₀' d' C Δ ∧
          HasAtMostOneOuterEdge D' d' C ∧
          D'.toGraph.Simple ∧
          IsIsoMinor D₁.toGraph D'.toGraph ∧
          HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d ∧
          R_N' ∈ (innerDraw D' d' C).R ∧
          r₀' ⊆ R_N' ∧
          (perimDraw (innerDraw D' d' C) R_N').IsCircuit := by
    intro rem
    induction rem with
    | zero =>
      intro D₁ r₀₁ R_N₁ _ _ hSim₁ _ _ _ _ hrem
      have hN₁_sim : (innerDraw D₁ d' C).toGraph.Simple :=
        Simple.mono hSim₁ (innerDraw_spec D₁ d' C).2.2.2
      have hbound := ncard_E_le_sq_of_simple hN₁_sim
      omega
    | succ rem ih =>
      intro D₁ r₀₁ R_N₁ hSh₁ hOut₁ hSim₁ hRad₁ hRN₁ hr₀₁_sub hcard₁ hrem
      have hN₁_sim : (innerDraw D₁ d' C).toGraph.Simple :=
        Simple.mono hSim₁ (innerDraw_spec D₁ d' C).2.2.2
      have hbound := ncard_E_le_sq_of_simple hN₁_sim
      by_cases hConn : IsGraphConnected (perimDraw (innerDraw D₁ d' C) R_N₁).toGraph
      · by_cases hCirc : (perimDraw (innerDraw D₁ d' C) R_N₁).IsCircuit
        · exact ⟨D₁, r₀₁, R_N₁, hSh₁.r₀_mem, hSh₁, hOut₁, hSim₁,
            IsIsoMinor.refl D₁.toGraph, hRad₁, hRN₁, hr₀₁_sub, hCirc⟩
        · obtain ⟨D₂, r₀₂, R_N₂, _, hSh₂, hOut₂, hSim₂, hMin₂, hRad₂, hRN₂, hr₀₂_sub,
              hcard₂, hV_eq, hE_eq⟩ :=
            lemma_2_2_claim_2 hS hSph hd'd hSh₁ hOut₁ hSim₁ hRad₁ hRN₁ hr₀₁_sub hcard₁ hConn hCirc
          have hrem₂ : (innerDraw D₂ d' C).V.ncard * (innerDraw D₂ d' C).V.ncard + 1 -
              (innerDraw D₂ d' C).E.ncard ≤ rem := by
            rw [hV_eq, hE_eq]
            omega
          obtain ⟨D', r₀', R_N', hr₀', hSh', hOut', hSim', hMin', hRad', hRN', hr₀'_sub, hCirc'⟩ :=
            ih D₂ r₀₂ R_N₂ hSh₂ hOut₂ hSim₂ hRad₂ hRN₂ hr₀₂_sub hcard₂ hrem₂
          exact ⟨D', r₀', R_N', hr₀', hSh', hOut', hSim', hMin₂.trans hMin', hRad',
            hRN', hr₀'_sub, hCirc'⟩
      · obtain ⟨D₂, r₀₂, R_N₂, _, hSh₂, hOut₂, hSim₂, hMin₂, hRad₂, hRN₂, hr₀₂_sub,
            hcard₂, hV_eq, hE_eq⟩ :=
          lemma_2_2_claim_1 hS hSph hd'd hSh₁ hOut₁ hSim₁ hRad₁ hRN₁ hr₀₁_sub hcard₁ hConn
        have hrem₂ : (innerDraw D₂ d' C).V.ncard * (innerDraw D₂ d' C).V.ncard + 1 -
            (innerDraw D₂ d' C).E.ncard ≤ rem := by
          rw [hV_eq, hE_eq]
          omega
        obtain ⟨D', r₀', R_N', hr₀', hSh', hOut', hSim', hMin', hRad', hRN', hr₀'_sub, hCirc'⟩ :=
          ih D₂ r₀₂ R_N₂ hSh₂ hOut₂ hSim₂ hRad₂ hRN₂ hr₀₂_sub hcard₂ hrem₂
        exact ⟨D', r₀', R_N', hr₀', hSh', hOut', hSim', hMin₂.trans hMin', hRad',
          hRN', hr₀'_sub, hCirc'⟩
  exact h_aux _ D r₀ R_N hShell hOuter hSimple hrad hRN hr₀_sub hcard3 le_rfl

/-- Complement of a closed disc in a 2-sphere is preconnected. -/
theorem compl_closedDisc_isPreconnected (hS : IsClosedSurface S) (hSph : IsSphere S)
    {Δ : Set S} (hΔ : IsClosedDisc Δ) :
    IsPreconnected Δᶜ := by
  have : T2Space S := hS.2.1
  have hF : IsOArc (discBd Δ) := IsClosedDisc.isOArc_discBd hΔ
  obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap, -, huniq⟩ :=
    sphere_disc S hSph (discBd Δ) hF
  rcases huniq Δ hΔ rfl with hΔ_eq | hΔ_eq
  · have hcompl : Δᶜ = discInt Δ₂ := by
      refine Subset.antisymm (fun x hx => ?_) (fun x hx hxΔ => hx.2 ?_)
      · rcases (hcup ▸ mem_univ x : x ∈ Δ₁ ∪ Δ₂) with hx₁ | hx₂
        · exact (hx (hΔ_eq ▸ hx₁)).elim
        · refine ⟨hx₂, fun hbd => hx ?_⟩
          rw [hb₂, ← hcap, ← hΔ_eq] at hbd
          exact hbd.1
      · rw [hb₂, ← hcap]
        exact ⟨hΔ_eq ▸ hxΔ, hx.1⟩
    rw [hcompl]
    exact hΔ₂.isPreconnected_discInt
  · have hcompl : Δᶜ = discInt Δ₁ := by
      refine Subset.antisymm (fun x hx => ?_) (fun x hx hxΔ => hx.2 ?_)
      · rcases (hcup ▸ mem_univ x : x ∈ Δ₁ ∪ Δ₂) with hx₁ | hx₂
        · refine ⟨hx₁, fun hbd => hx ?_⟩
          rw [hb₁, ← hcap, ← hΔ_eq] at hbd
          exact hbd.2
        · exact (hx (hΔ_eq ▸ hx₂)).elim
      · rw [hb₁, ← hcap]
        exact ⟨hx.1, hΔ_eq ▸ hxΔ⟩
    rw [hcompl]
    exact hΔ₁.isPreconnected_discInt

/-- Single inductive step of `(2.2)` (pages 52–54):
extending `SurfaceDShell D r₀ d' C Δ` (`d' < d`) to `SurfaceDShell D' r₀' (d' + 1) C' Δ'` while
preserving simplicity, minor inclusion, and `HasDrawingRadiusLE _ d`. -/
theorem exists_surfaceDShell_step [ConnectedSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {r₀ : Set S} {d d' : ℕ}
    {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hd'd : d' < d)
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hSimple : D.toGraph.Simple)
    (hrad : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem) d) :
    ∃ (D' : Drawing S) (r₀' : Set S) (hr₀' : r₀' ∈ D'.R)
      (C' : Fin (d' + 1) → Drawing S) (Δ' : Fin (d' + 1) → Set S),
      SurfaceDShell D' r₀' (d' + 1) C' Δ' ∧
      D'.toGraph.Simple ∧
      IsIsoMinor D.toGraph D'.toGraph ∧
      HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d := by
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  -- Step (iv): achieve `HasAtMostOneOuterEdge`.
  obtain ⟨D₁, _, hSh₁, hOut₁, hSim₁, hMin₁, hRad₁⟩ :=
    exists_surfaceDShell_step_iv hS hSph hShell hSimple hrad
  -- Step (iii): ensure at least 3 vertices on `perimDraw (innerDraw _ d' C) R_N`.
  obtain ⟨D₂, r₀₂, R_N₂, _, hSh₂, hOut₂, hSim₂, hMin₂, hRad₂, hRN₂, hr₀₂_sub, hcard₂⟩ :=
    exists_surfaceDShell_step_iii hS hSph hSh₁ hOut₁ hSim₁ hRad₁
  -- Step (v) + Claims (1) and (2): add chords until the outer perimeter `B` is a circuit.
  obtain ⟨D₃, r₀₃, R_N₃, _, hSh₃, _, hSim₃, hMin₃, hRad₃, hRN₃, hr₀₃_sub, hCirc⟩ :=
    exists_surfaceDShell_circuit hS hSph hd'd hSh₂ hOut₂ hSim₂ hRad₂ hRN₂ hr₀₂_sub hcard₂
  let N₃ := innerDraw D₃ d' C
  let B := perimDraw N₃ R_N₃
  obtain ⟨hN₃s, hN₃V, hN₃E, _⟩ := innerDraw_spec D₃ d' C
  obtain ⟨hBs, hBV, hBE, hBU_fr, _⟩ := perimDraw_spec hS hRN₃
  have hBDs : B.IsSubdrawing D₃ := ⟨hBs.1.trans hN₃s.1, fun e he => hN₃s.2 (hBs.2 he)⟩
  -- Choose the closed disc `Δ_new` bounded by `B.U` missing `R_N₃`.
  have hdisj_RN₃_BU : Disjoint R_N₃ B.U :=
    Set.disjoint_left.mpr fun x hxRN hxBU => GM11.region_subset hRN₃ hxRN (hBs.U_subset hxBU)
  obtain ⟨Δ_new, hΔ_new, hbd_new, hdisj_Δ_RN₃⟩ :=
    GM11.exists_disc_missing hS hSph (GM11.IsCircuit.isOArc_U hCirc)
      (GM11.region_isPreconnected hRN₃) hdisj_RN₃_BU
  have hdisj_Δ_r₀₃ : Disjoint Δ_new r₀₃ := hdisj_Δ_RN₃.mono_right hr₀₃_sub
  -- Prove `R_N₃ = Δ_newᶜ`, hence `N₃.U ⊆ Δ_new`.
  have hRN₃_eq_compl : R_N₃ = Δ_newᶜ := by
    have hsub₁ : R_N₃ ⊆ Δ_newᶜ := fun x hxRN hxΔ => Set.disjoint_left.mp hdisj_Δ_RN₃ hxΔ hxRN
    have hcompl_pre : IsPreconnected Δ_newᶜ := compl_closedDisc_isPreconnected hS hSph hΔ_new
    have hcov : Δ_newᶜ ⊆ R_N₃ ∪ (Δ_new ∪ closure R_N₃)ᶜ := by
      intro x hx_not_Δ
      by_cases hxRN : x ∈ R_N₃
      · exact Or.inl hxRN
      · refine Or.inr fun hx_un => ?_
        rcases hx_un with hxΔ | hxcl
        · exact hx_not_Δ hxΔ
        · have hx_fr : x ∈ frontier R_N₃ :=
            ⟨hxcl, by rw [(GM11.region_isOpen hRN₃).interior_eq]; exact hxRN⟩
          have hx_BU : x ∈ discBd Δ_new := hbd_new.trans hBU_fr |>.symm ▸ hx_fr
          exact hx_not_Δ (GM11.discBd_subset Δ_new hx_BU)
    have hdisj_open : Disjoint R_N₃ (Δ_new ∪ closure R_N₃)ᶜ :=
      Set.disjoint_left.mpr fun x hxRN hnot => hnot (Or.inr (subset_closure hxRN))
    rcases hcompl_pre.subset_or_subset (GM11.region_isOpen hRN₃)
        (hΔ_new.isClosed.union isClosed_closure).isOpen_compl hdisj_open hcov with hsub₂ | hsub₂
    · exact Subset.antisymm hsub₁ hsub₂
    · obtain ⟨p₀, hp₀⟩ := GM11.region_nonempty hRN₃
      exact (hsub₂ (hsub₁ hp₀) (Or.inr (subset_closure hp₀))).elim
  have hN₃U_sub_Δ : N₃.U ⊆ Δ_new := by
    intro x hxN
    by_contra hx_not_Δ
    have hxRN : x ∈ R_N₃ := hRN₃_eq_compl.symm ▸ hx_not_Δ
    exact GM11.region_subset hRN₃ hxRN hxN
  -- Show `Δ_new ⊆ interior (Δ j)` for all `j : Fin d'`.
  have hΔ_new_sub_int : ∀ j : Fin d', Δ_new ⊆ interior (Δ j) := by
    intro j
    have hd' : 0 < d' := pos_of_gt j.2
    let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
    have hN₃U_int : N₃.U ⊆ interior (Δ j_last) := hSh₃.innerDraw_U_subset_interior hd'
    have hcompl_last : (Δ j_last)ᶜ ⊆ R_N₃ :=
      compl_disc_subset_RN hS hSph hRN₃ (GM11.region_nonempty hSh₃.r₀_mem) hr₀₃_sub
        (hSh₃.isClosedDisc j_last) (hSh₃.disjoint_inf j_last)
        (hN₃U_int.trans interior_subset)
    have hΔ_sub_last : Δ_new ⊆ Δ j_last := by
      intro x hxΔ
      by_contra hx_not
      exact Set.disjoint_left.mp hdisj_Δ_RN₃ hxΔ (hcompl_last hx_not)
    have hΔ_int_last : Δ_new ⊆ interior (Δ j_last) := by
      intro x hxΔ
      by_cases hxbd : x ∈ discBd Δ_new
      · exact hN₃U_int (hBs.U_subset (hbd_new ▸ hxbd))
      · have hx_int : x ∈ interior Δ_new :=
          (discInt_eq_interior_of_isClosedDisc hS hΔ_new) ▸ ⟨hxΔ, hxbd⟩
        exact interior_mono hΔ_sub_last hx_int
    by_cases hjeq : j = j_last
    · exact hjeq ▸ hΔ_int_last
    · have hjlt : j < j_last :=
        lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt j.2)) hjeq
      exact hΔ_int_last.trans (interior_subset.trans (hSh₃.disc_subset_interior hjlt))
  -- Every edge `e ∈ N₃.E \ B.E` lies in `interior Δ_new`.
  have hedge_N₃_int : ∀ {e : Set S}, e ∈ N₃.E → e ∉ B.E → e ⊆ interior Δ_new := by
    intro e heN he_not_B x hxe
    rw [← discInt_eq_interior_of_isClosedDisc hS hΔ_new]
    refine ⟨hN₃U_sub_Δ (N₃.closure_subset_U heN (subset_closure hxe)), fun hxbd => ?_⟩
    rw [hbd_new] at hxbd
    have hx_not_N₃V : x ∉ N₃.V := (heN.2.1 hxe).2
    have hx_not_BV : x ∉ B.V := fun hxBV => hx_not_N₃V (hBs.1 hxBV)
    obtain ⟨f, hfB, hxf⟩ := B.exists_edge_of_mem hxbd hx_not_BV
    have hef : e = f := N₃.edge_eq_of_mem heN (hBs.2 hfB) hxe hxf
    exact he_not_B (hef ▸ hfB)
  -- Subdivide chords `F` of `B` in `D₃`.
  let F : Set (Set S) := {e ∈ D₃.E \ B.E | closure e ∩ D₃.V ⊆ B.V}
  have hF_sub : F ⊆ D₃.E := fun _ he => he.1.1
  have hF_in_N₃ : ∀ {e : Set S}, e ∈ F → e ∈ N₃.E := by
    intro e ⟨⟨heD, _⟩, he_sub⟩
    rw [hN₃E]
    exact ⟨heD, hN₃V ▸ he_sub.trans hBs.1⟩
  have hF_int_new : ∀ {e : Set S}, e ∈ F → e ⊆ interior Δ_new :=
    fun heF => hedge_N₃_int (hF_in_N₃ heF) heF.1.2
  have hF_not_Ci : ∀ (i : Fin d') {e : Set S}, e ∈ F → e ∉ (C i).E := by
    intro i e heF heCi
    obtain ⟨z, hz⟩ := heCi.1
    have hz_int : z ∈ interior (Δ i) := (hΔ_new_sub_int i) (interior_subset (hF_int_new heF hz))
    rw [← discInt_eq_interior_of_isClosedDisc hS (hSh₃.isClosedDisc i)] at hz_int
    exact hz_int.2 ((hSh₃.discBd_eq i).symm ▸ (C i).closure_subset_U heCi (subset_closure hz))
  have : Nonempty S := ⟨(GM11.region_nonempty hSh₃.r₀_mem).some⟩
  obtain ⟨D₃_all, D₄, A_s, B_s, m, x_s, y_s, hp⟩ := exists_partial_split D₃ hF_sub
  let hd := hp.split
  have hR₄_eq : D₄.R = D₃.R := by
    change componentsIn (univ \ D₄.U) = componentsIn (univ \ D₃.U)
    rw [hp.U_eq]
  have hr₀₄ : r₀₃ ∈ D₄.R := hR₄_eq ▸ hSh₃.r₀_mem
  have hSim₄ : D₄.toGraph.Simple := simple_of_partialSplitData hp hSim₃
  have hMin₄ : IsIsoMinor D₃.toGraph D₄.toGraph := isIsoMinor_of_partialSplitData hp
  have hRad₄ : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D₄ r₀₃ hr₀₄) d := by
    intro R hR
    obtain ⟨k, hkd, R_seq, hR_mem, hR0, hRk, hstep⟩ := hRad₃ R (hR₄_eq ▸ hR)
    refine ⟨k, hkd, R_seq, fun j => hR₄_eq.symm ▸ hR_mem j, hR0, hRk, fun j => ?_⟩
    obtain ⟨v, hvV, hv1, hv2⟩ := hstep j
    exact ⟨v, hp.V_sub hvV, hv1, hv2⟩
  -- Shell vertex chain for vertices of `B = C' (Fin.last d')`.
  have hChain_B : ∀ u ∈ B.V,
      ∃ r_u ∈ D₃.R, u ∈ closure r_u ∧ Disjoint r_u Δ_new ∧
        ∃ k ≤ d', ∃ R_seq : Fin (k + 1) → Set S,
          (∀ m_idx, R_seq m_idx ∈ D₃.R) ∧
          R_seq ⟨0, Nat.zero_lt_succ k⟩ = r₀₃ ∧
          R_seq ⟨k, Nat.lt_succ_self k⟩ = r_u ∧
          (∀ m_idx, Disjoint (R_seq m_idx) Δ_new) ∧
          ∀ m_idx : Fin k, ∃ w ∈ D₃.V, w ∉ interior Δ_new ∧
            w ∈ closure (R_seq ⟨m_idx.1, Nat.lt_succ_of_lt m_idx.2⟩) ∧
            w ∈ closure (R_seq ⟨m_idx.1 + 1, Nat.succ_lt_succ m_idx.2⟩) := by
    intro u huB
    have hu_cl_RN₃ : u ∈ closure R_N₃ := (hBV ▸ huB).2
    have hcl_eq := closure_RN_eq_biUnion_closure_regions hS hN₃s hRN₃
    rw [hcl_eq] at hu_cl_RN₃
    simp only [mem_iUnion, exists_prop] at hu_cl_RN₃
    obtain ⟨q_u, hqu_R, hqu_RN₃, hu_cl_qu⟩ := hu_cl_RN₃
    have hqu_disj_Δ : Disjoint q_u Δ_new := (hdisj_Δ_RN₃.mono_right hqu_RN₃).symm
    by_cases hd' : 0 < d'
    · let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
      have hu_int_last : u ∈ interior (Δ j_last) :=
        hSh₃.innerDraw_U_subset_interior hd' (N₃.V_subset_U (hBs.1 huB))
      have hqu_int_last : q_u ⊆ interior (Δ j_last) := by
        obtain ⟨z, hz_int, hz_qu⟩ :=
          mem_closure_iff.mp hu_cl_qu (interior (Δ j_last)) isOpen_interior hu_int_last
        have hfr_sub : frontier (interior (Δ j_last)) ⊆ D₃.U := by
          refine frontier_interior_subset.trans ?_
          rw [GM11.IsClosedDisc.frontier_eq_discBd hS (hSh₃.isClosedDisc j_last),
            hSh₃.discBd_eq j_last]
          exact (hSh₃.isSubdrawing j_last).U_subset
        have hdisj_fr : Disjoint q_u (frontier (interior (Δ j_last))) :=
          Set.disjoint_left.mpr fun x hxq hxfr => GM11.region_subset hqu_R hxq (hfr_sub hxfr)
        have hsub_cl : q_u ⊆ closure (interior (Δ j_last)) := by
          rcases GM11.subset_or_disjoint_of_frontier isClosed_closure
              (GM11.region_isPreconnected hqu_R)
              (hdisj_fr.mono_right frontier_closure_subset) with hsub | hdisj
          · exact hsub
          · exact (Set.disjoint_left.mp hdisj hz_qu (subset_closure hz_int)).elim
        intro x hxq
        have hx_Δ : x ∈ Δ j_last :=
          closure_minimal interior_subset (hSh₃.isClosedDisc j_last).isClosed (hsub_cl hxq)
        rw [← discInt_eq_interior_of_isClosedDisc hS (hSh₃.isClosedDisc j_last)]
        refine ⟨hx_Δ, fun hx_bd => ?_⟩
        rw [hSh₃.discBd_eq j_last] at hx_bd
        exact GM11.region_subset hqu_R hxq ((hSh₃.isSubdrawing j_last).U_subset hx_bd)
      have hV_split : ∀ v ∈ D₃.V, v ∈ Δ j_last → v ∈ (C j_last).V ∨ v ∈ N₃.V := by
        intro v hvD hvΔ
        by_cases hvN : v ∈ N₃.V
        · exact Or.inr hvN
        · rw [hN₃V, Set.mem_sdiff] at hvN
          push Not at hvN
          obtain ⟨i, hvi⟩ := mem_iUnion.mp (hvN hvD)
          by_cases hij : i = j_last
          · exact Or.inl (hij ▸ hvi)
          · exfalso
            have hilt : i < j_last :=
              lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.2)) hij
            have hv_int_i : v ∈ interior (Δ i) := hSh₃.disc_subset_interior hilt hvΔ
            rw [← discInt_eq_interior_of_isClosedDisc hS (hSh₃.isClosedDisc i)] at hv_int_i
            exact hv_int_i.2 ((hSh₃.discBd_eq i).symm ▸ (C i).V_subset_U hvi)
      have hE_N₃ : ∀ e ∈ D₃.E, closure e ∩ D₃.V ⊆ N₃.V → e ∈ N₃.E :=
        fun e he hsub => hN₃E ▸ ⟨he, hN₃V ▸ hsub⟩
      obtain ⟨u_prev, hu_prev_C, hu_prev_cl⟩ :=
        region_in_RN_incident_shell hS hN₃s (hSh₃.isSubdrawing j_last) hSh₃.r₀_mem hRN₃ hr₀₃_sub
          (hSh₃.isClosedDisc j_last) (hSh₃.discBd_eq j_last) (hSh₃.disjoint_inf j_last)
          hV_split hE_N₃ hqu_R hqu_RN₃ hqu_int_last
      obtain ⟨r_prev, hr_prev_D, hu_prev_rprev, _, k₀, hk₀_le, R_seq₀, hseq₀_D, hseq₀_0,
          hseq₀_k, hseq₀_disj, hseq₀_step⟩ :=
        hSh₃.shell_vertex_chain j_last u_prev hu_prev_C
      let R_seq' : Fin (k₀ + 1 + 1) → Set S := fun m_idx =>
        if hm : m_idx.1 < k₀ + 1 then R_seq₀ ⟨m_idx.1, hm⟩ else q_u
      refine ⟨q_u, hqu_R, hu_cl_qu, hqu_disj_Δ, k₀ + 1, by omega, R_seq', ?_, ?_, ?_, ?_, ?_⟩
      · intro m_idx
        by_cases hm : m_idx.1 < k₀ + 1
        · dsimp only [R_seq']; simp only [hm, ↓reduceDIte]
          exact hseq₀_D ⟨m_idx.1, hm⟩
        · dsimp only [R_seq']; simp only [hm, ↓reduceDIte]
          exact hqu_R
      · dsimp only [R_seq']; simp only [Nat.zero_lt_succ, ↓reduceDIte]
        exact hseq₀_0
      · have hnot : ¬ (k₀ + 1 < k₀ + 1) := lt_irrefl _
        dsimp only [R_seq']; simp only [hnot, ↓reduceDIte]
      · intro m_idx
        by_cases hm : m_idx.1 < k₀ + 1
        · dsimp only [R_seq']; simp only [hm, ↓reduceDIte]
          exact (hseq₀_disj ⟨m_idx.1, hm⟩).mono_right
            ((hΔ_new_sub_int j_last).trans interior_subset)
        · dsimp only [R_seq']; simp only [hm, ↓reduceDIte]
          exact hqu_disj_Δ
      · intro m_idx
        by_cases hm : m_idx.1 < k₀
        · obtain ⟨w, hwD, hw_not_int, hw1, hw2⟩ := hseq₀_step ⟨m_idx.1, hm⟩
          have hw_not_new : w ∉ interior Δ_new :=
            fun hw_new => hw_not_int (interior_mono
              ((hΔ_new_sub_int j_last).trans interior_subset) hw_new)
          refine ⟨w, hwD, hw_not_new, ?_, ?_⟩
          · have hm1 : m_idx.1 < k₀ + 1 := Nat.lt_succ_of_lt hm
            dsimp only [R_seq']; simp only [hm1, ↓reduceDIte]
            exact hw1
          · have hm2 : m_idx.1 + 1 < k₀ + 1 := Nat.succ_lt_succ hm
            dsimp only [R_seq']; simp only [hm2, ↓reduceDIte]
            exact hw2
        · have hmk : m_idx.1 = k₀ := by omega
          have hu_prev_not_new : u_prev ∉ interior Δ_new := by
            intro hu_new
            have hu_int_j : u_prev ∈ interior (Δ j_last) :=
              (hΔ_new_sub_int j_last) (interior_subset hu_new)
            rw [← discInt_eq_interior_of_isClosedDisc hS (hSh₃.isClosedDisc j_last)] at hu_int_j
            exact hu_int_j.2 ((hSh₃.discBd_eq j_last).symm ▸ (C j_last).V_subset_U hu_prev_C)
          refine ⟨u_prev, (hSh₃.isSubdrawing j_last).1 hu_prev_C, hu_prev_not_new, ?_, ?_⟩
          · have hm1 : m_idx.1 < k₀ + 1 := by omega
            dsimp only [R_seq']; simp only [hm1, ↓reduceDIte]
            have hmk' : (⟨m_idx.1, hm1⟩ : Fin (k₀ + 1)) = ⟨k₀, Nat.lt_succ_self k₀⟩ := Fin.ext hmk
            rw [hmk', hseq₀_k]
            exact hu_prev_rprev
          · have hm2 : ¬ (m_idx.1 + 1 < k₀ + 1) := by omega
            dsimp only [R_seq']; simp only [hm2, ↓reduceDIte]
            exact hu_prev_cl
    · have hd'0 : d' = 0 := Nat.eq_zero_of_not_pos hd'
      subst hd'0
      have hN₃_eq : N₃ = D₃ := innerDraw_zero_eq D₃ C
      have hRN₃_D₃ : R_N₃ ∈ D₃.R := hN₃_eq ▸ hRN₃
      obtain ⟨z₀, hz₀⟩ := GM11.region_nonempty hqu_R
      have hqu_eq : q_u = R_N₃ := GM11.region_eq_of_mem hqu_R hRN₃_D₃ hz₀ (hqu_RN₃ hz₀)
      obtain ⟨p₀, hp₀⟩ := GM11.region_nonempty hSh₃.r₀_mem
      have hr₀₃_eq : r₀₃ = R_N₃ := GM11.region_eq_of_mem hSh₃.r₀_mem hRN₃_D₃ hp₀ (hr₀₃_sub hp₀)
      refine ⟨q_u, hqu_R, hu_cl_qu, hqu_disj_Δ, 0, le_rfl, fun _ => r₀₃,
        fun _ => hSh₃.r₀_mem, rfl, hr₀₃_eq.trans hqu_eq.symm,
        fun _ => hr₀₃_eq ▸ hdisj_Δ_RN₃.symm, fun m_idx => Fin.elim0 m_idx⟩
  -- Assemble `SurfaceDShell D₄ r₀₃ (d' + 1) (Fin.snoc C B) (Fin.snoc Δ Δ_new)`.
  have hC_sub₄ : ∀ i : Fin d', (C i).IsSubdrawing D₄ := fun i =>
    ⟨(hSh₃.isSubdrawing i).1.trans hp.V_sub,
     fun e he => hp.unsplit_mem_E ((hSh₃.isSubdrawing i).2 he) (hF_not_Ci i · he)⟩
  have hB_sub₄ : B.IsSubdrawing D₄ :=
    ⟨hBDs.1.trans hp.V_sub,
     fun e he => hp.unsplit_mem_E (hBDs.2 he) fun heF => heF.1.2 he⟩
  have hShell₄ : SurfaceDShell D₄ r₀₃ (d' + 1) (Fin.snoc C B) (Fin.snoc Δ Δ_new) :=
    { r₀_mem := hr₀₄
      isSubdrawing := fun j => by
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]; exact hC_sub₄ i
        · rw [Fin.snoc_last]; exact hB_sub₄
      isCircuit := fun j => by
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]; exact hSh₃.isCircuit i
        · rw [Fin.snoc_last]; exact hCirc
      isClosedDisc := fun j => by
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]; exact hSh₃.isClosedDisc i
        · rw [Fin.snoc_last]; exact hΔ_new
      discBd_eq := fun j => by
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hSh₃.discBd_eq i
        · rw [Fin.snoc_last, Fin.snoc_last]; exact hbd_new
      disjoint_inf := fun j => by
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]; exact hSh₃.disjoint_inf i
        · rw [Fin.snoc_last]; exact hdisj_Δ_r₀₃
      disjoint_V := fun j₁ j₂ hlt => by
        rcases Fin.eq_castSucc_or_eq_last j₂ with ⟨i₂, rfl⟩ | rfl
        · rcases Fin.eq_castSucc_or_eq_last j₁ with ⟨i₁, rfl⟩ | rfl
          · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
            exact hSh₃.disjoint_V (Fin.castSucc_lt_castSucc_iff.mp hlt)
          · exact (not_lt_of_ge (Fin.le_last _) hlt).elim
        · rcases Fin.eq_castSucc_or_eq_last j₁ with ⟨i₁, rfl⟩ | rfl
          · rw [Fin.snoc_castSucc, Fin.snoc_last]
            refine Set.disjoint_left.mpr fun x hxi hxB => ?_
            have hxN : x ∈ N₃.V := hBs.1 hxB
            rw [hN₃V] at hxN
            exact hxN.2 (mem_iUnion.mpr ⟨i₁, hxi⟩)
          · exact (lt_irrefl _ hlt).elim
      disc_subset_interior := fun j₁ j₂ hlt => by
        rcases Fin.eq_castSucc_or_eq_last j₂ with ⟨i₂, rfl⟩ | rfl
        · rcases Fin.eq_castSucc_or_eq_last j₁ with ⟨i₁, rfl⟩ | rfl
          · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
            exact hSh₃.disc_subset_interior (Fin.castSucc_lt_castSucc_iff.mp hlt)
          · exact (not_lt_of_ge (Fin.le_last _) hlt).elim
        · rcases Fin.eq_castSucc_or_eq_last j₁ with ⟨i₁, rfl⟩ | rfl
          · rw [Fin.snoc_castSucc, Fin.snoc_last]
            exact hΔ_new_sub_int i₁
          · exact (lt_irrefl _ hlt).elim
      vertex_in_or_inside := fun hd1 v hv => by
        have hlast_eq : (⟨d' + 1 - 1, Nat.sub_lt hd1 zero_lt_one⟩ : Fin (d' + 1)) = Fin.last d' :=
          Fin.ext (Nat.add_sub_cancel d' 1)
        rw [hlast_eq, Fin.snoc_last]
        rw [hp.V_eq] at hv
        rcases hv with hvD₃ | ⟨e, heF, rfl⟩
        · by_cases hvC : v ∈ ⋃ i : Fin d', (C i).V
          · obtain ⟨i, hvi⟩ := mem_iUnion.mp hvC
            refine Or.inl ⟨i.castSucc, ?_⟩
            rwa [Fin.snoc_castSucc]
          · have hvN₃ : v ∈ N₃.V := hN₃V.symm ▸ ⟨hvD₃, hvC⟩
            by_cases hvB : v ∈ B.V
            · refine Or.inl ⟨Fin.last d', ?_⟩
              rwa [Fin.snoc_last]
            · refine Or.inr ?_
              rw [← discInt_eq_interior_of_isClosedDisc hS hΔ_new]
              refine ⟨hN₃U_sub_Δ (N₃.V_subset_U hvN₃), fun hvbd => hvB ?_⟩
              rw [hbd_new, hBU_fr] at hvbd
              exact hBV.symm ▸ ⟨hvN₃, hvbd.1⟩
        · exact Or.inr (hF_int_new heF (hd.mid e (hF_sub heF)))
      edge_inside_of_ends := fun j g hg₄ hnot_ends => by
        rw [hp.E_eq] at hg₄
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i₀, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]
          rcases hg₄ with (⟨hgD₃, hgF⟩ | ⟨e, heF, rfl⟩) | ⟨e, heF, rfl⟩
          · refine hSh₃.edge_inside_of_ends i₀ g hgD₃ fun v hv k hk => ?_
            have hv₄ : v ∈ closure g ∩ D₄.V := ⟨hv.1, hp.V_sub hv.2⟩
            have hk' : k.castSucc ≤ i₀.castSucc := Fin.castSucc_le_castSucc_iff.mpr hk
            have hnot := hnot_ends v hv₄ k.castSucc hk'
            rwa [Fin.snoc_castSucc] at hnot
          · exact (hd.A_sub (hF_sub heF)).trans ((hF_int_new heF).trans
              (interior_subset.trans (hΔ_new_sub_int i₀)))
          · exact (hd.B_sub (hF_sub heF)).trans ((hF_int_new heF).trans
              (interior_subset.trans (hΔ_new_sub_int i₀)))
        · rw [Fin.snoc_last]
          rcases hg₄ with (⟨hgD₃, _⟩ | ⟨e, heF, rfl⟩) | ⟨e, heF, rfl⟩
          · have hgN₃ : g ∈ N₃.E := by
              rw [hN₃E]
              refine ⟨hgD₃, fun v hv => ⟨hv.2, ?_⟩⟩
              intro hv_un
              obtain ⟨i, hvi⟩ := mem_iUnion.mp hv_un
              have hnot := hnot_ends v ⟨hv.1, hp.V_sub hv.2⟩ i.castSucc (Fin.le_last _)
              rw [Fin.snoc_castSucc] at hnot
              exact hnot hvi
            have hg_not_B : g ∉ B.E := by
              intro hgB
              obtain ⟨u, _, _, hcap_g⟩ :=
                noLoop_of_simple_subdrawing hSim₃ ⟨Subset.rfl, Subset.rfl⟩ g hgD₃
              have hu_D₃ : u ∈ closure g ∩ D₃.V := hcap_g ▸ mem_insert u _
              have hu_B : u ∈ B.V := by
                have : u ∈ closure g ∩ B.V := by rwa [hBDs.closure_inter_V hgB]
                exact this.2
              have hnot := hnot_ends u ⟨hu_D₃.1, hp.V_sub hu_D₃.2⟩ (Fin.last d') le_rfl
              rw [Fin.snoc_last] at hnot
              exact hnot hu_B
            exact hedge_N₃_int hgN₃ hg_not_B
          · exact (hd.A_sub (hF_sub heF)).trans (hF_int_new heF)
          · exact (hd.B_sub (hF_sub heF)).trans (hF_int_new heF)
      edge_induced := fun j g u v ⟨hg₄, _, _, hcap₄⟩ huC hvC => by
        have hCV_sub_D₃ : (Fin.snoc (α := fun _ => Drawing S) C B j).V ⊆ D₃.V := by
          rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
          · rw [Fin.snoc_castSucc]; exact (hSh₃.isSubdrawing i).1
          · rw [Fin.snoc_last]; exact hBDs.1
        have huD₃ : u ∈ D₃.V := hCV_sub_D₃ huC
        have hvD₃ : v ∈ D₃.V := hCV_sub_D₃ hvC
        rw [hp.E_eq] at hg₄
        rcases hg₄ with (⟨hgD₃, hgF⟩ | ⟨e, heF, rfl⟩) | ⟨e, heF, rfl⟩
        · rw [hp.cap_unsplit hgD₃ hgF] at hcap₄
          have hcap₃ : closure g ∩ D₃.V = {u, v} := (hd.cap g hgD₃).trans hcap₄
          rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
          · rw [Fin.snoc_castSucc] at huC hvC ⊢
            exact hSh₃.edge_induced i ⟨hgD₃, huD₃, hvD₃, hcap₃⟩ huC hvC
          · rw [Fin.snoc_last] at huC hvC ⊢
            by_contra hg_not_B
            refine hgF ⟨⟨hgD₃, hg_not_B⟩, ?_⟩
            rw [hcap₃]
            rintro w (rfl | rfl)
            · exact huC
            · exact hvC
        · exfalso
          have hm_mem : m e ∈ ({u, v} : Set S) := by
            rw [← hcap₄, hp.cap_A heF]; exact mem_insert_of_mem _ rfl
          rcases hm_mem with hmu | hmv
          · exact hd.mid_notMem (hF_sub heF) (hmu ▸ huD₃)
          · exact hd.mid_notMem (hF_sub heF) (hmv ▸ hvD₃)
        · exfalso
          have hm_mem : m e ∈ ({u, v} : Set S) := by
            rw [← hcap₄, hp.cap_B heF]; exact mem_insert _ _
          rcases hm_mem with hmu | hmv
          · exact hd.mid_notMem (hF_sub heF) (hmu ▸ huD₃)
          · exact hd.mid_notMem (hF_sub heF) (hmv ▸ hvD₃)
      shell_vertex_chain := fun j u huC => by
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc] at huC ⊢
          obtain ⟨r_u, hru, hu_cl, hru_disj, k, hk_le, R_seq, hseq_R, hseq_0, hseq_k,
              hseq_disj, hseq_step⟩ := hSh₃.shell_vertex_chain i u huC
          refine ⟨r_u, hR₄_eq.symm ▸ hru, hu_cl, hru_disj, k, hk_le, R_seq,
            fun m_idx => hR₄_eq.symm ▸ hseq_R m_idx, hseq_0, hseq_k, hseq_disj, fun m_idx => ?_⟩
          obtain ⟨w, hwD, hw_not_int, hw1, hw2⟩ := hseq_step m_idx
          exact ⟨w, hp.V_sub hwD, hw_not_int, hw1, hw2⟩
        · rw [Fin.snoc_last] at huC ⊢
          obtain ⟨r_u, hru, hu_cl, hru_disj, k, hk_le, R_seq, hseq_R, hseq_0, hseq_k,
              hseq_disj, hseq_step⟩ := hChain_B u huC
          refine ⟨r_u, hR₄_eq.symm ▸ hru, hu_cl, hru_disj, k, hk_le, R_seq,
            fun m_idx => hR₄_eq.symm ▸ hseq_R m_idx, hseq_0, hseq_k, hseq_disj, fun m_idx => ?_⟩
          obtain ⟨w, hwD, hw_not_int, hw1, hw2⟩ := hseq_step m_idx
          exact ⟨w, hp.V_sub hwD, hw_not_int, hw1, hw2⟩ }
  exact ⟨D₄, r₀₃, hr₀₄, Fin.snoc C B, Fin.snoc Δ Δ_new,
    hShell₄, hSim₄, ((hMin₁.trans hMin₂).trans hMin₃).trans hMin₄, hRad₄⟩

end ShellStep

/-- Full inductive construction for `(2.2)` (pages 52–54):
for any simple graph `G` with `HasRadiusLE G d` and any `d' ≤ d`, there exist a simple planar
graph `G'` with `G` as an isomorphic minor and a drawing `M'` of `G'` with `ρ(M') ≤ d` and a
`d'`-shell. -/
theorem exists_dShell_le {G : Graph α β} {d : ℕ}
    (hSimple : G.Simple) (hrad : HasRadiusLE G d) (d' : ℕ) (hd' : d' ≤ d) :
    ∃ (α' : Type) (β' : Type) (G' : Graph α' β') (M' : PlanarDrawing G')
      (C : Fin d' → Graph α' β'),
      G'.Simple ∧ IsIsoMinor G G' ∧ HasDrawingRadiusLE M' d ∧ IsDShell M' d' C := by
  obtain ⟨M, hMrad⟩ := hrad
  have hS : IsClosedSurface M.S := M.isClosedSurface
  have hSph : IsSphere M.S := M.isSphere
  have : ConnectedSpace M.S := (GM11.IsSphere.isClosedSurface hSph).2
  have : T2Space M.S := hS.2.1
  let D₀ : Drawing M.S := M.drawing
  have hIso : Iso G D₀.toGraph := M.graphDrawing.iso
  have hSimple₀ : D₀.toGraph.Simple :=
    { not_isLoopAt := fun e x hloop => by
        obtain ⟨u, hu⟩ := hIso.vertexEquiv.surjective ⟨x, hloop.left_mem⟩
        obtain ⟨f, hf⟩ := hIso.edgeEquiv.surjective ⟨e, hloop.edge_mem⟩
        have hlG : G.IsLink f u.1 u.1 :=
          (hIso.isLink_iff f u u).mpr (by rw [hf, hu]; exact hloop)
        exact hSimple.not_isLoopAt f u.1 hlG
      eq_of_isLink := fun e₁ e₂ x y hl₁ hl₂ => by
        obtain ⟨u, hu⟩ := hIso.vertexEquiv.surjective ⟨x, hl₁.left_mem⟩
        obtain ⟨v, hv⟩ := hIso.vertexEquiv.surjective ⟨y, hl₁.right_mem⟩
        obtain ⟨f₁, hf₁⟩ := hIso.edgeEquiv.surjective ⟨e₁, hl₁.edge_mem⟩
        obtain ⟨f₂, hf₂⟩ := hIso.edgeEquiv.surjective ⟨e₂, hl₂.edge_mem⟩
        have hlG₁ : G.IsLink f₁ u.1 v.1 :=
          (hIso.isLink_iff f₁ u v).mpr (by rw [hf₁, hu, hv]; exact hl₁)
        have hlG₂ : G.IsLink f₂ u.1 v.1 :=
          (hIso.isLink_iff f₂ u v).mpr (by rw [hf₂, hu, hv]; exact hl₂)
        have hfeq : f₁ = f₂ := Subtype.ext (hSimple.eq_of_isLink hlG₁ hlG₂)
        exact Subtype.ext_iff.mp (hf₁.symm.trans (congrArg hIso.edgeEquiv hfeq |>.trans hf₂)) }
  have hRad₀ : HasDrawingRadiusLE
      (planarDrawingOfDrawing hS hSph D₀ M.infRegion M.infRegion_mem) d :=
    fun R hR => hMrad R hR
  have hSurf : ∀ (k : ℕ), k ≤ d →
      ∃ (D' : Drawing M.S) (r₀' : Set M.S) (hr₀' : r₀' ∈ D'.R)
        (C_draw : Fin k → Drawing M.S) (Δ : Fin k → Set M.S),
        SurfaceDShell D' r₀' k C_draw Δ ∧
        D'.toGraph.Simple ∧
        IsIsoMinor D₀.toGraph D'.toGraph ∧
        HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d := by
    intro k hk
    induction k with
    | zero =>
      exact ⟨D₀, M.infRegion, M.infRegion_mem, Fin.elim0, Fin.elim0,
        surfaceDShell_zero M.infRegion_mem, hSimple₀, IsIsoMinor.refl D₀.toGraph, hRad₀⟩
    | succ k ih =>
      have hk_lt : k < d := Nat.lt_of_succ_le hk
      obtain ⟨D₁, r₀₁, _, C₁, Δ₁, hSh₁, hSim₁, hMin₁, hRad₁⟩ := ih hk_lt.le
      obtain ⟨D₂, r₀₂, hr₀₂, C₂, Δ₂, hSh₂, hSim₂, hMin₂, hRad₂⟩ :=
        exists_surfaceDShell_step hS hSph hk_lt hSh₁ hSim₁ hRad₁
      exact ⟨D₂, r₀₂, hr₀₂, C₂, Δ₂, hSh₂, hSim₂, hMin₁.trans hMin₂, hRad₂⟩
  obtain ⟨D', r₀', hr₀', C_draw, Δ, hSh', hSim', hMin', hRad'⟩ := hSurf d' hd'
  exact ⟨M.S, Set M.S, D'.toGraph,
    planarDrawingOfDrawing hS hSph D' r₀' hr₀',
    fun j => (C_draw j).toGraph,
    hSim', hIso.isIsoMinor_left hMin', hRad', hSh'.toIsDShell hS hSph⟩

end GraphMinor.GM03
