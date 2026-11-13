module

public import GraphMinor.GM03.Section2m

/-!
# Graph Minors III, Section 2n: Base Shell, Outward Shell Induction, and `(2.3)` Gluing

This file completes the proof of `(2.3)` (page 55) of N. Robertson and P. D. Seymour,
*Graph Minors. III. Planar Tree-Width*, J. Combin. Theory Ser. B **36** (1984), 49–64:
1. `exists_base_shell_cyclic_model`: embeds the innermost shell circuit `C_{d-1}` together with the
   connected inner tree `T` and its attachment edges into `graphN 1 lam` using `exists_region_walk`,
   `exists_end_limit`, `collar_sublevel_isClosedDisc`, `truncate_arc_at_closedDisc`, and
   `annulus_monotone_bipartite_order`;
2. `exists_succ_shell_cyclic_model`: shifts an inner cyclic model on `shellGraph D d C k` inward by
   one cylinder ring and attaches `C_{d-2-k}` with its radial edges;
3. `glue_shell_and_tree`: combines inner-forest connection with outward shell induction across all
   `d` circuits to embed `G` as a minor of `graphN d lam`.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Topology Filter
open Graph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11

local notation "𝕀" => unitInterval

universe u v

section ShellInduction

/-- Base shell step (`k = 0`): embed `shellGraph D d C 0` (consisting of `T = innerDraw D d C`,
`C_{d-1}`, and attachment edges between `T` and `C_{d-1}`) into `graphN 1 lam` with
`ShellStepInv`. -/
theorem exists_base_shell_cyclic_model {S : Type} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (hd : 0 < d) (hSimple : D.toGraph.Simple) (hSh : ShellDiscData D d C Δ)
    (hNoCirc : ∀ C' ≤ (innerDraw D d C).toGraph, ¬ IsGraphCircuit (innerDraw D d C).toGraph C')
    (hConn_if_ne : (innerDraw D d C).V.Nonempty → IsGraphConnected (innerDraw D d C).toGraph) :
    ShellStepInv D d C 0 hd := by
  classical
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let j_last : Fin d := ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩
  let T : Drawing S := innerDraw D d C
  let C_last : Drawing S := C j_last
  let Δ_last : Set S := Δ j_last
  let G₀ : Graph S (Set S) := shellGraph D d C 0
  obtain ⟨hTs, hTV, hTE, hT_le_D⟩ := innerDraw_spec D d C
  have hC_le_D : C_last.toGraph ≤ D.toGraph := hSh.subdrawing_toGraph_le j_last
  have hC_sim : C_last.toGraph.Simple := Simple.mono hSimple hC_le_D
  have hG₀_sim : G₀.Simple := Simple.mono hSimple (shellGraph_le hSh 0)
  have hsv0 : shellVerts D d C 0 = T.V ∪ C_last.V := by
    ext x; simp only [shellVerts, mem_union]
    refine or_congr_right ⟨fun h => ?_, fun hx => mem_iUnion₂.mpr ⟨j_last, by dsimp only [j_last]; omega, hx⟩⟩
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp h
    have hjeq : j = j_last := Fin.ext (by have := j.2; dsimp only [j_last]; omega)
    exact show x ∈ (C j_last).V from hjeq ▸ hxj
  have hV_G₀ : V(G₀) = T.V ∪ C_last.V := hsv0
  have hT_le_G₀ : T.toGraph ≤ G₀ := by
    refine ⟨fun v hv => show v ∈ shellVerts D d C 0 by rw [hsv0]; exact Or.inl hv, fun e u v hl => ?_⟩
    rw [show G₀ = D.toGraph.induce (shellVerts D d C 0) from rfl, Graph.induce_isLink, hsv0]
    exact ⟨hT_le_D.2 hl, Or.inl hl.2.1, Or.inl hl.2.2.1⟩
  have hC_le_G₀ : C_last.toGraph ≤ G₀ := by
    refine ⟨fun v hv => show v ∈ shellVerts D d C 0 by rw [hsv0]; exact Or.inr hv, fun e u v hl => ?_⟩
    rw [show G₀ = D.toGraph.induce (shellVerts D d C 0) from rfl, Graph.induce_isLink, hsv0]
    exact ⟨hC_le_D.2 hl, Or.inr hl.2.1, Or.inr hl.2.2.1⟩
  have hDisj_TC : Disjoint T.V C_last.V := hSh.innerDraw_V_disjoint_circuit_V j_last
  -- Define attachment edge set `E_att` between `T.V` and `C_last.V`
  let E_att : Set (Set S) :=
    {e | ∃ u ∈ T.V, ∃ v ∈ C_last.V, D.toGraph.IsLink e u v ∧ e ⊆ interior Δ_last \ T.U}
  have hE_att_fin : E_att.Finite := by
    refine D.finite_edges.subset ?_
    rintro _ ⟨_, _, _, _, hl, _⟩
    exact hl.1
  have : Finite E_att := hE_att_fin.to_subtype
  have hE_G₀ : E(G₀) = T.E ∪ C_last.E ∪ E_att := by
    ext e
    rw [show G₀ = D.toGraph.induce (shellVerts D d C 0) from rfl, Graph.edgeSet_induce, hsv0]
    constructor
    · rintro ⟨x, y, hl, hx, hy⟩
      rcases hSh.edge_classification hS hd hl with heT | ⟨j, heCj⟩ | ⟨hends, hsub⟩ | ⟨j, hj, hends, _⟩
      · exact Or.inl (Or.inl heT)
      · by_cases hjeq : j = j_last
        · exact Or.inl (Or.inr (show e ∈ (C j_last).E from hjeq ▸ heCj))
        · exfalso
          have hcap_j := (hSh.isSubdrawing j).closure_inter_V heCj
          rw [hl.2.2.2] at hcap_j
          have hxCj : x ∈ (C j).V := (hcap_j.symm ▸ mem_insert x {y}).2
          rcases hx with hxT | hxC
          · exact Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j) hxT hxCj
          · exact Set.disjoint_left.mp (hSh.disjoint_V_ne hjeq) hxCj hxC
      · rcases hends with ⟨hxT, hyC⟩ | ⟨hxC, hyT⟩
        · exact Or.inr ⟨x, hxT, y, hyC, hl, hsub⟩
        · exact Or.inr ⟨y, hyT, x, hxC, hl.symm, hsub⟩
      · exfalso
        have hlt_j : (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin d) ≠ j_last :=
          Fin.ne_of_lt (Fin.lt_def.mpr (by dsimp only [j_last]; omega))
        rcases hends with ⟨_, hyj⟩ | ⟨hxj, _⟩
        · rcases hy with hyT | hyC
          · exact Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V _) hyT hyj
          · exact Set.disjoint_left.mp (hSh.disjoint_V_ne hlt_j) hyj hyC
        · rcases hx with hxT | hxC
          · exact Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V _) hxT hxj
          · exact Set.disjoint_left.mp (hSh.disjoint_V_ne hlt_j) hxj hxC
    · rintro ((heT | heC) | ⟨u, huT, v, hvC, hl, _⟩)
      · obtain ⟨u, v, hl⟩ := T.toGraph.exists_isLink_of_mem_edgeSet heT
        exact ⟨u, v, hT_le_D.2 hl, Or.inl hl.2.1, Or.inl hl.2.2.1⟩
      · obtain ⟨u, v, hl⟩ := C_last.toGraph.exists_isLink_of_mem_edgeSet heC
        exact ⟨u, v, hC_le_D.2 hl, Or.inr hl.2.1, Or.inr hl.2.2.1⟩
      · exact ⟨u, v, hl, Or.inl huT, Or.inr hvC⟩
  -- Parameterize every edge `i : E_att` from `u_att i ∈ T.V` to `v_att i ∈ C_last.V`
  have hex_arc : ∀ i : E_att, ∃ (u v : S) (ψ : 𝕀 → S),
      u ∈ T.V ∧ v ∈ C_last.V ∧ D.toGraph.IsLink i.1 u v ∧
      Continuous ψ ∧ Injective ψ ∧ ψ 0 = u ∧ ψ 1 = v ∧ ψ '' Ioo 0 1 = i.1 := by
    intro i
    obtain ⟨u, huT, v, hvC, hl, _⟩ := i.2
    have huv : u ≠ v := fun h => Set.disjoint_left.mp hDisj_TC huT (h ▸ hvC)
    obtain ⟨ψ, hc, hi, h0, h1, hEq⟩ := exists_edge_arc hl huv
    exact ⟨u, v, ψ, huT, hvC, hl, hc, hi, h0, h1, hEq⟩
  choose u_att v_att ψ_att hu_att hv_att hl_att hψ_cont hψ_inj hψ0 hψ1 hψ_img using hex_arc
  have hψ_disj : ∀ ⦃i₁ i₂ : E_att⦄, i₁ ≠ i₂ →
      Disjoint (ψ_att i₁ '' Ioo 0 1) (ψ_att i₂ '' Ioo 0 1) := by
    intro i₁ i₂ hne
    rw [hψ_img i₁, hψ_img i₂, Set.disjoint_left]
    intro x hx₁ hx₂
    exact hne (Subtype.ext (D.edge_eq_of_mem (hl_att i₁).1 (hl_att i₂).1 hx₁ hx₂))
  -- Split on `T.V = ∅`, `T.V ≠ ∅ ∧ T.E = ∅`, and `T.E ≠ ∅`
  by_cases hTV_ne : T.V.Nonempty
  · have hConn : IsGraphConnected T.toGraph := hConn_if_ne hTV_ne
    by_cases hTE_ne : T.E.Nonempty
    · -- Subcase 1c: `T.E.Nonempty`. Use `exists_region_walk` and `exists_end_limit`
      have hTU_pre : IsPreconnected T.U := ((isGraphConnected_iff_isPreconnected_U T).mp hConn).2
      have hTU_ne : T.U.Nonempty := hTV_ne.mono T.V_subset_U
      have hno_draw : ∀ C₀ : Drawing S, C₀.IsCircuit → C₀.IsSubdrawing T → False := by
        intro C₀ hC₀ hSub₀
        have hC₀_le : C₀.toGraph ≤ T.toGraph := by
          refine ⟨hSub₀.1, fun e u v hl => ⟨hSub₀.2 hl.1, hSub₀.1 hl.2.1, hSub₀.1 hl.2.2.1, ?_⟩⟩
          rw [← hSub₀.closure_inter_V hl.1]
          exact hl.2.2.2
        obtain ⟨u, W, hCyc, hPos, hV, hE⟩ := hC₀
        exact hNoCirc C₀.toGraph hC₀_le ⟨hC₀_le, u, W, hCyc, hPos, hV, hE⟩
      have hPre_compl : IsPreconnected T.Uᶜ := GM11.isPreconnected_compl_of_noCircuit hS T hno_draw
      obtain ⟨p₀, -, hp₀_not_TU⟩ := GM11.exists_notMem_U (Γ := T) hS isOpen_univ univ_nonempty
      let r_reg : Set S := univ \ T.U
      have hr_mem : r_reg ∈ T.R := by
        rw [GM11.mem_R_iff]
        refine ⟨p₀, hp₀_not_TU, Subset.antisymm ?_ (connectedComponentIn_subset _ _)⟩
        exact (compl_eq_univ_sdiff T.U ▸ hPre_compl).subset_connectedComponentIn
          ⟨mem_univ p₀, hp₀_not_TU⟩ subset_rfl
      have hcl_r : closure r_reg = univ := by
        refine eq_univ_of_forall fun x => mem_closure_iff.mpr fun O hO hxO => ?_
        obtain ⟨z, hzO, hz_not⟩ := GM11.exists_notMem_U (Γ := T) hS hO ⟨x, hxO⟩
        exact ⟨z, hzO, mem_univ z, hz_not⟩
      have hfr_r : frontier r_reg = T.U := by
        rw [frontier, hcl_r, (GM11.region_isOpen hr_mem).interior_eq]
        ext x; simp [r_reg]
      have hrc_eq : r_regᶜ = T.U := by ext x; simp [r_reg]
      have hr_disc : IsOpenDisc r_reg :=
        (isOpenDisc_and_isPreconnected_frontier_of_isPreconnected_U hS hSph hTU_ne hTU_pre hr_mem).1
      have hTwoCell : (PaintingOrDrawing.drawing T).IsTwoCell :=
        ⟨inferInstance, fun q hq => GM11.region_eq_of_noCircuit hS hno_draw hq hr_mem ▸ hr_disc⟩
      obtain ⟨u₀, W, h, hW_pos, hinj, hr_pos, hrange_bot, hop_raw, hRuns, hEdgeCnt⟩ :=
        GM11.exists_region_walk hS hSph hTwoCell hTE_ne hr_mem
      have hbot : ∀ z : Circle, h (z, 0) ∈ T.U := fun z =>
        hfr_r ▸ hrange_bot ▸ mem_range_self z
      have hoff : ∀ p : Circle × 𝕀, 0 < p.2 → h p ∉ T.U := fun p hp hpU =>
        (hr_pos p hp).2 hpU
      have hop : IsOpen (T.U ∪ h '' {p | p.2 < 1}) := hrc_eq ▸ hop_raw
      have hu₀_mem : u₀ ∈ T.V := by
        cases W with
        | nil hu => exact hu
        | cons hl _ => exact hl.left_mem
      have hCount : ∀ e ∈ T.E, W.edges.count e = 2 := by
        intro e he
        have he_fr : (e ∩ frontier r_reg).Nonempty := by
          rw [hfr_r, inter_eq_self_of_subset_left (fun x hx => (he.2.1 hx).1)]
          exact he.1
        have he_two : GM11.IsTwoSided r_reg e := by
          have hopen_re : IsOpen (r_reg ∪ e) := by
            have heq : r_reg ∪ e = ((T.deleteEdge e).U)ᶜ := by
              rw [GM11.deleteEdge_U T he]
              ext x
              simp only [r_reg, mem_union, Set.mem_sdiff, mem_univ, true_and, mem_compl_iff]
              tauto
            rw [heq]
            exact (T.deleteEdge e).isClosed_U.isOpen_compl
          rw [GM11.IsTwoSided, hopen_re.interior_eq,
            inter_eq_self_of_subset_left subset_union_right]
          exact he.1
        have hcnt := hEdgeCnt e he
        simp only [GM11.edgeCount, he_fr, he_two, ↓reduceIte] at hcnt
        exact hcnt
      -- Extract support times `τ` along `W`
      obtain ⟨τ, hτ_mono, hτ0, hτ_last, hτ_sup, hτ_edge⟩ := runsAlongOn_support_times hRuns
      let L := W.length
      have hsup_len : W.support.length = L + 1 := graphWalk_support_length W
      have hτ_L : τ ⟨L, by omega⟩ = 1 := by
        convert hτ_last using 2; apply Fin.ext; dsimp only; omega
      -- Any `t ∈ [0, 1)` mapping into `T.V` under `collarCurve h` equals `τ ⟨j.1, _⟩` for `j : Fin L`
      have hτ_of_TV : ∀ t ∈ Ico (0 : ℝ) 1, collarCurve h t ∈ T.V →
          ∃ j : Fin L, t = τ ⟨j.1, by omega⟩ := by
        intro t ⟨ht0, ht1⟩ htV
        let S_le : Finset (Fin L) := Finset.univ.filter fun j => τ ⟨j.1, by omega⟩ ≤ t
        have h0_in : (⟨0, hW_pos⟩ : Fin L) ∈ S_le := by
          simp only [S_le, Finset.mem_filter, Finset.mem_univ, true_and, hτ0, ht0]
        let j := S_le.max' ⟨⟨0, hW_pos⟩, h0_in⟩
        have hj_le : τ ⟨j.1, by omega⟩ ≤ t := (Finset.mem_filter.mp (Finset.max'_mem S_le _)).2
        have hj_gt : t < τ ⟨j.1 + 1, by omega⟩ := by
          by_cases hj1 : j.1 + 1 < L
          · by_contra hnot
            have hmem1 : (⟨j.1 + 1, hj1⟩ : Fin L) ∈ S_le :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hnot⟩
            have hle_max := Fin.le_def.mp (Finset.le_max' S_le _ hmem1)
            dsimp only at hle_max; omega
          · have hjeq : (⟨j.1 + 1, by omega⟩ : Fin W.support.length) = ⟨L, by omega⟩ :=
              Fin.ext (by dsimp only; omega)
            rw [hjeq, hτ_L]; exact ht1
        rcases eq_or_lt_of_le hj_le with heq | hlt
        · exact ⟨j, heq.symm⟩
        · exfalso
          have he_mem := hτ_edge j.1 (by omega)
          have hin_e : collarCurve h t ∈
              collarCurve h '' Ioo (τ ⟨j.1, by omega⟩) (τ ⟨j.1 + 1, by omega⟩) :=
            ⟨t, ⟨hlt, hj_gt⟩, rfl⟩
          exact (he_mem.2.1 hin_e).2 htV
      -- Every `u ∈ T.V` has finitely many preimages on `Circle × {0}`
      have hfin_pre : ∀ u ∈ T.V, {z : Circle | h (z, 0) = u}.Finite := by
        intro u hu
        have h2pi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
        let tOf : Circle → ℝ := fun z =>
          toIcoMod h2pi 0 (Complex.arg (z : ℂ)) / (2 * Real.pi)
        have htOf_Ico : ∀ z : Circle, tOf z ∈ Ico 0 1 := by
          intro z
          obtain ⟨hlo, hhi⟩ := toIcoMod_mem_Ico h2pi 0 (Complex.arg (z : ℂ))
          rw [zero_add] at hhi
          exact ⟨div_nonneg hlo h2pi.le, (div_lt_one h2pi).mpr hhi⟩
        have hexp_tOf : ∀ z : Circle, Circle.exp (2 * Real.pi * tOf z) = z := by
          intro z
          have hmul : 2 * Real.pi * tOf z = toIcoMod h2pi 0 (Complex.arg (z : ℂ)) :=
            mul_div_cancel₀ _ h2pi.ne'
          have hk := self_sub_toIcoDiv_zsmul h2pi 0 (Complex.arg (z : ℂ))
          refine (Circle.exp_eq_exp.mpr ⟨-toIcoDiv h2pi 0 (Complex.arg (z : ℂ)), ?_⟩).trans
            (Circle.exp_arg z)
          rw [hmul, ← hk, zsmul_eq_mul]; push_cast; ring
        have htOf_inj : Injective tOf := fun z₁ z₂ heq => by
          rw [← hexp_tOf z₁, ← hexp_tOf z₂, heq]
        refine Finite.of_injOn (f := tOf)
          (s := {z : Circle | h (z, 0) = u}) (t := range fun j : Fin L => τ ⟨j.1, by omega⟩)
          (fun z hz => ?_) htOf_inj.injOn (finite_range _)
        have hcc : collarCurve h (tOf z) = u := by
          change h (Circle.exp (2 * Real.pi * tOf z), 0) = u
          rw [hexp_tOf]; exact hz
        obtain ⟨j, hj⟩ := hτ_of_TV (tOf z) (htOf_Ico z) (by rw [hcc]; exact hu)
        exact ⟨j, hj.symm⟩
      -- Define tour angles `θ_k (j : Fin L) = 2π * τ j` and gap margin `μ > 0`
      let θ_k : Fin L → ℝ := fun j => 2 * Real.pi * τ ⟨j.1, by omega⟩
      have h2pi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
      have hθk_0 : θ_k ⟨0, hW_pos⟩ = 0 := by dsimp only [θ_k]; rw [hτ0, mul_zero]
      let gap : Fin L → ℝ := fun j =>
        2 * Real.pi * (τ ⟨j.1 + 1, by omega⟩ - τ ⟨j.1, by omega⟩)
      have hgap_pos : ∀ j : Fin L, 0 < gap j := fun j =>
        mul_pos h2pi (sub_pos.mpr (hτ_mono (Fin.lt_def.mpr (by dsimp only; omega))))
      have hgap_ne : (Finset.univ.image gap).Nonempty :=
        ⟨gap ⟨0, hW_pos⟩, Finset.mem_image_of_mem gap (Finset.mem_univ _)⟩
      let g_min : ℝ := (Finset.univ.image gap).min' hgap_ne
      have hgmin_pos : 0 < g_min := by
        dsimp only [g_min]
        rw [Finset.lt_min'_iff]
        intro x hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact hgap_pos j
      have hgmin_le : ∀ j : Fin L, g_min ≤ gap j := fun j =>
        Finset.min'_le _ _ (Finset.mem_image_of_mem gap (Finset.mem_univ j))
      let μ : ℝ := g_min / 4
      have hμ_pos : 0 < μ := by dsimp only [μ]; linarith
      have hθk_step : ∀ j : Fin L,
          4 * μ ≤ 2 * Real.pi * τ ⟨j.1 + 1, by omega⟩ - θ_k j := by
        intro j
        have := hgmin_le j
        dsimp only [μ, gap, θ_k] at this ⊢; linarith
      have hθk_mono : StrictMono θ_k := fun j₁ j₂ hlt =>
        mul_lt_mul_of_pos_left (hτ_mono (Fin.lt_def.mpr (Fin.lt_def.mp hlt))) h2pi
      have hθk_bounds : ∀ j : Fin L, 0 ≤ θ_k j ∧ θ_k j + 4 * μ ≤ 2 * Real.pi := by
        intro j
        constructor
        · rw [← hθk_0]; exact hθk_mono.monotone (Fin.le_def.mpr (Nat.zero_le _))
        · have h1 : θ_k j ≤ θ_k ⟨L - 1, Nat.sub_lt hW_pos zero_lt_one⟩ :=
            hθk_mono.monotone (Fin.le_def.mpr (by have := j.2; dsimp only; omega))
          have h2 := hθk_step ⟨L - 1, Nat.sub_lt hW_pos zero_lt_one⟩
          have hL_eq : (⟨L - 1 + 1, by omega⟩ : Fin W.support.length) = ⟨L, by omega⟩ :=
            Fin.ext (by dsimp only; omega)
          rw [hL_eq, hτ_L, mul_one] at h2
          linarith
      -- Apply `exists_end_limit` to each `i : E_att` to locate its tour slot `j_att i : Fin L`
      have hex_lim : ∀ i : E_att, ∃ (j : Fin L) (ρ : ℝ) (s_i : 𝕀),
          W.support[(⟨j.1, by omega⟩ : Fin W.support.length)] = u_att i ∧
          0 < ρ ∧
          (∀ θ ∈ Icc (-μ) (θ_k j - μ) ∪ Icc (θ_k j + μ) (-μ + 2 * Real.pi),
            ρ ≤ ‖(Circle.exp θ : ℂ) - (Circle.exp (θ_k j) : ℂ)‖) ∧
          (0 : 𝕀) < s_i ∧
          (∀ s' ∈ Ioo (0 : 𝕀) s_i,
            ‖((GM11.collarInv h (ψ_att i s')).1 : ℂ) - (Circle.exp (θ_k j) : ℂ)‖ < ρ) := by
        intro i
        have hψi_off : ∀ t ∈ Ioo (0 : 𝕀) 1, ψ_att i t ∉ T.U := by
          intro t ht
          obtain ⟨_, _, _, _, _, hsub⟩ := i.2
          have hmem_e : ψ_att i t ∈ i.1 := hψ_img i ▸ mem_image_of_mem _ ht
          exact (hsub hmem_e).2
        obtain ⟨z_i, hz_bot, hz_nhds⟩ := GM11.exists_end_limit hinj hoff hbot hop
          (hψ_cont i) hψi_off (by rw [hψ0 i]; exact T.V_subset_U (hu_att i))
          (by rw [hψ0 i]; exact hfin_pre (u_att i) (hu_att i))
        -- Identify `z_i = Circle.exp (θ_k j)` for `j : Fin L`
        let t_i : ℝ := toIcoMod h2pi 0 (Complex.arg (z_i : ℂ)) / (2 * Real.pi)
        have hti_Ico : t_i ∈ Ico 0 1 := by
          obtain ⟨hlo, hhi⟩ := toIcoMod_mem_Ico h2pi 0 (Complex.arg (z_i : ℂ))
          rw [zero_add] at hhi
          exact ⟨div_nonneg hlo h2pi.le, (div_lt_one h2pi).mpr hhi⟩
        have hexp_ti : Circle.exp (2 * Real.pi * t_i) = z_i := by
          have hmul : 2 * Real.pi * t_i = toIcoMod h2pi 0 (Complex.arg (z_i : ℂ)) :=
            mul_div_cancel₀ _ h2pi.ne'
          have hk := self_sub_toIcoDiv_zsmul h2pi 0 (Complex.arg (z_i : ℂ))
          refine (Circle.exp_eq_exp.mpr ⟨-toIcoDiv h2pi 0 (Complex.arg (z_i : ℂ)), ?_⟩).trans
            (Circle.exp_arg z_i)
          rw [hmul, ← hk, zsmul_eq_mul]; push_cast; ring
        have hcc_ti : collarCurve h t_i = u_att i := by
          change h (Circle.exp (2 * Real.pi * t_i), 0) = u_att i
          rw [hexp_ti, hz_bot, hψ0 i]
        obtain ⟨j, hti_eq⟩ := hτ_of_TV t_i hti_Ico (by rw [hcc_ti]; exact hu_att i)
        have hzi_eq : z_i = Circle.exp (θ_k j) := by
          dsimp only [θ_k]; rw [← hti_eq, hexp_ti]
        have hW_u : W.support[(⟨j.1, by omega⟩ : Fin W.support.length)] = u_att i := by
          rw [← hτ_sup ⟨j.1, by omega⟩, ← hti_eq, hcc_ti]
        -- Compactness gives positive lower bound `ρ` on `K_out`
        let K_out : Set ℝ := Icc (-μ) (θ_k j - μ) ∪ Icc (θ_k j + μ) (-μ + 2 * Real.pi)
        have hK_comp : IsCompact K_out := isCompact_Icc.union isCompact_Icc
        have hK_ne : K_out.Nonempty :=
          ⟨-μ + 2 * Real.pi, Or.inr ⟨by linarith [(hθk_bounds j).2], le_rfl⟩⟩
        let d_fn : ℝ → ℝ := fun θ => ‖(Circle.exp θ : ℂ) - (Circle.exp (θ_k j) : ℂ)‖
        have hd_cont : Continuous d_fn :=
          (continuous_subtype_val.comp Circle.exp.continuous |>.sub continuous_const).norm
        obtain ⟨θ_m, hθm_mem, hθm_min⟩ := hK_comp.exists_isMinOn hK_ne hd_cont.continuousOn
        have hρ_pos : 0 < d_fn θ_m := by
          refine norm_sub_pos_iff.mpr fun heq => ?_
          obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Subtype.ext heq)
          have hbd_j := hθk_bounds j
          have habs : μ ≤ |θ_m - θ_k j| ∧ |θ_m - θ_k j| < 2 * Real.pi := by
            rcases hθm_mem with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [abs_of_neg (by linarith)]
              exact ⟨by linarith, by linarith⟩
            · rw [abs_of_pos (by linarith)]
              exact ⟨by linarith, by linarith⟩
          have hm0 : m = 0 := by
            by_contra hne
            have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hne
            have h2 : |θ_m - θ_k j| = |(m : ℝ)| * (2 * Real.pi) := by
              rw [hm, add_sub_cancel_left, abs_mul, abs_of_pos h2pi]
            nlinarith
          rw [hm, hm0] at habs
          simp at habs; linarith
        let N_i : Set (Circle × 𝕀) :=
          {z : Circle | ‖(z : ℂ) - (z_i : ℂ)‖ < d_fn θ_m} ×ˢ univ
        have hNi_open : IsOpen N_i :=
          (isOpen_lt (continuous_subtype_val.sub continuous_const).norm continuous_const).prod
            isOpen_univ
        have hzi_Ni : ((z_i, 0) : Circle × 𝕀) ∈ N_i :=
          ⟨by simp [hρ_pos], mem_univ _⟩
        obtain ⟨s_i, hsi_pos, hsi_spec⟩ := hz_nhds N_i (hNi_open.mem_nhds hzi_Ni)
        refine ⟨j, d_fn θ_m, s_i, hW_u, hρ_pos, fun θ hθ => isMinOn_iff.mp hθm_min θ hθ,
          hsi_pos, fun s' hs' => ?_⟩
        rw [← hzi_eq]
        exact (hsi_spec s' hs').1
      choose j_att ρ_att s_att hW_u_att hρ_pos hρ_min hs_pos hs_spec using hex_lim
      -- Choose collar height `ε` inside `interior Δ_last \ ⋃ i, ψ_att i '' Icc (s_att i) 1`
      let U_avoid : Set S := interior Δ_last \ ⋃ i : E_att, ψ_att i '' Icc (s_att i) 1
      have hU_avoid_open : IsOpen U_avoid :=
        isOpen_interior.sdiff (isClosed_iUnion_of_finite fun i =>
          (isCompact_Icc.image (hψ_cont i)).isClosed)
      have hTU_sub_avoid : T.U ⊆ U_avoid := by
        refine subset_sdiff.mpr ⟨hSh.innerDraw_U_subset_interior hS hd, ?_⟩
        rw [Set.disjoint_left]
        intro x hxTU hx_un
        obtain ⟨i, hxi⟩ := mem_iUnion.mp hx_un
        obtain ⟨t, ⟨ht_lo, ht_hi⟩, rfl⟩ := hxi
        rcases eq_or_lt_of_le ht_hi with ht1 | ht_lt1
        · rw [ht1, hψ1 i] at hxTU
          have hv_int := hSh.innerDraw_U_subset_interior hS hd hxTU
          rw [← discInt_eq_interior_of_isClosedDisc hS (hSh.isClosedDisc j_last)] at hv_int
          exact hv_int.2 ((hSh.discBd_eq j_last).symm ▸ C_last.V_subset_U (hv_att i))
        · obtain ⟨_, _, _, _, _, hsub⟩ := i.2
          have hin_e : ψ_att i t ∈ i.1 :=
            hψ_img i ▸ mem_image_of_mem _ ⟨lt_of_lt_of_le (hs_pos i) ht_lo, ht_lt1⟩
          exact (hsub hin_e).2 hxTU
      obtain ⟨ε, hε0, hε1, hK_avoid⟩ :=
        exists_small_collar_height h hU_avoid_open hTU_sub_avoid hbot
      let K_ε : Set S := T.U ∪ h '' {p | p.2 ≤ ε}
      obtain ⟨hK_disc, _, hK_sub_diff, hTU_int_K, φ_ε, hφ_ε_apply⟩ :=
        collar_sublevel_isClosedDisc hS (hSh.isClosedDisc j_last) hTU_ne T.isClosed_U hTU_pre
          h hinj hoff hbot hop hε0 hε1 (hK_avoid.trans sdiff_subset)
      -- Truncate each `ψ_att i` at `K_ε`
      have hex_trunc : ∀ i : E_att, ∃ (t_i : 𝕀) (γ_i : 𝕀 → S),
          (0 : 𝕀) < t_i ∧ t_i < s_att i ∧
          γ_i 0 = ψ_att i t_i ∧ γ_i 0 ∈ discBd K_ε ∧ γ_i 1 = v_att i ∧
          Continuous γ_i ∧ Injective γ_i ∧
          (∀ s : 𝕀, (0 : 𝕀) < s → s < 1 → γ_i s ∈ interior Δ_last \ K_ε) ∧
          γ_i '' Ioo 0 1 ⊆ ψ_att i '' Ioo 0 1 := by
        intro i
        obtain ⟨_, _, _, _, _, hsub⟩ := i.2
        obtain ⟨t_i, γ_i, ht_pos, _, hγ0_eq, hγ0_bd, hγ1_eq, hγ_c, hγ_inj, hγ_in, hγ_sub⟩ :=
          truncate_arc_at_closedDisc hS hK_disc (hψ_cont i) (hψ_inj i)
            (by rw [hψ0 i]; exact hTU_int_K (T.V_subset_U (hu_att i)))
            (by rw [hψ1 i, hSh.discBd_eq j_last]; exact C_last.V_subset_U (hv_att i))
            hK_sub_diff
            (fun t ht0 ht1 => (hsub (hψ_img i ▸ mem_image_of_mem _ ⟨ht0, ht1⟩)).1)
        have hti_lt_s : t_i < s_att i := by
          by_contra hge
          have hmem_K : ψ_att i t_i ∈ K_ε := hγ0_eq ▸ GM11.discBd_subset K_ε hγ0_bd
          exact (hK_avoid hmem_K).2 (mem_iUnion.mpr ⟨i, t_i,
            ⟨not_lt.mp hge, unitInterval.le_one t_i⟩, rfl⟩)
        exact ⟨t_i, γ_i, ht_pos, hti_lt_s, hγ0_eq, hγ0_bd, hγ1_eq.trans (hψ1 i),
          hγ_c, hγ_inj, hγ_in, hγ_sub⟩
      choose t_tr γ_tr ht_tr_pos ht_tr_lt_s hγ0_tr hγ0_bd hγ1_tr hγ_cont hγ_inj hγ_in hγ_sub
        using hex_trunc
      -- Apply `annulus_monotone_bipartite_order` with `α_base = -μ`
      obtain ⟨cyc_out, φ_out, θ_out, m, σ, α_ord, f,
          hθ_strict, hθ_Ico, hθ_u, hθ_of_V, hα_mono, hα_Ico, hα_end, hf_mono, hf_end⟩ :=
        annulus_monotone_bipartite_order hS hK_disc (hSh.isClosedDisc j_last) hK_sub_diff
          φ_ε (-μ) C_last (hSh.isCircuit j_last) hC_sim (hSh.discBd_eq j_last)
          γ_tr hγ_cont hγ_inj hγ0_bd (fun i => by rw [hγ1_tr i]; exact hv_att i) hγ_in
          (fun i₁ i₂ hne => (hψ_disj hne).mono (hγ_sub i₁) (hγ_sub i₂))
      -- Show `α_ord r ∈ Ioo (θ_k (j_att (σ r)) - μ) (θ_k (j_att (σ r)) + μ)` for every `r`
      have hα_in_ball : ∀ r : Fin m,
          θ_k (j_att (σ r)) - μ < α_ord r ∧ α_ord r < θ_k (j_att (σ r)) + μ := by
        intro r
        let i := σ r
        let z' : Circle := Circle.exp (α_ord r)
        have hz'_eq : h (z', ε) = ψ_att i (t_tr i) := by
          rw [← hφ_ε_apply z', hα_end r, hγ0_tr i]
        have hcinv : (GM11.collarInv h (ψ_att i (t_tr i))).1 = z' := by
          rw [← hz'_eq, GM11.collarInv_apply hinj hε0]
        have hnorm_lt : ‖(z' : ℂ) - (Circle.exp (θ_k (j_att i)) : ℂ)‖ < ρ_att i := by
          rw [← hcinv]
          exact hs_spec i (t_tr i) ⟨ht_tr_pos i, ht_tr_lt_s i⟩
        have hIco_r := hα_Ico r
        by_contra hnot
        have hmem_Kout : α_ord r ∈
            Icc (-μ) (θ_k (j_att i) - μ) ∪ Icc (θ_k (j_att i) + μ) (-μ + 2 * Real.pi) := by
          by_cases hlo : α_ord r ≤ θ_k (j_att i) - μ
          · exact Or.inl ⟨hIco_r.1, hlo⟩
          · exact Or.inr ⟨le_of_not_gt fun hhi => hnot ⟨not_le.mp hlo, hhi⟩, hIco_r.2.le⟩
        exact not_lt_of_ge (hρ_min i (α_ord r) hmem_Kout) hnorm_lt
      let g : Fin m → Fin W.support.length := fun r => ⟨(j_att (σ r)).1, by omega⟩
      have hg_mono : Monotone g := by
        intro r₁ r₂ hle
        have hα_le := hα_mono hle
        by_contra hnot_le
        have hlt_j : j_att (σ r₂) < j_att (σ r₁) :=
          Fin.lt_def.mpr (not_le.mp hnot_le)
        have hstep1 := hθk_step (j_att (σ r₂))
        have hmono_rest : 2 * Real.pi * τ ⟨(j_att (σ r₂)).1 + 1, by omega⟩ ≤
            θ_k (j_att (σ r₁)) :=
          mul_le_mul_of_nonneg_left
            (hτ_mono.monotone (Fin.le_def.mpr (by have := Fin.lt_def.mp hlt_j; dsimp only; omega)))
            h2pi.le
        have hb₁ := (hα_in_ball r₁).1
        have hb₂ := (hα_in_ball r₂).2
        linarith
      let attE : Fin m → Set S := fun r => (σ r).1
      have hatt_inj : Injective attE := fun r₁ r₂ h => σ.injective (Subtype.ext h)
      have hrange_attE : range attE = E_att := by
        ext e
        exact ⟨by rintro ⟨r, rfl⟩; exact (σ r).2, fun he => ⟨σ.symm ⟨e, he⟩, by simp [attE]⟩⟩
      have hConn_u₀ : ∀ z ∈ V(T.toGraph), Relation.ReflTransGen T.toGraph.Adj u₀ z := by
        intro z hz
        obtain ⟨_, hwalk⟩ := hConn
        obtain ⟨Q⟩ := hwalk u₀ hu₀_mem z hz
        exact graphWalk_to_reflTransGen Q
      obtain ⟨lam, hcyc⟩ := exists_graphN1_cyclic_model G₀ T.toGraph C_last.toGraph
        hG₀_sim hT_le_G₀ hC_le_G₀ hDisj_TC T.finite_V T.finite_edges hNoCirc hu₀_mem hConn_u₀
        W hCount cyc_out attE hatt_inj g f hg_mono hf_mono hV_G₀ (hrange_attE.symm ▸ hE_G₀)
        (fun r => by
          rw [show G₀ = D.toGraph.induce (shellVerts D d C 0) from rfl, Graph.induce_isLink, hsv0]
          have hu_eq : W.support[g r] = u_att (σ r) := hW_u_att (σ r)
          have hv_eq : cyc_out.u ⟨(f r).1 % C_last.V.ncard,
              Nat.mod_lt _ (by have := cyc_out.hp; omega)⟩ = v_att (σ r) :=
            (hf_end r).trans (hγ1_tr (σ r))
          rw [hu_eq, hv_eq]
          exact ⟨hl_att (σ r), Or.inl (hu_att (σ r)), Or.inr (hv_att (σ r))⟩)
      exact ⟨cyc_out, φ_out, θ_out, lam, hθ_strict, hθ_Ico, hθ_u, hθ_of_V, hcyc⟩
    · -- Subcase 1b: `T.V.Nonempty` and `T.E = ∅` (single-vertex tree `T.V = {v₀}`)
      have hTE_emp : T.E = ∅ := not_nonempty_iff_eq_empty.mp hTE_ne
      obtain ⟨v₀, hv₀⟩ := hTV_ne
      have hTV_eq : T.V = {v₀} := by
        refine Subset.antisymm (fun z hz => ?_) (singleton_subset_iff.mpr hv₀)
        obtain ⟨_, hwalk⟩ := hConn
        obtain ⟨Q⟩ := hwalk v₀ hv₀ z hz
        cases Q with
        | nil _ => rfl
        | cons hl _ => exact (hTE_emp ▸ hl.1).elim
      have hTU_eq : T.U = {v₀} := by
        rw [T.U_eq, hTV_eq, hTE_emp]; simp
      obtain ⟨h, hinj, hoff_v, hbot_v, hop_v⟩ := GM11.exists_point_collar hS v₀
      have hv₀_int : ({v₀} : Set S) ⊆ interior Δ_last :=
        hTU_eq ▸ hSh.innerDraw_U_subset_interior hS hd
      obtain ⟨ε, hε0, hε1, hK_sub⟩ :=
        exists_small_collar_height h isOpen_interior hv₀_int (fun z => by simp [hbot_v z])
      let K_ε : Set S := {v₀} ∪ h '' {p | p.2 ≤ ε}
      obtain ⟨hK_disc, _, hK_sub_diff, hv₀_int_K, φ_ε, _⟩ :=
        collar_sublevel_isClosedDisc hS (hSh.isClosedDisc j_last) (singleton_nonempty v₀)
          isClosed_singleton isPreconnected_singleton h hinj
          (fun p hp hpv => hoff_v p hp (mem_singleton_iff.mp hpv))
          (fun z => mem_singleton_iff.mpr (hbot_v z)) hop_v hε0 hε1 hK_sub
      have hex_trunc : ∀ i : E_att, ∃ γ_i : 𝕀 → S,
          γ_i 0 ∈ discBd K_ε ∧ γ_i 1 = v_att i ∧
          Continuous γ_i ∧ Injective γ_i ∧
          (∀ s : 𝕀, (0 : 𝕀) < s → s < 1 → γ_i s ∈ interior Δ_last \ K_ε) ∧
          γ_i '' Ioo 0 1 ⊆ ψ_att i '' Ioo 0 1 := by
        intro i
        obtain ⟨_, _, _, _, _, hsub⟩ := i.2
        have hu_eq : u_att i = v₀ := mem_singleton_iff.mp (hTV_eq ▸ hu_att i)
        obtain ⟨_, γ_i, _, _, _, hγ0_bd, hγ1_eq, hγ_c, hγ_inj, hγ_in, hγ_sub⟩ :=
          truncate_arc_at_closedDisc hS hK_disc (hψ_cont i) (hψ_inj i)
            (by rw [hψ0 i, hu_eq]; exact hv₀_int_K (mem_singleton v₀))
            (by rw [hψ1 i, hSh.discBd_eq j_last]; exact C_last.V_subset_U (hv_att i))
            hK_sub_diff
            (fun t ht0 ht1 => (hsub (hψ_img i ▸ mem_image_of_mem _ ⟨ht0, ht1⟩)).1)
        exact ⟨γ_i, hγ0_bd, hγ1_eq.trans (hψ1 i), hγ_c, hγ_inj, hγ_in, hγ_sub⟩
      choose γ_tr hγ0_bd hγ1_tr hγ_cont hγ_inj hγ_in hγ_sub using hex_trunc
      obtain ⟨cyc_out, φ_out, θ_out, m, σ, _, f,
          hθ_strict, hθ_Ico, hθ_u, hθ_of_V, _, _, _, hf_mono, hf_end⟩ :=
        annulus_monotone_bipartite_order hS hK_disc (hSh.isClosedDisc j_last) hK_sub_diff
          φ_ε 0 C_last (hSh.isCircuit j_last) hC_sim (hSh.discBd_eq j_last)
          γ_tr hγ_cont hγ_inj hγ0_bd (fun i => by rw [hγ1_tr i]; exact hv_att i) hγ_in
          (fun i₁ i₂ hne => (hψ_disj hne).mono (hγ_sub i₁) (hγ_sub i₂))
      let W₀ : GraphWalk T.toGraph v₀ v₀ := .nil hv₀
      let g : Fin m → Fin W₀.support.length := fun _ => ⟨0, by simp [W₀, GraphWalk.support]⟩
      let attE : Fin m → Set S := fun r => (σ r).1
      have hatt_inj : Injective attE := fun r₁ r₂ h => σ.injective (Subtype.ext h)
      have hrange_attE : range attE = E_att := by
        ext e
        exact ⟨by rintro ⟨r, rfl⟩; exact (σ r).2, fun he => ⟨σ.symm ⟨e, he⟩, by simp [attE]⟩⟩
      obtain ⟨lam, hcyc⟩ := exists_graphN1_cyclic_model G₀ T.toGraph C_last.toGraph
        hG₀_sim hT_le_G₀ hC_le_G₀ hDisj_TC T.finite_V T.finite_edges hNoCirc hv₀
        (fun z hz => by
          have h1 : z ∈ ({v₀} : Set S) := hTV_eq ▸ hz
          rw [mem_singleton_iff.mp h1])
        W₀ (fun e (he : e ∈ T.E) => (hTE_emp ▸ he).elim) cyc_out attE hatt_inj g f
        (fun _ _ _ => le_rfl) hf_mono hV_G₀ (hrange_attE.symm ▸ hE_G₀)
        (fun r => by
          rw [show G₀ = D.toGraph.induce (shellVerts D d C 0) from rfl, Graph.induce_isLink, hsv0]
          have hu_eq : W₀.support[g r] = u_att (σ r) := by
            have h1 : u_att (σ r) ∈ ({v₀} : Set S) := hTV_eq ▸ hu_att (σ r)
            exact (mem_singleton_iff.mp h1).symm
          have hv_eq : cyc_out.u ⟨(f r).1 % C_last.V.ncard,
              Nat.mod_lt _ (by have := cyc_out.hp; omega)⟩ = v_att (σ r) :=
            (hf_end r).trans (hγ1_tr (σ r))
          rw [hu_eq, hv_eq]
          exact ⟨hl_att (σ r), Or.inl (hu_att (σ r)), Or.inr (hv_att (σ r))⟩)
      exact ⟨cyc_out, φ_out, θ_out, lam, hθ_strict, hθ_Ico, hθ_u, hθ_of_V, hcyc⟩
  · -- Subcase 1a: `T.V = ∅`, so `G₀ = C_last.toGraph`
    have hTV_emp : T.V = ∅ := not_nonempty_iff_eq_empty.mp hTV_ne
    have hG₀_eq : shellGraph D d C 0 = C_last.toGraph := by
      refine Graph.ext (by change shellVerts D d C 0 = C_last.V; rw [hsv0, hTV_emp, empty_union])
        fun e u v => ?_
      rw [show shellGraph D d C 0 = D.toGraph.induce (shellVerts D d C 0) from rfl,
        Graph.induce_isLink, hsv0, hTV_emp, empty_union]
      refine ⟨fun ⟨hl, hu, hv⟩ => ?_, fun hl => ⟨hC_le_D.2 hl, hl.2.1, hl.2.2.1⟩⟩
      have heC : e ∈ C_last.E := hSh.edge_induced j_last hl hu hv
      exact ⟨heC, hu, hv, ((hSh.isSubdrawing j_last).closure_inter_V heC).trans hl.2.2.2⟩
    obtain ⟨φ_bd⟩ := (hSh.isClosedDisc j_last).isOArc_discBd
    let φ_C : Circle ≃ₜ C_last.U := φ_bd.trans (Homeomorph.setCongr (hSh.discBd_eq j_last))
    obtain ⟨cyc_out, θ_out, hθ_strict, hθ_Ico, hθ_u, hθ_of_V⟩ :=
      exists_circuitCycle_of_homeo C_last (hSh.isCircuit j_last) hC_sim φ_C 0
    simp only [zero_add] at hθ_Ico hθ_of_V
    obtain ⟨lam, hcyc⟩ := exists_graphN1_empty_inner C_last.toGraph hC_sim cyc_out
    have hcyc' : HasCyclicModel (shellGraph D d C 0) C_last.toGraph cyc_out 1 lam := by
      rw [hG₀_eq]; exact hcyc
    exact ⟨cyc_out, φ_C, θ_out, lam, hθ_strict, hθ_Ico, hθ_u, hθ_of_V, hcyc'⟩

/-- Outward shell induction step (`k ↦ k + 1` for `k + 1 < d`): shift the inner cyclic model on
`shellGraph D d C k` inward by one cylinder ring and attach `C_{d-2-k}` with its radial edges. -/
theorem exists_succ_shell_cyclic_model {S : Type} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S)
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (hSimple : D.toGraph.Simple) (hSh : ShellDiscData D d C Δ)
    {k : ℕ} (hk1 : k + 1 < d)
    (hInv : ShellStepInv D d C k (Nat.lt_of_succ_lt hk1)) :
    ShellStepInv D d C (k + 1) hk1 := by
  classical
  have hd : 0 < d := by omega
  let j_in : Fin d := ⟨d - 1 - k, by omega⟩
  let j_out : Fin d := ⟨d - 1 - (k + 1), by omega⟩
  have hj_succ : j_in.1 = j_out.1 + 1 := by dsimp only [j_in, j_out]; omega
  have hj_lt : j_out < j_in := Fin.lt_def.mpr (by omega)
  obtain ⟨cyc_in, φ_in_U, θ_in, lam_in,
      hθin_strict, hθin_Ico, hθin_u, hθin_of_V, hcyc_in⟩ := hInv
  let G_in := shellGraph D d C k
  let G_out := shellGraph D d C (k + 1)
  let C_in := C j_in
  let C_out := C j_out
  have hCout_le_D : C_out.toGraph ≤ D.toGraph := hSh.subdrawing_toGraph_le j_out
  have hCout_sim : C_out.toGraph.Simple := Simple.mono hSimple hCout_le_D
  have hGout_sim : G_out.Simple := Simple.mono hSimple (shellGraph_le hSh (k + 1))
  have hV_split : shellVerts D d C (k + 1) = shellVerts D d C k ∪ C_out.V := by
    ext x
    simp only [shellVerts, mem_union]
    constructor
    · rintro (hxN | hxUn)
      · exact Or.inl (Or.inl hxN)
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxUn
        by_cases hjeq : j = j_out
        · exact Or.inr (show x ∈ (C j_out).V from hjeq ▸ hxj)
        · have hj_ge : d - 1 - k ≤ j.1 := by
            have : j.1 ≠ d - 1 - (k + 1) := fun h => hjeq (Fin.ext h)
            omega
          exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨j, hj_ge, hxj⟩))
    · rintro ((hxN | hxUn) | hxOut)
      · exact Or.inl hxN
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxUn
        exact Or.inr (mem_iUnion₂.mpr ⟨j, by omega, hxj⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨j_out, le_rfl, hxOut⟩)
  have hGin_le_Gout : G_in ≤ G_out := by
    refine ⟨fun x hx => show x ∈ shellVerts D d C (k + 1) by rw [hV_split]; exact Or.inl hx,
      fun e u v hl => ?_⟩
    rw [show G_in = D.toGraph.induce _ from rfl, Graph.induce_isLink] at hl
    rw [show G_out = D.toGraph.induce _ from rfl, Graph.induce_isLink, hV_split]
    exact ⟨hl.1, Or.inl hl.2.1, Or.inl hl.2.2⟩
  have hCout_le_Gout : C_out.toGraph ≤ G_out := by
    refine ⟨fun x hx => show x ∈ shellVerts D d C (k + 1) by rw [hV_split]; exact Or.inr hx,
      fun e u v hl => ?_⟩
    rw [show G_out = D.toGraph.induce _ from rfl, Graph.induce_isLink, hV_split]
    exact ⟨hCout_le_D.2 hl, Or.inr hl.2.1, Or.inr hl.2.2.1⟩
  have hDisj_Gin_Cout : Disjoint V(G_in) C_out.V := by
    rw [Set.disjoint_left]
    rintro x (hxN | hxUn) hxOut
    · exact Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j_out) hxN hxOut
    · obtain ⟨j, hj_ge, hxj⟩ := mem_iUnion₂.mp hxUn
      have hj_ne : j ≠ j_out := Fin.ne_of_gt (Fin.lt_def.mpr (by dsimp only [j_out]; omega))
      exact Set.disjoint_left.mp (hSh.disjoint_V_ne hj_ne) hxj hxOut
  -- Radial edges between `C_in.V` and `C_out.V`
  let E_rad : Set (Set S) :=
    {e | ∃ u ∈ C_in.V, ∃ v ∈ C_out.V, D.toGraph.IsLink e u v ∧ e ⊆ interior (Δ j_out) \ Δ j_in}
  have hE_rad_fin : E_rad.Finite := by
    refine D.finite_edges.subset ?_
    rintro _ ⟨_, _, _, _, hl, _⟩
    exact hl.1
  have : Finite E_rad := hE_rad_fin.to_subtype
  have hE_Gout : E(G_out) = E(G_in) ∪ C_out.E ∪ E_rad := by
    ext e
    rw [show G_out = D.toGraph.induce _ from rfl, Graph.edgeSet_induce,
      show G_in = D.toGraph.induce _ from rfl, Graph.edgeSet_induce, hV_split]
    constructor
    · rintro ⟨x, y, hl, hx, hy⟩
      by_cases hx_in : x ∈ shellVerts D d C k
      · by_cases hy_in : y ∈ shellVerts D d C k
        · exact Or.inl (Or.inl ⟨x, y, hl, hx_in, hy_in⟩)
        · have hyOut : y ∈ C_out.V := hy.resolve_left hy_in
          rcases hSh.edge_classification hS hd hl with heN | ⟨j, heCj⟩ | ⟨hends, _⟩ | ⟨j, hj, hends, hsub⟩
          · obtain ⟨_, hNV, hNE, _⟩ := innerDraw_spec D d C
            have hyN : y ∈ (innerDraw D d C).V :=
              hNV.symm ▸ (hNE ▸ heN).2 (hl.2.2.2.symm ▸ mem_insert_of_mem x (mem_singleton y))
            exact (Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j_out) hyN hyOut).elim
          · have hcap := (hSh.isSubdrawing j).closure_inter_V heCj
            rw [hl.2.2.2] at hcap
            have hxCj : x ∈ (C j).V := (hcap.symm ▸ mem_insert x {y}).2
            have hyCj : y ∈ (C j).V := (hcap.symm ▸ mem_insert_of_mem x (mem_singleton y)).2
            have hjeq : j = j_out := by
              by_contra hne; exact Set.disjoint_left.mp (hSh.disjoint_V_ne hne) hyCj hyOut
            exact (Set.disjoint_left.mp hDisj_Gin_Cout hx_in
              (show x ∈ (C j_out).V from hjeq ▸ hxCj)).elim
          · have hj_ne : (⟨d - 1, Nat.sub_lt hd zero_lt_one⟩ : Fin d) ≠ j_out :=
              Fin.ne_of_gt (Fin.lt_def.mpr (by dsimp only [j_out]; omega))
            rcases hends with ⟨_, hyL⟩ | ⟨_, hyN⟩
            · exact (Set.disjoint_left.mp (hSh.disjoint_V_ne hj_ne) hyL hyOut).elim
            · exact (Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j_out) hyN hyOut).elim
          · rcases hends with ⟨hx1, hy0⟩ | ⟨hx0, hy1⟩
            · have hj_eq : j = j_out.1 := by
                by_contra hne
                exact Set.disjoint_left.mp (hSh.disjoint_V_ne (Fin.ne_of_val_ne hne)) hy0 hyOut
              have hfin1 : (⟨j + 1, hj⟩ : Fin d) = j_in :=
                Fin.ext (by dsimp only [j_in, j_out] at hj_eq ⊢; omega)
              have hfin0 : (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin d) = j_out := Fin.ext hj_eq
              rw [hfin1] at hx1 hsub; rw [hfin0] at hsub
              exact Or.inr ⟨x, hx1, y, hyOut, hl, hsub⟩
            · exfalso
              have hj1_eq : j + 1 = j_out.1 := by
                by_contra hne
                exact Set.disjoint_left.mp (hSh.disjoint_V_ne (Fin.ne_of_val_ne hne)) hy1 hyOut
              have hx_ge : d - 1 - k ≤ j := by
                rcases hx_in with hxN | hxUn
                · exact (Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V _) hxN hx0).elim
                · obtain ⟨j', hj'_ge, hxj'⟩ := mem_iUnion₂.mp hxUn
                  have : j' = ⟨j, Nat.lt_of_succ_lt hj⟩ := by
                    by_contra hne
                    exact Set.disjoint_left.mp (hSh.disjoint_V_ne hne) hxj' hx0
                  have := congrArg Fin.val this; dsimp only at this; omega
              dsimp only [j_out] at hj1_eq; omega
      · have hxOut : x ∈ C_out.V := hx.resolve_left hx_in
        by_cases hy_in : y ∈ shellVerts D d C k
        · rcases hSh.edge_classification hS hd hl with heN | ⟨j, heCj⟩ | ⟨hends, _⟩ | ⟨j, hj, hends, hsub⟩
          · obtain ⟨_, hNV, hNE, _⟩ := innerDraw_spec D d C
            have hxN : x ∈ (innerDraw D d C).V :=
              hNV.symm ▸ (hNE ▸ heN).2 (hl.2.2.2.symm ▸ mem_insert x {y})
            exact (Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j_out) hxN hxOut).elim
          · have hcap := (hSh.isSubdrawing j).closure_inter_V heCj
            rw [hl.2.2.2] at hcap
            have hxCj : x ∈ (C j).V := (hcap.symm ▸ mem_insert x {y}).2
            have hyCj : y ∈ (C j).V := (hcap.symm ▸ mem_insert_of_mem x (mem_singleton y)).2
            have hjeq : j = j_out := by
              by_contra hne; exact Set.disjoint_left.mp (hSh.disjoint_V_ne hne) hxCj hxOut
            exact (Set.disjoint_left.mp hDisj_Gin_Cout hy_in
              (show y ∈ (C j_out).V from hjeq ▸ hyCj)).elim
          · have hj_ne : (⟨d - 1, Nat.sub_lt hd zero_lt_one⟩ : Fin d) ≠ j_out :=
              Fin.ne_of_gt (Fin.lt_def.mpr (by dsimp only [j_out]; omega))
            rcases hends with ⟨hxN, _⟩ | ⟨hxL, _⟩
            · exact (Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j_out) hxN hxOut).elim
            · exact (Set.disjoint_left.mp (hSh.disjoint_V_ne hj_ne) hxL hxOut).elim
          · rcases hends with ⟨hx1, hy0⟩ | ⟨hx0, hy1⟩
            · exfalso
              have hj1_eq : j + 1 = j_out.1 := by
                by_contra hne
                exact Set.disjoint_left.mp (hSh.disjoint_V_ne (Fin.ne_of_val_ne hne)) hx1 hxOut
              have hy_ge : d - 1 - k ≤ j := by
                rcases hy_in with hyN | hyUn
                · exact (Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V _) hyN hy0).elim
                · obtain ⟨j', hj'_ge, hyj'⟩ := mem_iUnion₂.mp hyUn
                  have : j' = ⟨j, Nat.lt_of_succ_lt hj⟩ := by
                    by_contra hne
                    exact Set.disjoint_left.mp (hSh.disjoint_V_ne hne) hyj' hy0
                  have := congrArg Fin.val this; dsimp only at this; omega
              dsimp only [j_out] at hj1_eq; omega
            · have hj_eq : j = j_out.1 := by
                by_contra hne
                exact Set.disjoint_left.mp (hSh.disjoint_V_ne (Fin.ne_of_val_ne hne)) hx0 hxOut
              have hfin1 : (⟨j + 1, hj⟩ : Fin d) = j_in :=
                Fin.ext (by dsimp only [j_in, j_out] at hj_eq ⊢; omega)
              have hfin0 : (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin d) = j_out := Fin.ext hj_eq
              rw [hfin1] at hy1 hsub; rw [hfin0] at hsub
              exact Or.inr ⟨y, hy1, x, hxOut, hl.symm, hsub⟩
        · have hyOut : y ∈ C_out.V := hy.resolve_left hy_in
          exact Or.inl (Or.inr (hSh.edge_induced j_out hl hxOut hyOut))
    · rintro ((⟨x, y, hl, hx, hy⟩ | heCout) | ⟨u, huIn, v, hvOut, hl, _⟩)
      · exact ⟨x, y, hl, Or.inl hx, Or.inl hy⟩
      · obtain ⟨x, y, hl⟩ := C_out.toGraph.exists_isLink_of_mem_edgeSet heCout
        exact ⟨x, y, hCout_le_D.2 hl, Or.inr hl.2.1, Or.inr hl.2.2.1⟩
      · have hu_sv : u ∈ shellVerts D d C k :=
          Or.inr (mem_iUnion₂.mpr ⟨j_in, by dsimp only [j_in]; exact le_rfl,
            show u ∈ (C j_in).V from huIn⟩)
        exact ⟨u, v, hl, Or.inl hu_sv, Or.inr hvOut⟩
  -- Parameterize each radial edge `i : E_rad` directly from `C_in.V` to `C_out.V`
  have hex_rad : ∀ i : E_rad, ∃ (u v : S) (γ : 𝕀 → S),
      u ∈ C_in.V ∧ v ∈ C_out.V ∧ D.toGraph.IsLink i.1 u v ∧
      Continuous γ ∧ Injective γ ∧ γ 0 = u ∧ γ 1 = v ∧ γ '' Ioo 0 1 = i.1 := by
    intro i
    obtain ⟨u, huIn, v, hvOut, hl, _⟩ := i.2
    have huv : u ≠ v := fun h =>
      Set.disjoint_left.mp (hSh.disjoint_V hj_lt) hvOut (h ▸ huIn)
    obtain ⟨γ, hc, hi, h0, h1, hEq⟩ := exists_edge_arc hl huv
    exact ⟨u, v, γ, huIn, hvOut, hl, hc, hi, h0, h1, hEq⟩
  choose u_rad v_rad γ_rad hu_rad hv_rad hl_rad hγ_cont hγ_inj hγ0 hγ1 hγ_img using hex_rad
  let φ_in_bd : Circle ≃ₜ discBd (Δ j_in) :=
    φ_in_U.trans (Homeomorph.setCongr (hSh.discBd_eq j_in).symm)
  have hin_disc : Δ j_in ⊆ Δ j_out \ discBd (Δ j_out) := by
    rw [show Δ j_out \ discBd (Δ j_out) = discInt (Δ j_out) from rfl,
      discInt_eq_interior_of_isClosedDisc hS (hSh.isClosedDisc j_out)]
    exact hSh.disc_subset_interior hj_lt
  have hp_in_pos : 0 < C_in.V.ncard := by
    dsimp only [C_in, j_in]
    exact Nat.lt_of_lt_of_le zero_lt_two cyc_in.hp
  obtain ⟨cyc_out, φ_out, θ_out, m, σ, α_ord, f,
      hθ_strict, hθ_Ico, hθ_u, hθ_of_V, hα_mono, hα_Ico, hα_end, hf_mono, hf_end⟩ :=
    annulus_monotone_bipartite_order hS (hSh.isClosedDisc j_in) (hSh.isClosedDisc j_out) hin_disc
      φ_in_bd (θ_in ⟨0, hp_in_pos⟩) C_out (hSh.isCircuit j_out) hCout_sim (hSh.discBd_eq j_out)
      γ_rad hγ_cont hγ_inj
      (fun i => by rw [hγ0 i, hSh.discBd_eq j_in]; exact C_in.V_subset_U (hu_rad i))
      (fun i => by rw [hγ1 i]; exact hv_rad i)
      (fun i s hs0 hs1 => by
        obtain ⟨_, _, _, _, _, hsub⟩ := i.2
        exact hsub (hγ_img i ▸ mem_image_of_mem _ ⟨hs0, hs1⟩))
      (fun i₁ i₂ hne => by
        rw [hγ_img i₁, hγ_img i₂, Set.disjoint_left]
        intro x hx₁ hx₂
        exact hne (Subtype.ext (D.edge_eq_of_mem (hl_rad i₁).1 (hl_rad i₂).1 hx₁ hx₂)))
  -- Map `α_ord r ∈ Ico (θ_in 0) (θ_in 0 + 2π)` to inner vertex index `t_in r : Fin p_in`
  have hex_tin : ∀ r : Fin m, ∃ t : Fin C_in.V.ncard, α_ord r = θ_in t := by
    intro r
    have hIco_r := hα_Ico r
    have h0_Ico := hθin_Ico ⟨0, hp_in_pos⟩
    have hv_mem : (φ_in_U (Circle.exp (α_ord r))).1 ∈ C_in.V := by
      have : (φ_in_U (Circle.exp (α_ord r))).1 = (φ_in_bd (Circle.exp (α_ord r))).1 := rfl
      rw [this, hα_end r, hγ0 (σ r)]
      exact hu_rad (σ r)
    have hlt_2pi : α_ord r < 2 * Real.pi := by
      by_contra hge
      let θ' : ℝ := α_ord r - 2 * Real.pi
      have hθ'_Ico : θ' ∈ Ico 0 (2 * Real.pi) :=
        ⟨by linarith [not_lt.mp hge], by linarith [hIco_r.2, h0_Ico.2]⟩
      have hexp_eq : Circle.exp θ' = Circle.exp (α_ord r) :=
        Circle.exp_eq_exp.mpr ⟨-1, by dsimp only [θ']; ring⟩
      obtain ⟨t, ht⟩ := hθin_of_V θ' hθ'_Ico (by rw [hexp_eq]; exact hv_mem)
      have h0_le : θ_in ⟨0, hp_in_pos⟩ ≤ θ_in t :=
        hθin_strict.monotone (Fin.le_def.mpr (Nat.zero_le _))
      linarith [hIco_r.2]
    exact hθin_of_V (α_ord r) ⟨le_trans h0_Ico.1 hIco_r.1, hlt_2pi⟩ hv_mem
  choose t_in ht_in_eq using hex_tin
  let g : Fin m → Fin (C_in.V.ncard + 1) := fun r => ⟨(t_in r).1, Nat.lt_succ_of_lt (t_in r).2⟩
  have hg_mono : Monotone g := fun r₁ r₂ hle =>
    Fin.le_def.mpr (Fin.le_def.mp (hθin_strict.le_iff_le.mp
      (by rw [← ht_in_eq r₁, ← ht_in_eq r₂]; exact hα_mono hle)))
  let attE : Fin m → Set S := fun r => (σ r).1
  have hatt_inj : Injective attE := fun r₁ r₂ h => σ.injective (Subtype.ext h)
  have hrange_attE : range attE = E_rad := by
    ext e
    exact ⟨by rintro ⟨r, rfl⟩; exact (σ r).2, fun he => ⟨σ.symm ⟨e, he⟩, by simp [attE]⟩⟩
  obtain ⟨lam_out, _, hcyc_out⟩ := exists_graphN_succ_cyclic_model
    G_out G_in C_in.toGraph C_out.toGraph hGout_sim hGin_le_Gout hCout_le_Gout hDisj_Gin_Cout
    cyc_in cyc_out hcyc_in attE hatt_inj g f hg_mono hf_mono hV_split
    (hrange_attE.symm ▸ hE_Gout)
    (fun r => by
      rw [show G_out = D.toGraph.induce _ from rfl, Graph.induce_isLink, hV_split]
      have hmod_in : (g r).1 % C_in.V.ncard = (t_in r).1 := Nat.mod_eq_of_lt (t_in r).2
      have hfin_in : (⟨(g r).1 % C_in.V.ncard,
          Nat.mod_lt _ (by have := cyc_in.hp; omega)⟩ : Fin C_in.V.ncard) = t_in r :=
        Fin.ext hmod_in
      have hu_eq : cyc_in.u ⟨(g r).1 % C_in.V.ncard,
          Nat.mod_lt _ (by have := cyc_in.hp; omega)⟩ = u_rad (σ r) := by
        rw [hfin_in, ← hθin_u (t_in r), ← ht_in_eq r]
        exact (hα_end r).trans (hγ0 (σ r))
      have hv_eq : cyc_out.u ⟨(f r).1 % C_out.V.ncard,
          Nat.mod_lt _ (by have := cyc_out.hp; omega)⟩ = v_rad (σ r) :=
        (hf_end r).trans (hγ1 (σ r))
      rw [hu_eq, hv_eq]
      have hu_sv : u_rad (σ r) ∈ shellVerts D d C k :=
        Or.inr (mem_iUnion₂.mpr ⟨j_in, by dsimp only [j_in]; exact le_rfl,
          show u_rad (σ r) ∈ (C j_in).V from hu_rad (σ r)⟩)
      exact ⟨hl_rad (σ r), Or.inl hu_sv, Or.inr (hv_rad (σ r))⟩)
  exact ⟨cyc_out, φ_out, θ_out, lam_out, hθ_strict, hθ_Ico, hθ_u, hθ_of_V, hcyc_out⟩

/-- **Planar Shell-and-Tree Gluing for `(2.3)` (Graph Minors III, page 55):**
Given a simple planar graph `G` with drawing `M` (`HasDrawingRadiusLE M d`) and a `d`-shell `C`,
together with an inner-forest minor bound `IsIsoMinor (G \ ⋃ C_i) (treeY lam₀)` (`1 ≤ lam₀`),
`G` is isomorphic to a minor of `graphN d lam` for some `lam ≥ lam₀`. -/
theorem glue_shell_and_tree {α : Type u} {β : Type v}
    {G : Graph α β} {M : PlanarDrawing G} {d : ℕ} {C : Fin d → Graph α β}
    (hSimple : G.Simple) (hrad : HasDrawingRadiusLE M d) (hShell : IsDShell M d C)
    (lam₀ : ℕ) (_hlam₀ : 1 ≤ lam₀)
    (hMinY : IsIsoMinor (GM09.deleteVertices G (⋃ i : Fin d, V(C i))) (treeY lam₀)) :
    ∃ lam : ℕ, lam₀ ≤ lam ∧ IsIsoMinor G (graphN d lam) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hdel_eq : GM09.deleteVertices G (⋃ i : Fin 0, V(C i)) = G := by
      unfold GM09.deleteVertices
      simp [Graph.induce_vertexSet]
    exact ⟨lam₀, le_rfl, hdel_eq ▸ hMinY⟩
  · have hS : IsClosedSurface M.S := M.isClosedSurface
    have hSph : IsSphere M.S := M.isSphere
    have : ConnectedSpace M.S := (GM11.IsSphere.isClosedSurface hSph).2
    have : T2Space M.S := hS.2.1
    obtain ⟨C_D, Δ, hSimpleD, hMin_GD, hSh₀, hNoCirc₀⟩ :=
      exists_shellDiscData_of_isDShell hSimple hrad hShell
    -- Augment `M.drawing` to `D'` so `innerDraw D' d C_D` is connected whenever nonempty
    have hex_D' : ∃ D' : Drawing M.S,
        D'.toGraph.Simple ∧ M.drawing.toGraph ≤ D'.toGraph ∧
        ShellDiscData D' d C_D Δ ∧
        (∀ C' ≤ (innerDraw D' d C_D).toGraph, ¬ IsGraphCircuit (innerDraw D' d C_D).toGraph C') ∧
        ((innerDraw D' d C_D).V.Nonempty → IsGraphConnected (innerDraw D' d C_D).toGraph) := by
      by_cases hne : (innerDraw M.drawing d C_D).V.Nonempty
      · obtain ⟨D', hSim', hle', hSh', _, hConn', hNo'⟩ :=
          exists_connected_innerDraw hS hSph hd hSimpleD hSh₀ hNoCirc₀ hne
        exact ⟨D', hSim', hle', hSh', hNo', fun _ => hConn'⟩
      · exact ⟨M.drawing, hSimpleD, le_refl _, hSh₀, hNoCirc₀, fun h => (hne h).elim⟩
    obtain ⟨D', hSim', hle_DD', hSh', hNoCirc', hConn_if⟩ := hex_D'
    -- Induct outward from `k = 0` to `k = d - 1`
    have hstep_all : ∀ (k : ℕ) (hk : k < d), ShellStepInv D' d C_D k hk := by
      intro k
      induction k with
      | zero =>
        intro hk
        exact exists_base_shell_cyclic_model hS hSph hk hSim' hSh' hNoCirc' hConn_if
      | succ k ih =>
        intro hk1
        exact exists_succ_shell_cyclic_model hS hSim' hSh' hk1 (ih (Nat.lt_of_succ_lt hk1))
    obtain ⟨cyc₀, _, _, lam₁, _, _, _, _, hcyc_full⟩ :=
      hstep_all (d - 1) (Nat.sub_lt hd zero_lt_one)
    have hG_full : shellGraph D' d C_D (d - 1) = D'.toGraph := by
      unfold shellGraph
      have hsv_eq : shellVerts D' d C_D (d - 1) = D'.V := by
        refine Subset.antisymm (shellVerts_subset_V hSh' (d - 1)) fun v hv => ?_
        obtain ⟨_, hNV, _, _⟩ := innerDraw_spec D' d C_D
        by_cases hvC : ∃ j : Fin d, v ∈ (C_D j).V
        · obtain ⟨j, hvj⟩ := hvC
          exact Or.inr (mem_iUnion₂.mpr ⟨j, by omega, hvj⟩)
        · refine Or.inl ?_
          rw [hNV]
          refine ⟨hv, fun hv_un => ?_⟩
          obtain ⟨j, hvj⟩ := mem_iUnion.mp hv_un
          exact hvC ⟨j, hvj⟩
      rw [hsv_eq]
      exact Graph.induce_vertexSet D'.toGraph
    rw [show d - 1 + 1 = d by omega, hG_full] at hcyc_full
    obtain ⟨_, hlam₁, _, ηv, ηe, _, hm, _, _, _⟩ := hcyc_full
    have hMin_D'_N : IsIsoMinor D'.toGraph (graphN d lam₁) :=
      isIsoMinor_of_isMinorModel D'.toGraph (graphN d lam₁)
        D'.finite_V D'.finite_edges (Set.toFinite _) (Set.toFinite _) ηv ηe hm
    let lam := max lam₀ lam₁
    have hMin_N_mono : IsIsoMinor (graphN d lam₁) (graphN d lam) :=
      graphN_minor_mono_lam hd hlam₁ (le_max_right lam₀ lam₁)
    exact ⟨lam, le_max_left lam₀ lam₁,
      hMin_GD.trans ((isIsoMinor_of_le hle_DD').trans (hMin_D'_N.trans hMin_N_mono))⟩

end ShellInduction

end GraphMinor.GM03
