module

public import GraphMinor.GM08.Section7Model
import GraphMinor.GM05.Main
import GraphMinor.GM05.ShadowMinor
import GraphMinor.Minor.Basic
import GraphMinor.GM12.Section3OneDiscComplement
import GraphMinor.GM11.PerimeterPull

@[expose] public section

/-!
# Graph Minors VIII, Section 7: Tree-Width (Theorem (7.1))

Formalization of (7.1) of Robertson and Seymour,
*Graph Minors. VIII. A Kuratowski theorem for general surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288 (page 267).
-/

namespace GraphMinor
namespace GM08

open Set Function Topology Graph SimpleGraph Surface GM11

/-!
## 1. Constructing an `(r, s)`-Nest from a Monotone Subsequence of Concentric Frames
-/

/-- Helper: in any walk subdrawing `walkDrawing D₀ W`, every point of `(walkDrawing D₀ W).U ∩ D₀.V`
belongs to `W.support`. -/
private theorem mem_support_of_mem_walkDrawing_U_inter_V {D₀ : Drawing SphereSurf}
    {u v x : SphereSurf} (W : GraphWalk D₀.toGraph u v)
    (hxU : x ∈ (walkDrawing D₀ W).U) (hxV : x ∈ D₀.V) : x ∈ W.support := by
  rcases (GM11.mem_walkDrawing_U D₀ W).mp hxU with hx | ⟨e, he, hxe⟩
  · exact hx
  · have hsub := GM11.walkDrawing_isSubdrawing D₀ W
    have heE : e ∈ (walkDrawing D₀ W).E := by rw [GM11.walkDrawing_E]; exact he
    have hxWV : x ∈ closure e ∩ (walkDrawing D₀ W).V := by
      rw [hsub.closure_inter_V heE]
      exact ⟨hxe, hxV⟩
    rw [GM11.walkDrawing_V] at hxWV
    exact hxWV.2

/-- Given a sequence `idx : Fin s → ℕ` (`1 ≤ s`, `idx i ≤ m`) whose corresponding frame circuits
satisfy `(C' (idx i)).U ⊆ discInt (D_ins (idx (i + 1)))` at each step, lifting `r` vertical columns
produces a `DrawingNest D₀ Δ₀ r s`. -/
theorem exists_nest_of_monotone_frames {D₀ : Drawing SphereSurf} {Δ₀ : Set SphereSurf}
    (hΔ₀ : IsClosedDisc Δ₀) (hU₀ : D₀.U ⊆ Δ₀)
    {r s : ℕ} (hs : 1 ≤ s)
    {ηv : (Fin (2 * (2 * s + r + 5)) × Fin (2 * (2 * s + r + 5))) → Set SphereSurf}
    {ηe : Sym2 (Fin (2 * (2 * s + r + 5)) × Fin (2 * (2 * s + r + 5))) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph (2 * (2 * s + r + 5))) D₀.toGraph ηv ηe)
    (C' : ℕ → Drawing SphereSurf)
    (dc : ∀ k, k ≤ 2 * s → DiscCircuit D₀ Δ₀)
    (hdc_U : ∀ k (hk : k ≤ 2 * s), (dc k hk).U = (C' k).U)
    (hC'_hit : ∀ k, k ≤ 2 * s →
      ∀ p ∈ frameGridSet (2 * (2 * s + r + 5)) k, ((C' k).V ∩ ηv p).Nonempty)
    (idx : Fin s → ℕ) (hidx : ∀ i : Fin s, idx i ≤ 2 * s)
    (hstep : ∀ (i : Fin s) (hi : i.1 + 1 < s),
      (C' (idx i)).U ⊆ discInt (dc (idx ⟨i.1 + 1, hi⟩) (hidx ⟨i.1 + 1, hi⟩)).ins) :
    Nonempty (DrawingNest D₀ Δ₀ r s) := by
  let m := 2 * s
  let θ := 2 * (2 * s + r + 5)
  have hstep_discInt : ∀ (a b : ℕ) (hb : b < s) (hab : a < b),
      (C' (idx ⟨a, Nat.lt_trans hab hb⟩)).U ⊆
        discInt (dc (idx ⟨b, hb⟩) (hidx ⟨b, hb⟩)).ins ∧
      discInt (dc (idx ⟨a, Nat.lt_trans hab hb⟩) (hidx ⟨a, Nat.lt_trans hab hb⟩)).ins ⊆
        discInt (dc (idx ⟨b, hb⟩) (hidx ⟨b, hb⟩)).ins := by
    intro a b hb hab
    obtain ⟨d, hd⟩ : ∃ d, b = a + 1 + d := ⟨b - (a + 1), by omega⟩
    induction d generalizing b with
    | zero =>
      have hb_eq : b = a + 1 := by omega
      subst hb_eq
      have h1 := hstep ⟨a, by omega⟩ hb
      have henc : OArcEncloses Δ₀ (dc (idx ⟨a + 1, hb⟩) (hidx _)).U
          (dc (idx ⟨a, by omega⟩) (hidx _)).U := by
        rw [oArcEncloses_iff_subset hΔ₀ (dc (idx ⟨a + 1, hb⟩) (hidx _)).isInside, hdc_U]
        exact h1.trans (discInt_subset _)
      exact ⟨h1, (insideDisc_subset_of_oArcEncloses hΔ₀
        (dc (idx ⟨a + 1, hb⟩) (hidx _)).isInside
        (dc (idx ⟨a, by omega⟩) (hidx _)).isInside henc).2⟩
    | succ d ih =>
      have hb' : a + 1 + d < s := by omega
      obtain ⟨hU_mid, hint_mid⟩ := ih (a + 1 + d) hb' (by omega) rfl
      have hmid_eq : (⟨a + 1 + d, hb'⟩ : Fin s).1 + 1 < s := by dsimp; omega
      have h1 : (C' (idx ⟨a + 1 + d, hb'⟩)).U ⊆
          discInt (dc (idx ⟨b, hb⟩) (hidx ⟨b, hb⟩)).ins := by
        have hb_fin : (⟨b, hb⟩ : Fin s) = ⟨a + 1 + d + 1, hmid_eq⟩ := by ext; dsimp; omega
        rw [hb_fin]
        exact hstep ⟨a + 1 + d, hb'⟩ hmid_eq
      have henc : OArcEncloses Δ₀ (dc (idx ⟨b, hb⟩) (hidx _)).U
          (dc (idx ⟨a + 1 + d, hb'⟩) (hidx _)).U := by
        rw [oArcEncloses_iff_subset hΔ₀ (dc (idx ⟨b, hb⟩) (hidx _)).isInside, hdc_U]
        exact h1.trans (discInt_subset _)
      have hint_top := (insideDisc_subset_of_oArcEncloses hΔ₀
        (dc (idx ⟨b, hb⟩) (hidx _)).isInside
        (dc (idx ⟨a + 1 + d, hb'⟩) (hidx _)).isInside henc).2
      exact ⟨hU_mid.trans hint_top, hint_mid.trans hint_top⟩
  -- Construct a path-connected column set `R p` for each `p : Fin r`.
  let k_in := idx ⟨0, hs⟩
  let k_out := idx ⟨s - 1, Nat.sub_lt hs Nat.one_pos⟩
  have hk_in : k_in ≤ m := hidx ⟨0, hs⟩
  have hk_out : k_out ≤ m := hidx ⟨s - 1, Nat.sub_lt hs Nat.one_pos⟩
  have hrad : ∀ p : Fin r, ∃ R : Set SphereSurf,
      IsPreconnected R ∧ R ⊆ D₀.U ∧
      (R ∩ (dc k_in hk_in).U).Nonempty ∧
      (R ∩ (dc k_out hk_out).U).Nonempty ∧
      ∀ x ∈ R ∩ D₀.V, ∃ t : Fin θ, x ∈ ηv (t, ⟨m + 3 + p.1, by omega⟩) := by
    intro p
    let col : Fin θ := ⟨m + 3 + p.1, by omega⟩
    let n_col := θ - 2
    let p_col : ℕ → Fin θ × Fin θ := fun t => (⟨min t (θ - 1), by omega⟩, col)
    have hadj_col : ∀ t ≤ n_col, (pathGraph θ □ pathGraph θ).Adj (p_col t) (p_col (t + 1)) := by
      intro t ht; simp only [p_col, boxProd_adj, pathGraph_adj]; left
      exact ⟨Or.inl (by omega), trivial⟩
    have hinj_col : ∀ i ≤ n_col + 1, ∀ j ≤ n_col + 1, p_col i = p_col j → i = j := by
      intro i hi j hj h; have := congrArg (fun x => x.1.1) h; dsimp only [p_col] at this; omega
    obtain ⟨x₀, hx₀⟩ := hm.vertex_nonempty (p_col 0) (mem_gridGraph_V _)
    let W_col := liftGridSteps hm n_col p_col hadj_col hx₀
    obtain ⟨_, hW_el, hW_sup, _⟩ := liftGridSteps_props hm n_col p_col hadj_col hinj_col hx₀
    have hk_in_le : k_in ≤ n_col := by omega
    have hk_out_le : k_out ≤ n_col := by omega
    have hp_in_mem : p_col k_in ∈ frameGridSet θ k_in :=
      Set.mem_iUnion.mpr ⟨0, by dsimp [sideGridSet, p_col, col]; omega⟩
    have hp_out_mem : p_col k_out ∈ frameGridSet θ k_out :=
      Set.mem_iUnion.mpr ⟨0, by dsimp [sideGridSet, p_col, col]; omega⟩
    obtain ⟨u_in, hu_inC, hu_in_η⟩ := hC'_hit k_in hk_in _ hp_in_mem
    obtain ⟨u_out, hu_outC, hu_out_η⟩ := hC'_hit k_out hk_out _ hp_out_mem
    obtain ⟨B_in, _, hB_in_sup⟩ :=
      exists_branch_walk hm (p_col k_in) (edgeLeft_mem hm (hadj_col k_in hk_in_le)) hu_in_η
    obtain ⟨B_out, _, hB_out_sup⟩ :=
      exists_branch_walk hm (p_col k_out) (edgeLeft_mem hm (hadj_col k_out hk_out_le)) hu_out_η
    let R := ((walkDrawing D₀ W_col).U ∪ (walkDrawing D₀ B_in).U) ∪ (walkDrawing D₀ B_out).U
    have hpc_W := isPathConnected_walkDrawing_U D₀ W_col
    have hpc_in := isPathConnected_walkDrawing_U D₀ B_in
    have hpc_out := isPathConnected_walkDrawing_U D₀ B_out
    have hmeet_in : edgeLeft hm (hadj_col k_in hk_in_le) ∈
        (walkDrawing D₀ W_col).U ∩ (walkDrawing D₀ B_in).U :=
      ⟨(walkDrawing D₀ W_col).V_subset_U (by rw [GM11.walkDrawing_V]; exact hW_el k_in hk_in_le),
       (walkDrawing D₀ B_in).V_subset_U (by rw [GM11.walkDrawing_V]; exact B_in.start_mem_support)⟩
    have hmeet_out : edgeLeft hm (hadj_col k_out hk_out_le) ∈
        ((walkDrawing D₀ W_col).U ∪ (walkDrawing D₀ B_in).U) ∩ (walkDrawing D₀ B_out).U :=
      ⟨Or.inl ((walkDrawing D₀ W_col).V_subset_U
        (by rw [GM11.walkDrawing_V]; exact hW_el k_out hk_out_le)),
       (walkDrawing D₀ B_out).V_subset_U
        (by rw [GM11.walkDrawing_V]; exact B_out.start_mem_support)⟩
    have hR_pc : IsPathConnected R := (hpc_W.union hpc_in ⟨_, hmeet_in⟩).union hpc_out ⟨_, hmeet_out⟩
    have hR_sub : R ⊆ D₀.U := union_subset
      (union_subset (GM11.walkDrawing_isSubdrawing D₀ W_col).U_subset
        (GM11.walkDrawing_isSubdrawing D₀ B_in).U_subset)
      (GM11.walkDrawing_isSubdrawing D₀ B_out).U_subset
    refine ⟨R, hR_pc.isConnected.isPreconnected, hR_sub, ?_, ?_, ?_⟩
    · refine ⟨u_in, Or.inl (Or.inr ((walkDrawing D₀ B_in).V_subset_U
        (by rw [GM11.walkDrawing_V]; exact B_in.end_mem_support))), ?_⟩
      rw [hdc_U k_in hk_in]
      exact (C' k_in).V_subset_U hu_inC
    · refine ⟨u_out, Or.inr ((walkDrawing D₀ B_out).V_subset_U
        (by rw [GM11.walkDrawing_V]; exact B_out.end_mem_support)), ?_⟩
      rw [hdc_U k_out hk_out]
      exact (C' k_out).V_subset_U hu_outC
    · rintro x ⟨hxR, hxV⟩
      rcases hxR with (hxW | hxBin) | hxBout
      · have hxs := mem_support_of_mem_walkDrawing_U_inter_V W_col hxW hxV
        rcases hW_sup x hxs with rfl | ⟨t, _, hxt⟩
        · exact ⟨(p_col (n_col + 1)).1, edgeRight_mem hm (hadj_col n_col le_rfl)⟩
        · exact ⟨(p_col t).1, hxt⟩
      · have hxs := mem_support_of_mem_walkDrawing_U_inter_V B_in hxBin hxV
        exact ⟨(p_col k_in).1, hB_in_sup x hxs⟩
      · have hxs := mem_support_of_mem_walkDrawing_U_inter_V B_out hxBout hxV
        exact ⟨(p_col k_out).1, hB_out_sup x hxs⟩
  refine ⟨{
    circuit := fun i => dc (idx i) (hidx i)
    inside_of_lt := fun {i j} hij => by
      intro x hx
      rw [hdc_U (idx i) (hidx i)] at hx
      have hmem := (hstep_discInt i.1 j.1 j.2 hij).1 hx
      exact (insideOArc_iff_mem_discInt hΔ₀ (dc (idx j) (hidx j)).isInside).mpr hmem
    radialPath := fun p => (hrad p).choose
    isPreconnected_radialPath := fun p => (hrad p).choose_spec.1
    radialPath_sub_U := fun p => (hrad p).choose_spec.2.1
    radialPath_sub_disc := fun p => (hrad p).choose_spec.2.1.trans hU₀
    pairwise_disjoint_paths := fun p q hpq => by
      refine Set.disjoint_left.mpr fun x hxp hxq => ?_
      obtain ⟨t₁, hx₁⟩ := (hrad p).choose_spec.2.2.2.2 x hxp
      obtain ⟨t₂, hx₂⟩ := (hrad q).choose_spec.2.2.2.2 x hxq
      have hne : (t₁, (⟨m + 3 + p.1, by omega⟩ : Fin θ)) ≠
          (t₂, (⟨m + 3 + q.1, by omega⟩ : Fin θ)) := by
        intro h
        have := congrArg (fun z => z.2.1) h
        dsimp at this
        exact hpq (Fin.ext (by omega))
      exact Set.disjoint_left.mp
        (hm.vertex_disjoint _ (mem_gridGraph_V _) _ (mem_gridGraph_V _) hne) hx₁ hx₂
    meets_inner := fun p _ => (hrad p).choose_spec.2.2.1
    meets_outer := fun p _ => (hrad p).choose_spec.2.2.2.1
  }⟩

/-!
## 2. Two-Case Cascade on `2s + 1` Concentric Frames and Proof of `(7.1)`
-/

/-- Any minor model of `gridGraph (2 * (2 * s + r + 5))` in a sphere-disc drawing `(D₀, Δ₀)`
produces an `(r, s)`-nest `DrawingNest D₀ Δ₀ r s`. -/
theorem exists_nest_of_grid_model {D₀ : Drawing SphereSurf} {Δ₀ : Set SphereSurf}
    (hΔ₀ : IsClosedDisc Δ₀) (hU₀ : D₀.U ⊆ Δ₀)
    {r s : ℕ} (hs : 1 ≤ s)
    {ηv : (Fin (2 * (2 * s + r + 5)) × Fin (2 * (2 * s + r + 5))) → Set SphereSurf}
    {ηe : Sym2 (Fin (2 * (2 * s + r + 5)) × Fin (2 * (2 * s + r + 5))) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph (2 * (2 * s + r + 5))) D₀.toGraph ηv ηe) :
    Nonempty (DrawingNest D₀ Δ₀ r s) := by
  classical
  let m := 2 * s
  let c₀ := m + 2
  let θ := 2 * (2 * s + r + 5)
  have hsph : Surface.IsSphere SphereSurf := ⟨Homeomorph.refl _⟩
  have hS_sph : IsClosedSurface SphereSurf := (GM11.IsSphere.isClosedSurface hsph).1
  have hbd_frame : ∀ k ≤ m, 2 * k + 4 ≤ θ := fun k hk => by omega
  let C' : ℕ → Drawing SphereSurf := fun k =>
    if hk : 2 * k + 4 ≤ θ then (exists_frame_circuit hm k hk).choose else D₀
  have hC'_spec : ∀ k (hk : k ≤ m),
      (C' k).IsCircuit ∧
      (C' k).IsSubdrawing D₀ ∧
      (∀ x ∈ (C' k).V, ∃ p ∈ frameGridSet θ k, x ∈ ηv p) ∧
      (∀ p ∈ frameGridSet θ k, ((C' k).V ∩ ηv p).Nonempty) ∧
      (∀ {a b c d : SphereSurf},
        a ∈ (C' k).V ∩ sideBranchSet ηv k 0 →
        b ∈ (C' k).V ∩ sideBranchSet ηv k 1 →
        c ∈ (C' k).V ∩ sideBranchSet ηv k 2 →
        d ∈ (C' k).V ∩ sideBranchSet ηv k 3 →
        PairsCrossOn (C' k).U a c b d) := by
    intro k hk
    have hk' := hbd_frame k hk
    simp only [C', hk', ↓reduceDIte]
    exact (exists_frame_circuit hm k hk').choose_spec
  let dc : ∀ k, k ≤ m → DiscCircuit D₀ Δ₀ := fun k hk =>
    let spec := hC'_spec k hk
    let hU_sub_D₀ : (C' k).U ⊆ D₀.U := spec.2.1.U_subset
    let hU_sub_Δ₀ : (C' k).U ⊆ Δ₀ := hU_sub_D₀.trans hU₀
    let hOArc : IsOArc (C' k).U := GM11.IsCircuit.isOArc_U spec.1
    let D_k := (disc_oArc Δ₀ (C' k).U hΔ₀ hU_sub_Δ₀ hOArc).choose
    have hD_k : IsInsideDisc Δ₀ (C' k).U D_k :=
      (disc_oArc Δ₀ (C' k).U hΔ₀ hU_sub_Δ₀ hOArc).choose_spec.1
    { U := (C' k).U
      ins := D_k
      U_sub_drawing := hU_sub_D₀
      U_sub_disc := hU_sub_Δ₀
      isOArc_U := hOArc
      isInside := hD_k }
  have hdc_U : ∀ k (hk : k ≤ m), (dc k hk).U = (C' k).U := fun _ _ => rfl
  have hdc_ins_congr : ∀ {a b : ℕ} (ha : a ≤ m) (hb : b ≤ m), a = b →
      (dc a ha).ins = (dc b hb).ins := by
    rintro a b ha hb rfl
    rfl
  have hC'_disj_U : ∀ k₁ k₂ (hk₁ : k₁ ≤ m) (hk₂ : k₂ ≤ m), k₁ ≠ k₂ →
      Disjoint (C' k₁).U (C' k₂).U := by
    intro k₁ k₂ hk₁ hk₂ hne
    refine disjoint_U_of_disjoint_V (hC'_spec k₁ hk₁).2.1 (hC'_spec k₂ hk₂).2.1
      (Set.disjoint_left.mpr fun x hx₁ hx₂ => ?_)
    obtain ⟨p, hp, hxp⟩ := (hC'_spec k₁ hk₁).2.2.1 x hx₁
    obtain ⟨q, hq, hxq⟩ := (hC'_spec k₂ hk₂).2.2.1 x hx₂
    have hpq : p ≠ q := fun h =>
      Set.disjoint_left.mp (frameGridSet_disjoint (hbd_frame k₁ hk₁) (hbd_frame k₂ hk₂) hne)
        hp (h ▸ hq)
    exact Set.disjoint_left.mp
      (hm.vertex_disjoint p (mem_gridGraph_V p) q (mem_gridGraph_V q) hpq) hxp hxq
  have hC'_pc : ∀ k (hk : k ≤ m), IsPreconnected (C' k).U := by
    intro k hk
    obtain ⟨u, W, -, -, hV, hE⟩ := (hC'_spec k hk).1
    obtain ⟨W', hsW, heW⟩ := (hC'_spec k hk).2.1.exists_walk_up W
    have hEq : C' k = walkDrawing D₀ W' := Drawing.ext_of_V_E
      (by rw [hV, GM11.walkDrawing_V, hsW]) (by rw [hE, GM11.walkDrawing_E, heW])
    rw [hEq]
    exact (isPathConnected_walkDrawing_U D₀ W').isConnected.isPreconnected
  have hC'_side : ∀ k₁ k₂ (hk₁ : k₁ ≤ m) (hk₂ : k₂ ≤ m), k₁ ≠ k₂ →
      (C' k₁).U ⊆ discInt (dc k₂ hk₂).ins ∨ Disjoint (C' k₁).U (dc k₂ hk₂).ins := by
    intro k₁ k₂ hk₁ hk₂ hne
    have hins := (dc k₂ hk₂).isInside
    refine side_of_closedDisc hΔ₀ hins.1 (dc k₁ hk₁).U_sub_disc hins.2.1 (hC'_pc k₁ hk₁) ?_
    rw [hins.2.2.1]
    exact hC'_disj_U k₁ k₂ hk₁ hk₂ hne
  have hC'_nonempty : ∀ k (hk : k ≤ m), ((C' k).U).Nonempty := by
    intro k hk
    have hp : (⟨k, by omega⟩, ⟨k, by omega⟩) ∈ frameGridSet θ k :=
      Set.mem_iUnion.mpr ⟨0, by dsimp [sideGridSet]; omega⟩
    obtain ⟨x, hxV, _⟩ := (hC'_spec k hk).2.2.2.1 _ hp
    exact ⟨x, (C' k).V_subset_U hxV⟩
  -- Key propagation: if `C'_{k-1}` is outside `D_ins k`, then `C'_{k+1}` is inside `D_ins k`
  -- AND `C'_k` is outside `D_ins (k + 1)`.
  have hprop_step : ∀ k (hk1 : 1 ≤ k) (hkm : k + 1 ≤ m),
      Disjoint (C' (k - 1)).U (dc k (by omega)).ins →
      (C' (k + 1)).U ⊆ discInt (dc k (by omega)).ins ∧
        Disjoint (C' k).U (dc (k + 1) hkm).ins := by
    intro k hk1 hkm hdis_prev
    have hk_le : k ≤ m := by omega
    have hk_prev : k - 1 ≤ m := by omega
    have hin_next : (C' (k + 1)).U ⊆ discInt (dc k hk_le).ins := by
      rcases hC'_side (k + 1) k hkm hk_le (by omega) with hin | hdis_next
      · exact hin
      · exfalso
        let D_k := (dc k hk_le).ins
        have hDk := (dc k hk_le).isInside
        let E := closure (univ \ D_k)
        obtain ⟨hE_disc, hE_bd⟩ :=
          GM12.isClosedDisc_closure_compl_of_sphere hS_sph hsph hDk.2.1
        have hE_bd' : discBd E = (C' k).U := hE_bd.trans hDk.2.2.1
        have hsub_compl : ∀ {X : Set SphereSurf}, Disjoint X D_k → X ⊆ discInt E := by
          intro X hX x hx
          have hx_not_Dk : x ∉ D_k := Set.disjoint_left.mp hX hx
          refine ⟨subset_closure ⟨mem_univ x, hx_not_Dk⟩, ?_⟩
          rw [hE_bd]
          exact fun hbd => hx_not_Dk (Surface.discBd_subset D_k hbd)
        exact not_same_disc_of_three_frames hm hk1
          (by omega)
          (c₀ := c₀) (by omega) (by omega)
          (hC'_spec (k - 1) hk_prev).2.1 (hC'_spec k hk_le).2.1 (hC'_spec (k + 1) hkm).2.1
          (hC'_spec (k - 1) hk_prev).1 (hC'_spec (k + 1) hkm).1
          (hC'_spec (k - 1) hk_prev).2.2.1 (hC'_spec k hk_le).2.2.1 (hC'_spec (k + 1) hkm).2.2.1
          (hC'_spec (k - 1) hk_prev).2.2.2.1 (hC'_spec k hk_le).2.2.2.1
          (hC'_spec (k + 1) hkm).2.2.2.1
          (hC'_spec k hk_le).2.2.2.2
          hE_disc hE_bd' (hsub_compl hdis_prev) (hsub_compl hdis_next)
    refine ⟨hin_next, ?_⟩
    rcases hC'_side k (k + 1) hk_le hkm (by omega) with hin_rev | hdis_rev
    · exfalso
      have henc : OArcEncloses Δ₀ (dc k hk_le).U (dc (k + 1) hkm).U := by
        rw [oArcEncloses_iff_subset hΔ₀ (dc k hk_le).isInside, hdc_U (k + 1) hkm]
        exact hin_next.trans (discInt_subset _)
      have hint_sub := (insideDisc_subset_of_oArcEncloses hΔ₀
        (dc k hk_le).isInside (dc (k + 1) hkm).isInside henc).2
      obtain ⟨x, hx⟩ := hC'_nonempty k hk_le
      have hx_int : x ∈ discInt (dc k hk_le).ins := hint_sub (hin_rev hx)
      exact hx_int.2 ((dc k hk_le).isInside.2.2.1 ▸ hx)
    · exact hdis_rev
  -- Two-case cascade on `{1, ..., s - 1}`.
  by_cases hall : ∀ k (_ : 1 ≤ k) (_ : k ≤ s - 1), ¬ Disjoint (C' (k - 1)).U (dc k (by omega)).ins
  · -- Case 1: `(C'_0, ..., C'_{s-1})` is nested insideward-to-outward.
    refine exists_nest_of_monotone_frames hΔ₀ hU₀ hs hm C' dc hdc_U
      (fun k hk => (hC'_spec k hk).2.2.2.1)
      (fun i => i.1) (fun i => by have := i.2; omega) ?_
    intro i hi
    have hnot := hall (i.1 + 1) (by omega) (by omega)
    rcases hC'_side i.1 (i.1 + 1) (by omega) (by omega) (by omega)
      with hin | hdis
    · simpa using hin
    · exact absurd hdis (by simpa using hnot)
  · -- Case 2: pick `1 ≤ k₀ ≤ s - 1` with `C'_{k₀ - 1}` outside `D_ins k₀`; cascade outward!
    push Not at hall
    obtain ⟨k₀, hk₀_lo, hk₀_hi, hdis₀⟩ := hall
    have hcascade : ∀ d (hbd : k₀ + d + 1 ≤ m),
        (C' (k₀ + d + 1)).U ⊆ discInt (dc (k₀ + d) (by omega)).ins ∧
        Disjoint (C' (k₀ + d)).U (dc (k₀ + d + 1) hbd).ins := by
      intro d
      induction d with
      | zero =>
        intro hbd
        simpa using hprop_step k₀ hk₀_lo hbd hdis₀
      | succ d ih =>
        intro hbd
        obtain ⟨_, hdis_d⟩ := ih (by omega)
        have hstep_d := hprop_step (k₀ + d + 1) (by omega) hbd (by simpa using hdis_d)
        simpa [Nat.add_assoc] using hstep_d
    refine exists_nest_of_monotone_frames hΔ₀ hU₀ hs hm C' dc hdc_U
      (fun k hk => (hC'_spec k hk).2.2.2.1)
      (fun i => k₀ + s - i.1) (fun i => by omega) ?_
    intro i hi
    let d := s - (i.1 + 1)
    have hd_bd : k₀ + d + 1 ≤ m := by omega
    have h1 := (hcascade d hd_bd).1
    have heq₁ : k₀ + s - i.1 = k₀ + d + 1 := by omega
    have heq₂ : k₀ + s - (i.1 + 1) = k₀ + d := by omega
    have ha_bd : k₀ + s - (i.1 + 1) ≤ m := by omega
    have hb_bd : k₀ + d ≤ m := by omega
    dsimp only
    rw [heq₁, hdc_ins_congr ha_bd hb_bd heq₂]
    exact h1

/-- **(7.1)** (Graph Minors VIII, Section 7, page 267):
"Let $r, s \ge 0$ be integers. Then there is an integer $w$ such that every drawing in a disc
with no $(r, s)$-nest has tree-width $\le w$." -/
theorem theorem_7_1_proof (r s : ℕ) :
    ∃ w : ℕ, ∀ {S : Type*} [TopologicalSpace S] (D : Drawing S) (Δ : Set S),
      IsClosedDisc Δ → D.U ⊆ Δ → IsEmpty (DrawingNest D Δ r s) → DrawingTreeWidthLE D w := by
  by_cases hs0 : s = 0
  · subst hs0
    refine ⟨0, fun {S} _ D Δ _ _ hEmpty => ?_⟩
    exfalso
    refine hEmpty.false {
      circuit := Fin.elim0
      inside_of_lt := fun {i} => i.elim0
      radialPath := fun _ => ∅
      isPreconnected_radialPath := fun _ => isPreconnected_empty
      radialPath_sub_U := fun _ => empty_subset _
      radialPath_sub_disc := fun _ => empty_subset _
      pairwise_disjoint_paths := fun _ _ _ => by simp
      meets_inner := fun _ h => absurd h (Nat.not_lt_zero 0)
      meets_outer := fun _ h => absurd h (Nat.not_lt_zero 0)
    }
  · have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
    let θ := 2 * (2 * s + r + 5)
    have hθ6 : 6 ≤ θ := by dsimp [θ]; omega
    have hθ_even : Even θ := ⟨2 * s + r + 5, by dsimp [θ]; ring⟩
    refine ⟨GM05.θ₉ θ, fun {S} _ D Δ hΔ hDU hEmpty => ?_⟩
    obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
    obtain ⟨D₀, iso, hD₀U, hD₀V, -⟩ := sc.exists_transport_drawing hΔ D hDU
    have hΔ₀ : IsClosedDisc (f '' Δ) := (sc.disc_f Subset.rfl hΔ).1
    have hU₀ : D₀.U ⊆ f '' Δ := hD₀U ▸ image_mono hDU
    rw [DrawingTreeWidthLE, graphTreeWidthLE_iff_of_iso iso,
      graphTreeWidthLE_iff_gm05 D₀.finite_V]
    by_contra hnot_tw
    have hnot_F : GM05.simpleShadow D₀.toGraph ∉ GM01.𝓕 θ := fun hmem =>
      hnot_tw (GM05.theorem_7_3_proved hθ6 hθ_even D₀.finite_V hmem)
    rw [GM01.𝓕, Set.mem_ofPred_eq, not_not] at hnot_F
    have hminor_D₀ : IsIsoMinor (GM01.gridGraph θ) D₀.toGraph :=
      hnot_F.trans (GM05.simpleShadow_isIsoMinor D₀.toGraph D₀.finite_V D₀.finite_edges)
    obtain ⟨ηv, ηe, hm⟩ :=
      exists_isMinorModel_of_isIsoMinor D₀.finite_V D₀.finite_edges hminor_D₀
    obtain ⟨N₀⟩ := exists_nest_of_grid_model hΔ₀ hU₀ hs hm
    exact hEmpty.false (sc.pullBackNest hΔ hDU hD₀U hD₀V N₀)

/-- `drawingTreeWidth` formulation of (7.1). -/
theorem theorem_7_1_treeWidth (r s : ℕ) :
    ∃ w : ℕ, ∀ {S : Type*} [TopologicalSpace S] (D : Drawing S) (Δ : Set S),
      IsClosedDisc Δ → D.U ⊆ Δ → IsEmpty (DrawingNest D Δ r s) → drawingTreeWidth D ≤ w := by
  obtain ⟨w, hw⟩ := theorem_7_1_proof r s
  exact ⟨w, fun D Δ hΔ hDU hE => Nat.sInf_le (hw D Δ hΔ hDU hE)⟩

end GM08
end GraphMinor
