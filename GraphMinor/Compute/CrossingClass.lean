module

import GraphMinor.Compute.CrossingClassBridgeProved

public import GraphMinor.Compute.SpecsCrossing
import GraphMinor.Compute.Algorithm101Defs
import GraphMinor.Compute.F92GraphCopy
import GraphMinor.Compute.SpecsCrossingReduction
import GraphMinor.Crossing.PlanarFactT
import GraphMinor.HP25.Embedding

/-!
# Classification of a clean instance (`Classify`, Section 6 of
`docs/crossing/crossing_extractor.tex`)

This file proves `classifyProgClaim_of`: given a Word RAM program satisfying `BridgeCrossProgClaim`
(Section 5 of `docs/crossing/crossing_extractor.tex`), we construct the classification program of
Section 6 (`ClassifyProgClaim`), calling `BridgeCross` first and, if no crossing in distinct
bridges is found, invoking the shifted linear-time planarity test (`IsPlanarityProg`) on the
instance's adjacency lists.

We also prove the equivalence between planarity on the active vertex set `S` and planarity on
`Set.univ` for graphs supported on `S` (`nonempty_planeEmbedding_iff_univ`,
`isEmpty_planeEmbedding_iff_univ`), since isolated deleted vertices outside `S` can be placed
outside a closed ball containing the compact drawn set `φ.U`.
-/

public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph Set GraphMinor.Crossing GraphMinor.HP25 GraphMinor.Compute.TwoPaths

/-! ### Planarity on the support set versus `Set.univ` -/

/-- For a graph `G` on `Fin N` supported on `S`, any plane embedding of `G` on `S` extends to a
plane embedding of `G` on `Set.univ` by placing vertices outside `S` at distinct real points outside
a closed ball containing the compact drawn set `φ.U`. -/
noncomputable def extendPlaneEmbeddingUniv {N : ℕ} {G : SimpleGraph (Fin N)} {S : Set (Fin N)}
    [DecidablePred (· ∈ S)] (hG : IsSupportedOn G S) (φ : PlaneEmbedding G S) :
    PlaneEmbedding G Set.univ := by
  have hex : ∃ M : ℝ, 0 < M ∧ φ.U ⊆ Metric.closedBall (0 : ℂ) M :=
    φ.isCompact_U.isBounded.subset_closedBall_lt 0 0
  let M : ℝ := Classical.choose hex
  have hM0 : 0 < M := (Classical.choose_spec hex).1
  have hMU : φ.U ⊆ Metric.closedBall (0 : ℂ) M := (Classical.choose_spec hex).2
  let pt : Fin N → ℂ := fun u =>
    if u ∈ S then φ.pt u else ((M + 1 + (u.val : ℝ) : ℝ) : ℂ)
  have hpt_S : ∀ {u : Fin N}, u ∈ S → pt u = φ.pt u := fun hu => by simp [pt, hu]
  have hpt_not_U : ∀ {u : Fin N}, u ∉ S → pt u ∉ φ.U := by
    intro u hu hmem
    have hball : pt u ∈ Metric.closedBall (0 : ℂ) M := hMU hmem
    have hpt_eq : pt u = ((M + 1 + (u.val : ℝ) : ℝ) : ℂ) := by simp [pt, hu]
    rw [hpt_eq, Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at hball
    have hu0 : (0 : ℝ) ≤ (u.val : ℝ) := Nat.cast_nonneg u.val
    rw [abs_of_pos (by linarith)] at hball
    linarith
  refine
    { pt := pt
      line := φ.line
      finite := Set.toFinite _
      injOn := ?_
      line_comm := φ.line_comm
      isLine := ?_
      inter := ?_
      avoid := ?_ }
  · intro u _ v _ huv
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · rw [hpt_S hu, hpt_S hv] at huv
      exact φ.injOn hu hv huv
    · exfalso
      apply hpt_not_U hv
      rw [← huv, hpt_S hu]
      exact φ.pt_mem_U hu
    · exfalso
      apply hpt_not_U hu
      rw [huv, hpt_S hv]
      exact φ.pt_mem_U hv
    · have huv' : ((M + 1 + (u.val : ℝ) : ℝ) : ℂ) = ((M + 1 + (v.val : ℝ) : ℝ) : ℂ) := by
        simpa [pt, hu, hv] using huv
      have hreal : M + 1 + (u.val : ℝ) = M + 1 + (v.val : ℝ) := Complex.ofReal_inj.mp huv'
      have hcast : (u.val : ℝ) = (v.val : ℝ) := by linarith
      exact Fin.ext (Nat.cast_inj.mp hcast)
  · intro u _ v _ hadj
    have hu : u ∈ S := hG hadj
    have hv : v ∈ S := hG hadj.symm
    rw [hpt_S hu, hpt_S hv]
    exact φ.isLine u hu v hv hadj
  · intro u _ v _ u' _ v' _ hadj hadj' hne z hz
    have hu : u ∈ S := hG hadj
    have hv : v ∈ S := hG hadj.symm
    have hu' : u' ∈ S := hG hadj'
    have hv' : v' ∈ S := hG hadj'.symm
    obtain ⟨w, hw, rfl⟩ := φ.inter u hu v hv u' hu' v' hv' hadj hadj' hne hz
    have hwS : w ∈ S := by
      rcases hw.1 with rfl | rfl <;> assumption
    exact ⟨w, hw, hpt_S hwS⟩
  · intro u _ v _ hadj w _ hptw
    have hu : u ∈ S := hG hadj
    have hv : v ∈ S := hG hadj.symm
    have hwU : pt w ∈ φ.U := φ.line_subset_U hu hv hadj hptw
    have hwS : w ∈ S := by
      by_contra hnot
      exact hpt_not_U hnot hwU
    rw [hpt_S hwS] at hptw
    exact φ.avoid u hu v hv hadj w hwS hptw

/-- For a graph `G` on `Fin N` supported on `S`, `G` has a plane embedding on `S` if and only if it
has a plane embedding on `Set.univ`. -/
theorem nonempty_planeEmbedding_iff_univ {N : ℕ} {G : SimpleGraph (Fin N)} {S : Set (Fin N)}
    (hG : IsSupportedOn G S) :
    Nonempty (PlaneEmbedding G S) ↔ Nonempty (PlaneEmbedding G Set.univ) := by
  classical
  constructor
  · rintro ⟨φ⟩
    exact ⟨extendPlaneEmbeddingUniv hG φ⟩
  · rintro ⟨φ⟩
    exact ⟨φ.mono (fun _ _ _ _ h => h) (Set.subset_univ S)⟩

/-- For a graph `G` on `Fin N` supported on `S`, `PlaneEmbedding G S` is empty if and only if
`PlaneEmbedding G Set.univ` is empty. -/
theorem isEmpty_planeEmbedding_iff_univ {N : ℕ} {G : SimpleGraph (Fin N)} {S : Set (Fin N)}
    (hG : IsSupportedOn G S) :
    IsEmpty (PlaneEmbedding G S) ↔ IsEmpty (PlaneEmbedding G Set.univ) := by
  rw [← not_nonempty_iff, ← not_nonempty_iff, nonempty_planeEmbedding_iff_univ hG]

/-! ### The `Classify` program -/

/-- Copy the instance's adjacency lists `(a.st, a.en, a.ent)` into `(a_base + 30, a_base + 31,
a_base + 32)`, store `N = |a.alive|` into register `r_base + 30`, run `prog.shiftMem r_base a_base`,
and negate the boolean planarity result in `r_base + 35` into `r_base` (`0` for planar / NO, `1`
for nonplanar / YES). -/
def classifyPlanarBranchProg (prog : Cmd) (a : InstArrs) (a_base r_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 1) (.len a.ent))
    (.seq (Alg92.f92CopyBoundedProg a.st (a_base + 30) (r_base + 1) (r_base + 2))
      (.seq (Alg92.f92CopyBoundedProg a.en (a_base + 31) (r_base + 1) (r_base + 2))
        (.seq (.assign (r_base + 30) (.len a.alive))
          (.seq (Alg92.f92CopyBoundedProg a.ent (a_base + 32) (r_base + 30) (r_base + 31))
            (.seq (prog.shiftMem r_base a_base)
              (.assign r_base (.op .sub (.const 1) (.reg (r_base + 35)))))))))

/-- Full `Classify` program: run `P_B` (`BridgeCross`), return `2` (WITNESS) if `r_base = 1`, and
otherwise run `classifyPlanarBranchProg`. -/
def classifyProg (P_B prog : Cmd) (a : InstArrs) (a_base r_base : ℕ) : Cmd :=
  .seq P_B
    (.ite (.op .eq (.reg r_base) (.const 1))
      (.assign r_base (.const 2))
      (classifyPlanarBranchProg prog a a_base r_base))

private theorem inst_arrs_lt {a : InstArrs} {a_Q a_R a_base : ℕ}
    (ha : ArrsOk (a.list ++ [a_Q, a_R]) a_base) :
    a.alive < a_base ∧ a.st < a_base ∧ a.en < a_base ∧ a.ent < a_base ∧ a.cyc < a_base := by
  rcases ha with ⟨_, hlt⟩
  refine ⟨hlt a.alive ?_, hlt a.st ?_, hlt a.en ?_, hlt a.ent ?_, hlt a.cyc ?_⟩ <;>
    simp [InstArrs.list]

private theorem inst_arrs_not_mem_QR {a : InstArrs} {a_Q a_R a_base : ℕ}
    (ha : ArrsOk (a.list ++ [a_Q, a_R]) a_base) :
    a.alive ∉ [a_Q, a_R] ∧ a.st ∉ [a_Q, a_R] ∧ a.en ∉ [a_Q, a_R] ∧
      a.ent ∉ [a_Q, a_R] ∧ a.cyc ∉ [a_Q, a_R] := by
  rcases ha with ⟨hnd, _⟩
  simp only [InstArrs.list, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false] at hnd
  rcases hnd with ⟨h1, h2, h3, h4, h5, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;> tauto

/-- **Classification of a clean instance** (`docs/crossing/crossing_extractor.tex`, Section 6), from
`BridgeCrossProgClaim`. -/
theorem classifyProgClaim_of : ClassifyProgClaim := by
  intro prog Cp cp_w hprog a a_Q a_R a_base r_base ha
  obtain ⟨P_B, C_B, c_B, hP_B⟩ := bridgeCrossProgClaim_proved a a_Q a_R a_base r_base ha
  refine ⟨classifyProg P_B prog a a_base r_base, C_B + Cp + 120, c_B + cp_w + 10, ?_⟩
  intro w N G S D s hw hinst hD
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  have hS : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  have hM_eq : G.edgeSet.ncard = G.edgeFinset.card := ncard_edgeSet_eq G
  have hw_B : wordSize c_B (instSize N G) ≤ w :=
    (wordSize_mono_left (by omega) _).trans hw
  have hw_cp : wordSize cp_w (G.edgeFinset.card + N + 1) ≤ w := by
    have heq : G.edgeFinset.card + N + 1 = instSize N G := by omega
    rw [heq]
    exact (wordSize_mono_left (by omega) _).trans hw
  have hbig : ∀ V, V ≤ 4 * (instSize N G + 1) → V < 2 ^ w := fun V hV =>
    lt_two_pow_of_le_mul hV ((wordSize_mono_left (by omega) _).trans hw)
  have hw1 : 1 < 2 ^ w := hbig 1 (by omega)
  have hw2 : 2 < 2 ^ w := hbig 2 (by omega)
  have hNw : N < 2 ^ w := hbig N (by omega)
  have hent_len : (s.arrs a.ent).length = 2 * G.edgeSet.ncard := hinst.2.2.2.1
  have hent_w : (s.arrs a.ent).length < 2 ^ w := by
    rw [hent_len]
    exact hbig (2 * G.edgeSet.ncard) (by omega)
  have halive_len : (s.arrs a.alive).length = N := by
    rw [hinst.2.1, List.length_ofFn]
  have halive_lt := inst_arrs_lt ha
  have halive_not_QR := inst_arrs_not_mem_QR ha
  -- 1. Execute `P_B`.
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hout₁⟩ := hP_B w N G S D s hw_B hinst hD
  have hs₁_alive : s₁.arrs a.alive = s.arrs a.alive :=
    hk₁.2 a.alive halive_lt.1 halive_not_QR.1
  have hs₁_st : s₁.arrs a.st = s.arrs a.st :=
    hk₁.2 a.st halive_lt.2.1 halive_not_QR.2.1
  have hs₁_en : s₁.arrs a.en = s.arrs a.en :=
    hk₁.2 a.en halive_lt.2.2.1 halive_not_QR.2.2.1
  have hs₁_ent : s₁.arrs a.ent = s.arrs a.ent :=
    hk₁.2 a.ent halive_lt.2.2.2.1 halive_not_QR.2.2.2.1
  rcases hout₁ with ⟨hr₁, hcross₁⟩ | ⟨hr₀, hno_bridge⟩
  · -- Branch 1: `BridgeCross` found a crossing (`s₁.regs r_base = 1`).
    have hcond : (Expr.op .eq (.reg r_base) (.const 1)).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr₁, hw1]
    let s₂ := s₁.setReg r_base 2
    have hex₂ : Exec w (.assign r_base (.const 2)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw2])
    have hex : Exec w (classifyProg P_B prog a a_base r_base) s s₂
        (t₁ + ((Expr.op .eq (.reg r_base) (.const 1)).cost + 2)) :=
      .seq hex₁ (.ite_true hcond (by decide) hex₂)
    refine ⟨s₂, _, hex, ?_, ?_, Or.inl ⟨by simp [s₂], hcross₁⟩⟩
    · simp only [Expr.cost]
      have hpos : 1 ≤ instSize N G := by omega
      calc t₁ + 5 ≤ C_B * instSize N G + 120 * instSize N G := by omega
        _ ≤ (C_B + Cp + 120) * instSize N G := by
          have : C_B + 120 ≤ C_B + Cp + 120 := by omega
          nlinarith
    · refine ⟨fun r hr _ => ?_, fun x hx hnot => ?_⟩
      · rw [State.setReg_regs_ne _ _ (show (r : ℕ) ≠ r_base by omega)]
        exact hk₁.1 r hr (by simp)
      · exact hk₁.2 x hx hnot
  · -- Branch 2: `BridgeCross` returned `0` (`s₁.regs r_base = 0`).
    have hcond : (Expr.op .eq (.reg r_base) (.const 1)).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr₀, hw1, show 0 < 2 ^ w by omega]
    obtain ⟨lists, hadj_s⟩ := hinst.2.2.1
    have hadj₁ : IsAdjList G a.st a.en a.ent lists s₁ :=
      hadj_s.of_arrs_eq hs₁_st hs₁_en hs₁_ent
    let M_ent := (s.arrs a.ent).length
    have hs₁_ent_len : (s₁.arrs a.ent).length = M_ent := by rw [hs₁_ent]
    -- Step 2a: `.assign (r_base + 1) (.len a.ent)`
    let s₂ := s₁.setReg (r_base + 1) M_ent
    have hex₂ : Exec w (.assign (r_base + 1) (.len a.ent)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, hs₁_ent_len, M_ent, hent_w])
    -- Step 2b: bounded copy of `a.st` to `a_base + 30`
    have hst_len : (s₁.arrs a.st).length < 2 ^ w := by
      rw [hadj₁.1.1]; exact hNw
    have hen_len : (s₁.arrs a.en).length < 2 ^ w := by
      rw [hadj₁.1.2.1]; exact hNw
    obtain ⟨s₃, t₃, hex₃, ht₃, hst₃, harr₃, hreg₃⟩ :=
      Alg92.f92CopyBoundedProg_exec a.st (a_base + 30) (r_base + 1) (r_base + 2) M_ent
        (by omega) (by omega) (s₁.arrs a.st) hw1 hent_w hst_len (s := s₂) rfl (by simp [s₂])
    -- Step 2c: bounded copy of `a.en` to `a_base + 31`
    obtain ⟨s₄, t₄, hex₄, ht₄, hen₄, harr₄, hreg₄⟩ :=
      Alg92.f92CopyBoundedProg_exec a.en (a_base + 31) (r_base + 1) (r_base + 2) M_ent
        (by omega) (by omega) (s₁.arrs a.en) hw1 hent_w hen_len (s := s₃)
        (by rw [harr₃ a.en (by omega)]; rfl)
        (by rw [hreg₃ (r_base + 1) (by omega)]; simp [s₂])
    -- Step 2d: `.assign (r_base + 30) (.len a.alive)`
    have hs₄_alive_len : (s₄.arrs a.alive).length = N := by
      rw [harr₄ a.alive (by omega), harr₃ a.alive (by omega)]
      simp [s₂, hs₁_alive, halive_len]
    let s₅ := s₄.setReg (r_base + 30) N
    have hex₅ : Exec w (.assign (r_base + 30) (.len a.alive)) s₄ s₅ 2 :=
      .assign (by simp [Expr.eval, checkWord, hs₄_alive_len, hNw])
    -- Step 2e: bounded copy of `a.ent` to `a_base + 32`
    obtain ⟨s₆, t₆, hex₆, ht₆, hent₆, harr₆, hreg₆⟩ :=
      Alg92.f92CopyBoundedProg_exec a.ent (a_base + 32) (r_base + 30) (r_base + 31) N
        (by omega) (by omega) (s₁.arrs a.ent) hw1 hNw (by rw [hs₁_ent]; exact hent_w) (s := s₅)
        (by simp only [s₅, State.setReg_arrs]; rw [harr₄ a.ent (by omega), harr₃ a.ent (by omega)]; rfl)
        (by simp [s₅])
    -- Step 2f: `prog.shiftMem r_base a_base`
    have hs₆_st : s₆.arrs (a_base + 30) =
        (s₁.arrs a.st).map (fun v => min v (s₁.arrs a.ent).length) := by
      rw [harr₆ (a_base + 30) (by omega)]
      simp only [s₅, State.setReg_arrs]
      rw [harr₄ (a_base + 30) (by omega), hs₁_ent_len]
      exact hst₃
    have hs₆_en : s₆.arrs (a_base + 31) =
        (s₁.arrs a.en).map (fun v => min v (s₁.arrs a.ent).length) := by
      rw [harr₆ (a_base + 31) (by omega)]
      simp only [s₅, State.setReg_arrs, hs₁_ent_len]
      exact hen₄
    have hadj₆ : IsAdjList G (a_base + 30) (a_base + 31) (a_base + 32) lists s₆ :=
      Alg92.f92AdjList_of_bounded_copies hadj₁ hs₆_st hs₆_en hent₆
    have hadj_down : IsAdjList G 30 31 32 lists (s₆.shiftDown r_base a_base) := by
      refine hadj₆.of_arrs_eq ?_ ?_ ?_ <;> rfl
    have hent_down_w : ((s₆.shiftDown r_base a_base).arrs 32).length < 2 ^ w := by
      change (s₆.arrs (a_base + 32)).length < 2 ^ w
      rw [hent₆, List.length_map, hs₁_ent]
      exact hent_w
    have hreg30_down : (s₆.shiftDown r_base a_base).regs 30 = N := by
      change s₆.regs (r_base + 30) = N
      rw [hreg₆ (r_base + 30) (by omega)]
      simp [s₅]
    obtain ⟨s₀', t_p, hex_p, ht_p, _, _, hout_p⟩ :=
      hprog N G lists w hw_cp (s₆.shiftDown r_base a_base) hadj_down hent_down_w hreg30_down
    let s₇ := s₆.shiftUp r_base a_base s₀'
    have hex₇ : Exec w (prog.shiftMem r_base a_base) s₆ s₇ t_p := hex_p.shiftMem
    have hs₇_reg35 : s₇.regs (r_base + 35) = s₀'.regs 35 := by
      change (s₆.shiftUp r_base a_base s₀').regs (r_base + 35) = s₀'.regs 35
      exact State.regs_shiftUp_add r_base a_base s₆ s₀' 35
    -- Step 2g: `.assign r_base (.op .sub (.const 1) (.reg (r_base + 35)))`
    have hkeep_regs : ∀ r < r_base, ∀ (s_end : State),
        (∀ q < r_base, s_end.regs q = s₇.regs q) → s_end.regs r = s.regs r := by
      intro r hr s_end h_end
      rw [h_end r hr]
      change (s₆.shiftUp r_base a_base s₀').regs r = s.regs r
      rw [State.regs_shiftUp_lt _ _ _ _ hr, hreg₆ r (by omega)]
      simp only [s₅]
      rw [State.setReg_regs_ne _ _ (show (r : ℕ) ≠ r_base + 30 by omega),
        hreg₄ r (by omega), hreg₃ r (by omega)]
      simp only [s₂]
      rw [State.setReg_regs_ne _ _ (show (r : ℕ) ≠ r_base + 1 by omega)]
      exact hk₁.1 r hr (by simp)
    have hkeep_arrs : ∀ x < a_base, x ∉ [a_Q, a_R] → s₇.arrs x = s.arrs x := by
      intro x hx hnot
      change (s₆.shiftUp r_base a_base s₀').arrs x = s.arrs x
      rw [State.arrs_shiftUp_lt _ _ _ _ hx, harr₆ x (by omega)]
      simp only [s₅, State.setReg_arrs]
      rw [harr₄ x (by omega), harr₃ x (by omega)]
      simp only [s₂, State.setReg_arrs]
      exact hk₁.2 x hx hnot
    have htime_bound : ∀ t_total,
        t_total = t₁ + (3 + (2 + (t₃ + (t₄ + (2 + (t₆ + (t_p + 4))))))) →
        t_total ≤ (C_B + Cp + 120) * instSize N G := by
      intro t_total htot_eq
      rw [hadj₁.1.1] at ht₃
      rw [hadj₁.1.2.1] at ht₄
      rw [hs₁_ent, hent_len] at ht₆
      rw [ ← hM_eq] at ht_p
      have h1 : t₃ + t₄ + t₆ + 30 ≤ 120 * instSize N G := by omega
      have h2 : Cp * (G.edgeSet.ncard + N + 1) = Cp * instSize N G := by
        rw [hS]; ring
      have h3 : (C_B + Cp + 120) * instSize N G =
          C_B * instSize N G + Cp * instSize N G + 120 * instSize N G := by ring
      omega
    rcases hout_p with ⟨h35_1, hplanar_univ⟩ | ⟨h35_0, hnonplanar_univ⟩
    · -- Planar (`s₀'.regs 35 = 1`), output `0` (NO).
      have heval_sub : (Expr.op .sub (.const 1) (.reg (r_base + 35))).eval w s₇ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hs₇_reg35, h35_1, hw1,
          show 0 < 2 ^ w by omega]
      let s₈ := s₇.setReg r_base 0
      have hex₈ : Exec w (.assign r_base (.op .sub (.const 1) (.reg (r_base + 35)))) s₇ s₈ 4 :=
        .assign heval_sub
      have hex_branch : Exec w (classifyPlanarBranchProg prog a a_base r_base) s₁ s₈
          (2 + (t₃ + (t₄ + (2 + (t₆ + (t_p + 4)))))) :=
        .seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))
      have hex : Exec w (classifyProg P_B prog a a_base r_base) s s₈
          (t₁ + (3 + (2 + (t₃ + (t₄ + (2 + (t₆ + (t_p + 4)))))))) :=
        .seq hex₁ (.ite_false hcond hex_branch)
      have hplanar_S : Nonempty (PlaneEmbedding G (S : Set (Fin N))) :=
        (nonempty_planeEmbedding_iff_univ hinst.1).mpr hplanar_univ
      refine ⟨s₈, _, hex, htime_bound _ rfl, ?_, Or.inr (Or.inl ⟨by simp [s₈], hplanar_S, hno_bridge⟩)⟩
      refine ⟨fun r hr _ => hkeep_regs r hr s₈
        (fun q hq => State.setReg_regs_ne _ _ (show (q : ℕ) ≠ r_base by omega)),
        fun x hx hnot => hkeep_arrs x hx hnot⟩
    · -- Nonplanar (`s₀'.regs 35 = 0`), output `1` (YES).
      have heval_sub : (Expr.op .sub (.const 1) (.reg (r_base + 35))).eval w s₇ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hs₇_reg35, h35_0, hw1,
          show 0 < 2 ^ w by omega]
      let s₈ := s₇.setReg r_base 1
      have hex₈ : Exec w (.assign r_base (.op .sub (.const 1) (.reg (r_base + 35)))) s₇ s₈ 4 :=
        .assign heval_sub
      have hex_branch : Exec w (classifyPlanarBranchProg prog a a_base r_base) s₁ s₈
          (2 + (t₃ + (t₄ + (2 + (t₆ + (t_p + 4)))))) :=
        .seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))
      have hex : Exec w (classifyProg P_B prog a a_base r_base) s s₈
          (t₁ + (3 + (2 + (t₃ + (t₄ + (2 + (t₆ + (t_p + 4)))))))) :=
        .seq hex₁ (.ite_false hcond hex_branch)
      have hnonplanar_S : IsEmpty (PlaneEmbedding G (S : Set (Fin N))) :=
        (isEmpty_planeEmbedding_iff_univ hinst.1).mpr hnonplanar_univ
      refine ⟨s₈, _, hex, htime_bound _ rfl, ?_, Or.inr (Or.inr ⟨by simp [s₈], hnonplanar_S, hno_bridge⟩)⟩
      refine ⟨fun r hr _ => hkeep_regs r hr s₈
        (fun q hq => State.setReg_regs_ne _ _ (show (q : ℕ) ≠ r_base by omega)),
        fun x hx hnot => hkeep_arrs x hx hnot⟩

end GraphMinor.Compute.Crossing
