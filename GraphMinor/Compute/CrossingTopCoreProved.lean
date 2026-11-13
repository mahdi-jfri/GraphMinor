module

import GraphMinor.Compute.PlanarityProved
import GraphMinor.Compute.CrossingClassProg
import GraphMinor.Compute.CrossingLiftProg

public import GraphMinor.Compute.CrossingTopLift
public import GraphMinor.Compute.CrossingTopClean2
public import GraphMinor.Compute.CrossingTopBuild
public import GraphMinor.Compute.CrossingOpsReplace
public import GraphMinor.Compute.CrossingOpsSparsify
public import GraphMinor.Compute.CrossingCleanRestore
public import GraphMinor.Compute.CrossingLoop
public import GraphMinor.Crossing.LinkLift

/-!
# The Top-Level Crossing Extractor and the Disjoint Paths Theorem from Planarity

This file assembles the top-level crossing extractor of `docs/crossing/crossing_extractor.tex`
(Section 10):
1. `buildInitProg` (`CrossingTopBuild.lean`) compacts the input adjacency lists into an initial
   instance `IsInstanceAt (topInstArrs a_base) G Finset.univ D` and allocates the record buffer
   `IsRecBufAt (a_base + 5) r_base [] cap`.
2. `initialCleaningRecFullProgClaim_of` (`CrossingTopClean2.lean`) cleans the initial instance to
   `(G', S', D)` while preserving `HP25.IsCrossed G D ↔ HP25.IsCrossed G' D`.
3. `ClassifyProgClaim` classifies `(G', S', D)`:
   * `0` (`NO`): `G'` is planar on `S'` and has no crossing in distinct bridges; by Lemma 4
     (`not_isCrossed_of_planar_of_no_distinctBridges`) and cleaning equivalence, `¬ HP25.IsCrossed G D`.
   * `1` (`YES`): `G'` is nonplanar on `S'`; by Fact T (`isCrossed_of_clean_of_isEmpty_planeEmbedding`),
     `HP25.IsCrossed G' D`, and `LoopRecProgClaim` produces a crossing pair `IsCrossingPairAt K' D' a_Q a_R`.
   * `2` (`WITNESS`): `Classify` directly returns a crossing pair `IsCrossingPairAt G' D a_Q a_R`.
4. In the `YES` and `WITNESS` branches, `LiftRecHistProgClaim` and `liftHistory_proved` lift the
   crossing pair back to `IsCrossingPairAt G D a_Q a_R`, and `orientCrossingProg`
   (`CrossingTopBuild.lean`) orients `a_Q, a_R` into walks `Q, R` satisfying `HP25.IsCrossing G D Q R`.

Combining `crossingExtractor_of` with `shiloach80Statement_of_crossingExtractor`,
`algorithm_9_9_of_case3Steps`, and `disjointPathsStatement_of_shiloach` yields
`disjointPathsStatement_of_planarity`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing GraphMinor.Compute.TwoPaths

local macro "ne_nat" : tactic => `(tactic| (change (_ : ℕ) ≠ _; omega))

/-- The top-level crossing extractor program (Section 10 of
`docs/crossing/crossing_extractor.tex`). -/
def crossingExtractorProg (C_buf : ℕ) (a_st a_en a_ent a_cyc a_Q a_R : Arr)
    (a_base : ℕ) (r_N r_out r_base : Reg)
    (P_clean P_class P_loop P_lift : Cmd) : Cmd :=
  .seq (buildInitProg C_buf a_st a_en a_ent a_cyc a_base r_N r_base)
  (.seq P_clean
  (.seq P_class
  (.ite (.op .eq (.reg (r_base + 1)) (.const 0))
    (.assign r_out (.const 0))
    (.seq (.ite (.op .eq (.reg (r_base + 1)) (.const 1)) P_loop .skip)
      (.seq P_lift
        (.seq (orientCrossingProg a_cyc a_Q a_R (a_base + 6) r_N (r_base + 1))
              (.assign r_out (.const 1))))))))

theorem arrsOk_topInstArrs_rec (a_base : ℕ) :
    ArrsOk ((topInstArrs a_base).list ++ [a_base + 5]) (a_base + 6) := by
  dsimp [ArrsOk, topInstArrs, InstArrs.list]
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      not_false_eq_true, List.nodup_nil, and_true]
    refine ⟨⟨by omega, by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega⟩,
      ⟨by omega, by omega⟩,
      by omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem arrsOk_topInstArrs_QR {a_Q a_R a_base : ℕ}
    (hQ : a_Q < a_base) (replaceRecProgClaim_proved : a_R < a_base) (hQR : a_Q ≠ a_R) :
    ArrsOk ((topInstArrs a_base).list ++ [a_Q, a_R]) (a_base + 6) := by
  dsimp [ArrsOk, topInstArrs, InstArrs.list]
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      not_false_eq_true, List.nodup_nil, and_true]
    refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega⟩,
      ⟨by omega, by omega⟩,
      hQR⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem arrsOk_topInstArrs_rec_QR {a_Q a_R a_base : ℕ}
    (hQ : a_Q < a_base) (replaceRecProgClaim_proved : a_R < a_base) (hQR : a_Q ≠ a_R) :
    ArrsOk ((topInstArrs a_base).list ++ [a_base + 5, a_Q, a_R]) (a_base + 6) := by
  dsimp [ArrsOk, topInstArrs, InstArrs.list]
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      not_false_eq_true, List.nodup_nil, and_true]
    refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega⟩,
      ⟨by omega, by omega⟩,
      hQR⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem arrsOk_rec_QR {a_Q a_R a_base : ℕ}
    (hQ : a_Q < a_base) (replaceRecProgClaim_proved : a_R < a_base) (hQR : a_Q ≠ a_R) :
    ArrsOk [a_base + 5, a_Q, a_R] (a_base + 6) := by
  dsimp [ArrsOk]
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      not_false_eq_true, List.nodup_nil, and_true]
    exact ⟨⟨by omega, by omega⟩, hQR⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega

theorem arrsOk_cyc_QR {a_cyc a_Q a_R a_base : ℕ}
    (hcyc : a_cyc < a_base) (hQ : a_Q < a_base) (replaceRecProgClaim_proved : a_R < a_base)
    (hcQ : a_cyc ≠ a_Q) (hcR : a_cyc ≠ a_R) (hQR : a_Q ≠ a_R) :
    ArrsOk [a_cyc, a_Q, a_R] (a_base + 6) := by
  dsimp [ArrsOk]
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      not_false_eq_true, List.nodup_nil, and_true]
    exact ⟨⟨hcQ, hcR⟩, hQR⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega

/-- Length of a `D`-path list on `Fin N` is at most `N`. -/
theorem length_le_of_isDPathList {N : ℕ} {G : SimpleGraph (Fin N)} {D L : List (Fin N)}
    (h : IsDPathList G D L) : L.length ≤ N := by
  simpa using h.1.2.1.length_le_card

/-- In `IsRecBufAt a_rec r_rec recs k s`, `s.regs r_rec ≤ (s.arrs a_rec).length`. -/
theorem regs_le_length_of_isRecBufAt {N : ℕ} {a_rec r_rec : ℕ}
    {recs : List (CrossRecord (Fin N))} {k : ℕ} {s : State}
    (h : IsRecBufAt a_rec r_rec recs k s) :
    s.regs r_rec ≤ (s.arrs a_rec).length := by
  obtain ⟨ls, -, harr, hreg⟩ := h
  rw [harr, hreg, List.length_append]
  omega

theorem isHistory_append {V : Type*} [DecidableEq V] {recs₁ recs₂ : List (CrossRecord V)} :
    ∀ {st₁ st₂ st₃ : SimpleGraph V × Set V × List V},
      IsHistory st₁ recs₁ st₂ → IsHistory st₂ recs₂ st₃ → IsHistory st₁ (recs₁ ++ recs₂) st₃
  | st₁, _, _, h₁, h₂ => by
    rcases recs₁ with _ | ⟨rec, rs⟩
    · cases h₁; exact h₂
    · rcases st₁ with ⟨G, S, D⟩
      cases rec with
      | repl r =>
        obtain ⟨hG, hS, hval, hrest⟩ := h₁
        exact ⟨hG, hS, hval, isHistory_append hrest h₂⟩
      | contr r =>
        obtain ⟨hG, hS, hD, hval, hrest⟩ := h₁
        exact ⟨hG, hS, hD, hval, isHistory_append hrest h₂⟩
      | del G' S' =>
        obtain ⟨hle, hsub, hsupp, hD, hce, hrest⟩ := h₁
        exact ⟨hle, hsub, hsupp, hD, hce, isHistory_append hrest h₂⟩

theorem contractionsLong_append {N : ℕ} {recs₁ recs₂ : List (CrossRecord (Fin N))}
    (h₁ : ContractionsLong recs₁) (h₂ : ContractionsLong recs₂) :
    ContractionsLong (recs₁ ++ recs₂) := fun r hr => by
  rcases List.mem_append.mp hr with hr₁ | hr₂
  · exact h₁ r hr₁
  · exact h₂ r hr₂

/-- **The crossing extractor** (`CrossingExtractorStatement`, Sections 4–12 of
`docs/crossing/crossing_extractor.tex`), proved from planarity testing (`PlanarityTestStatement`),
replacement (`ReplaceRecProgClaim`), classification (`ClassifyProgClaim`), the contraction
trial loop (`LoopRecProgClaim`), and lifting (`LiftRecHistProgClaim`). -/
theorem crossingExtractor_of_full : CrossingExtractorStatement := by
  intro a_st a_en a_ent a_cyc a_Q a_R a_base r_N r_out r_base hok hrN hrout hNout
  have hst_lt : a_st < a_base := hok.2 a_st (by simp)
  have hen_lt : a_en < a_base := hok.2 a_en (by simp)
  have hent_lt : a_ent < a_base := hok.2 a_ent (by simp)
  have hcyc_lt : a_cyc < a_base := hok.2 a_cyc (by simp)
  have hQ_lt : a_Q < a_base := hok.2 a_Q (by simp)
  have hR_lt : a_R < a_base := hok.2 a_R (by simp)
  have hnd := hok.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  have hcQ : a_cyc ≠ a_Q := hnd.2.2.2.1.1
  have hcR : a_cyc ≠ a_R := hnd.2.2.2.1.2
  have hQR : a_Q ≠ a_R := hnd.2.2.2.2.1
  obtain ⟨prog_pl, Cp, cp_w, -, -, hPlProg⟩ := planarityTestStatement_closed
  obtain ⟨P_clean, C_cln, c_cln, hP_clean⟩ :=
    initialCleaningRecFullProgClaim_of (topInstArrs a_base) (a_base + 5) r_base
      (a_base + 6) (r_base + 1) (arrsOk_topInstArrs_rec a_base) (by omega)
  obtain ⟨P_class, C_cls, c_cls, hP_class⟩ :=
    classifyProgClaim_proved prog_pl Cp cp_w hPlProg (topInstArrs a_base) a_Q a_R (a_base + 6) (r_base + 1)
      (arrsOk_topInstArrs_QR hQ_lt hR_lt hQR)
  obtain ⟨P_loop, C_lp, c_lp, hP_loop⟩ :=
    loopRecProgClaim_of prog_pl Cp cp_w hPlProg (topInstArrs a_base) (a_base + 5) r_base a_Q a_R
      (a_base + 6) (r_base + 1) (arrsOk_topInstArrs_rec_QR hQ_lt hR_lt hQR) (by omega)
  obtain ⟨P_lift, C_lft, c_lft, hP_lift⟩ :=
    liftRecHistProgClaim_proved (a_base + 5) r_base a_Q a_R (a_base + 6) (r_base + 1)
      (arrsOk_rec_QR hQ_lt hR_lt hQR) (by omega)
  set C_buf := C_cln + 4 * C_lp + 1
  set K_scale := 2 * C_buf + 105
  set c_sum := c_cln + c_cls + c_lp + c_lft + 1
  refine ⟨crossingExtractorProg C_buf a_st a_en a_ent a_cyc a_Q a_R a_base r_N r_out r_base
            P_clean P_class P_loop P_lift,
          4 * C_buf + C_cln + 4 * C_cls + 4 * C_lp + (2 * C_buf + 1) * C_lft + 500,
          c_sum * (K_scale + 3),
          by omega,
          Nat.mul_pos (by dsimp [c_sum]; omega) (by dsimp [K_scale]; omega), ?_⟩
  intro N G lists D w s hw hadj hent_w hN_reg hcyc hD
  set E := G.edgeSet.ncard
  set M₀ := (N + 1) * (E + N + 1)
  have hsz_eq : instSize N G = E + N + 1 := by unfold instSize; omega
  have hM₀_eq : (N + 1) * instSize N G = M₀ := by rw [hsz_eq]
  have hM₀_ge1 : 1 ≤ M₀ := Nat.mul_pos (by omega) (by omega)
  have hN1_le_M₀ : N + 1 ≤ M₀ := Nat.le_mul_of_pos_right _ (by omega)
  have hsz_le_M₀ : instSize N G ≤ M₀ := by
    rw [← hM₀_eq]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hN2_le_M₀ : (N + 1) * (N + 1) ≤ M₀ := Nat.mul_le_mul_left _ (by omega)
  have hK_expand : K_scale * (M₀ + 1) = 2 * C_buf * M₀ + 105 * M₀ + 2 * C_buf + 105 := by
    dsimp [K_scale]; ring
  -- Word size bounds
  have hw_big : (2 * C_buf + 4) * (N + 1) * instSize N G + 100 < 2 ^ w := by
    have hle : (2 * C_buf + 4) * (N + 1) * instSize N G + 100 ≤ K_scale * (M₀ + 1) := by
      rw [mul_assoc, hM₀_eq, hK_expand]
      have : (2 * C_buf + 4) * M₀ = 2 * C_buf * M₀ + 4 * M₀ := by ring
      omega
    have hw_1 : wordSize (K_scale + 3) M₀ ≤ w := by
      have : K_scale + 3 ≤ c_sum * (K_scale + 3) :=
        Nat.le_mul_of_pos_left _ (by dsimp [c_sum]; omega)
      exact (wordSize_mono_left this M₀).trans hw
    exact lt_two_pow_of_le_mul hle hw_1
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have h4N_w : 4 * N + 4 < 2 ^ w := by
    have : 4 * (N + 1) ≤ (2 * C_buf + 4) * (N + 1) * instSize N G := by
      calc 4 * (N + 1)
          ≤ (2 * C_buf + 4) * (N + 1) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (2 * C_buf + 4) * (N + 1) * instSize N G := Nat.le_mul_of_pos_right _ (by omega)
    omega
  -- Step 1: buildInitProg
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hinst₁, hrec₁, hcap_ge⟩ :=
    buildInitProg_exec C_buf a_st a_en a_ent a_cyc a_base r_N r_base
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> omega)
      hrN hadj hent_w hN_reg hcyc hD hw_big
  set cap := C_buf * (N + 1) * (N + 2 * E + 1)
  have hcap_le : cap ≤ 2 * C_buf * M₀ := by
    have : N + 2 * E + 1 ≤ 2 * (E + N + 1) := by omega
    calc C_buf * (N + 1) * (N + 2 * E + 1)
        ≤ C_buf * (N + 1) * (2 * (E + N + 1)) := Nat.mul_le_mul_left _ this
      _ = 2 * C_buf * M₀ := by dsimp [M₀]; ring
  have hrec₁_len : (s₁.arrs (a_base + 5)).length = cap := by
    obtain ⟨ls, hls, harr, -⟩ := hrec₁
    cases hls
    simp [harr]
  -- Step 2: P_clean
  have hw_clean : wordSize c_cln ((N + 1) * instSize N G + (s₁.arrs (a_base + 5)).length) ≤ w := by
    have hle : (N + 1) * instSize N G + (s₁.arrs (a_base + 5)).length ≤ K_scale * (M₀ + 1) := by
      rw [hM₀_eq, hrec₁_len, hK_expand]
      omega
    exact (wordSize_le_of_le_mul' hle).trans
      ((wordSize_mono_left (Nat.mul_le_mul_right _ (by dsimp [c_sum]; omega)) M₀).trans hw)
  have hcap_cln : C_cln * (N + 1) * instSize N G ≤ cap := by
    calc C_cln * (N + 1) * instSize N G
        ≤ C_buf * (N + 1) * instSize N G :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by dsimp [C_buf]; omega))
      _ ≤ cap := hcap_ge
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, G', S', recs₁, k₁,
          hinst₂, hD₂, hclean₂, hhist₂, hlong₂, hcross_iff, hrec₂, hedge₂, hlen₂, hk₁_bound⟩ :=
    hP_clean w N G Finset.univ D [] cap s₁ hw_clean hinst₁ hD hrec₁ hcap_cln
  rw [List.nil_append] at hrec₂
  have hrec₂_len : (s₂.arrs (a_base + 5)).length = cap := by rw [hlen₂, hrec₁_len]
  have hsz_G' : instSize N G' ≤ 4 * instSize N G := by
    unfold instSize; omega
  have hM_G' : (N + 1) * instSize N G' ≤ 4 * M₀ := by
    rw [← hM₀_eq]
    calc (N + 1) * instSize N G' ≤ (N + 1) * (4 * instSize N G) := Nat.mul_le_mul_left _ hsz_G'
      _ = 4 * ((N + 1) * instSize N G) := by ring
  -- Step 3: P_class on (G', S', D)
  have hw_class : wordSize c_cls (instSize N G') ≤ w := by
    have hle : instSize N G' ≤ K_scale * (M₀ + 1) := by
      rw [hK_expand]
      omega
    exact (wordSize_le_of_le_mul' hle).trans
      ((wordSize_mono_left (Nat.mul_le_mul_right _ (by dsimp [c_sum]; omega)) M₀).trans hw)
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hclass_cases⟩ :=
    hP_class w N G' S' D s₂ hw_class hinst₂ hD₂
  have ht₃_le : t₃ ≤ 4 * C_cls * M₀ := by
    calc t₃ ≤ C_cls * instSize N G' := ht₃
      _ ≤ C_cls * (4 * instSize N G) := Nat.mul_le_mul_left _ hsz_G'
      _ ≤ C_cls * (4 * M₀) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * C_cls * M₀ := by ring
  rw [mul_assoc, hM₀_eq] at ht₁ ht₂
  have hlow₃_regs : ∀ r < r_base, s₃.regs r = s.regs r := fun r hr => by
    rw [hk₃.1 r (by omega) (by simp), hk₂.1 r (by omega) (by simp; omega), hk₁.1 r hr (by simp)]
  have hlow₃_arrs : ∀ x < a_base, x ≠ a_Q → x ≠ a_R → s₃.arrs x = s.arrs x := fun x hx hxQ hxR => by
    rw [hk₃.2 x (by omega) (by simp [hxQ, hxR]),
      hk₂.2 x (by omega) (by dsimp [topInstArrs, InstArrs.list]; simp; omega),
      hk₁.2 x hx (by simp)]
  -- Check if Classify returned 0 (NO)
  rcases hclass_cases with ⟨hr_cls2, hpair₃⟩ | ⟨hr_cls0, hpl₃, hno₃⟩ | ⟨hr_cls1, hnpl₃, _⟩
  · -- Case WITNESS (r_base + 1 = 2)
    have hcond0 : (Expr.op .eq (.reg (r_base + 1)) (.const 0)).eval w s₃ = some 0 := by
      have := eval_eq (eval_reg hr_cls2 (by omega)) (eval_const h0_w) hw1
      simpa using this
    have hcond1 : (Expr.op .eq (.reg (r_base + 1)) (.const 1)).eval w s₃ = some 0 := by
      have := eval_eq (eval_reg hr_cls2 (by omega)) (eval_const hw1) hw1
      simpa using this
    have hex_loop : Exec w (.ite (.op .eq (.reg (r_base + 1)) (.const 1)) P_loop .skip) s₃ s₃ _ :=
      .ite_false hcond1 (.skip s₃)
    have hrec₃ : IsRecBufAt (a_base + 5) r_base recs₁ k₁ s₃ := by
      obtain ⟨ls, hls, harr, hreg⟩ := hrec₂
      refine ⟨ls, hls, ?_, ?_⟩
      · rw [hk₃.2 (a_base + 5) (by omega) (by simp; omega), harr]
      · rw [hk₃.1 r_base (by omega) (by simp), hreg]
    have hrec₃_len : (s₃.arrs (a_base + 5)).length = cap := by
      rw [hk₃.2 (a_base + 5) (by omega) (by simp; omega), hrec₂_len]
    obtain ⟨L₁, L₂, hcp₃, hQ₃, hR₃⟩ := hpair₃
    have hw_lift : wordSize c_lft ((s₃.arrs (a_base + 5)).length + (N + 1) * (N + 1)) ≤ w := by
      have hle : (s₃.arrs (a_base + 5)).length + (N + 1) * (N + 1) ≤ K_scale * (M₀ + 1) := by
        rw [hrec₃_len, hK_expand]
        omega
      exact (wordSize_le_of_le_mul' hle).trans
        ((wordSize_mono_left (Nat.mul_le_mul_right _ (by dsimp [c_sum]; omega)) M₀).trans hw)
    obtain ⟨s₅, t₅, hex₅, ht₅, hk₅, P', hlift₅, hQ₅, hR₅⟩ :=
      hP_lift w N G G' Finset.univ S' D D recs₁ k₁ L₁ L₂ s₃ hw_lift
        hhist₂ hlong₂ hcp₃ hrec₃ hQ₃ hR₃
        (length_le_of_isDPathList hcp₃.1) (length_le_of_isDPathList hcp₃.2.1)
    have hcp_G : IsCrossingPair G D P'.1 P'.2 :=
      (liftHistory_proved G ((Finset.univ : Finset (Fin N)) : Set (Fin N)) D recs₁
        G' (S' : Set (Fin N)) D L₁ L₂ (Set.toFinite _) hinst₁.1 hD hhist₂ hlong₂ hcp₃).2 P' hlift₅
    have hpair₅ : IsCrossingPairAt G D a_Q a_R s₅ := ⟨P'.1, P'.2, hcp_G, hQ₅, hR₅⟩
    have hrN₅ : s₅.regs r_N = N := by
      rw [hk₅.1 r_N (by omega) (by simp), hlow₃_regs r_N hrN, hN_reg]
    have hcyc₅ : s₅.arrs a_cyc = D.map Fin.val := by
      rw [hk₅.2 a_cyc (by omega) (by simp [hcQ, hcR]), hlow₃_arrs a_cyc hcyc_lt hcQ hcR, hcyc]
    obtain ⟨s₆, t₆, hex₆, ht₆, hk₆, a₀, b₀, c₀, d₀, Q, R, hcross₆, hQ₆, hR₆⟩ :=
      orientCrossingProg_exec (w := w) a_cyc a_Q a_R (a_base + 6) r_N (r_base + 1)
        (arrsOk_cyc_QR hcyc_lt hQ_lt hR_lt hcQ hcR hQR) (by omega)
        hrN₅ hcyc₅ hD hpair₅ h4N_w
    set s₇ := s₆.setReg r_out 1
    have hex₇ : Exec w (.assign r_out (.const 1)) s₆ s₇ 2 := .assign (eval_const hw1)
    have hex_ite : Exec w (.ite (.op .eq (.reg (r_base + 1)) (.const 0)) (.assign r_out (.const 0))
        (.seq (.ite (.op .eq (.reg (r_base + 1)) (.const 1)) P_loop .skip)
          (.seq P_lift (.seq (orientCrossingProg a_cyc a_Q a_R (a_base + 6) r_N (r_base + 1))
            (.assign r_out (.const 1)))))) s₃ s₇ _ :=
      .ite_false hcond0 (.seq hex_loop (.seq hex₅ (.seq hex₆ hex₇)))
    refine ⟨s₇, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex_ite)), ?_, ?_,
      Or.inl ⟨by simp [s₇], a₀, b₀, c₀, d₀, Q, R, hcross₆, hQ₆, hR₆⟩⟩
    · have hr_rec_le : s₃.regs r_base ≤ cap := by
        rw [← hrec₃_len]; exact regs_le_length_of_isRecBufAt hrec₃
      have hN2_le : (N + 1) * (N + 1) ≤ M₀ := Nat.mul_le_mul_left _ (by omega)
      have ht₅_le : t₅ ≤ C_lft * ((2 * C_buf + 1) * M₀) := by
        calc t₅ ≤ C_lft * (s₃.regs r_base + (N + 1) * (N + 1)) := ht₅
          _ ≤ C_lft * (2 * C_buf * M₀ + M₀) := Nat.mul_le_mul_left _ (by omega)
          _ = C_lft * ((2 * C_buf + 1) * M₀) := by ring
      simp only [Expr.cost]
      have hgoal_eq :
          (4 * C_buf + C_cln + 4 * C_cls + 4 * C_lp + (2 * C_buf + 1) * C_lft + 500) *
            (N + 1) * (E + N + 1) =
          (2 * C_buf + 150) * M₀ + C_cln * M₀ + 4 * C_cls * M₀ + C_lft * ((2 * C_buf + 1) * M₀) +
            (2 * C_buf + 4 * C_lp) * M₀ + 350 * M₀ := by
        dsimp [M₀]; ring
      rw [hgoal_eq]
      omega
    · refine ⟨fun r hr hro => ?_, fun x hx hxQR => ?_⟩
      · simp only [List.mem_singleton] at hro
        simp only [s₇, State.setReg_regs_ne _ _ (show (r : Reg) ≠ r_out by ne_nat)]
        rw [hk₆.1 r (by omega) (by simp), hk₅.1 r (by omega) (by simp), hlow₃_regs r hr]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxQR
        simp only [s₇, State.setReg_arrs]
        rw [hk₆.2 x (by omega) (by simp [hxQR.1, hxQR.2]),
          hk₅.2 x (by omega) (by simp [hxQR.1, hxQR.2]),
          hlow₃_arrs x hx hxQR.1 hxQR.2]
  · -- Case NO (r_base + 1 = 0)
    have hcond0 : (Expr.op .eq (.reg (r_base + 1)) (.const 0)).eval w s₃ = some 1 := by
      have := eval_eq (eval_reg hr_cls0 (by omega)) (eval_const h0_w) hw1
      simpa using this
    set s₄ := s₃.setReg r_out 0
    have hex₄ : Exec w (.assign r_out (.const 0)) s₃ s₄ 2 := .assign (eval_const h0_w)
    have hex_ite : Exec w (.ite (.op .eq (.reg (r_base + 1)) (.const 0)) (.assign r_out (.const 0))
        (.seq (.ite (.op .eq (.reg (r_base + 1)) (.const 1)) P_loop .skip)
          (.seq P_lift (.seq (orientCrossingProg a_cyc a_Q a_R (a_base + 6) r_N (r_base + 1))
            (.assign r_out (.const 1)))))) s₃ s₄ _ :=
      .ite_true hcond0 (by decide) hex₄
    have hnot_cross_G' : ¬ HP25.IsCrossed G' D :=
      not_isCrossed_of_planar_of_no_distinctBridges hpl₃ hinst₂.1 hD₂ hno₃
    have hnot_cross_G : ¬ HP25.IsCrossed G D :=
      fun hcr => hnot_cross_G' (hcross_iff.mp hcr)
    refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex_ite)), ?_, ?_,
      Or.inr ⟨by simp [s₄], hnot_cross_G⟩⟩
    · simp only [Expr.cost]
      have hgoal_eq :
          (4 * C_buf + C_cln + 4 * C_cls + 4 * C_lp + (2 * C_buf + 1) * C_lft + 500) *
            (N + 1) * (E + N + 1) =
          (2 * C_buf + 150) * M₀ + C_cln * M₀ + 4 * C_cls * M₀ +
            (2 * C_buf + 4 * C_lp + (2 * C_buf + 1) * C_lft) * M₀ + 350 * M₀ := by
        dsimp [M₀]; ring
      rw [hgoal_eq]
      omega
    · refine ⟨fun r hr hro => ?_, fun x hx hxQR => ?_⟩
      · simp only [List.mem_singleton] at hro
        simp only [s₄, State.setReg_regs_ne _ _ (show (r : Reg) ≠ r_out by ne_nat)]
        exact hlow₃_regs r hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxQR
        exact hlow₃_arrs x hx hxQR.1 hxQR.2
  · -- Case YES (r_base + 1 = 1)
    have hcond0 : (Expr.op .eq (.reg (r_base + 1)) (.const 0)).eval w s₃ = some 0 := by
      have := eval_eq (eval_reg hr_cls1 (by omega)) (eval_const h0_w) hw1
      simpa using this
    have hcond1 : (Expr.op .eq (.reg (r_base + 1)) (.const 1)).eval w s₃ = some 1 := by
      have := eval_eq (eval_reg hr_cls1 (by omega)) (eval_const hw1) hw1
      simpa using this
    have hcross_G' : HP25.IsCrossed G' D :=
      isCrossed_of_clean_of_isEmpty_planeEmbedding (Set.toFinite _) hinst₂.1 hD₂ hclean₂ hnpl₃
    have hinst₃ : IsInstanceAt (topInstArrs a_base) G' S' D s₃ := by
      obtain ⟨h1, h2, ⟨l_adj, h3⟩, h4, h5⟩ := hinst₂
      have ha_eq : ∀ y ∈ (topInstArrs a_base).list, s₃.arrs y = s₂.arrs y := fun y hy =>
        hk₃.2 y (arrsOk_topInstArrs_QR hQ_lt hR_lt hQR |>.2 y (List.mem_append_left _ hy))
          (by
            simp only [topInstArrs, InstArrs.list, List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
      refine ⟨h1, ?_, ⟨l_adj, h3.of_arrs_eq (ha_eq _ (by simp [InstArrs.list]))
        (ha_eq _ (by simp [InstArrs.list])) (ha_eq _ (by simp [InstArrs.list]))⟩,
        by rw [ha_eq _ (by simp [InstArrs.list]), h4],
        by rw [ha_eq _ (by simp [InstArrs.list]), h5]⟩
      rw [ha_eq _ (by simp [InstArrs.list]), h2]
    have hrec₃ : IsRecBufAt (a_base + 5) r_base recs₁ k₁ s₃ := by
      obtain ⟨ls, hls, harr, hreg⟩ := hrec₂
      refine ⟨ls, hls, ?_, ?_⟩
      · rw [hk₃.2 (a_base + 5) (by omega) (by simp; omega), harr]
      · rw [hk₃.1 r_base (by omega) (by simp), hreg]
    have hrec₃_len : (s₃.arrs (a_base + 5)).length = cap := by
      rw [hk₃.2 (a_base + 5) (by omega) (by simp; omega), hrec₂_len]
    have hw_loop : wordSize c_lp ((N + 1) * instSize N G' + (s₃.arrs (a_base + 5)).length) ≤ w := by
      have hle : (N + 1) * instSize N G' + (s₃.arrs (a_base + 5)).length ≤ K_scale * (M₀ + 1) := by
        rw [hrec₃_len, hK_expand]
        omega
      exact (wordSize_le_of_le_mul' hle).trans
        ((wordSize_mono_left (Nat.mul_le_mul_right _ (by dsimp [c_sum]; omega)) M₀).trans hw)
    have hcap_lp : C_lp * (N + 1) * instSize N G' ≤ k₁ := by
      have h1 : C_lp * (N + 1) * instSize N G' ≤ 4 * C_lp * M₀ := by
        calc C_lp * (N + 1) * instSize N G'
            = C_lp * ((N + 1) * instSize N G') := by ring
          _ ≤ C_lp * (4 * M₀) := Nat.mul_le_mul_left _ hM_G'
          _ = 4 * C_lp * M₀ := by ring
      have h2 : C_buf * (N + 1) * instSize N G = C_cln * M₀ + 4 * C_lp * M₀ + M₀ := by
        rw [mul_assoc, hM₀_eq]; dsimp [C_buf]; ring
      have h3 : C_cln * (N + 1) * instSize N G = C_cln * M₀ := by
        rw [mul_assoc, hM₀_eq]
      omega
    obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, K', S'', D', recs₂, k₂,
            hhist₄, hlong₄, hrec₄, hpair₄, hlen₄, _⟩ :=
      hP_loop w N G' S' D recs₁ k₁ s₃ hw_loop hinst₃ hD₂ hclean₂ hnpl₃ hcross_G' hrec₃ hcap_lp
    have hex_loop : Exec w (.ite (.op .eq (.reg (r_base + 1)) (.const 1)) P_loop .skip) s₃ s₄ _ :=
      .ite_true hcond1 (by decide) hex₄
    have hrec₄_len : (s₄.arrs (a_base + 5)).length = cap := by rw [hlen₄, hrec₃_len]
    have hhist_all : IsHistoryFin G Finset.univ D (recs₁ ++ recs₂) K' S'' D' :=
      isHistory_append hhist₂ hhist₄
    have hlong_all : ContractionsLong (recs₁ ++ recs₂) :=
      contractionsLong_append hlong₂ hlong₄
    obtain ⟨L₁, L₂, hcp₄, hQ₄, hR₄⟩ := hpair₄
    have hw_lift : wordSize c_lft ((s₄.arrs (a_base + 5)).length + (N + 1) * (N + 1)) ≤ w := by
      have hle : (s₄.arrs (a_base + 5)).length + (N + 1) * (N + 1) ≤ K_scale * (M₀ + 1) := by
        rw [hrec₄_len, hK_expand]
        omega
      exact (wordSize_le_of_le_mul' hle).trans
        ((wordSize_mono_left (Nat.mul_le_mul_right _ (by dsimp [c_sum]; omega)) M₀).trans hw)
    obtain ⟨s₅, t₅, hex₅, ht₅, hk₅, P', hlift₅, hQ₅, hR₅⟩ :=
      hP_lift w N G K' Finset.univ S'' D D' (recs₁ ++ recs₂) k₂ L₁ L₂ s₄ hw_lift
        hhist_all hlong_all hcp₄ hrec₄ hQ₄ hR₄
        (length_le_of_isDPathList hcp₄.1) (length_le_of_isDPathList hcp₄.2.1)
    have hcp_G : IsCrossingPair G D P'.1 P'.2 :=
      (liftHistory_proved G ((Finset.univ : Finset (Fin N)) : Set (Fin N)) D (recs₁ ++ recs₂)
        K' (S'' : Set (Fin N)) D' L₁ L₂ (Set.toFinite _) hinst₁.1
        hD hhist_all hlong_all hcp₄).2 P' hlift₅
    have hpair₅ : IsCrossingPairAt G D a_Q a_R s₅ := ⟨P'.1, P'.2, hcp_G, hQ₅, hR₅⟩
    have hrN₅ : s₅.regs r_N = N := by
      rw [hk₅.1 r_N (by omega) (by simp), hk₄.1 r_N (by omega) (by simp; omega),
        hlow₃_regs r_N hrN, hN_reg]
    have hcyc₅ : s₅.arrs a_cyc = D.map Fin.val := by
      rw [hk₅.2 a_cyc (by omega) (by simp [hcQ, hcR]),
        hk₄.2 a_cyc (by omega) (by dsimp [topInstArrs, InstArrs.list]; simp [hcQ, hcR]; omega),
        hlow₃_arrs a_cyc hcyc_lt hcQ hcR, hcyc]
    obtain ⟨s₆, t₆, hex₆, ht₆, hk₆, a₀, b₀, c₀, d₀, Q, R, hcross₆, hQ₆, hR₆⟩ :=
      orientCrossingProg_exec (w := w) a_cyc a_Q a_R (a_base + 6) r_N (r_base + 1)
        (arrsOk_cyc_QR hcyc_lt hQ_lt hR_lt hcQ hcR hQR) (by omega)
        hrN₅ hcyc₅ hD hpair₅ h4N_w
    set s₇ := s₆.setReg r_out 1
    have hex₇ : Exec w (.assign r_out (.const 1)) s₆ s₇ 2 := .assign (eval_const hw1)
    have hex_ite : Exec w (.ite (.op .eq (.reg (r_base + 1)) (.const 0)) (.assign r_out (.const 0))
        (.seq (.ite (.op .eq (.reg (r_base + 1)) (.const 1)) P_loop .skip)
          (.seq P_lift (.seq (orientCrossingProg a_cyc a_Q a_R (a_base + 6) r_N (r_base + 1))
            (.assign r_out (.const 1)))))) s₃ s₇ _ :=
      .ite_false hcond0 (.seq hex_loop (.seq hex₅ (.seq hex₆ hex₇)))
    refine ⟨s₇, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex_ite)), ?_, ?_,
      Or.inl ⟨by simp [s₇], a₀, b₀, c₀, d₀, Q, R, hcross₆, hQ₆, hR₆⟩⟩
    · have hr_rec_le : s₄.regs r_base ≤ cap := by
        rw [← hrec₄_len]; exact regs_le_length_of_isRecBufAt hrec₄
      have hN2_le : (N + 1) * (N + 1) ≤ M₀ := Nat.mul_le_mul_left _ (by omega)
      have ht₅_le : t₅ ≤ C_lft * ((2 * C_buf + 1) * M₀) := by
        calc t₅ ≤ C_lft * (s₄.regs r_base + (N + 1) * (N + 1)) := ht₅
          _ ≤ C_lft * (2 * C_buf * M₀ + M₀) := Nat.mul_le_mul_left _ (by omega)
          _ = C_lft * ((2 * C_buf + 1) * M₀) := by ring
      have ht₄_le : t₄ ≤ 4 * C_lp * M₀ := by
        calc t₄ ≤ C_lp * (N + 1) * instSize N G' := ht₄
          _ = C_lp * ((N + 1) * instSize N G') := by ring
          _ ≤ C_lp * (4 * M₀) := Nat.mul_le_mul_left _ hM_G'
          _ = 4 * C_lp * M₀ := by ring
      simp only [Expr.cost]
      have hgoal_eq :
          (4 * C_buf + C_cln + 4 * C_cls + 4 * C_lp + (2 * C_buf + 1) * C_lft + 500) *
            (N + 1) * (E + N + 1) =
          (2 * C_buf + 150) * M₀ + C_cln * M₀ + 4 * C_cls * M₀ + 4 * C_lp * M₀ +
            C_lft * ((2 * C_buf + 1) * M₀) + 2 * C_buf * M₀ + 350 * M₀ := by
        dsimp [M₀]; ring
      rw [hgoal_eq]
      omega
    · refine ⟨fun r hr hro => ?_, fun x hx hxQR => ?_⟩
      · simp only [List.mem_singleton] at hro
        simp only [s₇, State.setReg_regs_ne _ _ (show (r : Reg) ≠ r_out by ne_nat)]
        rw [hk₆.1 r (by omega) (by simp), hk₅.1 r (by omega) (by simp),
          hk₄.1 r (by omega) (by simp; omega), hlow₃_regs r hr]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxQR
        simp only [s₇, State.setReg_arrs]
        rw [hk₆.2 x (by omega) (by simp [hxQR.1, hxQR.2]),
          hk₅.2 x (by omega) (by simp [hxQR.1, hxQR.2]),
          hk₄.2 x (by omega) (by dsimp [topInstArrs, InstArrs.list]; simp [hxQR.1, hxQR.2]; omega),
          hlow₃_arrs x hx hxQR.1 hxQR.2]

/-- Unconditional proof of `InitialCleaningRecFullProgClaim`, plugging in
`replaceRecProgClaim_proved`. -/
theorem initialCleaningRecFullProgClaim_proved : InitialCleaningRecFullProgClaim :=
  initialCleaningRecFullProgClaim_of

/-- **The crossing extractor** (`CrossingExtractorStatement`, Sections 4–12 of
`docs/crossing/crossing_extractor.tex`), proved from planarity testing (`PlanarityTestStatement`),
classification (`ClassifyProgClaim`), and lifting (`LiftRecHistProgClaim`), discharging
`ReplaceRecProgClaim`, `SparsifyRecProgClaim`, `RestoreRecNeProgClaim`, and `LoopRecProgClaim`
via `replaceRecProgClaim_proved`, `sparsifyRecProgClaim_proved`, `restoreRecNeProgClaim_of`,
and `loopRecProgClaim_of`. -/
theorem crossingExtractor_of : CrossingExtractorStatement :=
  crossingExtractor_of_full

end GraphMinor.Compute.Crossing
