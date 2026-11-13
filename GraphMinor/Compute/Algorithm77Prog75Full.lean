module

public import GraphMinor.Compute.Algorithm77Prog75Case

/-!
# Full Word RAM Implementation of Step (7.5) and Input Packing for GM XIII (7.7)

This file completes the Word RAM implementation of Graph Minors XIII, (7.5) (`Algorithm77Step75.lean`):
1. **Section 1:** `step75StepSliceCmd` (scanning `Qs` for Case A and falling back to `caseBCmd` in
   Case B, matching `WallOfHeight.step75Step`) and `step75RecCmd` (the `k`-step induction matching
   `WallOfHeight.step75Rec`).
2. **Section 2:** `packAlg74InCmd` (packing `encAlg74In (runStep75 hp hr x)` into `inArr`) and
   `runStep75Cmd` (sequencing `runStep76Cmd`, `initAllStarsActiveSliceCmd`, `step75RecCmd`, and
   `packAlg74InCmd`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

set_option linter.deprecated false

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges

/-! ### Section 1: `step75StepSliceCmd` and `step75RecCmd` -/

theorem find?_eq_some_of_lt_of_ge {α : Type*} :
    ∀ (L : List α) (p : α → Bool) {j : ℕ} (hj : j < L.length)
      (_hprev : ∀ m (hm : m < j), p (L[m]'(by omega)) = false)
      (_hj_true : p (L[j]'hj) = true),
      L.find? p = some (L[j]'hj)
  | [], _, _, hj, _, _ => False.elim (Nat.not_lt_zero _ hj)
  | x :: xs, p, 0, _, _, hj_true => by
    simp only [List.getElem_cons_zero] at hj_true ⊢
    simp [List.find?, hj_true]
  | x :: xs, p, j + 1, hj, hprev, hj_true => by
    have hx : p x = false := by
      simpa using hprev 0 (Nat.zero_lt_succ j)
    have hj_xs : j < xs.length := by simpa using hj
    have hprev_xs : ∀ m (hm : m < j), p (xs[m]'(by omega)) = false := by
      intro m hm
      simpa using hprev (m + 1) (Nat.succ_lt_succ hm)
    have hj_true_xs : p (xs[j]'hj_xs) = true := by
      simpa using hj_true
    simp only [List.find?, hx, List.getElem_cons_succ]
    exact find?_eq_some_of_lt_of_ge xs p hj_xs hprev_xs hj_true_xs

/-- Time bound for one call to `computeHitsOnQCmd` plus branch overhead in `step75StepSliceCmd`. -/
def step75HitScanTime (l n : ℕ) : ℕ :=
  l * (65 * n + 36) + n * (28 * l + 48) + 30

/-- Combined Case A + Case B tail time bound in `step75StepSliceCmd`. -/
def step75TailTime (l sIdx n : ℕ) : ℕ :=
  (sIdx + 1) * (2 * l * (22 * n + 16) + 240 * n + 155) +
  ((79 * n + 242500) * sIdx + 30) * l +
  2 * (l * (22 * n + 16)) + 84 * n + 45

/-- Check `Qs[j], ..., Qs[j + rem - 1]` for `2 * (sIdx + 1) ≤ (hitsOnQ rs Qs[j]).length`:
if found, execute `buildCaseAPathsCmd l (sIdx + 1) (qPathArr j)` (Case A); if none is found
(`rem = 0`), execute `caseBCmd r l a sIdx` (Case B). -/
def step75StepSliceCmd (r l a sIdx j : ℕ) : ℕ → Cmd
  | 0 => caseBCmd r l a sIdx
  | rem + 1 =>
    .seq (computeHitsOnQCmd l a (qPathArr j))
      (.ite (exprLe (.const (2 * (sIdx + 1))) (.reg 20))
        (buildCaseAPathsCmd l (sIdx + 1) (qPathArr j))
        (step75StepSliceCmd r l a sIdx (j + 1) rem))

theorem step75StepSliceCmd_exec {w h n l a sIdx r : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {c : Fin n} (Qs : List (List (Fin n)))
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (hrs : W.IsStarRayList (2 * r) c (activeRayList rays act))
    (hQs : W.IsFarHPathList r Qs) (hQs_len : Qs.length = sIdx)
    (hcQs : ∀ Q ∈ Qs, c ∉ Q)
    (hl : 2 * (sIdx + 1) ^ 2 - (sIdx + 1) + 3 ≤ (activeRayList rays act).length)
    (hP_valid : ∀ i : Fin l, W.IsStarRay c (rays i))
    (hneP : ∀ i : Fin l, rays i ≠ [])
    (hP_len : ∀ i : Fin l, (rays i).length ≤ n)
    (hw2 : 2 < 2 ^ w) (h3n_w : 3 * n < 2 ^ w) (hl_w : l < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w) (h2r_w : 2 * r < 2 ^ w)
    (h2s2_w : 2 * (sIdx + 1) < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w) :
    ∀ (rem j : ℕ) (_hrem : j + rem = sIdx) {s : State}
      (_hs : WallStateHolds W s)
      (_hqArr : ∀ m (hm : m < Qs.length), s.arrs (qPathArr m) = (Qs[m]'hm).map Fin.val)
      (_hpArr : ∀ i : Fin l, s.arrs (starRayArr l a i.1) = (rays i).map Fin.val)
      (_hact : ∀ i : Fin l, s.regs (regRayActive l a i.1) = if act i then 1 else 0)
      (_hprev : ∀ m (hm : m < j),
        (WallOfHeight.hitsOnQ (activeRayList rays act) (Qs[m]'(by omega))).length < 2 * (sIdx + 1)),
      let Qs' := W.step75Step r sIdx Qs (activeRayList rays act)
      have hlen_Qs' : Qs'.length = sIdx + 1 :=
        (W.step75Step_spec h2 he hW hrs hQs hQs_len hcQs hl).1
      ∃ s' time,
        Exec w (step75StepSliceCmd r l a sIdx j rem) s s' time ∧
        time ≤ rem * step75HitScanTime l n + step75TailTime l sIdx n ∧
        WallStateHolds W s' ∧
        (∀ m (hm : m < sIdx + 1),
          s'.arrs (qPathArr m) = (Qs'[m]'(by rw [hlen_Qs']; exact hm)).map Fin.val) ∧
        s'.regs 1 = s.regs 1 ∧
        s'.regs 2 = s.regs 2 ∧
        (∀ b : ℕ, s'.regs (regCenter b) = s.regs (regCenter b)) ∧
        (∀ b : ℕ, ∀ i < l, s'.regs (regRayActive l b i) = s.regs (regRayActive l b i)) ∧
        s'.arrs inArr = s.arrs inArr ∧
        (∀ b i, s'.arrs (starRayArr l b i) = s.arrs (starRayArr l b i))
  | 0, j, hrem, s, hs, hqArr, hpArr, hact, hprev => by
    have hj_eq : j = sIdx := by omega
    subst hj_eq
    have hhits_all : ∀ Q ∈ Qs,
        (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length < 2 * (j + 1) := by
      intro Q hQ
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hQ
      exact hprev m (by omega)
    have hfind_none :
        Qs.find? (fun Q => decide (2 * (j + 1) ≤
          (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length)) = none := by
      rw [List.find?_eq_none]
      intro Q hQ
      simpa [decide_eq_true_eq] using hhits_all Q hQ
    have hstep_eq : W.step75Step r j Qs (activeRayList rays act) =
        let good := (activeRayList rays act).filter (W.isGoodRay r Qs)
        Qs ++ [WallOfHeight.joinTwoRays (good.headD []) ((good.drop 1).headD [])] := by
      simp [WallOfHeight.step75Step, hfind_none]
    have hgood_ge : 2 ≤ ((activeRayList rays act).filter (W.isGoodRay r Qs)).length :=
      W.two_le_length_filter_isGoodRay h2 he hW hrs hQs hQs_len hcQs hhits_all hl
    rcases caseBCmd_exec W h2 he hW Qs rays act hQs_len hQs.paths_valid hP_valid hgood_ge
        hw2 (by omega) (by omega) hl_w h4h4_w hloc_w
        hs hqArr hpArr hact with
      ⟨s', t, hex, ht, hs', hqArr', hregs', harrs'⟩
    refine ⟨s', t, hex,
      by unfold step75TailTime; omega,
      hs',
      fun m hm => by simpa [hstep_eq] using hqArr' m (by simp [hQs_len, hm]),
      hregs' 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun _ _ => ⟨by dsimp [regRayHitVert, Reg]; omega, by dsimp [regRayMeets, Reg]; omega⟩),
      hregs' 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun _ _ => ⟨by dsimp [regRayHitVert, Reg]; omega, by dsimp [regRayMeets, Reg]; omega⟩),
      fun b => hregs' (regCenter b)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (fun _ _ => ⟨by dsimp [regCenter, regRayHitVert, Reg]; omega,
          by dsimp [regCenter, regRayMeets, Reg]; omega⟩),
      fun b i _ => hregs' (regRayActive l b i)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (fun _ _ => ⟨by dsimp [regRayActive, regRayHitVert, Reg]; omega,
          by dsimp [regRayActive, regRayMeets, Reg]; omega⟩),
      harrs' inArr (by decide) (by decide) (by decide) (by decide)
        (by dsimp [inArr, qPathArr, Arr]; omega)
        (fun _ _ => by dsimp [inArr, hitPrefArr, Arr]; omega),
      fun b i => harrs' (starRayArr l b i)
        (by dsimp [starRayArr, qMemArr, Arr]; omega)
        (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
        (by dsimp [starRayArr, tmpPathArr2, Arr]; omega)
        (by dsimp [starRayArr, tmpPathArr3, Arr]; omega)
        (by dsimp [starRayArr, qPathArr, Arr]; omega)
        (fun _ _ => by dsimp [starRayArr, hitPrefArr, Arr]; omega)⟩
  | rem + 1, j, hrem, s, hs, hqArr, hpArr, hact, hprev => by
    have h1_w : 1 < 2 ^ w := by omega
    have hn_w : n < 2 ^ w := by omega
    have hj_lt : j < Qs.length := by omega
    let Q := Qs[j]'hj_lt
    have hQ_mem : Q ∈ Qs := List.getElem_mem hj_lt
    have hQ_valid : W.IsHPath Q := hQs.paths_valid Q hQ_mem
    have hQ_len : Q.length ≤ n := length_le_of_nodup_fin hQ_valid.choose_spec.2.1
    rcases computeHitsOnQCmd_exec (qPathArr j)
        (by dsimp [qPathArr, qMemArr, Arr]; omega)
        (by dsimp [qPathArr, tmpPathArr1, Arr]; omega)
        (fun m _ => by dsimp [qPathArr, hitPrefArr, Arr]; omega)
        (by dsimp [qPathArr, hitIdxArr, Arr]; omega)
        (by dsimp [qPathArr, hitRayIdxArr, Arr]; omega)
        Q rays act hneP hP_len hQ_len h1_w hn_w hl_w
        hs.hr0 (hqArr j hj_lt) hpArr hact with
      ⟨s₁, t₁, hex₁, ht₁, hr20_1, hbuf1_1, hbuf2_1, hpref₁, hregs₁, harrs₁⟩
    have hs₁ : WallStateHolds W s₁ :=
      hs.of_preserve
        (hregs₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [regRayHitVert, Reg]; omega)
          (fun _ _ => by dsimp [regRayMeets, Reg]; omega))
        (hregs₁ 3 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [regRayHitVert, Reg]; omega)
          (fun _ _ => by dsimp [regRayMeets, Reg]; omega))
        (hregs₁ 12 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [regRayHitVert, Reg]; omega)
          (fun _ _ => by dsimp [regRayMeets, Reg]; omega))
        (hregs₁ 13 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [regRayHitVert, Reg]; omega)
          (fun _ _ => by dsimp [regRayMeets, Reg]; omega))
        (hregs₁ 14 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [regRayHitVert, Reg]; omega)
          (fun _ _ => by dsimp [regRayMeets, Reg]; omega))
        (harrs₁ wallEncArr (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [wallEncArr, hitPrefArr, Arr]; omega))
        (harrs₁ locArr (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [locArr, hitPrefArr, Arr]; omega))
        (harrs₁ wallMemArr (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [wallMemArr, hitPrefArr, Arr]; omega))
        (harrs₁ edgeOffArr (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [edgeOffArr, hitPrefArr, Arr]; omega))
        (harrs₁ edgeLenArr (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [edgeLenArr, hitPrefArr, Arr]; omega))
        (harrs₁ edgeU1Arr (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [edgeU1Arr, hitPrefArr, Arr]; omega))
        (harrs₁ edgeU2Arr (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [edgeU2Arr, hitPrefArr, Arr]; omega))
        (harrs₁ horizEdgeIdxArr (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [horizEdgeIdxArr, hitPrefArr, Arr]; omega))
        (harrs₁ vertEdgeIdxArr (by decide) (by decide) (by decide) (by decide)
          (fun _ _ => by dsimp [vertEdgeIdxArr, hitPrefArr, Arr]; omega))
    have hqArr₁ : ∀ m (hm : m < Qs.length), s₁.arrs (qPathArr m) = (Qs[m]'hm).map Fin.val := by
      intro m hm
      rw [harrs₁ (qPathArr m)
        (by dsimp [qPathArr, qMemArr, Arr]; omega)
        (by dsimp [qPathArr, tmpPathArr1, Arr]; omega)
        (by dsimp [qPathArr, hitIdxArr, Arr]; omega)
        (by dsimp [qPathArr, hitRayIdxArr, Arr]; omega)
        (fun _ _ => by dsimp [qPathArr, hitPrefArr, Arr]; omega)]
      exact hqArr m hm
    have hhits_len_le :
        (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length ≤ Q.length := by
      have h2 := hbuf1_1.2.2.1
      rw [hitsOnQ_activeRayList]
      simp only [List.length_map] at h2 ⊢
      exact h2
    have hr20_w : (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length < 2 ^ w := by omega
    have heval_c : (Expr.const (2 * (sIdx + 1))).eval w s₁ = some (2 * (sIdx + 1)) :=
      eval_const s₁ h2s2_w
    have heval_20 : (Expr.reg 20).eval w s₁ =
        some (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length := by
      simp [Expr.eval, checkWord, hr20_1, hr20_w]
    have heval_cond : (exprLe (.const (2 * (sIdx + 1))) (.reg 20)).eval w s₁ =
        some (if 2 * (sIdx + 1) ≤
          (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length then 1 else 0) :=
      eval_exprLe h1_w heval_c heval_20
    by_cases hcaseA : 2 * (sIdx + 1) ≤ (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length
    · rw [if_pos hcaseA] at heval_cond
      have hfind_some :
          Qs.find? (fun Q' => decide (2 * (sIdx + 1) ≤
            (WallOfHeight.hitsOnQ (activeRayList rays act) Q').length)) = some Q := by
        apply find?_eq_some_of_lt_of_ge Qs
          (fun Q' => decide (2 * (sIdx + 1) ≤
            (WallOfHeight.hitsOnQ (activeRayList rays act) Q').length)) hj_lt
        · intro m hm
          simpa [decide_eq_true_eq] using hprev m hm
        · simpa [decide_eq_true_eq] using hcaseA
      have hstep_eq : W.step75Step r sIdx Qs (activeRayList rays act) =
          WallOfHeight.buildCaseAPaths (sIdx + 1) (activeRayList rays act) Q := by
        simp [WallOfHeight.step75Step, hfind_some]
      rcases buildCaseAPathsCmd_exec W h2 he hW (qPathArr j)
          (by dsimp [qPathArr, tmpPathArr1, Arr]; omega)
          (by dsimp [qPathArr, tmpPathArr2, Arr]; omega)
          (by dsimp [qPathArr, tmpPathArr3, Arr]; omega)
          (by dsimp [qPathArr, bufArr, Arr]; omega)
          (fun t _ => by dsimp [qPathArr, rPathArr, Arr]; omega)
          Q rays act hrs hQ_valid (hcQs Q hQ_mem) hneP hP_len hcaseA
          h1_w h3n_w hl_w (hqArr₁ j hj_lt) hbuf1_1 hbuf2_1 hpref₁ with
        ⟨s₂, t₂, hex₂, ht₂, hq₂, hregs₂, harrs₂⟩
      have hs₂ : WallStateHolds W s₂ :=
        hs₁.of_preserve
          (hregs₂ 0 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide))
          (hregs₂ 3 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide))
          (hregs₂ 12 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide))
          (hregs₂ 13 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide))
          (hregs₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide))
          (harrs₂ wallEncArr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [wallEncArr, rPathArr, Arr]; omega)
            (fun _ _ => by dsimp [wallEncArr, qPathArr, Arr]; omega))
          (harrs₂ locArr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [locArr, rPathArr, Arr]; omega)
            (fun _ _ => by dsimp [locArr, qPathArr, Arr]; omega))
          (harrs₂ wallMemArr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [wallMemArr, rPathArr, Arr]; omega)
            (fun _ _ => by dsimp [wallMemArr, qPathArr, Arr]; omega))
          (harrs₂ edgeOffArr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [edgeOffArr, rPathArr, Arr]; omega)
            (fun _ _ => by dsimp [edgeOffArr, qPathArr, Arr]; omega))
          (harrs₂ edgeLenArr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [edgeLenArr, rPathArr, Arr]; omega)
            (fun _ _ => by dsimp [edgeLenArr, qPathArr, Arr]; omega))
          (harrs₂ edgeU1Arr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [edgeU1Arr, rPathArr, Arr]; omega)
            (fun _ _ => by dsimp [edgeU1Arr, qPathArr, Arr]; omega))
          (harrs₂ edgeU2Arr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [edgeU2Arr, rPathArr, Arr]; omega)
            (fun _ _ => by dsimp [edgeU2Arr, qPathArr, Arr]; omega))
          (harrs₂ horizEdgeIdxArr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [horizEdgeIdxArr, rPathArr, Arr]; omega)
            (fun _ _ => by dsimp [horizEdgeIdxArr, qPathArr, Arr]; omega))
          (harrs₂ vertEdgeIdxArr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [vertEdgeIdxArr, rPathArr, Arr]; omega)
            (fun _ _ => by dsimp [vertEdgeIdxArr, qPathArr, Arr]; omega))
      have ht_step : t₁ + ((exprLe (.const (2 * (sIdx + 1))) (.reg 20)).cost + t₂) ≤
          (rem + 1) * step75HitScanTime l n + step75TailTime l sIdx n := by
        have hcost : (exprLe (.const (2 * (sIdx + 1))) (.reg 20)).cost = 3 := rfl
        have h1 : t₁ + 3 ≤ step75HitScanTime l n := by
          unfold step75HitScanTime; omega
        have h2 : step75HitScanTime l n ≤ (rem + 1) * step75HitScanTime l n :=
          Nat.le_mul_of_pos_left _ (Nat.succ_pos rem)
        have h3 : t₂ ≤ step75TailTime l sIdx n := by
          unfold step75TailTime; omega
        omega
      refine ⟨s₂, _, .seq hex₁ (.ite_true heval_cond (by omega) hex₂),
        ht_step, hs₂,
        fun m hm => by simpa [hstep_eq] using hq₂ m hm,
        by rw [hregs₂ 1 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide),
            hregs₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [regRayHitVert, Reg]; omega)
            (fun _ _ => by dsimp [regRayMeets, Reg]; omega)],
        by rw [hregs₂ 2 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide),
            hregs₁ 2 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [regRayHitVert, Reg]; omega)
            (fun _ _ => by dsimp [regRayMeets, Reg]; omega)],
        fun b => by
          rw [hregs₂ (regCenter b)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega),
            hregs₁ (regCenter b)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (fun _ _ => by dsimp [regCenter, regRayHitVert, Reg]; omega)
            (fun _ _ => by dsimp [regCenter, regRayMeets, Reg]; omega)],
        fun b i _ => by
          rw [hregs₂ (regRayActive l b i)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega),
            hregs₁ (regRayActive l b i)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (fun _ _ => by dsimp [regRayActive, regRayHitVert, Reg]; omega)
            (fun _ _ => by dsimp [regRayActive, regRayMeets, Reg]; omega)],
        by rw [harrs₂ inArr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [inArr, rPathArr, Arr]; omega)
            (fun _ _ => by dsimp [inArr, qPathArr, Arr]; omega),
            harrs₁ inArr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [inArr, hitPrefArr, Arr]; omega)],
        fun b i => by
          rw [harrs₂ (starRayArr l b i)
            (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
            (by dsimp [starRayArr, tmpPathArr2, Arr]; omega)
            (by dsimp [starRayArr, tmpPathArr3, Arr]; omega)
            (by dsimp [starRayArr, bufArr, Arr]; omega)
            (fun _ _ => by dsimp [starRayArr, rPathArr, Arr]; omega)
            (fun _ _ => by dsimp [starRayArr, qPathArr, Arr]; omega),
            harrs₁ (starRayArr l b i)
            (by dsimp [starRayArr, qMemArr, Arr]; omega)
            (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
            (by dsimp [starRayArr, hitIdxArr, Arr]; omega)
            (by dsimp [starRayArr, hitRayIdxArr, Arr]; omega)
            (fun _ _ => by dsimp [starRayArr, hitPrefArr, Arr]; omega)]⟩
    · rw [if_neg hcaseA] at heval_cond
      have hpArr₁ : ∀ i : Fin l, s₁.arrs (starRayArr l a i.1) = (rays i).map Fin.val := by
        intro i
        rw [harrs₁ (starRayArr l a i.1)
          (by dsimp [starRayArr, qMemArr, Arr]; omega)
          (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
          (by dsimp [starRayArr, hitIdxArr, Arr]; omega)
          (by dsimp [starRayArr, hitRayIdxArr, Arr]; omega)
          (fun _ _ => by dsimp [starRayArr, hitPrefArr, Arr]; omega)]
        exact hpArr i
      have hact₁ : ∀ i : Fin l, s₁.regs (regRayActive l a i.1) = if act i then 1 else 0 := by
        intro i
        rw [hregs₁ (regRayActive l a i.1)
          (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
          (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
          (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
          (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
          (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
          (fun _ _ => by dsimp [regRayActive, regRayHitVert, Reg]; omega)
          (fun _ _ => by dsimp [regRayActive, regRayMeets, Reg]; omega)]
        exact hact i
      have hprev₁ : ∀ m (hm : m < j + 1),
          (WallOfHeight.hitsOnQ (activeRayList rays act) (Qs[m]'(by omega))).length <
            2 * (sIdx + 1) := by
        intro m hm
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with hlt | rfl
        · exact hprev m hlt
        · exact Nat.lt_of_not_ge hcaseA
      rcases step75StepSliceCmd_exec W h2 he hW Qs rays act hrs hQs hQs_len hcQs hl
          hP_valid hneP hP_len hw2 h3n_w hl_w h4h4_w h2r_w h2s2_w hVJW_w hloc_w henc_w
          rem (j + 1) (by omega) hs₁ hqArr₁ hpArr₁ hact₁ hprev₁ with
        ⟨s₂, t₂, hex₂, ht₂, hs₂, hq₂, hr1_2, hr2_2, hcent₂, hact₂, hin₂, hstar₂⟩
      have ht_step : t₁ + ((exprLe (.const (2 * (sIdx + 1))) (.reg 20)).cost + t₂) ≤
          (rem + 1) * step75HitScanTime l n + step75TailTime l sIdx n := by
        have hcost : (exprLe (.const (2 * (sIdx + 1))) (.reg 20)).cost = 3 := rfl
        have h1 : t₁ + 3 ≤ step75HitScanTime l n := by
          unfold step75HitScanTime; omega
        have hmul : (rem + 1) * step75HitScanTime l n =
            step75HitScanTime l n + rem * step75HitScanTime l n := by ring
        omega
      refine ⟨s₂, _, .seq hex₁ (.ite_false heval_cond hex₂),
        ht_step, hs₂, hq₂,
        by rw [hr1_2, hregs₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [regRayHitVert, Reg]; omega)
            (fun _ _ => by dsimp [regRayMeets, Reg]; omega)],
        by rw [hr2_2, hregs₁ 2 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [regRayHitVert, Reg]; omega)
            (fun _ _ => by dsimp [regRayMeets, Reg]; omega)],
        fun b => by
          rw [hcent₂ b, hregs₁ (regCenter b)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (fun _ _ => by dsimp [regCenter, regRayHitVert, Reg]; omega)
            (fun _ _ => by dsimp [regCenter, regRayMeets, Reg]; omega)],
        fun b i hi => by
          rw [hact₂ b i hi, hregs₁ (regRayActive l b i)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (fun _ _ => by dsimp [regRayActive, regRayHitVert, Reg]; omega)
            (fun _ _ => by dsimp [regRayActive, regRayMeets, Reg]; omega)],
        by rw [hin₂, harrs₁ inArr (by decide) (by decide) (by decide) (by decide)
            (fun _ _ => by dsimp [inArr, hitPrefArr, Arr]; omega)],
        fun b i => by
          rw [hstar₂ b i, harrs₁ (starRayArr l b i)
            (by dsimp [starRayArr, qMemArr, Arr]; omega)
            (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
            (by dsimp [starRayArr, hitIdxArr, Arr]; omega)
            (by dsimp [starRayArr, hitRayIdxArr, Arr]; omega)
            (fun _ _ => by dsimp [starRayArr, hitPrefArr, Arr]; omega)]⟩

/-- Time bound for one recursive level of `step75RecCmd` at depth ` ≤ K`. -/
def step75OneStepBound (l K n : ℕ) : ℕ :=
  K * (l * (23 * n + 25) + 1) + 1 +
  K * step75HitScanTime l n + step75TailTime l K n

theorem step75OneStepBound_mono {l k K n : ℕ} (hk : k ≤ K) :
    k * (l * (23 * n + 25) + 1) + 1 +
      k * step75HitScanTime l n + step75TailTime l k n ≤
    step75OneStepBound l K n := by
  unfold step75OneStepBound step75TailTime
  have h1 : k * (l * (23 * n + 25) + 1) ≤ K * (l * (23 * n + 25) + 1) :=
    Nat.mul_le_mul_right _ hk
  have h2 : k * step75HitScanTime l n ≤ K * step75HitScanTime l n :=
    Nat.mul_le_mul_right _ hk
  have h3 : (k + 1) * (2 * l * (22 * n + 16) + 240 * n + 155) ≤
      (K + 1) * (2 * l * (22 * n + 16) + 240 * n + 155) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : ((79 * n + 242500) * k + 30) * l ≤
      ((79 * n + 242500) * K + 30) * l :=
    Nat.mul_le_mul_right l (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) 30)
  omega

/-- Recursive Word RAM command for the induction in GM XIII (7.5), matching `W.step75Rec`. -/
def step75RecCmd (r l : ℕ) : ℕ → Cmd
  | 0 => .skip
  | k + 1 =>
    .seq (filterAllStarsAvoidSliceCmd l (regCenter k) 0 k)
      (.seq (step75RecCmd r l k)
        (step75StepSliceCmd r l k k 0 k))

theorem step75RecCmd_exec {w h n l r K : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hw2 : 2 < 2 ^ w) (h3n_w : 3 * n < 2 ^ w) (hl_w : l < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w) (h2r_w : 2 * r < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w) :
    ∀ (k : ℕ) (_hk_le : k ≤ K) (_h2k_w : 2 * k < 2 ^ w)
      (rays : Fin k → Fin l → List (Fin n))
      (act : Fin k → Fin l → Bool)
      (v : Fin k → Fin n)
      (_hS : ∀ a : Fin k, W.IsStarRayList (2 * r) (v a) (activeRayList (rays a) (act a)))
      (_hl : ∀ a : Fin k, 2 * k ^ 2 - k + 3 ≤ (activeRayList (rays a) (act a)).length)
      (_hv : Function.Injective v)
      (_hP_valid : ∀ a : Fin k, ∀ j : Fin l, W.IsStarRay (v a) (rays a j))
      (_hneP : ∀ a : Fin k, ∀ j : Fin l, rays a j ≠ [])
      (_hP_len : ∀ a : Fin k, ∀ j : Fin l, (rays a j).length ≤ n)
      {s : State}
      (_hs : WallStateHolds W s)
      (_hcenters : ∀ a : Fin k, s.regs (regCenter a.1) = (v a).1)
      (_hsrc : ∀ a : Fin k, ∀ j : Fin l, s.arrs (starRayArr l a.1 j.1) = (rays a j).map Fin.val)
      (_hact : ∀ a : Fin k, ∀ j : Fin l, s.regs (regRayActive l a.1 j.1) = if act a j then 1 else 0),
      let S : Fin k → List (List (Fin n)) := fun a => activeRayList (rays a) (act a)
      let Qs := W.step75Rec r k S v
      have hlenQs : Qs.length = k :=
        (W.step75Rec_spec h2 he hW r k S v _hS _hl _hv).1
      ∃ s' time,
        Exec w (step75RecCmd r l k) s s' time ∧
        time ≤ k * step75OneStepBound l K n + 1 ∧
        WallStateHolds W s' ∧
        (∀ m (hm : m < k),
          s'.arrs (qPathArr m) = (Qs[m]'(by rw [hlenQs]; exact hm)).map Fin.val) ∧
        s'.regs 1 = s.regs 1 ∧
        s'.regs 2 = s.regs 2 ∧
        (∀ b : ℕ, s'.regs (regCenter b) = s.regs (regCenter b)) ∧
        (∀ b ≥ k, ∀ j < l, s'.regs (regRayActive l b j) = s.regs (regRayActive l b j)) ∧
        s'.arrs inArr = s.arrs inArr ∧
        (∀ b j, s'.arrs (starRayArr l b j) = s.arrs (starRayArr l b j))
  | 0, _, _, _, _, _, _, _, _, _, _, _, s, hs, _, _, _ => by
    refine ⟨s, 1, .skip s, by omega, hs,
      fun _ hm => False.elim (Nat.not_lt_zero _ hm),
      rfl, rfl, fun _ => rfl, fun _ _ _ _ => rfl, rfl, fun _ _ => rfl⟩
  | k + 1, hk_le, h2k_w, rays, act, v, hS, hl, hv, hP_valid, hneP, hP_len,
      s, hs, hcenters, hsrc, hact => by
    have h1_w : 1 < 2 ^ w := by omega
    have hn_w : n < 2 ^ w := by omega
    let w_last := v (Fin.last k)
    let rays' : Fin k → Fin l → List (Fin n) := fun a => rays a.castSucc
    let act₀ : Fin k → Fin l → Bool := fun a => act a.castSucc
    let act' : Fin k → Fin l → Bool :=
      fun a j => act a.castSucc j && decide (w_last ∉ rays a.castSucc j)
    let v' : Fin k → Fin n := fun a => v a.castSucc
    -- Step 1: filterAllStarsAvoidSliceCmd l (regCenter k) 0 k
    rcases filterAllStarsAvoidSliceCmd_exec (k := k) (l := l) (regCenter k)
        (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega)
        (fun a _ j _ => by dsimp [regCenter, regRayActive, Reg]; omega)
        w_last rays' act₀ h1_w hn_w (fun a j => hP_len a.castSucc j)
        k 0 (Nat.zero_add k) (s := s)
        (fun a j => hsrc a.castSucc j)
        (hcenters (Fin.last k))
        (fun _ ha => False.elim (Nat.not_lt_zero _ ha))
        (fun a _ j => hact a.castSucc j) with
      ⟨s₁, t₁, hex₁, ht₁, hact₁, hregs₁, harrs₁⟩
    have hs₁ : WallStateHolds W s₁ :=
      hs.of_preserve
        (hregs₁ 0 (by decide) (by decide) (by decide)
          (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega))
        (hregs₁ 3 (by decide) (by decide) (by decide)
          (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega))
        (hregs₁ 12 (by decide) (by decide) (by decide)
          (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega))
        (hregs₁ 13 (by decide) (by decide) (by decide)
          (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega))
        (hregs₁ 14 (by decide) (by decide) (by decide)
          (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega))
        (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁])
        (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁])
    have hS'_eq : ∀ a : Fin k,
        activeRayList (rays' a) (act' a) =
          WallOfHeight.filterAvoidVertex w_last (activeRayList (rays a.castSucc) (act a.castSucc)) := by
      intro a
      exact (filterAvoidVertex_activeRayList w_last (rays a.castSucc) (act a.castSucc)).symm
    have hS' : ∀ a : Fin k, W.IsStarRayList (2 * r) (v' a) (activeRayList (rays' a) (act' a)) := by
      intro a
      rw [hS'_eq a]
      exact (hS a.castSucc).filterAvoidVertex w_last
    have hwc : ∀ a : Fin k, w_last ≠ v' a := fun a h =>
      (Fin.castSucc_lt_last a).ne (hv h).symm
    have hk1 : k + 1 ≤ 2 * (k + 1) ^ 2 := by nlinarith
    have hk0 : k ≤ 2 * k ^ 2 := by nlinarith
    have hl_step : 2 * k ^ 2 - k + 3 + 1 ≤ 2 * (k + 1) ^ 2 - (k + 1) + 3 := by
      zify [hk1, hk0]; nlinarith
    have hl' : ∀ a : Fin k, 2 * k ^ 2 - k + 3 ≤ (activeRayList (rays' a) (act' a)).length := by
      intro a
      rw [hS'_eq a]
      have hge := (hS a.castSucc).length_filterAvoidVertex_ge (hwc a)
      have hla := hl a.castSucc
      omega
    have hv' : Function.Injective v' := hv.comp (Fin.castSucc_injective k)
    have hcenters₁ : ∀ a : Fin k, s₁.regs (regCenter a.1) = (v' a).1 := by
      intro a
      rw [hregs₁ (regCenter a.1)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega)
        (fun _ _ _ _ => by dsimp [regCenter, regRayActive, Reg]; omega)]
      exact hcenters a.castSucc
    have hsrc₁ : ∀ a : Fin k, ∀ j : Fin l,
        s₁.arrs (starRayArr l a.1 j.1) = (rays' a j).map Fin.val := by
      intro a j; rw [harrs₁]; exact hsrc a.castSucc j
    -- Step 2: step75RecCmd r l k
    rcases step75RecCmd_exec (K := K) W h2 he hW hw2 h3n_w hl_w h4h4_w h2r_w hVJW_w hloc_w henc_w
        k (by omega) (by omega) rays' act' v' hS' hl' hv'
        (fun a j => hP_valid a.castSucc j)
        (fun a j => hneP a.castSucc j) (fun a j => hP_len a.castSucc j)
        hs₁ hcenters₁ hsrc₁ hact₁ with
      ⟨s₂, t₂, hex₂, ht₂, hs₂, hq₂, hr1_2, hr2_2, hcent₂, hact₂_ge, hin₂, hstar₂⟩
    let S' : Fin k → List (List (Fin n)) :=
      fun a => WallOfHeight.filterAvoidVertex w_last (activeRayList (rays a.castSucc) (act a.castSucc))
    have hS'_fun : (fun a : Fin k => activeRayList (rays' a) (act' a)) = S' := by
      funext a; exact hS'_eq a
    let Qs := W.step75Rec r k S' v'
    have hS'_valid : ∀ a : Fin k, W.IsStarRayList (2 * r) (v' a) (S' a) := by
      intro a; dsimp [S']; rw [← hS'_eq a]; exact hS' a
    have hl'_valid : ∀ a : Fin k, 2 * k ^ 2 - k + 3 ≤ (S' a).length := by
      intro a; dsimp [S']; rw [← hS'_eq a]; exact hl' a
    obtain ⟨hlenQs, hfarQs, hmemQs⟩ :=
      W.step75Rec_spec h2 he hW r k S' v' hS'_valid hl'_valid hv'
    have hq₂' : ∀ m (hm : m < Qs.length), s₂.arrs (qPathArr m) = (Qs[m]'hm).map Fin.val := by
      intro m hm
      have hm' : m < k := by dsimp [Qs] at hm; omega
      simpa [Qs, hS'_fun] using hq₂ m hm'
    have hw_not_Qs : ∀ Q ∈ Qs, w_last ∉ Q := by
      intro Q hQ hwQ
      rcases hmemQs Q hQ w_last hwQ with ⟨a, P, hP, hwP⟩
      exact (WallOfHeight.mem_filterAvoidVertex_iff.mp hP).2 hwP
    have hpArr₂ : ∀ j : Fin l,
        s₂.arrs (starRayArr l k j.1) = (rays (Fin.last k) j).map Fin.val := by
      intro j
      rw [hstar₂ k j.1, harrs₁]
      exact hsrc (Fin.last k) j
    have hact₂_k : ∀ j : Fin l,
        s₂.regs (regRayActive l k j.1) = if act (Fin.last k) j then 1 else 0 := by
      intro j
      rw [hact₂_ge k (le_refl k) j.1 j.2,
        hregs₁ (regRayActive l k j.1)
          (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
          (by dsimp [regRayActive, Reg]; omega)
          (fun a' ha' j' hj' hcol => by
            have := (regRayActive_inj j.2 hj' hcol).1
            omega)]
      exact hact (Fin.last k) j
    -- Step 3: step75StepSliceCmd r l k k 0 k
    rcases step75StepSliceCmd_exec W h2 he hW Qs (rays (Fin.last k)) (act (Fin.last k))
        (hS (Fin.last k)) hfarQs hlenQs hw_not_Qs (hl (Fin.last k))
        (hP_valid (Fin.last k)) (hneP (Fin.last k)) (hP_len (Fin.last k))
        hw2 h3n_w hl_w h4h4_w h2r_w h2k_w hVJW_w hloc_w henc_w
        k 0 (Nat.zero_add k) hs₂ hq₂' hpArr₂ hact₂_k
        (fun _ hm => False.elim (Nat.not_lt_zero _ hm)) with
      ⟨s₃, t₃, hex₃, ht₃, hs₃, hq₃, hr1_3, hr2_3, hcent₃, hact₃, hin₃, hstar₃⟩
    have ht_all : t₁ + (t₂ + t₃) ≤ (k + 1) * step75OneStepBound l K n + 1 := by
      have hmono := step75OneStepBound_mono (l := l) (n := n) (Nat.le_of_succ_le hk_le)
      have hmul : (k + 1) * step75OneStepBound l K n =
          step75OneStepBound l K n + k * step75OneStepBound l K n := by ring
      omega
    refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃),
      ht_all, hs₃, hq₃,
      by rw [hr1_3, hr1_2, hregs₁ 1 (by decide) (by decide) (by decide)
          (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega)],
      by rw [hr2_3, hr2_2, hregs₁ 2 (by decide) (by decide) (by decide)
          (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega)],
      fun b => by
        rw [hcent₃ b, hcent₂ b, hregs₁ (regCenter b)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega)
          (fun _ _ _ _ => by dsimp [regCenter, regRayActive, Reg]; omega)],
      fun b hb j hj => by
        rw [hact₃ b j hj, hact₂_ge b (by omega) j hj,
          hregs₁ (regRayActive l b j)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
            (by dsimp [regRayActive, Reg]; omega)
            (fun a' ha' j' hj' hcol => by
              have := (regRayActive_inj hj hj' hcol).1
              omega)],
      by rw [hin₃, hin₂, harrs₁],
      fun b j => by rw [hstar₃ b j, hstar₂ b j, harrs₁]⟩

/-! ### Section 2: `packAlg74InCmd` and `runStep75Cmd` -/

theorem mem_enc_lt_two_pow {n w : ℕ} (G : MultiDigraph n)
    (hn_w : n < 2 ^ w) (hedges_w : G.numEdges < 2 ^ w) :
    ∀ x ∈ G.enc, x < 2 ^ w := by
  intro x hx
  have hm'_le : G.numActivePairs ≤ G.numEdges := numActivePairs_le_numEdges G
  simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · exact hn_w
  · omega
  · exact all_lt_flatTriples G G.activePairsList hn_w
      (fun p _ => Nat.lt_of_le_of_lt (G.edgeMult_le_numEdges p.1 p.2) hedges_w) x hx

/-- Suffix of `encHPaths paths` starting from path index `j` for `rem` paths. -/
def encHPathsFrom {n k : ℕ} (paths : Fin k → List (Fin n)) (j : ℕ) : ℕ → List ℕ
  | 0 => []
  | rem + 1 =>
    if hj : j < k then
      (paths ⟨j, hj⟩).length :: (paths ⟨j, hj⟩).map Fin.val ++ encHPathsFrom paths (j + 1) rem
    else
      []

theorem encHPathsFrom_eq_drop_flatMap {n k : ℕ} (paths : Fin k → List (Fin n)) :
    ∀ (rem j : ℕ) (_hrem : j + rem = k),
      encHPathsFrom paths j rem =
        ((List.finRange k).drop j).flatMap (fun i => (paths i).length :: (paths i).map Fin.val)
  | 0, j, hrem => by
    have hj : j = k := by omega
    subst hj
    simp [encHPathsFrom, List.drop_eq_nil_of_le]
  | rem + 1, j, hrem => by
    have hj : j < k := by omega
    have hj_len : j < (List.finRange k).length := by simp [hj]
    rw [List.drop_eq_getElem_cons hj_len]
    simp only [List.getElem_finRange, List.flatMap_cons, encHPathsFrom, dif_pos hj]
    rw [encHPathsFrom_eq_drop_flatMap paths rem (j + 1) (by omega)]
    rfl

theorem encHPathsFrom_zero_eq_encHPaths {n k : ℕ} (paths : Fin k → List (Fin n)) :
    encHPathsFrom paths 0 k = encHPaths paths := by
  rw [encHPathsFrom_eq_drop_flatMap paths k 0 (Nat.zero_add k)]
  simp [encHPaths]

theorem length_encHPathsFrom_le {n k : ℕ} (paths : Fin k → List (Fin n))
    (hP_len : ∀ i : Fin k, (paths i).length ≤ n) :
    ∀ (rem j : ℕ), (encHPathsFrom paths j rem).length ≤ rem * (n + 1)
  | 0, _ => by simp [encHPathsFrom]
  | rem + 1, j => by
    unfold encHPathsFrom
    split_ifs with hj
    · have ih := length_encHPathsFrom_le paths hP_len rem (j + 1)
      have hj_le := hP_len ⟨j, hj⟩
      simp only [List.length_append, List.length_cons, List.length_map]
      calc (paths ⟨j, hj⟩).length + 1 + (encHPathsFrom paths (j + 1) rem).length
          ≤ (n + 1) + rem * (n + 1) := by omega
        _ = (rem + 1) * (n + 1) := by ring
    · simp

theorem length_encHPaths_le {n k : ℕ} (paths : Fin k → List (Fin n))
    (hP_len : ∀ i : Fin k, (paths i).length ≤ n) :
    (encHPaths paths).length ≤ k * (n + 1) := by
  rw [← encHPathsFrom_zero_eq_encHPaths]
  exact length_encHPathsFrom_le paths hP_len k 0

/-- Add `1 + len (qPathArr j)` to `r_15` for `j, j + 1, ..., j + rem - 1`. -/
def sumQPathsLenSliceCmd (j : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (.assign 15 (.op .add (.op .add (.reg 15) (.const 1)) (.len (qPathArr j))))
      (sumQPathsLenSliceCmd (j + 1) rem)

theorem sumQPathsLenSliceCmd_exec {w n k : ℕ} (paths : Fin k → List (Fin n))
    (hw1 : 1 < 2 ^ w) :
    ∀ (rem j : ℕ) (_hrem : j + rem = k) (acc : ℕ) {s : State}
      (_htot_w : acc + (encHPathsFrom paths j rem).length < 2 ^ w)
      (_hr15 : s.regs 15 = acc)
      (_hq : ∀ m : Fin k, s.arrs (qPathArr m.1) = (paths m).map Fin.val),
      ∃ s' t,
        Exec w (sumQPathsLenSliceCmd j rem) s s' t ∧
        t ≤ 6 * rem + 1 ∧
        s'.regs 15 = acc + (encHPathsFrom paths j rem).length ∧
        (∀ r : Reg, r ≠ 15 → s'.regs r = s.regs r) ∧
        s'.arrs = s.arrs
  | 0, j, _, acc, s, _, hr15, _ => by
    refine ⟨s, 1, .skip s, by omega, by simp [encHPathsFrom, hr15],
      fun _ _ => rfl, rfl⟩
  | rem + 1, j, hrem, acc, s, htot_w, hr15, hq => by
    have hj : j < k := by omega
    have hlen_step : (encHPathsFrom paths j (rem + 1)).length =
        1 + (paths ⟨j, hj⟩).length + (encHPathsFrom paths (j + 1) rem).length := by
      simp [encHPathsFrom, dif_pos hj]
      omega
    have hacc_w : acc < 2 ^ w := by omega
    have hacc1_w : acc + 1 < 2 ^ w := by omega
    have hPj_w : (paths ⟨j, hj⟩).length < 2 ^ w := by omega
    have hacc_Pj_w : acc + 1 + (paths ⟨j, hj⟩).length < 2 ^ w := by omega
    have hq_j : (s.arrs (qPathArr j)).length = (paths ⟨j, hj⟩).length := by
      simpa using congrArg List.length (hq ⟨j, hj⟩)
    let s₁ := s.setReg 15 (acc + 1 + (paths ⟨j, hj⟩).length)
    have hex₁ : Exec w (.assign 15 (.op .add (.op .add (.reg 15) (.const 1)) (.len (qPathArr j))))
        s s₁ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr15, hacc_w, hw1,
        hacc1_w, hq_j, hPj_w, hacc_Pj_w])
    rcases sumQPathsLenSliceCmd_exec paths hw1 rem (j + 1) (by omega)
        (acc + 1 + (paths ⟨j, hj⟩).length) (s := s₁)
        (by omega) (by simp [s₁]) (fun m => by simp [s₁, hq m]) with
      ⟨s₂, t₂, hex₂, ht₂, hr15_2, hregs₂, harrs₂⟩
    refine ⟨s₂, 6 + t₂, .seq hex₁ hex₂, by omega,
      by rw [hr15_2, hlen_step]; omega,
      fun r hr => by rw [hregs₂ r hr]; simp [s₁, hr],
      harrs₂⟩

/-- Append `(paths ⟨j, hj⟩).length :: (paths ⟨j, hj⟩).map Fin.val` to `bufArr` at `r_7` for
`j, j + 1, ..., j + rem - 1`. -/
def appendQPathsEncSliceCmd (j : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (pushBufCmd bufArr 7 (.len (qPathArr j)))
      (.seq (.assign 8 (.const 0))
        (.seq (.assign 9 (.len (qPathArr j)))
          (.seq (appendForwardSliceLoop bufArr (qPathArr j))
            (appendQPathsEncSliceCmd (j + 1) rem))))

theorem appendQPathsEncSliceCmd_exec {w n k : ℕ} (paths : Fin k → List (Fin n))
    (hP_len : ∀ m : Fin k, (paths m).length ≤ n)
    (cap : ℕ) (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w) :
    ∀ (rem j : ℕ) (_hrem : j + rem = k) (L : List ℕ) {s : State}
      (_hbuf : IsBufPrefix s bufArr 7 cap L)
      (_hfit : L.length + (encHPathsFrom paths j rem).length ≤ cap)
      (_hq : ∀ m : Fin k, s.arrs (qPathArr m.1) = (paths m).map Fin.val),
      ∃ s' t,
        Exec w (appendQPathsEncSliceCmd j rem) s s' t ∧
        t ≤ rem * (21 * n + 15) + 1 ∧
        IsBufPrefix s' bufArr 7 cap (L ++ encHPathsFrom paths j rem) ∧
        (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ arr : Arr, arr ≠ bufArr → s'.arrs arr = s.arrs arr)
  | 0, j, _, L, s, hbuf, _, _ => by
    refine ⟨s, 1, .skip s, by omega, by simpa [encHPathsFrom] using hbuf,
      fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | rem + 1, j, hrem, L, s, hbuf, hfit, hq => by
    have h0_w : 0 < 2 ^ w := by omega
    have hj : j < k := by omega
    let P := paths ⟨j, hj⟩
    have hP_le : P.length ≤ n := hP_len ⟨j, hj⟩
    have hP_w : P.length < 2 ^ w := by omega
    have henc_step : encHPathsFrom paths j (rem + 1) =
        P.length :: P.map Fin.val ++ encHPathsFrom paths (j + 1) rem := by
      simp [encHPathsFrom, dif_pos hj, P]
    rw [henc_step] at hfit
    simp only [List.length_append, List.length_cons, List.length_map] at hfit
    have hq_j : s.arrs (qPathArr j) = P.map Fin.val := hq ⟨j, hj⟩
    rcases pushBufCmd_exec bufArr 7 (.len (qPathArr j)) cap L P.length (s := s)
        hw1 hcap_w hbuf (by omega)
        (by simp [Expr.eval, checkWord, hq_j, hP_w]) with
      ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hregs₁, harrs₁⟩
    simp only [Expr.cost_len] at ht₁
    have hq₁_j : s₁.arrs (qPathArr j) = P.map Fin.val := by
      rw [harrs₁ (qPathArr j) (by dsimp [qPathArr, bufArr, Arr]; omega), hq_j]
    let s₂ := s₁.setReg 8 0
    have hex₂ : Exec w (.assign 8 (.const 0)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    let s₃ := s₂.setReg 9 P.length
    have hex₃ : Exec w (.assign 9 (.len (qPathArr j))) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, s₂, hq₁_j, hP_w])
    have hbuf₃ : IsBufPrefix s₃ bufArr 7 cap (L ++ [P.length]) :=
      hbuf₁.of_preserve (by simp [s₃, s₂]) (by simp [s₃, s₂])
    have hq₃_j : s₃.arrs (qPathArr j) = P.map Fin.val := by
      simp [s₃, s₂, hq₁_j]
    rcases appendForwardSliceLoop_exec bufArr (qPathArr j)
        (by dsimp [qPathArr, bufArr, Arr]; omega)
        cap hw1 hcap_w (P.map Fin.val) 0 (L ++ [P.length]) (s := s₃)
        (by simp [hq₃_j, hP_w])
        (by simp [hq₃_j])
        (fun i hi => by simp [hq₃_j, List.getElem?_eq_getElem hi])
        (fun v hv => by rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega)
        hbuf₃
        (by simp; omega)
        (by simp [s₃, s₂])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hbuf₄, _, _, hregs₄, harrs₄⟩
    simp only [List.length_map] at ht₄
    have hq₄ : ∀ m : Fin k, s₄.arrs (qPathArr m.1) = (paths m).map Fin.val := by
      intro m
      rw [harrs₄ (qPathArr m.1) (by dsimp [qPathArr, bufArr, Arr]; omega)]
      simp only [s₃, s₂, State.setReg_arrs]
      rw [harrs₁ (qPathArr m.1) (by dsimp [qPathArr, bufArr, Arr]; omega)]
      exact hq m
    rcases appendQPathsEncSliceCmd_exec paths hP_len cap hw1 hn_w hcap_w
        rem (j + 1) (by omega) ((L ++ [P.length]) ++ P.map Fin.val) (s := s₄)
        hbuf₄ (by simp; omega) hq₄ with
      ⟨s₅, t₅, hex₅, ht₅, hbuf₅, hregs₅, harrs₅⟩
    have hlist_eq :
        ((L ++ [P.length]) ++ P.map Fin.val) ++ encHPathsFrom paths (j + 1) rem =
          L ++ encHPathsFrom paths j (rem + 1) := by
      simp [henc_step, List.append_assoc]
    rw [hlist_eq] at hbuf₅
    have hmul : (rem + 1) * (21 * n + 15) = (21 * n + 15) + rem * (21 * n + 15) := by ring
    refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
      by omega,
      hbuf₅,
      fun r h7 h8 h9 h11 => by
        rw [hregs₅ r h7 h8 h9 h11, hregs₄ r h7 h8 h9 h11]
        simp only [s₃, s₂, State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8]
        exact hregs₁ r h7,
      fun arr ha => by
        rw [harrs₅ arr ha, harrs₄ arr ha]
        simp only [s₃, s₂, State.setReg_arrs]
        exact harrs₁ arr ha⟩

/-- Pack `encAlg74In y = y.G.enc ++ y.W.encList ++ encHPaths y.paths` into `inArr`. -/
def packAlg74InCmd (k : ℕ) : Cmd :=
  .seq (.assign 15 (.op .add (.reg 2) (.len wallEncArr)))
    (.seq (sumQPathsLenSliceCmd 0 k)
      (.seq (initBufCmd bufArr 7 (.reg 15))
        (.seq (.assign 8 (.const 0))
          (.seq (.assign 9 (.reg 2))
            (.seq (appendForwardSliceLoop bufArr inArr)
              (.seq (.assign 8 (.const 0))
                (.seq (.assign 9 (.len wallEncArr))
                  (.seq (appendForwardSliceLoop bufArr wallEncArr)
                    (.seq (appendQPathsEncSliceCmd 0 k)
                      (copyArrCmd bufArr inArr))))))))))

theorem packAlg74InCmd_exec {w p r l m : ℕ}
    (x : Alg77Input p l m) (y : Alg74Input p r)
    (hn_eq : y.n = x.n)
    (hG_eq : y.G.enc = x.G.enc)
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hn_w : 2 * x.n < 2 ^ w)
    (hedges_w : x.G.numEdges < 2 ^ w)
    (hin_x_w : (encAlg77In x).length < 2 ^ w)
    (hin_y_w : (encAlg74In y).length < 2 ^ w)
    (hr2 : s.regs 2 = 2 + 3 * x.G.numActivePairs)
    (hin : s.arrs inArr = encAlg77In x)
    (hwall : s.arrs wallEncArr = y.W.encList)
    (hq : ∀ j : Fin (p.choose 2), s.arrs (qPathArr j.1) = (y.paths j).map Fin.val) :
    ∃ s' t,
      Exec w (packAlg74InCmd (p.choose 2)) s s' t ∧
      t ≤ (p.choose 2) * (21 * x.n + 21) + 44 * (encAlg74In y).length + 35 ∧
      s'.arrs inArr = encAlg74In y := by
  have h0_w : 0 < 2 ^ w := by omega
  let k := p.choose 2
  have hG_len : x.G.enc.length = 2 + 3 * x.G.numActivePairs := x.G.length_enc
  have hP_len : ∀ j : Fin k, (y.paths j).length ≤ y.n := fun j =>
    length_le_of_nodup_fin (y.hpaths_valid j).choose_spec.2.1
  have hy_n_w : y.n < 2 ^ w := by omega
  have hlen_y : (encAlg74In y).length =
      x.G.enc.length + y.W.encList.length + (encHPaths y.paths).length := by
    simp [encAlg74In, hG_eq, List.length_append]
    omega
  have hr2_w : s.regs 2 < 2 ^ w := by omega
  have hG_len_w : x.G.enc.length < 2 ^ w := by omega
  have hW_w : y.W.encList.length < 2 ^ w := by omega
  have hGW_w : x.G.enc.length + y.W.encList.length < 2 ^ w := by omega
  -- Step 1: r_15 := r_2 + len wallEncArr
  let s₁ := s.setReg 15 (x.G.enc.length + y.W.encList.length)
  have hr2' : s.regs 2 = x.G.enc.length := hr2.trans hG_len.symm
  have hex₁ : Exec w (.assign 15 (.op .add (.reg 2) (.len wallEncArr))) s s₁ 4 :=
    .assign (eval_op_add
      (by rw [Expr.eval, hr2', checkWord, if_pos hG_len_w])
      (eval_len (congrArg List.length hwall) hW_w) hGW_w)
  -- Step 2: sumQPathsLenSliceCmd 0 k
  rcases sumQPathsLenSliceCmd_exec y.paths hw1 k 0 (Nat.zero_add k)
      (x.G.enc.length + y.W.encList.length) (s := s₁)
      (by rw [encHPathsFrom_zero_eq_encHPaths]; omega)
      (by simp [s₁])
      (fun m => by simp [s₁, hq m]) with
    ⟨s₂, t₂, hex₂, ht₂, hr15_2, hregs₂, harrs₂⟩
  rw [encHPathsFrom_zero_eq_encHPaths, ← hlen_y] at hr15_2
  -- Step 3: initBufCmd bufArr 7 (.reg 15)
  rcases initBufCmd_exec bufArr 7 (.reg 15) (encAlg74In y).length (s := s₂) h0_w
      (by simp [Expr.eval, checkWord, hr15_2, hin_y_w]) with
    ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hregs₃, harrs₃⟩
  simp only [Expr.cost_reg] at ht₃
  -- Step 4: append x.G.enc from inArr
  have hin₃ : s₃.arrs inArr = encAlg77In x := by
    rw [harrs₃ inArr (by decide), harrs₂]; exact hin
  have hr2_3 : s₃.regs 2 = x.G.enc.length := by
    rw [hregs₃ 2 (by decide), hregs₂ 2 (by decide)]
    simp [s₁, hr2, hG_len]
  let s₄ := s₃.setReg 8 0
  have hex₄ : Exec w (.assign 8 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₅ := s₄.setReg 9 x.G.enc.length
  have hex₅ : Exec w (.assign 9 (.reg 2)) s₄ s₅ 2 :=
    .assign (by rw [Expr.eval, State.setReg_regs_ne _ _ (by decide), hr2_3, checkWord, if_pos hG_len_w])
  have hbuf₅ : IsBufPrefix s₅ bufArr 7 (encAlg74In y).length [] :=
    hbuf₃.of_preserve (by simp [s₅, s₄]) (by simp [s₅, s₄])
  have hin₅ : s₅.arrs inArr = encAlg77In x := by simp [s₅, s₄, hin₃]
  have hG_prefix : encAlg77In x =
      x.G.enc ++ (x.W.encList ++
        (List.finRange k).flatMap (fun a => (x.centers a).1 :: encHPaths (x.rays a))) := by
    simp [encAlg77In, k, List.append_assoc]
  rcases appendForwardSliceLoop_exec bufArr inArr (by decide)
      (encAlg74In y).length hw1 hin_y_w x.G.enc 0 [] (s := s₅)
      (by simp [hin₅, hin_x_w])
      (by rw [hin₅, hG_prefix, List.length_append]; omega)
      (fun j hj => by
        rw [hin₅, hG_prefix, Nat.zero_add, List.getElem?_append_left hj,
          List.getElem?_eq_getElem hj])
      (mem_enc_lt_two_pow x.G (by omega) hedges_w)
      hbuf₅ (by simp; omega) (by simp [s₅, s₄]) (by simp [s₅]) with
    ⟨s₆, t₆, hex₆, ht₆, hbuf₆, _, _, hregs₆, harrs₆⟩
  simp only [List.nil_append] at hbuf₆
  -- Step 5: append y.W.encList from wallEncArr
  have hwall₆ : s₆.arrs wallEncArr = y.W.encList := by
    rw [harrs₆ wallEncArr (by decide)]
    simp only [s₅, s₄, State.setReg_arrs]
    rw [harrs₃ wallEncArr (by decide), harrs₂]
    exact hwall
  let s₇ := s₆.setReg 8 0
  have hex₇ : Exec w (.assign 8 (.const 0)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₈ := s₇.setReg 9 y.W.encList.length
  have hex₈ : Exec w (.assign 9 (.len wallEncArr)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₇, hwall₆, hW_w])
  have hbuf₈ : IsBufPrefix s₈ bufArr 7 (encAlg74In y).length x.G.enc :=
    hbuf₆.of_preserve (by simp [s₈, s₇]) (by simp [s₈, s₇])
  have hwall₈ : s₈.arrs wallEncArr = y.W.encList := by simp [s₈, s₇, hwall₆]
  have hy_h1 : 1 ≤ y.h := by have := y.hW_valid.1; omega
  obtain ⟨hy_VJ, hy_2h2, hy_EJ, _⟩ := validWall_size_bounds y.W hy_h1 y.hW_valid.2.2
  have hW_words : ∀ v ∈ y.W.encList, v < 2 ^ w :=
    forall_mem_wallEncList_lt y.W (by omega) (by omega) (by omega) hy_n_w hW_w
  rcases appendForwardSliceLoop_exec bufArr wallEncArr (by decide)
      (encAlg74In y).length hw1 hin_y_w y.W.encList 0 x.G.enc (s := s₈)
      (by simp [hwall₈, hW_w])
      (by simp [hwall₈])
      (fun j hj => by simp [hwall₈, List.getElem?_eq_getElem hj])
      hW_words hbuf₈ (by omega) (by simp [s₈, s₇]) (by simp [s₈]) with
    ⟨s₉, t₉, hex₉, ht₉, hbuf₉, _, _, hregs₉, harrs₉⟩
  -- Step 6: appendQPathsEncSliceCmd 0 k
  have hq₉ : ∀ j : Fin k, s₉.arrs (qPathArr j.1) = (y.paths j).map Fin.val := by
    intro j
    rw [harrs₉ (qPathArr j.1) (by dsimp [qPathArr, bufArr, Arr]; omega)]
    simp only [s₈, s₇, State.setReg_arrs]
    rw [harrs₆ (qPathArr j.1) (by dsimp [qPathArr, bufArr, Arr]; omega)]
    simp only [s₅, s₄, State.setReg_arrs]
    rw [harrs₃ (qPathArr j.1) (by dsimp [qPathArr, bufArr, Arr]; omega), harrs₂]
    exact hq j
  rcases appendQPathsEncSliceCmd_exec y.paths hP_len (encAlg74In y).length
      hw1 hy_n_w hin_y_w k 0 (Nat.zero_add k) (x.G.enc ++ y.W.encList) (s := s₉)
      hbuf₉ (by rw [encHPathsFrom_zero_eq_encHPaths, List.length_append]; omega) hq₉ with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hbuf₁₀, hregs₁₀, harrs₁₀⟩
  rw [hn_eq] at ht₁₀
  rw [encHPathsFrom_zero_eq_encHPaths, ← hG_eq] at hbuf₁₀
  have hbuf₁₀_eq : s₁₀.arrs bufArr = encAlg74In y :=
    hbuf₁₀.to_eq
  -- Step 7: copyArrCmd bufArr inArr
  have hy_words : ∀ v ∈ encAlg74In y, v < 2 ^ w := by
    intro v hv
    simp only [encAlg74In, List.mem_append] at hv
    rcases hv with (hvG | hvW) | hvP
    · rw [hG_eq] at hvG
      exact mem_enc_lt_two_pow x.G (by omega) hedges_w v hvG
    · exact hW_words v hvW
    · simp only [encHPaths, List.mem_flatMap, List.mem_finRange, true_and,
        List.mem_cons, List.mem_map] at hvP
      rcases hvP with ⟨j, rfl | ⟨u, _, rfl⟩⟩
      · have := hP_len j; omega
      · have := u.2; omega
  rcases copyArrCmd_exec bufArr inArr (by decide) (s := s₁₀) hw1
      (by simp [hbuf₁₀_eq, hin_y_w])
      (by rw [hbuf₁₀_eq]; exact hy_words) with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hin₁₁, _, _⟩
  rw [hbuf₁₀_eq] at hin₁₁ ht₁₁
  have hmul_k : (p.choose 2) * (21 * x.n + 21) =
      6 * (p.choose 2) + (p.choose 2) * (21 * x.n + 15) := by ring
  dsimp only [k] at ht₂ ht₁₀
  refine ⟨s₁₁, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex₁₁))))))))),
    by omega,
    hin₁₁⟩

/-- Complete Word RAM command for GM XIII (7.6) + (7.5): runs `runStep76Cmd`, initializes active
ray flags, executes `step75RecCmd`, and packs `encAlg74In (runStep75 hp hr x)` into `inArr`. -/
def runStep75Cmd (p r : ℕ) : Cmd :=
  let k := p.choose 2
  let l := 2 * k ^ 2 - k + 3
  .seq (runStep76Cmd p l)
    (.seq (initAllStarsActiveSliceCmd l 0 k)
      (.seq (step75RecCmd r l k)
        (packAlg74InCmd k)))

/-- Total time-bound polynomial `B(p, n, L_in, L_out)` for `runStep75Cmd p r` on an input with `n`
vertices, input length `L_in`, and output length `L_out`. -/
def runStep75TimeBound (p n L_out : ℕ) : ℕ :=
  let k := p.choose 2
  let l := 2 * k ^ 2 - k + 3
  (k * (k * (l * (745 * n + 1230) + 1) + 5700 * n + 5700) +
    k * (l * (22 * n + 25) + 9) + 414 * n + 300) +
  (k * (2 * l + 1) + 1) +
  (k * step75OneStepBound l k n + 1) +
  (k * (21 * n + 21) + 44 * L_out + 35)

theorem runStep75Cmd_exec {w p r : ℕ} (hp : 2 ≤ p) (hr : 2 ≤ r)
    (x : Alg77Input p (2 * (p.choose 2) ^ 2 - p.choose 2 + 3) (2 * r + 4 * p.choose 2))
    {s : State}
    (hword : 4 * x.n + 12 < 2 ^ w)
    (hedges_w : x.G.numEdges < 2 ^ w)
    (hl_w : 2 * (p.choose 2) ^ 2 - p.choose 2 + 3 < 2 ^ w)
    (h2r_w : 2 * r < 2 ^ w)
    (hin_x_w : (encAlg77In x).length < 2 ^ w)
    (hin_y_w : (encAlg74In (runStep75 hp hr x)).length < 2 ^ w)
    (hin : s.arrs inArr = encAlg77In x) :
    ∃ s' t,
      Exec w (runStep75Cmd p r) s s' t ∧
      t ≤ runStep75TimeBound p x.n (encAlg74In (runStep75 hp hr x)).length ∧
      s'.arrs inArr = encAlg74In (runStep75 hp hr x) := by
  let k := p.choose 2
  let l := 2 * k ^ 2 - k + 3
  have hk_pos : 0 < k := Nat.choose_pos hp
  have hk_le_l : k ≤ 2 * k ^ 2 := by nlinarith
  have hl3 : 3 ≤ l := by dsimp [l]; omega
  have hm3 : 3 ≤ 2 * r := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hl_w' : l < 2 ^ w := hl_w
  have h2k_w : 2 * k < 2 ^ w := by
    have : 2 * k ≤ l := by
      dsimp [l]
      have : 1 ≤ k := hk_pos
      have : 3 * k ≤ 2 * k ^ 2 + 3 := by nlinarith
      omega
    omega
  -- Step 1: runStep76Cmd p l
  rcases runStep76Cmd_exec hp hl3 hm3 x hword hin_x_w hin with
    ⟨s₁, t₁, hex₁, ht₁, hm₁, hr0_1, hr1_1, hr2_1, hin₁⟩
  -- Step 2: initAllStarsActiveSliceCmd l 0 k
  rcases initAllStarsActiveSliceCmd_exec (k := k) (l := l) h1_w k 0 (Nat.zero_add k) (s := s₁)
      (fun _ ha => False.elim (Nat.not_lt_zero _ ha)) with
    ⟨s₂, t₂, hex₂, ht₂, hact₂, hregs₂, harrs₂⟩
  let st := runStep76 hp hl3 hm3 x
  have hst := runStep76_spec hp hl3 hm3 x
  have hs₂_wall : WallStateHolds st.W s₂ :=
    hm₁.hwall.of_preserve
      (hregs₂ 0 (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega))
      (hregs₂ 3 (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega))
      (hregs₂ 12 (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega))
      (hregs₂ 13 (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega))
      (hregs₂ 14 (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega))
      (by rw [harrs₂]) (by rw [harrs₂]) (by rw [harrs₂]) (by rw [harrs₂])
      (by rw [harrs₂]) (by rw [harrs₂]) (by rw [harrs₂]) (by rw [harrs₂]) (by rw [harrs₂])
  have hcenters₂ : ∀ a : Fin k, s₂.regs (regCenter a.1) = (x.centers a).1 := by
    intro a
    rw [hregs₂ (regCenter a.1) (fun _ _ _ _ => by dsimp [regCenter, regRayActive, Reg]; omega)]
    exact hm₁.hcenters a
  have hsrc₂ : ∀ a : Fin k, ∀ j : Fin l,
      s₂.arrs (starRayArr l a.1 j.1) = (st.rays a j).map Fin.val := by
    intro a j
    rw [harrs₂]
    exact hm₁.hrays a j
  -- Step 3: step75RecCmd r l k
  have hh1 : 1 ≤ x.h - 2 * p.choose 2 := by have := hst.1.1; omega
  obtain ⟨hVJ_n, h2h2_VJ, hEJ_n, henc_n⟩ := validWall_size_bounds st.W hh1 hst.1.2.2
  let act_true : Fin k → Fin l → Bool := fun _ _ => true
  have hS_true : ∀ a : Fin k,
      st.W.IsStarRayList (2 * r) (x.centers a) (activeRayList (st.rays a) (act_true a)) := by
    intro a
    rw [activeRayList_true]
    exact st.W.isStarRayList_starRayListOfFin (hst.2.1 a) (hst.2.2.1 a)
      (hst.2.2.2.1 a) (hst.2.2.2.2 a)
  have hl_true : ∀ a : Fin k,
      2 * k ^ 2 - k + 3 ≤ (activeRayList (st.rays a) (act_true a)).length := by
    intro a
    rw [activeRayList_true, WallOfHeight.length_starRayListOfFin]
  have hneP_st : ∀ a : Fin k, ∀ j : Fin l, st.rays a j ≠ [] :=
    fun a j => (hst.2.2.1 a j).choose
  have hP_len_st : ∀ a : Fin k, ∀ j : Fin l, (st.rays a j).length ≤ x.n :=
    fun a j => length_le_of_nodup_fin (hst.2.2.1 a j).choose_spec.2.2.1
  rcases step75RecCmd_exec (K := k) st.W hst.1.1 hst.1.2.1 hst.1.2.2
      h2_w (by omega) hl_w (by omega) h2r_w (by omega) (by omega) (by omega)
      k (le_refl k) h2k_w st.rays act_true x.centers
      hS_true hl_true x.hcenters hst.2.2.1 hneP_st hP_len_st
      hs₂_wall hcenters₂ hsrc₂ (fun a j => by dsimp [act_true]; exact hact₂ a j) with
    ⟨s₃, t₃, hex₃, ht₃, hs₃_wall, hq₃, hr1_3, hr2_3, _, _, hin₃, _⟩
  -- Step 4: packAlg74InCmd k
  let y := runStep75 hp hr x
  have hy_paths : ∀ j : Fin k, s₃.arrs (qPathArr j.1) = (y.paths j).map Fin.val := by
    intro j
    have hfun : (fun a : Fin k => activeRayList (st.rays a) (act_true a)) =
        (fun a : Fin k => WallOfHeight.starRayListOfFin (st.rays a)) := by
      funext a; exact activeRayList_true (st.rays a)
    simpa [y, runStep75, WallOfHeight.IsFarHPathList.toAlg74Input, hfun] using hq₃ j.1 j.2
  have hr2_3' : s₃.regs 2 = 2 + 3 * x.G.numActivePairs := by
    rw [hr2_3, hregs₂ 2 (fun _ _ _ _ => by dsimp [regRayActive, Reg]; omega), hr2_1]
  have hin₃' : s₃.arrs inArr = encAlg77In x := by
    rw [hin₃, harrs₂, hin₁]
  rcases packAlg74InCmd_exec x y (runStep75_n hp hr x)
      (congrArg MultiDigraph.enc (runStep75_G hp hr x))
      h1_w (by omega) hedges_w hin_x_w hin_y_w
      hr2_3' hin₃' hs₃_wall.henc hy_paths with
    ⟨s₄, t₄, hex₄, ht₄, hin₄⟩
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by unfold runStep75TimeBound; dsimp only [k, l, y] at ht₁ ht₂ ht₃ ht₄ ⊢; omega,
    hin₄⟩

end GraphMinor.Compute
