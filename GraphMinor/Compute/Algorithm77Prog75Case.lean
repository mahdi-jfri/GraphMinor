module

public import GraphMinor.Compute.Algorithm77Prog76Full
public import GraphMinor.Compute.Algorithm77Prog75

/-!
# Word RAM Implementation of Step (7.5) Case A and Case B for GM XIII (7.7)

This file implements the Word RAM subroutines for Case A and Case B of the inductive step in
Graph Minors XIII, (7.5):
1. **Section 1:** Dynamic-index array copy (`copyArrByIdxSliceCmd`) and Case A path construction
   (`buildOneCaseAPathCmd`, `buildCaseAPathsSliceCmd`, `copyRPathsToQPathsSliceCmd`,
   `buildCaseAPathsCmd`), matching `WallOfHeight.buildCaseAPaths`.
2. **Section 2:** Pure `ℕ` brick distance command (`exprNatCornerFaceDist`, `listMinMapCmd`,
   `computeBrickDistCmd`) and Case B good-ray search and joining (`testGoodRayForQCmd`,
   `testIsGoodRaySliceCmd`, `findTwoGoodRaysSliceCmd`, `caseBCmd`), matching
   `WallOfHeight.isGoodRay` and `WallOfHeight.joinTwoRays`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

set_option linter.deprecated false

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges

/-! ### Section 1: Dynamic-Index Array Copy and Case A Path Construction -/

/-- Check indices `i, i + 1, ..., i + rem - 1` and copy `arrOf i₀` into `dst` when
`s.regs regIdx == i₀`. -/
def copyArrByIdxSliceCmd (arrOf : ℕ → Arr) (regIdx : Reg) (dst : Arr) (i : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (.ite (exprEq (.reg regIdx) (.const i))
        (copyArrCmd (arrOf i) dst)
        .skip)
      (copyArrByIdxSliceCmd arrOf regIdx dst (i + 1) rem)

theorem copyArrByIdxSliceCmd_exec {w n l : ℕ} (arrOf : ℕ → Arr) (regIdx : Reg) (dst : Arr)
    (hne_dst : ∀ j < l, arrOf j ≠ dst)
    (hne_r7 : regIdx ≠ 7) (hne_r8 : regIdx ≠ 8) (hne_r9 : regIdx ≠ 9) (hne_r11 : regIdx ≠ 11)
    (i₀ : Fin l)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hl_w : l < 2 ^ w) :
    ∀ (rem i : ℕ) (_hrem : i + rem = l) {s : State}
      (_hrIdx : s.regs regIdx = i₀.1)
      (_hsrc_len : (s.arrs (arrOf i₀.1)).length ≤ n)
      (_hsrc_w : ∀ v ∈ s.arrs (arrOf i₀.1), v < 2 ^ w),
      ∃ s' t,
        Exec w (copyArrByIdxSliceCmd arrOf regIdx dst i rem) s s' t ∧
        t ≤ rem * (22 * n + 16) + 1 ∧
        s'.arrs dst = (if i ≤ i₀.1 then s.arrs (arrOf i₀.1) else s.arrs dst) ∧
        (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ arr : Arr, arr ≠ dst → s'.arrs arr = s.arrs arr)
  | 0, i, hrem, s, _, _, _ => by
    have hi_gt : ¬ (i ≤ i₀.1) := by have := i₀.2; omega
    refine ⟨s, 1, .skip s, by omega, by simp [hi_gt],
      fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | rem + 1, i, hrem, s, hrIdx, hsrc_len, hsrc_w => by
    have h0_w : 0 < 2 ^ w := by omega
    have hi_lt : i < l := by omega
    have hi_w : i < 2 ^ w := by omega
    have hi₀_w : i₀.1 < 2 ^ w := by have := i₀.2; omega
    have heval_idx : (Expr.reg regIdx).eval w s = some i₀.1 := by
      simp [Expr.eval, checkWord, hrIdx, hi₀_w]
    have heval_i : (Expr.const i).eval w s = some i := by
      simp [Expr.eval, checkWord, hi_w]
    have heval_eq : (exprEq (.reg regIdx) (.const i)).eval w s =
        some (if i₀.1 = i then 1 else 0) :=
      eval_exprEq hw1 heval_idx heval_i
    by_cases heq : i₀.1 = i
    · rw [if_pos heq] at heval_eq
      have hsrc_len_w : (s.arrs (arrOf i)).length < 2 ^ w := by rw [← heq]; omega
      have hsrc_vals_w : ∀ v ∈ s.arrs (arrOf i), v < 2 ^ w := by rw [← heq]; exact hsrc_w
      rcases copyArrCmd_exec (arrOf i) dst (hne_dst i hi_lt) (s := s)
          hw1 hsrc_len_w hsrc_vals_w with
        ⟨s₁, t₁, hex_cp, ht₁, hdst₁, hregs₁, harrs₁⟩
      have hex₁ : Exec w (.ite (exprEq (.reg regIdx) (.const i))
          (copyArrCmd (arrOf i) dst) .skip) s s₁ _ :=
        .ite_true heval_eq (by omega) hex_cp
      have hrIdx₁ : s₁.regs regIdx = i₀.1 := by
        rw [hregs₁ regIdx hne_r7 hne_r8 hne_r9 hne_r11, hrIdx]
      have hsrc₁ : s₁.arrs (arrOf i₀.1) = s.arrs (arrOf i₀.1) :=
        harrs₁ (arrOf i₀.1) (hne_dst i₀.1 i₀.2)
      rcases copyArrByIdxSliceCmd_exec arrOf regIdx dst hne_dst hne_r7 hne_r8 hne_r9 hne_r11
          i₀ hw1 hn_w hl_w rem (i + 1) (by omega) (s := s₁)
          hrIdx₁ (by rwa [hsrc₁]) (by rwa [hsrc₁]) with
        ⟨s₂, t₂, hex₂, ht₂, hdst₂, hregs₂, harrs₂⟩
      have hnot_le : ¬ (i + 1 ≤ i₀.1) := by omega
      have hle_i : i ≤ i₀.1 := by omega
      rw [if_neg hnot_le, hdst₁, ← heq] at hdst₂
      have ht₁_le : t₁ ≤ 22 * n + 10 := by rw [← heq] at ht₁; omega
      have hmul : (rem + 1) * (22 * n + 16) = rem * (22 * n + 16) + (22 * n + 16) := by ring
      refine ⟨s₂, _, .seq hex₁ hex₂,
        by simp [exprEq]; omega,
        by rw [if_pos hle_i]; exact hdst₂,
        fun r h7 h8 h9 h11 => by rw [hregs₂ r h7 h8 h9 h11, hregs₁ r h7 h8 h9 h11],
        fun arr ha => by rw [harrs₂ arr ha, harrs₁ arr ha]⟩
    · rw [if_neg heq] at heval_eq
      have hex₁ : Exec w (.ite (exprEq (.reg regIdx) (.const i))
          (copyArrCmd (arrOf i) dst) .skip) s s _ :=
        .ite_false heval_eq (.skip s)
      rcases copyArrByIdxSliceCmd_exec arrOf regIdx dst hne_dst hne_r7 hne_r8 hne_r9 hne_r11
          i₀ hw1 hn_w hl_w rem (i + 1) (by omega) (s := s)
          hrIdx hsrc_len hsrc_w with
        ⟨s₂, t₂, hex₂, ht₂, hdst₂, hregs₂, harrs₂⟩
      have hdst₂' : s₂.arrs dst = if i ≤ i₀.1 then s.arrs (arrOf i₀.1) else s.arrs dst := by
        rw [hdst₂]
        by_cases hle : i ≤ i₀.1
        · have hle1 : i + 1 ≤ i₀.1 := by omega
          simp [hle, hle1]
        · have hle1 : ¬ (i + 1 ≤ i₀.1) := by omega
          simp [hle, hle1]
      have hmul : (rem + 1) * (22 * n + 16) = rem * (22 * n + 16) + (22 * n + 16) := by ring
      refine ⟨s₂, _, .seq hex₁ hex₂,
        by simp [exprEq]; omega,
        hdst₂', hregs₂, harrs₂⟩

/-- Construct the `t`-th Case A replacement `H`-path in `rPathArr t` from the hit tables
`hitIdxArr`, `hitRayIdxArr`, and `hitPrefArr`. -/
def buildOneCaseAPathCmd (l t : ℕ) (qArr : Arr) : Cmd :=
  .seq (.assign 17 (.read hitIdxArr (.const (2 * t))))
    (.seq (.assign 18 (.read hitIdxArr (.const (2 * t + 1))))
      (.seq (.assign 22 (.read qArr (.reg 17)))
        (.seq (.assign 23 (.read qArr (.reg 18)))
          (.seq (.assign 19 (.read hitRayIdxArr (.const (2 * t))))
            (.seq (copyArrByIdxSliceCmd hitPrefArr 19 tmpPathArr1 0 l)
              (.seq (.assign 19 (.read hitRayIdxArr (.const (2 * t + 1))))
                (.seq (copyArrByIdxSliceCmd hitPrefArr 19 tmpPathArr2 0 l)
                  (.seq (suffixFromArrCmd qArr tmpPathArr3 22)
                    (.seq (prefixUntilSingleArrCmd tmpPathArr3 bufArr 23)
                      (.seq (concatOverlapArrCmd tmpPathArr1 bufArr tmpPathArr3)
                        (.seq (reverseArrCmd tmpPathArr2 bufArr)
                          (concatOverlapArrCmd tmpPathArr3 bufArr (rPathArr t)))))))))))))

theorem length_suffixFrom_le {α : Type*} [DecidableEq α] (u : α) :
    ∀ L : List α, (suffixFrom u L).length ≤ L.length
  | [] => by simp [suffixFrom]
  | x :: xs => by
    unfold suffixFrom
    split_ifs
    · exact le_rfl
    · exact Nat.le_succ_of_le (length_suffixFrom_le u xs)

theorem subpathBetween_ne_nil_and_length_le {n : ℕ} (Q : List (Fin n)) (z₁ z₂ : Fin n)
    (hz₁ : z₁ ∈ Q) :
    WallOfHeight.subpathBetween Q z₁ z₂ ≠ [] ∧
    (WallOfHeight.subpathBetween Q z₁ z₂).length ≤ Q.length := by
  unfold WallOfHeight.subpathBetween
  have hneS : suffixFrom z₁ Q ≠ [] := suffixFrom_ne_nil hz₁
  have hneB : prefixUntil {z₂} (suffixFrom z₁ Q) ≠ [] := prefixUntil_ne_nil {z₂} hneS
  have hlen : (prefixUntil {z₂} (suffixFrom z₁ Q)).length ≤ Q.length :=
    (length_prefixUntil_le {z₂} (suffixFrom z₁ Q)).trans (length_suffixFrom_le z₁ Q)
  exact ⟨hneB, hlen⟩

theorem buildOneCaseAPathCmd_exec {w n l k' t : ℕ} (qArr : Arr)
    (hne_q1 : qArr ≠ tmpPathArr1) (hne_q2 : qArr ≠ tmpPathArr2)
    (hne_q3 : qArr ≠ tmpPathArr3) (_hne_qbuf : qArr ≠ bufArr)
    (_hne_qr : qArr ≠ rPathArr t)
    (Q : List (Fin n))
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (hneP : ∀ j : Fin l, rays j ≠ [])
    (hP_len : ∀ j : Fin l, (rays j).length ≤ n)
    (hQ_len : Q.length ≤ n)
    (ht_lt : t < k')
    (hhits : 2 * k' ≤ (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length)
    {s : State}
    (hw1 : 1 < 2 ^ w) (h3n_w : 3 * n < 2 ^ w) (hl_w : l < 2 ^ w)
    (hqArr : s.arrs qArr = Q.map Fin.val)
    (hbuf1 : IsBufPrefix s hitIdxArr 20 Q.length ((hitsIdxOnQ rays act Q).map Prod.fst))
    (hbuf2 : IsBufPrefix s hitRayIdxArr 21 Q.length ((hitsIdxOnQ rays act Q).map (fun p => p.2.1)))
    (hpref : ∀ j : Fin l,
      s.arrs (hitPrefArr j.1) = (WallOfHeight.rayHitPrefix Q (rays j)).map Fin.val) :
    let rs := activeRayList rays act
    have hlen_R : t < (WallOfHeight.buildCaseAPaths k' rs Q).length := by
      rw [WallOfHeight.length_buildCaseAPaths]; exact ht_lt
    ∃ s' time,
      Exec w (buildOneCaseAPathCmd l t qArr) s s' time ∧
      time ≤ 2 * l * (22 * n + 16) + 218 * n + 145 ∧
      s'.arrs (rPathArr t) = ((WallOfHeight.buildCaseAPaths k' rs Q)[t]'hlen_R).map Fin.val ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 17 → r ≠ 18 → r ≠ 19 → r ≠ 22 → r ≠ 23 → s'.regs r = s.regs r) ∧
      (∀ arr : Arr, arr ≠ tmpPathArr1 → arr ≠ tmpPathArr2 → arr ≠ tmpPathArr3 →
        arr ≠ bufArr → arr ≠ rPathArr t → s'.arrs arr = s.arrs arr) := by
  intro rs hlen_R
  change 2 * k' ≤ (WallOfHeight.hitsOnQ rs Q).length at hhits
  have hn_w : n < 2 ^ w := by omega
  have hQ_w : Q.length < 2 ^ w := by omega
  let hitsIdx := hitsIdxOnQ rays act Q
  have hhits_eq : WallOfHeight.hitsOnQ rs Q = hitsIdx.map (fun p => (p.1, rays p.2)) :=
    hitsOnQ_activeRayList rays act Q
  have hlen_hitsIdx : (WallOfHeight.hitsOnQ rs Q).length = hitsIdx.length := by
    rw [hhits_eq, List.length_map]
  have h0_hits : 2 * t < (WallOfHeight.hitsOnQ rs Q).length := by omega
  have h1_hits : 2 * t + 1 < (WallOfHeight.hitsOnQ rs Q).length := by omega
  have h2t_lt : 2 * t < hitsIdx.length := by omega
  have h2t1_lt : 2 * t + 1 < hitsIdx.length := by omega
  let p₁ := hitsIdx[2 * t]'h2t_lt
  let p₂ := hitsIdx[2 * t + 1]'h2t1_lt
  have hp₁_hits : (WallOfHeight.hitsOnQ rs Q)[2 * t]'h0_hits = (p₁.1, rays p₁.2) := by
    simp [hhits_eq, p₁]
  have hp₂_hits : (WallOfHeight.hitsOnQ rs Q)[2 * t + 1]'h1_hits = (p₂.1, rays p₂.2) := by
    simp [hhits_eq, p₂]
  obtain ⟨hi₁_raw, _, _, _⟩ :=
    WallOfHeight.mem_hitsOnQ (List.getElem_mem h0_hits)
  obtain ⟨hi₂_raw, _, _, _⟩ :=
    WallOfHeight.mem_hitsOnQ (List.getElem_mem h1_hits)
  have hi₁ : p₁.1 < Q.length := by simpa [hp₁_hits] using hi₁_raw
  have hi₂ : p₂.1 < Q.length := by simpa [hp₂_hits] using hi₂_raw
  let z₁ := Q[p₁.1]'hi₁
  let z₂ := Q[p₂.1]'hi₂
  have hbuild_eq : (WallOfHeight.buildCaseAPaths k' rs Q)[t]'hlen_R =
      WallOfHeight.joinRaysAlongSubpath Q (rays p₁.2) (rays p₂.2) z₁ z₂ := by
    rw [WallOfHeight.getElem_buildCaseAPaths rs Q hlen_R h0_hits h1_hits hi₁_raw hi₂_raw]
    simp [hp₁_hits, hp₂_hits, z₁, z₂]
  have hhitsIdx_le_Q : hitsIdx.length ≤ Q.length := by
    have h := hbuf1.2.2.1
    simpa [hitsIdx] using h
  have h2t_w : 2 * t < 2 ^ w := by omega
  have h2t1_w : 2 * t + 1 < 2 ^ w := by omega
  have hp1_w : p₁.1 < 2 ^ w := by omega
  have hp2_w : p₂.1 < 2 ^ w := by omega
  have hz1_w : z₁.1 < 2 ^ w := by have := z₁.2; omega
  have hz2_w : z₂.1 < 2 ^ w := by have := z₂.2; omega
  have hi1_ray_w : p₁.2.1 < 2 ^ w := by have := p₁.2.2; omega
  have hi2_ray_w : p₂.2.1 < 2 ^ w := by have := p₂.2.2; omega
  -- Step 1: r_17 := hitIdxArr[2 * t]
  have hget_idx1 : (s.arrs hitIdxArr)[2 * t]'(by rw [hbuf1.1]; omega) = p₁.1 := by
    apply getElem_of_getElem?
    have h := hbuf1.2.2.2 (2 * t) (by rw [List.length_map]; exact h2t_lt)
    rw [List.getElem_map] at h
    exact h
  let s₁ := s.setReg 17 p₁.1
  have hex₁ : Exec w (.assign 17 (.read hitIdxArr (.const (2 * t)))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h2t_w, hbuf1.1,
      show 2 * t < Q.length by omega, hget_idx1, hp1_w])
  -- Step 2: r_18 := hitIdxArr[2 * t + 1]
  have hget_idx2 : (s.arrs hitIdxArr)[2 * t + 1]'(by rw [hbuf1.1]; omega) = p₂.1 := by
    apply getElem_of_getElem?
    have h := hbuf1.2.2.2 (2 * t + 1) (by rw [List.length_map]; exact h2t1_lt)
    rw [List.getElem_map] at h
    exact h
  let s₂ := s₁.setReg 18 p₂.1
  have hex₂ : Exec w (.assign 18 (.read hitIdxArr (.const (2 * t + 1)))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₁, h2t1_w, hbuf1.1,
      show 2 * t + 1 < Q.length by omega, hget_idx2, hp2_w])
  -- Step 3: r_22 := qArr[r_17]
  let s₃ := s₂.setReg 22 z₁.1
  have hex₃ : Exec w (.assign 22 (.read qArr (.reg 17))) s₂ s₃ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₂, s₁, hp1_w, hqArr, hi₁, z₁, hz1_w])
  -- Step 4: r_23 := qArr[r_18]
  let s₄ := s₃.setReg 23 z₂.1
  have hex₄ : Exec w (.assign 23 (.read qArr (.reg 18))) s₃ s₄ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hp2_w, hqArr, hi₂, z₂, hz2_w])
  -- Step 5: r_19 := hitRayIdxArr[2 * t]
  have hget_ray1 : (s.arrs hitRayIdxArr)[2 * t]'(by rw [hbuf2.1]; omega) = p₁.2.1 := by
    apply getElem_of_getElem?
    have h := hbuf2.2.2.2 (2 * t) (by rw [List.length_map]; exact h2t_lt)
    rw [List.getElem_map] at h
    exact h
  let s₅ := s₄.setReg 19 p₁.2.1
  have hex₅ : Exec w (.assign 19 (.read hitRayIdxArr (.const (2 * t)))) s₄ s₅ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₄, s₃, s₂, s₁, h2t_w, hbuf2.1,
      show 2 * t < Q.length by omega, hget_ray1, hi1_ray_w])
  -- Step 6: copyArrByIdxSliceCmd hitPrefArr 19 tmpPathArr1 0 l
  let A₁ := WallOfHeight.rayHitPrefix Q (rays p₁.2)
  let A₂ := WallOfHeight.rayHitPrefix Q (rays p₂.2)
  have hA₁_ne : A₁ ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP p₁.2))
  have hA₂_ne : A₂ ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP p₂.2))
  have hA₁_len : A₁.length ≤ n := by
    calc A₁.length ≤ (rays p₁.2).reverse.length := length_prefixUntil_le Q.toFinset _
      _ = (rays p₁.2).length := List.length_reverse
      _ ≤ n := hP_len p₁.2
  have hA₂_len : A₂.length ≤ n := by
    calc A₂.length ≤ (rays p₂.2).reverse.length := length_prefixUntil_le Q.toFinset _
      _ = (rays p₂.2).length := List.length_reverse
      _ ≤ n := hP_len p₂.2
  rcases copyArrByIdxSliceCmd_exec hitPrefArr 19 tmpPathArr1
      (fun j _ => by dsimp [hitPrefArr, tmpPathArr1, Arr]; omega)
      (by decide) (by decide) (by decide) (by decide) p₁.2 hw1 hn_w hl_w l 0 (Nat.zero_add l)
      (s := s₅) (by simp [s₅])
      (by simp [s₅, s₄, s₃, s₂, s₁, hpref p₁.2, A₁, hA₁_len])
      (fun v hv => by
        simp only [s₅, s₄, s₃, s₂, s₁, State.setReg_arrs, hpref p₁.2] at hv
        rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
    ⟨s₆, t₆, hex₆, ht₆, htmp1_6, hregs₆, harrs₆⟩
  simp only [Nat.zero_le, ↓reduceIte, s₅, s₄, s₃, s₂, s₁, State.setReg_arrs, hpref p₁.2] at htmp1_6
  -- Step 7: r_19 := hitRayIdxArr[2 * t + 1]
  have hget_ray2 : (s.arrs hitRayIdxArr)[2 * t + 1]'(by rw [hbuf2.1]; omega) = p₂.2.1 := by
    apply getElem_of_getElem?
    have h := hbuf2.2.2.2 (2 * t + 1) (by rw [List.length_map]; exact h2t1_lt)
    rw [List.getElem_map] at h
    exact h
  have harr_ray_6 : s₆.arrs hitRayIdxArr = s.arrs hitRayIdxArr := by
    rw [harrs₆ hitRayIdxArr (by decide)]; rfl
  let s₇ := s₆.setReg 19 p₂.2.1
  have hex₇ : Exec w (.assign 19 (.read hitRayIdxArr (.const (2 * t + 1)))) s₆ s₇ 3 :=
    .assign (by simp [Expr.eval, checkWord, harr_ray_6, h2t1_w, hbuf2.1,
      show 2 * t + 1 < Q.length by omega, hget_ray2, hi2_ray_w])
  -- Step 8: copyArrByIdxSliceCmd hitPrefArr 19 tmpPathArr2 0 l
  have hpref₂_7 : s₇.arrs (hitPrefArr p₂.2.1) = A₂.map Fin.val := by
    simp only [s₇, State.setReg_arrs]
    rw [harrs₆ (hitPrefArr p₂.2.1) (by dsimp [hitPrefArr, tmpPathArr1, Arr]; omega)]
    exact hpref p₂.2
  rcases copyArrByIdxSliceCmd_exec hitPrefArr 19 tmpPathArr2
      (fun j _ => by dsimp [hitPrefArr, tmpPathArr2, Arr]; omega)
      (by decide) (by decide) (by decide) (by decide) p₂.2 hw1 hn_w hl_w l 0 (Nat.zero_add l)
      (s := s₇) (by simp [s₇])
      (by simp [hpref₂_7, hA₂_len])
      (fun v hv => by
        rw [hpref₂_7] at hv
        rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
    ⟨s₈, t₈, hex₈, ht₈, htmp2_8, hregs₈, harrs₈⟩
  rw [if_pos (Nat.zero_le _), hpref₂_7] at htmp2_8
  -- Step 9: suffixFromArrCmd qArr tmpPathArr3 22
  have hqArr₈ : s₈.arrs qArr = Q.map Fin.val := by
    rw [harrs₈ qArr hne_q2, show s₇.arrs qArr = s₆.arrs qArr from rfl,
      harrs₆ qArr hne_q1]
    exact hqArr
  have hr22_8 : s₈.regs 22 = z₁.1 := by
    rw [hregs₈ 22 (by decide) (by decide) (by decide) (by decide)]
    simp only [s₇, State.setReg_regs_ne _ _ (by decide : (22 : Reg) ≠ 19)]
    rw [hregs₆ 22 (by decide) (by decide) (by decide) (by decide)]
    simp [s₅, s₄, s₃]
  rcases suffixFromArrCmd_exec qArr tmpPathArr3 22 hne_q3
      (by decide) (by decide) (by decide) z₁ Q (s := s₈)
      hw1 hn_w hqArr₈ hQ_w hr22_8 with
    ⟨s₉, t₉, hex₉, ht₉, htmp3_9, hregs₉, harrs₉⟩
  -- Step 10: prefixUntilSingleArrCmd tmpPathArr3 bufArr 23
  let S₁ := suffixFrom z₁ Q
  have hS₁_len : S₁.length ≤ Q.length := length_suffixFrom_le z₁ Q
  have hr23_9 : s₉.regs 23 = z₂.1 := by
    rw [hregs₉ 23 (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs₈ 23 (by decide) (by decide) (by decide) (by decide)]
    simp only [s₇, State.setReg_regs_ne _ _ (by decide : (23 : Reg) ≠ 19)]
    rw [hregs₆ 23 (by decide) (by decide) (by decide) (by decide)]
    simp [s₅, s₄]
  rcases prefixUntilSingleArrCmd_exec tmpPathArr3 bufArr 23 (by decide)
      (by decide) (by decide) (by decide) (by decide) z₂ S₁ (s := s₉)
      hw1 hn_w htmp3_9 (by omega) hr23_9 with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hbuf_10, hregs₁₀, harrs₁₀⟩
  set B := WallOfHeight.subpathBetween Q z₁ z₂
  change s₁₀.arrs bufArr = B.map Fin.val at hbuf_10
  obtain ⟨hB_ne, hB_len⟩ : B ≠ [] ∧ B.length ≤ Q.length :=
    subpathBetween_ne_nil_and_length_le Q z₁ z₂ (List.getElem_mem hi₁)
  -- Step 11: concatOverlapArrCmd tmpPathArr1 bufArr tmpPathArr3
  have htmp1_10 : s₁₀.arrs tmpPathArr1 = A₁.map Fin.val := by
    rw [harrs₁₀ tmpPathArr1 (by decide), harrs₉ tmpPathArr1 (by decide),
      harrs₈ tmpPathArr1 (by decide)]
    exact htmp1_6
  rcases concatOverlapArrCmd_exec tmpPathArr1 bufArr tmpPathArr3 (by decide) (by decide)
      (s := s₁₀) hw1
      (by simp [htmp1_10, hA₁_ne])
      (by simp [htmp1_10, hbuf_10]; omega)
      (by simp [htmp1_10]; omega)
      (by simp [hbuf_10]; omega)
      (fun v hv => by rw [htmp1_10] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega)
      (fun v hv => by rw [hbuf_10] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, htmp3_11, hregs₁₁, harrs₁₁⟩
  rw [htmp1_10, hbuf_10, ← concatOverlap_map] at htmp3_11
  -- Step 12: reverseArrCmd tmpPathArr2 bufArr
  have htmp2_11 : s₁₁.arrs tmpPathArr2 = A₂.map Fin.val := by
    rw [harrs₁₁ tmpPathArr2 (by decide), harrs₁₀ tmpPathArr2 (by decide),
      harrs₉ tmpPathArr2 (by decide)]
    exact htmp2_8
  rcases reverseArrCmd_exec tmpPathArr2 bufArr (by decide) (s := s₁₁) hw1
      (by simp [htmp2_11]; omega)
      (fun v hv => by rw [htmp2_11] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
    ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hbuf_12, hregs₁₂, harrs₁₂⟩
  rw [htmp2_11, ← List.map_reverse] at hbuf_12
  -- Step 13: concatOverlapArrCmd tmpPathArr3 bufArr (rPathArr t)
  have htmp3_12 : s₁₂.arrs tmpPathArr3 = (concatOverlap A₁ B).map Fin.val := by
    rw [harrs₁₂ tmpPathArr3 (by decide), htmp3_11]
  have hAB_ne : concatOverlap A₁ B ≠ [] := List.append_ne_nil_of_right_ne_nil _ hB_ne
  have hAB_len : (concatOverlap A₁ B).length ≤ 2 * n := by
    simp only [concatOverlap, List.length_append, List.length_dropLast]
    omega
  rcases concatOverlapArrCmd_exec tmpPathArr3 bufArr (rPathArr t)
      (by dsimp [tmpPathArr3, rPathArr, Arr]; omega)
      (by dsimp [bufArr, rPathArr, Arr]; omega)
      (s := s₁₂) hw1
      (by simp [htmp3_12, hAB_ne])
      (by simp [htmp3_12, hbuf_12]; omega)
      (by simp [htmp3_12]; omega)
      (by simp [hbuf_12]; omega)
      (fun v hv => by rw [htmp3_12] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega)
      (fun v hv => by rw [hbuf_12] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
    ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hrPath_13, hregs₁₃, harrs₁₃⟩
  rw [htmp3_12, hbuf_12, ← concatOverlap_map] at hrPath_13
  change s₁₃.arrs (rPathArr t) =
    (WallOfHeight.joinRaysAlongSubpath Q (rays p₁.2) (rays p₂.2) z₁ z₂).map Fin.val at hrPath_13
  rw [← hbuild_eq] at hrPath_13
  simp only [htmp1_10, hbuf_10, htmp2_11, htmp3_12, hbuf_12, List.length_map,
    List.length_reverse] at ht₁₁ ht₁₂ ht₁₃
  have h2l : 2 * l * (22 * n + 16) = l * (22 * n + 16) + l * (22 * n + 16) := by ring
  refine ⟨s₁₃, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
      (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ hex₁₃))))))))))),
    by omega,
    hrPath_13,
    fun r h7 h8 h9 h10 h11 h17 h18 h19 h22 h23 => by
      rw [hregs₁₃ r h7 h8 h9 h10 h11, hregs₁₂ r h7 h9 h11,
        hregs₁₁ r h7 h8 h9 h10 h11, hregs₁₀ r h7 h8 h9 h10 h11,
        hregs₉ r h7 h8 h9 h10 h11, hregs₈ r h7 h8 h9 h11]
      simp only [s₇, State.setReg_regs_ne _ _ h19]
      rw [hregs₆ r h7 h8 h9 h11]
      simp [s₅, s₄, s₃, s₂, s₁, h17, h18, h19, h22, h23],
    fun arr ha1 ha2 ha3 habuf har => by
      rw [harrs₁₃ arr har, harrs₁₂ arr habuf, harrs₁₁ arr ha3,
        harrs₁₀ arr habuf, harrs₉ arr ha3, harrs₈ arr ha2]
      simp only [s₇, State.setReg_arrs]
      rw [harrs₆ arr ha1]
      rfl⟩

/-- Build `rPathArr t` for `t, t + 1, ..., t + rem - 1`. -/
def buildCaseAPathsSliceCmd (l : ℕ) (qArr : Arr) (t : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (buildOneCaseAPathCmd l t qArr)
      (buildCaseAPathsSliceCmd l qArr (t + 1) rem)

theorem buildCaseAPathsSliceCmd_exec {w n l k' : ℕ} (qArr : Arr)
    (hne_q1 : qArr ≠ tmpPathArr1) (hne_q2 : qArr ≠ tmpPathArr2)
    (hne_q3 : qArr ≠ tmpPathArr3) (hne_qbuf : qArr ≠ bufArr)
    (hne_qr : ∀ t < k', qArr ≠ rPathArr t)
    (Q : List (Fin n))
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (hneP : ∀ j : Fin l, rays j ≠ [])
    (hP_len : ∀ j : Fin l, (rays j).length ≤ n)
    (hQ_len : Q.length ≤ n)
    (hhits : 2 * k' ≤ (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length)
    (hw1 : 1 < 2 ^ w) (h3n_w : 3 * n < 2 ^ w) (hl_w : l < 2 ^ w) :
    ∀ (rem t : ℕ) (_hrem : t + rem = k') {s : State}
      (_hqArr : s.arrs qArr = Q.map Fin.val)
      (_hbuf1 : IsBufPrefix s hitIdxArr 20 Q.length ((hitsIdxOnQ rays act Q).map Prod.fst))
      (_hbuf2 : IsBufPrefix s hitRayIdxArr 21 Q.length ((hitsIdxOnQ rays act Q).map (fun p => p.2.1)))
      (_hpref : ∀ j : Fin l,
        s.arrs (hitPrefArr j.1) = (WallOfHeight.rayHitPrefix Q (rays j)).map Fin.val)
      (_hprev : ∀ t' (ht' : t' < t),
        have hlen_R : t' < (WallOfHeight.buildCaseAPaths k' (activeRayList rays act) Q).length := by
          rw [WallOfHeight.length_buildCaseAPaths]; omega
        s.arrs (rPathArr t') =
          ((WallOfHeight.buildCaseAPaths k' (activeRayList rays act) Q)[t']'hlen_R).map Fin.val),
      ∃ s' time,
        Exec w (buildCaseAPathsSliceCmd l qArr t rem) s s' time ∧
        time ≤ rem * (2 * l * (22 * n + 16) + 218 * n + 145) + 1 ∧
        (∀ t' (ht' : t' < k'),
          have hlen_R : t' < (WallOfHeight.buildCaseAPaths k' (activeRayList rays act) Q).length := by
            rw [WallOfHeight.length_buildCaseAPaths]; exact ht'
          s'.arrs (rPathArr t') =
            ((WallOfHeight.buildCaseAPaths k' (activeRayList rays act) Q)[t']'hlen_R).map Fin.val) ∧
        (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
          r ≠ 17 → r ≠ 18 → r ≠ 19 → r ≠ 22 → r ≠ 23 → s'.regs r = s.regs r) ∧
        (∀ arr : Arr, arr ≠ tmpPathArr1 → arr ≠ tmpPathArr2 → arr ≠ tmpPathArr3 →
          arr ≠ bufArr → (∀ t' < k', arr ≠ rPathArr t') → s'.arrs arr = s.arrs arr)
  | 0, t, hrem, s, _, _, _, _, hprev => by
    have ht : t = k' := by omega
    subst ht
    refine ⟨s, 1, .skip s, by omega, hprev,
      fun _ _ _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | rem + 1, t, hrem, s, hqArr, hbuf1, hbuf2, hpref, hprev => by
    have ht_lt : t < k' := by omega
    rcases buildOneCaseAPathCmd_exec qArr hne_q1 hne_q2 hne_q3 hne_qbuf (hne_qr t ht_lt)
        Q rays act hneP hP_len hQ_len ht_lt hhits hw1 h3n_w hl_w hqArr hbuf1 hbuf2 hpref with
      ⟨s₁, t₁, hex₁, ht₁, hr_t, hregs₁, harrs₁⟩
    have hqArr₁ : s₁.arrs qArr = Q.map Fin.val := by
      rw [harrs₁ qArr hne_q1 hne_q2 hne_q3 hne_qbuf (hne_qr t ht_lt), hqArr]
    have hbuf1_1 : IsBufPrefix s₁ hitIdxArr 20 Q.length ((hitsIdxOnQ rays act Q).map Prod.fst) :=
      hbuf1.of_preserve
        (harrs₁ hitIdxArr (by decide) (by decide) (by decide) (by decide)
          (by dsimp [hitIdxArr, rPathArr, Arr]; omega))
        (hregs₁ 20 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide))
    have hbuf2_1 : IsBufPrefix s₁ hitRayIdxArr 21 Q.length
        ((hitsIdxOnQ rays act Q).map (fun p => p.2.1)) :=
      hbuf2.of_preserve
        (harrs₁ hitRayIdxArr (by decide) (by decide) (by decide) (by decide)
          (by dsimp [hitRayIdxArr, rPathArr, Arr]; omega))
        (hregs₁ 21 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide))
    have hpref₁ : ∀ j : Fin l,
        s₁.arrs (hitPrefArr j.1) = (WallOfHeight.rayHitPrefix Q (rays j)).map Fin.val := by
      intro j
      rw [harrs₁ (hitPrefArr j.1)
        (by dsimp [hitPrefArr, tmpPathArr1, Arr]; omega)
        (by dsimp [hitPrefArr, tmpPathArr2, Arr]; omega)
        (by dsimp [hitPrefArr, tmpPathArr3, Arr]; omega)
        (by dsimp [hitPrefArr, bufArr, Arr]; omega)
        (by dsimp [hitPrefArr, rPathArr, Arr]; omega)]
      exact hpref j
    have hprev₁ : ∀ t' (ht' : t' < t + 1),
        have hlen_R : t' < (WallOfHeight.buildCaseAPaths k' (activeRayList rays act) Q).length := by
          rw [WallOfHeight.length_buildCaseAPaths]; omega
        s₁.arrs (rPathArr t') =
          ((WallOfHeight.buildCaseAPaths k' (activeRayList rays act) Q)[t']'hlen_R).map Fin.val := by
      intro t' ht'
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht') with hlt | rfl
      · rw [harrs₁ (rPathArr t')
          (by dsimp [rPathArr, tmpPathArr1, Arr]; omega)
          (by dsimp [rPathArr, tmpPathArr2, Arr]; omega)
          (by dsimp [rPathArr, tmpPathArr3, Arr]; omega)
          (by dsimp [rPathArr, bufArr, Arr]; omega)
          (by dsimp [rPathArr, Arr]; omega)]
        exact hprev t' hlt
      · exact hr_t
    rcases buildCaseAPathsSliceCmd_exec qArr hne_q1 hne_q2 hne_q3 hne_qbuf hne_qr
        Q rays act hneP hP_len hQ_len hhits hw1 h3n_w hl_w rem (t + 1) (by omega)
        hqArr₁ hbuf1_1 hbuf2_1 hpref₁ hprev₁ with
      ⟨s₂, t₂, hex₂, ht₂, hres₂, hregs₂, harrs₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by calc t₁ + t₂
          ≤ (2 * l * (22 * n + 16) + 218 * n + 145) +
            (rem * (2 * l * (22 * n + 16) + 218 * n + 145) + 1) := by omega
        _ = (rem + 1) * (2 * l * (22 * n + 16) + 218 * n + 145) + 1 := by ring,
      hres₂,
      fun r h7 h8 h9 h10 h11 h17 h18 h19 h22 h23 => by
        rw [hregs₂ r h7 h8 h9 h10 h11 h17 h18 h19 h22 h23,
          hregs₁ r h7 h8 h9 h10 h11 h17 h18 h19 h22 h23],
      fun arr ha1 ha2 ha3 habuf har => by
        rw [harrs₂ arr ha1 ha2 ha3 habuf har,
          harrs₁ arr ha1 ha2 ha3 habuf (har t ht_lt)]⟩

/-- Copy `rPathArr t` to `qPathArr t` for `t, t + 1, ..., t + rem - 1`. -/
def copyRPathsToQPathsSliceCmd (t : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (copyArrCmd (rPathArr t) (qPathArr t))
      (copyRPathsToQPathsSliceCmd (t + 1) rem)

theorem copyRPathsToQPathsSliceCmd_exec {w n k' : ℕ}
    (Rs : List (List (Fin n))) (hlenRs : Rs.length = k')
    (hR_len : ∀ R ∈ Rs, R.length ≤ n)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) :
    ∀ (rem t : ℕ) (_hrem : t + rem = k') {s : State}
      (_hr : ∀ t' (ht' : t' < k'),
        s.arrs (rPathArr t') = (Rs[t']'(by omega)).map Fin.val)
      (_hq : ∀ t' (ht' : t' < t),
        s.arrs (qPathArr t') = (Rs[t']'(by omega)).map Fin.val),
      ∃ s' time,
        Exec w (copyRPathsToQPathsSliceCmd t rem) s s' time ∧
        time ≤ rem * (22 * n + 10) + 1 ∧
        (∀ t' (ht' : t' < k'),
          s'.arrs (qPathArr t') = (Rs[t']'(by omega)).map Fin.val) ∧
        (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ arr : Arr, (∀ t' < k', arr ≠ qPathArr t') → s'.arrs arr = s.arrs arr)
  | 0, t, hrem, s, _, hq => by
    have ht : t = k' := by omega
    subst ht
    refine ⟨s, 1, .skip s, by omega, hq, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | rem + 1, t, hrem, s, hr, hq => by
    have ht_lt : t < k' := by omega
    have ht_Rs : t < Rs.length := by omega
    have hlen_t : (Rs[t]'ht_Rs).length ≤ n := hR_len _ (List.getElem_mem ht_Rs)
    have hrt : s.arrs (rPathArr t) = (Rs[t]'ht_Rs).map Fin.val := hr t ht_lt
    rcases copyArrCmd_exec (rPathArr t) (qPathArr t)
        (by dsimp [rPathArr, qPathArr, Arr]; omega) (s := s) hw1
        (by simp [hrt]; omega)
        (fun v hv => by rw [hrt] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
      ⟨s₁, t₁, hex₁, ht₁, hdst₁, hregs₁, harrs₁⟩
    rw [hrt] at hdst₁ ht₁
    simp only [List.length_map] at ht₁
    have hr₁ : ∀ t' (ht' : t' < k'),
        s₁.arrs (rPathArr t') = (Rs[t']'(by omega)).map Fin.val := by
      intro t' ht'
      rw [harrs₁ (rPathArr t') (by dsimp [rPathArr, qPathArr, Arr]; omega)]
      exact hr t' ht'
    have hq₁ : ∀ t' (ht' : t' < t + 1),
        s₁.arrs (qPathArr t') = (Rs[t']'(by omega)).map Fin.val := by
      intro t' ht'
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht') with hlt | rfl
      · rw [harrs₁ (qPathArr t') (by dsimp [qPathArr, Arr]; omega)]
        exact hq t' hlt
      · exact hdst₁
    rcases copyRPathsToQPathsSliceCmd_exec Rs hlenRs hR_len hw1 hn_w rem (t + 1) (by omega)
        hr₁ hq₁ with
      ⟨s₂, t₂, hex₂, ht₂, hres₂, hregs₂, harrs₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by calc t₁ + t₂
          ≤ (22 * n + 10) + (rem * (22 * n + 10) + 1) := by omega
        _ = (rem + 1) * (22 * n + 10) + 1 := by ring,
      hres₂,
      fun r h7 h8 h9 h11 => by rw [hregs₂ r h7 h8 h9 h11, hregs₁ r h7 h8 h9 h11],
      fun arr ha => by rw [harrs₂ arr ha, harrs₁ arr (ha t ht_lt)]⟩

/-- Build all `k'` Case A replacement `H`-paths and store them into `qPathArr 0 .. qPathArr (k' - 1)`. -/
def buildCaseAPathsCmd (l k' : ℕ) (qArr : Arr) : Cmd :=
  .seq (buildCaseAPathsSliceCmd l qArr 0 k')
    (copyRPathsToQPathsSliceCmd 0 k')

theorem buildCaseAPathsCmd_exec {w h n l k' r : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (qArr : Arr)
    (hne_q1 : qArr ≠ tmpPathArr1) (hne_q2 : qArr ≠ tmpPathArr2)
    (hne_q3 : qArr ≠ tmpPathArr3) (hne_qbuf : qArr ≠ bufArr)
    (hne_qr : ∀ t < k', qArr ≠ rPathArr t)
    {c : Fin n} (Q : List (Fin n))
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (hrs : W.IsStarRayList (2 * r) c (activeRayList rays act))
    (hQ : W.IsHPath Q) (hcQ : c ∉ Q)
    (hneP : ∀ j : Fin l, rays j ≠ [])
    (hP_len : ∀ j : Fin l, (rays j).length ≤ n)
    (hhits : 2 * k' ≤ (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length)
    {s : State}
    (hw1 : 1 < 2 ^ w) (h3n_w : 3 * n < 2 ^ w) (hl_w : l < 2 ^ w)
    (hqArr : s.arrs qArr = Q.map Fin.val)
    (hbuf1 : IsBufPrefix s hitIdxArr 20 Q.length ((hitsIdxOnQ rays act Q).map Prod.fst))
    (hbuf2 : IsBufPrefix s hitRayIdxArr 21 Q.length ((hitsIdxOnQ rays act Q).map (fun p => p.2.1)))
    (hpref : ∀ j : Fin l,
      s.arrs (hitPrefArr j.1) = (WallOfHeight.rayHitPrefix Q (rays j)).map Fin.val) :
    let Rs := WallOfHeight.buildCaseAPaths k' (activeRayList rays act) Q
    have hlenRs : Rs.length = k' := WallOfHeight.length_buildCaseAPaths k' _ Q
    ∃ s' time,
      Exec w (buildCaseAPathsCmd l k' qArr) s s' time ∧
      time ≤ k' * (2 * l * (22 * n + 16) + 240 * n + 155) + 2 ∧
      (∀ t (ht : t < k'),
        s'.arrs (qPathArr t) = (Rs[t]'(by rw [hlenRs]; exact ht)).map Fin.val) ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 17 → r ≠ 18 → r ≠ 19 → r ≠ 22 → r ≠ 23 → s'.regs r = s.regs r) ∧
      (∀ arr : Arr, arr ≠ tmpPathArr1 → arr ≠ tmpPathArr2 → arr ≠ tmpPathArr3 →
        arr ≠ bufArr → (∀ t < k', arr ≠ rPathArr t) → (∀ t < k', arr ≠ qPathArr t) →
        s'.arrs arr = s.arrs arr) := by
  intro Rs hlenRs
  have hn_w : n < 2 ^ w := by omega
  have hQ_len : Q.length ≤ n := length_le_of_nodup_fin hQ.choose_spec.2.1
  obtain ⟨_, hfarRs, _⟩ := W.buildCaseAPaths_spec h2 he hW hrs hQ hcQ hhits
  have hR_len : ∀ R ∈ Rs, R.length ≤ n :=
    fun R hR => length_le_of_nodup_fin (hfarRs.paths_valid R hR).choose_spec.2.1
  rcases buildCaseAPathsSliceCmd_exec qArr hne_q1 hne_q2 hne_q3 hne_qbuf hne_qr
      Q rays act hneP hP_len hQ_len hhits hw1 h3n_w hl_w k' 0 (Nat.zero_add k')
      hqArr hbuf1 hbuf2 hpref (fun _ ht => False.elim (Nat.not_lt_zero _ ht)) with
    ⟨s₁, t₁, hex₁, ht₁, hr₁, hregs₁, harrs₁⟩
  rcases copyRPathsToQPathsSliceCmd_exec Rs hlenRs hR_len hw1 hn_w k' 0 (Nat.zero_add k')
      hr₁ (fun _ ht => False.elim (Nat.not_lt_zero _ ht)) with
    ⟨s₂, t₂, hex₂, ht₂, hq₂, hregs₂, harrs₂⟩
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
    by calc t₁ + t₂
        ≤ (k' * (2 * l * (22 * n + 16) + 218 * n + 145) + 1) +
          (k' * (22 * n + 10) + 1) := by omega
      _ = k' * (2 * l * (22 * n + 16) + 240 * n + 155) + 2 := by ring,
    hq₂,
    fun r h7 h8 h9 h10 h11 h17 h18 h19 h22 h23 => by
      rw [hregs₂ r h7 h8 h9 h11, hregs₁ r h7 h8 h9 h10 h11 h17 h18 h19 h22 h23],
    fun arr ha1 ha2 ha3 habuf har haq => by
      rw [harrs₂ arr haq, harrs₁ arr ha1 ha2 ha3 habuf har]⟩

/-! ### Section 2: Pure `ℕ` Brick Distance Command and Case B -/

/-- Expression for `x = if sx = 0 then cx / 2 else (cx - 1) / 2`. -/
def exprCornerX (sx : ℕ) (rCX : Reg) : Expr :=
  if sx = 0 then
    .op .div (.reg rCX) (.const 2)
  else
    .op .div (.op .sub (.reg rCX) (.const 1)) (.const 2)

/-- Expression for `y = if sy = 0 then cy / 2 else (cy - 1) / 2`. -/
def exprCornerY (sy : ℕ) (rCY : Reg) : Expr :=
  if sy = 0 then
    .op .div (.reg rCY) (.const 2)
  else
    .op .div (.op .sub (.reg rCY) (.const 1)) (.const 2)

/-- Expression for `X = x + (x + y) % 2`. -/
def exprCornerBigX (sx sy : ℕ) (rCX rCY : Reg) : Expr :=
  let ex := exprCornerX sx rCX
  let ey := exprCornerY sy rCY
  .op .add ex (.op .mod (.op .add ex ey) (.const 2))

/-- Expression for `if natCornerIsBrick h cx cy sx sy then 1 else 0`. -/
def exprCornerIsBrick (sx sy : ℕ) (rH rCX rCY : Reg) : Expr :=
  let eX := exprCornerBigX sx sy rCX rCY
  let eY := exprCornerY sy rCY
  let condX := if sx = 0 then Expr.const 1 else .op .lt (.const 0) (.reg rCX)
  let condY := if sy = 0 then Expr.const 1 else .op .lt (.const 0) (.reg rCY)
  exprAnd condX
    (exprAnd condY
      (exprAnd (.op .lt eY (.reg rH))
        (exprAnd (exprLe (.const 1) eX) (exprLe eX (.op .mul (.const 2) (.reg rH))))))

/-- Expression for `natOutDepth h X Y`. -/
def exprNatOutDepth (rH : Reg) (eX eY : Expr) : Expr :=
  exprMin
    (exprMin (.op .add eY (.const 1)) (.op .sub (.reg rH) eY))
    (exprMin (.op .div (.op .add eX (.const 1)) (.const 2))
      (.op .div (.op .sub (.op .add (.op .mul (.const 2) (.reg rH)) (.const 2)) eX) (.const 2)))

/-- Expression for `natHexDist X₁ Y₁ X₂ Y₂`. -/
def exprNatHexDist (eX1 eY1 eX2 eY2 : Expr) : Expr :=
  let dX := exprAbsDiff eX1 eX2
  let dY := exprAbsDiff eY1 eY2
  exprMax dY (.op .div (.op .add dX dY) (.const 2))

/-- Expression for `natCornerFaceDist h cx₁ cy₁ sx₁ sy₁ cx₂ cy₂ sx₂ sy₂`. -/
def exprNatCornerFaceDist (sx₁ sy₁ sx₂ sy₂ : ℕ) (rH rCX₁ rCY₁ rCX₂ rCY₂ : Reg) : Expr :=
  let eX1 := exprCornerBigX sx₁ sy₁ rCX₁ rCY₁
  let eY1 := exprCornerY sy₁ rCY₁
  let eb1 := exprCornerIsBrick sx₁ sy₁ rH rCX₁ rCY₁
  let eX2 := exprCornerBigX sx₂ sy₂ rCX₂ rCY₂
  let eY2 := exprCornerY sy₂ rCY₂
  let eb2 := exprCornerIsBrick sx₂ sy₂ rH rCX₂ rCY₂
  let od1 := exprNatOutDepth rH eX1 eY1
  let od2 := exprNatOutDepth rH eX2 eY2
  exprIte (exprNot eb1)
    (exprIte (exprNot eb2) (.const 0) od2)
    (exprIte (exprNot eb2) od1
      (exprMin (exprNatHexDist eX1 eY1 eX2 eY2) (.op .add od1 od2)))

theorem eval_exprCornerXY {w : ℕ} {s : State} {sx sy : ℕ} {rH rCX rCY : Reg} {h cx cy : ℕ}
    (hw2 : 2 < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w)
    (hcx : cx ≤ 4 * h + 2) (hcy : cy ≤ 2 * h)
    (hrH : s.regs rH = h) (hrCX : s.regs rCX = cx) (hrCY : s.regs rCY = cy) :
    let x := if sx = 0 then cx / 2 else (cx - 1) / 2
    let y := if sy = 0 then cy / 2 else (cy - 1) / 2
    let X := x + (x + y) % 2
    (exprCornerX sx rCX).eval w s = some x ∧
    (exprCornerY sy rCY).eval w s = some y ∧
    (exprCornerBigX sx sy rCX rCY).eval w s = some X ∧
    (exprCornerIsBrick sx sy rH rCX rCY).eval w s =
      some (if natCornerIsBrick h cx cy sx sy then 1 else 0) ∧
    (exprNatOutDepth rH (exprCornerBigX sx sy rCX rCY) (exprCornerY sy rCY)).eval w s =
      some (natOutDepth h X y) := by
  intro x y X
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hh_w : h < 2 ^ w := by omega
  have h2h_w : 2 * h < 2 ^ w := by omega
  have h2h2_w : 2 * h + 2 < 2 ^ w := by omega
  have hcx_w : cx < 2 ^ w := by omega
  have hcy_w : cy < 2 ^ w := by omega
  have hx_le : x ≤ 2 * h + 1 := by dsimp [x]; split_ifs <;> omega
  have hy_le : y ≤ h := by dsimp [y]; split_ifs <;> omega
  have hX_le : X ≤ 2 * h + 2 := by dsimp [X]; omega
  have hxy_w : x + y < 2 ^ w := by omega
  have hX_w : X < 2 ^ w := by omega
  have hex : (exprCornerX sx rCX).eval w s = some x := by
    unfold exprCornerX
    have heCX : (Expr.reg rCX).eval w s = some cx := by simp [Expr.eval, checkWord, hrCX, hcx_w]
    have he2 : (Expr.const 2).eval w s = some 2 := eval_const s hw2
    split_ifs with hsx
    · simpa [x, hsx] using eval_op_div heCX he2 (by omega)
    · simpa [x, hsx] using eval_op_div (eval_op_sub heCX (eval_const s h1_w)) he2 (by omega)
  have hey : (exprCornerY sy rCY).eval w s = some y := by
    unfold exprCornerY
    have heCY : (Expr.reg rCY).eval w s = some cy := by simp [Expr.eval, checkWord, hrCY, hcy_w]
    have he2 : (Expr.const 2).eval w s = some 2 := eval_const s hw2
    split_ifs with hsy
    · simpa [y, hsy] using eval_op_div heCY he2 (by omega)
    · simpa [y, hsy] using eval_op_div (eval_op_sub heCY (eval_const s h1_w)) he2 (by omega)
  have heX : (exprCornerBigX sx sy rCX rCY).eval w s = some X := by
    unfold exprCornerBigX
    have hsum : (Expr.op .add (exprCornerX sx rCX) (exprCornerY sy rCY)).eval w s = some (x + y) :=
      eval_op_add hex hey hxy_w
    have hmod : (Expr.op .mod (.op .add (exprCornerX sx rCX) (exprCornerY sy rCY)) (.const 2)).eval w s =
        some ((x + y) % 2) :=
      eval_op_mod hsum (by simp [Expr.eval, checkWord, hw2]) (by omega)
    exact eval_op_add hex hmod hX_w
  have heH : (Expr.reg rH).eval w s = some h := by
    simp [Expr.eval, checkWord, hrH, hh_w]
  have he2H : (Expr.op .mul (.const 2) (.reg rH)).eval w s = some (2 * h) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrH, hh_w, hw2, h2h_w]
  have hcondX : (if sx = 0 then Expr.const 1 else .op .lt (.const 0) (.reg rCX)).eval w s =
      some (if decide (sx = 0 ∨ 0 < cx) then 1 else 0) := by
    by_cases hsx : sx = 0
    · simp [hsx, checkWord, h1_w]
    · rw [if_neg hsx]
      simpa [exprLt, hsx] using eval_exprLt h1_w (eval_const s h0_w)
        (by simp [Expr.eval, checkWord, hrCX, hcx_w])
  have hcondY : (if sy = 0 then Expr.const 1 else .op .lt (.const 0) (.reg rCY)).eval w s =
      some (if decide (sy = 0 ∨ 0 < cy) then 1 else 0) := by
    by_cases hsy : sy = 0
    · simp [hsy, checkWord, h1_w]
    · rw [if_neg hsy]
      simpa [exprLt, hsy] using eval_exprLt h1_w (eval_const s h0_w)
        (by simp [Expr.eval, checkWord, hrCY, hcy_w])
  have hlt_yH : (Expr.op .lt (exprCornerY sy rCY) (.reg rH)).eval w s =
      some (if decide (y < h) then 1 else 0) := by
    simpa [exprLt] using eval_exprLt h1_w hey heH
  have hle_1X : (exprLe (.const 1) (exprCornerBigX sx sy rCX rCY)).eval w s =
      some (if decide (1 ≤ X) then 1 else 0) := by
    simpa using eval_exprLe h1_w (by simp [Expr.eval, checkWord, h1_w]) heX
  have hle_X2H : (exprLe (exprCornerBigX sx sy rCX rCY) (.op .mul (.const 2) (.reg rH))).eval w s =
      some (if decide (X ≤ 2 * h) then 1 else 0) := by
    simpa using eval_exprLe h1_w heX he2H
  have heb : (exprCornerIsBrick sx sy rH rCX rCY).eval w s =
      some (if natCornerIsBrick h cx cy sx sy then 1 else 0) := by
    unfold exprCornerIsBrick natCornerIsBrick
    rw [eval_exprAnd_bool h1_w hcondX
      (eval_exprAnd_bool h1_w hcondY
        (eval_exprAnd_bool h1_w hlt_yH (eval_exprAnd_bool h1_w hle_1X hle_X2H)))]
    congr 2
  have hod : (exprNatOutDepth rH (exprCornerBigX sx sy rCX rCY) (exprCornerY sy rCY)).eval w s =
      some (natOutDepth h X y) := by
    unfold exprNatOutDepth natOutDepth
    have hy1 : (Expr.op .add (exprCornerY sy rCY) (.const 1)).eval w s = some (y + 1) :=
      eval_op_add hey (by simp [Expr.eval, checkWord, h1_w]) (by omega)
    have hhy : (Expr.op .sub (.reg rH) (exprCornerY sy rCY)).eval w s = some (h - y) :=
      eval_op_sub heH hey
    have hX1 : (Expr.op .add (exprCornerBigX sx sy rCX rCY) (.const 1)).eval w s = some (X + 1) :=
      eval_op_add heX (by simp [Expr.eval, checkWord, h1_w]) (by omega)
    have hX1_div : (Expr.op .div (.op .add (exprCornerBigX sx sy rCX rCY) (.const 1)) (.const 2)).eval w s =
        some ((X + 1) / 2) :=
      eval_op_div hX1 (by simp [Expr.eval, checkWord, hw2]) (by omega)
    have h2H2 : (Expr.op .add (.op .mul (.const 2) (.reg rH)) (.const 2)).eval w s =
        some (2 * h + 2) :=
      eval_op_add he2H (by simp [Expr.eval, checkWord, hw2]) h2h2_w
    have hsubX : (Expr.op .sub (.op .add (.op .mul (.const 2) (.reg rH)) (.const 2))
        (exprCornerBigX sx sy rCX rCY)).eval w s = some (2 * h + 2 - X) :=
      eval_op_sub h2H2 heX
    have hsubX_div : (Expr.op .div (.op .sub (.op .add (.op .mul (.const 2) (.reg rH)) (.const 2))
        (exprCornerBigX sx sy rCX rCY)) (.const 2)).eval w s = some ((2 * h + 2 - X) / 2) :=
      eval_op_div hsubX (by simp [Expr.eval, checkWord, hw2]) (by omega)
    exact eval_exprMin h1_w (eval_exprMin h1_w hy1 hhy) (eval_exprMin h1_w hX1_div hsubX_div)
  exact ⟨hex, hey, heX, heb, hod⟩

theorem absDiff_eq_ite (a b : ℕ) :
    (a - b) + (b - a) = if a ≤ b then b - a else a - b := by
  split_ifs <;> omega

theorem eval_exprNatCornerFaceDist {w : ℕ} {s : State}
    (sx₁ sy₁ sx₂ sy₂ : ℕ) (rH rCX₁ rCY₁ rCX₂ rCY₂ : Reg)
    {h cx₁ cy₁ cx₂ cy₂ : ℕ}
    (hw2 : 2 < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w)
    (hcx₁ : cx₁ ≤ 4 * h + 2) (hcy₁ : cy₁ ≤ 2 * h)
    (hcx₂ : cx₂ ≤ 4 * h + 2) (hcy₂ : cy₂ ≤ 2 * h)
    (hrH : s.regs rH = h)
    (hrCX₁ : s.regs rCX₁ = cx₁) (hrCY₁ : s.regs rCY₁ = cy₁)
    (hrCX₂ : s.regs rCX₂ = cx₂) (hrCY₂ : s.regs rCY₂ = cy₂) :
    (exprNatCornerFaceDist sx₁ sy₁ sx₂ sy₂ rH rCX₁ rCY₁ rCX₂ rCY₂).eval w s =
      some (natCornerFaceDist h cx₁ cy₁ sx₁ sy₁ cx₂ cy₂ sx₂ sy₂) ∧
    natCornerFaceDist h cx₁ cy₁ sx₁ sy₁ cx₂ cy₂ sx₂ sy₂ ≤ 2 * h + 2 := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  obtain ⟨_, hey₁, heX₁, heb₁, hod₁⟩ :=
    eval_exprCornerXY (sx := sx₁) (sy := sy₁) hw2 h4h4_w hcx₁ hcy₁ hrH hrCX₁ hrCY₁
  obtain ⟨_, hey₂, heX₂, heb₂, hod₂⟩ :=
    eval_exprCornerXY (sx := sx₂) (sy := sy₂) hw2 h4h4_w hcx₂ hcy₂ hrH hrCX₂ hrCY₂
  set x₁ := if sx₁ = 0 then cx₁ / 2 else (cx₁ - 1) / 2
  set y₁ := if sy₁ = 0 then cy₁ / 2 else (cy₁ - 1) / 2
  set X₁ := x₁ + (x₁ + y₁) % 2
  set x₂ := if sx₂ = 0 then cx₂ / 2 else (cx₂ - 1) / 2
  set y₂ := if sy₂ = 0 then cy₂ / 2 else (cy₂ - 1) / 2
  set X₂ := x₂ + (x₂ + y₂) % 2
  have hx₁_le : x₁ ≤ 2 * h + 1 := by dsimp [x₁]; split_ifs <;> omega
  have hy₁_le : y₁ ≤ h := by dsimp [y₁]; split_ifs <;> omega
  have hX₁_le : X₁ ≤ 2 * h + 2 := by dsimp [X₁]; omega
  have hx₂_le : x₂ ≤ 2 * h + 1 := by dsimp [x₂]; split_ifs <;> omega
  have hy₂_le : y₂ ≤ h := by dsimp [y₂]; split_ifs <;> omega
  have hX₂_le : X₂ ≤ 2 * h + 2 := by dsimp [X₂]; omega
  have hod₁_le : natOutDepth h X₁ y₁ ≤ h + 1 := by
    unfold natOutDepth
    have : min (y₁ + 1) (h - y₁) ≤ y₁ + 1 := Nat.min_le_left _ _
    have : min (min (y₁ + 1) (h - y₁)) (min ((X₁ + 1) / 2) ((2 * h + 2 - X₁) / 2)) ≤
        min (y₁ + 1) (h - y₁) := Nat.min_le_left _ _
    omega
  have hod₂_le : natOutDepth h X₂ y₂ ≤ h + 1 := by
    unfold natOutDepth
    have : min (y₂ + 1) (h - y₂) ≤ y₂ + 1 := Nat.min_le_left _ _
    have : min (min (y₂ + 1) (h - y₂)) (min ((X₂ + 1) / 2) ((2 * h + 2 - X₂) / 2)) ≤
        min (y₂ + 1) (h - y₂) := Nat.min_le_left _ _
    omega
  have hdX : (exprAbsDiff (exprCornerBigX sx₁ sy₁ rCX₁ rCY₁)
      (exprCornerBigX sx₂ sy₂ rCX₂ rCY₂)).eval w s =
      some (if X₁ ≤ X₂ then X₂ - X₁ else X₁ - X₂) := by
    rw [← absDiff_eq_ite X₁ X₂]
    exact eval_exprAbsDiff heX₁ heX₂
  have hdY : (exprAbsDiff (exprCornerY sy₁ rCY₁) (exprCornerY sy₂ rCY₂)).eval w s =
      some (if y₁ ≤ y₂ then y₂ - y₁ else y₁ - y₂) := by
    rw [← absDiff_eq_ite y₁ y₂]
    exact eval_exprAbsDiff hey₁ hey₂
  have hhex : (exprNatHexDist (exprCornerBigX sx₁ sy₁ rCX₁ rCY₁) (exprCornerY sy₁ rCY₁)
      (exprCornerBigX sx₂ sy₂ rCX₂ rCY₂) (exprCornerY sy₂ rCY₂)).eval w s =
      some (natHexDist X₁ y₁ X₂ y₂) := by
    unfold exprNatHexDist natHexDist
    let dX_val := if X₁ ≤ X₂ then X₂ - X₁ else X₁ - X₂
    let dY_val := if y₁ ≤ y₂ then y₂ - y₁ else y₁ - y₂
    have hdX_le : dX_val ≤ 2 * h + 2 := by dsimp [dX_val]; split_ifs <;> omega
    have hdY_le : dY_val ≤ h := by dsimp [dY_val]; split_ifs <;> omega
    have hsum_d : (Expr.op .add
        (exprAbsDiff (exprCornerBigX sx₁ sy₁ rCX₁ rCY₁) (exprCornerBigX sx₂ sy₂ rCX₂ rCY₂))
        (exprAbsDiff (exprCornerY sy₁ rCY₁) (exprCornerY sy₂ rCY₂))).eval w s =
        some (dX_val + dY_val) :=
      eval_op_add hdX hdY (by omega)
    have hdiv_d : (Expr.op .div (.op .add
        (exprAbsDiff (exprCornerBigX sx₁ sy₁ rCX₁ rCY₁) (exprCornerBigX sx₂ sy₂ rCX₂ rCY₂))
        (exprAbsDiff (exprCornerY sy₁ rCY₁) (exprCornerY sy₂ rCY₂))) (.const 2)).eval w s =
        some ((dX_val + dY_val) / 2) := by
      have hdiv_w : (dX_val + dY_val) / 2 < 2 ^ w := by omega
      unfold Expr.eval
      rw [hsum_d]
      simp [BinOp.eval, BinOp.raw, checkWord, hw2, hdiv_w]
    exact eval_exprMax h1_w hdY hdiv_d
  have hnot_b1 : (exprNot (exprCornerIsBrick sx₁ sy₁ rH rCX₁ rCY₁)).eval w s =
      some (if !natCornerIsBrick h cx₁ cy₁ sx₁ sy₁ then 1 else 0) :=
    eval_exprNot_bool h1_w heb₁
  have hnot_b2 : (exprNot (exprCornerIsBrick sx₂ sy₂ rH rCX₂ rCY₂)).eval w s =
      some (if !natCornerIsBrick h cx₂ cy₂ sx₂ sy₂ then 1 else 0) :=
    eval_exprNot_bool h1_w heb₂
  have hadd_od : (Expr.op .add
      (exprNatOutDepth rH (exprCornerBigX sx₁ sy₁ rCX₁ rCY₁) (exprCornerY sy₁ rCY₁))
      (exprNatOutDepth rH (exprCornerBigX sx₂ sy₂ rCX₂ rCY₂) (exprCornerY sy₂ rCY₂))).eval w s =
      some (natOutDepth h X₁ y₁ + natOutDepth h X₂ y₂) :=
    eval_op_add hod₁ hod₂ (by omega)
  have hmin_both := eval_exprMin h1_w hhex hadd_od
  have h0_eval : (Expr.const 0).eval w s = some 0 := eval_const s h0_w
  have hite_b2_0 := eval_exprIte h1_w hnot_b2 h0_eval hod₂
  have hite_b2_1 := eval_exprIte h1_w hnot_b2 hod₁ hmin_both
  have hite_top := eval_exprIte h1_w hnot_b1 hite_b2_0 hite_b2_1
  refine ⟨?_, ?_⟩
  · unfold exprNatCornerFaceDist natCornerFaceDist
    simpa [x₁, y₁, X₁, x₂, y₂, X₂] using hite_top
  · unfold natCornerFaceDist
    dsimp only
    change (if !natCornerIsBrick h cx₁ cy₁ sx₁ sy₁ then
        if !natCornerIsBrick h cx₂ cy₂ sx₂ sy₂ then 0 else natOutDepth h X₂ y₂
      else if !natCornerIsBrick h cx₂ cy₂ sx₂ sy₂ then
        natOutDepth h X₁ y₁
      else min (natHexDist X₁ y₁ X₂ y₂) (natOutDepth h X₁ y₁ + natOutDepth h X₂ y₂)) ≤ 2 * h + 2
    have hmin_le : min (natHexDist X₁ y₁ X₂ y₂) (natOutDepth h X₁ y₁ + natOutDepth h X₂ y₂) ≤
        natOutDepth h X₁ y₁ + natOutDepth h X₂ y₂ := Nat.min_le_right _ _
    split_ifs <;> omega

/-- Fold `min` into `r_16` over a list of elements mapped by `f : α → Expr`, using `r_15` as scratch. -/
def foldMinMapCmd {α : Type*} (f : α → Expr) : List α → Cmd
  | [] => .skip
  | x :: xs =>
    .seq (.assign 15 (f x))
      (.seq (.assign 16 (exprMin (.reg 16) (.reg 15)))
        (foldMinMapCmd f xs))

theorem foldMinMapCmd_exec {α : Type*} {w C : ℕ} (f : α → Expr) (g : α → ℕ)
    (hc : ∀ x, (f x).cost ≤ C)
    (hw1 : 1 < 2 ^ w) :
    ∀ (xs : List α) (acc : ℕ) {s : State}
      (_hacc_w : acc < 2 ^ w)
      (_hr16 : s.regs 16 = acc)
      (_heval : ∀ x ∈ xs, ∀ s' : State,
        (∀ r : Reg, r ≠ 15 → r ≠ 16 → s'.regs r = s.regs r) →
        (f x).eval w s' = some (g x) ∧ g x < 2 ^ w),
      ∃ s' t,
        Exec w (foldMinMapCmd f xs) s s' t ∧
        t ≤ xs.length * (C + 30) + 1 ∧
        s'.regs 16 = (xs.map g).foldl min acc ∧
        (∀ r : Reg, r ≠ 15 → r ≠ 16 → s'.regs r = s.regs r) ∧
        s'.arrs = s.arrs
  | [], acc, s, _, hr16, _ =>
    ⟨s, 1, .skip s, by omega, hr16, fun _ _ _ => rfl, rfl⟩
  | x :: xs, acc, s, hacc_w, hr16, heval => by
    obtain ⟨heval_x, hgx_w⟩ := heval x List.mem_cons_self s (fun _ _ _ => rfl)
    let s₁ := s.setReg 15 (g x)
    have hex₁ : Exec w (.assign 15 (f x)) s s₁ ((f x).cost + 1) := .assign heval_x
    have hr16_1 : (Expr.reg 16).eval w s₁ = some acc := by
      simp [Expr.eval, checkWord, s₁, hr16, hacc_w]
    have hr15_1 : (Expr.reg 15).eval w s₁ = some (g x) := by
      simp [Expr.eval, checkWord, s₁, hgx_w]
    let s₂ := s₁.setReg 16 (min acc (g x))
    have hex₂ : Exec w (.assign 16 (exprMin (.reg 16) (.reg 15))) s₁ s₂ _ :=
      .assign (eval_exprMin hw1 hr16_1 hr15_1)
    have hc2 : (exprMin (.reg 16) (.reg 15)).cost + 1 ≤ 28 := by decide
    have hmin_w : min acc (g x) < 2 ^ w := by
      have : min acc (g x) ≤ acc := Nat.min_le_left _ _
      omega
    rcases foldMinMapCmd_exec f g hc hw1 xs (min acc (g x)) (s := s₂)
        hmin_w (by simp [s₂])
        (fun y hy s' hs' => heval y (List.mem_cons_of_mem x hy) s' (fun r h15 h16 => by
          rw [hs' r h15 h16]; simp [s₂, s₁, h15, h16])) with
      ⟨s₃, t₃, hex₃, ht₃, hr16_3, hregs₃, harrs₃⟩
    have hcost_x : (f x).cost ≤ C := hc x
    refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃),
      by simp only [List.length_cons]
         calc ((f x).cost + 1) + (((exprMin (.reg 16) (.reg 15)).cost + 1) + t₃)
             ≤ (C + 30) + (xs.length * (C + 30) + 1) := by omega
           _ = (xs.length + 1) * (C + 30) + 1 := by ring,
      hr16_3,
      fun r h15 h16 => by rw [hregs₃ r h15 h16]; simp [s₂, s₁, h15, h16],
      by rw [harrs₃]; rfl⟩

/-- Compute `listMinNat (xs.map g)` into `r_16` using `r_15` as scratch. -/
def listMinMapCmd {α : Type*} (f : α → Expr) : List α → Cmd
  | [] => .assign 16 (.const 0)
  | x :: xs => .seq (.assign 16 (f x)) (foldMinMapCmd f xs)

theorem listMinMapCmd_exec {α : Type*} {w C : ℕ} (f : α → Expr) (g : α → ℕ)
    (hc : ∀ x, (f x).cost ≤ C)
    (hw1 : 1 < 2 ^ w) (xs : List α) {s : State}
    (heval : ∀ x ∈ xs, ∀ s' : State,
      (∀ r : Reg, r ≠ 15 → r ≠ 16 → s'.regs r = s.regs r) →
      (f x).eval w s' = some (g x) ∧ g x < 2 ^ w) :
    ∃ s' t,
      Exec w (listMinMapCmd f xs) s s' t ∧
      t ≤ xs.length * (C + 30) + 2 ∧
      s'.regs 16 = listMinNat (xs.map g) ∧
      (∀ r : Reg, r ≠ 15 → r ≠ 16 → s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs := by
  have h0_w : 0 < 2 ^ w := by omega
  cases xs with
  | nil =>
    let s₁ := s.setReg 16 0
    have hex₁ : Exec w (.assign 16 (.const 0)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    exact ⟨s₁, 2, hex₁, by omega, by simp [s₁, listMinNat],
      fun r _ h16 => by simp [s₁, h16], rfl⟩
  | cons x xs =>
    obtain ⟨heval_x, hgx_w⟩ := heval x List.mem_cons_self s (fun _ _ _ => rfl)
    let s₁ := s.setReg 16 (g x)
    have hex₁ : Exec w (.assign 16 (f x)) s s₁ ((f x).cost + 1) := .assign heval_x
    rcases foldMinMapCmd_exec f g hc hw1 xs (g x) (s := s₁) hgx_w (by simp [s₁])
        (fun y hy s' hs' => heval y (List.mem_cons_of_mem x hy) s' (fun r h15 h16 => by
          rw [hs' r h15 h16]; simp [s₁, h16])) with
      ⟨s₂, t₂, hex₂, ht₂, hr16_2, hregs₂, harrs₂⟩
    have hcost_x : (f x).cost ≤ C := hc x
    refine ⟨s₂, ((f x).cost + 1) + t₂, .seq hex₁ hex₂,
      by simp only [List.length_cons]
         calc ((f x).cost + 1) + t₂
             ≤ (C + 30) + (xs.length * (C + 30) + 1) := by omega
           _ ≤ (xs.length + 1) * (C + 30) + 2 := by ring_nf; omega,
      hr16_2,
      fun r h15 h16 => by rw [hregs₂ r h15 h16]; simp [s₁, h16],
      by rw [harrs₂]; rfl⟩

/-- The 16 corner index pairs `(d₁, d₂) ∈ {0, 1, 2, 3} × {0, 1, 2, 3}`. -/
def cornerPairs16 : List (ℕ × ℕ) :=
  ([0, 1, 2, 3] : List ℕ).flatMap fun d₁ =>
    ([0, 1, 2, 3] : List ℕ).map fun d₂ => (d₁, d₂)

theorem map_cornerPairs16 (h cx₁ cy₁ cx₂ cy₂ : ℕ) :
    cornerPairs16.map (fun p =>
      natCornerFaceDist h cx₁ cy₁ (p.1 / 2) (p.1 % 2) cx₂ cy₂ (p.2 / 2) (p.2 % 2)) =
      natFaceDistCandidates h cx₁ cy₁ cx₂ cy₂ := rfl

theorem exprNot_cost (e : Expr) : (exprNot e).cost = e.cost + 2 := rfl

theorem exprAnd_cost (e₁ e₂ : Expr) : (exprAnd e₁ e₂).cost = e₁.cost + e₂.cost + 1 := rfl

theorem exprLe_cost (e₁ e₂ : Expr) : (exprLe e₁ e₂).cost = e₁.cost + e₂.cost + 1 := rfl

theorem exprIte_cost (c e₁ e₂ : Expr) :
    (exprIte c e₁ e₂).cost = 2 * c.cost + e₁.cost + e₂.cost + 5 := by
  simp [exprIte, exprNot]; omega

theorem exprMin_cost (e₁ e₂ : Expr) :
    (exprMin e₁ e₂).cost = 3 * e₁.cost + 3 * e₂.cost + 7 := by
  simp [exprMin, exprIte_cost, exprLe_cost]; omega

theorem exprMax_cost (e₁ e₂ : Expr) :
    (exprMax e₁ e₂).cost = 3 * e₁.cost + 3 * e₂.cost + 7 := by
  simp [exprMax, exprIte_cost, exprLe_cost]; omega

theorem exprAbsDiff_cost (e₁ e₂ : Expr) :
    (exprAbsDiff e₁ e₂).cost = 2 * e₁.cost + 2 * e₂.cost + 3 := by
  simp [exprAbsDiff]; omega

theorem exprCornerX_cost_le (sx : ℕ) (rCX : Reg) : (exprCornerX sx rCX).cost ≤ 5 := by
  unfold exprCornerX; split_ifs <;> simp

theorem exprCornerY_cost_le (sy : ℕ) (rCY : Reg) : (exprCornerY sy rCY).cost ≤ 5 := by
  unfold exprCornerY; split_ifs <;> simp

theorem exprCornerBigX_cost_le (sx sy : ℕ) (rCX rCY : Reg) :
    (exprCornerBigX sx sy rCX rCY).cost ≤ 20 := by
  unfold exprCornerBigX
  have hx := exprCornerX_cost_le sx rCX
  have hy := exprCornerY_cost_le sy rCY
  simp only [Expr.cost_op, Expr.cost_const]
  omega

theorem exprCornerIsBrick_cost_le (sx sy : ℕ) (rH rCX rCY : Reg) :
    (exprCornerIsBrick sx sy rH rCX rCY).cost ≤ 80 := by
  unfold exprCornerIsBrick
  have hX := exprCornerBigX_cost_le sx sy rCX rCY
  have hY := exprCornerY_cost_le sy rCY
  have hcX : (if sx = 0 then Expr.const 1 else .op .lt (.const 0) (.reg rCX)).cost ≤ 3 := by
    split_ifs <;> simp
  have hcY : (if sy = 0 then Expr.const 1 else .op .lt (.const 0) (.reg rCY)).cost ≤ 3 := by
    split_ifs <;> simp
  simp only [exprAnd_cost, exprLe_cost, Expr.cost_op, Expr.cost_const, Expr.cost_reg]
  omega

theorem exprNatOutDepth_cost_le (rH : Reg) (eX eY : Expr) :
    (exprNatOutDepth rH eX eY).cost ≤ 18 * eX.cost + 18 * eY.cost + 200 := by
  unfold exprNatOutDepth
  simp only [exprMin_cost, Expr.cost_op, Expr.cost_const, Expr.cost_reg]
  omega

theorem exprNatHexDist_cost_le (eX1 eY1 eX2 eY2 : Expr) :
    (exprNatHexDist eX1 eY1 eX2 eY2).cost ≤
      6 * eX1.cost + 12 * eY1.cost + 6 * eX2.cost + 12 * eY2.cost + 50 := by
  unfold exprNatHexDist
  simp only [exprMax_cost, exprAbsDiff_cost, Expr.cost_op, Expr.cost_const]
  omega

theorem exprNatCornerFaceDist_cost_le (sx₁ sy₁ sx₂ sy₂ : ℕ) (rH rCX₁ rCY₁ rCX₂ rCY₂ : Reg) :
    (exprNatCornerFaceDist sx₁ sy₁ sx₂ sy₂ rH rCX₁ rCY₁ rCX₂ rCY₂).cost ≤ 7500 := by
  unfold exprNatCornerFaceDist
  have hX1 := exprCornerBigX_cost_le sx₁ sy₁ rCX₁ rCY₁
  have hY1 := exprCornerY_cost_le sy₁ rCY₁
  have hb1 := exprCornerIsBrick_cost_le sx₁ sy₁ rH rCX₁ rCY₁
  have hX2 := exprCornerBigX_cost_le sx₂ sy₂ rCX₂ rCY₂
  have hY2 := exprCornerY_cost_le sy₂ rCY₂
  have hb2 := exprCornerIsBrick_cost_le sx₂ sy₂ rH rCX₂ rCY₂
  have hod1 := exprNatOutDepth_cost_le rH
    (exprCornerBigX sx₁ sy₁ rCX₁ rCY₁) (exprCornerY sy₁ rCY₁)
  have hod2 := exprNatOutDepth_cost_le rH
    (exprCornerBigX sx₂ sy₂ rCX₂ rCY₂) (exprCornerY sy₂ rCY₂)
  have hhex := exprNatHexDist_cost_le
    (exprCornerBigX sx₁ sy₁ rCX₁ rCY₁) (exprCornerY sy₁ rCY₁)
    (exprCornerBigX sx₂ sy₂ rCX₂ rCY₂) (exprCornerY sy₂ rCY₂)
  simp only [exprIte_cost, exprNot_cost, exprMin_cost, Expr.cost_op, Expr.cost_const]
  omega

theorem vertCellNat_isWallCell_and_bounds {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {v : Fin n} (hv : v ∈ W.vertexFinset) :
    natIsWallCell h (W.vertCellNat v).1 (W.vertCellNat v).2 = true ∧
    (W.vertCellNat v).1 ≤ 4 * h + 2 ∧
    (W.vertCellNat v).2 ≤ 2 * h := by
  have hmem := W.vertCell_mem_fig1WallCells h2 he hW hv
  rw [GM13.mem_fig1WallCells_iff (by omega) he, W.vertCell_eq_cast_vertCellNat] at hmem
  have hnat := (natIsWallCell_eq_true_iff h (W.vertCellNat v).1 (W.vertCellNat v).2).mpr hmem
  have hbounds : (W.vertCellNat v).1 ≤ 4 * h + 2 ∧ (W.vertCellNat v).2 ≤ 2 * h := by
    unfold natIsWallCell at hnat
    rw [decide_eq_true_iff] at hnat
    exact ⟨hnat.1, hnat.2.1⟩
  exact ⟨hnat, hbounds.1, hbounds.2⟩

/-- Compute `W.computeBrickDist u v` into `regOut` for `u, v ∈ W.vertexFinset` stored in
`regU, regV`. Uses scratch registers `6 .. 11`, `15, 16`, `23, 24`, `26, 27`. -/
def computeBrickDistCmd (regU regV regOut : Reg) : Cmd :=
  .ite (exprEq (.reg regU) (.reg regV))
    (.assign regOut (.const 0))
    (.seq (computeVertCellNatCmd regU 23 24)
      (.seq (computeVertCellNatCmd regV 26 27)
        (.seq (listMinMapCmd
            (fun p : ℕ × ℕ =>
              exprNatCornerFaceDist (p.1 / 2) (p.1 % 2) (p.2 / 2) (p.2 % 2) 3 23 24 26 27)
            cornerPairs16)
          (.assign regOut (.op .add (.const 2) (.reg 16))))))

theorem computeBrickDistCmd_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (regU regV regOut : Reg)
    (hne_V6 : regV ≠ 6) (hne_V7 : regV ≠ 7) (hne_V8 : regV ≠ 8)
    (hne_V9 : regV ≠ 9) (hne_V10 : regV ≠ 10) (hne_V11 : regV ≠ 11)
    (hne_V23 : regV ≠ 23) (hne_V24 : regV ≠ 24)
    {s : State}
    (hw2 : 2 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (hs : WallStateHolds W s)
    (u v : Fin n) (hu : u ∈ W.vertexFinset) (hv : v ∈ W.vertexFinset)
    (hrU : s.regs regU = u.1) (hrV : s.regs regV = v.1) :
    ∃ s' t,
      Exec w (computeBrickDistCmd regU regV regOut) s s' t ∧
      t ≤ 121000 ∧
      s'.regs regOut = W.computeBrickDist u v ∧
      W.computeBrickDist u v ≤ 2 * h + 4 ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 15 → r ≠ 16 → r ≠ 23 → r ≠ 24 → r ≠ 26 → r ≠ 27 → r ≠ regOut →
        s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hu_w : u.1 < 2 ^ w := by have := u.2; omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  have heval_eq : (exprEq (.reg regU) (.reg regV)).eval w s =
      some (if u.1 = v.1 then 1 else 0) :=
    eval_exprEq h1_w
      (by simp [Expr.eval, checkWord, hrU, hu_w])
      (by simp [Expr.eval, checkWord, hrV, hv_w])
  by_cases huv : u = v
  · subst huv
    rw [if_pos rfl] at heval_eq
    let s₁ := s.setReg regOut 0
    have hex₁ : Exec w (.assign regOut (.const 0)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    refine ⟨s₁, _, .ite_true heval_eq (by omega) hex₁,
      by simp [exprEq, Expr.cost],
      by simp [s₁, WallOfHeight.computeBrickDist],
      by simp [WallOfHeight.computeBrickDist],
      fun r _ _ _ _ _ _ _ _ _ _ _ _ hOut => by simp [s₁, hOut],
      rfl⟩
  · have huv_val : u.1 ≠ v.1 := Fin.val_ne_of_ne huv
    rw [if_neg huv_val] at heval_eq
    rcases computeVertCellNatCmd_exec W hW regU 23 24
        (by decide) (by decide) (by decide) (by decide)
        hw2 hn_w h4h4_w hloc_w hs u hu hrU with
      ⟨s₁, t₁, hex₁, ht₁, hX₁, hY₁, hregs₁, harrs₁⟩
    have hs₁ : WallStateHolds W s₁ :=
      hs.of_preserve
        (hregs₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hregs₁ 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hregs₁ 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hregs₁ 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hregs₁ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁])
        (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁])
    have hrV₁ : s₁.regs regV = v.1 := by
      rw [hregs₁ regV hne_V6 hne_V7 hne_V8 hne_V9 hne_V10 hne_V11 hne_V23 hne_V24, hrV]
    rcases computeVertCellNatCmd_exec W hW regV 26 27
        (by decide) (by decide) (by decide) (by decide)
        hw2 hn_w h4h4_w hloc_w hs₁ v hv hrV₁ with
      ⟨s₂, t₂, hex₂, ht₂, hX₂, hY₂, hregs₂, harrs₂⟩
    have hr3_2 : s₂.regs 3 = h := by
      rw [hregs₂ 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hs₁.hr3]
    have hr23_2 : s₂.regs 23 = (W.vertCellNat u).1 := by
      rw [hregs₂ 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hX₁]
    have hr24_2 : s₂.regs 24 = (W.vertCellNat u).2 := by
      rw [hregs₂ 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hY₁]
    obtain ⟨hcell_u, hcx₁_le, hcy₁_le⟩ := vertCellNat_isWallCell_and_bounds W h2 he hW hu
    obtain ⟨hcell_v, hcx₂_le, hcy₂_le⟩ := vertCellNat_isWallCell_and_bounds W h2 he hW hv
    let fPair : ℕ × ℕ → Expr := fun p =>
      exprNatCornerFaceDist (p.1 / 2) (p.1 % 2) (p.2 / 2) (p.2 % 2) 3 23 24 26 27
    let gPair : ℕ × ℕ → ℕ := fun p =>
      natCornerFaceDist h (W.vertCellNat u).1 (W.vertCellNat u).2 (p.1 / 2) (p.1 % 2)
        (W.vertCellNat v).1 (W.vertCellNat v).2 (p.2 / 2) (p.2 % 2)
    rcases listMinMapCmd_exec fPair gPair
        (fun p => exprNatCornerFaceDist_cost_le _ _ _ _ 3 23 24 26 27)
        h1_w cornerPairs16 (s := s₂)
        (fun p _ s' hs' => by
          obtain ⟨hev, hle⟩ := eval_exprNatCornerFaceDist
            (p.1 / 2) (p.1 % 2) (p.2 / 2) (p.2 % 2) 3 23 24 26 27
            hw2 h4h4_w hcx₁_le hcy₁_le hcx₂_le hcy₂_le
            (by rw [hs' 3 (by decide) (by decide), hr3_2])
            (by rw [hs' 23 (by decide) (by decide), hr23_2])
            (by rw [hs' 24 (by decide) (by decide), hr24_2])
            (by rw [hs' 26 (by decide) (by decide), hX₂])
            (by rw [hs' 27 (by decide) (by decide), hY₂])
          exact ⟨hev, by dsimp [gPair]; omega⟩) with
      ⟨s₃, t₃, hex₃, ht₃, hr16_3, hregs₃, harrs₃⟩
    rw [map_cornerPairs16] at hr16_3
    have hmin_le : listMinNat (natFaceDistCandidates h (W.vertCellNat u).1 (W.vertCellNat u).2
        (W.vertCellNat v).1 (W.vertCellNat v).2) ≤ 2 * h + 2 := by
      have hmem0 : gPair (0, 0) ∈ natFaceDistCandidates h (W.vertCellNat u).1 (W.vertCellNat u).2
          (W.vertCellNat v).1 (W.vertCellNat v).2 := by
        rw [← map_cornerPairs16]
        exact List.mem_map_of_mem (by decide : (0, 0) ∈ cornerPairs16)
      have h0_le : gPair (0, 0) ≤ 2 * h + 2 :=
        (eval_exprNatCornerFaceDist 0 0 0 0 3 23 24 26 27 hw2 h4h4_w
          hcx₁_le hcy₁_le hcx₂_le hcy₂_le hr3_2 hr23_2 hr24_2 hX₂ hY₂).2
      exact (listMinNat_le_of_mem hmem0).trans h0_le
    let minVal := listMinNat (natFaceDistCandidates h (W.vertCellNat u).1 (W.vertCellNat u).2
      (W.vertCellNat v).1 (W.vertCellNat v).2)
    have hmin_w : minVal < 2 ^ w := by dsimp [minVal]; omega
    have h2min_w : 2 + minVal < 2 ^ w := by dsimp [minVal]; omega
    let s₄ := s₃.setReg regOut (2 + minVal)
    have hex₄ : Exec w (.assign regOut (.op .add (.const 2) (.reg 16))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr16_3, hw2, hmin_w, h2min_w, minVal])
    have hdist_eq : 2 + minVal = W.computeBrickDist u v := by
      unfold WallOfHeight.computeBrickDist
      rw [if_neg huv, W.vertCell_eq_cast_vertCellNat u, W.vertCell_eq_cast_vertCellNat v,
        ← natCellBrickDist_eq_computeCellBrickDist]
      unfold natCellBrickDist
      rw [if_pos hcell_u, if_pos hcell_v]
    have hlen16 : cornerPairs16.length = 16 := rfl
    rw [hlen16] at ht₃
    refine ⟨s₄, _,
      .ite_false heval_eq (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))),
      by simp [exprEq, Expr.cost]; omega,
      by simp [s₄, hdist_eq],
      by rw [← hdist_eq]; dsimp [minVal]; omega,
      fun r h6 h7 h8 h9 h10 h11 h15 h16 h23 h24 h26 h27 hOut => by
        simp only [s₄, State.setReg_regs_ne _ _ hOut]
        rw [hregs₃ r h15 h16, hregs₂ r h6 h7 h8 h9 h10 h11 h26 h27,
          hregs₁ r h6 h7 h8 h9 h10 h11 h23 h24],
      by simp [s₄, harrs₃, harrs₂, harrs₁]⟩

/-- Update `r_18 := if (r_18 == 1 && W.isGoodRayForQ r (Qs[j]) (rays i)) then 1 else 0`. -/
def testGoodRayForQCmd (r l a j i : ℕ) : Cmd :=
  .seq (computeQMemCmd (qPathArr j))
    (.seq (computeOneRayHitCmd l a i)
      (.seq (.assign 22
          (.read (starRayArr l a i) (.op .sub (.len (starRayArr l a i)) (.const 1))))
        (.seq (.assign 25 (.read (qPathArr j) (.const 0)))
          (.seq (computeBrickDistCmd 22 25 28)
            (.seq (.assign 25
                (.read (qPathArr j) (.op .sub (.len (qPathArr j)) (.const 1))))
              (.seq (computeBrickDistCmd 22 25 29)
                (.assign 18
                  (exprAnd (.reg 18)
                    (exprAnd (exprEq (.reg (regRayMeets i)) (.const 0))
                      (exprAnd (exprLe (.const r) (.reg 28))
                        (exprLe (.const r) (.reg 29))))))))))))

theorem isGoodRayForQ_eq_decide {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (r : ℕ) {Q P : List (Fin n)}
    (hneQ : Q ≠ []) (hneP : P ≠ []) :
    W.isGoodRayForQ r Q P =
      (!WallOfHeight.rayMeetsPath Q P &&
        (decide (r ≤ W.computeBrickDist (P.getLast hneP) (Q.head hneQ)) &&
         decide (r ≤ W.computeBrickDist (P.getLast hneP) (Q.getLast hneQ)))) := by
  unfold WallOfHeight.isGoodRayForQ WallOfHeight.closeToHead WallOfHeight.closeToLast
    WallOfHeight.closeToVert
  rw [List.head?_eq_some_head hneQ, List.getLast?_eq_some_getLast hneQ,
    List.getLast?_eq_some_getLast hneP]
  dsimp only
  rw [ ← decide_not, ← decide_not]
  simp only [not_lt]

theorem testGoodRayForQCmd_exec {w h n r l a j i : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {c : Fin n} (Q P : List (Fin n))
    (hQ : W.IsHPath Q) (hP : W.IsStarRay c P)
    (acc : Bool)
    {s : State}
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hr_w : r < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hqArr : s.arrs (qPathArr j) = Q.map Fin.val)
    (hpArr : s.arrs (starRayArr l a i) = P.map Fin.val)
    (hr18 : s.regs 18 = if acc then 1 else 0) :
    ∃ s' t,
      Exec w (testGoodRayForQCmd r l a j i) s s' t ∧
      t ≤ 79 * n + 242500 ∧
      WallStateHolds W s' ∧
      s'.regs 18 = (if (acc && W.isGoodRayForQ r Q P) then 1 else 0) ∧
      (∀ r' : Reg, r' ≠ 6 → r' ≠ 7 → r' ≠ 8 → r' ≠ 9 → r' ≠ 10 → r' ≠ 11 →
        r' ≠ 15 → r' ≠ 16 → r' ≠ 18 → r' ≠ 22 → r' ≠ 23 → r' ≠ 24 →
        r' ≠ 25 → r' ≠ 26 → r' ≠ 27 → r' ≠ 28 → r' ≠ 29 →
        r' ≠ regRayHitVert i → r' ≠ regRayMeets i → s'.regs r' = s.regs r') ∧
      (∀ arr : Arr, arr ≠ qMemArr → arr ≠ tmpPathArr1 → arr ≠ hitPrefArr i →
        s'.arrs arr = s.arrs arr) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  obtain ⟨hneQ, _, hndQ, _, hheadQ_W, hlastQ_W, _, _⟩ := hQ
  obtain ⟨hneP, _, _, hndP, _, hlastP_W, _, _⟩ := hP
  have hQ_len : Q.length ≤ n := length_le_of_nodup_fin hndQ
  have hP_len : P.length ≤ n := length_le_of_nodup_fin hndP
  have hQ_pos : 1 ≤ Q.length := List.length_pos_iff.mpr hneQ
  have hP_pos : 1 ≤ P.length := List.length_pos_iff.mpr hneP
  have hQ_w : Q.length < 2 ^ w := by omega
  have hP_w : P.length < 2 ^ w := by omega
  -- Step 1: computeQMemCmd (qPathArr j)
  rcases computeQMemCmd_exec (qPathArr j)
      (by dsimp [qPathArr, qMemArr, Arr]; omega)
      Q h1_w hn_w hQ_w hs.hr0 hqArr with
    ⟨s₁, t₁, hex₁, ht₁, hmem_len₁, hmem_val₁, hregs₁, harrs₁⟩
  -- Step 2: computeOneRayHitCmd l a i
  have hpArr₁ : s₁.arrs (starRayArr l a i) = P.map Fin.val := by
    rw [harrs₁ (starRayArr l a i) (by dsimp [starRayArr, qMemArr, Arr]; omega)]
    exact hpArr
  rcases computeOneRayHitCmd_exec Q P hneP h1_w hn_w hP_w hpArr₁ hmem_len₁ hmem_val₁ with
    ⟨s₂, t₂, hex₂, ht₂, _, _, hrm₂, hregs₂, harrs₂⟩
  have hs₂ : WallStateHolds W s₂ :=
    hs.of_preserve
      (by rw [hregs₂ 0 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega),
          hregs₁ 0 (by decide) (by decide)])
      (by rw [hregs₂ 3 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega),
          hregs₁ 3 (by decide) (by decide)])
      (by rw [hregs₂ 12 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega),
          hregs₁ 12 (by decide) (by decide)])
      (by rw [hregs₂ 13 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega),
          hregs₁ 13 (by decide) (by decide)])
      (by rw [hregs₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega),
          hregs₁ 14 (by decide) (by decide)])
      (by rw [harrs₂ wallEncArr (by decide) (by dsimp [wallEncArr, hitPrefArr, Arr]; omega),
          harrs₁ wallEncArr (by decide)])
      (by rw [harrs₂ locArr (by decide) (by dsimp [locArr, hitPrefArr, Arr]; omega),
          harrs₁ locArr (by decide)])
      (by rw [harrs₂ wallMemArr (by decide) (by dsimp [wallMemArr, hitPrefArr, Arr]; omega),
          harrs₁ wallMemArr (by decide)])
      (by rw [harrs₂ edgeOffArr (by decide) (by dsimp [edgeOffArr, hitPrefArr, Arr]; omega),
          harrs₁ edgeOffArr (by decide)])
      (by rw [harrs₂ edgeLenArr (by decide) (by dsimp [edgeLenArr, hitPrefArr, Arr]; omega),
          harrs₁ edgeLenArr (by decide)])
      (by rw [harrs₂ edgeU1Arr (by decide) (by dsimp [edgeU1Arr, hitPrefArr, Arr]; omega),
          harrs₁ edgeU1Arr (by decide)])
      (by rw [harrs₂ edgeU2Arr (by decide) (by dsimp [edgeU2Arr, hitPrefArr, Arr]; omega),
          harrs₁ edgeU2Arr (by decide)])
      (by rw [harrs₂ horizEdgeIdxArr (by decide) (by dsimp [horizEdgeIdxArr, hitPrefArr, Arr]; omega),
          harrs₁ horizEdgeIdxArr (by decide)])
      (by rw [harrs₂ vertEdgeIdxArr (by decide) (by dsimp [vertEdgeIdxArr, hitPrefArr, Arr]; omega),
          harrs₁ vertEdgeIdxArr (by decide)])
  -- Step 3: r_22 := (starRayArr l a i)[P.length - 1]
  let u := P.getLast hneP
  have hu_w : u.1 < 2 ^ w := by have := u.2; omega
  have hpArr₂ : s₂.arrs (starRayArr l a i) = P.map Fin.val := by
    rw [harrs₂ (starRayArr l a i)
      (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
      (by dsimp [starRayArr, hitPrefArr, Arr]; omega)]
    exact hpArr₁
  have hget_u : (s₂.arrs (starRayArr l a i))[P.length - 1]'(by simp [hpArr₂]; omega) = u.1 := by
    have hlast_eq : P[P.length - 1]'(by omega) = u := (List.getLast_eq_getElem hneP).symm
    simp [hpArr₂, hlast_eq]
  have heval_subP : (Expr.op .sub (.len (starRayArr l a i)) (.const 1)).eval w s₂ =
      some (P.length - 1) :=
    eval_op_sub (eval_len (by simp [hpArr₂]) hP_w) (by simp [Expr.eval, checkWord, h1_w])
  have heval_read_u :
      (Expr.read (starRayArr l a i) (.op .sub (.len (starRayArr l a i)) (.const 1))).eval w s₂ =
        some u.1 := by
    have hlt_len : P.length - 1 < (s₂.arrs (starRayArr l a i)).length := by simp [hpArr₂]; omega
    unfold Expr.eval
    rw [heval_subP]
    simp [hlt_len, hget_u, checkWord, hu_w]
  let s₃ := s₂.setReg 22 u.1
  have hex₃ : Exec w (.assign 22
      (.read (starRayArr l a i) (.op .sub (.len (starRayArr l a i)) (.const 1)))) s₂ s₃ 5 :=
    .assign heval_read_u
  -- Step 4: r_25 := (qPathArr j)[0]
  let e₁ := Q.head hneQ
  have he₁_w : e₁.1 < 2 ^ w := by have := e₁.2; omega
  have hqArr₂ : s₂.arrs (qPathArr j) = Q.map Fin.val := by
    rw [harrs₂ (qPathArr j)
      (by dsimp [qPathArr, tmpPathArr1, Arr]; omega)
      (by dsimp [qPathArr, hitPrefArr, Arr]; omega),
      harrs₁ (qPathArr j) (by dsimp [qPathArr, qMemArr, Arr]; omega)]
    exact hqArr
  have hget_e₁ : (s₃.arrs (qPathArr j))[0]'(by simp [s₃, hqArr₂]; omega) = e₁.1 := by
    have hhead_eq : Q[0]'(by omega) = e₁ := (List.head_eq_getElem_zero hneQ).symm
    simp [s₃, hqArr₂, hhead_eq]
  have heval_read_e₁ : (Expr.read (qPathArr j) (.const 0)).eval w s₃ = some e₁.1 := by
    have hlt0 : 0 < (s₃.arrs (qPathArr j)).length := by simp [s₃, hqArr₂]; omega
    unfold Expr.eval
    simp [checkWord, h0_w, hlt0, hget_e₁, he₁_w]
  let s₄ := s₃.setReg 25 e₁.1
  have hex₄ : Exec w (.assign 25 (.read (qPathArr j) (.const 0))) s₃ s₄ 3 :=
    .assign heval_read_e₁
  -- Step 5: computeBrickDistCmd 22 25 28
  have hs₄ : WallStateHolds W s₄ :=
    hs₂.of_preserve (by simp [s₄, s₃]) (by simp [s₄, s₃]) (by simp [s₄, s₃])
      (by simp [s₄, s₃]) (by simp [s₄, s₃])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rcases computeBrickDistCmd_exec W h2 he hW 22 25 28
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw2 hn_w h4h4_w hloc_w hs₄ u e₁ hlastP_W hheadQ_W
      (by simp [s₄, s₃]) (by simp [s₄]) with
    ⟨s₅, t₅, hex₅, ht₅, hr28_5, hd1_le, hregs₅, harrs₅⟩
  -- Step 6: r_25 := (qPathArr j)[Q.length - 1]
  let e₂ := Q.getLast hneQ
  have he₂_w : e₂.1 < 2 ^ w := by have := e₂.2; omega
  have hqArr₅ : s₅.arrs (qPathArr j) = Q.map Fin.val := by
    rw [harrs₅]; exact hqArr₂
  have hget_e₂ : (s₅.arrs (qPathArr j))[Q.length - 1]'(by simp [hqArr₅]; omega) = e₂.1 := by
    have hlast_eq : Q[Q.length - 1]'(by omega) = e₂ := (List.getLast_eq_getElem hneQ).symm
    simp [hqArr₅, hlast_eq]
  have heval_subQ : (Expr.op .sub (.len (qPathArr j)) (.const 1)).eval w s₅ =
      some (Q.length - 1) :=
    eval_op_sub (eval_len (by simp [hqArr₅]) hQ_w) (by simp [Expr.eval, checkWord, h1_w])
  have heval_read_e₂ :
      (Expr.read (qPathArr j) (.op .sub (.len (qPathArr j)) (.const 1))).eval w s₅ =
        some e₂.1 := by
    have hlt_len : Q.length - 1 < (s₅.arrs (qPathArr j)).length := by simp [hqArr₅]; omega
    unfold Expr.eval
    rw [heval_subQ]
    simp [hlt_len, hget_e₂, checkWord, he₂_w]
  let s₆ := s₅.setReg 25 e₂.1
  have hex₆ : Exec w (.assign 25
      (.read (qPathArr j) (.op .sub (.len (qPathArr j)) (.const 1)))) s₅ s₆ 5 :=
    .assign heval_read_e₂
  -- Step 7: computeBrickDistCmd 22 25 29
  have hs₆ : WallStateHolds W s₆ :=
    hs₄.of_preserve
      (by simp [s₆, hregs₅ 0 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₆, hregs₅ 3 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₆, hregs₅ 12 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₆, hregs₅ 13 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₆, hregs₅ 14 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₆, harrs₅]) (by simp [s₆, harrs₅]) (by simp [s₆, harrs₅])
      (by simp [s₆, harrs₅]) (by simp [s₆, harrs₅]) (by simp [s₆, harrs₅])
      (by simp [s₆, harrs₅]) (by simp [s₆, harrs₅]) (by simp [s₆, harrs₅])
  have hr22_6 : s₆.regs 22 = u.1 := by
    simp only [s₆, State.setReg_regs_ne _ _ (by decide : (22 : Reg) ≠ 25)]
    rw [hregs₅ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s₄, s₃]
  rcases computeBrickDistCmd_exec W h2 he hW 22 25 29
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw2 hn_w h4h4_w hloc_w hs₆ u e₂ hlastP_W hlastQ_W
      hr22_6 (by simp [s₆]) with
    ⟨s₇, t₇, hex₇, ht₇, hr29_7, hd2_le, hregs₇, harrs₇⟩
  -- Step 8: update r_18
  have hr28_7 : s₇.regs 28 = W.computeBrickDist u e₁ := by
    rw [hregs₇ 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s₆, hr28_5]
  have hr18_7 : s₇.regs 18 = if acc then 1 else 0 := by
    rw [hregs₇ 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s₆, State.setReg_regs_ne _ _ (by decide : (18 : Reg) ≠ 25)]
    rw [hregs₅ 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s₄, s₃, State.setReg_regs_ne _ _ (by decide : (18 : Reg) ≠ 25),
      State.setReg_regs_ne _ _ (by decide : (18 : Reg) ≠ 22)]
    rw [hregs₂ 18 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega),
      hregs₁ 18 (by decide) (by decide), hr18]
  have hrm_7 : s₇.regs (regRayMeets i) = if WallOfHeight.rayMeetsPath Q P then 1 else 0 := by
    rw [hregs₇ (regRayMeets i)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega)]
    simp only [s₆, State.setReg_regs_ne _ _
      (by dsimp [regRayMeets, Reg]; omega : regRayMeets i ≠ 25)]
    rw [hregs₅ (regRayMeets i)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
        (by dsimp [regRayMeets, Reg]; omega)]
    simp [s₄, s₃,
      State.setReg_regs_ne _ _ (by dsimp [regRayMeets, Reg]; omega : regRayMeets i ≠ 25),
      State.setReg_regs_ne _ _ (by dsimp [regRayMeets, Reg]; omega : regRayMeets i ≠ 22),
      hrm₂]
  have hd1_w : W.computeBrickDist u e₁ < 2 ^ w := by omega
  have hd2_w : W.computeBrickDist u e₂ < 2 ^ w := by omega
  have heval_le1 : (exprLe (.const r) (.reg 28)).eval w s₇ =
      some (if decide (r ≤ W.computeBrickDist u e₁) then 1 else 0) := by
    simp only [decide_eq_true_eq]
    exact eval_exprLe h1_w
      (by simp [Expr.eval, checkWord, hr_w])
      (by simp [Expr.eval, checkWord, hr28_7, hd1_w])
  have heval_le2 : (exprLe (.const r) (.reg 29)).eval w s₇ =
      some (if decide (r ≤ W.computeBrickDist u e₂) then 1 else 0) := by
    simp only [decide_eq_true_eq]
    exact eval_exprLe h1_w
      (by simp [Expr.eval, checkWord, hr_w])
      (by simp [Expr.eval, checkWord, hr29_7, hd2_w])
  have heval_rm0 : (exprEq (.reg (regRayMeets i)) (.const 0)).eval w s₇ =
      some (if !WallOfHeight.rayMeetsPath Q P then 1 else 0) := by
    have hev : (exprEq (.reg (regRayMeets i)) (.const 0)).eval w s₇ =
        some (if (if WallOfHeight.rayMeetsPath Q P then 1 else 0) = 0 then 1 else 0) :=
      eval_exprEq h1_w
        (by unfold Expr.eval; rw [hrm_7]; split_ifs <;> simp [checkWord, h1_w, h0_w])
        (by simp [Expr.eval, checkWord, h0_w])
    rw [hev]
    cases WallOfHeight.rayMeetsPath Q P <;> rfl
  have heval_and1 : (exprAnd (exprLe (.const r) (.reg 28)) (exprLe (.const r) (.reg 29))).eval w s₇ =
      some (if (decide (r ≤ W.computeBrickDist u e₁) && decide (r ≤ W.computeBrickDist u e₂))
            then 1 else 0) :=
    eval_exprAnd_bool h1_w heval_le1 heval_le2
  have heval_and2 :
      (exprAnd (exprEq (.reg (regRayMeets i)) (.const 0))
        (exprAnd (exprLe (.const r) (.reg 28)) (exprLe (.const r) (.reg 29)))).eval w s₇ =
      some (if W.isGoodRayForQ r Q P then 1 else 0) := by
    rw [isGoodRayForQ_eq_decide W r hneQ hneP]
    exact eval_exprAnd_bool h1_w heval_rm0 heval_and1
  have heval_and3 :
      (exprAnd (.reg 18)
        (exprAnd (exprEq (.reg (regRayMeets i)) (.const 0))
          (exprAnd (exprLe (.const r) (.reg 28)) (exprLe (.const r) (.reg 29))))).eval w s₇ =
      some (if (acc && W.isGoodRayForQ r Q P) then 1 else 0) :=
    eval_exprAnd_bool h1_w
      (by unfold Expr.eval; rw [hr18_7]; split_ifs <;> simp [checkWord, h1_w, h0_w])
      heval_and2
  let s₈ := s₇.setReg 18 (if (acc && W.isGoodRayForQ r Q P) then 1 else 0)
  have hex₈ : Exec w (.assign 18
      (exprAnd (.reg 18)
        (exprAnd (exprEq (.reg (regRayMeets i)) (.const 0))
          (exprAnd (exprLe (.const r) (.reg 28)) (exprLe (.const r) (.reg 29)))))) s₇ s₈ _ :=
    .assign heval_and3
  have hs₈ : WallStateHolds W s₈ :=
    hs₆.of_preserve
      (by simp [s₈, hregs₇ 0 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₈, hregs₇ 3 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₈, hregs₇ 12 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₈, hregs₇ 13 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₈, hregs₇ 14 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by simp [s₈, harrs₇]) (by simp [s₈, harrs₇]) (by simp [s₈, harrs₇])
      (by simp [s₈, harrs₇]) (by simp [s₈, harrs₇]) (by simp [s₈, harrs₇])
      (by simp [s₈, harrs₇]) (by simp [s₈, harrs₇]) (by simp [s₈, harrs₇])
  refine ⟨s₈, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
    by simp only [exprAnd, exprEq, exprLe, Expr.cost]; omega,
    hs₈,
    by simp [s₈],
    fun r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h22 h23 h24 h25 h26 h27 h28 h29 hhv hrm => by
      simp only [s₈, State.setReg_regs_ne _ _ h18]
      rw [hregs₇ r' h6 h7 h8 h9 h10 h11 h15 h16 h23 h24 h26 h27 h29]
      simp only [s₆, State.setReg_regs_ne _ _ h25]
      rw [hregs₅ r' h6 h7 h8 h9 h10 h11 h15 h16 h23 h24 h26 h27 h28]
      simp only [s₄, s₃, State.setReg_regs_ne _ _ h25, State.setReg_regs_ne _ _ h22]
      rw [hregs₂ r' h7 h8 h9 h10 h11 hhv hrm, hregs₁ r' h8 h11],
    fun arr hqm htmp1 hpref => by
      simp only [s₈, State.setReg_arrs, harrs₇, s₆, harrs₅, s₄, s₃]
      rw [harrs₂ arr htmp1 hpref, harrs₁ arr hqm]⟩

/-- Update `r_18` over `rem` paths `qPathArr j .. qPathArr (j + rem - 1)`. -/
def testIsGoodRaySliceCmd (r l a i j : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (testGoodRayForQCmd r l a j i)
      (testIsGoodRaySliceCmd r l a i (j + 1) rem)

theorem testIsGoodRaySliceCmd_exec {w h n : ℕ} (r l a i : ℕ) {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {c : Fin n} (P : List (Fin n)) (hP : W.IsStarRay c P)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hr_w : r < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w) :
    ∀ (Qs : List (List (Fin n))) (j : ℕ) (acc : Bool) {s : State},
      (∀ Q ∈ Qs, W.IsHPath Q) →
      (∀ m (hm : m < Qs.length), s.arrs (qPathArr (j + m)) = (Qs[m]'hm).map Fin.val) →
      WallStateHolds W s →
      s.arrs (starRayArr l a i) = P.map Fin.val →
      s.regs 18 = (if acc then 1 else 0) →
      ∃ s' t,
        Exec w (testIsGoodRaySliceCmd r l a i j Qs.length) s s' t ∧
        t ≤ (79 * n + 242500) * Qs.length + 1 ∧
        WallStateHolds W s' ∧
        s'.regs 18 = (if (acc && W.isGoodRay r Qs P) then 1 else 0) ∧
        (∀ r' : Reg, r' ≠ 6 → r' ≠ 7 → r' ≠ 8 → r' ≠ 9 → r' ≠ 10 → r' ≠ 11 →
          r' ≠ 15 → r' ≠ 16 → r' ≠ 18 → r' ≠ 22 → r' ≠ 23 → r' ≠ 24 →
          r' ≠ 25 → r' ≠ 26 → r' ≠ 27 → r' ≠ 28 → r' ≠ 29 →
          r' ≠ regRayHitVert i → r' ≠ regRayMeets i → s'.regs r' = s.regs r') ∧
        (∀ arr : Arr, arr ≠ qMemArr → arr ≠ tmpPathArr1 → arr ≠ hitPrefArr i →
          s'.arrs arr = s.arrs arr)
  | [], j, acc, s, _, _, hs, _, hr18 => by
    refine ⟨s, 1, .skip s, by simp, hs, ?_, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ => rfl⟩
    simp [WallOfHeight.isGoodRay, hr18]
  | Q :: Qs, j, acc, s, hQs_valid, hqArr, hs, hpArr, hr18 => by
    have hQ_valid : W.IsHPath Q := hQs_valid Q List.mem_cons_self
    have hq0 : s.arrs (qPathArr j) = Q.map Fin.val := hqArr 0 (by simp)
    rcases testGoodRayForQCmd_exec W h2 he hW Q P hQ_valid hP acc
        hw2 hn_w hr_w h4h4_w hloc_w hs hq0 hpArr hr18 with
      ⟨s₁, t₁, hex₁, ht₁, hs₁, hr18_1, hregs₁, harrs₁⟩
    rcases testIsGoodRaySliceCmd_exec r l a i W h2 he hW P hP hw2 hn_w hr_w h4h4_w hloc_w
        Qs (j + 1) (acc && W.isGoodRayForQ r Q P) (s := s₁)
        (fun Q' hQ' => hQs_valid Q' (List.mem_cons_of_mem Q hQ'))
        (fun m hm => by
          rw [harrs₁ (qPathArr (j + 1 + m))
            (by dsimp [qPathArr, qMemArr, Arr]; omega)
            (by dsimp [qPathArr, tmpPathArr1, Arr]; omega)
            (by dsimp [qPathArr, hitPrefArr, Arr]; omega)]
          have h := hqArr (m + 1) (by simp [hm])
          simpa [Nat.add_right_comm, Nat.add_assoc] using h)
        hs₁
        (by
          rw [harrs₁ (starRayArr l a i)
            (by dsimp [starRayArr, qMemArr, Arr]; omega)
            (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
            (by dsimp [starRayArr, hitPrefArr, Arr]; omega)]
          exact hpArr)
        hr18_1 with
      ⟨s₂, t₂, hex₂, ht₂, hs₂, hr18_2, hregs₂, harrs₂⟩
    have hand_assoc :
        ((acc && W.isGoodRayForQ r Q P) && W.isGoodRay r Qs P) =
          (acc && W.isGoodRay r (Q :: Qs) P) := by
      simp [WallOfHeight.isGoodRay, Bool.and_assoc]
    rw [hand_assoc] at hr18_2
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by simp only [List.length_cons, Nat.mul_add, Nat.mul_one]; omega,
      hs₂, hr18_2,
      fun r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h22 h23 h24 h25 h26 h27 h28 h29 hhv hrm =>
        (hregs₂ r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h22 h23 h24 h25 h26 h27 h28 h29 hhv hrm).trans
          (hregs₁ r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h22 h23 h24 h25 h26 h27 h28 h29 hhv hrm),
      fun arr hqm htmp1 hpref =>
        (harrs₂ arr hqm htmp1 hpref).trans (harrs₁ arr hqm htmp1 hpref)⟩

/-- Set `r_18 := if W.isGoodRay r Qs (rays i) then 1 else 0` over the `s` paths `qPathArr 0 .. qPathArr (s - 1)`. -/
def testIsGoodRayCmd (r l a s i : ℕ) : Cmd :=
  .seq (.assign 18 (.const 1))
    (testIsGoodRaySliceCmd r l a i 0 s)

theorem testIsGoodRayCmd_exec {w h n r l a sIdx i : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {c : Fin n} (Qs : List (List (Fin n))) (P : List (Fin n))
    (hQs_len : Qs.length = sIdx)
    (hQs_valid : ∀ Q ∈ Qs, W.IsHPath Q)
    (hP : W.IsStarRay c P)
    {s : State}
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hr_w : r < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hqArr : ∀ m (hm : m < Qs.length), s.arrs (qPathArr m) = (Qs[m]'hm).map Fin.val)
    (hpArr : s.arrs (starRayArr l a i) = P.map Fin.val) :
    ∃ s' t,
      Exec w (testIsGoodRayCmd r l a sIdx i) s s' t ∧
      t ≤ (79 * n + 242500) * sIdx + 3 ∧
      WallStateHolds W s' ∧
      s'.regs 18 = (if W.isGoodRay r Qs P then 1 else 0) ∧
      (∀ r' : Reg, r' ≠ 6 → r' ≠ 7 → r' ≠ 8 → r' ≠ 9 → r' ≠ 10 → r' ≠ 11 →
        r' ≠ 15 → r' ≠ 16 → r' ≠ 18 → r' ≠ 22 → r' ≠ 23 → r' ≠ 24 →
        r' ≠ 25 → r' ≠ 26 → r' ≠ 27 → r' ≠ 28 → r' ≠ 29 →
        r' ≠ regRayHitVert i → r' ≠ regRayMeets i → s'.regs r' = s.regs r') ∧
      (∀ arr : Arr, arr ≠ qMemArr → arr ≠ tmpPathArr1 → arr ≠ hitPrefArr i →
        s'.arrs arr = s.arrs arr) := by
  have h1_w : 1 < 2 ^ w := by omega
  let s₁ := s.setReg 18 1
  have hex₁ : Exec w (.assign 18 (.const 1)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h1_w])
  have hs₁ : WallStateHolds W s₁ :=
    hs.of_preserve (by simp [s₁]) (by simp [s₁]) (by simp [s₁]) (by simp [s₁]) (by simp [s₁])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
  subst hQs_len
  rcases testIsGoodRaySliceCmd_exec r l a i W h2 he hW P hP hw2 hn_w hr_w h4h4_w hloc_w
      Qs 0 true (s := s₁) hQs_valid
      (fun m hm => by simpa [s₁] using hqArr m hm)
      hs₁ hpArr (by simp [s₁]) with
    ⟨s₂, t₂, hex₂, ht₂, hs₂, hr18_2, hregs₂, harrs₂⟩
  simp only [Bool.true_and] at hr18_2
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hs₂, hr18_2,
    fun r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h22 h23 h24 h25 h26 h27 h28 h29 hhv hrm => by
      rw [hregs₂ r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h22 h23 h24 h25 h26 h27 h28 h29 hhv hrm]
      simp [s₁, h18],
    fun arr hqm htmp1 hpref => by
      rw [harrs₂ arr hqm htmp1 hpref]
      rfl⟩

/-- Loop invariant for scanning `0 ≤ idx < l` to find the first two active good rays:
`r_30` holds `min L.length 2`, `r_19` holds the first index if `1 ≤ L.length`, and `r_21` holds
the second index if `2 ≤ L.length`. -/
def goodScanInv {l : ℕ} (s : State) (L : List (Fin l)) : Prop :=
  match L with
  | [] => s.regs 30 = 0
  | [i₁] => s.regs 30 = 1 ∧ s.regs 19 = i₁.1
  | i₁ :: i₂ :: _ => s.regs 30 = 2 ∧ s.regs 19 = i₁.1 ∧ s.regs 21 = i₂.1

theorem goodScanInv_of_regs_eq {l : ℕ} {s s' : State} {L : List (Fin l)}
    (h : goodScanInv s L)
    (h19 : s'.regs 19 = s.regs 19)
    (h21 : s'.regs 21 = s.regs 21)
    (h30 : s'.regs 30 = s.regs 30) :
    goodScanInv s' L := by
  rcases L with _ | ⟨i₁, _ | ⟨i₂, rest⟩⟩ <;>
    simpa [goodScanInv, h19, h21, h30] using h

/-- Test ray `i` of star `a` and update `(r_30, r_19, r_21)` if ray `i` is active and good for `Qs`. -/
def findTwoGoodRaysOneCmd (r l a s i : ℕ) : Cmd :=
  .seq (testIsGoodRayCmd r l a s i)
    (.ite (exprAnd (exprEq (.reg (regRayActive l a i)) (.const 1))
                   (exprEq (.reg 18) (.const 1)))
      (.ite (exprEq (.reg 30) (.const 1))
        (.seq (.assign 21 (.const i)) (.assign 30 (.const 2)))
        (.ite (exprEq (.reg 30) (.const 0))
          (.seq (.assign 19 (.const i)) (.assign 30 (.const 1)))
          .skip))
      .skip)

theorem findTwoGoodRaysOneCmd_exec {w h n r l a sIdx : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {c : Fin n} (Qs : List (List (Fin n)))
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (idx : Fin l) (L : List (Fin l))
    (hQs_len : Qs.length = sIdx)
    (hQs_valid : ∀ Q ∈ Qs, W.IsHPath Q)
    (hP : W.IsStarRay c (rays idx))
    {s : State}
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hr_w : r < 2 ^ w) (hl_w : l < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hqArr : ∀ m (hm : m < Qs.length), s.arrs (qPathArr m) = (Qs[m]'hm).map Fin.val)
    (hpArr : s.arrs (starRayArr l a idx.1) = (rays idx).map Fin.val)
    (hact : s.regs (regRayActive l a idx.1) = if act idx then 1 else 0)
    (hinv : goodScanInv s L) :
    ∃ s' t,
      Exec w (findTwoGoodRaysOneCmd r l a sIdx idx.1) s s' t ∧
      t ≤ (79 * n + 242500) * sIdx + 30 ∧
      WallStateHolds W s' ∧
      goodScanInv s' (L ++ (if (act idx && W.isGoodRay r Qs (rays idx)) then [idx] else [])) ∧
      (∀ r' : Reg, r' ≠ 6 → r' ≠ 7 → r' ≠ 8 → r' ≠ 9 → r' ≠ 10 → r' ≠ 11 →
        r' ≠ 15 → r' ≠ 16 → r' ≠ 18 → r' ≠ 19 → r' ≠ 21 → r' ≠ 22 → r' ≠ 23 →
        r' ≠ 24 → r' ≠ 25 → r' ≠ 26 → r' ≠ 27 → r' ≠ 28 → r' ≠ 29 → r' ≠ 30 →
        r' ≠ regRayHitVert idx.1 → r' ≠ regRayMeets idx.1 → s'.regs r' = s.regs r') ∧
      (∀ arr : Arr, arr ≠ qMemArr → arr ≠ tmpPathArr1 → arr ≠ hitPrefArr idx.1 →
        s'.arrs arr = s.arrs arr) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hidx_w : idx.1 < 2 ^ w := by have := idx.2; omega
  rcases testIsGoodRayCmd_exec W h2 he hW Qs (rays idx) hQs_len hQs_valid hP
      hw2 hn_w hr_w h4h4_w hloc_w hs hqArr hpArr with
    ⟨s₁, t₁, hex₁, ht₁, hs₁, hr18_1, hregs₁, harrs₁⟩
  have hact₁ : s₁.regs (regRayActive l a idx.1) = if act idx then 1 else 0 := by
    rw [hregs₁ (regRayActive l a idx.1)
      (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
      (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
      (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
      (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
      (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
      (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
      (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
      (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
      (by dsimp [regRayActive, Reg]; omega)
      (by dsimp [regRayActive, regRayHitVert, Reg]; omega)
      (by dsimp [regRayActive, regRayMeets, Reg]; omega), hact]
  have hinv₁ : goodScanInv s₁ L :=
    goodScanInv_of_regs_eq hinv
      (hregs₁ 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega))
      (hregs₁ 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega))
      (hregs₁ 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega))
  have heval_act : (exprEq (.reg (regRayActive l a idx.1)) (.const 1)).eval w s₁ =
      some (if act idx then 1 else 0) := by
    have hev : (exprEq (.reg (regRayActive l a idx.1)) (.const 1)).eval w s₁ =
        some (if (if act idx then 1 else 0) = 1 then 1 else 0) :=
      eval_exprEq h1_w
        (by unfold Expr.eval; rw [hact₁]; split_ifs <;> simp [checkWord, h1_w, h0_w])
        (by simp [Expr.eval, checkWord, h1_w])
    rw [hev]
    cases act idx <;> rfl
  have heval_good : (exprEq (.reg 18) (.const 1)).eval w s₁ =
      some (if W.isGoodRay r Qs (rays idx) then 1 else 0) := by
    have hev : (exprEq (.reg 18) (.const 1)).eval w s₁ =
        some (if (if W.isGoodRay r Qs (rays idx) then 1 else 0) = 1 then 1 else 0) :=
      eval_exprEq h1_w
        (by unfold Expr.eval; rw [hr18_1]; split_ifs <;> simp [checkWord, h1_w, h0_w])
        (by simp [Expr.eval, checkWord, h1_w])
    rw [hev]
    cases W.isGoodRay r Qs (rays idx) <;> rfl
  have heval_cond :
      (exprAnd (exprEq (.reg (regRayActive l a idx.1)) (.const 1))
               (exprEq (.reg 18) (.const 1))).eval w s₁ =
      some (if (act idx && W.isGoodRay r Qs (rays idx)) then 1 else 0) :=
    eval_exprAnd_bool h1_w heval_act heval_good
  cases hb : (act idx && W.isGoodRay r Qs (rays idx))
  · rw [hb] at heval_cond
    refine ⟨s₁, _, .seq hex₁ (.ite_false heval_cond (.skip s₁)),
      by simp only [exprAnd, exprEq, Expr.cost]; omega,
      hs₁, by simpa using hinv₁,
      fun r' h6 h7 h8 h9 h10 h11 h15 h16 h18 _ _ h22 h23 h24 h25 h26 h27 h28 h29 _ hhv hrm =>
        hregs₁ r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h22 h23 h24 h25 h26 h27 h28 h29 hhv hrm,
      harrs₁⟩
  · rw [hb] at heval_cond
    have h1_ne : (1 : ℕ) ≠ 0 := by decide
    rcases L with _ | ⟨i₁, _ | ⟨i₂, rest⟩⟩
    · -- Case `L = []`: `s₁.regs 30 = 0`
      have hr30_1 : s₁.regs 30 = 0 := hinv₁
      have heval_30_1 : (exprEq (.reg 30) (.const 1)).eval w s₁ = some 0 := by
        simp [exprEq, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr30_1, h0_w, h1_w]
      have heval_30_0 : (exprEq (.reg 30) (.const 0)).eval w s₁ = some 1 := by
        simp [exprEq, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr30_1, h0_w, h1_w]
      let s₂ := (s₁.setReg 19 idx.1).setReg 30 1
      have hex_set : Exec w (.seq (.assign 19 (.const idx.1)) (.assign 30 (.const 1))) s₁ s₂ 4 :=
        .seq (.assign (by simp [Expr.eval, checkWord, hidx_w]))
             (.assign (by simp [Expr.eval, checkWord, h1_w]))
      have hex_br : Exec w
          (.ite (exprEq (.reg 30) (.const 1))
            (.seq (.assign 21 (.const idx.1)) (.assign 30 (.const 2)))
            (.ite (exprEq (.reg 30) (.const 0))
              (.seq (.assign 19 (.const idx.1)) (.assign 30 (.const 1)))
              .skip)) s₁ s₂ _ :=
        .ite_false heval_30_1 (.ite_true heval_30_0 h1_ne hex_set)
      have hs₂ : WallStateHolds W s₂ :=
        hs₁.of_preserve (by simp [s₂]) (by simp [s₂]) (by simp [s₂]) (by simp [s₂]) (by simp [s₂])
          rfl rfl rfl rfl rfl rfl rfl rfl rfl
      refine ⟨s₂, _, .seq hex₁ (.ite_true heval_cond h1_ne hex_br),
        by simp only [exprAnd, exprEq, Expr.cost]; omega,
        hs₂, by simp [goodScanInv, s₂],
        fun r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h19 _ h22 h23 h24 h25 h26 h27 h28 h29 h30 hhv hrm => by
          simp only [s₂, State.setReg_regs_ne _ _ h30, State.setReg_regs_ne _ _ h19]
          exact hregs₁ r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h22 h23 h24 h25 h26 h27 h28 h29 hhv hrm,
        harrs₁⟩
    · -- Case `L = [i₁]`: `s₁.regs 30 = 1 ∧ s₁.regs 19 = i₁.1`
      obtain ⟨hr30_1, hr19_1⟩ := hinv₁
      have heval_30_1 : (exprEq (.reg 30) (.const 1)).eval w s₁ = some 1 := by
        simp [exprEq, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr30_1, h1_w]
      let s₂ := (s₁.setReg 21 idx.1).setReg 30 2
      have hex_set : Exec w (.seq (.assign 21 (.const idx.1)) (.assign 30 (.const 2))) s₁ s₂ 4 :=
        .seq (.assign (by simp [Expr.eval, checkWord, hidx_w]))
             (.assign (by simp [Expr.eval, checkWord, hw2]))
      have hex_br : Exec w
          (.ite (exprEq (.reg 30) (.const 1))
            (.seq (.assign 21 (.const idx.1)) (.assign 30 (.const 2)))
            (.ite (exprEq (.reg 30) (.const 0))
              (.seq (.assign 19 (.const idx.1)) (.assign 30 (.const 1)))
              .skip)) s₁ s₂ _ :=
        .ite_true heval_30_1 h1_ne hex_set
      have hs₂ : WallStateHolds W s₂ :=
        hs₁.of_preserve (by simp [s₂]) (by simp [s₂]) (by simp [s₂]) (by simp [s₂]) (by simp [s₂])
          rfl rfl rfl rfl rfl rfl rfl rfl rfl
      refine ⟨s₂, _, .seq hex₁ (.ite_true heval_cond h1_ne hex_br),
        by simp only [exprAnd, exprEq, Expr.cost]; omega,
        hs₂, by simp [goodScanInv, s₂, hr19_1],
        fun r' h6 h7 h8 h9 h10 h11 h15 h16 h18 _ h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 hhv hrm => by
          simp only [s₂, State.setReg_regs_ne _ _ h30, State.setReg_regs_ne _ _ h21]
          exact hregs₁ r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h22 h23 h24 h25 h26 h27 h28 h29 hhv hrm,
        harrs₁⟩
    · -- Case `L = i₁ :: i₂ :: rest`: `s₁.regs 30 = 2`
      obtain ⟨hr30_1, hr19_1, hr21_1⟩ := hinv₁
      have heval_30_1 : (exprEq (.reg 30) (.const 1)).eval w s₁ = some 0 := by
        simp [exprEq, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr30_1, h0_w, h1_w, hw2]
      have heval_30_0 : (exprEq (.reg 30) (.const 0)).eval w s₁ = some 0 := by
        simp [exprEq, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr30_1, h0_w, hw2]
      have hex_br : Exec w
          (.ite (exprEq (.reg 30) (.const 1))
            (.seq (.assign 21 (.const idx.1)) (.assign 30 (.const 2)))
            (.ite (exprEq (.reg 30) (.const 0))
              (.seq (.assign 19 (.const idx.1)) (.assign 30 (.const 1)))
              .skip)) s₁ s₁ _ :=
        .ite_false heval_30_1 (.ite_false heval_30_0 (.skip s₁))
      refine ⟨s₁, _, .seq hex₁ (.ite_true heval_cond h1_ne hex_br),
        by simp only [exprAnd, exprEq, Expr.cost]; omega,
        hs₁, ⟨hr30_1, hr19_1, hr21_1⟩,
        fun r' h6 h7 h8 h9 h10 h11 h15 h16 h18 _ _ h22 h23 h24 h25 h26 h27 h28 h29 _ hhv hrm =>
          hregs₁ r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h22 h23 h24 h25 h26 h27 h28 h29 hhv hrm,
        harrs₁⟩

/-- Unrolled loop scanning rays `i .. i + rem - 1` of star `a` to find two active good rays. -/
def findTwoGoodRaysSliceCmd (r l a s i : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (findTwoGoodRaysOneCmd r l a s i)
      (findTwoGoodRaysSliceCmd r l a s (i + 1) rem)

theorem findTwoGoodRaysSliceCmd_exec {w h n : ℕ} (r l a sIdx : ℕ) {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {c : Fin n} (Qs : List (List (Fin n)))
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (hQs_len : Qs.length = sIdx)
    (hQs_valid : ∀ Q ∈ Qs, W.IsHPath Q)
    (hP_valid : ∀ idx : Fin l, W.IsStarRay c (rays idx))
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hr_w : r < 2 ^ w) (hl_w : l < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w) :
    ∀ (rem i : ℕ) (_hi : i + rem = l) {s : State},
      WallStateHolds W s →
      (∀ m (hm : m < Qs.length), s.arrs (qPathArr m) = (Qs[m]'hm).map Fin.val) →
      (∀ idx : Fin l, s.arrs (starRayArr l a idx.1) = (rays idx).map Fin.val) →
      (∀ idx : Fin l, s.regs (regRayActive l a idx.1) = if act idx then 1 else 0) →
      goodScanInv s (((List.finRange l).take i).filter
        (fun idx : Fin l => act idx && W.isGoodRay r Qs (rays idx))) →
      ∃ s' t,
        Exec w (findTwoGoodRaysSliceCmd r l a sIdx i rem) s s' t ∧
        t ≤ ((79 * n + 242500) * sIdx + 30) * rem + 1 ∧
        WallStateHolds W s' ∧
        goodScanInv s' ((List.finRange l).filter
          (fun idx : Fin l => act idx && W.isGoodRay r Qs (rays idx))) ∧
        (∀ r' : Reg, r' ≠ 6 → r' ≠ 7 → r' ≠ 8 → r' ≠ 9 → r' ≠ 10 → r' ≠ 11 →
          r' ≠ 15 → r' ≠ 16 → r' ≠ 18 → r' ≠ 19 → r' ≠ 21 → r' ≠ 22 → r' ≠ 23 →
          r' ≠ 24 → r' ≠ 25 → r' ≠ 26 → r' ≠ 27 → r' ≠ 28 → r' ≠ 29 → r' ≠ 30 →
          (∀ m < l, r' ≠ regRayHitVert m ∧ r' ≠ regRayMeets m) → s'.regs r' = s.regs r') ∧
        (∀ arr : Arr, arr ≠ qMemArr → arr ≠ tmpPathArr1 →
          (∀ m < l, arr ≠ hitPrefArr m) → s'.arrs arr = s.arrs arr)
  | 0, i, hi, s, hs, _, _, _, hinv => by
    have hi_eq : i = l := by omega
    subst hi_eq
    have htake : (List.finRange i).take i = List.finRange i :=
      List.take_of_length_le (by simp)
    rw [htake] at hinv
    exact ⟨s, 1, .skip s, by simp, hs, hinv,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ => rfl⟩
  | rem + 1, i, hi, s, hs, hqArr, hpArr, hact, hinv => by
    have hi_lt : i < l := by omega
    let idx : Fin l := ⟨i, hi_lt⟩
    let goodPred : Fin l → Bool := fun j => act j && W.isGoodRay r Qs (rays j)
    rcases findTwoGoodRaysOneCmd_exec W h2 he hW Qs rays act idx
        (((List.finRange l).take i).filter goodPred)
        hQs_len hQs_valid (hP_valid idx)
        hw2 hn_w hr_w hl_w h4h4_w hloc_w hs hqArr (hpArr idx) (hact idx) hinv with
      ⟨s₁, t₁, hex₁, ht₁, hs₁, hinv₁, hregs₁, harrs₁⟩
    have hinv₁' : goodScanInv s₁ (((List.finRange l).take (i + 1)).filter goodPred) := by
      rw [finRange_take_succ l i hi_lt, List.filter_append]
      change goodScanInv s₁
        (List.filter goodPred (List.take i (List.finRange l)) ++ List.filter goodPred [idx])
      cases hgp : goodPred idx <;> simpa [List.filter, hgp, goodPred] using hinv₁
    rcases findTwoGoodRaysSliceCmd_exec r l a sIdx W h2 he hW Qs rays act
        hQs_len hQs_valid hP_valid hw2 hn_w hr_w hl_w h4h4_w hloc_w
        rem (i + 1) (by omega) (s := s₁) hs₁
        (fun m hm => by
          rw [harrs₁ (qPathArr m)
            (by dsimp [qPathArr, qMemArr, Arr]; omega)
            (by dsimp [qPathArr, tmpPathArr1, Arr]; omega)
            (by dsimp [qPathArr, hitPrefArr, Arr]; omega)]
          exact hqArr m hm)
        (fun j => by
          rw [harrs₁ (starRayArr l a j.1)
            (by dsimp [starRayArr, qMemArr, Arr]; omega)
            (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
            (by dsimp [starRayArr, hitPrefArr, Arr]; omega)]
          exact hpArr j)
        (fun j => by
          rw [hregs₁ (regRayActive l a j.1)
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
            (by dsimp [regRayActive, regRayHitVert, Reg]; omega)
            (by dsimp [regRayActive, regRayMeets, Reg]; omega)]
          exact hact j)
        hinv₁' with
      ⟨s₂, t₂, hex₂, ht₂, hs₂, hinv₂, hregs₂, harrs₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by simp only [Nat.mul_add, Nat.mul_one]; omega,
      hs₂, hinv₂,
      fun r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h19 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 hray =>
        (hregs₂ r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h19 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 hray).trans
          (hregs₁ r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h19 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30
            (hray i hi_lt).1 (hray i hi_lt).2),
      fun arr hqm htmp1 hpref =>
        (harrs₂ arr hqm htmp1 hpref).trans (harrs₁ arr hqm htmp1 (hpref i hi_lt))⟩

/-- Find the first two active good rays of star `a`, storing their ray indices in `r_19` and `r_21`. -/
def findTwoGoodRaysCmd (r l a s : ℕ) : Cmd :=
  .seq (.assign 30 (.const 0))
    (findTwoGoodRaysSliceCmd r l a s 0 l)

theorem filter_activeRayList {l n : ℕ} (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (p : List (Fin n) → Bool) :
    (activeRayList rays act).filter p =
      ((List.finRange l).filter (fun idx => act idx && p (rays idx))).map rays := by
  unfold activeRayList
  rw [List.filter_map, List.filter_filter]
  congr 2
  funext idx
  exact Bool.and_comm _ _

/-- Case B command of Step (7.5): finds the first two active good rays of star `a` and joins them
into `qPathArr s`. -/
def caseBCmd (r l a s : ℕ) : Cmd :=
  .seq (findTwoGoodRaysCmd r l a s)
    (.seq (copyArrByIdxSliceCmd (starRayArr l a) 19 tmpPathArr1 0 l)
      (.seq (copyArrByIdxSliceCmd (starRayArr l a) 21 tmpPathArr2 0 l)
        (.seq (reverseArrCmd tmpPathArr1 tmpPathArr3)
          (concatOverlapArrCmd tmpPathArr3 tmpPathArr2 (qPathArr s)))))

theorem caseBCmd_exec {w h n r l a sIdx : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {c : Fin n} (Qs : List (List (Fin n)))
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (hQs_len : Qs.length = sIdx)
    (hQs_valid : ∀ Q ∈ Qs, W.IsHPath Q)
    (hP_valid : ∀ idx : Fin l, W.IsStarRay c (rays idx))
    (hgood_ge : 2 ≤ ((activeRayList rays act).filter (W.isGoodRay r Qs)).length)
    {s : State}
    (hw2 : 2 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w) (hr_w : r < 2 ^ w) (hl_w : l < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hqArr : ∀ m (hm : m < Qs.length), s.arrs (qPathArr m) = (Qs[m]'hm).map Fin.val)
    (hpArr : ∀ idx : Fin l, s.arrs (starRayArr l a idx.1) = (rays idx).map Fin.val)
    (hact : ∀ idx : Fin l, s.regs (regRayActive l a idx.1) = if act idx then 1 else 0) :
    let good := (activeRayList rays act).filter (W.isGoodRay r Qs)
    let Q_new := WallOfHeight.joinTwoRays (good.headD []) ((good.drop 1).headD [])
    let Qs' := Qs ++ [Q_new]
    ∃ s' t,
      Exec w (caseBCmd r l a sIdx) s s' t ∧
      t ≤ ((79 * n + 242500) * sIdx + 30) * l + 2 * (l * (22 * n + 16)) + 62 * n + 40 ∧
      WallStateHolds W s' ∧
      (∀ m (hm : m < Qs'.length), s'.arrs (qPathArr m) = (Qs'[m]'hm).map Fin.val) ∧
      (∀ r' : Reg, r' ≠ 6 → r' ≠ 7 → r' ≠ 8 → r' ≠ 9 → r' ≠ 10 → r' ≠ 11 →
        r' ≠ 15 → r' ≠ 16 → r' ≠ 18 → r' ≠ 19 → r' ≠ 21 → r' ≠ 22 → r' ≠ 23 →
        r' ≠ 24 → r' ≠ 25 → r' ≠ 26 → r' ≠ 27 → r' ≠ 28 → r' ≠ 29 → r' ≠ 30 →
        (∀ m < l, r' ≠ regRayHitVert m ∧ r' ≠ regRayMeets m) → s'.regs r' = s.regs r') ∧
      (∀ arr : Arr, arr ≠ qMemArr → arr ≠ tmpPathArr1 → arr ≠ tmpPathArr2 →
        arr ≠ tmpPathArr3 → arr ≠ qPathArr sIdx →
        (∀ m < l, arr ≠ hitPrefArr m) → s'.arrs arr = s.arrs arr) := by
  intro good Q_new Qs'
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  -- Step 1: r_30 := 0 and findTwoGoodRaysSliceCmd
  let s₀ := s.setReg 30 0
  have hex₀ : Exec w (.assign 30 (.const 0)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hs₀ : WallStateHolds W s₀ :=
    hs.of_preserve (by simp [s₀]) (by simp [s₀]) (by simp [s₀]) (by simp [s₀]) (by simp [s₀])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rcases findTwoGoodRaysSliceCmd_exec r l a sIdx W h2 he hW Qs rays act
      hQs_len hQs_valid hP_valid hw2 hn_w hr_w hl_w h4h4_w hloc_w
      l 0 (Nat.zero_add l) (s := s₀) hs₀
      (fun m hm => by simpa [s₀] using hqArr m hm)
      (fun idx => by simpa [s₀] using hpArr idx)
      (fun idx => by
        simp only [s₀, State.setReg_regs_ne _ _
          (by dsimp [regRayActive, Reg]; omega : regRayActive l a idx.1 ≠ 30)]
        exact hact idx)
      (by simp [goodScanInv, s₀]) with
    ⟨s₁, t₁, hex₁, ht₁, hs₁, hinv₁, hregs₁, harrs₁⟩
  -- Extract the first two good ray indices `i₁, i₂` from `hgood_ge`
  have hgood_eq : good =
      ((List.finRange l).filter (fun idx : Fin l => act idx && W.isGoodRay r Qs (rays idx))).map rays :=
    filter_activeRayList rays act (W.isGoodRay r Qs)
  generalize hL_def :
    (List.finRange l).filter (fun idx : Fin l => act idx && W.isGoodRay r Qs (rays idx)) = L
    at hinv₁ hgood_eq
  have hL_len : 2 ≤ L.length := by
    have hlen : good.length = L.length := by rw [hgood_eq, List.length_map]
    have hge : 2 ≤ good.length := hgood_ge
    omega
  rcases L with _ | ⟨i₁, _ | ⟨i₂, rest⟩⟩
  · simp at hL_len
  · simp at hL_len
  obtain ⟨_, hr19_1, hr21_1⟩ := hinv₁
  have hhead_good : good.headD [] = rays i₁ := by simp [hgood_eq]
  have hdrop_good : (good.drop 1).headD [] = rays i₂ := by simp [hgood_eq]
  -- Bounds on `rays i₁` and `rays i₂`
  obtain ⟨hneP₁, _, _, hndP₁, _, _, _, _⟩ := hP_valid i₁
  obtain ⟨hneP₂, _, _, hndP₂, _, _, _, _⟩ := hP_valid i₂
  have hlenP₁ : (rays i₁).length ≤ n := length_le_of_nodup_fin hndP₁
  have hlenP₂ : (rays i₂).length ≤ n := length_le_of_nodup_fin hndP₂
  -- Step 2: copy `starRayArr l a i₁.1` to `tmpPathArr1`
  have hpArr₁_i₁ : s₁.arrs (starRayArr l a i₁.1) = (rays i₁).map Fin.val := by
    rw [harrs₁ (starRayArr l a i₁.1)
      (by dsimp [starRayArr, qMemArr, Arr]; omega)
      (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
      (fun m _ => by dsimp [starRayArr, hitPrefArr, Arr]; omega)]
    exact hpArr i₁
  rcases copyArrByIdxSliceCmd_exec (starRayArr l a) 19 tmpPathArr1
      (fun j _ => by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
      (by decide) (by decide) (by decide) (by decide) i₁ h1_w hn_w hl_w l 0 (Nat.zero_add l)
      (s := s₁) hr19_1
      (by simp [hpArr₁_i₁, hlenP₁])
      (fun v hv => by rw [hpArr₁_i₁] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
    ⟨s₂, t₂, hex₂, ht₂, htmp1_2, hregs₂, harrs₂⟩
  rw [if_pos (Nat.zero_le _), hpArr₁_i₁] at htmp1_2
  -- Step 3: copy `starRayArr l a i₂.1` to `tmpPathArr2`
  have hpArr₂_i₂ : s₂.arrs (starRayArr l a i₂.1) = (rays i₂).map Fin.val := by
    rw [harrs₂ (starRayArr l a i₂.1) (by dsimp [starRayArr, tmpPathArr1, Arr]; omega),
      harrs₁ (starRayArr l a i₂.1)
        (by dsimp [starRayArr, qMemArr, Arr]; omega)
        (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
        (fun m _ => by dsimp [starRayArr, hitPrefArr, Arr]; omega)]
    exact hpArr i₂
  have hr21_2 : s₂.regs 21 = i₂.1 := by
    rw [hregs₂ 21 (by decide) (by decide) (by decide) (by decide), hr21_1]
  rcases copyArrByIdxSliceCmd_exec (starRayArr l a) 21 tmpPathArr2
      (fun j _ => by dsimp [starRayArr, tmpPathArr2, Arr]; omega)
      (by decide) (by decide) (by decide) (by decide) i₂ h1_w hn_w hl_w l 0 (Nat.zero_add l)
      (s := s₂) hr21_2
      (by simp [hpArr₂_i₂, hlenP₂])
      (fun v hv => by rw [hpArr₂_i₂] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
    ⟨s₃, t₃, hex₃, ht₃, htmp2_3, hregs₃, harrs₃⟩
  rw [if_pos (Nat.zero_le _), hpArr₂_i₂] at htmp2_3
  -- Step 4: reverse `tmpPathArr1` into `tmpPathArr3`
  have htmp1_3 : s₃.arrs tmpPathArr1 = (rays i₁).map Fin.val := by
    rw [harrs₃ tmpPathArr1 (by decide), htmp1_2]
  rcases reverseArrCmd_exec tmpPathArr1 tmpPathArr3 (by decide) (s := s₃) h1_w
      (by simp [htmp1_3]; omega)
      (fun v hv => by rw [htmp1_3] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
    ⟨s₄, t₄, hex₄, ht₄, htmp3_4, hregs₄, harrs₄⟩
  rw [htmp1_3, ← List.map_reverse] at htmp3_4
  -- Step 5: concatOverlapArrCmd tmpPathArr3 tmpPathArr2 (qPathArr sIdx)
  have htmp2_4 : s₄.arrs tmpPathArr2 = (rays i₂).map Fin.val := by
    rw [harrs₄ tmpPathArr2 (by decide), htmp2_3]
  rcases concatOverlapArrCmd_exec tmpPathArr3 tmpPathArr2 (qPathArr sIdx)
      (by dsimp [tmpPathArr3, qPathArr, Arr]; omega)
      (by dsimp [tmpPathArr2, qPathArr, Arr]; omega)
      (s := s₄) h1_w
      (by simp [htmp3_4, hneP₁])
      (by simp [htmp3_4, htmp2_4]; omega)
      (by simp [htmp3_4]; omega)
      (by simp [htmp2_4]; omega)
      (fun v hv => by rw [htmp3_4] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega)
      (fun v hv => by rw [htmp2_4] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
    ⟨s₅, t₅, hex₅, ht₅, hqNew_5, hregs₅, harrs₅⟩
  rw [htmp3_4, htmp2_4, ← concatOverlap_map] at hqNew_5
  have hqNew_eq : concatOverlap (rays i₁).reverse (rays i₂) = Q_new := by
    dsimp [Q_new, WallOfHeight.joinTwoRays]
    rw [hhead_good, hdrop_good]
  rw [hqNew_eq] at hqNew_5
  simp only [htmp1_3, htmp3_4, htmp2_4, List.length_map, List.length_reverse] at ht₄ ht₅
  have hs₅ : WallStateHolds W s₅ :=
    hs₁.of_preserve
      (by rw [hregs₅ 0 (by decide) (by decide) (by decide) (by decide) (by decide),
          hregs₄ 0 (by decide) (by decide) (by decide),
          hregs₃ 0 (by decide) (by decide) (by decide) (by decide),
          hregs₂ 0 (by decide) (by decide) (by decide) (by decide)])
      (by rw [hregs₅ 3 (by decide) (by decide) (by decide) (by decide) (by decide),
          hregs₄ 3 (by decide) (by decide) (by decide),
          hregs₃ 3 (by decide) (by decide) (by decide) (by decide),
          hregs₂ 3 (by decide) (by decide) (by decide) (by decide)])
      (by rw [hregs₅ 12 (by decide) (by decide) (by decide) (by decide) (by decide),
          hregs₄ 12 (by decide) (by decide) (by decide),
          hregs₃ 12 (by decide) (by decide) (by decide) (by decide),
          hregs₂ 12 (by decide) (by decide) (by decide) (by decide)])
      (by rw [hregs₅ 13 (by decide) (by decide) (by decide) (by decide) (by decide),
          hregs₄ 13 (by decide) (by decide) (by decide),
          hregs₃ 13 (by decide) (by decide) (by decide) (by decide),
          hregs₂ 13 (by decide) (by decide) (by decide) (by decide)])
      (by rw [hregs₅ 14 (by decide) (by decide) (by decide) (by decide) (by decide),
          hregs₄ 14 (by decide) (by decide) (by decide),
          hregs₃ 14 (by decide) (by decide) (by decide) (by decide),
          hregs₂ 14 (by decide) (by decide) (by decide) (by decide)])
      (by rw [harrs₅ wallEncArr (by dsimp [wallEncArr, qPathArr, Arr]; omega),
          harrs₄ wallEncArr (by decide), harrs₃ wallEncArr (by decide), harrs₂ wallEncArr (by decide)])
      (by rw [harrs₅ locArr (by dsimp [locArr, qPathArr, Arr]; omega),
          harrs₄ locArr (by decide), harrs₃ locArr (by decide), harrs₂ locArr (by decide)])
      (by rw [harrs₅ wallMemArr (by dsimp [wallMemArr, qPathArr, Arr]; omega),
          harrs₄ wallMemArr (by decide), harrs₃ wallMemArr (by decide), harrs₂ wallMemArr (by decide)])
      (by rw [harrs₅ edgeOffArr (by dsimp [edgeOffArr, qPathArr, Arr]; omega),
          harrs₄ edgeOffArr (by decide), harrs₃ edgeOffArr (by decide), harrs₂ edgeOffArr (by decide)])
      (by rw [harrs₅ edgeLenArr (by dsimp [edgeLenArr, qPathArr, Arr]; omega),
          harrs₄ edgeLenArr (by decide), harrs₃ edgeLenArr (by decide), harrs₂ edgeLenArr (by decide)])
      (by rw [harrs₅ edgeU1Arr (by dsimp [edgeU1Arr, qPathArr, Arr]; omega),
          harrs₄ edgeU1Arr (by decide), harrs₃ edgeU1Arr (by decide), harrs₂ edgeU1Arr (by decide)])
      (by rw [harrs₅ edgeU2Arr (by dsimp [edgeU2Arr, qPathArr, Arr]; omega),
          harrs₄ edgeU2Arr (by decide), harrs₃ edgeU2Arr (by decide), harrs₂ edgeU2Arr (by decide)])
      (by rw [harrs₅ horizEdgeIdxArr (by dsimp [horizEdgeIdxArr, qPathArr, Arr]; omega),
          harrs₄ horizEdgeIdxArr (by decide), harrs₃ horizEdgeIdxArr (by decide), harrs₂ horizEdgeIdxArr (by decide)])
      (by rw [harrs₅ vertEdgeIdxArr (by dsimp [vertEdgeIdxArr, qPathArr, Arr]; omega),
          harrs₄ vertEdgeIdxArr (by decide), harrs₃ vertEdgeIdxArr (by decide), harrs₂ vertEdgeIdxArr (by decide)])
  refine ⟨s₅, _, .seq (.seq hex₀ hex₁) (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hs₅, ?_, ?_, ?_⟩
  · intro m hm
    have hlen_Qs' : Qs'.length = sIdx + 1 := by simp [Qs', hQs_len]
    by_cases hm_lt : m < sIdx
    · have hm_Qs : m < Qs.length := by omega
      have hne_m : qPathArr m ≠ qPathArr sIdx := by dsimp [qPathArr, Arr]; omega
      rw [harrs₅ (qPathArr m) hne_m,
        harrs₄ (qPathArr m) (by dsimp [qPathArr, tmpPathArr3, Arr]; omega),
        harrs₃ (qPathArr m) (by dsimp [qPathArr, tmpPathArr2, Arr]; omega),
        harrs₂ (qPathArr m) (by dsimp [qPathArr, tmpPathArr1, Arr]; omega),
        harrs₁ (qPathArr m) (by dsimp [qPathArr, qMemArr, Arr]; omega)
          (by dsimp [qPathArr, tmpPathArr1, Arr]; omega)
          (fun _ _ => by dsimp [qPathArr, hitPrefArr, Arr]; omega)]
      simp only [s₀, State.setReg_arrs, hqArr m hm_Qs, Qs', List.getElem_append_left hm_Qs]
    · have hm_eq : m = sIdx := by omega
      subst hm_eq
      rw [hqNew_5]
      simp [Qs', hQs_len]
  · intro r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h19 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 hray
    rw [hregs₅ r' h7 h8 h9 h10 h11, hregs₄ r' h7 h9 h11,
      hregs₃ r' h7 h8 h9 h11, hregs₂ r' h7 h8 h9 h11,
      hregs₁ r' h6 h7 h8 h9 h10 h11 h15 h16 h18 h19 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 hray]
    simp [s₀, h30]
  · intro arr hqm htmp1 htmp2 htmp3 hqs hpref
    rw [harrs₅ arr hqs, harrs₄ arr htmp3, harrs₃ arr htmp2, harrs₂ arr htmp1,
      harrs₁ arr hqm htmp1 hpref]
    rfl

end GraphMinor.Compute


