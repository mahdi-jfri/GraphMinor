module

public import GraphMinor.Compute.Algorithm77Step75
public import GraphMinor.Compute.Algorithm77Prog76Full

/-!
# Word RAM Implementation of Step (7.5), Part 1: Filtering and Ray-Hit Precomputation

This file implements the first half of the Word RAM subroutines for Step (7.5) of Graph Minors XIII,
(7.7) (`Algorithm77Step75.lean`):

1. **Active ray lists and vertex-avoidance filtering (`Section 1`):**
   - Represents each star `a`'s active ray list as
     `activeRayList (st.rays a) (act a) = ((List.finRange l).filter (act a)).map (st.rays a)`,
     where `regRayActive l a i` stores `if act a i then 1 else 0` while `starRayArr l a i` remains
     read-only throughout Step (7.5).
   - Implements `initAllStarsActiveSliceCmd` and `filterAllStarsAvoidSliceCmd` matching
     `WallOfHeight.starRayListOfFin` and `WallOfHeight.filterAvoidVertex`.
2. **Path membership indicator and ray-hit prefixes (`Section 2`):**
   - Populates `qMemArr` with the indicator of `Q.toFinset` (`computeQMemCmd`).
   - Computes `hitPrefArr i = (WallOfHeight.rayHitPrefix Q (st.rays a i)).map Fin.val`,
     `regRayHitVert i`, and `regRayMeets i` for all `i < l` (`computeAllRayHitsSliceCmd`).
3. **Scanning `Q` to build `hitsOnQ` (`Section 3`):**
   - Implements `findHitRaySliceCmd`, `scanHitsOnQLoop`, and `computeHitsOnQCmd`, populating
     `hitIdxArr` and `hitRayIdxArr` with the hit positions and ray indices of
     `WallOfHeight.hitsOnQ (activeRayList (st.rays a) act) Q`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

set_option linter.deprecated false

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges

/-! ### Section 1: Active Ray Lists and Vertex-Avoidance Filtering -/

/-- The sublist of rays of a star `rays : Fin l → List (Fin n)` selected by an active mask
`act : Fin l → Bool`. -/
def activeRayList {l n : ℕ} (rays : Fin l → List (Fin n)) (act : Fin l → Bool) :
    List (List (Fin n)) :=
  ((List.finRange l).filter act).map rays

theorem activeRayList_true {l n : ℕ} (rays : Fin l → List (Fin n)) :
    activeRayList rays (fun _ => true) = WallOfHeight.starRayListOfFin rays := by
  simp [activeRayList, WallOfHeight.starRayListOfFin]

theorem filterAvoidVertex_activeRayList {l n : ℕ} (w : Fin n)
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool) :
    WallOfHeight.filterAvoidVertex w (activeRayList rays act) =
      activeRayList rays (fun i => act i && decide (w ∉ rays i)) := by
  unfold WallOfHeight.filterAvoidVertex activeRayList
  rw [List.filter_map, List.filter_filter]
  congr 2
  ext i
  exact Bool.and_comm _ _

/-- Initialize `regRayActive l a i := 1` for `i, i + 1, ..., i + rem - 1`. -/
def initStarActiveSliceCmd (l a i : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (.assign (regRayActive l a i) (.const 1))
      (initStarActiveSliceCmd l a (i + 1) rem)

theorem initStarActiveSliceCmd_exec {w l a : ℕ} (hw1 : 1 < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = l) {s : State}
      (_hprev : ∀ j : Fin l, j.1 < idx → s.regs (regRayActive l a j.1) = 1),
      ∃ s' t,
        Exec w (initStarActiveSliceCmd l a idx rem) s s' t ∧
        t ≤ 2 * rem + 1 ∧
        (∀ j : Fin l, s'.regs (regRayActive l a j.1) = 1) ∧
        (∀ r : Reg, (∀ j < l, r ≠ regRayActive l a j) → s'.regs r = s.regs r) ∧
        s'.arrs = s.arrs
  | 0, idx, hrem, s, hprev => by
    refine ⟨s, 1, .skip s, by omega, fun j => hprev j (by have := j.2; omega),
      fun _ _ => rfl, rfl⟩
  | rem + 1, idx, hrem, s, hprev => by
    have hi_lt : idx < l := by omega
    let s₁ := s.setReg (regRayActive l a idx) 1
    have hex₁ : Exec w (.assign (regRayActive l a idx) (.const 1)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw1])
    have hprev₁ : ∀ j : Fin l, j.1 < idx + 1 → s₁.regs (regRayActive l a j.1) = 1 := by
      intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
      · simp only [s₁, State.setReg_regs_ne _ _
          (by dsimp [regRayActive, Reg]; omega : regRayActive l a j.1 ≠ regRayActive l a idx)]
        exact hprev j hlt
      · simp [s₁, heq]
    rcases initStarActiveSliceCmd_exec hw1 rem (idx + 1) (by omega) hprev₁ with
      ⟨s₂, t₂, hex₂, ht₂, hall₂, hregs₂, harrs₂⟩
    refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hall₂, ?_, harrs₂⟩
    intro r hr
    rw [hregs₂ r hr]
    simp [s₁, hr idx hi_lt]

/-- Initialize `regRayActive l a i := 1` for all `i < l` and `a_idx ≤ a < a_idx + rem`. -/
def initAllStarsActiveSliceCmd (l a_idx : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (initStarActiveSliceCmd l a_idx 0 l)
      (initAllStarsActiveSliceCmd l (a_idx + 1) rem)

theorem initAllStarsActiveSliceCmd_exec {w k l : ℕ} (hw1 : 1 < 2 ^ w) :
    ∀ (rem a_idx : ℕ) (_hrem : a_idx + rem = k) {s : State}
      (_hprev : ∀ a : Fin k, a.1 < a_idx → ∀ i : Fin l, s.regs (regRayActive l a.1 i.1) = 1),
      ∃ s' t,
        Exec w (initAllStarsActiveSliceCmd l a_idx rem) s s' t ∧
        t ≤ rem * (2 * l + 1) + 1 ∧
        (∀ a : Fin k, ∀ i : Fin l, s'.regs (regRayActive l a.1 i.1) = 1) ∧
        (∀ r : Reg, (∀ a < k, ∀ i < l, r ≠ regRayActive l a i) → s'.regs r = s.regs r) ∧
        s'.arrs = s.arrs
  | 0, a_idx, hrem, s, hprev => by
    refine ⟨s, 1, .skip s, by omega, fun a i => hprev a (by have := a.2; omega) i,
      fun _ _ => rfl, rfl⟩
  | rem + 1, a_idx, hrem, s, hprev => by
    have ha_lt : a_idx < k := by omega
    rcases initStarActiveSliceCmd_exec (a := a_idx) hw1 l 0 (Nat.zero_add l) (s := s)
        (fun _ hj => False.elim (Nat.not_lt_zero _ hj)) with
      ⟨s₁, t₁, hex₁, ht₁, hall₁, hregs₁, harrs₁⟩
    have hprev₁ : ∀ a : Fin k, a.1 < a_idx + 1 → ∀ i : Fin l,
        s₁.regs (regRayActive l a.1 i.1) = 1 := by
      intro a ha i
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ha) with hlt | heq
      · rw [hregs₁ (regRayActive l a.1 i.1) (fun j hj => by
          intro hcol
          have := (regRayActive_inj i.2 hj hcol).1
          omega)]
        exact hprev a hlt i
      · subst heq
        exact hall₁ i
    rcases initAllStarsActiveSliceCmd_exec hw1 rem (a_idx + 1) (by omega) hprev₁ with
      ⟨s₂, t₂, hex₂, ht₂, hall₂, hregs₂, harrs₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by calc t₁ + t₂ ≤ (2 * l + 1) + (rem * (2 * l + 1) + 1) := by omega
           _ = (rem + 1) * (2 * l + 1) + 1 := by ring,
      hall₂,
      fun r hr => by rw [hregs₂ r hr, hregs₁ r (fun j hj => hr a_idx ha_lt j hj)],
      harrs₂.trans harrs₁⟩

/-- Filter ray `i` of star `a` to avoid the vertex in `regW`: scans `starRayArr l a i` using
`findFirstEqLoop` and multiplies `regRayActive l a i` by `r_8 == len (starRayArr l a i)`. -/
def filterOneRayAvoidCmd (l a i : ℕ) (regW : Reg) : Cmd :=
  .seq (.assign 8 (.const 0))
    (.seq (.assign 10 (.const 1))
      (.seq (findFirstEqLoop (starRayArr l a i) regW)
        (.assign (regRayActive l a i)
          (.op .mul (.reg (regRayActive l a i))
            (exprEq (.reg 8) (.len (starRayArr l a i)))))))

theorem filterOneRayAvoidCmd_exec {w n l a i : ℕ} (regW : Reg)
    (hne_w8 : regW ≠ 8) (hne_w10 : regW ≠ 10) (hne_w11 : regW ≠ 11)
    (v_avoid : Fin n) (P : List (Fin n)) (b : Bool)
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hP_w : P.length < 2 ^ w)
    (hsrc : s.arrs (starRayArr l a i) = P.map Fin.val)
    (hrw : s.regs regW = v_avoid.1)
    (hact : s.regs (regRayActive l a i) = if b then 1 else 0) :
    ∃ s' t,
      Exec w (filterOneRayAvoidCmd l a i regW) s s' t ∧
      t ≤ 23 * P.length + 25 ∧
      s'.regs (regRayActive l a i) = (if (b && decide (v_avoid ∉ P)) then 1 else 0) ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 10 → r ≠ 11 → r ≠ regRayActive l a i → s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 8 0
  have hex₁ : Exec w (.assign 8 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 10 1
  have hex₂ : Exec w (.assign 10 (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  rcases findFirstEqLoop_exec (starRayArr l a i) regW hne_w8 hne_w10 hne_w11 v_avoid hw1 hn_w
      P 0 (s := s₂)
      (by simp [s₂, s₁, hsrc, hP_w])
      (by simp [s₂, s₁, hsrc])
      (fun j hj => by
        simp only [s₂, s₁, State.setReg_arrs, hsrc, Nat.zero_add]
        rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_map])
      (by simp [s₂, s₁]) (by simp [s₂])
      (by simp [s₂, s₁, hne_w8, hne_w10, hrw]) with
    ⟨s₃, t₃, hex₃, ht₃, hlen₃, _, hregs₃, harrs₃⟩
  have hsrc₃ : s₃.arrs (starRayArr l a i) = P.map Fin.val := by
    rw [harrs₃ (starRayArr l a i)]; simp [s₂, s₁, hsrc]
  have hlen₃' : s₃.regs 8 + (suffixFrom v_avoid P).length = P.length := by
    simpa [s₂, s₁, hsrc] using hlen₃
  have hr8_w : s₃.regs 8 < 2 ^ w := by omega
  have hact₃ : s₃.regs (regRayActive l a i) = if b then 1 else 0 := by
    rw [hregs₃ (regRayActive l a i)
      (by dsimp [regRayActive, Reg]; omega)
      (by dsimp [regRayActive, Reg]; omega)
      (by dsimp [regRayActive, Reg]; omega)]
    simp [s₂, s₁,
      State.setReg_regs_ne _ _ (by dsimp [regRayActive, Reg]; omega : regRayActive l a i ≠ 10),
      State.setReg_regs_ne _ _ (by dsimp [regRayActive, Reg]; omega : regRayActive l a i ≠ 8),
      hact]
  have hr8_eq_iff : s₃.regs 8 = P.length ↔ v_avoid ∉ P := by
    constructor
    · intro heq hmem
      have hpos : 0 < (suffixFrom v_avoid P).length :=
        List.length_pos_iff.mpr (suffixFrom_ne_nil hmem)
      omega
    · intro hnot
      have hnil : suffixFrom v_avoid P = [] := suffixFrom_eq_nil_of_not_mem hnot
      simp [hnil] at hlen₃'
      exact hlen₃'
  have heval_r8 : (Expr.reg 8).eval w s₃ = some (s₃.regs 8) := by
    simp [Expr.eval, checkWord, hr8_w]
  have heval_len : (Expr.len (starRayArr l a i)).eval w s₃ = some P.length := by
    simp [Expr.eval, checkWord, hsrc₃, hP_w]
  have heval_eq : (exprEq (.reg 8) (.len (starRayArr l a i))).eval w s₃ =
      some (if v_avoid ∉ P then 1 else 0) := by
    rw [eval_exprEq hw1 heval_r8 heval_len]
    exact congrArg some (if_congr hr8_eq_iff rfl rfl)
  have heval_act : (Expr.reg (regRayActive l a i)).eval w s₃ = some (if b then 1 else 0) := by
    cases b <;> simp [Expr.eval, checkWord, hact₃, hw1, h0_w]
  let newAct : ℕ := if (b && decide (v_avoid ∉ P)) then 1 else 0
  have heval_mul :
      (Expr.op .mul (.reg (regRayActive l a i))
        (exprEq (.reg 8) (.len (starRayArr l a i)))).eval w s₃ = some newAct := by
    have h := eval_op_mul heval_act heval_eq (by split_ifs <;> omega)
    have hmul_eq : (if b = true then 1 else 0) * (if v_avoid ∉ P then 1 else 0) = newAct := by
      dsimp [newAct]
      cases b <;> by_cases hv : v_avoid ∉ P <;> simp [hv]
    rwa [hmul_eq] at h
  let s₄ := s₃.setReg (regRayActive l a i) newAct
  have hex₄ : Exec w (.assign (regRayActive l a i)
      (.op .mul (.reg (regRayActive l a i))
        (exprEq (.reg 8) (.len (starRayArr l a i))))) s₃ s₄
      ((Expr.op .mul (.reg (regRayActive l a i))
        (exprEq (.reg 8) (.len (starRayArr l a i)))).cost + 1) :=
    .assign heval_mul
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by simp [exprEq, Expr.cost]; omega,
    by simp [s₄, newAct],
    fun r h8 h10 h11 hact_r => by
      simp only [s₄, State.setReg_regs_ne _ _ hact_r]
      rw [hregs₃ r h8 h10 h11]
      simp [s₂, s₁, h8, h10],
    by ext arr; simp [s₄, harrs₃ arr, s₂, s₁]⟩

/-- Filter rays `i, i + 1, ..., i + rem - 1` of star `a` to avoid the vertex in `regW`. -/
def filterStarAvoidSliceCmd (l a : ℕ) (regW : Reg) (i : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (filterOneRayAvoidCmd l a i regW)
      (filterStarAvoidSliceCmd l a regW (i + 1) rem)

theorem filterStarAvoidSliceCmd_exec {w n l a : ℕ} (regW : Reg)
    (hne_w8 : regW ≠ 8) (hne_w10 : regW ≠ 10) (hne_w11 : regW ≠ 11)
    (hne_wact : ∀ j < l, regW ≠ regRayActive l a j)
    (v_avoid : Fin n) (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hP_len : ∀ j : Fin l, (rays j).length ≤ n) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = l) {s : State}
      (_hsrc : ∀ j : Fin l, s.arrs (starRayArr l a j.1) = (rays j).map Fin.val)
      (_hrw : s.regs regW = v_avoid.1)
      (_hprev : ∀ j : Fin l, j.1 < idx →
        s.regs (regRayActive l a j.1) = if (act j && decide (v_avoid ∉ rays j)) then 1 else 0)
      (_htodo : ∀ j : Fin l, idx ≤ j.1 →
        s.regs (regRayActive l a j.1) = if act j then 1 else 0),
      ∃ s' t,
        Exec w (filterStarAvoidSliceCmd l a regW idx rem) s s' t ∧
        t ≤ rem * (23 * n + 25) + 1 ∧
        (∀ j : Fin l,
          s'.regs (regRayActive l a j.1) =
            if (act j && decide (v_avoid ∉ rays j)) then 1 else 0) ∧
        (∀ r : Reg, r ≠ 8 → r ≠ 10 → r ≠ 11 →
          (∀ j < l, r ≠ regRayActive l a j) → s'.regs r = s.regs r) ∧
        s'.arrs = s.arrs
  | 0, idx, hrem, s, _, _, hprev, _ => by
    refine ⟨s, 1, .skip s, by omega, fun j => hprev j (by have := j.2; omega),
      fun _ _ _ _ _ => rfl, rfl⟩
  | rem + 1, idx, hrem, s, hsrc, hrw, hprev, htodo => by
    have hi_lt : idx < l := by omega
    let i : Fin l := ⟨idx, hi_lt⟩
    have hPi_len : (rays i).length ≤ n := hP_len i
    rcases filterOneRayAvoidCmd_exec (l := l) (a := a) (i := idx) regW
        hne_w8 hne_w10 hne_w11 v_avoid (rays i) (act i)
        hw1 hn_w (by omega) (hsrc i) hrw (htodo i (by dsimp [i]; omega)) with
      ⟨s₁, t₁, hex₁, ht₁, hact₁, hregs₁, harrs₁⟩
    have ht₁_le : t₁ ≤ 23 * n + 25 := by omega
    have hsrc₁ : ∀ j : Fin l, s₁.arrs (starRayArr l a j.1) = (rays j).map Fin.val := by
      intro j; rw [harrs₁]; exact hsrc j
    have hrw₁ : s₁.regs regW = v_avoid.1 := by
      rw [hregs₁ regW hne_w8 hne_w10 hne_w11 (hne_wact idx hi_lt), hrw]
    have hprev₁ : ∀ j : Fin l, j.1 < idx + 1 →
        s₁.regs (regRayActive l a j.1) =
          if (act j && decide (v_avoid ∉ rays j)) then 1 else 0 := by
      intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
      · rw [hregs₁ (regRayActive l a j.1)
          (by dsimp [regRayActive, Reg]; omega)
          (by dsimp [regRayActive, Reg]; omega)
          (by dsimp [regRayActive, Reg]; omega)
          (by dsimp [regRayActive, Reg]; omega)]
        exact hprev j hlt
      · have hj_eq : j = i := Fin.ext heq
        subst hj_eq
        exact hact₁
    have htodo₁ : ∀ j : Fin l, idx + 1 ≤ j.1 →
        s₁.regs (regRayActive l a j.1) = if act j then 1 else 0 := by
      intro j hj
      rw [hregs₁ (regRayActive l a j.1)
        (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega)]
      exact htodo j (by omega)
    rcases filterStarAvoidSliceCmd_exec regW hne_w8 hne_w10 hne_w11 hne_wact v_avoid rays act
        hw1 hn_w hP_len rem (idx + 1) (by omega) hsrc₁ hrw₁ hprev₁ htodo₁ with
      ⟨s₂, t₂, hex₂, ht₂, hall₂, hregs₂, harrs₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by calc t₁ + t₂ ≤ (23 * n + 25) + (rem * (23 * n + 25) + 1) := by omega
           _ = (rem + 1) * (23 * n + 25) + 1 := by ring,
      hall₂,
      fun r h8 h10 h11 hact_r => by
        rw [hregs₂ r h8 h10 h11 hact_r, hregs₁ r h8 h10 h11 (hact_r idx hi_lt)],
      harrs₂.trans harrs₁⟩

/-- Filter all rays of stars `a_idx, a_idx + 1, ..., a_idx + rem - 1` to avoid the vertex in
`regW`. -/
def filterAllStarsAvoidSliceCmd (l : ℕ) (regW : Reg) (a_idx : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (filterStarAvoidSliceCmd l a_idx regW 0 l)
      (filterAllStarsAvoidSliceCmd l regW (a_idx + 1) rem)

theorem filterAllStarsAvoidSliceCmd_exec {w n k l : ℕ} (regW : Reg)
    (hne_w8 : regW ≠ 8) (hne_w10 : regW ≠ 10) (hne_w11 : regW ≠ 11)
    (hne_wact : ∀ a < k, ∀ j < l, regW ≠ regRayActive l a j)
    (v_avoid : Fin n) (rays : Fin k → Fin l → List (Fin n)) (act : Fin k → Fin l → Bool)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hP_len : ∀ a : Fin k, ∀ j : Fin l, (rays a j).length ≤ n) :
    ∀ (rem a_idx : ℕ) (_hrem : a_idx + rem = k) {s : State}
      (_hsrc : ∀ a : Fin k, ∀ j : Fin l, s.arrs (starRayArr l a.1 j.1) = (rays a j).map Fin.val)
      (_hrw : s.regs regW = v_avoid.1)
      (_hprev : ∀ a : Fin k, a.1 < a_idx → ∀ j : Fin l,
        s.regs (regRayActive l a.1 j.1) =
          if (act a j && decide (v_avoid ∉ rays a j)) then 1 else 0)
      (_htodo : ∀ a : Fin k, a_idx ≤ a.1 → ∀ j : Fin l,
        s.regs (regRayActive l a.1 j.1) = if act a j then 1 else 0),
      ∃ s' t,
        Exec w (filterAllStarsAvoidSliceCmd l regW a_idx rem) s s' t ∧
        t ≤ rem * (l * (23 * n + 25) + 1) + 1 ∧
        (∀ a : Fin k, ∀ j : Fin l,
          s'.regs (regRayActive l a.1 j.1) =
            if (act a j && decide (v_avoid ∉ rays a j)) then 1 else 0) ∧
        (∀ r : Reg, r ≠ 8 → r ≠ 10 → r ≠ 11 →
          (∀ a < k, ∀ j < l, r ≠ regRayActive l a j) → s'.regs r = s.regs r) ∧
        s'.arrs = s.arrs
  | 0, a_idx, hrem, s, _, _, hprev, _ => by
    refine ⟨s, 1, .skip s, by omega, fun a j => hprev a (by have := a.2; omega) j,
      fun _ _ _ _ _ => rfl, rfl⟩
  | rem + 1, a_idx, hrem, s, hsrc, hrw, hprev, htodo => by
    have ha_lt : a_idx < k := by omega
    let a : Fin k := ⟨a_idx, ha_lt⟩
    rcases filterStarAvoidSliceCmd_exec (a := a_idx) regW hne_w8 hne_w10 hne_w11
        (hne_wact a_idx ha_lt) v_avoid (rays a) (act a) hw1 hn_w (hP_len a)
        l 0 (Nat.zero_add l) (s := s) (hsrc a) hrw
        (fun _ hj => False.elim (Nat.not_lt_zero _ hj))
        (fun j _ => htodo a (by dsimp [a]; omega) j) with
      ⟨s₁, t₁, hex₁, ht₁, hall₁, hregs₁, harrs₁⟩
    have hsrc₁ : ∀ a' : Fin k, ∀ j : Fin l,
        s₁.arrs (starRayArr l a'.1 j.1) = (rays a' j).map Fin.val := by
      intro a' j; rw [harrs₁]; exact hsrc a' j
    have hrw₁ : s₁.regs regW = v_avoid.1 := by
      rw [hregs₁ regW hne_w8 hne_w10 hne_w11 (hne_wact a_idx ha_lt), hrw]
    have hprev₁ : ∀ a' : Fin k, a'.1 < a_idx + 1 → ∀ j : Fin l,
        s₁.regs (regRayActive l a'.1 j.1) =
          if (act a' j && decide (v_avoid ∉ rays a' j)) then 1 else 0 := by
      intro a' ha' j
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ha') with hlt | heq
      · rw [hregs₁ (regRayActive l a'.1 j.1)
          (by dsimp [regRayActive, Reg]; omega)
          (by dsimp [regRayActive, Reg]; omega)
          (by dsimp [regRayActive, Reg]; omega)
          (fun j' hj' hcol => by
            have := (regRayActive_inj j.2 hj' hcol).1
            omega)]
        exact hprev a' hlt j
      · have ha'_eq : a' = a := Fin.ext heq
        subst ha'_eq
        exact hall₁ j
    have htodo₁ : ∀ a' : Fin k, a_idx + 1 ≤ a'.1 → ∀ j : Fin l,
        s₁.regs (regRayActive l a'.1 j.1) = if act a' j then 1 else 0 := by
      intro a' ha' j
      rw [hregs₁ (regRayActive l a'.1 j.1)
        (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega)
        (fun j' hj' hcol => by
          have := (regRayActive_inj j.2 hj' hcol).1
          omega)]
      exact htodo a' (by omega) j
    rcases filterAllStarsAvoidSliceCmd_exec regW hne_w8 hne_w10 hne_w11 hne_wact
        v_avoid rays act hw1 hn_w hP_len rem (a_idx + 1) (by omega)
        hsrc₁ hrw₁ hprev₁ htodo₁ with
      ⟨s₂, t₂, hex₂, ht₂, hall₂, hregs₂, harrs₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by calc t₁ + t₂ ≤ (l * (23 * n + 25) + 1) + (rem * (l * (23 * n + 25) + 1) + 1) := by omega
           _ = (rem + 1) * (l * (23 * n + 25) + 1) + 1 := by ring,
      hall₂,
      fun r h8 h10 h11 hact_r => by
        rw [hregs₂ r h8 h10 h11 hact_r, hregs₁ r h8 h10 h11 (hact_r a_idx ha_lt)],
      harrs₂.trans harrs₁⟩

/-! ### Section 2: `qMemArr` Indicator Array and Ray-Hit Precomputation -/

/-- Loop body of `fillQMemLoop`: reads `r_11 := qArr[r_8]`, writes `qMemArr[r_11] := 1`, and
increments `r_8 := r_8 + 1`. -/
def fillQMemBody (qArr : Arr) : Cmd :=
  .seq (.assign 11 (.read qArr (.reg 8)))
    (.seq (.write qMemArr (.reg 11) (.const 1))
      (.assign 8 (.op .add (.reg 8) (.const 1))))

/-- Loop marking `qMemArr[v] := 1` for all `v` in `qArr[r_8 .. len qArr)`. -/
def fillQMemLoop (qArr : Arr) : Cmd :=
  .while (.op .lt (.reg 8) (.len qArr)) (fillQMemBody qArr)

theorem fillQMemLoop_exec {w n : ℕ} (qArr : Arr) (hne_arr : qArr ≠ qMemArr)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) :
    ∀ (rest : List (Fin n)) (off : ℕ) (S : Finset (Fin n)) {s : State}
      (_hq_w : (s.arrs qArr).length < 2 ^ w)
      (_hlen : off + rest.length = (s.arrs qArr).length)
      (_hget : ∀ j (hj : j < rest.length), (s.arrs qArr)[off + j]? = some (rest[j]'hj).1)
      (_hmem_len : (s.arrs qMemArr).length = n)
      (_hmem_val : ∀ u : Fin n, (s.arrs qMemArr)[u.1]? = some (if u ∈ S then 1 else 0))
      (_hr8 : s.regs 8 = off),
      ∃ s' t,
        Exec w (fillQMemLoop qArr) s s' t ∧
        t ≤ 13 * rest.length + 3 ∧
        (s'.arrs qMemArr).length = n ∧
        (∀ u : Fin n, (s'.arrs qMemArr)[u.1]? = some (if u ∈ S ∪ rest.toFinset then 1 else 0)) ∧
        (∀ r : Reg, r ≠ 8 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ qMemArr → s'.arrs a = s.arrs a)
  | [], off, S, s, hq_w, hlen, _, hmem_len, hmem_val, hr8 => by
    simp only [List.length_nil, Nat.add_zero] at hlen
    have hcond : (Expr.op .lt (.reg 8) (.len qArr)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8, hlen, hq_w,
        show (0 : ℕ) < 2 ^ w by omega]
    refine ⟨s, 3, .while_false hcond, by omega, hmem_len,
      fun u => by simpa using hmem_val u,
      fun _ _ _ => rfl, fun _ _ => rfl⟩
  | v :: rest, off, S, s, hq_w, hlen, hget, hmem_len, hmem_val, hr8 => by
    simp only [List.length_cons] at hlen
    have hoff_lt : off < (s.arrs qArr).length := by omega
    have hoff_w : off < 2 ^ w := by omega
    have hoff1_w : off + 1 < 2 ^ w := by omega
    have hv_lt : v.1 < n := v.2
    have hv_w : v.1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 8) (.len qArr)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8, hoff_w, hq_w, hoff_lt, hw1]
    have hget0 : (s.arrs qArr)[off]'hoff_lt = v.1 := by
      have h := hget 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h
      exact getElem_of_getElem? h hoff_lt
    let s₁ := s.setReg 11 v.1
    have hex₁ : Exec w (.assign 11 (.read qArr (.reg 8))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr8, hoff_w, hoff_lt, hget0, hv_w])
    let s₂ := s₁.writeArr qMemArr v.1 1
    have hex₂ : Exec w (.write qMemArr (.reg 11) (.const 1)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, s₁, hv_w])
        (by simp [Expr.eval, checkWord, hw1])
        (by simp [s₁, hmem_len, hv_lt])
    let s₃ := s₂.setReg 8 (off + 1)
    have hex₃ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hr8,
        hoff_w, hw1, hoff1_w])
    have hex_body : Exec w (fillQMemBody qArr) s s₃ (3 + (3 + 4)) :=
      .seq hex₁ (.seq hex₂ hex₃)
    have hq₃ : s₃.arrs qArr = s.arrs qArr := by
      simp [s₃, s₂, State.writeArr_arrs_ne _ _ _ hne_arr, s₁]
    have hmem_len₃ : (s₃.arrs qMemArr).length = n := by
      simp [s₃, s₂, s₁, hmem_len]
    have hmem_val₃ : ∀ u : Fin n,
        (s₃.arrs qMemArr)[u.1]? = some (if u ∈ insert v S then 1 else 0) := by
      intro u
      simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, Finset.mem_insert]
      by_cases huv : u = v
      · subst huv
        rw [List.getElem?_set_self (by rw [hmem_len]; exact hv_lt)]
        simp
      · have huv_val : v.1 ≠ u.1 := Fin.val_ne_of_ne (Ne.symm huv)
        rw [List.getElem?_set_ne huv_val, hmem_val u]
        simp [huv]
    rcases fillQMemLoop_exec qArr hne_arr hw1 hn_w rest (off + 1) (insert v S) (s := s₃)
        (by rwa [hq₃]) (by rw [hq₃]; omega)
        (fun j hj => by
          rw [hq₃, show off + 1 + j = off + (j + 1) by omega]
          have h := hget (j + 1) (by simp; omega)
          simpa using h)
        hmem_len₃ hmem_val₃ (by simp [s₃]) with
      ⟨s', t_rest, hex_rest, ht_rest, hmem_len', hmem_val', hregs', harrs'⟩
    have hunion : insert v S ∪ rest.toFinset = S ∪ (v :: rest).toFinset := by
      ext u
      simp
    rw [hunion] at hmem_val'
    refine ⟨s', 3 + (3 + (3 + 4)) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by simp only [List.length_cons]; omega,
      hmem_len', hmem_val',
      fun r h8 h11 => by rw [hregs' r h8 h11]; simp [s₃, s₂, s₁, h8, h11],
      fun a ha => by rw [harrs' a ha]; simp [s₃, s₂, State.writeArr_arrs_ne _ _ _ ha, s₁]⟩

/-- Populate `qMemArr` of length `n = r_0` with the indicator of `Q.toFinset`, where
`s.arrs qArr = Q.map Fin.val`. -/
def computeQMemCmd (qArr : Arr) : Cmd :=
  .seq (.alloc qMemArr (.reg 0))
    (.seq (.assign 8 (.const 0))
      (fillQMemLoop qArr))

theorem computeQMemCmd_exec {w n : ℕ} (qArr : Arr) (hne_arr : qArr ≠ qMemArr)
    (Q : List (Fin n))
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hQ_w : Q.length < 2 ^ w)
    (hr0 : s.regs 0 = n)
    (hqArr : s.arrs qArr = Q.map Fin.val) :
    ∃ s' t,
      Exec w (computeQMemCmd qArr) s s' t ∧
      t ≤ n + 13 * Q.length + 7 ∧
      (s'.arrs qMemArr).length = n ∧
      (∀ u : Fin n, (s'.arrs qMemArr)[u.1]? = some (if u ∈ Q.toFinset then 1 else 0)) ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ qMemArr → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr qMemArr (List.replicate n 0)
  have hex₁ : Exec w (.alloc qMemArr (.reg 0)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hr0, hn_w])
  let s₂ := s₁.setReg 8 0
  have hex₂ : Exec w (.assign 8 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases fillQMemLoop_exec qArr hne_arr hw1 hn_w Q 0 ∅ (s := s₂)
      (by simp [s₂, s₁, State.setArr_arrs_ne _ _ hne_arr, hqArr, hQ_w])
      (by simp [s₂, s₁, State.setArr_arrs_ne _ _ hne_arr, hqArr])
      (fun j hj => by
        simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ hne_arr, hqArr, Nat.zero_add]
        rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_map])
      (by simp [s₂, s₁])
      (fun u => by simp [s₂, s₁, u.2])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hmem_len₃, hmem_val₃, hregs₃, harrs₃⟩
  simp only [Finset.empty_union] at hmem_val₃
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hmem_len₃, hmem_val₃,
    fun r h8 h11 => by rw [hregs₃ r h8 h11]; simp [s₂, s₁, h8],
    fun a ha => by rw [harrs₃ a ha]; simp [s₂, s₁, State.setArr_arrs_ne _ _ ha]⟩

theorem rayMeetsPath_eq_decide_getLast_mem {n : ℕ} (Q P : List (Fin n)) (hneP : P ≠ []) :
    let A := WallOfHeight.rayHitPrefix Q P
    have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr hneP)
    WallOfHeight.rayMeetsPath Q P = decide (A.getLast hneA ∈ Q.toFinset) := by
  intro A hneA
  have hnePrev : P.reverse ≠ [] := List.reverse_ne_nil_iff.mpr hneP
  by_cases hmeet : WallOfHeight.rayMeetsPath Q P = true
  · have hmeet' : ∃ y ∈ P.reverse, y ∈ Q.toFinset := by
      simp only [WallOfHeight.rayMeetsPath, List.any_eq_true, decide_eq_true_eq] at hmeet
      rcases hmeet with ⟨y, hyP, hyQ⟩
      exact ⟨y, List.mem_reverse.mpr hyP, List.mem_toFinset.mpr hyQ⟩
    have hmem : A.getLast hneA ∈ Q.toFinset :=
      getLast_prefixUntil_mem_of_exists Q.toFinset hnePrev hmeet'
    simp [hmeet, hmem]
  · simp only [Bool.not_eq_true] at hmeet
    have hnot : A.getLast hneA ∉ Q.toFinset := by
      intro hmem
      have hlastP : A.getLast hneA ∈ P :=
        List.mem_reverse.mp (mem_of_mem_prefixUntil Q.toFinset (List.getLast_mem hneA))
      have htrue : WallOfHeight.rayMeetsPath Q P = true := by
        simp only [WallOfHeight.rayMeetsPath, List.any_eq_true, decide_eq_true_eq]
        exact ⟨A.getLast hneA, hlastP, List.mem_toFinset.mp hmem⟩
      exact Bool.false_ne_true (hmeet.symm.trans htrue)
    simp [hmeet, hnot]

/-- Precompute `hitPrefArr i = (WallOfHeight.rayHitPrefix Q (st.rays a i)).map Fin.val`,
`regRayHitVert i`, and `regRayMeets i` for ray `i` of star `a` using `qMemArr`. -/
def computeOneRayHitCmd (l a i : ℕ) : Cmd :=
  .seq (reverseArrCmd (starRayArr l a i) tmpPathArr1)
    (.seq (prefixUntilArrCmd tmpPathArr1 qMemArr (hitPrefArr i))
      (.seq (.assign (regRayHitVert i)
          (.read (hitPrefArr i) (.op .sub (.len (hitPrefArr i)) (.const 1))))
        (.assign (regRayMeets i) (.read qMemArr (.reg (regRayHitVert i))))))

theorem computeOneRayHitCmd_exec {w n l a i : ℕ}
    (Q P : List (Fin n)) (hneP : P ≠ [])
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hP_w : P.length < 2 ^ w)
    (hsrc : s.arrs (starRayArr l a i) = P.map Fin.val)
    (hmem_len : (s.arrs qMemArr).length = n)
    (hmem_val : ∀ u : Fin n, (s.arrs qMemArr)[u.1]? = some (if u ∈ Q.toFinset then 1 else 0)) :
    let A := WallOfHeight.rayHitPrefix Q P
    have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr hneP)
    ∃ s' t,
      Exec w (computeOneRayHitCmd l a i) s s' t ∧
      t ≤ 65 * P.length + 36 ∧
      s'.arrs (hitPrefArr i) = A.map Fin.val ∧
      s'.regs (regRayHitVert i) = (A.getLast hneA).1 ∧
      s'.regs (regRayMeets i) = (if WallOfHeight.rayMeetsPath Q P then 1 else 0) ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ regRayHitVert i → r ≠ regRayMeets i → s'.regs r = s.regs r) ∧
      (∀ arr : Arr, arr ≠ tmpPathArr1 → arr ≠ hitPrefArr i → s'.arrs arr = s.arrs arr) := by
  intro A hneA
  have h0_w : 0 < 2 ^ w := by omega
  rcases reverseArrCmd_exec (starRayArr l a i) tmpPathArr1
      (by dsimp [starRayArr, tmpPathArr1, Arr]; omega) (s := s) hw1
      (by simp [hsrc, hP_w])
      (fun v hv => by rw [hsrc] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
    ⟨s₁, t₁, hex₁, ht₁, hrev₁, hregs₁, harrs₁⟩
  rw [hsrc, ← List.map_reverse] at hrev₁
  have hmem_len₁ : (s₁.arrs qMemArr).length = n := by
    rw [harrs₁ qMemArr (by decide), hmem_len]
  have hmem_val₁ : ∀ u : Fin n,
      (s₁.arrs qMemArr)[u.1]? = some (if u ∈ Q.toFinset then 1 else 0) := by
    intro u; rw [harrs₁ qMemArr (by decide)]; exact hmem_val u
  rcases prefixUntilArrCmd_exec tmpPathArr1 qMemArr (hitPrefArr i)
      (by dsimp [tmpPathArr1, hitPrefArr, Arr]; omega)
      Q.toFinset P.reverse (s := s₁) hw1 hn_w hrev₁
      (by simp [hP_w]) hmem_len₁ hmem_val₁ with
    ⟨s₂, t₂, hex₂, ht₂, hpref₂, hregs₂, harrs₂⟩
  change s₂.arrs (hitPrefArr i) = A.map Fin.val at hpref₂
  have hA_le : A.length ≤ P.length := by
    simpa [A, WallOfHeight.rayHitPrefix] using length_prefixUntil_le Q.toFinset P.reverse
  have hA_pos : 1 ≤ A.length := List.length_pos_iff.mpr hneA
  have hA_w : A.length < 2 ^ w := by omega
  have hA_sub_w : A.length - 1 < 2 ^ w := by omega
  let z := A.getLast hneA
  have hz_lt : z.1 < n := z.2
  have hz_w : z.1 < 2 ^ w := by omega
  have hget_z : (s₂.arrs (hitPrefArr i))[A.length - 1]'(by simp [hpref₂]; omega) = z.1 := by
    have hlast_eq : A[A.length - 1]'(by omega) = z := (List.getLast_eq_getElem hneA).symm
    simp [hpref₂, hlast_eq]
  have heval_sub : (Expr.op .sub (.len (hitPrefArr i)) (.const 1)).eval w s₂ =
      some (A.length - 1) :=
    eval_op_sub (eval_len (by simp [hpref₂]) hA_w) (by simp [Expr.eval, checkWord, hw1])
  have heval_read_z :
      (Expr.read (hitPrefArr i) (.op .sub (.len (hitPrefArr i)) (.const 1))).eval w s₂ =
        some z.1 := by
    have hlt_len : A.length - 1 < (s₂.arrs (hitPrefArr i)).length := by simp [hpref₂]; omega
    unfold Expr.eval
    rw [heval_sub]
    simp [hlt_len, hget_z, checkWord, hz_w]
  let s₃ := s₂.setReg (regRayHitVert i) z.1
  have hex₃ : Exec w (.assign (regRayHitVert i)
      (.read (hitPrefArr i) (.op .sub (.len (hitPrefArr i)) (.const 1)))) s₂ s₃ 5 :=
    .assign heval_read_z
  have hmem_len₂ : (s₂.arrs qMemArr).length = n := by
    rw [harrs₂ qMemArr (by dsimp [qMemArr, hitPrefArr, Arr]; omega), hmem_len₁]
  have hmem_z : (s₂.arrs qMemArr)[z.1]'
      (by rw [hmem_len₂]; exact hz_lt) = if z ∈ Q.toFinset then 1 else 0 := by
    apply getElem_of_getElem?
    rw [harrs₂ qMemArr (by dsimp [qMemArr, hitPrefArr, Arr]; omega)]
    exact hmem_val₁ z
  have hmeet_eq : (if z ∈ Q.toFinset then 1 else 0) =
      (if WallOfHeight.rayMeetsPath Q P then 1 else 0) := by
    rw [rayMeetsPath_eq_decide_getLast_mem Q P hneP]
    by_cases hzQ : z ∈ Q <;> simp [z, A, hzQ]
  have heval_read_mem :
      (Expr.read qMemArr (.reg (regRayHitVert i))).eval w s₃ =
        some (if WallOfHeight.rayMeetsPath Q P then 1 else 0) := by
    rw [← hmeet_eq]
    by_cases hzQ : z ∈ Q.toFinset <;>
      simp [Expr.eval, checkWord, s₃, hz_w, hmem_len₂, hz_lt, hmem_z, hzQ, hw1, h0_w]
  let s₄ := s₃.setReg (regRayMeets i) (if WallOfHeight.rayMeetsPath Q P then 1 else 0)
  have hex₄ : Exec w (.assign (regRayMeets i) (.read qMemArr (.reg (regRayHitVert i)))) s₃ s₄ 3 :=
    .assign heval_read_mem
  simp only [hsrc, List.length_map, List.length_reverse] at ht₁ ht₂
  refine ⟨s₄, t₁ + (t₂ + (5 + 3)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega,
    by simp [s₄, s₃, hpref₂],
    by simp [s₄, s₃, z, State.setReg_regs_ne _ _
      (by dsimp [regRayHitVert, regRayMeets, Reg]; omega : regRayHitVert i ≠ regRayMeets i)],
    by simp [s₄],
    fun r h7 h8 h9 h10 h11 hrv hrm => by
      simp only [s₄, s₃, State.setReg_regs_ne _ _ hrm, State.setReg_regs_ne _ _ hrv]
      rw [hregs₂ r h7 h8 h9 h10 h11, hregs₁ r h7 h9 h11],
    fun arr ha1 ha2 => by
      simp only [s₄, s₃, State.setReg_arrs]
      rw [harrs₂ arr ha2, harrs₁ arr ha1]⟩

/-- Precompute `hitPrefArr j`, `regRayHitVert j`, and `regRayMeets j` for `j = i .. i + rem - 1`. -/
def computeAllRayHitsSliceCmd (l a i : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (computeOneRayHitCmd l a i)
      (computeAllRayHitsSliceCmd l a (i + 1) rem)

theorem computeAllRayHitsSliceCmd_exec {w n l a : ℕ}
    (Q : List (Fin n)) (rays : Fin l → List (Fin n))
    (hneP : ∀ j : Fin l, rays j ≠ [])
    (hP_len : ∀ j : Fin l, (rays j).length ≤ n)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = l) {s : State}
      (_hsrc : ∀ j : Fin l, s.arrs (starRayArr l a j.1) = (rays j).map Fin.val)
      (_hmem_len : (s.arrs qMemArr).length = n)
      (_hmem_val : ∀ u : Fin n, (s.arrs qMemArr)[u.1]? = some (if u ∈ Q.toFinset then 1 else 0))
      (_hprev : ∀ j : Fin l, j.1 < idx →
        let A := WallOfHeight.rayHitPrefix Q (rays j)
        have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
        s.arrs (hitPrefArr j.1) = A.map Fin.val ∧
        s.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
        s.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0)),
      ∃ s' t,
        Exec w (computeAllRayHitsSliceCmd l a idx rem) s s' t ∧
        t ≤ rem * (65 * n + 36) + 1 ∧
        (∀ j : Fin l,
          let A := WallOfHeight.rayHitPrefix Q (rays j)
          have hneA : A ≠ [] :=
            prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
          s'.arrs (hitPrefArr j.1) = A.map Fin.val ∧
          s'.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
          s'.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0)) ∧
        (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
          (∀ j < l, r ≠ regRayHitVert j) →
          (∀ j < l, r ≠ regRayMeets j) → s'.regs r = s.regs r) ∧
        (∀ arr : Arr, arr ≠ tmpPathArr1 → (∀ j < l, arr ≠ hitPrefArr j) → s'.arrs arr = s.arrs arr)
  | 0, idx, hrem, s, _, _, _, hprev => by
    refine ⟨s, 1, .skip s, by omega, fun j => hprev j (by have := j.2; omega),
      fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | rem + 1, idx, hrem, s, hsrc, hmem_len, hmem_val, hprev => by
    have hi_lt : idx < l := by omega
    let i : Fin l := ⟨idx, hi_lt⟩
    have hPi_len : (rays i).length ≤ n := hP_len i
    rcases computeOneRayHitCmd_exec (l := l) (a := a) (i := idx) Q (rays i) (hneP i)
        hw1 hn_w (by omega) (hsrc i) hmem_len hmem_val with
      ⟨s₁, t₁, hex₁, ht₁, hpref₁, hrv₁, hrm₁, hregs₁, harrs₁⟩
    have ht₁_le : t₁ ≤ 65 * n + 36 := by omega
    have hsrc₁ : ∀ j : Fin l, s₁.arrs (starRayArr l a j.1) = (rays j).map Fin.val := by
      intro j
      rw [harrs₁ (starRayArr l a j.1)
        (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
        (by dsimp [starRayArr, hitPrefArr, Arr]; omega)]
      exact hsrc j
    have hmem_len₁ : (s₁.arrs qMemArr).length = n := by
      rw [harrs₁ qMemArr (by decide) (by dsimp [qMemArr, hitPrefArr, Arr]; omega), hmem_len]
    have hmem_val₁ : ∀ u : Fin n,
        (s₁.arrs qMemArr)[u.1]? = some (if u ∈ Q.toFinset then 1 else 0) := by
      intro u
      rw [harrs₁ qMemArr (by decide) (by dsimp [qMemArr, hitPrefArr, Arr]; omega)]
      exact hmem_val u
    have hprev₁ : ∀ j : Fin l, j.1 < idx + 1 →
        let A := WallOfHeight.rayHitPrefix Q (rays j)
        have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
        s₁.arrs (hitPrefArr j.1) = A.map Fin.val ∧
        s₁.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
        s₁.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0) := by
      intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
      · rw [harrs₁ (hitPrefArr j.1)
            (by dsimp [hitPrefArr, tmpPathArr1, Arr]; omega)
            (by dsimp [hitPrefArr, Arr]; omega),
          hregs₁ (regRayHitVert j.1)
            (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayHitVert, Reg]; omega)
            (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayHitVert, Reg]; omega)
            (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayHitVert, Reg]; omega)
            (by dsimp [regRayHitVert, regRayMeets, Reg]; omega),
          hregs₁ (regRayMeets j.1)
            (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
            (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)
            (by dsimp [regRayMeets, Reg]; omega)
            (by dsimp [regRayHitVert, regRayMeets, Reg]; omega)
            (by dsimp [regRayMeets, Reg]; omega)]
        exact hprev j hlt
      · have hj_eq : j = i := Fin.ext heq
        subst hj_eq
        exact ⟨hpref₁, hrv₁, hrm₁⟩
    rcases computeAllRayHitsSliceCmd_exec Q rays hneP hP_len hw1 hn_w rem (idx + 1) (by omega)
        hsrc₁ hmem_len₁ hmem_val₁ hprev₁ with
      ⟨s₂, t₂, hex₂, ht₂, hall₂, hregs₂, harrs₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by calc t₁ + t₂ ≤ (65 * n + 36) + (rem * (65 * n + 36) + 1) := by omega
           _ = (rem + 1) * (65 * n + 36) + 1 := by ring,
      hall₂,
      fun r h7 h8 h9 h10 h11 hrv hrm => by
        rw [hregs₂ r h7 h8 h9 h10 h11 hrv hrm,
          hregs₁ r h7 h8 h9 h10 h11 (hrv idx hi_lt) (hrm idx hi_lt)],
      fun arr ha1 ha2 => by
        rw [harrs₂ arr ha1 ha2, harrs₁ arr ha1 (ha2 idx hi_lt)]⟩

/-! ### Section 3: Scanning `Q` to Build `hitsOnQ` -/

theorem list_find?_map {α β : Type*} (f : α → β) (p : β → Bool) :
    ∀ (L : List α), (L.map f).find? p = (L.find? (fun x => p (f x))).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.find?_cons]
    cases p (f x)
    · exact list_find?_map f p xs
    · rfl

theorem list_find?_filter {α : Type*} (q p : α → Bool) :
    ∀ (L : List α), (L.filter q).find? p = L.find? (fun x => q x && p x)
  | [] => rfl
  | x :: xs => by
    cases hq : q x <;> cases hp : p x <;>
      simp [hq, hp, list_find?_filter q p xs]

/-- Find the first active ray index `i : Fin l` whose ray meets `Q` and has its first hit on `Q`
at vertex `z`. -/
def findHitRayIdxAt {l n : ℕ} (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (Q : List (Fin n)) (z : Fin n) : Option (Fin l) :=
  (List.finRange l).find? (fun i =>
    act i && (WallOfHeight.rayMeetsPath Q (rays i) &&
      ((WallOfHeight.rayHitPrefix Q (rays i)).getLast? == some z)))

theorem findHitRayAt_activeRayList {l n : ℕ} (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (Q : List (Fin n)) (z : Fin n) :
    WallOfHeight.findHitRayAt (activeRayList rays act) Q z =
      (findHitRayIdxAt rays act Q z).map rays := by
  unfold WallOfHeight.findHitRayAt activeRayList findHitRayIdxAt
  rw [list_find?_map, list_find?_filter]

/-- Index-preserving counterpart of `WallOfHeight.hitsOnQ` returning `List (ℕ × Fin l)`. -/
def hitsIdxOnQ {l n : ℕ} (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (Q : List (Fin n)) : List (ℕ × Fin l) :=
  (List.range Q.length).filterMap (fun idx =>
    match Q[idx]? with
    | none => none
    | some z => (findHitRayIdxAt rays act Q z).map (fun i => (idx, i)))

theorem hitsOnQ_activeRayList {l n : ℕ} (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (Q : List (Fin n)) :
    WallOfHeight.hitsOnQ (activeRayList rays act) Q =
      (hitsIdxOnQ rays act Q).map (fun p => (p.1, rays p.2)) := by
  unfold WallOfHeight.hitsOnQ hitsIdxOnQ
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro idx _
  cases Q[idx]? with
  | none => rfl
  | some z =>
    dsimp only
    rw [findHitRayAt_activeRayList, Option.map_map, Option.map_map]
    rfl

theorem length_hitsIdxOnQ_le {l n : ℕ} (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (Q : List (Fin n)) :
    (hitsIdxOnQ rays act Q).length ≤ Q.length := by
  unfold hitsIdxOnQ
  calc ((List.range Q.length).filterMap _).length
      ≤ (List.range Q.length).length := List.length_filterMap_le _ _
    _ = Q.length := List.length_range

/-- Check if ray `i` of star `a` is the first active ray hitting `Q` at `regZ`: if `r_18 == 0`,
`regRayActive l a i == 1`, `regRayMeets i == 1`, and `regRayHitVert i == r_regZ`, sets
`r_18 := 1` and `r_19 := i`. -/
def checkOneRayHitAtCmd (l a i : ℕ) (regZ : Reg) : Cmd :=
  .ite (exprAnd (exprEq (.reg 18) (.const 0))
      (exprAnd (.reg (regRayActive l a i))
        (exprAnd (.reg (regRayMeets i))
          (exprEq (.reg (regRayHitVert i)) (.reg regZ)))))
    (.seq (.assign 18 (.const 1)) (.assign 19 (.const i)))
    .skip

/-- Slice over `i, i + 1, ..., i + rem - 1` checking `checkOneRayHitAtCmd l a i regZ`. -/
def findHitRaySliceCmd (l a : ℕ) (regZ : Reg) (i : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 =>
    .seq (checkOneRayHitAtCmd l a i regZ)
      (findHitRaySliceCmd l a regZ (i + 1) rem)

/-- Find the first active ray `i < l` of star `a` hitting `Q` at `regZ`, setting `r_18 := 1` and
`r_19 := i` if found, or `r_18 := 0` if none. -/
def findHitRayCmd (l a : ℕ) (regZ : Reg) : Cmd :=
  .seq (.assign 18 (.const 0))
    (.seq (.assign 19 (.const 0))
      (findHitRaySliceCmd l a regZ 0 l))

theorem find?_append_singleton {α : Type*} (p : α → Bool) (L : List α) (x : α) :
    (L ++ [x]).find? p =
      match L.find? p with
      | some a => some a
      | none => if p x then some x else none := by
  induction L with
  | nil =>
    simp only [List.nil_append, List.find?_nil, List.find?_cons]
    cases p x <;> rfl
  | cons y ys ih =>
    simp only [List.cons_append, List.find?_cons]
    cases p y
    · exact ih
    · rfl

theorem finRange_take_succ (l idx : ℕ) (hi : idx < l) :
    (List.finRange l).take (idx + 1) = (List.finRange l).take idx ++ [⟨idx, hi⟩] := by
  have hi' : idx < (List.finRange l).length := by simpa using hi
  rw [List.take_succ_eq_append_getElem hi']
  simp

/-- Predicate testing whether active ray `j : Fin l` meets `Q` and has its first hit on `Q` at `z`. -/
def hitRayPred {l n : ℕ} (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (Q : List (Fin n)) (z : Fin n) (j : Fin l) : Bool :=
  act j && (WallOfHeight.rayMeetsPath Q (rays j) &&
    ((WallOfHeight.rayHitPrefix Q (rays j)).getLast? == some z))

theorem findHitRaySliceCmd_exec {w n l a : ℕ} (regZ : Reg)
    (hne_z18 : regZ ≠ 18) (hne_z19 : regZ ≠ 19)
    (Q : List (Fin n)) (z : Fin n)
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (hneP : ∀ j : Fin l, rays j ≠ [])
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hl_w : l < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = l) {s : State}
      (_hact : ∀ j : Fin l, s.regs (regRayActive l a j.1) = if act j then 1 else 0)
      (_hhit : ∀ j : Fin l,
        let A := WallOfHeight.rayHitPrefix Q (rays j)
        have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
        s.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
        s.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0))
      (_hrz : s.regs regZ = z.1)
      (_hinv : match ((List.finRange l).take idx).find? (hitRayPred rays act Q z) with
        | some i₀ => s.regs 18 = 1 ∧ s.regs 19 = i₀.1
        | none => s.regs 18 = 0),
      ∃ s' t,
        Exec w (findHitRaySliceCmd l a regZ idx rem) s s' t ∧
        t ≤ 28 * rem + 1 ∧
        (match (List.finRange l).find? (hitRayPred rays act Q z) with
          | some i₀ => s'.regs 18 = 1 ∧ s'.regs 19 = i₀.1
          | none => s'.regs 18 = 0) ∧
        (∀ r : Reg, r ≠ 18 → r ≠ 19 → s'.regs r = s.regs r) ∧
        s'.arrs = s.arrs
  | 0, idx, hrem, s, _, _, _, hinv => by
    have hidx : idx = l := by omega
    subst hidx
    have htake : (List.finRange idx).take idx = List.finRange idx :=
      List.take_of_length_le (by simp)
    rw [htake] at hinv
    refine ⟨s, 1, .skip s, by omega, hinv, fun _ _ _ => rfl, rfl⟩
  | rem + 1, idx, hrem, s, hact, hhit, hrz, hinv => by
    let hitPred := hitRayPred rays act Q z
    have h0_w : 0 < 2 ^ w := by omega
    have hi_lt : idx < l := by omega
    have hi_w : idx < 2 ^ w := by omega
    let i : Fin l := ⟨idx, hi_lt⟩
    let A := WallOfHeight.rayHitPrefix Q (rays i)
    have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP i))
    obtain ⟨hrv_i, hrm_i⟩ := hhit i
    have hlast_eq : (A.getLast? == some z) = decide ((A.getLast hneA).1 = z.1) := by
      rw [List.getLast?_eq_some_getLast hneA]
      by_cases heq : A.getLast hneA = z
      · subst heq; simp
      · have hne_val : (A.getLast hneA).1 ≠ z.1 := Fin.val_ne_of_ne heq
        simp [heq, hne_val]
    have hpred_i : hitPred i =
        (act i && (WallOfHeight.rayMeetsPath Q (rays i) && decide ((A.getLast hneA).1 = z.1))) := by
      dsimp [hitPred, hitRayPred, A]
      rw [hlast_eq]
    have heval_act : (Expr.reg (regRayActive l a idx)).eval w s =
        some (if act i then 1 else 0) := by
      have h := hact i
      change s.regs (regRayActive l a idx) = if act i then 1 else 0 at h
      cases ha : act i <;> simp [Expr.eval, checkWord, h, ha, hw1, h0_w]
    have heval_rm : (Expr.reg (regRayMeets idx)).eval w s =
        some (if WallOfHeight.rayMeetsPath Q (rays i) then 1 else 0) := by
      change s.regs (regRayMeets idx) =
        if WallOfHeight.rayMeetsPath Q (rays i) then 1 else 0 at hrm_i
      cases hm : WallOfHeight.rayMeetsPath Q (rays i) <;>
        simp [Expr.eval, checkWord, hrm_i, hm, hw1, h0_w]
    have hrv_w : (A.getLast hneA).1 < 2 ^ w := by have := (A.getLast hneA).2; omega
    have hz_w : z.1 < 2 ^ w := by have := z.2; omega
    have heval_rv : (Expr.reg (regRayHitVert idx)).eval w s = some (A.getLast hneA).1 := by
      change s.regs (regRayHitVert idx) = (A.getLast hneA).1 at hrv_i
      simp [Expr.eval, checkWord, hrv_i, hrv_w]
    have heval_z : (Expr.reg regZ).eval w s = some z.1 := by
      simp [Expr.eval, checkWord, hrz, hz_w]
    have heval_eqZ : (exprEq (.reg (regRayHitVert idx)) (.reg regZ)).eval w s =
        some (if (A.getLast hneA).1 = z.1 then 1 else 0) :=
      eval_exprEq hw1 heval_rv heval_z
    have heval_and1 :
        (exprAnd (.reg (regRayMeets idx))
          (exprEq (.reg (regRayHitVert idx)) (.reg regZ))).eval w s =
          some (if (WallOfHeight.rayMeetsPath Q (rays i) &&
            decide ((A.getLast hneA).1 = z.1)) then 1 else 0) := by
      rw [eval_exprAnd hw1 heval_rm heval_eqZ]
      cases WallOfHeight.rayMeetsPath Q (rays i) <;>
        by_cases hz_eq : (A.getLast hneA).1 = z.1 <;> simp [hz_eq]
    have heval_and2 :
        (exprAnd (.reg (regRayActive l a idx))
          (exprAnd (.reg (regRayMeets idx))
            (exprEq (.reg (regRayHitVert idx)) (.reg regZ)))).eval w s =
          some (if hitPred i then 1 else 0) := by
      rw [eval_exprAnd hw1 heval_act heval_and1, hpred_i]
      cases act i <;>
        cases (WallOfHeight.rayMeetsPath Q (rays i) && decide ((A.getLast hneA).1 = z.1)) <;>
        simp
    have hstep_find :
        ((List.finRange l).take (idx + 1)).find? hitPred =
          match ((List.finRange l).take idx).find? hitPred with
          | some i₀ => some i₀
          | none => if hitPred i then some i else none := by
      rw [finRange_take_succ l idx hi_lt, List.find?_append]
      cases ((List.finRange l).take idx).find? hitPred <;> simp [i]
    cases hfind_prev : ((List.finRange l).take idx).find? hitPred with
    | some i₀ =>
      rw [hfind_prev] at hinv
      have hr18 : s.regs 18 = 1 := hinv.1
      have h18_eval : (Expr.reg 18).eval w s = some (s.regs 18) := by
        simp [Expr.eval, checkWord, hr18, hw1]
      have h0_eval : (Expr.const 0).eval w s = some 0 := by
        simp [Expr.eval, checkWord, h0_w]
      have heval_r18_0 : (exprEq (.reg 18) (.const 0)).eval w s =
          some (if s.regs 18 = 0 then 1 else 0) :=
        eval_exprEq hw1 h18_eval h0_eval
      have hcond :
          (exprAnd (exprEq (.reg 18) (.const 0))
            (exprAnd (.reg (regRayActive l a idx))
              (exprAnd (.reg (regRayMeets idx))
                (exprEq (.reg (regRayHitVert idx)) (.reg regZ))))).eval w s = some 0 := by
        rw [eval_exprAnd hw1 heval_r18_0 heval_and2]
        simp [hr18]
      have hex₁ : Exec w (checkOneRayHitAtCmd l a idx regZ) s s _ :=
        .ite_false hcond (.skip s)
      have hinv₁ : match ((List.finRange l).take (idx + 1)).find? hitPred with
          | some i₀ => s.regs 18 = 1 ∧ s.regs 19 = i₀.1
          | none => s.regs 18 = 0 := by
        rw [hstep_find, hfind_prev]
        exact hinv
      rcases findHitRaySliceCmd_exec regZ hne_z18 hne_z19 Q z rays act hneP
          hw1 hn_w hl_w rem (idx + 1) (by omega) hact hhit hrz hinv₁ with
        ⟨s₂, t₂, hex₂, ht₂, hres₂, hregs₂, harrs₂⟩
      refine ⟨s₂, _, .seq hex₁ hex₂,
        by simp [exprAnd, exprEq, Expr.cost]; omega,
        hres₂, hregs₂, harrs₂⟩
    | none =>
      rw [hfind_prev] at hinv
      have hr18 : s.regs 18 = 0 := hinv
      have h18_eval : (Expr.reg 18).eval w s = some (s.regs 18) := by
        simp [Expr.eval, checkWord, hr18, h0_w]
      have h0_eval : (Expr.const 0).eval w s = some 0 := by
        simp [Expr.eval, checkWord, h0_w]
      have heval_r18_0 : (exprEq (.reg 18) (.const 0)).eval w s =
          some (if s.regs 18 = 0 then 1 else 0) :=
        eval_exprEq hw1 h18_eval h0_eval
      by_cases hpi : hitPred i = true
      · have hcond :
            (exprAnd (exprEq (.reg 18) (.const 0))
              (exprAnd (.reg (regRayActive l a idx))
                (exprAnd (.reg (regRayMeets idx))
                  (exprEq (.reg (regRayHitVert idx)) (.reg regZ))))).eval w s = some 1 := by
          rw [eval_exprAnd hw1 heval_r18_0 heval_and2]
          simp [hr18, hpi]
        let s₁a := s.setReg 18 1
        have hex₁a : Exec w (.assign 18 (.const 1)) s s₁a 2 :=
          .assign (by simp [Expr.eval, checkWord, hw1])
        let s₁ := s₁a.setReg 19 idx
        have hex₁b : Exec w (.assign 19 (.const idx)) s₁a s₁ 2 :=
          .assign (by simp [Expr.eval, checkWord, hi_w])
        have hex₁ : Exec w (checkOneRayHitAtCmd l a idx regZ) s s₁ _ :=
          .ite_true hcond (by omega) (.seq hex₁a hex₁b)
        have hact₁ : ∀ j : Fin l, s₁.regs (regRayActive l a j.1) = if act j then 1 else 0 := by
          intro j
          simp [s₁, s₁a,
            State.setReg_regs_ne _ _ (by dsimp [regRayActive, Reg]; omega : regRayActive l a j.1 ≠ 19),
            State.setReg_regs_ne _ _ (by dsimp [regRayActive, Reg]; omega : regRayActive l a j.1 ≠ 18),
            hact j]
        have hhit₁ : ∀ j : Fin l,
            let A := WallOfHeight.rayHitPrefix Q (rays j)
            have hneA : A ≠ [] :=
              prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
            s₁.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
            s₁.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0) := by
          intro j
          simp [s₁, s₁a,
            State.setReg_regs_ne _ _ (by dsimp [regRayHitVert, Reg]; omega : regRayHitVert j.1 ≠ 19),
            State.setReg_regs_ne _ _ (by dsimp [regRayHitVert, Reg]; omega : regRayHitVert j.1 ≠ 18),
            State.setReg_regs_ne _ _ (by dsimp [regRayMeets, Reg]; omega : regRayMeets j.1 ≠ 19),
            State.setReg_regs_ne _ _ (by dsimp [regRayMeets, Reg]; omega : regRayMeets j.1 ≠ 18),
            hhit j]
        have hrz₁ : s₁.regs regZ = z.1 := by
          simp [s₁, s₁a, hne_z19, hne_z18, hrz]
        have hinv₁ : match ((List.finRange l).take (idx + 1)).find? hitPred with
            | some i₀ => s₁.regs 18 = 1 ∧ s₁.regs 19 = i₀.1
            | none => s₁.regs 18 = 0 := by
          rw [hstep_find, hfind_prev, if_pos hpi]
          simp [s₁, s₁a, i]
        rcases findHitRaySliceCmd_exec regZ hne_z18 hne_z19 Q z rays act hneP
            hw1 hn_w hl_w rem (idx + 1) (by omega) hact₁ hhit₁ hrz₁ hinv₁ with
          ⟨s₂, t₂, hex₂, ht₂, hres₂, hregs₂, harrs₂⟩
        refine ⟨s₂, _, .seq hex₁ hex₂,
          by simp [exprAnd, exprEq, Expr.cost]; omega,
          hres₂,
          fun r h18 h19 => by rw [hregs₂ r h18 h19]; simp [s₁, s₁a, h18, h19],
          by rw [harrs₂]; rfl⟩
      · simp only [Bool.not_eq_true] at hpi
        have hcond :
            (exprAnd (exprEq (.reg 18) (.const 0))
              (exprAnd (.reg (regRayActive l a idx))
                (exprAnd (.reg (regRayMeets idx))
                  (exprEq (.reg (regRayHitVert idx)) (.reg regZ))))).eval w s = some 0 := by
          rw [eval_exprAnd hw1 heval_r18_0 heval_and2]
          simp [hr18, hpi]
        have hex₁ : Exec w (checkOneRayHitAtCmd l a idx regZ) s s _ :=
          .ite_false hcond (.skip s)
        have hinv₁ : match ((List.finRange l).take (idx + 1)).find? hitPred with
            | some i₀ => s.regs 18 = 1 ∧ s.regs 19 = i₀.1
            | none => s.regs 18 = 0 := by
          rw [hstep_find, hfind_prev, hpi]
          exact hr18
        rcases findHitRaySliceCmd_exec regZ hne_z18 hne_z19 Q z rays act hneP
            hw1 hn_w hl_w rem (idx + 1) (by omega) hact hhit hrz hinv₁ with
          ⟨s₂, t₂, hex₂, ht₂, hres₂, hregs₂, harrs₂⟩
        refine ⟨s₂, _, .seq hex₁ hex₂,
          by simp [exprAnd, exprEq, Expr.cost]; omega,
          hres₂, hregs₂, harrs₂⟩

theorem findHitRayCmd_exec {w n l a : ℕ} (regZ : Reg)
    (hne_z18 : regZ ≠ 18) (hne_z19 : regZ ≠ 19)
    (Q : List (Fin n)) (z : Fin n)
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (hneP : ∀ j : Fin l, rays j ≠ [])
    {s : State}
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hl_w : l < 2 ^ w)
    (hact : ∀ j : Fin l, s.regs (regRayActive l a j.1) = if act j then 1 else 0)
    (hhit : ∀ j : Fin l,
      let A := WallOfHeight.rayHitPrefix Q (rays j)
      have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
      s.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
      s.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0))
    (hrz : s.regs regZ = z.1) :
    ∃ s' t,
      Exec w (findHitRayCmd l a regZ) s s' t ∧
      t ≤ 28 * l + 5 ∧
      (match findHitRayIdxAt rays act Q z with
        | some i₀ => s'.regs 18 = 1 ∧ s'.regs 19 = i₀.1
        | none => s'.regs 18 = 0) ∧
      (∀ r : Reg, r ≠ 18 → r ≠ 19 → s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 18 0
  have hex₁ : Exec w (.assign 18 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 19 0
  have hex₂ : Exec w (.assign 19 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hact₂ : ∀ j : Fin l, s₂.regs (regRayActive l a j.1) = if act j then 1 else 0 := by
    intro j
    simp [s₂, s₁,
      State.setReg_regs_ne _ _ (by dsimp [regRayActive, Reg]; omega : regRayActive l a j.1 ≠ 19),
      State.setReg_regs_ne _ _ (by dsimp [regRayActive, Reg]; omega : regRayActive l a j.1 ≠ 18),
      hact j]
  have hhit₂ : ∀ j : Fin l,
      let A := WallOfHeight.rayHitPrefix Q (rays j)
      have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
      s₂.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
      s₂.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0) := by
    intro j
    simp [s₂, s₁,
      State.setReg_regs_ne _ _ (by dsimp [regRayHitVert, Reg]; omega : regRayHitVert j.1 ≠ 19),
      State.setReg_regs_ne _ _ (by dsimp [regRayHitVert, Reg]; omega : regRayHitVert j.1 ≠ 18),
      State.setReg_regs_ne _ _ (by dsimp [regRayMeets, Reg]; omega : regRayMeets j.1 ≠ 19),
      State.setReg_regs_ne _ _ (by dsimp [regRayMeets, Reg]; omega : regRayMeets j.1 ≠ 18),
      hhit j]
  have hrz₂ : s₂.regs regZ = z.1 := by
    simp [s₂, s₁, hne_z19, hne_z18, hrz]
  rcases findHitRaySliceCmd_exec regZ hne_z18 hne_z19 Q z rays act hneP
      hw1 hn_w hl_w l 0 (Nat.zero_add l) (s := s₂) hact₂ hhit₂ hrz₂ (by simp [s₂, s₁]) with
    ⟨s₃, t₃, hex₃, ht₃, hres₃, hregs₃, harrs₃⟩
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hres₃,
    fun r h18 h19 => by rw [hregs₃ r h18 h19]; simp [s₂, s₁, h18, h19],
    by rw [harrs₃]; rfl⟩

/-- Loop body of `scanHitsOnQLoop`: reads `r_17 := qArr[r_8]`, finds a hit ray at `r_17`,
pushes `(r_8, r_19)` to `(hitIdxArr, hitRayIdxArr)` if `r_18 == 1`, and increments `r_8`. -/
def scanHitsOnQBody (l a : ℕ) (qArr : Arr) : Cmd :=
  .seq (.assign 17 (.read qArr (.reg 8)))
    (.seq (findHitRayCmd l a 17)
      (.seq (.ite (.reg 18)
          (.seq (pushBufCmd hitIdxArr 20 (.reg 8))
            (pushBufCmd hitRayIdxArr 21 (.reg 19)))
          .skip)
        (.assign 8 (.op .add (.reg 8) (.const 1)))))

/-- Loop scanning `qArr[r_8 .. len qArr)` and accumulating hits into `hitIdxArr` (length `r_20`)
and `hitRayIdxArr` (length `r_21`). -/
def scanHitsOnQLoop (l a : ℕ) (qArr : Arr) : Cmd :=
  .while (.op .lt (.reg 8) (.len qArr)) (scanHitsOnQBody l a qArr)

theorem hitsIdxOnQ_take_succ {l n : ℕ} (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (Q : List (Fin n)) (off : ℕ) (hoff : off < Q.length) :
    ((List.range Q.length).take (off + 1)).filterMap (fun idx =>
      match Q[idx]? with
      | none => none
      | some z => (findHitRayIdxAt rays act Q z).map (fun i => (idx, i))) =
    ((List.range Q.length).take off).filterMap (fun idx =>
      match Q[idx]? with
      | none => none
      | some z => (findHitRayIdxAt rays act Q z).map (fun i => (idx, i))) ++
    match findHitRayIdxAt rays act Q (Q[off]'hoff) with
    | none => []
    | some i₀ => [(off, i₀)] := by
  have hoff_range : off < (List.range Q.length).length := by simpa using hoff
  rw [List.take_succ_eq_append_getElem hoff_range, List.getElem_range, List.filterMap_append]
  simp only [List.filterMap_cons, List.filterMap_nil, List.getElem?_eq_getElem hoff]
  cases findHitRayIdxAt rays act Q (Q[off]'hoff) <;> rfl

/-- Prefix of `hitsIdxOnQ` over the first `k` indices of `Q`. -/
def hitsIdxPrefix {l n : ℕ} (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (Q : List (Fin n)) (k : ℕ) : List (ℕ × Fin l) :=
  ((List.range Q.length).take k).filterMap (fun idx =>
    match Q[idx]? with
    | none => none
    | some z => (findHitRayIdxAt rays act Q z).map (fun i => (idx, i)))

theorem scanHitsOnQLoop_exec {w n l a : ℕ} (qArr : Arr)
    (hne_q1 : qArr ≠ hitIdxArr) (hne_q2 : qArr ≠ hitRayIdxArr)
    (Q : List (Fin n))
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (hneP : ∀ j : Fin l, rays j ≠ [])
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hl_w : l < 2 ^ w) (hQ_w : Q.length < 2 ^ w) :
    ∀ (rem off : ℕ) (_hrem : off + rem = Q.length) {s : State}
      (_hqArr : s.arrs qArr = Q.map Fin.val)
      (_hact : ∀ j : Fin l, s.regs (regRayActive l a j.1) = if act j then 1 else 0)
      (_hhit : ∀ j : Fin l,
        let A := WallOfHeight.rayHitPrefix Q (rays j)
        have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
        s.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
        s.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0))
      (_hbuf1 : IsBufPrefix s hitIdxArr 20 Q.length ((hitsIdxPrefix rays act Q off).map Prod.fst))
      (_hbuf2 : IsBufPrefix s hitRayIdxArr 21 Q.length ((hitsIdxPrefix rays act Q off).map (fun p => p.2.1)))
      (_hr8 : s.regs 8 = off),
      ∃ s' t,
        Exec w (scanHitsOnQLoop l a qArr) s s' t ∧
        t ≤ rem * (28 * l + 32) + 3 ∧
        IsBufPrefix s' hitIdxArr 20 Q.length ((hitsIdxOnQ rays act Q).map Prod.fst) ∧
        IsBufPrefix s' hitRayIdxArr 21 Q.length ((hitsIdxOnQ rays act Q).map (fun p => p.2.1)) ∧
        (∀ r : Reg, r ≠ 8 → r ≠ 17 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → s'.regs r = s.regs r) ∧
        (∀ arr : Arr, arr ≠ hitIdxArr → arr ≠ hitRayIdxArr → s'.arrs arr = s.arrs arr)
  | 0, off, hrem, s, hqArr, _, _, hbuf1, hbuf2, hr8 => by
    have hoff : off = Q.length := by omega
    subst hoff
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 8) (.len qArr)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8, hqArr, hQ_w, h0_w]
    have htake : hitsIdxPrefix rays act Q Q.length = hitsIdxOnQ rays act Q := by
      unfold hitsIdxPrefix hitsIdxOnQ
      rw [List.take_of_length_le (by simp)]
    rw [htake] at hbuf1 hbuf2
    refine ⟨s, 3, .while_false hcond, by omega, hbuf1, hbuf2,
      fun _ _ _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | rem + 1, off, hrem, s, hqArr, hact, hhit, hbuf1, hbuf2, hr8 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hoff_lt : off < Q.length := by omega
    have hoff_w : off < 2 ^ w := by omega
    have hoff1_w : off + 1 < 2 ^ w := by omega
    let z := Q[off]'hoff_lt
    have hz_w : z.1 < 2 ^ w := by have := z.2; omega
    have hcond : (Expr.op .lt (.reg 8) (.len qArr)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8, hqArr, hoff_w, hQ_w, hoff_lt, hw1]
    let s₁ := s.setReg 17 z.1
    have hex₁ : Exec w (.assign 17 (.read qArr (.reg 8))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr8, hoff_w, hqArr, hoff_lt, z, hz_w])
    have hact₁ : ∀ j : Fin l, s₁.regs (regRayActive l a j.1) = if act j then 1 else 0 := by
      intro j
      simp [s₁, State.setReg_regs_ne _ _
        (by dsimp [regRayActive, Reg]; omega : regRayActive l a j.1 ≠ 17), hact j]
    have hhit₁ : ∀ j : Fin l,
        let A := WallOfHeight.rayHitPrefix Q (rays j)
        have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
        s₁.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
        s₁.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0) := by
      intro j
      simp [s₁,
        State.setReg_regs_ne _ _ (by dsimp [regRayHitVert, Reg]; omega : regRayHitVert j.1 ≠ 17),
        State.setReg_regs_ne _ _ (by dsimp [regRayMeets, Reg]; omega : regRayMeets j.1 ≠ 17),
        hhit j]
    rcases findHitRayCmd_exec 17 (by decide) (by decide) Q z rays act hneP
        (s := s₁) hw1 hn_w hl_w hact₁ hhit₁ (by simp [s₁]) with
      ⟨s₂, t₂, hex₂, ht₂, hfind₂, hregs₂, harrs₂⟩
    have hbuf1_2 : IsBufPrefix s₂ hitIdxArr 20 Q.length ((hitsIdxPrefix rays act Q off).map Prod.fst) :=
      hbuf1.of_preserve (by rw [harrs₂]; rfl)
        (by rw [hregs₂ 20 (by decide) (by decide)]; simp [s₁])
    have hbuf2_2 : IsBufPrefix s₂ hitRayIdxArr 21 Q.length ((hitsIdxPrefix rays act Q off).map (fun p => p.2.1)) :=
      hbuf2.of_preserve (by rw [harrs₂]; rfl)
        (by rw [hregs₂ 21 (by decide) (by decide)]; simp [s₁])
    have hr8_2 : s₂.regs 8 = off := by
      rw [hregs₂ 8 (by decide) (by decide)]; simp [s₁, hr8]
    have hlen_prefix : (hitsIdxPrefix rays act Q off).length ≤ off := by
      unfold hitsIdxPrefix
      calc (((List.range Q.length).take off).filterMap _).length
          ≤ ((List.range Q.length).take off).length := List.length_filterMap_le _ _
        _ ≤ off := List.length_take_le off _
    have hstep_pref : hitsIdxPrefix rays act Q (off + 1) =
        hitsIdxPrefix rays act Q off ++
          match findHitRayIdxAt rays act Q z with
          | none => []
          | some i₀ => [(off, i₀)] :=
      hitsIdxOnQ_take_succ rays act Q off hoff_lt
    cases hopt : findHitRayIdxAt rays act Q z with
    | none =>
      rw [hopt] at hfind₂ hstep_pref
      simp only [List.append_nil] at hstep_pref
      have hex₃ : Exec w (.ite (.reg 18)
          (.seq (pushBufCmd hitIdxArr 20 (.reg 8))
            (pushBufCmd hitRayIdxArr 21 (.reg 19)))
          .skip) s₂ s₂ 2 :=
        .ite_false (by simp [Expr.eval, checkWord, hfind₂, h0_w]) (.skip s₂)
      let s₄ := s₂.setReg 8 (off + 1)
      have hex₄ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₂ s₄ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_2, hoff_w, hw1, hoff1_w])
      have hex_body : Exec w (scanHitsOnQBody l a qArr) s s₄ (3 + (t₂ + (2 + 4))) :=
        .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
      have hbuf1_4 : IsBufPrefix s₄ hitIdxArr 20 Q.length ((hitsIdxPrefix rays act Q (off + 1)).map Prod.fst) := by
        rw [hstep_pref]
        exact hbuf1_2.of_preserve rfl (by simp [s₄])
      have hbuf2_4 : IsBufPrefix s₄ hitRayIdxArr 21 Q.length
          ((hitsIdxPrefix rays act Q (off + 1)).map (fun p => p.2.1)) := by
        rw [hstep_pref]
        exact hbuf2_2.of_preserve rfl (by simp [s₄])
      have hact₄ : ∀ j : Fin l, s₄.regs (regRayActive l a j.1) = if act j then 1 else 0 := by
        intro j
        simp only [s₄, State.setReg_regs_ne _ _
          (by dsimp [regRayActive, Reg]; omega : regRayActive l a j.1 ≠ 8)]
        rw [hregs₂ (regRayActive l a j.1)
          (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)]
        exact hact₁ j
      have hhit₄ : ∀ j : Fin l,
          let A := WallOfHeight.rayHitPrefix Q (rays j)
          have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
          s₄.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
          s₄.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0) := by
        intro j
        simp only [s₄,
          State.setReg_regs_ne _ _ (by dsimp [regRayHitVert, Reg]; omega : regRayHitVert j.1 ≠ 8),
          State.setReg_regs_ne _ _ (by dsimp [regRayMeets, Reg]; omega : regRayMeets j.1 ≠ 8)]
        rw [hregs₂ (regRayHitVert j.1)
            (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayHitVert, Reg]; omega),
          hregs₂ (regRayMeets j.1)
            (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)]
        exact hhit₁ j
      rcases scanHitsOnQLoop_exec qArr hne_q1 hne_q2 Q rays act hneP
          hw1 hn_w hl_w hQ_w rem (off + 1) (by omega)
          (by simp [s₄, harrs₂, s₁, hqArr]) hact₄ hhit₄ hbuf1_4 hbuf2_4 (by simp [s₄]) with
        ⟨s', t_rest, hex_rest, ht_rest, hres1, hres2, hregs', harrs'⟩
      refine ⟨s', 3 + (3 + (t₂ + (2 + 4))) + t_rest,
        .while_true hcond (by omega) hex_body hex_rest,
        by calc 3 + (3 + (t₂ + (2 + 4))) + t_rest
            ≤ 12 + (28 * l + 5) + (rem * (28 * l + 32) + 3) := by omega
          _ ≤ (rem + 1) * (28 * l + 32) + 3 := by nlinarith,
        hres1, hres2,
        fun r h8 h17 h18 h19 h20 h21 => by
          rw [hregs' r h8 h17 h18 h19 h20 h21]
          simp only [s₄, State.setReg_regs_ne _ _ h8]
          rw [hregs₂ r h18 h19]
          simp [s₁, h17],
        fun arr ha1 ha2 => by
          rw [harrs' arr ha1 ha2]
          simp [s₄, harrs₂, s₁]⟩
    | some i₀ =>
      rw [hopt] at hfind₂ hstep_pref
      obtain ⟨hr18_2, hr19_2⟩ := hfind₂
      have hi₀_w : i₀.1 < 2 ^ w := by have := i₀.2; omega
      rcases pushBufCmd_exec hitIdxArr 20 (.reg 8) Q.length ((hitsIdxPrefix rays act Q off).map Prod.fst) off
          (s := s₂) hw1 hQ_w hbuf1_2 (by simp; omega)
          (by simp [Expr.eval, checkWord, hr8_2, hoff_w]) with
        ⟨s₃a, t₃a, hex₃a, ht₃a, hbuf1_3a, hregs₃a, harrs₃a⟩
      have hbuf2_3a : IsBufPrefix s₃a hitRayIdxArr 21 Q.length
          ((hitsIdxPrefix rays act Q off).map (fun p => p.2.1)) :=
        hbuf2_2.of_preserve (harrs₃a hitRayIdxArr (by decide)) (hregs₃a 21 (by decide))
      have hr19_3a : s₃a.regs 19 = i₀.1 := by rw [hregs₃a 19 (by decide), hr19_2]
      rcases pushBufCmd_exec hitRayIdxArr 21 (.reg 19) Q.length
          ((hitsIdxPrefix rays act Q off).map (fun p => p.2.1)) i₀.1
          (s := s₃a) hw1 hQ_w hbuf2_3a (by simp; omega)
          (by simp [Expr.eval, checkWord, hr19_3a, hi₀_w]) with
        ⟨s₃, t₃b, hex₃b, ht₃b, hbuf2_3, hregs₃b, harrs₃b⟩
      have hcond18 : (Expr.reg 18).eval w s₂ = some 1 := by
        simp [Expr.eval, checkWord, hr18_2, hw1]
      have hex₃ : Exec w (.ite (.reg 18)
          (.seq (pushBufCmd hitIdxArr 20 (.reg 8))
            (pushBufCmd hitRayIdxArr 21 (.reg 19)))
          .skip) s₂ s₃ (1 + (t₃a + t₃b)) :=
        .ite_true hcond18 (by omega) (.seq hex₃a hex₃b)
      have hr8_3 : s₃.regs 8 = off := by
        rw [hregs₃b 8 (by decide), hregs₃a 8 (by decide), hr8_2]
      let s₄ := s₃.setReg 8 (off + 1)
      have hex₄ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₃ s₄ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_3, hoff_w, hw1, hoff1_w])
      have hex_body : Exec w (scanHitsOnQBody l a qArr) s s₄
          (3 + (t₂ + ((1 + (t₃a + t₃b)) + 4))) :=
        .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
      have hbuf1_4 : IsBufPrefix s₄ hitIdxArr 20 Q.length ((hitsIdxPrefix rays act Q (off + 1)).map Prod.fst) := by
        rw [hstep_pref, List.map_append, List.map_singleton]
        exact hbuf1_3a.of_preserve
          (by simp [s₄, harrs₃b hitIdxArr (by decide)])
          (by simp [s₄, hregs₃b 20 (by decide)])
      have hbuf2_4 : IsBufPrefix s₄ hitRayIdxArr 21 Q.length
          ((hitsIdxPrefix rays act Q (off + 1)).map (fun p => p.2.1)) := by
        rw [hstep_pref, List.map_append, List.map_singleton]
        exact hbuf2_3.of_preserve rfl (by simp [s₄])
      have hact₄ : ∀ j : Fin l, s₄.regs (regRayActive l a j.1) = if act j then 1 else 0 := by
        intro j
        simp only [s₄, State.setReg_regs_ne _ _
          (by dsimp [regRayActive, Reg]; omega : regRayActive l a j.1 ≠ 8)]
        rw [hregs₃b (regRayActive l a j.1) (by dsimp [regRayActive, Reg]; omega),
          hregs₃a (regRayActive l a j.1) (by dsimp [regRayActive, Reg]; omega),
          hregs₂ (regRayActive l a j.1)
            (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)]
        exact hact₁ j
      have hhit₄ : ∀ j : Fin l,
          let A := WallOfHeight.rayHitPrefix Q (rays j)
          have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
          s₄.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
          s₄.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0) := by
        intro j
        simp only [s₄,
          State.setReg_regs_ne _ _ (by dsimp [regRayHitVert, Reg]; omega : regRayHitVert j.1 ≠ 8),
          State.setReg_regs_ne _ _ (by dsimp [regRayMeets, Reg]; omega : regRayMeets j.1 ≠ 8)]
        rw [hregs₃b (regRayHitVert j.1) (by dsimp [regRayHitVert, Reg]; omega),
          hregs₃a (regRayHitVert j.1) (by dsimp [regRayHitVert, Reg]; omega),
          hregs₂ (regRayHitVert j.1)
            (by dsimp [regRayHitVert, Reg]; omega) (by dsimp [regRayHitVert, Reg]; omega),
          hregs₃b (regRayMeets j.1) (by dsimp [regRayMeets, Reg]; omega),
          hregs₃a (regRayMeets j.1) (by dsimp [regRayMeets, Reg]; omega),
          hregs₂ (regRayMeets j.1)
            (by dsimp [regRayMeets, Reg]; omega) (by dsimp [regRayMeets, Reg]; omega)]
        exact hhit₁ j
      have hq₄ : s₄.arrs qArr = Q.map Fin.val := by
        simp [s₄, harrs₃b qArr hne_q2, harrs₃a qArr hne_q1, harrs₂, s₁, hqArr]
      rcases scanHitsOnQLoop_exec qArr hne_q1 hne_q2 Q rays act hneP
          hw1 hn_w hl_w hQ_w rem (off + 1) (by omega)
          hq₄ hact₄ hhit₄ hbuf1_4 hbuf2_4 (by simp [s₄]) with
        ⟨s', t_rest, hex_rest, ht_rest, hres1, hres2, hregs', harrs'⟩
      simp only [Expr.cost_reg] at ht₃a ht₃b
      refine ⟨s', 3 + (3 + (t₂ + ((1 + (t₃a + t₃b)) + 4))) + t_rest,
        .while_true hcond (by omega) hex_body hex_rest,
        by calc 3 + (3 + (t₂ + ((1 + (t₃a + t₃b)) + 4))) + t_rest
            ≤ (28 * l + 32) + (rem * (28 * l + 32) + 3) := by omega
          _ = (rem + 1) * (28 * l + 32) + 3 := by ring,
        hres1, hres2,
        fun r h8 h17 h18 h19 h20 h21 => by
          rw [hregs' r h8 h17 h18 h19 h20 h21]
          simp only [s₄, State.setReg_regs_ne _ _ h8]
          rw [hregs₃b r h21, hregs₃a r h20, hregs₂ r h18 h19]
          simp [s₁, h17],
        fun arr ha1 ha2 => by
          rw [harrs' arr ha1 ha2]
          simp [s₄, harrs₃b arr ha2, harrs₃a arr ha1, harrs₂, s₁]⟩

/-- Compute all ray-hit prefixes and scan `Q` (in `qArr`) to populate `hitIdxArr` (length `r_20`)
and `hitRayIdxArr` (length `r_21`) with `hitsIdxOnQ (st.rays a) act Q`. -/
def computeHitsOnQCmd (l a : ℕ) (qArr : Arr) : Cmd :=
  .seq (computeQMemCmd qArr)
    (.seq (computeAllRayHitsSliceCmd l a 0 l)
      (.seq (initBufCmd hitIdxArr 20 (.len qArr))
        (.seq (initBufCmd hitRayIdxArr 21 (.len qArr))
          (.seq (.assign 8 (.const 0))
            (scanHitsOnQLoop l a qArr)))))

theorem computeHitsOnQCmd_exec {w n l a : ℕ} (qArr : Arr)
    (hne_qmem : qArr ≠ qMemArr) (hne_qtmp : qArr ≠ tmpPathArr1)
    (hne_qpref : ∀ j < l, qArr ≠ hitPrefArr j)
    (hne_q1 : qArr ≠ hitIdxArr) (hne_q2 : qArr ≠ hitRayIdxArr)
    (Q : List (Fin n))
    (rays : Fin l → List (Fin n)) (act : Fin l → Bool)
    (hneP : ∀ j : Fin l, rays j ≠ [])
    (hP_len : ∀ j : Fin l, (rays j).length ≤ n)
    (hQ_len : Q.length ≤ n)
    {s : State}
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hl_w : l < 2 ^ w)
    (hr0 : s.regs 0 = n)
    (hqArr : s.arrs qArr = Q.map Fin.val)
    (hsrc : ∀ j : Fin l, s.arrs (starRayArr l a j.1) = (rays j).map Fin.val)
    (hact : ∀ j : Fin l, s.regs (regRayActive l a j.1) = if act j then 1 else 0) :
    ∃ s' t,
      Exec w (computeHitsOnQCmd l a qArr) s s' t ∧
      t ≤ l * (65 * n + 36) + n * (28 * l + 48) + 25 ∧
      s'.regs 20 = (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length ∧
      IsBufPrefix s' hitIdxArr 20 Q.length ((hitsIdxOnQ rays act Q).map Prod.fst) ∧
      IsBufPrefix s' hitRayIdxArr 21 Q.length ((hitsIdxOnQ rays act Q).map (fun p => p.2.1)) ∧
      (∀ j : Fin l,
        s'.arrs (hitPrefArr j.1) = (WallOfHeight.rayHitPrefix Q (rays j)).map Fin.val) ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 17 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 →
        (∀ j < l, r ≠ regRayHitVert j) →
        (∀ j < l, r ≠ regRayMeets j) → s'.regs r = s.regs r) ∧
      (∀ arr : Arr, arr ≠ qMemArr → arr ≠ tmpPathArr1 →
        arr ≠ hitIdxArr → arr ≠ hitRayIdxArr →
        (∀ j < l, arr ≠ hitPrefArr j) → s'.arrs arr = s.arrs arr) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hQ_w : Q.length < 2 ^ w := by omega
  rcases computeQMemCmd_exec qArr hne_qmem Q hw1 hn_w hQ_w hr0 hqArr with
    ⟨s₁, t₁, hex₁, ht₁, hmem_len₁, hmem_val₁, hregs₁, harrs₁⟩
  have hsrc₁ : ∀ j : Fin l, s₁.arrs (starRayArr l a j.1) = (rays j).map Fin.val := by
    intro j
    rw [harrs₁ (starRayArr l a j.1) (by dsimp [starRayArr, qMemArr, Arr]; omega)]
    exact hsrc j
  rcases computeAllRayHitsSliceCmd_exec Q rays hneP hP_len hw1 hn_w l 0 (Nat.zero_add l)
      (s := s₁) hsrc₁ hmem_len₁ hmem_val₁
      (fun _ hj => False.elim (Nat.not_lt_zero _ hj)) with
    ⟨s₂, t₂, hex₂, ht₂, hrayhits₂, hregs₂, harrs₂⟩
  have hqArr₂ : s₂.arrs qArr = Q.map Fin.val := by
    rw [harrs₂ qArr hne_qtmp hne_qpref, harrs₁ qArr hne_qmem, hqArr]
  rcases initBufCmd_exec hitIdxArr 20 (.len qArr) Q.length (s := s₂) h0_w
      (by simp [Expr.eval, checkWord, hqArr₂, hQ_w]) with
    ⟨s₃, t₃, hex₃, ht₃, hbuf1_3, hregs₃, harrs₃⟩
  have hqArr₃ : s₃.arrs qArr = Q.map Fin.val := by
    rw [harrs₃ qArr hne_q1, hqArr₂]
  rcases initBufCmd_exec hitRayIdxArr 21 (.len qArr) Q.length (s := s₃) h0_w
      (by simp [Expr.eval, checkWord, hqArr₃, hQ_w]) with
    ⟨s₄, t₄, hex₄, ht₄, hbuf2_4, hregs₄, harrs₄⟩
  let s₅ := s₄.setReg 8 0
  have hex₅ : Exec w (.assign 8 (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hqArr₅ : s₅.arrs qArr = Q.map Fin.val := by
    simp [s₅, harrs₄ qArr hne_q2, hqArr₃]
  have hact₅ : ∀ j : Fin l, s₅.regs (regRayActive l a j.1) = if act j then 1 else 0 := by
    intro j
    simp only [s₅, State.setReg_regs_ne _ _
      (by dsimp [regRayActive, Reg]; omega : regRayActive l a j.1 ≠ 8)]
    rw [hregs₄ (regRayActive l a j.1) (by dsimp [regRayActive, Reg]; omega),
      hregs₃ (regRayActive l a j.1) (by dsimp [regRayActive, Reg]; omega),
      hregs₂ (regRayActive l a j.1)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)
        (by dsimp [regRayActive, Reg]; omega)
        (fun j' _ => by dsimp [regRayActive, regRayHitVert, Reg]; omega)
        (fun j' _ => by dsimp [regRayActive, regRayMeets, Reg]; omega),
      hregs₁ (regRayActive l a j.1)
        (by dsimp [regRayActive, Reg]; omega) (by dsimp [regRayActive, Reg]; omega)]
    exact hact j
  have hhit₅ : ∀ j : Fin l,
      let A := WallOfHeight.rayHitPrefix Q (rays j)
      have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset (List.reverse_ne_nil_iff.mpr (hneP j))
      s₅.regs (regRayHitVert j.1) = (A.getLast hneA).1 ∧
      s₅.regs (regRayMeets j.1) = (if WallOfHeight.rayMeetsPath Q (rays j) then 1 else 0) := by
    intro j
    simp only [s₅,
      State.setReg_regs_ne _ _ (by dsimp [regRayHitVert, Reg]; omega : regRayHitVert j.1 ≠ 8),
      State.setReg_regs_ne _ _ (by dsimp [regRayMeets, Reg]; omega : regRayMeets j.1 ≠ 8)]
    rw [hregs₄ (regRayHitVert j.1) (by dsimp [regRayHitVert, Reg]; omega),
      hregs₃ (regRayHitVert j.1) (by dsimp [regRayHitVert, Reg]; omega),
      hregs₄ (regRayMeets j.1) (by dsimp [regRayMeets, Reg]; omega),
      hregs₃ (regRayMeets j.1) (by dsimp [regRayMeets, Reg]; omega)]
    exact (hrayhits₂ j).2
  have hbuf1_5 : IsBufPrefix s₅ hitIdxArr 20 Q.length [] :=
    hbuf1_3.of_preserve
      (by simp [s₅, harrs₄ hitIdxArr (by decide)])
      (by simp [s₅, hregs₄ 20 (by decide)])
  have hbuf2_5 : IsBufPrefix s₅ hitRayIdxArr 21 Q.length [] :=
    hbuf2_4.of_preserve (by simp [s₅]) (by simp [s₅])
  rcases scanHitsOnQLoop_exec qArr hne_q1 hne_q2 Q rays act hneP
      hw1 hn_w hl_w hQ_w Q.length 0 (Nat.zero_add Q.length) (s := s₅)
      hqArr₅ hact₅ hhit₅ hbuf1_5 hbuf2_5 (by simp [s₅]) with
    ⟨s₆, t₆, hex₆, ht₆, hbuf1_6, hbuf2_6, hregs₆, harrs₆⟩
  have hlen_hits : s₆.regs 20 = (WallOfHeight.hitsOnQ (activeRayList rays act) Q).length := by
    have h := hbuf1_6.2.1
    rw [hitsOnQ_activeRayList, List.length_map]
    simpa using h
  simp only [Expr.cost_len] at ht₃ ht₄
  have ht_bound : t₁ + (t₂ + (t₃ + (t₄ + (2 + t₆)))) ≤
      l * (65 * n + 36) + n * (28 * l + 48) + 25 := by
    have hQ_mul : Q.length * (28 * l + 32) ≤ n * (28 * l + 32) :=
      Nat.mul_le_mul_right (28 * l + 32) hQ_len
    have h_np : n * (28 * l + 48) = n * (28 * l + 32) + 16 * n := by ring
    omega
  refine ⟨s₆, t₁ + (t₂ + (t₃ + (t₄ + (2 + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    ht_bound,
    hlen_hits, hbuf1_6, hbuf2_6,
    fun j => by
      rw [harrs₆ (hitPrefArr j.1)
          (by dsimp [hitPrefArr, hitIdxArr, Arr]; omega)
          (by dsimp [hitPrefArr, hitRayIdxArr, Arr]; omega)]
      simp only [s₅, State.setReg_arrs]
      rw [harrs₄ (hitPrefArr j.1) (by dsimp [hitPrefArr, hitRayIdxArr, Arr]; omega),
        harrs₃ (hitPrefArr j.1) (by dsimp [hitPrefArr, hitIdxArr, Arr]; omega)]
      exact (hrayhits₂ j).1,
    fun r h7 h8 h9 h10 h11 h17 h18 h19 h20 h21 hrv hrm => by
      rw [hregs₆ r h8 h17 h18 h19 h20 h21]
      simp only [s₅, State.setReg_regs_ne _ _ h8]
      rw [hregs₄ r h21, hregs₃ r h20, hregs₂ r h7 h8 h9 h10 h11 hrv hrm, hregs₁ r h8 h11],
    fun arr ha1 ha2 ha3 ha4 hapref => by
      rw [harrs₆ arr ha3 ha4]
      simp only [s₅, State.setReg_arrs]
      rw [harrs₄ arr ha4, harrs₃ arr ha3, harrs₂ arr ha2 hapref, harrs₁ arr ha1]⟩

end GraphMinor.Compute
