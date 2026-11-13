module

public import GraphMinor.Compute.TwoPathsLoopSide

/-!
# One iteration of the `while` loop of Algorithm 5.2

This file implements and proves one iteration (`stepProg`) of the `while` loop of Algorithm 5.2
(Humeau and Pous, page 23, run on a tight path as in `GraphMinor/HP25/Sec5Complete.lean`):

1. Run `bothSidesProg` to compute `aOnA` and `aOnB` for the current path `P` in `aNewPath`.
2. Scan `aOnA` and `aOnB` (`findRProg`) to find the first index `rIdxR` where
   `aOnA[i] * aOnB[i] == 0` (or `len aNewPath` if every vertex of `P` is on both sides).
3. If `rIdxR == len aNewPath`, set `rDone := 1` (the loop will terminate).
4. Otherwise (`0 < rIdxR < len aNewPath - 1` because the endpoints `a` and `b` are on both sides):
   - Read `rSideT := aOnA[rIdxR]` and run `findSProg` to find the first index `rIdxS > rIdxR`
     where `aOnB[i] == 1` (if `rSideT == 1`) or `aOnA[i] == 1` (if `rSideT == 0`).
   - Read `rValY := aNewPath[rIdxR - 1]` and `rValS := aNewPath[rIdxS]`.
   - Append `[rValY, rValS]` to `aF` (`appendEdgeProg`).
   - Replace `aNewPath` by `aNewPath[0 .. rIdxR) ++ aNewPath[rIdxS .. len aNewPath)`
     (`shortenPathProg`).
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {N : ℕ}

/-! ### Registers and arrays used by `stepProg` -/

/-- Register holding the side bit of `t = Pv[rIdxR]` on `A`. -/
abbrev rSideT : Reg := 113
/-- Register holding `1` when all vertices of `aNewPath` are on both sides, else `0`. -/
abbrev rDone : Reg := 120
/-- Register holding the index `r` of the first vertex `t = Pv[r]` not on both sides. -/
abbrev rIdxR : Reg := 116
/-- Register holding the index `idx_s > r` of the first vertex `s = Pv[idx_s]` on the missing side. -/
abbrev rIdxS : Reg := 117
/-- Register holding `y.1 = Pv[r - 1].1`. -/
abbrev rValY : Reg := 118
/-- Register holding `s.1 = Pv[idx_s].1`. -/
abbrev rValS : Reg := 119

/-- Registers modified by `stepProg` (all in `60 .. 120`). -/
def loopStepRegs : List ℕ := List.range' 60 61

/-- Arrays modified by `stepProg`. -/
def loopStepArrs : List ℕ := [aLab, aPar, aQue, aSrc, aOnA, aOnB, aTmp, aF, aNewPath]

/-! ### Copying from `aTmp` -/

/-- Copy `aTmp` into `dst`. -/
def copyFromTmp (dst : Arr) : Cmd :=
  mapProg rI3 (.len aTmp) dst aTmp (.reg rI3)

theorem copyFromTmp_exec {w : ℕ} (dst : Arr) (hne : dst ≠ aTmp) (L : List ℕ) (s : State)
    (hw1 : 1 < 2 ^ w) (hlen : L.length < 2 ^ w) (hL : ∀ x ∈ L, x < 2 ^ w)
    (htmp : s.arrs aTmp = L) :
    ∃ s' t, Exec w (copyFromTmp dst) s s' t ∧
      t ≤ 6 + 12 * L.length ∧
      Keeps [rI3] [dst] s s' ∧
      s'.arrs dst = L := by
  have hlenT : ∀ st, Keeps [rI3] [dst] s st → (Expr.len aTmp).eval w st = some L.length :=
    fun st hst => len_eval (by rw [hst.2 aTmp (by simp [Ne.symm hne])]; exact htmp) hlen
  obtain ⟨s', t, hex, ht, hk, hd⟩ := mapProg_exec rI3 (.len aTmp) dst aTmp (.reg rI3)
    hne L.length (fun i => i) L s hw1 hlen hlenT
    (fun _ i _ hri hi => reg_eval hri (lt_trans hi hlen))
    (fun i hi => hi) hL htmp
  rw [map_getD_self] at hd
  refine ⟨s', t, hex, ?_, hk, hd⟩
  simp only [Expr.cost] at ht
  omega

/-! ### Finding the first vertex `t = Pv[r]` not on both sides -/

/-- Body of `findRProg`: if `rI2 < rIdxR` and `aOnA[rI2] * aOnB[rI2] == 0`, set `rIdxR := rI2`. -/
def findRBody : Cmd :=
  .ite (.op .lt (.reg rI2) (.reg rIdxR))
    (.ite (.op .eq (.op .mul (.read aOnA (.reg rI2)) (.read aOnB (.reg rI2))) (.const 0))
      (.assign rIdxR (.reg rI2))
      .skip)
    .skip

/-- Scan `0 .. len aNewPath` to find the first index `rIdxR` where `aOnA[i] * aOnB[i] == 0`. -/
def findRProg : Cmd :=
  .seq (.assign rIdxR (.len aNewPath))
    (.seq (.assign rI2 (.const 0))
      (forUp rI2 (.len aNewPath) findRBody))

/-- Invariant of `findRProg` after scanning `[0, i)`: either `r = n` and all `j < i` have
`bA[j] = 1 ∧ bB[j] = 1`, or `r < i` is the first index where `bA[r] * bB[r] = 0`. -/
def FindRInv (bA bB : List ℕ) (n i r : ℕ) : Prop :=
  (r = n ∧ ∀ j (hj : j < i) (hja : j < bA.length) (hjb : j < bB.length),
    bA[j] = 1 ∧ bB[j] = 1) ∨
  (∃ (hr : r < i) (hra : r < bA.length) (hrb : r < bB.length),
    bA[r] * bB[r] = 0 ∧
    ∀ j (hj : j < r) (hja : j < bA.length) (hjb : j < bB.length),
      bA[j] = 1 ∧ bB[j] = 1)

theorem findRBody_exec {w : ℕ} {bA bB : List ℕ} {n i : ℕ}
    (hbA : bA.length = n) (hbB : bB.length = n)
    (hA_le : ∀ x ∈ bA, x ≤ 1) (hB_le : ∀ x ∈ bB, x ≤ 1)
    (hi : i < n) (hnw : n < 2 ^ w) (hw1 : 1 < 2 ^ w)
    {s₀ s : State} (hk : Keeps [rI2, rIdxR] [] s₀ s)
    (hA : s.arrs aOnA = bA) (hB : s.arrs aOnB = bB)
    (hri : s.regs rI2 = i) (hinv : FindRInv bA bB n i (s.regs rIdxR)) :
    ∃ s' t, Exec w findRBody s s' t ∧ t ≤ 16 ∧
      Keeps [rI2, rIdxR] [] s₀ s' ∧
      s'.regs rI2 = i ∧
      FindRInv bA bB n (i + 1) (s'.regs rIdxR) := by
  have hiw : i < 2 ^ w := lt_trans hi hnw
  have hia : i < bA.length := by omega
  have hib : i < bB.length := by omega
  have hvA : bA[i] ≤ 1 := hA_le _ (List.getElem_mem hia)
  have hvB : bB[i] ≤ 1 := hB_le _ (List.getElem_mem hib)
  rcases hinv with ⟨hrn, hall⟩ | ⟨hri_lt, hra, hrb, hzero, hall⟩
  · -- `s.regs rIdxR = n`, so `i < s.regs rIdxR` is true.
    have hlt_eval : (Expr.op .lt (.reg rI2) (.reg rIdxR)).eval w s = some 1 := by
      have := lt_eval (reg_eval hri hiw) (reg_eval hrn hnw) hw1
      simpa [hi] using this
    have hrA : (Expr.read aOnA (.reg rI2)).eval w s = some bA[i] := by
      rw [read_eval (reg_eval hri hiw) (by rw [hA]; exact hia)]
      · simp [hA]
      · simp [hA]; omega
    have hrB : (Expr.read aOnB (.reg rI2)).eval w s = some bB[i] := by
      rw [read_eval (reg_eval hri hiw) (by rw [hB]; exact hib)]
      · simp [hB]
      · simp [hB]; omega
    have hmul_le : bA[i] * bB[i] ≤ 1 := Nat.mul_le_mul hvA hvB
    have hmul : (Expr.op .mul (.read aOnA (.reg rI2)) (.read aOnB (.reg rI2))).eval w s =
        some (bA[i] * bB[i]) :=
      op_eval hrA hrB (by simp [BinOp.eval, BinOp.raw, checkWord]; omega)
    by_cases hz : bA[i] * bB[i] = 0
    · have heq : (Expr.op .eq (.op .mul (.read aOnA (.reg rI2)) (.read aOnB (.reg rI2)))
          (.const 0)).eval w s = some 1 := by
        have := eq_eval hmul (const_eval' (c := 0) (by omega)) hw1
        simpa [hz] using this
      refine ⟨s.setReg rIdxR i, _,
        .ite_true hlt_eval one_ne_zero (.ite_true heq one_ne_zero (.assign (reg_eval hri hiw))),
        by simp [Expr.cost], hk.setReg (by decide) _, by simp [hri], ?_⟩
      simp only [State.setReg_regs_self]
      exact Or.inr ⟨by omega, hia, hib, hz, fun j hj hja hjb => hall j hj hja hjb⟩
    · have heq : (Expr.op .eq (.op .mul (.read aOnA (.reg rI2)) (.read aOnB (.reg rI2)))
          (.const 0)).eval w s = some 0 := by
        have := eq_eval hmul (const_eval' (c := 0) (by omega)) hw1
        simpa [hz] using this
      refine ⟨s, _, .ite_true hlt_eval one_ne_zero (.ite_false heq (.skip _)),
        by simp [Expr.cost], hk, hri, ?_⟩
      refine Or.inl ⟨hrn, fun j hj hja hjb => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · exact hall j hlt hja hjb
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hvA with h0 | h1
        · simp [h0] at hz
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hvB with h0' | h1'
          · simp [h0'] at hz
          · exact ⟨h1, h1'⟩
  · -- `s.regs rIdxR < i`, so `i < s.regs rIdxR` is false.
    have hrw : s.regs rIdxR < 2 ^ w := lt_trans (lt_trans hri_lt hi) hnw
    have hlt_eval : (Expr.op .lt (.reg rI2) (.reg rIdxR)).eval w s = some 0 := by
      have := lt_eval (reg_eval hri hiw) (reg_eval rfl hrw) hw1
      simpa [show ¬ i < s.regs rIdxR by omega] using this
    refine ⟨s, _, .ite_false hlt_eval (.skip _), by simp [Expr.cost], hk, hri, ?_⟩
    exact Or.inr ⟨by omega, hra, hrb, hzero, hall⟩

/-- Full execution of `findRProg`. -/
theorem findRProg_exec {w : ℕ} {Pv : List (Fin N)} {bA bB : List ℕ}
    (hbA : bA.length = Pv.length) (hbB : bB.length = Pv.length)
    (hA_le : ∀ x ∈ bA, x ≤ 1) (hB_le : ∀ x ∈ bB, x ≤ 1)
    (hPn : Pv.length ≤ N) (hn : 4 * N + 4 < 2 ^ w)
    {s : State} (hpath : s.arrs aNewPath = Pv.map Fin.val)
    (hA : s.arrs aOnA = bA) (hB : s.arrs aOnB = bB) :
    ∃ s' t, Exec w findRProg s s' t ∧
      t ≤ 8 + 23 * N ∧
      Keeps [rI2, rIdxR] [] s s' ∧
      FindRInv bA bB Pv.length Pv.length (s'.regs rIdxR) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hPw : Pv.length < 2 ^ w := by omega
  set s₁ := s.setReg rIdxR Pv.length with hs₁
  have hex₁ : Exec w (.assign rIdxR (.len aNewPath)) s s₁ (1 + 1) :=
    .assign (len_eval_map hpath hPw)
  set s₂ := s₁.setReg rI2 0 with hs₂
  have hex₂ : Exec w (.assign rI2 (.const 0)) s₁ s₂ (1 + 1) :=
    .assign (const_eval' (by omega))
  let I : ℕ → State → Prop := fun i st =>
    Keeps [rI2, rIdxR] [] s st ∧
    st.regs rI2 = i ∧
    FindRInv bA bB Pv.length i (st.regs rIdxR)
  have hI0 : I 0 s₂ := ⟨((Keeps.refl _ _ s).setReg (by decide) _).setReg (by decide) _,
    by simp [s₂], Or.inl ⟨by simp [s₂, s₁], fun j hj => by omega⟩⟩
  have hloop := forUp_pot I (fun _ => 0) Pv.length 16 (r_i := rI2) (hi := .len aNewPath)
    (body := findRBody) hw1 hPw
    (fun i _ st hst => ⟨hst.2.1, len_eval_map (by rw [hst.1.2 aNewPath (by decide)]; exact hpath) hPw⟩)
    (fun i hi st hst => by
      obtain ⟨hk, hri, hinv⟩ := hst
      have hA' : st.arrs aOnA = bA := by rw [hk.2 aOnA (by decide)]; exact hA
      have hB' : st.arrs aOnB = bB := by rw [hk.2 aOnB (by decide)]; exact hB
      obtain ⟨s', t, hex, ht, hk', hri', hinv'⟩ :=
        findRBody_exec hbA hbB hA_le hB_le hi hPw hw1 hk hA' hB' hri hinv
      refine ⟨s', t, hex, by omega, ⟨hk'.setReg (by decide) _, by simp, ?_⟩, hri'⟩
      simpa [State.setReg_regs_ne _ _ (show rIdxR ≠ rI2 by decide)] using hinv')
    0 (Nat.zero_le _) s₂ hI0
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, -, hinv₃⟩ := hloop
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), ?_, hk₃, hinv₃⟩
  simp only [Expr.cost, Nat.sub_zero, Nat.add_zero] at ht₃
  omega

/-! ### Finding the first vertex `s = Pv[idx_s]` after `t = Pv[r]` on the missing side -/

/-- Body of `findOneFromProg aTarget`: if `rI2 < rIdxS` and `aTarget[rI2] == 1`, set `rIdxS := rI2`. -/
def findOneBody (aTarget : Arr) : Cmd :=
  .ite (.op .lt (.reg rI2) (.reg rIdxS))
    (.ite (.op .eq (.read aTarget (.reg rI2)) (.const 1))
      (.assign rIdxS (.reg rI2))
      .skip)
    .skip

/-- Scan `rIdxR + 1 .. len aNewPath` to find the first index `rIdxS > rIdxR` where
`aTarget[i] == 1`. -/
def findOneFromProg (aTarget : Arr) : Cmd :=
  .seq (.assign rIdxS (.len aNewPath))
    (.seq (.assign rI2 (.op .add (.reg rIdxR) (.const 1)))
      (forUp rI2 (.len aNewPath) (findOneBody aTarget)))

/-- Read `rSideT := aOnA[rIdxR]` and scan for the first `rIdxS > rIdxR` on the missing side
(`aOnB` if `rSideT == 1`, `aOnA` if `rSideT == 0`). -/
def findSProg : Cmd :=
  .seq (.assign rSideT (.read aOnA (.reg rIdxR)))
    (.ite (.op .eq (.reg rSideT) (.const 1))
      (findOneFromProg aOnB)
      (findOneFromProg aOnA))

/-- Invariant of `findOneFromProg` after scanning `[r + 1, i)`: either `idx_s = n` and all
`j ∈ (r, i)` have `bT[j] = 0`, or `r < idx_s < i` is the first index after `r` with
`bT[idx_s] = 1`. -/
def FindOneInv (bT : List ℕ) (n r i idx_s : ℕ) : Prop :=
  (idx_s = n ∧ ∀ j, r < j → j < i → (hj : j < bT.length) → bT[j] = 0) ∨
  (r < idx_s ∧ idx_s < i ∧ ∃ (hs : idx_s < bT.length),
    bT[idx_s] = 1 ∧ ∀ j, r < j → j < idx_s → (hj : j < bT.length) → bT[j] = 0)

theorem findOneBody_exec {w : ℕ} {aTarget : Arr} {bT : List ℕ} {n r i : ℕ}
    (hbT : bT.length = n) (hT_le : ∀ x ∈ bT, x ≤ 1)
    (hri_ge : r + 1 ≤ i) (hi : i < n) (hnw : n < 2 ^ w) (hw1 : 1 < 2 ^ w)
    {s₀ s : State} (hk : Keeps [rI2, rIdxS] [] s₀ s)
    (hT : s.arrs aTarget = bT) (hri : s.regs rI2 = i)
    (hinv : FindOneInv bT n r i (s.regs rIdxS)) :
    ∃ s' t, Exec w (findOneBody aTarget) s s' t ∧ t ≤ 13 ∧
      Keeps [rI2, rIdxS] [] s₀ s' ∧
      s'.regs rI2 = i ∧
      FindOneInv bT n r (i + 1) (s'.regs rIdxS) := by
  have hiw : i < 2 ^ w := lt_trans hi hnw
  have hit : i < bT.length := by omega
  have hvT : bT[i] ≤ 1 := hT_le _ (List.getElem_mem hit)
  rcases hinv with ⟨hsn, hall⟩ | ⟨hrs, hsi, hsb, hone, hall⟩
  · -- `s.regs rIdxS = n`, so `i < s.regs rIdxS` is true.
    have hlt_eval : (Expr.op .lt (.reg rI2) (.reg rIdxS)).eval w s = some 1 := by
      have := lt_eval (reg_eval hri hiw) (reg_eval hsn hnw) hw1
      simpa [hi] using this
    have hrT : (Expr.read aTarget (.reg rI2)).eval w s = some bT[i] := by
      rw [read_eval (reg_eval hri hiw) (by rw [hT]; exact hit)]
      · simp [hT]
      · simp [hT]; omega
    by_cases h1 : bT[i] = 1
    · have heq : (Expr.op .eq (.read aTarget (.reg rI2)) (.const 1)).eval w s = some 1 := by
        have := eq_eval hrT (const_eval' hw1) hw1
        simpa [h1] using this
      refine ⟨s.setReg rIdxS i, _,
        .ite_true hlt_eval one_ne_zero (.ite_true heq one_ne_zero (.assign (reg_eval hri hiw))),
        by simp [Expr.cost], hk.setReg (by decide) _, by simp [hri], ?_⟩
      simp only [State.setReg_regs_self]
      exact Or.inr ⟨by omega, by omega, hit, h1, fun j hj1 hj2 hj3 => hall j hj1 hj2 hj3⟩
    · have heq : (Expr.op .eq (.read aTarget (.reg rI2)) (.const 1)).eval w s = some 0 := by
        have := eq_eval hrT (const_eval' hw1) hw1
        simpa [h1] using this
      refine ⟨s, _, .ite_true hlt_eval one_ne_zero (.ite_false heq (.skip _)),
        by simp [Expr.cost], hk, hri, ?_⟩
      refine Or.inl ⟨hsn, fun j hj1 hj2 hj3 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj2 with hlt | rfl
      · exact hall j hj1 hlt hj3
      · omega
  · -- `s.regs rIdxS < i`, so `i < s.regs rIdxS` is false.
    have hsw : s.regs rIdxS < 2 ^ w := lt_trans (lt_trans hsi hi) hnw
    have hlt_eval : (Expr.op .lt (.reg rI2) (.reg rIdxS)).eval w s = some 0 := by
      have := lt_eval (reg_eval hri hiw) (reg_eval rfl hsw) hw1
      simpa [show ¬ i < s.regs rIdxS by omega] using this
    refine ⟨s, _, .ite_false hlt_eval (.skip _), by simp [Expr.cost], hk, hri, ?_⟩
    exact Or.inr ⟨hrs, by omega, hsb, hone, hall⟩

/-- Full execution of `findOneFromProg aTarget` when the last entry `bT[n - 1]` is `1` and
`r < n - 1`. -/
theorem findOneFromProg_exec {w : ℕ} {aTarget : Arr} {Pv : List (Fin N)} {bT : List ℕ} {r : ℕ}
    (hbT : bT.length = Pv.length) (hT_le : ∀ x ∈ bT, x ≤ 1)
    (hr_lt : r + 1 < Pv.length)
    (hlast : bT[Pv.length - 1]'(by omega) = 1)
    (hPn : Pv.length ≤ N) (hn : 4 * N + 4 < 2 ^ w)
    {s : State} (hpath : s.arrs aNewPath = Pv.map Fin.val)
    (hT : s.arrs aTarget = bT) (hrr : s.regs rIdxR = r) :
    ∃ s' t, Exec w (findOneFromProg aTarget) s s' t ∧
      t ≤ 10 + 20 * N ∧
      Keeps [rI2, rIdxS] [] s s' ∧
      r < s'.regs rIdxS ∧ s'.regs rIdxS < Pv.length ∧
      ∃ (hs : s'.regs rIdxS < bT.length),
        bT[s'.regs rIdxS] = 1 ∧
        ∀ j, r < j → j < s'.regs rIdxS → (hj : j < bT.length) → bT[j] = 0 := by
  have hw1 : 1 < 2 ^ w := by omega
  have hPw : Pv.length < 2 ^ w := by omega
  set s₁ := s.setReg rIdxS Pv.length with hs₁
  have hex₁ : Exec w (.assign rIdxS (.len aNewPath)) s s₁ (1 + 1) :=
    .assign (len_eval_map hpath hPw)
  set s₂ := s₁.setReg rI2 (r + 1) with hs₂
  have hex₂ : Exec w (.assign rI2 (.op .add (.reg rIdxR) (.const 1))) s₁ s₂ (1 + 1 + 1 + 1) :=
    .assign (add_eval (reg_eval (by simp [s₁, hrr]) (by omega)) (const_eval' hw1) (by omega))
  let I : ℕ → State → Prop := fun i st =>
    Keeps [rI2, rIdxS] [] s st ∧
    st.regs rI2 = i ∧
    FindOneInv bT Pv.length r i (st.regs rIdxS) ∧
    r + 1 ≤ i
  have hI0 : I (r + 1) s₂ := ⟨((Keeps.refl _ _ s).setReg (by decide) _).setReg (by decide) _,
    by simp [s₂], Or.inl ⟨by simp [s₂, s₁], fun j hj1 hj2 => by omega⟩, le_rfl⟩
  have hloop := forUp_pot I (fun _ => 0) Pv.length 13 (r_i := rI2) (hi := .len aNewPath)
    (body := findOneBody aTarget) hw1 hPw
    (fun i _ st hst => ⟨hst.2.1, len_eval_map (by rw [hst.1.2 aNewPath (by decide)]; exact hpath) hPw⟩)
    (fun i hi st hst => by
      obtain ⟨hk, hri, hinv, hge⟩ := hst
      have hT' : st.arrs aTarget = bT := by rw [hk.2 aTarget (by simp)]; exact hT
      obtain ⟨s', t, hex, ht, hk', hri', hinv'⟩ :=
        findOneBody_exec hbT hT_le hge hi hPw hw1 hk hT' hri hinv
      refine ⟨s', t, hex, by omega, ⟨hk'.setReg (by decide) _, by simp, ?_, by omega⟩, hri'⟩
      simpa [State.setReg_regs_ne _ _ (show rIdxS ≠ rI2 by decide)] using hinv')
    (r + 1) (by omega) s₂ hI0
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, -, hinv₃, -⟩ := hloop
  rcases hinv₃ with ⟨hsn, hall⟩ | ⟨hrs, hsi, hsb, hone, hall⟩
  · exfalso
    have h0 := hall (Pv.length - 1) (by omega) (by omega) (by omega)
    omega
  · refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), ?_, hk₃, hrs, hsi, hsb, hone, hall⟩
    simp only [Expr.cost, Nat.add_zero] at ht₃
    omega

/-- Full execution of `findSProg`. -/
theorem findSProg_exec {w : ℕ} {Pv : List (Fin N)} {bA bB : List ℕ} {r : ℕ}
    (hbA : bA.length = Pv.length) (hbB : bB.length = Pv.length)
    (hA_le : ∀ x ∈ bA, x ≤ 1) (hB_le : ∀ x ∈ bB, x ≤ 1)
    (hr_lt : r + 1 < Pv.length)
    (hlastA : bA[Pv.length - 1]'(by omega) = 1)
    (hlastB : bB[Pv.length - 1]'(by omega) = 1)
    (hPn : Pv.length ≤ N) (hn : 4 * N + 4 < 2 ^ w)
    {s : State} (hpath : s.arrs aNewPath = Pv.map Fin.val)
    (hA : s.arrs aOnA = bA) (hB : s.arrs aOnB = bB) (hrr : s.regs rIdxR = r) :
    ∃ s' t, Exec w findSProg s s' t ∧
      t ≤ 16 + 20 * N ∧
      Keeps [rSideT, rI2, rIdxS] [] s s' ∧
      r < s'.regs rIdxS ∧ ∃ (hslt : s'.regs rIdxS < Pv.length),
        ((bA[r]'(by omega) = 1 ∧ bB[s'.regs rIdxS]'(by omega) = 1 ∧
            ∀ j, r < j → j < s'.regs rIdxS → (hj : j < bB.length) → bB[j] = 0) ∨
          (bA[r]'(by omega) = 0 ∧ bA[s'.regs rIdxS]'(by omega) = 1 ∧
            ∀ j, r < j → j < s'.regs rIdxS → (hj : j < bA.length) → bA[j] = 0)) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hrw : r < 2 ^ w := by omega
  have hra : r < bA.length := by omega
  have hvA : bA[r] ≤ 1 := hA_le _ (List.getElem_mem hra)
  have hread : (Expr.read aOnA (.reg rIdxR)).eval w s = some bA[r] := by
    rw [read_eval (reg_eval hrr hrw) (by rw [hA]; exact hra)]
    · simp [hA]
    · simp [hA]; omega
  set s₁ := s.setReg rSideT bA[r] with hs₁
  have hex₁ : Exec w (.assign rSideT (.read aOnA (.reg rIdxR))) s s₁ (1 + 1 + 1) :=
    .assign hread
  have hk₁ : Keeps [rSideT, rI2, rIdxS] [] s s₁ := (Keeps.refl _ _ s).setReg (by decide) _
  have hs₁_side : s₁.regs rSideT = bA[r] := State.setReg_regs_self _ _ _
  have hs₁_path : s₁.arrs aNewPath = Pv.map Fin.val := hpath
  have hs₁_A : s₁.arrs aOnA = bA := hA
  have hs₁_B : s₁.arrs aOnB = bB := hB
  have hs₁_rr : s₁.regs rIdxR = r := by
    rw [State.setReg_regs_ne _ _ (by decide)]; exact hrr
  by_cases h1 : bA[r] = 1
  · have hcond : (Expr.op .eq (.reg rSideT) (.const 1)).eval w s₁ = some 1 := by
      have := eq_eval (reg_eval (hs₁_side.trans h1) hw1) (const_eval' hw1) hw1
      simpa using this
    obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hrs, hslt, hsb, hone, hall⟩ :=
      findOneFromProg_exec (aTarget := aOnB) hbB hB_le hr_lt hlastB hPn hn
        hs₁_path hs₁_B hs₁_rr
    refine ⟨s₂, _, .seq hex₁ (.ite_true hcond one_ne_zero hex₂),
      by simp [Expr.cost]; omega, hk₁.trans hk₂ (by decide) (by decide), hrs, hslt,
      Or.inl ⟨h1, hone, hall⟩⟩
  · have h0 : bA[r] = 0 := by omega
    have hcond : (Expr.op .eq (.reg rSideT) (.const 1)).eval w s₁ = some 0 := by
      have := eq_eval (reg_eval (hs₁_side.trans h0) (by omega)) (const_eval' hw1) hw1
      simpa using this
    obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hrs, hslt, hsa, hone, hall⟩ :=
      findOneFromProg_exec (aTarget := aOnA) hbA hA_le hr_lt hlastA hPn hn
        hs₁_path hs₁_A hs₁_rr
    refine ⟨s₂, _, .seq hex₁ (.ite_false hcond hex₂),
      by simp [Expr.cost]; omega, hk₁.trans hk₂ (by decide) (by decide), hrs, hslt,
      Or.inr ⟨h0, hone, hall⟩⟩

/-! ### Appending `[y, s]` to `aF` and shortening `aNewPath` -/

/-- Append `[rValY, rValS]` to `aF`. -/
def appendEdgeProg : Cmd :=
  .seq (.alloc aTmp (.op .add (.len aF) (.const 2)))
    (.seq (.assign rAp (.const 0))
      (.seq (appProg rI3 rAp (.const 0) (.len aF) aTmp aF (.reg rI3))
        (.seq (.write aTmp (.reg rAp) (.reg rValY))
          (.seq (.write aTmp (.op .add (.reg rAp) (.const 1)) (.reg rValS))
            (copyFromTmp aF)))))

theorem appendEdgeProg_exec {w : ℕ} {F : List ℕ} {vy vs : ℕ}
    (hF_lt : ∀ x ∈ F, x < N) (hvy : vy < N) (hvs : vs < N)
    (hFn : F.length ≤ 2 * N) (hn : 4 * N + 4 < 2 ^ w)
    {s : State} (hF : s.arrs aF = F) (hry : s.regs rValY = vy) (hrs : s.regs rValS = vs) :
    ∃ s' t, Exec w appendEdgeProg s s' t ∧
      t ≤ 50 + 56 * N ∧
      Keeps [rI3, rAp] [aTmp, aF] s s' ∧
      s'.arrs aF = F ++ [vy, vs] := by
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : N < 2 ^ w := by omega
  have hFw : ∀ x ∈ F, x < 2 ^ w := fun x hx => lt_trans (hF_lt x hx) hnw
  have hlenF : (Expr.len aF).eval w s = some F.length := len_eval hF (by omega)
  set s₁ := s.setArr aTmp (List.replicate (F.length + 2) 0) with hs₁
  have hex₁ : Exec w (.alloc aTmp (.op .add (.len aF) (.const 2))) s s₁
      ((1 + 1 + 1) + (F.length + 2)) :=
    .alloc (add_eval hlenF (const_eval' (by omega)) (by omega))
  set s₂ := s₁.setReg rAp 0 with hs₂
  have hex₂ : Exec w (.assign rAp (.const 0)) s₁ s₂ (1 + 1) := .assign (const_eval' (by omega))
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hrc₃, hd₃⟩ := appProg_exec rI3 rAp (.const 0) (.len aF) aTmp aF
    (.reg rI3) (by decide) (by decide) F [] (List.replicate (F.length + 2) 0) (fun i => i) 0
    F.length s₂ hw1 (Nat.zero_le _) (by simp) (by simp; omega) (by omega)
    (const_eval' (by omega))
    (fun st hst => len_eval (by rw [hst.2 aF (by decide)]; simp [s₂, s₁, hF]) (by omega))
    (fun _ i _ hri _ hi => reg_eval hri (by omega))
    (fun i _ hi => hi) hFw (by simp [s₂, s₁, hF]) (by simp [s₂, s₁]) (by simp [s₂])
  rw [List.length_nil, Nat.zero_add, Nat.sub_zero] at hrc₃
  have hd₃' : s₃.arrs aTmp = F ++ [0, 0] := by
    rw [hd₃, List.nil_append, Nat.sub_zero, map_range'_getD F 0 F.length (by omega),
      List.drop_zero, List.take_length, List.drop_replicate,
      show F.length + 2 - F.length = 2 by omega]
    rfl
  have hry₃ : s₃.regs rValY = vy := by rw [hk₃.1 rValY (by decide)]; simp [s₂, s₁, hry]
  have hrs₃ : s₃.regs rValS = vs := by rw [hk₃.1 rValS (by decide)]; simp [s₂, s₁, hrs]
  set s₄ := s₃.writeArr aTmp F.length vy with hs₄
  have hex₄ : Exec w (.write aTmp (.reg rAp) (.reg rValY)) s₃ s₄ (1 + 1 + 1) :=
    .write (reg_eval hrc₃ (by omega)) (reg_eval hry₃ (lt_trans hvy hnw))
      (by rw [hd₃']; simp)
  have hd₄ : s₄.arrs aTmp = F ++ [vy, 0] := by
    simp only [s₄, State.writeArr_arrs_self, hd₃']
    rw [List.set_append_right _ _ le_rfl, Nat.sub_self, List.set_cons_zero]
  set s₅ := s₄.writeArr aTmp (F.length + 1) vs with hs₅
  have hex₅ : Exec w (.write aTmp (.op .add (.reg rAp) (.const 1)) (.reg rValS)) s₄ s₅
      ((1 + 1 + 1) + 1 + 1) :=
    .write (add_eval (reg_eval (by simp [s₄, hrc₃]) (by omega)) (const_eval' hw1) (by omega))
      (reg_eval (by simp [s₄, hrs₃]) (lt_trans hvs hnw))
      (by rw [hd₄]; simp)
  have hd₅ : s₅.arrs aTmp = F ++ [vy, vs] := by
    simp only [s₅, State.writeArr_arrs_self, hd₄]
    rw [List.set_append_right _ _ (by omega), show F.length + 1 - F.length = 1 by omega]
    rfl
  have hF'_lt : ∀ x ∈ F ++ [vy, vs], x < 2 ^ w := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | rfl | rfl
    · exact hFw x hx
    · exact lt_trans hvy hnw
    · exact lt_trans hvs hnw
  obtain ⟨s₆, t₆, hex₆, ht₆, hk₆, hd₆⟩ := copyFromTmp_exec aF (by decide) (F ++ [vy, vs]) s₅
    hw1 (by simp; omega) hF'_lt hd₅
  have hk_all : Keeps [rI3, rAp] [aTmp, aF] s s₆ :=
    (((((((Keeps.refl _ _ s).setArr (by decide) _).setReg (by decide) _).trans hk₃
      (by decide) (by decide)).writeArr (by decide) _ _).writeArr (by decide) _ _).trans hk₆
      (by decide) (by decide))
  refine ⟨s₆, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), ?_, hk_all, hd₆⟩
  simp only [Expr.cost, List.length_append, List.length_cons, List.length_nil] at ht₃ ht₆
  omega

/-- Replace `aNewPath` (`Pv`) by `Pv.take rIdxR ++ Pv.drop rIdxS`. -/
def shortenPathProg : Cmd :=
  .seq (.alloc aTmp (.op .add (.reg rIdxR) (.op .sub (.len aNewPath) (.reg rIdxS))))
    (.seq (.assign rAp (.const 0))
      (.seq (appProg rI3 rAp (.const 0) (.reg rIdxR) aTmp aNewPath (.reg rI3))
        (.seq (appProg rI3 rAp (.reg rIdxS) (.len aNewPath) aTmp aNewPath (.reg rI3))
          (copyFromTmp aNewPath))))

theorem shortenPathProg_exec {w : ℕ} {Pv : List (Fin N)} {r idx_s : ℕ}
    (hr0 : 0 < r) (hrs : r < idx_s) (hsL : idx_s < Pv.length)
    (hPn : Pv.length ≤ N) (hn : 4 * N + 4 < 2 ^ w)
    {s : State} (hpath : s.arrs aNewPath = Pv.map Fin.val)
    (hrr : s.regs rIdxR = r) (hris : s.regs rIdxS = idx_s) :
    ∃ s' t, Exec w shortenPathProg s s' t ∧
      t ≤ 25 + 30 * N ∧
      Keeps [rI3, rAp] [aTmp, aNewPath] s s' ∧
      s'.arrs aNewPath = (Pv.take r ++ Pv.drop idx_s).map Fin.val := by
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : N < 2 ^ w := by omega
  have hPw : Pv.length < 2 ^ w := by omega
  have hPv_lt : ∀ x ∈ Pv.map Fin.val, x < 2 ^ w := vals_lt hnw
  set k := r + (Pv.length - idx_s) with hk_def
  have halloc_eval : (Expr.op .add (.reg rIdxR)
      (.op .sub (.len aNewPath) (.reg rIdxS))).eval w s = some k :=
    add_eval (reg_eval hrr (by omega))
      (sub_eval (len_eval_map hpath hPw) (reg_eval hris (by omega))) (by omega)
  set s₁ := s.setArr aTmp (List.replicate k 0) with hs₁
  have hex₁ : Exec w (.alloc aTmp (.op .add (.reg rIdxR) (.op .sub (.len aNewPath) (.reg rIdxS))))
      s s₁ ((1 + (1 + 1 + 1) + 1) + k) := .alloc halloc_eval
  set s₂ := s₁.setReg rAp 0 with hs₂
  have hex₂ : Exec w (.assign rAp (.const 0)) s₁ s₂ (1 + 1) := .assign (const_eval' (by omega))
  -- Copy Pv.take r
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hrc₃, hd₃⟩ := appProg_exec rI3 rAp (.const 0) (.reg rIdxR)
    aTmp aNewPath (.reg rI3) (by decide) (by decide) (Pv.map Fin.val) [] (List.replicate k 0)
    (fun i => i) 0 r s₂ hw1 (Nat.zero_le _) (by simp [k]) (by simp [k]; omega) (by omega)
    (const_eval' (by omega))
    (fun st hst => reg_eval (by rw [hst.1 rIdxR (by decide)]; simp [s₂, s₁, hrr]) (by omega))
    (fun _ i _ hri _ _ => reg_eval hri (by omega))
    (fun i _ hi => by simp; omega) hPv_lt (by simp [s₂, s₁, hpath]) (by simp [s₂, s₁])
    (by simp [s₂])
  rw [List.length_nil, Nat.zero_add, Nat.sub_zero] at hrc₃
  have hd₃' : s₃.arrs aTmp = (Pv.take r).map Fin.val ++ List.replicate (Pv.length - idx_s) 0 := by
    rw [hd₃, List.nil_append, Nat.sub_zero,
      map_range'_getD (Pv.map Fin.val) 0 r (by simp; omega),
      List.drop_zero, ← List.map_take, List.drop_replicate,
      show k - r = Pv.length - idx_s by omega]
  have hpath₃ : s₃.arrs aNewPath = Pv.map Fin.val := by
    rw [hk₃.2 aNewPath (by decide)]; simp [s₂, s₁, hpath]
  have hris₃ : s₃.regs rIdxS = idx_s := by
    rw [hk₃.1 rIdxS (by decide)]; simp [s₂, s₁, hris]
  -- Copy Pv.drop idx_s
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, -, hd₄⟩ := appProg_exec rI3 rAp (.reg rIdxS) (.len aNewPath)
    aTmp aNewPath (.reg rI3) (by decide) (by decide) (Pv.map Fin.val) ((Pv.take r).map Fin.val)
    (List.replicate (Pv.length - idx_s) 0) (fun i => i) idx_s Pv.length s₃ hw1 (by omega)
    (by simp) (by simp; omega) hPw
    (reg_eval hris₃ (by omega))
    (fun st hst => len_eval_map (by rw [hst.2 aNewPath (by decide)]; exact hpath₃) hPw)
    (fun _ i _ hri _ _ => reg_eval hri (by omega))
    (fun i _ hi => by simp; omega) hPv_lt hpath₃ hd₃'
    (by rw [hrc₃]; simp [Nat.min_eq_left (show r ≤ Pv.length by omega)])
  have hd₄' : s₄.arrs aTmp = (Pv.take r ++ Pv.drop idx_s).map Fin.val := by
    have hdrop : List.map (fun i => (Pv.map Fin.val).getD i 0)
        (List.range' idx_s (Pv.length - idx_s)) = (Pv.drop idx_s).map Fin.val := by
      rw [map_range'_getD (Pv.map Fin.val) idx_s (Pv.length - idx_s) (by simp; omega),
        ← List.map_drop, ← List.map_take, List.take_of_length_le (by simp)]
    rw [hd₄, hdrop, List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil,
      ← List.map_append]
  have hnew_lt : ∀ x ∈ (Pv.take r ++ Pv.drop idx_s).map Fin.val, x < 2 ^ w := vals_lt hnw
  obtain ⟨s₅, t₅, hex₅, ht₅, hk₅, hd₅⟩ := copyFromTmp_exec aNewPath (by decide)
    ((Pv.take r ++ Pv.drop idx_s).map Fin.val) s₄ hw1 (by simp; omega) hnew_lt hd₄'
  have hk_all : Keeps [rI3, rAp] [aTmp, aNewPath] s s₅ :=
    ((((((Keeps.refl _ _ s).setArr (by decide) _).setReg (by decide) _).trans hk₃
      (by decide) (by decide)).trans hk₄ (by decide) (by decide)).trans hk₅
      (by decide) (by decide))
  refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), ?_, hk_all, hd₅⟩
  simp only [Expr.cost, Nat.sub_zero, List.length_map, List.length_append, List.length_take,
    List.length_drop] at ht₃ ht₄ ht₅
  omega

/-! ### Complete single step `stepProg` -/

/-- One iteration of the `while` loop of Algorithm 5.2. -/
def stepProg : Cmd :=
  .seq bothSidesProg
    (.seq findRProg
      (.ite (.op .eq (.reg rIdxR) (.len aNewPath))
        (.assign rDone (.const 1))
        (.seq findSProg
          (.seq (.assign rValY (.read aNewPath (.op .sub (.reg rIdxR) (.const 1))))
            (.seq (.assign rValS (.read aNewPath (.reg rIdxS)))
              (.seq appendEdgeProg
                shortenPathProg))))))

/-- **One iteration of the loop.** Given the loop invariant for the current path `P` and edge list
`F` (whose edges all lie on `P.support` via the prefix `M <+: P.support`), `stepProg` runs in at
most `300 + 420 N + 98 M_adj` steps and either:
* sets `rDone = 1` when `OnBothSides (H ⊔ pairGraph N F) (a :: A ++ b :: B) A B P` holds, leaving
  `aF` and `aNewPath` unchanged; or
* keeps `rDone = 0`, appends a safe pair `[y.1, s.1]` to `aF`, updates `aNewPath` to a strictly
  shorter `C`-path `P'`, and extends the prefix `M` on both sides to a strictly longer prefix
  `M' <+: P'.support`. -/
theorem stepProg_exec {w : ℕ} {H : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {a b : Fin N} {A B M : List (Fin N)} {F : List ℕ}
    {P : (H ⊔ pairGraph N F).Walk a b}
    (hC : IsCycleList (H ⊔ pairGraph N F) (a :: A ++ b :: B))
    (hA_ne : A ≠ []) (hB_ne : B ≠ [])
    (hP : IsTPath (H ⊔ pairGraph N F) (a :: A ++ b :: B) P)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support,
      (H ⊔ pairGraph N F).Adj u v → IsListEdge P.support u v)
    (hsep : Separates (H ⊔ pairGraph N F) {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B})
    (htight : IsTight (H ⊔ pairGraph N F) (a :: A ++ b :: B) A B P.support)
    (hsided : ∀ v ∈ P.support,
      IsSided (H ⊔ pairGraph N F) {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} A B v)
    (hM_pref : M <+: P.support)
    (hM_both : ∀ v ∈ M,
      IsOnSide (H ⊔ pairGraph N F) {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ A} v ∧
      IsOnSide (H ⊔ pairGraph N F) {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ B} v)
    (hF_in_M : ∀ u v, (pairGraph N F).Adj u v → u ∈ M ∧ v ∈ M)
    (hF_even : Even F.length)
    (hF_lt : ∀ x ∈ F, x < N)
    (hFn : F.length ≤ 2 * N)
    {s : State}
    (h40 : s.regs 40 = N) (hlenA : s.regs rLenA = A.length)
    (hrDone : s.regs rDone = 0)
    (hadj : IsAdjList H aStart aEnd aEnt lists s)
    (hent : (s.arrs aEnt).length < 2 ^ w)
    (hcyc : s.arrs aCyc = (a :: A ++ b :: B).map Fin.val)
    (hpath : s.arrs aNewPath = P.support.map Fin.val)
    (hF : s.arrs aF = F)
    (hn : 4 * N + 4 < 2 ^ w) :
    ∃ s' t, Exec w stepProg s s' t ∧
      t ≤ 350 + 450 * N + 98 * totalAdjEntries lists ∧
      Keeps loopStepRegs loopStepArrs s s' ∧
      ((s'.regs rDone = 1 ∧ s'.arrs aF = F ∧ s'.arrs aNewPath = P.support.map Fin.val ∧
          OnBothSides (H ⊔ pairGraph N F) (a :: A ++ b :: B) A B P) ∨
        (s'.regs rDone = 0 ∧
          ∃ (y s_v : Fin N) (M' : List (Fin N)) (P' : (H ⊔ pairGraph N (F ++ [y.1, s_v.1])).Walk a b),
            y ≠ s_v ∧ y ∈ P.support ∧ s_v ∈ P.support ∧
            ¬ (H ⊔ pairGraph N F).Adj y s_v ∧
            IsSafe (H ⊔ pairGraph N F) (edge y s_v) (a :: A ++ b :: B) ∧
            s'.arrs aF = F ++ [y.1, s_v.1] ∧
            s'.arrs aNewPath = P'.support.map Fin.val ∧
            P'.support.Sublist P.support ∧
            P'.support.length < P.support.length ∧
            M.length + 1 ≤ M'.length ∧
            M' <+: P'.support ∧
            IsTPath (H ⊔ pairGraph N (F ++ [y.1, s_v.1])) (a :: A ++ b :: B) P' ∧
            (∀ u ∈ P'.support, ∀ v ∈ P'.support,
              (H ⊔ pairGraph N (F ++ [y.1, s_v.1])).Adj u v → IsListEdge P'.support u v) ∧
            Separates (H ⊔ pairGraph N (F ++ [y.1, s_v.1]))
              {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
            IsTight (H ⊔ pairGraph N (F ++ [y.1, s_v.1])) (a :: A ++ b :: B) A B P'.support ∧
            (∀ v ∈ P'.support, IsSided (H ⊔ pairGraph N (F ++ [y.1, s_v.1]))
              {x | x ∈ a :: A ++ b :: B ∨ x ∈ P'.support} A B v) ∧
            (∀ v ∈ M',
              IsOnSide (H ⊔ pairGraph N (F ++ [y.1, s_v.1]))
                {x | x ∈ a :: A ++ b :: B ∨ x ∈ P'.support} {x | x ∈ A} v ∧
              IsOnSide (H ⊔ pairGraph N (F ++ [y.1, s_v.1]))
                {x | x ∈ a :: A ++ b :: B ∨ x ∈ P'.support} {x | x ∈ B} v) ∧
            (∀ u v, (pairGraph N (F ++ [y.1, s_v.1])).Adj u v → u ∈ M' ∧ v ∈ M') ∧
            (∀ M₀, M₀ <+: P.support →
              (∀ v ∈ M₀,
                IsOnSide (H ⊔ pairGraph N F)
                  {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ A} v ∧
                IsOnSide (H ⊔ pairGraph N F)
                  {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ B} v) →
              M₀ <+: M'))) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : N < 2 ^ w := by omega
  let C := a :: A ++ b :: B
  let Pv := P.support
  let G := H ⊔ pairGraph N F
  have hC_nd : C.Nodup := hC.2.1
  have hPv_nd : Pv.Nodup := hP.1.support_nodup
  have hPv_ne : Pv ≠ [] := by exact SimpleGraph.Walk.support_ne_nil P
  have hPn : Pv.length ≤ N := by have := hPv_nd.length_le_card; simpa using this
  have hPw : Pv.length < 2 ^ w := by omega
  have hF_in_Pv : ∀ u v, (pairGraph N F).Adj u v → u ∈ Pv ∧ v ∈ Pv := fun u v huv =>
    ⟨hM_pref.subset (hF_in_M u v huv).1, hM_pref.subset (hF_in_M u v huv).2⟩
  -- Disjointness of A and B from Pv
  have ha_ne_b : a ≠ b := by
    intro hab; subst hab
    have hnd : (a :: A ++ a :: B).Nodup := hC.2.1
    rw [List.cons_append, List.nodup_cons] at hnd
    exact hnd.1 (by simp)
  have hAP : ∀ x ∈ A, x ∉ Pv := fun x hx =>
    notMem_support_of_mem hC hP (List.mem_append_left B hx)
  have hBP : ∀ x ∈ B, x ∉ Pv := fun x hx =>
    notMem_support_of_mem hC hP (List.mem_append_right A hx)
  -- Sides in G agree with sides in H
  have hadjG : ∀ u v, G.Adj u v → H.Adj u v ∨ (u ∈ Pv ∧ v ∈ Pv) :=
    fun u v h => h.imp id (hF_in_Pv u v)
  have hsideA : ∀ v ∈ Pv, IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ A} v ↔
      IsOnSide H {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ A} v :=
    fun v hv => isOnSide_iff_of_edges_in_path le_sup_left hadjG hAP hv
  have hsideB : ∀ v ∈ Pv, IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ B} v ↔
      IsOnSide H {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ B} v :=
    fun v hv => isOnSide_iff_of_edges_in_path le_sup_left hadjG hBP hv
  -- Endpoints a = Pv[0] and b = Pv[Pv.length - 1] are on both sides
  have hends : (IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ A} a ∧
      IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ B} a) ∧
      (IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ A} b ∧
      IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ B} b) :=
    ends_both hC (List.rotate_zero _) hA_ne hB_ne
  have hlen_ge2 : 2 ≤ Pv.length := by
    have ha_mem : a ∈ P.support := SimpleGraph.Walk.start_mem_support P
    have hb_mem : b ∈ P.support := SimpleGraph.Walk.end_mem_support P
    rcases h : P.support with _ | ⟨x, _ | ⟨y, tl⟩⟩
    · exact absurd h hPv_ne
    · rw [h, List.mem_singleton] at ha_mem hb_mem
      exact absurd (ha_mem.trans hb_mem.symm) ha_ne_b
    · simp [Pv, h]
  have hPv0 : Pv[0]'(by omega) = a := by
    have := SimpleGraph.Walk.head_support P
    rwa [List.head_eq_getElem] at this
  have hPv_last : Pv[Pv.length - 1]'(by omega) = b := by
    have := SimpleGraph.Walk.getLast_support P
    rwa [List.getLast_eq_getElem] at this
  -- Step 1: bothSidesProg
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hA₁, hB₁⟩ :=
    bothSidesProg_exec hC_nd hPv_nd hPv_ne hAP hBP h40 hlenA hadj hent hcyc hpath hn
  set bA := Pv.map (sideBit H C Pv A) with hbA_def
  set bB := Pv.map (sideBit H C Pv B) with hbB_def
  have hbA_len : bA.length = Pv.length := List.length_map _
  have hbB_len : bB.length = Pv.length := List.length_map _
  have hbA_le : ∀ x ∈ bA, x ≤ 1 := by
    intro x hx; obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx; exact sideBit_le_one H C Pv A v
  have hbB_le : ∀ x ∈ bB, x ≤ 1 := by
    intro x hx; obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx; exact sideBit_le_one H C Pv B v
  have hpath₁ : s₁.arrs aNewPath = Pv.map Fin.val := by
    rw [hk₁.2 aNewPath (by decide)]; exact hpath
  -- Step 2: findRProg
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hinvR⟩ :=
    findRProg_exec hbA_len hbB_len hbA_le hbB_le hPn hn hpath₁ hA₁ hB₁
  have hk₁₂ : Keeps loopStepRegs loopSideArrs s s₂ :=
    (hk₁.mono (by decide) (by decide)).trans hk₂ (by decide) (by decide)
  have hpath₂ : s₂.arrs aNewPath = Pv.map Fin.val := by
    rw [hk₁₂.2 aNewPath (by decide)]; exact hpath
  have hA₂ : s₂.arrs aOnA = bA := by rw [hk₂.2 aOnA (by decide)]; exact hA₁
  have hB₂ : s₂.arrs aOnB = bB := by rw [hk₂.2 aOnB (by decide)]; exact hB₁
  -- Step 3: branch on rIdxR == Pv.length
  rcases hinvR with ⟨hrn, hall⟩ | ⟨hr_lt, hra, hrb, hzero, hall⟩
  · -- Branch 1: all vertices on both sides (`rIdxR = Pv.length`)
    have hcond : (Expr.op .eq (.reg rIdxR) (.len aNewPath)).eval w s₂ = some 1 := by
      have := eq_eval (reg_eval hrn hPw) (len_eval_map hpath₂ hPw) hw1
      simpa using this
    set s₃ := s₂.setReg rDone 1 with hs₃
    have hex₃ : Exec w (.assign rDone (.const 1)) s₂ s₃ (1 + 1) :=
      .assign (const_eval' hw1)
    have hk_fin : Keeps loopStepRegs loopStepArrs s s₃ :=
      (hk₁₂.mono (by decide) (by decide)).setReg (by decide) _
    have hboth : OnBothSides G C A B P := by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
      have ⟨h1, h2⟩ := hall j hj (by rw [hbA_len]; exact hj) (by rw [hbB_len]; exact hj)
      simp only [bA, bB, List.getElem_map, sideBit_eq_one_iff] at h1 h2
      exact ⟨(hsideA _ hv).mpr h1, (hsideB _ hv).mpr h2⟩
    refine ⟨s₃, _, .seq hex₁ (.seq hex₂ (.ite_true hcond one_ne_zero hex₃)),
      by simp [Expr.cost]; omega, hk_fin, Or.inl ⟨by simp [s₃], ?_, ?_, hboth⟩⟩
    · simp only [s₃, State.setReg_arrs]; rw [hk₁₂.2 aF (by decide)]; exact hF
    · simp only [s₃, State.setReg_arrs]; rw [hk₁₂.2 aNewPath (by decide)]; exact hpath
  · -- Branch 2: `r < Pv.length` is the first vertex not on both sides
    set r := s₂.regs rIdxR with hr_def
    have hcond : (Expr.op .eq (.reg rIdxR) (.len aNewPath)).eval w s₂ = some 0 := by
      have := eq_eval (reg_eval (v := r) rfl (lt_trans hr_lt hPw)) (len_eval_map hpath₂ hPw) hw1
      simpa [Nat.ne_of_lt hr_lt] using this
    -- Prove `0 < r` and `r + 1 < Pv.length` using `ends_both`
    have hbA0 : bA[0]'(by omega) = 1 := by
      simp only [bA, List.getElem_map, hPv0, sideBit_eq_one_iff]
      exact (hsideA a (SimpleGraph.Walk.start_mem_support P)).mp hends.1.1
    have hbB0 : bB[0]'(by omega) = 1 := by
      simp only [bB, List.getElem_map, hPv0, sideBit_eq_one_iff]
      exact (hsideB a (SimpleGraph.Walk.start_mem_support P)).mp hends.1.2
    have hbA_last : bA[Pv.length - 1]'(by omega) = 1 := by
      simp only [bA, List.getElem_map, hPv_last, sideBit_eq_one_iff]
      exact (hsideA b (SimpleGraph.Walk.end_mem_support P)).mp hends.2.1
    have hbB_last : bB[Pv.length - 1]'(by omega) = 1 := by
      simp only [bB, List.getElem_map, hPv_last, sideBit_eq_one_iff]
      exact (hsideB b (SimpleGraph.Walk.end_mem_support P)).mp hends.2.2
    have hr0 : 0 < r := by
      by_contra h
      have hr_eq : r = 0 := by omega
      have hz : bA[r] * bB[r] = 0 := hzero
      simp only [hr_eq, hbA0, hbB0] at hz
      omega
    have hr_lt_last : r + 1 < Pv.length := by
      by_contra h
      have hr_eq : r = Pv.length - 1 := by omega
      have hz : bA[r] * bB[r] = 0 := hzero
      simp only [hr_eq, hbA_last, hbB_last] at hz
      omega
    -- Step 3a: findSProg
    obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hrs, hsL, hcaseS⟩ :=
      findSProg_exec hbA_len hbB_len hbA_le hbB_le hr_lt_last hbA_last hbB_last
        hPn hn hpath₂ hA₂ hB₂ rfl
    set idx_s := s₃.regs rIdxS with hidx_s_def
    have hk₁₃ : Keeps loopStepRegs loopSideArrs s s₃ :=
      hk₁₂.trans hk₃ (by decide) (by decide)
    have hpath₃ : s₃.arrs aNewPath = Pv.map Fin.val := by
      rw [hk₁₃.2 aNewPath (by decide)]; exact hpath
    have hrr₃ : s₃.regs rIdxR = r := by rw [hk₃.1 rIdxR (by decide)]
    -- Step 3b: read y = Pv[r - 1] and s_v = Pv[idx_s]
    set y := Pv[r - 1]'(by omega) with hy_def
    set t_v := Pv[r]'hr_lt with ht_def
    set s_v := Pv[idx_s]'hsL with hs_def
    have hread_y : (Expr.read aNewPath (.op .sub (.reg rIdxR) (.const 1))).eval w s₃ =
        some y.1 := by
      rw [read_eval (sub_eval (reg_eval hrr₃ (by omega)) (const_eval' hw1))
        (by rw [hpath₃]; simp; omega)]
      · simp [hpath₃, y]
      · simp [hpath₃]; exact lt_trans y.2 hnw
    set s₄ := s₃.setReg rValY y.1 with hs₄
    have hex₄ : Exec w (.assign rValY (.read aNewPath (.op .sub (.reg rIdxR) (.const 1))))
        s₃ s₄ ((1 + 1 + 1) + 1 + 1) := .assign hread_y
    have hread_s : (Expr.read aNewPath (.reg rIdxS)).eval w s₄ = some s_v.1 := by
      rw [read_eval (reg_eval (v := idx_s) (by simp [s₄]; rfl) (by omega))
        (by simp [s₄, hpath₃]; exact hsL)]
      · simp [s₄, hpath₃, s_v]
      · simp [s₄, hpath₃]; exact lt_trans s_v.2 hnw
    set s₅ := s₄.setReg rValS s_v.1 with hs₅
    have hex₅ : Exec w (.assign rValS (.read aNewPath (.reg rIdxS))) s₄ s₅ (1 + 1 + 1) :=
      .assign hread_s
    have hk₁₅ : Keeps loopStepRegs loopStepArrs s s₅ :=
      ((hk₁₃.mono (by decide) (by decide)).setReg (by decide) _).setReg (by decide) _
    have hF₅ : s₅.arrs aF = F := by
      simp only [s₅, s₄, State.setReg_arrs]
      rw [hk₁₃.2 aF (by decide)]
      exact hF
    -- Step 3c: appendEdgeProg
    obtain ⟨s₆, t₆, hex₆, ht₆, hk₆, hF₆⟩ :=
      appendEdgeProg_exec hF_lt y.2 s_v.2 hFn hn hF₅ (by simp [s₅, s₄]) (by simp [s₅])
    have hk₁₆ : Keeps loopStepRegs loopStepArrs s s₆ :=
      hk₁₅.trans hk₆ (by decide) (by decide)
    have hpath₆ : s₆.arrs aNewPath = Pv.map Fin.val := by
      rw [hk₆.2 aNewPath (by decide)]; simp [s₅, s₄, hpath₃]
    have hrr₆ : s₆.regs rIdxR = r := by
      rw [hk₆.1 rIdxR (by decide)]; simp [s₅, s₄, hrr₃]
    have hris₆ : s₆.regs rIdxS = idx_s := by
      rw [hk₆.1 rIdxS (by decide)]; simp [s₅, s₄, hidx_s_def]
    -- Step 3d: shortenPathProg
    obtain ⟨s₇, t₇, hex₇, ht₇, hk₇, hpath₇⟩ :=
      shortenPathProg_exec hr0 hrs hsL hPn hn hpath₆ hrr₆ hris₆
    have hk_fin : Keeps loopStepRegs loopStepArrs s s₇ :=
      hk₁₆.trans hk₇ (by decide) (by decide)
    have hF₇ : s₇.arrs aF = F ++ [y.1, s_v.1] := by
      rw [hk₇.2 aF (by decide)]; exact hF₆
    have hrDone₇ : s₇.regs rDone = 0 := by
      rw [hk₇.1 rDone (by decide), hk₆.1 rDone (by decide),
        State.setReg_regs_ne _ _ (by decide), State.setReg_regs_ne _ _ (by decide),
        hk₃.1 rDone (by decide), hk₂.1 rDone (by decide), hk₁.1 rDone (by decide)]
      exact hrDone
    -- Apply `split_path_at_indices` and `loop_step_math`
    set L₁ := Pv.take (r - 1)
    set N' := (Pv.take idx_s).drop (r + 1)
    set L₂ := Pv.drop (idx_s + 1)
    obtain ⟨hPv_split, htake_drop, hL₁y, hmem_L₁y, hmem_tN'⟩ :=
      split_path_at_indices Pv hr0 hrs hsL
    have hpre_both : ∀ v ∈ L₁ ++ [y],
        IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ A} v ∧
        IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ B} v := by
      intro v hv
      obtain ⟨i, hi_lt, rfl⟩ := hmem_L₁y v hv
      have ⟨h1, h2⟩ := hall i hi_lt (by simp [bA]; omega) (by simp [bB]; omega)
      simp only [bA, bB, List.getElem_map, sideBit_eq_one_iff] at h1 h2
      exact ⟨(hsideA _ (List.getElem_mem (by omega))).mpr h1,
        (hsideB _ (List.getElem_mem (by omega))).mpr h2⟩
    have ht_not_both : ¬ (IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ A} t_v ∧
        IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ B} t_v) := by
      rintro ⟨h1, h2⟩
      have h1' : bA[r] = 1 := by
        simp only [bA, List.getElem_map, sideBit_eq_one_iff]
        exact (hsideA t_v (List.getElem_mem hr_lt)).mp h1
      have h2' : bB[r] = 1 := by
        simp only [bB, List.getElem_map, sideBit_eq_one_iff]
        exact (hsideB t_v (List.getElem_mem hr_lt)).mp h2
      have hz := hzero
      rw [h1', h2'] at hz
      contradiction
    have hcase_math :
        (IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ A} t_v ∧
          IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ B} s_v ∧
          ∀ v ∈ t_v :: N', ¬ IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ B} v) ∨
        (IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ B} t_v ∧
          IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ A} s_v ∧
          ∀ v ∈ t_v :: N', ¬ IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ A} v) := by
      rcases hcaseS with ⟨htA, hsB, h0B⟩ | ⟨htA0, hsA, h0A⟩
      · refine Or.inl ⟨?_, ?_, ?_⟩
        · simp only [bA, List.getElem_map, sideBit_eq_one_iff] at htA
          exact (hsideA t_v (List.getElem_mem hr_lt)).mpr htA
        · simp only [bB, List.getElem_map, sideBit_eq_one_iff] at hsB
          exact (hsideB s_v (List.getElem_mem hsL)).mpr hsB
        · intro v hv
          obtain ⟨i, hri_le, hi_lt, rfl⟩ := hmem_tN' v hv
          rw [hsideB _ (List.getElem_mem (by omega)), ← sideBit_eq_zero_iff]
          rcases eq_or_lt_of_le hri_le with rfl | hri_lt
          · have hz := hzero
            rw [htA, one_mul] at hz
            simpa [bB] using hz
          · have h0 := h0B i hri_lt hi_lt (by simp [bB]; omega)
            simpa [bB] using h0
      · refine Or.inr ⟨?_, ?_, ?_⟩
        · have hts := hsided t_v (List.getElem_mem hr_lt)
          simp only [bA, List.getElem_map, sideBit_eq_zero_iff] at htA0
          rcases hts with hA_t | hB_t
          · exact absurd ((hsideA t_v (List.getElem_mem hr_lt)).mp hA_t) htA0
          · exact hB_t
        · simp only [bA, List.getElem_map, sideBit_eq_one_iff] at hsA
          exact (hsideA s_v (List.getElem_mem hsL)).mpr hsA
        · intro v hv
          obtain ⟨i, hri_le, hi_lt, rfl⟩ := hmem_tN' v hv
          rw [hsideA _ (List.getElem_mem (by omega)), ← sideBit_eq_zero_iff]
          rcases eq_or_lt_of_le hri_le with rfl | hri_lt
          · simpa [bA] using htA0
          · have h0 := h0A i hri_lt hi_lt (by simp [bA]; omega)
            simpa [bA] using h0
    obtain ⟨hsafe, P₀, hP₀_supp, hP₀_tpath, hP₀_ind, hP₀_sep, hP₀_tight, hP₀_sided,
      hP₀_both, hP₀_sub, hP₀_pref⟩ :=
      loop_step_math hC hP hPv_split hind hsep htight hsided hpre_both ht_not_both hcase_math
    obtain ⟨hys_ne, hys_not_adj⟩ : y ≠ s_v ∧ ¬ G.Adj y s_v :=
      not_adj_of_induced_split hPv_split hPv_nd hind
    -- Rewrite `G ⊔ edge y s_v` to `H ⊔ pairGraph N (F ++ [y.1, s_v.1])`
    have hgraph_eq : G ⊔ edge y s_v = H ⊔ pairGraph N (F ++ [y.1, s_v.1]) := by
      rw [pairGraph_append_pair hF_even hys_ne, sup_assoc]
    let P' : (H ⊔ pairGraph N (F ++ [y.1, s_v.1])).Walk a b := P₀.mapLe hgraph_eq.le
    have hP'_eq_P₀ : P'.support = P₀.support := by simp [P']
    have hP'_supp : P'.support = L₁ ++ y :: s_v :: L₂ := hP'_eq_P₀.trans hP₀_supp
    have hM_sub : M <+: L₁ ++ [y] := hP₀_pref M hM_pref hM_both
    set M' := L₁ ++ [y, s_v]
    have hM'_pref : M' <+: P'.support := by
      rw [hP'_supp]
      exact ⟨L₂, by simp [M']⟩
    have hM'_len : M.length + 1 ≤ M'.length := by
      have hle := hM_sub.length_le
      simp only [M', List.length_append, List.length_cons, List.length_nil] at hle ⊢
      omega
    have hP'_len : P'.support.length < Pv.length := by
      have hlen_split := congrArg List.length hPv_split
      rw [hP'_eq_P₀, hP₀_supp]
      simp only [List.length_append, List.length_cons] at hlen_split ⊢
      omega
    have hF'_in_M' : ∀ u v, (pairGraph N (F ++ [y.1, s_v.1])).Adj u v → u ∈ M' ∧ v ∈ M' := by
      intro u v huv
      rw [pairGraph_append_pair hF_even hys_ne] at huv
      rcases huv with huv | huv
      · obtain ⟨hu, hv⟩ := hF_in_M u v huv
        have hsub : M ⊆ M' := fun z hz => by
          have hz' := hM_sub.subset hz
          simp only [M', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz' ⊢
          rcases hz' with hz' | rfl
          · exact Or.inl hz'
          · exact Or.inr (Or.inl rfl)
        exact ⟨hsub hu, hsub hv⟩
      · simp only [edge_adj] at huv
        rcases huv with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
        · exact ⟨by simp [M'], by simp [M']⟩
        · exact ⟨by simp [M'], by simp [M']⟩
    refine ⟨s₇, _,
      .seq hex₁ (.seq hex₂ (.ite_false hcond
        (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))),
      by simp [Expr.cost]; omega, hk_fin, Or.inr ⟨hrDone₇, y, s_v, M', P', hys_ne,
        List.getElem_mem (l := Pv) (by omega), List.getElem_mem hsL,
        hys_not_adj, hsafe, hF₇, ?_, ?_, hP'_len, hM'_len, hM'_pref, ?_, ?_, ?_, ?_, ?_, ?_,
        hF'_in_M', fun M₀ h1 h2 => (hP₀_pref M₀ h1 h2).trans ⟨[s_v], by
          change (L₁ ++ [y]) ++ [s_v] = L₁ ++ [y, s_v]; simp⟩⟩⟩
    · rw [hpath₇, htake_drop, ← hP'_supp]
    · rw [hP'_eq_P₀]; exact hP₀_sub
    · exact ⟨hP₀_tpath.1.mapLe _,
        hP₀_tpath.2.1,
        hP₀_tpath.2.2.1,
        by rw [hP'_eq_P₀]; exact hP₀_tpath.2.2.2⟩
    · simp only [← hgraph_eq, hP'_eq_P₀]; exact hP₀_ind
    · simp only [← hgraph_eq, hP'_eq_P₀]; exact hP₀_sep
    · simp only [← hgraph_eq, hP'_eq_P₀]; exact hP₀_tight
    · simp only [← hgraph_eq, hP'_eq_P₀]; exact hP₀_sided
    · simp only [← hgraph_eq, hP'_eq_P₀]; exact hP₀_both

end GraphMinor.Compute.TwoPaths
