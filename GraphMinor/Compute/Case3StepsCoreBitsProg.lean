module

public import GraphMinor.Compute.Case3StepsCoreBitsBody

/-!
# Recovering the core bitset on the Word RAM

The division output can be decoded without an assumption that the output list
has a particular syntax. The program normalizes each of its first `n` core
membership words, using zero for a missing word. Its output is exactly the
core bitset read by `decAlg86Out` whenever that decoder returns a division.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Recover `n` core bits from the output tail. The register `r_n` contains `n`.
Only the destination array and the loop register are changed. -/
def case3CoreBitsProg (a_raw a_Z r_n r_i : ℕ) : Cmd :=
  .seq (.alloc a_Z (.reg r_n))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_n) (case3CoreBitBody a_raw a_Z r_i)))

private theorem case3CoreBitsLoop_exec {w n : ℕ} (out : List ℕ)
    (a_raw a_Z r_n r_i : ℕ) (ha : a_raw ≠ a_Z) (hr : r_n ≠ r_i)
    (hn : n + 1 < 2 ^ w) (hrawlen : out.length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hraw : s.arrs a_raw = out) (hrn : s.regs r_n = n) (hri : s.regs r_i = k)
    (hlen : (s.arrs a_Z).length = n)
    (hbits : ∀ j : Fin n, (s.arrs a_Z).getD j.1 0 =
      if j.1 < k then (if out.getD (j.1 + 1) 0 = 0 then 0 else 1) else 0) :
    ∃ s' t, Exec w (forUp r_i (.reg r_n) (case3CoreBitBody a_raw a_Z r_i)) s s' t ∧
      t ≤ 3 + 22 * rem ∧ s'.arrs a_Z = case3CoreBitList n out := by
  have hw : 1 < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hkn : k = n := by omega
    have hc : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hkn, hnw, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    apply List.ext_getElem (by simp only [hlen, case3CoreBitList, List.length_ofFn])
    intro j hj hj'
    have hjn : j < n := by rw [← hlen]; exact hj
    have hb := hbits ⟨j, hjn⟩
    rw [List.getD_eq_getElem _ 0 hj] at hb
    simpa only [hkn, hjn, ↓reduceIte, case3CoreBitList, List.getElem_ofFn] using hb
  | succ rem ih =>
    have hkn : k < n := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hnw, hkw, hw, hkn]
    obtain ⟨tb, hexB, htB⟩ := case3CoreBitBody_exec out a_raw a_Z r_i hkn hn hrawlen hraw hlen hri
    let sB := s.writeArr a_Z k (if out.getD (k + 1) 0 = 0 then 0 else 1)
    let sC := sB.setReg r_i (k + 1)
    have hexC : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, sB, hri, hkw, hw, hkpw])
    have hrawC : sC.arrs a_raw = out := by
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha, hraw]
    have hrnC : sC.regs r_n = n := by
      simp only [sC, sB, State.setReg_regs_ne _ _ hr, State.writeArr_regs, hrn]
    have hriC : sC.regs r_i = k + 1 := State.setReg_regs_self _ _ _
    have hlenC : (sC.arrs a_Z).length = n := by
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_self, List.length_set, hlen]
    have hbitsC : ∀ j : Fin n, (sC.arrs a_Z).getD j.1 0 =
        if j.1 < k + 1 then (if out.getD (j.1 + 1) 0 = 0 then 0 else 1) else 0 := by
      intro j
      have hj : j.1 < (s.arrs a_Z).length := by rw [hlen]; exact j.2
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_self]
      rw [List.getD_eq_getElem _ 0 (by rw [List.length_set]; exact hj), List.getElem_set]
      by_cases hkj : k = j.1
      · simp [hkj]
      · simp only [hkj, ↓reduceIte]
        have hb := hbits j
        rw [List.getD_eq_getElem _ 0 hj] at hb
        rw [hb]
        have htest : j.1 < k + 1 ↔ j.1 < k := by omega
        simp only [htest]
    obtain ⟨s', t, hex, ht, hdst⟩ := ih (k + 1) (by omega) hrawC hrnC hriC hlenC hbitsC
    exact ⟨s', 3 + (tb + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex,
      by omega, hdst⟩

/-- Core normalization runs in at most `23 n + 6` steps. It changes only the
core bitset array and the loop register. -/
theorem case3CoreBitsProg_exec {w n : ℕ} (out : List ℕ)
    (a_raw a_Z r_n r_i : ℕ) (ha : a_raw ≠ a_Z) (hr : r_n ≠ r_i)
    (hn : n + 1 < 2 ^ w) (hrawlen : out.length < 2 ^ w)
    {s : State} (hraw : s.arrs a_raw = out) (hrn : s.regs r_n = n) :
    ∃ s' t, Exec w (case3CoreBitsProg a_raw a_Z r_n r_i) s s' t ∧
      t ≤ 23 * n + 6 ∧ s'.arrs a_Z = case3CoreBitList n out ∧
      (∀ a, a ≠ a_Z → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → s'.regs r = s.regs r) := by
  have hnw : n < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_Z (List.replicate n 0)
  let s₂ := s₁.setReg r_i 0
  have hex₁ : Exec w (.alloc a_Z (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp only [Expr.eval, hrn, checkWord, hnw, ↓reduceIte])
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₃, t₃, hex₃, ht₃, hdst₃⟩ := case3CoreBitsLoop_exec out a_raw a_Z r_n r_i ha hr hn hrawlen n 0
    (by omega) (s := s₂)
    (by simpa only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ ha] using hraw)
    (by simpa only [s₂, s₁, State.setReg_regs_ne _ _ hr, State.setArr_regs] using hrn)
    (State.setReg_regs_self _ _ _)
    (by simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self, List.length_replicate])
    (fun j => by
      simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self,
        Nat.not_lt_zero, ↓reduceIte, List.getD_replicate 0 j.2])
  have hex : Exec w (case3CoreBitsProg a_raw a_Z r_n r_i) s s₃ (1 + n + (2 + t₃)) :=
    .seq hex₁ (.seq hex₂ hex₃)
  refine ⟨s₃, 1 + n + (2 + t₃), hex, by omega, hdst₃, ?_, ?_⟩
  · intro a ha'
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3CoreBitsProg, case3CoreBitBody, forUp, Cmd.writtenArrs, ha'])
  · intro r hr'
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3CoreBitsProg, case3CoreBitBody, forUp, Cmd.writtenRegs, hr'])

/-- Specialization to the core of the division actually returned by (8.6). -/
theorem case3CoreBitsProg_division_exec {w : ℕ} (x : Alg81Input) (out : List ℕ)
    (d : Alg86DivisionOutput x) (hdec : decAlg86Out x out = Sum.inr d)
    (a_raw a_Z r_n r_i : ℕ) (ha : a_raw ≠ a_Z) (hr : r_n ≠ r_i)
    (hn : x.n + 1 < 2 ^ w) (hrawlen : out.length < 2 ^ w)
    {s : State} (hraw : s.arrs a_raw = out) (hrn : s.regs r_n = x.n) :
    ∃ s' t, Exec w (case3CoreBitsProg a_raw a_Z r_n r_i) s s' t ∧
      t ≤ 23 * x.n + 6 ∧ s'.arrs a_Z = bitSetList d.core.Z ∧
      (∀ a, a ≠ a_Z → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → s'.regs r = s.regs r) := by
  obtain ⟨s', t, hex, ht, hdst, harr, hreg⟩ :=
    case3CoreBitsProg_exec out a_raw a_Z r_n r_i ha hr hn hrawlen hraw hrn
  exact ⟨s', t, hex, ht, hdst.trans (case3CoreBitList_eq_division x out d hdec), harr, hreg⟩

end GraphMinor.Compute
