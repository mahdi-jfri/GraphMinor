module

public import GraphMinor.Compute.Case3StepsAttachmentBitBody

/-!
# Writing the attachment bitset

The program scans vertices once. It masks positive neighbor counts by core
membership and writes a normalized attachment bitset. A prefix invariant
records which vertices have been tested.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Normalize all attachment bits, using a separate loop register. -/
def case3AttachmentBitsProg (a_Z a_deg a_att r_n r_i : ℕ) : Cmd :=
  .seq (.alloc a_att (.reg r_n))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_n) (case3AttachmentBitBody a_Z a_deg a_att r_i)))

private theorem attachmentBitsLoop_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (u : Fin x.n) (a_Z a_deg a_att r_n r_i : ℕ)
    (haZ : a_Z ≠ a_att) (haD : a_deg ≠ a_att) (hr : r_n ≠ r_i)
    (hw : 1 < 2 ^ w) (hn : x.n + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = x.n) {s : State}
    (hZ : IsBitSet Z a_Z s) (hdeg : IsDegIntoArr x.G (case3ComponentRowSet x Z u) a_deg s)
    (hrn : s.regs r_n = x.n) (hri : s.regs r_i = k)
    (hlen : (s.arrs a_att).length = x.n)
    (hbits : ∀ j : Fin x.n, (s.arrs a_att).getD j.1 0 =
      if j.1 < k then (if j ∈ case3AttachmentRowSet x Z u then 1 else 0) else 0) :
    ∃ s' t, Exec w (forUp r_i (.reg r_n) (case3AttachmentBitBody a_Z a_deg a_att r_i)) s s' t ∧
      t ≤ 3 + 16 * rem ∧ s'.arrs a_att = bitSetList (case3AttachmentRowSet x Z u) := by
  have h0 : 0 < 2 ^ w := by omega
  have hnw : x.n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = x.n := by omega
    have hc : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hnw, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    apply List.ext_getElem (by rw [hlen, length_bitSetList])
    intro j hj hj'
    have hjn : j < x.n := by rw [← hlen]; exact hj
    have hb := hbits ⟨j, hjn⟩
    rw [List.getD_eq_getElem _ 0 hj] at hb
    rw [getElem_bitSetList _ j hjn]
    simpa only [hk, hjn, ↓reduceIte] using hb
  | succ rem ih =>
    have hk : k < x.n := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hkw, hnw, hw]
    let sB := s.writeArr a_att k (if (⟨k, hk⟩ : Fin x.n) ∈ case3AttachmentRowSet x Z u then 1 else 0)
    let sC := sB.setReg r_i (k + 1)
    have hexB : Exec w (case3AttachmentBitBody a_Z a_deg a_att r_i) s sB 9 :=
      case3AttachmentBitBody_exec x Z u ⟨k, hk⟩ a_Z a_deg a_att r_i hw hnw hZ hdeg hlen hri
    have hexC : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, sB, hri, hkw, hw, hkpw])
    have hZC : IsBitSet Z a_Z sC := hZ.of_arr_eq (State.writeArr_arrs_ne _ _ _ haZ)
    have hdegC : IsDegIntoArr x.G (case3ComponentRowSet x Z u) a_deg sC :=
      hdeg.of_arr_eq (State.writeArr_arrs_ne _ _ _ haD)
    have hrnC : sC.regs r_n = x.n := by
      simp only [sC, sB, State.setReg_regs_ne _ _ hr, State.writeArr_regs, hrn]
    have hlenC : (sC.arrs a_att).length = x.n := by
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_self, List.length_set, hlen]
    have hbitsC : ∀ j : Fin x.n, (sC.arrs a_att).getD j.1 0 =
        if j.1 < k + 1 then (if j ∈ case3AttachmentRowSet x Z u then 1 else 0) else 0 := by
      intro j
      have hj : j.1 < (s.arrs a_att).length := by rw [hlen]; exact j.2
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_self]
      rw [List.getD_eq_getElem _ 0 (by rw [List.length_set]; exact hj), List.getElem_set]
      by_cases hkj : k = j.1
      · simp only [hkj, ↓reduceIte, Nat.lt_add_one]
      · simp only [hkj, ↓reduceIte]
        have hb := hbits j
        rw [List.getD_eq_getElem _ 0 hj] at hb
        rw [hb]
        have htest : j.1 < k + 1 ↔ j.1 < k := by omega
        simp only [htest]
    obtain ⟨s', t, hex, ht, hdst⟩ := ih (k + 1) (by omega) hZC hdegC hrnC
      (State.setReg_regs_self ..) hlenC hbitsC
    exact ⟨s', 3 + (9 + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, by omega, hdst⟩

/-- Writing all attachment bits costs at most `17 n + 6` steps and changes
only the destination array and loop register. -/
theorem case3AttachmentBitsProg_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (u : Fin x.n) (a_Z a_deg a_att r_n r_i : ℕ)
    (haZ : a_Z ≠ a_att) (haD : a_deg ≠ a_att) (hr : r_n ≠ r_i)
    (hw : 1 < 2 ^ w) (hn : x.n + 1 < 2 ^ w)
    {s : State} (hZ : IsBitSet Z a_Z s)
    (hdeg : IsDegIntoArr x.G (case3ComponentRowSet x Z u) a_deg s)
    (hrn : s.regs r_n = x.n) :
    ∃ s' t, Exec w (case3AttachmentBitsProg a_Z a_deg a_att r_n r_i) s s' t ∧
      t ≤ 17 * x.n + 6 ∧ s'.arrs a_att = bitSetList (case3AttachmentRowSet x Z u) ∧
      (∀ a, a ≠ a_att → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_att (List.replicate x.n 0)
  let s₂ := s₁.setReg r_i 0
  have hex₁ : Exec w (.alloc a_att (.reg r_n)) s s₁ (1 + x.n) :=
    .alloc (by simp only [Expr.eval, checkWord, hrn, hnw, ↓reduceIte])
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₃, t₃, hex₃, ht₃, hdst₃⟩ := attachmentBitsLoop_exec x Z u a_Z a_deg a_att r_n r_i
    haZ haD hr hw hn x.n 0 (by omega) (s := s₂)
    (hZ.of_arr_eq (State.setArr_arrs_ne _ _ haZ))
    (hdeg.of_arr_eq (State.setArr_arrs_ne _ _ haD))
    (by simp only [s₂, s₁, State.setReg_regs_ne _ _ hr, State.setArr_regs, hrn])
    (State.setReg_regs_self ..)
    (by simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self, List.length_replicate])
    (fun j => by simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self,
      Nat.not_lt_zero, ↓reduceIte, List.getD_replicate 0 j.2])
  have hex : Exec w (case3AttachmentBitsProg a_Z a_deg a_att r_n r_i) s s₃ (1 + x.n + (2 + t₃)) :=
    .seq hex₁ (.seq hex₂ hex₃)
  refine ⟨s₃, 1 + x.n + (2 + t₃), hex, by omega, hdst₃, ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3AttachmentBitsProg, case3AttachmentBitBody, forUp, Cmd.writtenArrs, ha])
  · intro r hr'
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3AttachmentBitsProg, case3AttachmentBitBody, forUp, Cmd.writtenRegs, hr'])

end GraphMinor.Compute
