module

public import GraphMinor.Compute.Case3StepsRepresentativeBody

/-!
# Computing all component representatives

The outer loop writes one representative per seed. Each outside seed uses a
linear first-match scan, so the representative array takes quadratic vertex
work. No graph or component arrays are changed.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Fill array 27 with the common representative of each component boundary. -/
def case3RepresentativesProg : Cmd :=
  .seq (.alloc 27 (.reg 14))
    (.seq (.assign 13 (.const 4))
      (.seq (.assign 15 (.const 0)) (forUp 15 (.reg 14) case3RepresentativeBody)))

private theorem representativesLoop_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = x.n) {s : State}
    (hZ : IsBitSet d.core.Z 10 s) (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hlen : (s.arrs 27).length = x.n)
    (hbits : ∀ j : Fin x.n, (s.arrs 27).getD j.1 0 =
      if j.1 < k then (if j ∈ d.core.Z then x.n else case3ComponentRepresentative x d.core.Z j) else 0)
    (hrn : s.regs 14 = x.n) (hrk : s.regs 15 = k) (hr4 : s.regs 13 = 4) :
    ∃ s' t, Exec w (forUp 15 (.reg 14) case3RepresentativeBody) s s' t ∧
      t ≤ 3 + rem * (56 * x.n + 103) ∧ s'.arrs 27 = case3ComponentRepList x d.core.Z ∧
      (∀ a, a ≠ 25 → a ≠ 27 → s'.arrs a = s.arrs a) ∧
      (∀ r < 13, s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = x.n := by omega
    have hc : (Expr.op .lt (.reg 15) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrn, hk, hnw, h0]
    refine ⟨s, 3, .while_false hc, by simp, ?_, fun _ _ _ => rfl, fun _ _ => rfl⟩
    apply List.ext_getElem (hlen.trans (case3ComponentRepList_length x d.core.Z).symm)
    intro j hj hj'
    have hjn : j < x.n := by rw [← hlen]; exact hj
    have hb := hbits ⟨j, hjn⟩
    rw [List.getD_eq_getElem _ 0 hj] at hb
    simpa only [hk, hjn, ↓reduceIte, case3ComponentRepList, List.getElem_ofFn] using hb
  | succ rem ih =>
    have hk : k < x.n := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg 15) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrn, hk, hkw, hnw, h1]
    obtain ⟨sB, tB, hexB, htB, hrepB, harrB, hregB⟩ :=
      case3RepresentativeBody_exec x d hd ⟨k, hk⟩ hw hn hkeys hZ htab hlen hrn hrk hr4
    let sC := sB.setReg 15 (k + 1)
    have hexC : Exec w (.assign 15 (.op .add (.reg 15) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hregB 15 (by decide), hrk, hkw, h1, hkpw])
    have hlenC : (sC.arrs 27).length = x.n := by
      rw [show sC.arrs 27 = sB.arrs 27 from rfl, hrepB, List.length_set, hlen]
    have hbitsC : ∀ j : Fin x.n, (sC.arrs 27).getD j.1 0 =
        if j.1 < k + 1 then (if j ∈ d.core.Z then x.n else case3ComponentRepresentative x d.core.Z j) else 0 := by
      intro j
      have hj : j.1 < (s.arrs 27).length := by rw [hlen]; exact j.2
      change (sB.arrs 27).getD j.1 0 = _
      rw [hrepB, List.getD_eq_getElem _ 0 (by rw [List.length_set]; exact hj), List.getElem_set]
      by_cases hkj : k = j.1
      · simp only [hkj, ↓reduceIte, Nat.lt_add_one]
      · simp only [hkj, ↓reduceIte]
        have hb := hbits j
        rw [List.getD_eq_getElem _ 0 hj] at hb
        rw [hb]
        have htest : j.1 < k + 1 ↔ j.1 < k := by omega
        simp only [htest]
    obtain ⟨s', t, hex, ht, hdst, harr, hreg⟩ := ih (k + 1) (by omega) (s := sC)
      (hZ.of_arr_eq (harrB 10 (by decide) (by decide)))
      ((harrB 26 (by decide) (by decide)).trans htab) hlenC hbitsC
      (by rw [State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 15 by decide), hregB 14 (by decide), hrn])
      (State.setReg_regs_self ..)
      (by rw [State.setReg_regs_ne _ _ (show (13 : ℕ) ≠ 15 by decide), hregB 13 (by decide), hr4])
    refine ⟨s', 3 + (tB + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, ?_, hdst, ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · intro a h25 h27
      exact (harr a h25 h27).trans (harrB a h25 h27)
    · intro r hr
      rw [hreg r hr]
      change (sB.setReg 15 (k + 1)).regs r = s.regs r
      rw [State.setReg_regs_ne _ _ (show r ≠ 15 by romega)]
      exact hregB r (by romega)

/-- Compute the whole representative array with quadratic vertex work.
Only arrays 25 and 27 and registers at least 13 may change. -/
theorem case3RepresentativesProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    {s : State} (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z) (hrn : s.regs 14 = x.n) :
    ∃ s' t, Exec w case3RepresentativesProg s s' t ∧
      t ≤ x.n + x.n * (56 * x.n + 103) + 8 ∧
      s'.arrs 27 = case3ComponentRepList x d.core.Z ∧
      (∀ a, a ≠ 25 → a ≠ 27 → s'.arrs a = s.arrs a) ∧
      (∀ r < 13, s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 27 (List.replicate x.n 0)
  let s₂ := s₁.setReg 13 4
  let s₃ := s₂.setReg 15 0
  have hex₁ : Exec w (.alloc 27 (.reg 14)) s s₁ (1 + x.n) :=
    .alloc (by simp only [Expr.eval, checkWord, hrn, hnw, ↓reduceIte])
  have hex₂ : Exec w (.assign 13 (.const 4)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hw, ↓reduceIte])
  have hex₃ : Exec w (.assign 15 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₄, t₄, hex₄, ht₄, hdst₄, harr₄, hreg₄⟩ := representativesLoop_exec x d hd hw hn hkeys
    x.n 0 (by omega) (s := s₃)
    (hZ.of_arr_eq (by
      simpa only [s₃, s₂, s₁, State.setReg_arrs] using
        State.setArr_arrs_ne s (List.replicate x.n 0) (show (10 : ℕ) ≠ 27 by decide)))
    (by simpa only [s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne s (List.replicate x.n 0) (show (26 : ℕ) ≠ 27 by decide)] using htab)
    (by simp only [s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_self, List.length_replicate])
    (fun j => by simp only [s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_self,
      Nat.not_lt_zero, ↓reduceIte, List.getD_replicate 0 j.2])
    (by simp [s₃, s₂, s₁, State.setReg, State.setArr_regs, hrn])
    (State.setReg_regs_self ..)
    (by simp [s₃, s₂, State.setReg])
  refine ⟨s₄, 1 + x.n + (2 + (2 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hdst₄, ?_, ?_⟩
  · intro a h25 h27
    exact (harr₄ a h25 h27).trans (State.setArr_arrs_ne _ _ h27)
  · intro r hr
    rw [hreg₄ r hr]
    simp only [s₃, s₂, s₁, State.setReg_regs_ne _ _ (show r ≠ 15 by romega),
      State.setReg_regs_ne _ _ (show r ≠ 13 by romega), State.setArr_regs]

end GraphMinor.Compute
