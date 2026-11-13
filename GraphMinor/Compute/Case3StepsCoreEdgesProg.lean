module

public import GraphMinor.Compute.Case3StepsCoreEdgeBody

/-!
# Computing all core-edge group labels

The program scans the simple edge encoding once. For each core edge it
searches only the component keys, so its total work is vertex count times
edge count. It never compares all pairs of core edges.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Read the simple encoding in array 16 and fill the core-edge label array 28. -/
def case3CoreEdgesProg : Cmd :=
  .seq (.assign 14 (.read 16 (.const 0)))
    (.seq (.assign 17 (.read 16 (.const 1)))
      (.seq (.alloc 28 (.reg 17))
        (.seq (.assign 18 (.const 0)) (forUp 18 (.reg 17) case3CoreEdgeBody))))

private theorem coreEdgesLoop_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsum : x.n + (case3InputEdges x).length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = (case3InputEdges x).length) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hlen : (s.arrs 28).length = (case3InputEdges x).length)
    (hbits : ∀ j : Fin (case3InputEdges x).length, (s.arrs 28).getD j.1 0 =
      if j.1 < k then case3CoreEdgeRepEntry x d.core.Z j else 0)
    (hrn : s.regs 14 = x.n) (hrm : s.regs 17 = (case3InputEdges x).length)
    (hrk : s.regs 18 = k) :
    ∃ s' t, Exec w (forUp 18 (.reg 17) case3CoreEdgeBody) s s' t ∧
      t ≤ 3 + rem * (56 * x.n + 57) ∧ s'.arrs 28 = case3CoreEdgeRepList x d.core.Z ∧
      (∀ a, a ≠ 25 → a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ r < 40, r ≠ 18 → s'.regs r = s.regs r) := by
  have hmw : (case3InputEdges x).length < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = (case3InputEdges x).length := by omega
    have hc : (Expr.op .lt (.reg 18) (.reg 17)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, hk, hmw, h0]
    refine ⟨s, 3, .while_false hc, by simp, ?_, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    apply List.ext_getElem (hlen.trans (case3CoreEdgeRepList_length x d.core.Z).symm)
    intro j hj hj'
    have hjm : j < (case3InputEdges x).length := by rw [← hlen]; exact hj
    have hb := hbits ⟨j, hjm⟩
    rw [List.getD_eq_getElem _ 0 hj] at hb
    simpa only [hk, hjm, ↓reduceIte, case3CoreEdgeRepList, List.getElem_ofFn] using hb
  | succ rem ih =>
    have hk : k < (case3InputEdges x).length := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg 18) (.reg 17)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, hk, hkw, hmw, h1]
    obtain ⟨sB, tB, hexB, htB, hrepB, harrB, hregB⟩ :=
      case3CoreEdgeBody_exec x d hd ⟨k, hk⟩ hw hn hkeys hm hsum hin hZ htab hlen hrn hrm hrk
    change sB.arrs 28 = (s.arrs 28).set k (case3CoreEdgeRepEntry x d.core.Z ⟨k, hk⟩) at hrepB
    have hregB' : ∀ r < 40, sB.regs r = s.regs r := by
      intro r hr
      exact hregB r (by romega) (by romega) (by romega) (by romega) (by romega)
    let sC := sB.setReg 18 (k + 1)
    have hexC : Exec w (.assign 18 (.op .add (.reg 18) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hregB' 18 (by decide), hrk, hkw, h1, hkpw])
    have hlenC : (sC.arrs 28).length = (case3InputEdges x).length := by
      rw [show sC.arrs 28 = sB.arrs 28 from rfl, hrepB, List.length_set, hlen]
    have hbitsC : ∀ j : Fin (case3InputEdges x).length, (sC.arrs 28).getD j.1 0 =
        if j.1 < k + 1 then case3CoreEdgeRepEntry x d.core.Z j else 0 := by
      intro j
      have hj : j.1 < (s.arrs 28).length := by rw [hlen]; exact j.2
      change (sB.arrs 28).getD j.1 0 = _
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
      ((harrB 16 (by decide) (by decide)).trans hin)
      (hZ.of_arr_eq (harrB 10 (by decide) (by decide)))
      ((harrB 26 (by decide) (by decide)).trans htab) hlenC hbitsC
      (by rw [State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 18 by decide), hregB' 14 (by decide), hrn])
      (by rw [State.setReg_regs_ne _ _ (show (17 : ℕ) ≠ 18 by decide), hregB' 17 (by decide), hrm])
      (State.setReg_regs_self ..)
    refine ⟨s', 3 + (tB + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, ?_, hdst, ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · intro a h25 h28
      exact (harr a h25 h28).trans (harrB a h25 h28)
    · intro r hr h18
      rw [hreg r hr h18]
      change (sB.setReg 18 (k + 1)).regs r = s.regs r
      rw [State.setReg_regs_ne _ _ h18]
      exact hregB' r hr

/-- Core-edge grouping uses at most edge count times linear vertex work.
The graph, core, component keys, and component representatives are retained. -/
theorem case3CoreEdgesProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsum : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z) :
    ∃ s' t, Exec w case3CoreEdgesProg s s' t ∧
      t ≤ (case3InputEdges x).length + (case3InputEdges x).length * (56 * x.n + 57) + 12 ∧
      s'.arrs 28 = case3CoreEdgeRepList x d.core.Z ∧ s'.regs 14 = x.n ∧
      s'.regs 17 = (case3InputEdges x).length ∧
      (∀ a, a ≠ 25 → a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ r < 14, s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have hmw : (case3InputEdges x).length < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hsyntax : s.arrs 16 = [x.n, (case3InputEdges x).length] ++ flatEdges (case3InputEdges x) ++ [] := by
    simpa only [case3InputEdges, encGraph, List.append_nil] using hin
  obtain ⟨hi0, hv0⟩ := inArr_getElem_zero (case3InputEdges x) [] hsyntax
  obtain ⟨hi1, hv1⟩ := inArr_getElem_one (case3InputEdges x) [] hsyntax
  let s₁ := s.setReg 14 x.n
  let s₂ := s₁.setReg 17 (case3InputEdges x).length
  let s₃ := s₂.setArr 28 (List.replicate (case3InputEdges x).length 0)
  let s₄ := s₃.setReg 18 0
  have hex₁ : Exec w (.assign 14 (.read 16 (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0, hi0, hv0, hnw])
  have hex₂ : Exec w (.assign 17 (.read 16 (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₁, State.setReg_arrs, h1, hi1, hv1, hmw])
  have hex₃ : Exec w (.alloc 28 (.reg 17)) s₂ s₃ (1 + (case3InputEdges x).length) :=
    .alloc (by simp only [Expr.eval, checkWord, s₂, State.setReg_regs_self, hmw, ↓reduceIte])
  have hex₄ : Exec w (.assign 18 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have harr₄ : ∀ a, a ≠ 28 → s₄.arrs a = s.arrs a := by
    intro a ha
    exact State.setArr_arrs_ne s₂ (List.replicate (case3InputEdges x).length 0) ha
  have hrn₄ : s₄.regs 14 = x.n := by simp [s₄, s₃, s₂, s₁, State.setReg, State.setArr_regs]
  have hrm₄ : s₄.regs 17 = (case3InputEdges x).length := by simp [s₄, s₃, s₂, State.setReg, State.setArr_regs]
  obtain ⟨s₅, t₅, hex₅, ht₅, hdst₅, harr₅, hreg₅⟩ := coreEdgesLoop_exec x d hd hw hn hkeys hm hsum
    (case3InputEdges x).length 0 (by omega) (s := s₄)
    ((harr₄ 16 (by decide)).trans hin) (hZ.of_arr_eq (harr₄ 10 (by decide)))
    ((harr₄ 26 (by decide)).trans htab)
    (by simp only [s₄, s₃, State.setReg_arrs, State.setArr_arrs_self, List.length_replicate])
    (fun j => by simp only [s₄, s₃, State.setReg_arrs, State.setArr_arrs_self,
      Nat.not_lt_zero, ↓reduceIte, List.getD_replicate 0 j.2])
    hrn₄ hrm₄ (State.setReg_regs_self ..)
  refine ⟨s₅, 3 + (3 + (1 + (case3InputEdges x).length + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), by omega, hdst₅,
    (hreg₅ 14 (by decide) (by decide)).trans hrn₄,
    (hreg₅ 17 (by decide) (by decide)).trans hrm₄, ?_, ?_⟩
  · intro a h25 h28
    exact (harr₅ a h25 h28).trans (harr₄ a h28)
  · intro r hr
    rw [hreg₅ r (by romega) (by romega)]
    simp only [s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ (show r ≠ 18 by romega),
      State.setArr_regs, State.setReg_regs_ne _ _ (show r ≠ 17 by romega),
      State.setReg_regs_ne _ _ (show r ≠ 14 by romega)]

end GraphMinor.Compute
