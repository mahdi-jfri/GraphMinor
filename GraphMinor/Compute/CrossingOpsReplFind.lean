module

public import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Testing whether a boundary vertex is already a neighbour

When rebuilding a boundary vertex's list, the replacement program tests each candidate
against the old list before adding a clique edge. There are at most three candidates.
This file proves the list scan used for that test.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Set `R+9` to one exactly when the candidate in `R+7` occurs in the list of `R`. -/
def findNeighbourProg (a_s a_e a_ent R : ℕ) : Cmd :=
  .seq (.assign (R + 9) (.const 0))
    (forList a_s a_e a_ent R (R + 1) (R + 2) (R + 3)
      (.ite (.op .eq (.reg (R + 3)) (.reg (R + 7))) (.assign (R + 9) (.const 1)) .skip))

/-- The membership test scans the old adjacency list and changes no array. -/
theorem findNeighbourProg_exec {w : ℕ} (a_s a_e a_ent R : ℕ)
    {s : State} {x y st en : ℕ} {l : List ℕ}
    (hl : IsListAt a_s a_e a_ent x st en l s) (hx : s.regs R = x)
    (hy : s.regs (R + 7) = y) (hxw : x < 2 ^ w) (hyw : y < 2 ^ w)
    (hen : en < 2 ^ w) (hlt : ∀ z ∈ l, z < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (findNeighbourProg a_s a_e a_ent R) s s' t ∧
      t ≤ 11 + 15 * l.length ∧ s'.regs (R + 9) = (if y ∈ l then 1 else 0) ∧
      s'.arrs = s.arrs ∧
      (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 9 →
        s'.regs r = s.regs r) := by
  classical
  let s0 := s.setReg (R + 9) 0
  have hex0 : Exec w (.assign (R + 9) (.const 0)) s s0 2 :=
    .assign (eval_const (by omega))
  let I : ℕ → State → Prop := fun j z => z.arrs = s.arrs ∧
    z.regs (R + 7) = y ∧ z.regs (R + 9) = (if y ∈ l.take j then 1 else 0)
  obtain ⟨s1, t1, hex1, ht1, hI⟩ := forList_exec a_s a_e a_ent R (R + 1) (R + 2) (R + 3)
    (.ite (.op .eq (.reg (R + 3)) (.reg (R + 7))) (.assign (R + 9) (.const 1)) .skip)
    x st en l I 5 (by omega) (by omega) hw hen hxw
    (hl.of_arrs_eq rfl rfl rfl : IsListAt a_s a_e a_ent x st en l s0)
    (by simp [s0, hx])
    (by simp [I, s0, hy])
    (fun j hj z h => by
      rw [h.1]
      obtain ⟨-, -, he, hd, -, -, -, hget⟩ := hl
      exact ⟨by omega, hget j hj⟩)
    hlt
    (fun j hj z h hrk hrhi => by
      obtain ⟨z', t', he, ht, harr, hflag, hreg⟩ := flag_exec (w := w)
        (r₁ := R + 3) (r₂ := R + 7) (rf := R + 9)
        (s := z.setReg (R + 3) l[j]) (a := l[j]) (b := y)
        (by simp) (by simp [h.2.1]) (hlt _ (List.getElem_mem hj)) hyw hw
      refine ⟨z', t', he, ht, ?_, ?_, ?_⟩
      · rw [hreg (R + 1) (by dsimp only [Reg]; omega)]
        simpa using hrk
      · rw [hreg (R + 2) (by dsimp only [Reg]; omega)]
        simpa using hrhi
      · refine ⟨harr.trans h.1, ?_, ?_⟩
        · simp [hreg (R + 7) (by dsimp only [Reg]; omega), h.2.1]
        · simp only [State.setReg_regs_ne _ _ (show R + 9 ≠ R + 1 by omega)]
          rw [hflag]
          simpa only [State.setReg_regs_ne _ _ (show R + 9 ≠ R + 3 by omega), h.2.2]
            using (ite_mem_take_succ (l := l) hj y).symm)
  have hex : Exec w (findNeighbourProg a_s a_e a_ent R) s s1 (2 + t1) := .seq hex0 hex1
  refine ⟨s1, 2 + t1, hex, by omega, by simpa using hI.2.2, hI.1, ?_⟩
  intro r h1 h2 h3 h9
  exact hex.regs_eq_of_not_mem_writtenRegs (by
    simp [findNeighbourProg, forList, forUp, Cmd.writtenRegs, h1, h2, h3, h9])

/-- Emit a candidate only when it differs from the vertex and is missing from its old list. -/
def emitMissingNeighbourProg (a_s a_e a_ent buf R : ℕ) : Cmd :=
  .seq (findNeighbourProg a_s a_e a_ent R)
    (.ite (.op .eq (.reg (R + 7)) (.reg R)) .skip
      (.ite (.reg (R + 9)) .skip (emitProg buf (R + 4) (.reg (R + 7)))))

/-- A boundary candidate is emitted exactly when its clique edge is missing. -/
theorem emitMissingNeighbourProg_exec {w : ℕ} (a_s a_e a_ent buf R : ℕ)
    {s : State} {x y st en : ℕ} {l pre : List ℕ} {k : ℕ}
    (hl : IsListAt a_s a_e a_ent x st en l s) (hx : s.regs R = x)
    (hy : s.regs (R + 7) = y) (hxw : x < 2 ^ w) (hyw : y < 2 ^ w)
    (hen : en < 2 ^ w) (hlt : ∀ z ∈ l, z < 2 ^ w) (hw : 1 < 2 ^ w)
    (hb : IsBuf buf (R + 4) pre k s)
    (hk : (if y ≠ x ∧ y ∉ l then 1 else 0) ≤ k)
    (hcap : pre.length + 1 < 2 ^ w) :
    ∃ s' t, Exec w (emitMissingNeighbourProg a_s a_e a_ent buf R) s s' t ∧
      t ≤ 22 + 15 * l.length ∧
      IsBuf buf (R + 4) (pre ++ if y ≠ x ∧ y ∉ l then [y] else [])
        (k - if y ≠ x ∧ y ∉ l then 1 else 0) s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 9 →
        s'.regs r = s.regs r) := by
  classical
  obtain ⟨s1, t1, hex1, ht1, hflag, harr, hr⟩ := findNeighbourProg_exec a_s a_e a_ent R
    hl hx hy hxw hyw hen hlt hw
  have hx1 : s1.regs R = x := (hr R (by omega) (by omega) (by omega) (by omega)).trans hx
  have hy1 : s1.regs (R + 7) = y :=
    (hr (R + 7) (by omega) (by omega) (by omega) (by omega)).trans hy
  have hb1 : IsBuf buf (R + 4) pre k s1 :=
    ⟨by rw [harr]; exact hb.1,
      (hr (R + 4) (by omega) (by omega) (by omega) (by omega)).trans hb.2⟩
  have htail : ∃ s2 t2,
      Exec w (.ite (.op .eq (.reg (R + 7)) (.reg R)) .skip
        (.ite (.reg (R + 9)) .skip (emitProg buf (R + 4) (.reg (R + 7))))) s1 s2 t2 ∧
      t2 ≤ 11 ∧ IsBuf buf (R + 4) (pre ++ if y ≠ x ∧ y ∉ l then [y] else [])
        (k - if y ≠ x ∧ y ∉ l then 1 else 0) s2 := by
    by_cases hyx : y = x
    · refine ⟨s1, 4, exec_ite_eq_true hy1 (hx1.trans hyx.symm) hyw hw (.skip s1), by omega, ?_⟩
      simpa [hyx] using hb1
    · by_cases hym : y ∈ l
      · have hf : s1.regs (R + 9) = 1 := by simpa [hym] using hflag
        refine ⟨s1, 5, exec_ite_eq_false hy1 hx1 hyx hyw hxw hw
          (.ite_true (eval_reg hf hw) (by decide) (.skip s1)), by omega, ?_⟩
        simpa [hym] using hb1
      · have hf : s1.regs (R + 9) = 0 := by simpa [hym] using hflag
        have hk1 : k = (k - 1) + 1 := by
          have hkpos : 1 ≤ k := by simpa [hyx, hym] using hk
          omega
        obtain ⟨s2, hex2, hb2, -, -⟩ := emitReg_exec buf (R + 4) (R + 7)
          (by rw [← hk1]; exact hb1) hy1 hyw hcap
        refine ⟨s2, 11, exec_ite_eq_false hy1 hx1 hyx hyw hxw hw
          (.ite_false (eval_reg hf (by omega)) hex2), le_rfl, ?_⟩
        simpa [hyx, hym] using hb2
  obtain ⟨s2, t2, hex2, ht2, hb2⟩ := htail
  have hex : Exec w (emitMissingNeighbourProg a_s a_e a_ent buf R) s s2 (t1 + t2) :=
    .seq hex1 hex2
  refine ⟨s2, t1 + t2, hex, by omega, hb2, ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [emitMissingNeighbourProg, findNeighbourProg, forList, forUp, emitProg,
        Cmd.writtenArrs, ha])
  · intro r h1 h2 h3 h4 h9
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [emitMissingNeighbourProg, findNeighbourProg, forList, forUp, emitProg,
        Cmd.writtenRegs, h1, h2, h3, h4, h9])

end GraphMinor.Compute.Crossing
