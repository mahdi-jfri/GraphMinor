module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Counting the edges whose smaller endpoint is a given vertex

The program scans one adjacency list and counts neighbours with larger indices.
Each original edge is counted in precisely its smaller endpoint's list. This count
lets the edge-selection program locate the row containing its last selected edge.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Count neighbours larger than the vertex in `R`. The result is in `R+4`. -/
def countGreaterProg (a_s a_e a_ent R : ℕ) : Cmd :=
  .seq (.assign (R + 4) (.const 0))
    (forList a_s a_e a_ent R (R + 1) (R + 2) (R + 3)
      (.ite (.op .lt (.reg R) (.reg (R + 3)))
        (.assign (R + 4) (.op .add (.reg (R + 4)) (.const 1))) .skip))

/-- Counting increasing neighbours takes linear time and changes no array. -/
theorem countGreaterProg_exec {w : ℕ} (a_s a_e a_ent R : ℕ)
    {s : State} {x st en : ℕ} {l : List ℕ}
    (hl : IsListAt a_s a_e a_ent x st en l s) (hx : s.regs R = x)
    (hxword : x < 2 ^ w) (hen : en < 2 ^ w) (hlen : l.length < 2 ^ w)
    (hlword : ∀ y ∈ l, y < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (countGreaterProg a_s a_e a_ent R) s s' t ∧ t ≤ 11 + 17 * l.length ∧
      s'.regs (R + 4) = (l.filter (fun y => x < y)).length ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → s'.regs r = s.regs r) := by
  let s0 := s.setReg (R + 4) 0
  let I : ℕ → State → Prop := fun j z => z.regs R = x ∧
    z.regs (R + 4) = ((l.take j).filter (fun y => x < y)).length ∧ z.arrs = s.arrs
  have hI0 : I 0 ((s0.setReg (R + 1) st).setReg (R + 2) en) := by
    simp [I, s0, hx]
  obtain ⟨s1, t1, he1, ht1, hI1⟩ := forList_exec (w := w)
    a_s a_e a_ent R (R + 1) (R + 2) (R + 3)
    (.ite (.op .lt (.reg R) (.reg (R + 3)))
      (.assign (R + 4) (.op .add (.reg (R + 4)) (.const 1))) .skip)
    x st en l I 7 (by omega) (by omega) hw hen hxword (hl.of_arrs_eq (s' := s0) rfl rfl rfl)
    (by simpa [s0] using hx) hI0
    (fun j hj z h => by
      rw [h.2.2]
      obtain ⟨_, _, hene, hdiff, _, _, hle, hget⟩ := hl
      exact ⟨by omega, hget j hj⟩)
    hlword
    (fun j hj z h hri hrhi => by
      let z0 := z.setReg (R + 3) l[j]
      have hroot : z0.regs R = x := by simp [z0, h.1]
      have hcount : z0.regs (R + 4) = ((l.take j).filter (fun y => x < y)).length := by
        simpa [z0] using h.2.1
      have hcntle : ((l.take j).filter (fun y => x < y)).length ≤ j :=
        (List.length_filter_le _ _).trans (by simp)
      have hc := eval_lt (eval_reg hroot hxword)
        (eval_reg (r := R + 3) (s := z0) (by simp [z0]) (hlword _ (List.getElem_mem hj))) hw
      have hlenStep : ((l.take (j + 1)).filter (fun y => x < y)).length =
          ((l.take j).filter (fun y => x < y)).length + (if x < l[j] then 1 else 0) := by
        rw [List.take_succ_eq_append_getElem hj, List.filter_append, List.length_append]
        split <;> simp_all
      by_cases hlt : x < l[j]
      · let z1 := z0.setReg (R + 4) (((l.take j).filter (fun y => x < y)).length + 1)
        have heinc : Exec w (.assign (R + 4) (.op .add (.reg (R + 4)) (.const 1))) z0 z1 4 :=
          .assign (eval_add (eval_reg hcount (by omega)) (eval_const hw) (by omega))
        refine ⟨z1, 7, .ite_true (by simpa [hlt] using hc) (by decide) heinc, le_rfl,
          by simp [z1, z0, hri], by simp [z1, z0, hrhi], ?_⟩
        refine ⟨by simp [z1, z0, h.1], ?_, h.2.2⟩
        simp [z1, hlenStep, hlt]
      · refine ⟨z0, 4, .ite_false (by simpa [hlt] using hc) (.skip z0), by omega,
          by simp [z0, hri], by simp [z0, hrhi], ?_⟩
        refine ⟨by simp [z0, h.1], ?_, h.2.2⟩
        simp [z0, h.2.1, hlenStep, hlt])
  have hex := Exec.seq (Exec.assign (r := R + 4) (eval_const (w := w) (s := s) (c := 0) (by omega))) he1
  refine ⟨s1, 2 + t1, hex, by omega, ?_, fun a => congrFun hI1.2.2 a, ?_⟩
  · simpa only [List.take_length] using hI1.2.1
  · intro r h1 h2 h3 h4
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [countGreaterProg, forList, forUp, Cmd.writtenRegs, h1, h2, h3, h4])

end GraphMinor.Compute.Crossing
