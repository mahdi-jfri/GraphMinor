module

public import GraphMinor.Compute.GM06Alg511BinaryRowArithmetic
public import GraphMinor.Compute.GM06Alg511BinaryPackedCall
import GraphMinor.Compute.CrossingOpsReplLists
import Mathlib.Tactic

/-!
# The binary controller for the feasibility loop

The current scaled value, target and positive increment occupy
signed binary rows 2800, 2801 and 2802. Compare the first two rows,
call the packed successor when the current value is smaller, and
add the increment on success. On failure clear the continuing bit.
The packed call retains all three binary rows and a one-word row
used to save the loop counter. It may use all other scratch space.

The finite controller has the paper's bound 1+|V(G)|/k from VI
(5.12). Once the paper's loop has stopped, the remaining controller
rounds do nothing. Correctness requires proving that this bound
excludes a still-running state at its end. This file supplies the
actual commands, exact binary guard and counter-preserving call
used by that proof of VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Compare the retained binary values and combine that Boolean
with the continuing bit. The loop guard is written to register 6001. -/
def gm06Alg511BinaryLoopGuardProg : Cmd :=
  .seq (gm06Alg511BinaryRowLessProg 2800 2801)
    (.assign 6001 (.op .mul (.reg 0) (.reg 6000)))

/-- The actual guard is one exactly when the loop is continuing
and its current binary value is strictly below the target. -/
theorem gm06Alg511BinaryLoopGuardProg_exec {w : ℕ} (a b : List ℕ) (sa sb continuing : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max a.length b.length + 2 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) (hsa : sa < 2) (hsb : sb < 2)
    (hc : continuing < 2) (hA : s.arrs 2800 = sa :: a) (hB : s.arrs 2801 = sb :: b)
    (hContinuing : s.regs 6000 = continuing) :
    ∃ t u guard, Exec w gm06Alg511BinaryLoopGuardProg s t u ∧
      u ≤ 404 + 350 * (a.length + b.length + 1) ∧
      Keeps [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2400, 2401, 2402, 2404, 2410, 2411, 6001]
        [2000, 2001, 2002, 2003, 2004, 2005] s t ∧ t.regs 6001 = guard ∧ guard < 2 ∧
      (guard = 1 ↔ continuing = 1 ∧ gm06Alg511BinaryRowValue (sa :: a) < gm06Alg511BinaryRowValue (sb :: b)) := by
  obtain ⟨st, u, flag, he, ht, hk, hflag, hbit, hiff⟩ := gm06Alg511BinaryRowLessProg_exec (w := w)
    2800 2801 (by decide) (by decide) a b sa sb s hw hsize habits hbbits hsa hsb hA hB
  let guard := flag * continuing
  have hguard : guard < 2 := by dsimp only [guard]; nlinarith only [hbit, hc]
  let t := st.setReg 6001 guard
  have he₂ : Exec w (.assign 6001 (.op .mul (.reg 0) (.reg 6000))) st t 4 :=
    .assign (Crossing.eval_mul (Crossing.eval_reg hflag (hbit.trans_le (by omega)))
      (Crossing.eval_reg ((hk.1 6000 (by decide)).trans hContinuing) (hc.trans_le (by omega)))
      (hguard.trans_le (by omega)))
  refine ⟨t, u + 4, guard, .seq he he₂, by omega,
    (hk.mono (by simp) (by simp)).setReg (by simp) guard, by simp [t], hguard, ?_⟩
  change flag * continuing = 1 ↔ _
  have hprod : flag * continuing = 1 ↔ flag = 1 ∧ continuing = 1 := by
    constructor
    · intro hp
      have hf : flag * continuing ≤ flag := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left flag (show continuing ≤ 1 by omega)
      have hc' : flag * continuing ≤ continuing := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right continuing (show flag ≤ 1 by omega)
      exact ⟨by omega, by omega⟩
    · rintro ⟨rfl, rfl⟩; rfl
  rw [hprod, hiff]
  exact and_comm

/-- Save the loop counter in its protected metadata row, run the
exact packed successor, then restore the counter. -/
def gm06Alg511BinaryCountedSuccessorCall (callee : Cmd) : Cmd :=
  .seq (.write 2803 (.const 0) (.reg 6002))
    (.seq (gm06Alg511BinaryPackedSuccessorCall callee) (.assign 6002 (.read 2803 (.const 0))))

/-- The counted call preserves the actual loop counter despite
arbitrary callee use of register 6002. Its returned bit and paths
are exactly the callee's outputs, and all retained rows survive. -/
theorem gm06Alg511BinaryCountedSuccessorCall_exec {w B : ℕ} (callee : Cmd) (x : GM06SuccessorInput)
    (s : State) (hw : 1 < 2 ^ w) (hfit : (gm06EncodeSuccessorInput x).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06EncodeSuccessorInput x, d < 2 ^ w)
    (hfields : ∀ i : Fin 6, s.arrs (gm06Alg511SuccessorFieldSources i) =
      (gm06SuccessorRows x)[i.val]'(by simp [gm06SuccessorRows]))
    (hbinary : ∀ a ∈ ([2800, 2801, 2802] : List ℕ), (s.arrs a).length < 2 ^ w ∧
      ∀ d ∈ s.arrs a, d < 2 ^ w)
    (hmeta : (s.arrs 2803).length = 1) (hcounter : s.regs 6002 < 2 ^ w)
    (hregs : ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], s.regs j < 2 ^ w)
    (post : State → Prop)
    (hcall : ∀ ss, ss.arrs 0 = gm06EncodeSuccessorInput x → ∃ raw u, Exec w callee ss raw u ∧ u ≤ B ∧ post raw) :
    ∃ t raw u, Exec w (gm06Alg511BinaryCountedSuccessorCall callee) s t u ∧
      u ≤ B + 215 + 68 * (gm06EncodeSuccessorInput x).length +
        24 * (([2800, 2801, 2802] : List ℕ).map (fun a => (s.arrs a).length)).sum ∧
      post raw ∧ t.regs 0 = raw.regs 0 ∧ t.arrs 8 = raw.arrs 8 ∧
      (∀ a ∈ gm06Alg511RetainedSuccessorArrays ++ [2800, 2801, 2802], t.arrs a = s.arrs a) ∧
      t.arrs 2803 = [s.regs 6002] ∧ t.regs 6002 = s.regs 6002 ∧
      ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j := by
  let sw := s.writeArr 2803 0 (s.regs 6002)
  have heWrite : Exec w (.write 2803 (.const 0) (.reg 6002)) s sw 3 :=
    .write (Crossing.eval_const (Nat.two_pow_pos w)) (Crossing.eval_reg rfl hcounter) (by rw [hmeta]; decide)
  obtain ⟨old, hold⟩ := List.length_eq_one_iff.mp hmeta
  have hmetaW : sw.arrs 2803 = [s.regs 6002] := by simp [sw, hold]
  have hfieldsW (i : Fin 6) : sw.arrs (gm06Alg511SuccessorFieldSources i) =
      (gm06SuccessorRows x)[i.val]'(by simp [gm06SuccessorRows]) :=
    (State.writeArr_arrs_ne _ _ _ (by fin_cases i <;> decide)).trans (hfields i)
  have hbinaryW : ∀ a ∈ gm06Alg511BinaryLoopArrays, (sw.arrs a).length < 2 ^ w ∧ ∀ d ∈ sw.arrs a, d < 2 ^ w := by
    intro a ha
    by_cases heq : a = 2803
    · subst a
      rw [hmetaW]
      exact ⟨by simpa using hw, by simpa using hcounter⟩
    · have ha' : a ∈ ([2800, 2801, 2802] : List ℕ) := by
        simp only [gm06Alg511BinaryLoopArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        tauto
      simpa only [sw, State.writeArr_arrs_ne _ _ _ heq] using hbinary a ha'
  obtain ⟨st, raw, u, he, ht, hp, hbit, hpath, hretained, hloop⟩ :=
    gm06Alg511BinaryPackedSuccessorCall_exec callee x sw hw hfit hwords hfieldsW hbinaryW hregs post hcall
  have hmetaSt : st.arrs 2803 = [s.regs 6002] := (hretained 2803 (by simp [gm06Alg511BinarySuccessorArrays, gm06Alg511BinaryLoopArrays])).trans hmetaW
  have hread : (Expr.read 2803 (.const 0)).eval w st = some (s.regs 6002) := by
    exact (Crossing.eval_read (a := 2803) (Crossing.eval_const (Nat.two_pow_pos w))
      (by rw [hmetaSt]; simp) (by simpa only [hmetaSt, List.getElem_cons_zero] using hcounter)).trans (by simp [hmetaSt])
  let t := st.setReg 6002 (s.regs 6002)
  have heRestore : Exec w (.assign 6002 (.read 2803 (.const 0))) st t 3 := .assign hread
  have hsum : (gm06Alg511BinaryLoopArrays.map (fun a => (sw.arrs a).length)).sum =
      (([2800, 2801, 2802] : List ℕ).map (fun a => (s.arrs a).length)).sum + 1 := by
    simp [gm06Alg511BinaryLoopArrays, sw, hold, Nat.add_assoc]
  refine ⟨t, raw, 3 + (u + 3), .seq heWrite (.seq he heRestore), by rw [hsum] at ht; omega,
    hp, ?_, hpath, ?_, hmetaSt, by simp [t], ?_⟩
  · exact (State.setReg_regs_ne _ _ (by decide : (0 : ℕ) ≠ 6002)).trans hbit
  · intro a ha
    have ha3 : a ≠ 2803 := by
      simp only [gm06Alg511RetainedSuccessorArrays, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl <;> decide
    have haAll : a ∈ gm06Alg511BinarySuccessorArrays := by
      simp only [gm06Alg511BinarySuccessorArrays, gm06Alg511RetainedSuccessorArrays,
        gm06Alg511BinaryLoopArrays, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
      tauto
    exact (hretained a haAll).trans (State.writeArr_arrs_ne _ _ _ ha3)
  · intro j hj
    have hj2 : j ≠ 6002 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (State.setReg_regs_ne _ _ hj2).trans (hloop j hj)

/-- The paper's call bound, computed from the retained vertex
count and the positive path count. -/
def gm06Alg511BinaryLoopLimit : Expr :=
  .op .add (.const 1) (.op .div (.read 1500 (.const 0)) (.reg 52))

/-- The controller reads exactly one plus the vertex count divided
by the positive path count, using only graph-bounded words. -/
theorem gm06Alg511BinaryLoopLimit_eval {w : ℕ} (n k : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n + 2 < 2 ^ w) (hk : 0 < k) (hkFit : k < 2 ^ w)
    (hvertices : s.arrs 1500 = [n]) (hcount : s.regs 52 = k) :
    gm06Alg511BinaryLoopLimit.eval w s = some (1 + n / k) := by
  have hnFit : n < 2 ^ w := by omega
  have hread : (Expr.read 1500 (.const 0)).eval w s = some n := by
    exact (Crossing.eval_read (a := 1500) (Crossing.eval_const (Nat.two_pow_pos w))
      (by rw [hvertices]; simp) (by simpa only [hvertices, List.getElem_cons_zero] using hnFit)).trans (by simp [hvertices])
  exact Crossing.eval_add (Crossing.eval_const hw)
    (Crossing.eval_div hread (Crossing.eval_reg hcount hkFit) hk.ne'
      ((Nat.div_le_self n k).trans_lt hnFit)) (by have := Nat.div_le_self n k; omega)

/-- Initialize the five unused scalar slots saved by the common
successor wrapper. Large current/target values stay in binary rows. -/
def gm06Alg511BinaryLoopScalarsProg : Cmd :=
  .seq (.assign 54 (.const 0)) (.seq (.assign 55 (.const 0))
    (.seq (.assign 62 (.const 0)) (.seq (.assign 63 (.const 0)) (.assign 66 (.const 0)))))

/-- Scalar initialization is a fixed ten-step program. It clears
only the five unused saved slots, without changing any array. -/
theorem gm06Alg511BinaryLoopScalarsProg_exec {w : ℕ} (s : State) :
    ∃ t, Exec w gm06Alg511BinaryLoopScalarsProg s t 10 ∧
      Keeps [54, 55, 62, 63, 66] [] s t ∧ ∀ r ∈ ([54, 55, 62, 63, 66] : List ℕ), t.regs r = 0 := by
  let t := ((((s.setReg 54 0).setReg 55 0).setReg 62 0).setReg 63 0).setReg 66 0
  have he : Exec w gm06Alg511BinaryLoopScalarsProg s t 10 :=
    .seq (.assign (Crossing.eval_const (Nat.two_pow_pos w)))
      (.seq (.assign (Crossing.eval_const (Nat.two_pow_pos w)))
        (.seq (.assign (Crossing.eval_const (Nat.two_pow_pos w)))
          (.seq (.assign (Crossing.eval_const (Nat.two_pow_pos w))) (.assign (Crossing.eval_const (Nat.two_pow_pos w))))))
  refine ⟨t, he, ?_, ?_⟩
  · exact (((((Keeps.refl _ _ s).setReg (by simp) 0).setReg (by simp) 0).setReg (by simp) 0).setReg (by simp) 0).setReg (by simp) 0
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [t]

/-- Initialize the controller's saved scalar slots, metadata row,
ordinary counter and continuing bit, leaving all binary values intact. -/
def gm06Alg511BinaryLoopPrefixProg : Cmd :=
  .seq gm06Alg511BinaryLoopScalarsProg
    (.seq (.alloc 2803 (.const 1))
      (.seq (.assign 6002 (.const 0)) (.assign 6000 (.const 1))))

/-- One active controller round executes the paper's successor
step, increments the scaled value or stops, then recomputes its guard. -/
def gm06Alg511BinaryLoopBody (callee : Cmd) : Cmd :=
  .ite (.reg 6001)
    (.seq (gm06Alg511BinaryCountedSuccessorCall callee)
      (.seq (.ite (.reg 0) (gm06Alg511BinaryRowAddProg 2800 2802 2800) (.assign 6000 (.const 0)))
        gm06Alg511BinaryLoopGuardProg)) .skip

/-- The binary controller executes at most the paper's call bound.
After termination of the paper's while-loop, its remaining rounds
are skips. The final bit is the retained continuing/decision bit. -/
def gm06Alg511BinaryLoopProg (callee : Cmd) : Cmd :=
  .seq gm06Alg511BinaryLoopPrefixProg
    (.seq gm06Alg511BinaryLoopGuardProg
      (.seq (forUp 6002 gm06Alg511BinaryLoopLimit (gm06Alg511BinaryLoopBody callee))
        (.assign 0 (.reg 6000))))

end GraphMinor.Compute
