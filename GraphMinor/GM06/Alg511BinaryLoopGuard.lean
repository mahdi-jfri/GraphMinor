module

public import GraphMinor.GM06.Alg511BinaryLoopState
import Mathlib.Tactic

/-!
# The binary guard and stopped controller rounds

Run the concrete signed-row comparison while retaining the loop's
common graph, scalar and binary data. At a live linkage its guard
is exactly comparison of the successful-call index with the target
index, because each binary value differs by the same positive
integer increment. Equality yields the retained target linkage.
After a proved negative answer the continuing bit forces the guard
to zero. Every later controller round is a skip. These are the guard
and stopped cases of VI (5.11), page 134.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Compute.TwoPaths GraphMinor.Surface

private theorem guard_time_bound {u a b base i : ℕ}
    (ht : u ≤ 404 + 350 * (a + b + 1)) (hlen : a ≤ base + i) :
    u ≤ 404 + 350 * (base + i + b + 1) := by
  exact ht.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left 350 (Nat.add_le_add_right (Nat.add_le_add_right hlen b) 1)) 404)

private theorem bit_zero {n : ℕ} (hbit : n < 2) (hne : n ≠ 1) : n = 0 := by omega

/-- The actual binary guard retains all common loop data, returns
its exact comparison and has a linear digit-width cost. -/
theorem alg511_binary_guard_common_exec {w : ℕ} (x : GM06Alg511WindingInput)
    (sb : ℕ) (b incrementRow : List ℕ) (base i continuing : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max base b.length + i + 2 < 2 ^ w)
    (hsb : sb < 2) (hbits : ∀ d ∈ b, d < 2) (hc : continuing < 2)
    (hcommon : alg511BinaryLoopCommon x (sb :: b) incrementRow base i s)
    (hContinuing : s.regs 6000 = continuing) :
    ∃ t u, Exec w gm06Alg511BinaryLoopGuardProg s t u ∧
      u ≤ 404 + 350 * (base + i + b.length + 1) ∧
      alg511BinaryLoopCommon x (sb :: b) incrementRow base i t ∧
      t.regs 6000 = continuing ∧ t.regs 6001 < 2 ∧
      (t.regs 6001 = 1 ↔ continuing = 1 ∧
        gm06Alg511BinaryRowValue (t.arrs 2800) < gm06Alg511BinaryRowValue (sb :: b)) ∧
      t.arrs 8 = s.arrs 8 ∧ t.arrs 2800 = s.arrs 2800 ∧ t.regs 6002 = s.regs 6002 := by
  have hparts := hcommon
  obtain ⟨hcounter, _, _, _, htarget, _, hmeta, hformat⟩ := hparts
  obtain ⟨sa, a, hcurrent, hsa, hlen, habits⟩ := hformat
  obtain ⟨t, u, guard, he, ht, hk, hguard, hbit, hiff⟩ := gm06Alg511BinaryLoopGuardProg_exec a b sa sb continuing s hw
    (by omega) habits hbits hsa hsb hc hcurrent htarget hContinuing
  have hrow : t.arrs 2800 = s.arrs 2800 := hk.2 2800 (by decide)
  have hcommonT : alg511BinaryLoopCommon x (sb :: b) incrementRow base i t := alg511BinaryLoopCommon.update hcommon
    (by
      intro r hr
      apply hk.1 r
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      intro a ha
      apply hk.2 a
      simp only [gm06Alg511RetainedSuccessorArrays, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> decide)
    (by rw [hk.1 6002 (by decide)]; exact hcounter)
    (by simpa only [hk.2 2803 (by decide)] using hmeta)
    (by rw [hrow]; exact ⟨sa, a, hcurrent, hsa, hlen, habits⟩)
  refine ⟨t, u, he, guard_time_bound ht hlen, hcommonT, (hk.1 6000 (by decide)).trans hContinuing,
    by simpa only [hguard] using hbit, ?_, hk.2 8 (by decide), hrow, hk.1 6002 (by decide)⟩
  simpa only [hguard, hrow, hcurrent] using hiff

/-- At a retained live linkage, the computed binary comparison
classifies the next state as still running or exactly at the target. -/
theorem alg511_binary_guard_linkage_exec {w : ℕ} {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (sb : ℕ) (b incrementRow : List ℕ)
    (base i steps increment : ℕ) (start : ℝ) (number : ℤ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max base b.length + i + 2 < 2 ^ w)
    (hsb : sb < 2) (hbits : ∀ d ∈ b, d < 2) (hinc : 0 < increment) (hi : i ≤ steps)
    (hcommon : alg511BinaryLoopCommon x (sb :: b) incrementRow base i s)
    (hf : s.regs 6000 = 1) (hcurrent : gm06Alg511BinaryRowValue (s.arrs 2800) = number + (i : ℤ) * increment)
    (htarget : gm06Alg511BinaryRowValue (sb :: b) = number + (steps : ℤ) * increment)
    (hL : alg511BinaryLoopLinkage rep start i s) :
    ∃ t u, Exec w gm06Alg511BinaryLoopGuardProg s t u ∧
      u ≤ 404 + 350 * (base + i + b.length + 1) ∧
      alg511BinaryLoopState rep (sb :: b) incrementRow base start number increment steps i t ∧ t.regs 6002 = s.regs 6002 := by
  obtain ⟨t, u, he, ht, hc, hfT, hgBit, hg, hp, ha, hcounter⟩ := alg511_binary_guard_common_exec x sb b incrementRow base i 1 s
    hw hsize hsb hbits (by decide) hcommon hf
  have hvalue : gm06Alg511BinaryRowValue (t.arrs 2800) = number + (i : ℤ) * increment :=
    (congrArg gm06Alg511BinaryRowValue ha).trans hcurrent
  have hround : t.regs 6001 = 1 ↔ i < steps := by
    rw [hg, hvalue, htarget]
    simp only [true_and]
    exact alg511_binary_round_value_lt number hinc
  have hLT := hL.frame hp
  refine ⟨t, u, he, ht, ⟨hc, ?_⟩, hcounter⟩
  by_cases hlt : i < steps
  · exact Or.inl ⟨hfT, hround.mpr hlt, hlt, hvalue, hLT⟩
  · have heq : i = steps := Nat.le_antisymm hi (Nat.le_of_not_gt hlt)
    have hzero : t.regs 6001 = 0 := by
      have hh : t.regs 6001 ≠ 1 := fun he => hlt (hround.mp he)
      exact bit_zero hgBit hh
    exact Or.inr (Or.inr ⟨hfT, hzero, heq ▸ hLT⟩)

/-- A proved failed successor clears the continuing bit, so the
actual binary guard reaches the stopped negative-answer branch. -/
theorem alg511_binary_guard_rejected_exec {w : ℕ} {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (sb : ℕ) (b incrementRow : List ℕ)
    (base i steps increment : ℕ) (start : ℝ) (number : ℤ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max base b.length + i + 2 < 2 ^ w)
    (hsb : sb < 2) (hbits : ∀ d ∈ b, d < 2)
    (hcommon : alg511BinaryLoopCommon x (sb :: b) incrementRow base i s) (hf : s.regs 6000 = 0)
    (hno : ¬ IsThetaFeasible x.drawing.pathCount G (start + (steps : ℝ) / x.drawing.pathCount)) :
    ∃ t u, Exec w gm06Alg511BinaryLoopGuardProg s t u ∧
      u ≤ 404 + 350 * (base + i + b.length + 1) ∧
      alg511BinaryLoopState rep (sb :: b) incrementRow base start number increment steps i t ∧ t.regs 6002 = s.regs 6002 := by
  obtain ⟨t, u, he, ht, hc, hfT, hgBit, hg, _, _, hcounter⟩ := alg511_binary_guard_common_exec x sb b incrementRow base i 0 s
    hw hsize hsb hbits (by decide) hcommon hf
  have hzero : t.regs 6001 = 0 := by
    have hh : t.regs 6001 ≠ 1 := fun h => Nat.zero_ne_one ((hg.mp h).1)
    exact bit_zero hgBit hh
  exact ⟨t, u, he, ht, ⟨hc, Or.inr (Or.inl ⟨hfT, hzero, hno⟩)⟩, hcounter⟩

/-- After either proved stopped branch, one controller round is a
skip and incrementing only its ordinary counter retains the invariant. -/
theorem alg511_binary_loop_stopped_round_exec {w : ℕ} {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (target incrementRow : List ℕ) (base : ℕ)
    (start : ℝ) (number : ℤ) (increment steps i : ℕ) (callee : Cmd) (s : State)
    (hcommon : alg511BinaryLoopCommon x target incrementRow base i s)
    (hstop : alg511BinaryLoopFinished rep start steps s) (hcounter : s.regs 6002 = i) :
    Exec w (gm06Alg511BinaryLoopBody callee) s s 2 ∧
      alg511BinaryLoopState rep target incrementRow base start number increment steps (i + 1) (s.setReg 6002 (i + 1)) ∧
      s.regs 6002 = i := by
  have hparts := hcommon
  obtain ⟨_, _, _, _, _, _, hmeta, hformat⟩ := hparts
  have hg : s.regs 6001 = 0 := hstop.elim (fun h => h.2.1) (fun h => h.2.1)
  have he : Exec w (gm06Alg511BinaryLoopBody callee) s s 2 :=
    .ite_false (Crossing.eval_reg hg (Nat.two_pow_pos w)) (.skip _)
  have hc : alg511BinaryLoopCommon x target incrementRow base (i + 1) (s.setReg 6002 (i + 1)) := alg511BinaryLoopCommon.update hcommon
    (by
      intro r hr
      apply State.setReg_regs_ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun _ _ => rfl) (by simp) hmeta (hformat.mono (by omega))
  have hs : alg511BinaryLoopFinished rep start steps (s.setReg 6002 (i + 1)) :=
    hstop.frame (State.setReg_regs_ne _ _ (by decide : (6000 : ℕ) ≠ 6002))
      (State.setReg_regs_ne _ _ (by decide : (6001 : ℕ) ≠ 6002)) rfl
  exact ⟨he, ⟨hc, Or.inr hs⟩, hcounter⟩

end GraphMinor.GM06
