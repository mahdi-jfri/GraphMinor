module

public import GraphMinor.Compute.GM06Alg34SingletonExhaust
import Mathlib.Tactic.Ring

/-!
# Original-input bounds for singleton exhaustion

The uniform reservation is cubic in the original size. Bounding it by
a fixed power gives a logarithmic word-size bound in that original
size. Substitution in the verified loop bound gives a polynomial time
bound for the complete singleton exhaustion program.
-/

public section
namespace GraphMinor.Compute

private theorem reservation_power (n : ℕ) :
    10 * (n + 2) ^ 3 + 2 ≤ (n + 2) ^ 7 := by
  ring_nf
  omega

/-- The fixed word size for singleton exhaustion is logarithmic in the
original input size, even though intermediate payloads may grow. -/
theorem gm06SingletonExhaust_wordSize_le (n : ℕ) :
    wordSize 3 (10 * (n + 2) ^ 3) ≤ wordSize 21 n := by
  have hlt := (reservation_power n).trans_lt (pow_lt_two_pow_wordSize (by decide : 1 ≤ 7) n)
  have hlog := Nat.log_lt_of_lt_pow (b := 2) (by omega : 10 * (n + 2) ^ 3 + 2 ≠ 0) hlt
  unfold wordSize at *
  omega

/-- Substituting the cubic reservation into the loop's time bound gives
a polynomial bound in the original size. -/
theorem gm06SingletonExhaust_time_le (x : GM06DrawingData) :
    (x.n + 1) * (1300 * (10 * (x.size + 2) ^ 3 + 2) ^ 3 + 10) + 1 ≤
      2000 * (x.size + 2) ^ 22 := by
  have hc := reservation_power x.size
  have hcube := Nat.pow_le_pow_left hc 3
  rw [← Nat.pow_mul] at hcube
  have hn : x.n + 1 ≤ x.size + 2 := by have hh := x.counts_le_size.1; omega
  have hprod := Nat.mul_le_mul hn (show
      1300 * (10 * (x.size + 2) ^ 3 + 2) ^ 3 + 10 ≤
      1300 * (x.size + 2) ^ 21 + 10 by norm_num at hcube; omega)
  have hcalc : (x.size + 2) * (1300 * (x.size + 2) ^ 21 + 10) =
      1300 * (x.size + 2) ^ 22 + 10 * (x.size + 2) := by ring
  rw [hcalc] at hprod
  have hbase := Nat.le_self_pow (by decide : 22 ≠ 0) (x.size + 2)
  omega

/-- The actual singleton exhaustion program has polynomial time and
logarithmic words in the original input size and returns its exact
finite-data exhaustion, with arbitrary scratch contents. -/
theorem gm06SingletonExhaustProg_exec_poly (x : GM06DrawingData)
    (hcuff : ∃ L, x.cuffs = [L]) {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize 21 x.size) gm06SingletonExhaustProg s s' t ∧
      t ≤ 2000 * (x.size + 2) ^ 22 ∧
      s'.arrs 0 = (gm06ReduceSingletons x).words ∧ s'.regs 113 = 0 := by
  have hr := gm06SingletonExhaust_reservation x
  obtain ⟨s', t, hex, ht, hin, hz⟩ :=
    gm06SingletonExhaustProg_exec x (gm06SingletonExhaust_wordSize_le x.size) hr.2 hr.1 hcuff hinput
  exact ⟨s', t, hex, ht.trans (gm06SingletonExhaust_time_le x), hin, hz⟩

end GraphMinor.Compute
