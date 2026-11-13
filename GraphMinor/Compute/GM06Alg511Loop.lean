module

public import GraphMinor.Compute.GM06Alg511CompareWinding
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# The successor loop of VI (5.11)

Keep the current winding as the signed numerator pair in registers
54 and 55 over the positive path count in 52. The target remains in
62 and 63 over denominator 66. Compare them by cross multiplication.
A successful successor call replaces the stored path rows and adds
one to register 54. A failed call clears the continuing flag 6000.
The final answer is that flag.

The execution theorem composes a supplied successor command with
this actual while loop. Its array invariant is indexed by the
number of successful calls. A bound on that index proves termination
independently of the size of the target. The geometric application
uses (5.12) for this bound. This is a composition theorem for a
command parameter, rather than a theorem asserting algorithm (5.11).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Continue precisely while the last call succeeded and the current
winding is smaller than the target. -/
def gm06Alg511LoopGuard : Expr :=
  .op .mul (.reg 6000) (.op .lt
    (.op .add (.op .mul (.reg 54) (.reg 66)) (.op .mul (.reg 63) (.reg 52)))
    (.op .add (.op .mul (.reg 55) (.reg 66)) (.op .mul (.reg 62) (.reg 52))))

/-- A successor returns its Boolean answer in register zero. On
success its ordinary-dart path rows become the next stored linkage. -/
def gm06Alg511LoopBody (successor : Cmd) : Cmd :=
  .seq successor (.ite (.reg 0)
    (.assign 54 (.op .add (.reg 54) (.const 1)))
    (.assign 6000 (.const 0)))

/-- Initialize the continuing flag, repeat the successor calls, and
write the decision bit in the ordinary output register. -/
def gm06Alg511LoopProg (successor : Cmd) : Cmd :=
  .seq (.assign 6000 (.const 1))
    (.seq (.while gm06Alg511LoopGuard (gm06Alg511LoopBody successor))
      (.assign 0 (.reg 6000)))

/-- The scalar register layout after the stated number of successful
calls. These are only equalities with stored machine words. -/
def GM06Alg511LoopRegisters (p q a b k d r : ℕ) (s : State) : Prop :=
  s.regs 54 = p + r ∧ s.regs 55 = q ∧ s.regs 62 = a ∧ s.regs 63 = b ∧
    s.regs 52 = k ∧ s.regs 66 = d ∧ s.regs 6000 = 1

private theorem registers_kept {p q a b k d r : ℕ} {s t : State}
    (h : GM06Alg511LoopRegisters p q a b k d r s)
    (ht : ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j) :
    GM06Alg511LoopRegisters p q a b k d r t := by
  rcases h with ⟨hp, hq, ha, hb, hk, hd, hf⟩
  exact ⟨(ht 54 (by decide)).trans hp, (ht 55 (by decide)).trans hq,
    (ht 62 (by decide)).trans ha, (ht 63 (by decide)).trans hb,
    (ht 52 (by decide)).trans hk, (ht 66 (by decide)).trans hd,
    (ht 6000 (by decide)).trans hf⟩

private theorem registers_increment {p q a b k d r : ℕ} {s : State}
    (h : GM06Alg511LoopRegisters p q a b k d r s) :
    GM06Alg511LoopRegisters p q a b k d (r + 1) (s.setReg 54 (p + (r + 1))) := by
  rcases h with ⟨_, hq, ha, hb, hk, hd, hf⟩
  exact ⟨by simp, by simpa using hq, by simpa using ha, by simpa using hb,
    by simpa using hk, by simpa using hd, by simpa using hf⟩

private theorem cross_comparison {p q a b k d r steps : ℕ}
    (hk : 0 < k) (hd : 0 < d)
    (htarget : ((a : ℝ) - b) / d = ((p : ℝ) - q) / k + (steps : ℝ) / k) :
    (p + r) * d + b * k < q * d + a * k ↔ r < steps := by
  have hc := gm06Alg511Above_iff (p := a) (q := b) (a := p + r) (b := q) hd hk
  have hcur : (((p + r : ℕ) : ℝ) - q) / k = ((p : ℝ) - q) / k + (r : ℝ) / k := by
    push_cast
    ring
  have hreal : (((p + r : ℕ) : ℝ) - q) / k < ((a : ℝ) - b) / d ↔ r < steps := by
    rw [htarget, hcur, add_lt_add_iff_left, div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hk)]
    exact Nat.cast_lt
  constructor
  · intro h
    apply hreal.mp
    apply hc.mpr
    simpa only [Nat.add_comm] using h
  · intro h
    have hh := hc.mp (hreal.mpr h)
    simpa only [Nat.add_comm] using hh

private theorem guard_eval {w p q a b k d r steps flag : ℕ} {s : State}
    (hw : 1 < 2 ^ w) (hk : 0 < k) (hd : 0 < d)
    (hp : p + r < 2 ^ w) (hq : q < 2 ^ w) (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (hkfit : k < 2 ^ w) (hdfit : d < 2 ^ w)
    (hl : (p + r) * d + b * k < 2 ^ w) (hr : q * d + a * k < 2 ^ w)
    (hflag : flag = 0 ∨ flag = 1)
    (hregs : s.regs 54 = p + r ∧ s.regs 55 = q ∧ s.regs 62 = a ∧ s.regs 63 = b ∧
      s.regs 52 = k ∧ s.regs 66 = d ∧ s.regs 6000 = flag)
    (htarget : ((a : ℝ) - b) / d = ((p : ℝ) - q) / k + (steps : ℝ) / k) :
    gm06Alg511LoopGuard.eval w s = some (if flag = 1 ∧ r < steps then 1 else 0) := by
  rcases hregs with ⟨hP, hQ, hA, hB, hK, hD, hF⟩
  have hL := Crossing.eval_add
    (Crossing.eval_mul (Crossing.eval_reg hP hp) (Crossing.eval_reg hD hdfit)
      (lt_of_le_of_lt (Nat.le_add_right _ _) hl))
    (Crossing.eval_mul (Crossing.eval_reg hB hb) (Crossing.eval_reg hK hkfit)
      (lt_of_le_of_lt (Nat.le_add_left _ _) hl)) hl
  have hR := Crossing.eval_add
    (Crossing.eval_mul (Crossing.eval_reg hQ hq) (Crossing.eval_reg hD hdfit)
      (lt_of_le_of_lt (Nat.le_add_right _ _) hr))
    (Crossing.eval_mul (Crossing.eval_reg hA ha) (Crossing.eval_reg hK hkfit)
      (lt_of_le_of_lt (Nat.le_add_left _ _) hr)) hr
  have hcmp := Crossing.eval_lt hL hR hw
  have hffit : flag < 2 ^ w := by rcases hflag with h | h <;> omega
  have hprod : flag * (if (p + r) * d + b * k < q * d + a * k then 1 else 0) < 2 ^ w := by
    rcases hflag with h | h
    · rw [h, zero_mul]; omega
    · rw [h, one_mul]; split_ifs <;> omega
  have he := Crossing.eval_mul (Crossing.eval_reg hF hffit) hcmp hprod
  change gm06Alg511LoopGuard.eval w s = _ at he
  simp only [cross_comparison hk hd htarget] at he
  rcases hflag with h | h
  · simpa only [h, zero_mul, Nat.zero_ne_one, false_and, ite_false] using he
  · simpa only [h, one_mul, and_self_left, true_and] using he

/-- Compose an actual successor command with the (5.11) loop.
The hypothesis is its execution interface: zero certifies rejection,
and one supplies the next stored linkage invariant. A separate bound
on successful invariant indices gives the call and execution bounds.
No successor algorithm is asserted or assumed by a numbered theorem. -/
theorem gm06Alg511LoopWhile_exec_of_successor {w p q a b k d steps limit B : ℕ}
    (successor : Cmd) (I : ℕ → (Arr → List ℕ) → Prop) (rejected : Prop)
    (hw : 1 < 2 ^ w) (hk : 0 < k) (hd : 0 < d)
    (hpfit : p + limit + 1 < 2 ^ w) (hqfit : q < 2 ^ w)
    (hafit : a < 2 ^ w) (hbfit : b < 2 ^ w)
    (hkfit : k < 2 ^ w) (hdfit : d < 2 ^ w)
    (hlfit : (p + limit + 1) * d + b * k < 2 ^ w)
    (hrfit : q * d + a * k < 2 ^ w)
    (htarget : ((a : ℝ) - b) / d = ((p : ℝ) - q) / k + (steps : ℝ) / k)
    (hbound : ∀ r arrays, I r arrays → r ≤ limit)
    (hcall : ∀ r s, r < steps → I r s.arrs → GM06Alg511LoopRegisters p q a b k d r s →
      ∃ t u, Exec w successor s t u ∧ u ≤ B ∧
        (∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j) ∧
        ((t.regs 0 = 0 ∧ rejected) ∨ (t.regs 0 = 1 ∧ I (r + 1) t.arrs)))
    (r : ℕ) (s : State) (hI : I r s.arrs) (hrsteps : r ≤ steps)
    (hregs : GM06Alg511LoopRegisters p q a b k d r s) :
    ∃ t u calls, Exec w (.while gm06Alg511LoopGuard (gm06Alg511LoopBody successor)) s t u ∧
      calls ≤ limit - r + 1 ∧ u ≤ 17 + calls * (B + 22) ∧
      ((t.regs 6000 = 0 ∧ rejected) ∨
        (t.regs 6000 = 1 ∧ I steps t.arrs ∧ GM06Alg511LoopRegisters p q a b k d steps t)) := by
  suffices ∀ fuel r s, r + fuel = limit → I r s.arrs → r ≤ steps →
      GM06Alg511LoopRegisters p q a b k d r s →
      ∃ t u calls, Exec w (.while gm06Alg511LoopGuard (gm06Alg511LoopBody successor)) s t u ∧
        calls ≤ fuel + 1 ∧ u ≤ 17 + calls * (B + 22) ∧
        ((t.regs 6000 = 0 ∧ rejected) ∨
          (t.regs 6000 = 1 ∧ I steps t.arrs ∧ GM06Alg511LoopRegisters p q a b k d steps t)) by
    exact this (limit - r) r s (Nat.add_sub_of_le (hbound r s.arrs hI)) hI hrsteps hregs
  intro fuel
  induction fuel with
  | zero =>
    intro r s hr hI hrsteps hregs
    have hrlim : r = limit := by omega
    have hpr : p + r < 2 ^ w := by omega
    have hleft : (p + r) * d + b * k < 2 ^ w :=
      lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_right d (by omega : p + r ≤ p + limit + 1)) _) hlfit
    have hg := guard_eval hw hk hd hpr hqfit hafit hbfit hkfit hdfit hleft hrfit
      (Or.inr rfl : (1 : ℕ) = 0 ∨ 1 = 1) hregs htarget
    by_cases hlt : r < steps
    · obtain ⟨t, u, he, hu, hkeep, hout⟩ := hcall r s hlt hI hregs
      have hrt := registers_kept hregs hkeep
      rcases hout with ⟨hzero, hbad⟩ | ⟨hone, hnext⟩
      · let t' := t.setReg 6000 0
        have hb : Exec w (gm06Alg511LoopBody successor) s t' (u + 3) :=
          .seq he (.ite_false (Crossing.eval_reg hzero (by omega)) (.assign (Crossing.eval_const (by omega))))
        have hf : gm06Alg511LoopGuard.eval w t' = some 0 := by
          have hh := guard_eval hw hk hd hpr hqfit hafit hbfit hkfit hdfit hleft hrfit
            (Or.inl rfl : (0 : ℕ) = 0 ∨ 0 = 1)
            (show t'.regs 54 = p + r ∧ t'.regs 55 = q ∧ t'.regs 62 = a ∧ t'.regs 63 = b ∧
              t'.regs 52 = k ∧ t'.regs 66 = d ∧ t'.regs 6000 = 0 by
                rcases hrt with ⟨hP, hQ, hA, hB, hK, hD, _⟩
                exact ⟨by simpa [t'] using hP, by simpa [t'] using hQ,
                  by simpa [t'] using hA, by simpa [t'] using hB,
                  by simpa [t'] using hK, by simpa [t'] using hD, by simp [t']⟩) htarget
          simpa using hh
        refine ⟨t', 17 + (u + 3) + 17, 1,
          .while_true (by simpa [hlt] using hg) (by decide) hb (.while_false hf), by omega, ?_,
          Or.inl ⟨by simp [t'], hbad⟩⟩
        omega
      · have hh := hbound (r + 1) t.arrs hnext
        omega
    · have hrEq : r = steps := by omega
      exact ⟨s, 17, 0, .while_false (by simpa [hlt] using hg), by omega, by simp,
        Or.inr ⟨hregs.2.2.2.2.2.2, hrEq ▸ hI, hrEq ▸ hregs⟩⟩
  | succ fuel ih =>
    intro r s hr hI hrsteps hregs
    have hrlim : r ≤ limit := hbound r s.arrs hI
    have hpr : p + r < 2 ^ w := by omega
    have hleft : (p + r) * d + b * k < 2 ^ w :=
      lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_right d (by omega : p + r ≤ p + limit + 1)) _) hlfit
    have hg := guard_eval hw hk hd hpr hqfit hafit hbfit hkfit hdfit hleft hrfit
      (Or.inr rfl : (1 : ℕ) = 0 ∨ 1 = 1) hregs htarget
    by_cases hlt : r < steps
    · obtain ⟨t, u, he, hu, hkeep, hout⟩ := hcall r s hlt hI hregs
      have hrt := registers_kept hregs hkeep
      rcases hout with ⟨hzero, hbad⟩ | ⟨hone, hnext⟩
      · let t' := t.setReg 6000 0
        have hb : Exec w (gm06Alg511LoopBody successor) s t' (u + 3) :=
          .seq he (.ite_false (Crossing.eval_reg hzero (by omega)) (.assign (Crossing.eval_const (by omega))))
        have hf : gm06Alg511LoopGuard.eval w t' = some 0 := by
          have hh := guard_eval hw hk hd hpr hqfit hafit hbfit hkfit hdfit hleft hrfit
            (Or.inl rfl : (0 : ℕ) = 0 ∨ 0 = 1)
            (show t'.regs 54 = p + r ∧ t'.regs 55 = q ∧ t'.regs 62 = a ∧ t'.regs 63 = b ∧
              t'.regs 52 = k ∧ t'.regs 66 = d ∧ t'.regs 6000 = 0 by
                rcases hrt with ⟨hP, hQ, hA, hB, hK, hD, _⟩
                exact ⟨by simpa [t'] using hP, by simpa [t'] using hQ,
                  by simpa [t'] using hA, by simpa [t'] using hB,
                  by simpa [t'] using hK, by simpa [t'] using hD, by simp [t']⟩) htarget
          simpa using hh
        refine ⟨t', 17 + (u + 3) + 17, 1,
          .while_true (by simpa [hlt] using hg) (by decide) hb (.while_false hf), by omega, ?_,
          Or.inl ⟨by simp [t'], hbad⟩⟩
        omega
      · let t' := t.setReg 54 (p + (r + 1))
        have hinc : Exec w (.assign 54 (.op .add (.reg 54) (.const 1))) t t' 4 := by
          have heval := Crossing.eval_add (Crossing.eval_reg hrt.1 hpr)
            (Crossing.eval_const hw) (by omega : p + r + 1 < 2 ^ w)
          simpa only [Nat.add_assoc, Expr.cost, Nat.reduceAdd] using Exec.assign (r := 54) heval
        have hb : Exec w (gm06Alg511LoopBody successor) s t' (u + 5) :=
          .seq he (.ite_true (Crossing.eval_reg hone hw) (by decide) hinc)
        have hregs' := registers_increment hrt
        obtain ⟨v, vtime, calls, hev, hcalls, htime, hv⟩ :=
          ih (r + 1) t' (by omega) hnext (by omega) hregs'
        refine ⟨v, 17 + (u + 5) + vtime, calls + 1,
          .while_true (by simpa [hlt] using hg) (by decide) hb hev, by omega, ?_, hv⟩
        calc
          17 + (u + 5) + vtime ≤ 17 + (B + 5) + (17 + calls * (B + 22)) := by omega
          _ = 17 + (calls + 1) * (B + 22) := by ring
    · have hrEq : r = steps := by omega
      exact ⟨s, 17, 0, .while_false (by simpa [hlt] using hg), by omega, by simp,
        Or.inr ⟨hregs.2.2.2.2.2.2, hrEq ▸ hI, hrEq ▸ hregs⟩⟩


/-- The complete loop command initializes its own flag and writes
the final Boolean answer. The successful branch retains the actual
array invariant at the target index; the negative branch retains
the successor's rejection conclusion. -/
theorem gm06Alg511LoopProg_exec_of_successor {w p q a b k d steps limit B : ℕ}
    (successor : Cmd) (I : ℕ → (Arr → List ℕ) → Prop) (rejected : Prop)
    (hw : 1 < 2 ^ w) (hk : 0 < k) (hd : 0 < d)
    (hpfit : p + limit + 1 < 2 ^ w) (hqfit : q < 2 ^ w)
    (hafit : a < 2 ^ w) (hbfit : b < 2 ^ w)
    (hkfit : k < 2 ^ w) (hdfit : d < 2 ^ w)
    (hlfit : (p + limit + 1) * d + b * k < 2 ^ w)
    (hrfit : q * d + a * k < 2 ^ w)
    (htarget : ((a : ℝ) - b) / d = ((p : ℝ) - q) / k + (steps : ℝ) / k)
    (hbound : ∀ r arrays, I r arrays → r ≤ limit)
    (hcall : ∀ r s, r < steps → I r s.arrs → GM06Alg511LoopRegisters p q a b k d r s →
      ∃ t u, Exec w successor s t u ∧ u ≤ B ∧
        (∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j) ∧
        ((t.regs 0 = 0 ∧ rejected) ∨ (t.regs 0 = 1 ∧ I (r + 1) t.arrs)))
    (s : State) (hI : I 0 s.arrs)
    (hregs : s.regs 54 = p ∧ s.regs 55 = q ∧ s.regs 62 = a ∧ s.regs 63 = b ∧
      s.regs 52 = k ∧ s.regs 66 = d) :
    ∃ t u calls, Exec w (gm06Alg511LoopProg successor) s t u ∧
      calls ≤ limit + 1 ∧ u ≤ 21 + calls * (B + 22) ∧
      ((t.regs 0 = 0 ∧ rejected) ∨
        (t.regs 0 = 1 ∧ I steps t.arrs ∧ GM06Alg511LoopRegisters p q a b k d steps t)) := by
  let s₀ := s.setReg 6000 1
  have he₀ : Exec w (.assign 6000 (.const 1)) s s₀ 2 :=
    .assign (Crossing.eval_const hw)
  have hr₀ : GM06Alg511LoopRegisters p q a b k d 0 s₀ := by
    rcases hregs with ⟨hP, hQ, hA, hB, hK, hD⟩
    exact ⟨by simpa [s₀] using hP, by simpa [s₀] using hQ,
      by simpa [s₀] using hA, by simpa [s₀] using hB,
      by simpa [s₀] using hK, by simpa [s₀] using hD, by simp [s₀]⟩
  obtain ⟨t, u, calls, he, hcalls, htime, hout⟩ := gm06Alg511LoopWhile_exec_of_successor
    successor I rejected hw hk hd hpfit hqfit hafit hbfit hkfit hdfit hlfit hrfit
    htarget hbound hcall 0 s₀ hI (Nat.zero_le _) hr₀
  have hbit : t.regs 6000 = 0 ∨ t.regs 6000 = 1 :=
    hout.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hfit : t.regs 6000 < 2 ^ w := by rcases hbit with h | h <;> omega
  let v := t.setReg 0 (t.regs 6000)
  have he₁ : Exec w (.assign 0 (.reg 6000)) t v 2 :=
    .assign (Crossing.eval_reg rfl hfit)
  have hefull : Exec w (gm06Alg511LoopProg successor) s v (2 + (u + 2)) :=
    .seq he₀ (.seq he he₁)
  refine ⟨v, 2 + (u + 2), calls, hefull, by simpa using hcalls, by omega, ?_⟩
  rcases hout with ⟨hzero, hbad⟩ | ⟨hone, hI, hregs⟩
  · exact Or.inl ⟨by simp [v, hzero], hbad⟩
  · refine Or.inr ⟨by simp [v, hone], hI, registers_kept hregs ?_⟩
    intro j hj
    have hj0 : j ≠ 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact State.setReg_regs_ne t (t.regs 6000) hj0

end GraphMinor.Compute
