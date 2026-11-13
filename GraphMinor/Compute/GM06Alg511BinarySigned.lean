module

public import GraphMinor.Compute.GM06Alg511BinaryAbsSubtract
public import GraphMinor.Compute.GM06Alg511BinaryMultiply
import Mathlib.Tactic

/-!
# Signed binary arithmetic

An integer is a sign bit and a little-endian binary digit row.
Equal signs use unsigned addition. Opposite signs use absolute
subtraction, and the original borrow selects the resulting sign.
Multiplication uses unsigned multiplication and the exclusive-or
of the signs. All magnitude computations stay in digit arrays.
The input signs are in registers 2400 and 2401, the output sign
is in 2402, and the magnitude rows are 2000, 2001 and 2002.
These operations implement the signed arithmetic of VI (5.11),
page 134, including both representations of zero.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Interpret a sign bit and binary magnitude row as an integer. -/
def gm06Alg511BinarySignedValue (sign : ℕ) (digits : List ℕ) : ℤ :=
  if sign = 1 then -(gm06Alg511BinaryValue digits : ℤ) else (gm06Alg511BinaryValue digits : ℤ)

/-- The machine interpretation agrees with the supplied signed
integer record, including either sign for zero. -/
theorem gm06Alg511BinarySignedValue_integer (z : GM06Alg511BinaryInteger) :
    gm06Alg511BinarySignedValue z.negative.toNat (z.digits.map Bool.toNat) = z.value := by
  cases z with
  | mk sign digits => cases sign <;> rfl

/-- Exclusive-or of two sign bits, computed using word equality. -/
def gm06Alg511BinarySignXor (a b : ℕ) : ℕ := if a = b then 0 else 1

/-- The expression for exclusive-or reads two sign registers. -/
def gm06Alg511BinarySignXorExpr (ra rb : ℕ) : Expr :=
  .op .sub (.const 1) (.op .eq (.reg ra) (.reg rb))

private theorem sign_xor_eval {w : ℕ} (s : State) (ra rb a b : ℕ)
    (hw : 1 < 2 ^ w) (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (hA : s.regs ra = a) (hB : s.regs rb = b) :
    (gm06Alg511BinarySignXorExpr ra rb).eval w s = some (gm06Alg511BinarySignXor a b) := by
  have he := Crossing.eval_sub (Crossing.eval_const hw)
    (Crossing.eval_eq (Crossing.eval_reg hA ha) (Crossing.eval_reg hB hb) hw)
  by_cases h : a = b <;> simpa only [gm06Alg511BinarySignXorExpr, gm06Alg511BinarySignXor, h, ite_true, ite_false, Nat.reduceSub] using he

private theorem different_sign_sum (sa sb flag : ℕ) (x y z : ℤ)
    (ha : sa < 2) (hb : sb < 2) (hf : flag < 2) (hne : sa ≠ sb)
    (hz : z = if flag = 1 then y - x else x - y) :
    (if gm06Alg511BinarySignXor sa flag = 1 then -z else z) =
      (if sa = 1 then -x else x) + (if sb = 1 then -y else y) := by
  interval_cases sa <;> interval_cases sb <;> interval_cases flag <;>
    simp_all [gm06Alg511BinarySignXor] <;> omega

private theorem sign_product (sa sb : ℕ) (x y : ℤ) (ha : sa < 2) (hb : sb < 2) :
    (if gm06Alg511BinarySignXor sa sb = 1 then -(x * y) else x * y) =
      (if sa = 1 then -x else x) * (if sb = 1 then -y else y) := by
  interval_cases sa <;> interval_cases sb <;> simp [gm06Alg511BinarySignXor]

/-- Add magnitude rows with the same sign. -/
def gm06Alg511BinarySameSignAddProg : Cmd :=
  .seq gm06Alg511BinaryAddProg (.assign 2402 (.reg 2400))

/-- Add magnitude rows with opposite signs, using the original
borrow to choose which supplied sign belongs to the difference. -/
def gm06Alg511BinaryDifferentSignAddProg : Cmd :=
  .seq gm06Alg511BinaryAbsSubtractProg
    (.seq (gm06Alg511CopyRowProg 2005 2002)
      (.assign 2402 (gm06Alg511BinarySignXorExpr 2400 2404)))

/-- Signed binary addition retains both supplied operands. -/
def gm06Alg511BinarySignedAddProg : Cmd :=
  .ite (.op .eq (.reg 2400) (.reg 2401))
    gm06Alg511BinarySameSignAddProg gm06Alg511BinaryDifferentSignAddProg

private theorem signed_add_frame {w : ℕ} {s t : State} {u : ℕ}
    (he : Exec w gm06Alg511BinarySignedAddProg s t u) :
    Keeps [0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2402, 2404]
      [2000, 2001, 2002, 2003, 2004, 2005] s t := by
  have hr : gm06Alg511BinarySignedAddProg.writtenRegs ⊆
      ([0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2402, 2404] : List ℕ).toFinset := by decide
  have ha : gm06Alg511BinarySignedAddProg.writtenArrs ⊆
      ([2000, 2001, 2002, 2003, 2004, 2005] : List ℕ).toFinset := by decide
  exact ⟨fun r hn => he.regs_eq_of_not_mem_writtenRegs (fun hm => hn (List.mem_toFinset.mp (hr hm))),
    fun a hn => he.arrs_eq_of_not_mem_writtenArrs (fun hm => hn (List.mem_toFinset.mp (ha hm)))⟩

/-- Signed addition computes the exact sum in linear time in the
supplied digit counts. Its sign is a bit, its magnitude row is binary,
its width is at most one more than the larger input width, and both
original operands and their signs are preserved. -/
theorem gm06Alg511BinarySignedAddProg_exec {w : ℕ} (a b : List ℕ) (sa sb : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max a.length b.length + 1 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) (hsa : sa < 2) (hsb : sb < 2)
    (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b)
    (hSA : s.regs 2400 = sa) (hSB : s.regs 2401 = sb) :
    ∃ t u out sign, Exec w gm06Alg511BinarySignedAddProg s t u ∧
      u ≤ 240 + 260 * max a.length b.length ∧
      Keeps [0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2402, 2404]
        [2002, 2003, 2004, 2005] s t ∧
      t.arrs 2002 = out ∧ t.regs 2402 = sign ∧ sign < 2 ∧
      out.length ≤ max a.length b.length + 1 ∧ (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinarySignedValue sign out = gm06Alg511BinarySignedValue sa a + gm06Alg511BinarySignedValue sb b := by
  have has : sa < 2 ^ w := hsa.trans_le (by omega)
  have hbs : sb < 2 ^ w := hsb.trans_le (by omega)
  have heq := Crossing.eval_eq (Crossing.eval_reg hSA has) (Crossing.eval_reg hSB hbs) (by omega : 1 < 2 ^ w)
  by_cases hsame : sa = sb
  · obtain ⟨st, u, he, ht, hk, hout⟩ := gm06Alg511BinaryAddProg_exec a b s hw hsize habits hbbits hA hB
    let out := gm06Alg511BinaryAddDigits (max a.length b.length) a b 0
    let t := st.setReg 2402 sa
    have he₂ : Exec w (.assign 2402 (.reg 2400)) st t 2 :=
      .assign (Crossing.eval_reg ((hk.1 2400 (by decide)).trans hSA) has)
    have hex : Exec w gm06Alg511BinarySignedAddProg s t (3 + (u + 2)) :=
      .ite_true (by simpa only [hsame, ite_true] using heq) (by decide) (.seq he he₂)
    have hframe := signed_add_frame hex
    refine ⟨t, _, out, sa, hex, by omega, ⟨hframe.1, ?_⟩,
      by simpa only [t, State.setReg_arrs] using hout, by simp [t], hsa, ?_, ?_, ?_⟩
    · intro ar har
      by_cases heq0 : ar = 2000
      · subst ar; simpa only [t, State.setReg_arrs] using hk.2 2000 (by decide)
      by_cases heqar : ar = 2001
      · subst ar; simpa only [t, State.setReg_arrs] using hk.2 2001 (by decide)
      · exact hframe.2 ar (by simp only [List.mem_cons, List.not_mem_nil, or_false] at har ⊢; tauto)
    · rw [gm06Alg511BinaryAddDigits_length]
    · exact gm06Alg511BinaryAddDigits_words _ a b 0 habits hbbits (by decide)
    · have hv := gm06Alg511BinaryAddDigits_value (max a.length b.length) a b 0
        (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      simp only [gm06Alg511BinarySignedValue, ← hsame, Nat.add_zero] at hv ⊢
      by_cases hsign : sa = 1 <;> simp only [hsign, ite_true, ite_false]
      · rw [show gm06Alg511BinaryValue out = gm06Alg511BinaryValue a + gm06Alg511BinaryValue b from hv, Nat.cast_add]
        ring
      · exact_mod_cast hv
  · obtain ⟨st, u, out, flag, he, ht, hk, hout, hflag, hflagBit, _, hlen, hbits, hval⟩ :=
      gm06Alg511BinaryAbsSubtractProg_exec a b s hw hsize habits hbbits hA hB
    have houtFit : out.length < 2 ^ w := by omega
    obtain ⟨su, v, he₂, ht₂, hk₂, hout₂⟩ := gm06Alg511CopyRowProg_exec 2005 2002 (by decide) out st
      (by omega) houtFit (fun d hd => (hbits d hd).trans_le (by omega)) hout
    let sign := gm06Alg511BinarySignXor sa flag
    have hsign : sign < 2 := by unfold sign gm06Alg511BinarySignXor; split_ifs <;> decide
    let t := su.setReg 2402 sign
    have he₃ : Exec w (.assign 2402 (gm06Alg511BinarySignXorExpr 2400 2404)) su t 6 :=
      .assign (sign_xor_eval su 2400 2404 sa flag (by omega) has (hflagBit.trans_le (by omega))
        ((hk₂.1 2400 (by decide)).trans ((hk.1 2400 (by decide)).trans hSA))
        ((hk₂.1 2404 (by decide)).trans hflag))
    have hex : Exec w gm06Alg511BinarySignedAddProg s t (3 + (u + (v + 6))) :=
      .ite_false (by simpa only [hsame, ite_false] using heq) (.seq he (.seq he₂ he₃))
    have hframe := signed_add_frame hex
    refine ⟨t, _, out, sign, hex, by omega, ⟨hframe.1, ?_⟩,
      by simpa only [t, State.setReg_arrs] using hout₂, by simp [t], hsign, by omega, hbits, ?_⟩
    · intro ar har
      by_cases heq0 : ar = 2000
      · subst ar
        simpa only [t, State.setReg_arrs] using (hk₂.2 2000 (by decide)).trans (hk.2 2000 (by decide))
      by_cases heqar : ar = 2001
      · subst ar
        simpa only [t, State.setReg_arrs] using (hk₂.2 2001 (by decide)).trans (hk.2 2001 (by decide))
      · exact hframe.2 ar (by simp only [List.mem_cons, List.not_mem_nil, or_false] at har ⊢; tauto)
    · exact different_sign_sum sa sb flag _ _ _ hsa hsb hflagBit hsame hval

/-- Multiply magnitude rows and compute the exclusive-or of their signs. -/
def gm06Alg511BinarySignedMultiplyProg : Cmd :=
  .seq gm06Alg511BinaryMultiplyProg (.assign 2402 (gm06Alg511BinarySignXorExpr 2400 2401))

/-- Signed multiplication has the exact integer product and a
quadratic digit-count bound, retaining both operands and signs. -/
theorem gm06Alg511BinarySignedMultiplyProg_exec {w : ℕ} (a b : List ℕ) (sa sb : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : a.length + b.length + 1 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) (hsa : sa < 2) (hsb : sb < 2)
    (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b)
    (hSA : s.regs 2400 = sa) (hSB : s.regs 2401 = sb) :
    ∃ t u out sign, Exec w gm06Alg511BinarySignedMultiplyProg s t u ∧
      u ≤ 510 * (a.length + b.length + 1) ^ 2 ∧
      Keeps [20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2233, 2235, 2402]
        [2002, 2300, 2301, 2302] s t ∧
      t.arrs 2002 = out ∧ t.regs 2402 = sign ∧ sign < 2 ∧
      out.length ≤ a.length + b.length ∧ (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinarySignedValue sign out = gm06Alg511BinarySignedValue sa a * gm06Alg511BinarySignedValue sb b := by
  obtain ⟨st, u, out, he, ht, hk, hout, hlen, hbits, hval⟩ :=
    gm06Alg511BinaryMultiplyProg_exec a b s hw hsize habits hbbits hA hB
  let sign := gm06Alg511BinarySignXor sa sb
  let t := st.setReg 2402 sign
  have hsign : sign < 2 := by unfold sign gm06Alg511BinarySignXor; split_ifs <;> decide
  have he₂ : Exec w (.assign 2402 (gm06Alg511BinarySignXorExpr 2400 2401)) st t 6 :=
    .assign (sign_xor_eval st 2400 2401 sa sb (by omega) (hsa.trans_le (by omega)) (hsb.trans_le (by omega))
      ((hk.1 2400 (by decide)).trans hSA) ((hk.1 2401 (by decide)).trans hSB))
  refine ⟨t, u + 6, out, sign, .seq he he₂, ?_, (hk.mono (by simp) (by simp)).setReg (by simp) sign,
    by simpa only [t, State.setReg_arrs] using hout, by simp [t], hsign, hlen, hbits, ?_⟩
  · have hp : 1 ≤ (a.length + b.length + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · unfold gm06Alg511BinarySignedValue
    rw [hval, Nat.cast_mul]
    exact sign_product sa sb _ _ hsa hsb

/-- Subtraction negates the second sign for the addition call,
then restores that original sign from a retained scratch register. -/
def gm06Alg511BinarySignedSubtractProg : Cmd :=
  .seq (.assign 2410 (.reg 2401))
    (.seq (.assign 2401 (.op .sub (.const 1) (.reg 2401)))
      (.seq gm06Alg511BinarySignedAddProg (.assign 2401 (.reg 2410))))

private theorem flip_sign_value (sign : ℕ) (ds : List ℕ) (hs : sign < 2) :
    gm06Alg511BinarySignedValue (1 - sign) ds = -gm06Alg511BinarySignedValue sign ds := by
  interval_cases sign <;> simp [gm06Alg511BinarySignedValue]

/-- Signed subtraction computes the exact difference in linear
time, while restoring both original magnitude rows and signs. -/
theorem gm06Alg511BinarySignedSubtractProg_exec {w : ℕ} (a b : List ℕ) (sa sb : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max a.length b.length + 1 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) (hsa : sa < 2) (hsb : sb < 2)
    (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b)
    (hSA : s.regs 2400 = sa) (hSB : s.regs 2401 = sb) :
    ∃ t u out sign, Exec w gm06Alg511BinarySignedSubtractProg s t u ∧
      u ≤ 250 + 260 * max a.length b.length ∧
      Keeps [0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2402, 2404, 2410]
        [2002, 2003, 2004, 2005] s t ∧
      t.arrs 2002 = out ∧ t.regs 2402 = sign ∧ sign < 2 ∧
      out.length ≤ max a.length b.length + 1 ∧ (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinarySignedValue sign out = gm06Alg511BinarySignedValue sa a - gm06Alg511BinarySignedValue sb b := by
  have hbs : sb < 2 ^ w := hsb.trans_le (by omega)
  let s₁ := s.setReg 2410 sb
  let s₂ := s₁.setReg 2401 (1 - sb)
  have he₁ : Exec w (.assign 2410 (.reg 2401)) s s₁ 2 := .assign (Crossing.eval_reg hSB hbs)
  have he₂ : Exec w (.assign 2401 (.op .sub (.const 1) (.reg 2401))) s₁ s₂ 4 :=
    .assign (Crossing.eval_sub (Crossing.eval_const (by omega))
      (Crossing.eval_reg (by simpa only [s₁, State.setReg_regs_ne _ _ (by decide : (2401 : ℕ) ≠ 2410)] using hSB) hbs))
  obtain ⟨st, u, out, sign, he₃, ht₃, hk₃, hout, hsign, hsignBit, hlen, hbits, hval⟩ :=
    gm06Alg511BinarySignedAddProg_exec a b sa (1 - sb) s₂ hw hsize habits hbbits hsa (by omega)
      hA hB (by simpa only [s₂, s₁, State.setReg_regs_ne _ _ (by decide : (2400 : ℕ) ≠ 2401),
        State.setReg_regs_ne _ _ (by decide : (2400 : ℕ) ≠ 2410)] using hSA) (by simp [s₂])
  let t := st.setReg 2401 sb
  have hbackup : st.regs 2410 = sb := (hk₃.1 2410 (by decide)).trans (by simp [s₂, s₁])
  have he₄ : Exec w (.assign 2401 (.reg 2410)) st t 2 := .assign (Crossing.eval_reg hbackup hbs)
  let R := [0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2401, 2402, 2404, 2410]
  let A := [2002, 2003, 2004, 2005]
  have hk₀ : Keeps R A s s₂ :=
    ((Keeps.refl _ _ s).setReg (by simp [R]) sb).setReg (by simp [R]) (1 - sb)
  have hk : Keeps R A s t := (hk₀.trans hk₃ (by simp [R]) (by simp [A])).setReg (show 2401 ∈ R by simp [R]) sb
  refine ⟨t, 2 + (4 + (u + 2)), out, sign, .seq he₁ (.seq he₂ (.seq he₃ he₄)), by omega,
    ⟨?_, hk.2⟩, by simpa only [t, State.setReg_arrs] using hout,
    by simpa only [t, State.setReg_regs_ne _ _ (by decide : (2402 : ℕ) ≠ 2401)] using hsign,
    hsignBit, hlen, hbits, ?_⟩
  · intro r hr
    by_cases heq : r = 2401
    · subst r
      exact (State.setReg_regs_self _ _ _).trans hSB.symm
    · exact hk.1 r (by simp only [R, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; tauto)
  · rw [flip_sign_value sb b hsb] at hval
    simpa only [sub_eq_add_neg] using hval

end GraphMinor.Compute
