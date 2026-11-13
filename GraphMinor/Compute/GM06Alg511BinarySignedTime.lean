module

public import GraphMinor.Compute.GM06Alg511BinaryCompare
import Mathlib.Tactic

/-!
# Bit-count time bounds for signed arithmetic

The size of two supplied signed integers is their total digit
count plus the two sign words. The magnitude values are not used
as a size measure. The exact execution theorems give linear time
for addition, subtraction and comparison, and quadratic time for
multiplication. This file places those executions on the Word RAM
with logarithmic words. It supplies the four arithmetic operations
needed by the binary implementation of VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Count both supplied sign words and every actual input bit. -/
def gm06Alg511BinarySignedSize (x : GM06Alg511BinaryInteger × GM06Alg511BinaryInteger) : ℕ :=
  x.1.digits.length + x.2.digits.length + 2

/-- The signed arithmetic input holds only the two supplied signs
and their actual bit rows, without interpreted magnitudes. -/
def gm06Alg511BinarySignedIn (x : GM06Alg511BinaryInteger × GM06Alg511BinaryInteger) (s : State) : Prop :=
  s.arrs 2000 = x.1.digits.map Bool.toNat ∧ s.arrs 2001 = x.2.digits.map Bool.toNat ∧
    s.regs 2400 = x.1.negative.toNat ∧ s.regs 2401 = x.2.negative.toNat

/-- An arithmetic output is a sign and a binary row for the exact
integer result, with a digit-count bound on its width. -/
def gm06Alg511BinarySignedOut (op : ℤ → ℤ → ℤ)
    (x : GM06Alg511BinaryInteger × GM06Alg511BinaryInteger) (s : State) : Prop :=
  gm06Alg511BinarySignedValue (s.regs 2402) (s.arrs 2002) = op x.1.value x.2.value ∧
    s.regs 2402 < 2 ∧ (∀ d ∈ s.arrs 2002, d < 2) ∧
      (s.arrs 2002).length ≤ x.1.digits.length + x.2.digits.length + 1

private theorem supplied_bits (xs : List Bool) : ∀ d ∈ xs.map Bool.toNat, d < 2 := by
  intro d hd
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
  cases q <;> decide

private theorem sign_bit (s : Bool) : s.toNat < 2 := by cases s <;> decide

private theorem signed_word_bounds (x : GM06Alg511BinaryInteger × GM06Alg511BinaryInteger) :
    3 < 2 ^ wordSize 2 (gm06Alg511BinarySignedSize x) ∧
      x.1.digits.length + x.2.digits.length + 1 < 2 ^ wordSize 2 (gm06Alg511BinarySignedSize x) := by
  let size := gm06Alg511BinarySignedSize x
  have hp := pow_lt_two_pow_wordSize (c := 2) (by decide) size
  have hb : 3 ≤ size + 2 := by dsimp only [size, gm06Alg511BinarySignedSize]; omega
  have hh : 3 < (size + 2) ^ 2 := by nlinarith only [hb]
  exact ⟨hh.trans hp,
    lt_two_pow_wordSize_of_le (c := 2) (n := size) (by decide) (by dsimp only [size, gm06Alg511BinarySignedSize]; omega)⟩

private theorem signed_computes_of_exec (op : ℤ → ℤ → ℤ) (prog : Cmd) (C p : ℕ) (hC : 1 ≤ C)
    (hrun : ∀ {w : ℕ} (a b : List ℕ) (sa sb : ℕ) (s : State),
      3 < 2 ^ w → a.length + b.length + 1 < 2 ^ w →
      (∀ d ∈ a, d < 2) → (∀ d ∈ b, d < 2) → sa < 2 → sb < 2 →
      s.arrs 2000 = a → s.arrs 2001 = b → s.regs 2400 = sa → s.regs 2401 = sb →
      ∃ t u out sign, Exec w prog s t u ∧ u ≤ C * (a.length + b.length + 1) ^ p ∧
        t.arrs 2002 = out ∧ t.regs 2402 = sign ∧ sign < 2 ∧
        out.length ≤ a.length + b.length + 1 ∧ (∀ d ∈ out, d < 2) ∧
        gm06Alg511BinarySignedValue sign out = op (gm06Alg511BinarySignedValue sa a) (gm06Alg511BinarySignedValue sb b)) :
    ComputesRelInTime gm06Alg511BinarySignedSize gm06Alg511BinarySignedIn (gm06Alg511BinarySignedOut op)
      prog (fun n => (n + 1) ^ p) := by
  refine ⟨C, 2, hC, by decide, ?_⟩
  intro x s hs
  have hb := signed_word_bounds x
  obtain ⟨t, u, out, sign, he, ht, hout, hsign, hsignBit, hlen, hbits, hval⟩ :=
    hrun (x.1.digits.map Bool.toNat) (x.2.digits.map Bool.toNat) x.1.negative.toNat x.2.negative.toNat s
      hb.1 (by simpa only [List.length_map] using hb.2) (supplied_bits _) (supplied_bits _)
      (sign_bit _) (sign_bit _) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  refine ⟨t, u, he, ?_, ?_, by simpa only [hsign] using hsignBit,
    by simpa only [hout] using hbits, ?_⟩
  · have hw : (x.1.digits.map Bool.toNat).length + (x.2.digits.map Bool.toNat).length + 1 ≤
        gm06Alg511BinarySignedSize x + 1 := by simp [gm06Alg511BinarySignedSize]
    exact ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw p))
  · simpa only [hout, hsign, gm06Alg511BinarySignedValue_integer] using hval
  · simpa only [hout, List.length_map] using hlen

/-- Signed binary addition has linear time in total supplied bit
count and logarithmic machine words, for every pair of integers. -/
theorem gm06Alg511BinarySignedAdd_computes :
    ComputesRelInTime gm06Alg511BinarySignedSize gm06Alg511BinarySignedIn
      (gm06Alg511BinarySignedOut (· + ·)) gm06Alg511BinarySignedAddProg (fun n => n + 1) := by
  have hh := signed_computes_of_exec (· + ·) gm06Alg511BinarySignedAddProg 500 1 (by decide)
  simp only [pow_one] at hh
  apply hh
  intro w a b sa sb s hw hsize habits hbbits hsa hsb hA hB hSA hSB
  obtain ⟨t, u, out, sign, he, ht, _, hout, hsign, hsignBit, hlen, hbits, hval⟩ :=
    gm06Alg511BinarySignedAddProg_exec a b sa sb s hw (by omega) habits hbbits hsa hsb hA hB hSA hSB
  refine ⟨t, u, out, sign, he, ?_, hout, hsign, hsignBit, by omega, hbits, hval⟩
  have hm : max a.length b.length ≤ a.length + b.length := by omega
  omega

/-- Signed binary subtraction has linear time in total supplied
bit count and logarithmic machine words, for every pair of integers. -/
theorem gm06Alg511BinarySignedSubtract_computes :
    ComputesRelInTime gm06Alg511BinarySignedSize gm06Alg511BinarySignedIn
      (gm06Alg511BinarySignedOut (· - ·)) gm06Alg511BinarySignedSubtractProg (fun n => n + 1) := by
  have hh := signed_computes_of_exec (· - ·) gm06Alg511BinarySignedSubtractProg 520 1 (by decide)
  simp only [pow_one] at hh
  apply hh
  intro w a b sa sb s hw hsize habits hbbits hsa hsb hA hB hSA hSB
  obtain ⟨t, u, out, sign, he, ht, _, hout, hsign, hsignBit, hlen, hbits, hval⟩ :=
    gm06Alg511BinarySignedSubtractProg_exec a b sa sb s hw (by omega) habits hbbits hsa hsb hA hB hSA hSB
  refine ⟨t, u, out, sign, he, ?_, hout, hsign, hsignBit, by omega, hbits, hval⟩
  have hm : max a.length b.length ≤ a.length + b.length := by omega
  omega

/-- Signed binary multiplication has quadratic time in total
supplied bit count and logarithmic machine words. -/
theorem gm06Alg511BinarySignedMultiply_computes :
    ComputesRelInTime gm06Alg511BinarySignedSize gm06Alg511BinarySignedIn
      (gm06Alg511BinarySignedOut (· * ·)) gm06Alg511BinarySignedMultiplyProg (fun n => (n + 1) ^ 2) := by
  apply signed_computes_of_exec (· * ·) gm06Alg511BinarySignedMultiplyProg 510 2 (by decide)
  intro w a b sa sb s hw hsize habits hbbits hsa hsb hA hB hSA hSB
  obtain ⟨t, u, out, sign, he, ht, _, hout, hsign, hsignBit, hlen, hbits, hval⟩ :=
    gm06Alg511BinarySignedMultiplyProg_exec a b sa sb s hw hsize habits hbbits hsa hsb hA hB hSA hSB
  exact ⟨t, u, out, sign, he, ht, hout, hsign, hsignBit, by omega, hbits, hval⟩

/-- Strict signed comparison has linear time in total supplied bit
count and logarithmic words, including both representations of zero. -/
theorem gm06Alg511BinarySignedLess_computes :
    ComputesRelInTime gm06Alg511BinarySignedSize gm06Alg511BinarySignedIn
      (fun x s => s.regs 0 < 2 ∧ (s.regs 0 = 1 ↔ x.1.value < x.2.value))
      gm06Alg511BinarySignedLessProg (fun n => n + 1) := by
  refine ⟨560, 2, by decide, by decide, ?_⟩
  intro x s hs
  have hb := signed_word_bounds x
  obtain ⟨t, u, flag, he, ht, _, hflag, hbit, hiff⟩ := gm06Alg511BinarySignedLessProg_exec
    (x.1.digits.map Bool.toNat) (x.2.digits.map Bool.toNat) x.1.negative.toNat x.2.negative.toNat s
    hb.1 (by simp only [List.length_map]; omega) (supplied_bits _) (supplied_bits _)
    (sign_bit _) (sign_bit _) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  refine ⟨t, u, he, ?_, by simpa only [hflag] using hbit, ?_⟩
  · change u ≤ 560 * (gm06Alg511BinarySignedSize x + 1)
    have hm : max (x.1.digits.map Bool.toNat).length (x.2.digits.map Bool.toNat).length ≤
        gm06Alg511BinarySignedSize x := by simp only [List.length_map, gm06Alg511BinarySignedSize]; omega
    omega
  · simpa only [hflag, gm06Alg511BinarySignedValue_integer] using hiff

end GraphMinor.Compute
