module

public import GraphMinor.Compute.GM06Alg511BinaryAdd
public import GraphMinor.Compute.GM06Alg511CopyRow
public import GraphMinor.Compute.GM06SpliceRotations
import Mathlib.Tactic

/-!
# A shifted-addition pass for binary multiplication

Unsigned multiplication scans the first operand's bits. At a set
bit, shift the second operand by the column index and add it to the
digit-array accumulator. A shift prepends zero digits. All additions
use the verified binary adder. The accumulator's length grows by
at most one beyond the shifted operand's width. Every machine word
holds only a bit, a carry, a length or an array position. This is the
arithmetic layer for VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

private theorem value_zero_digits (n : ℕ) : gm06Alg511BinaryValue (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, gm06Alg511BinaryValue, ih]

/-- Prepending zero digits multiplies the interpreted number by
a power of two without ever computing that number in a register. -/
theorem gm06Alg511BinaryValue_shift (n : ℕ) (b : List ℕ) :
    gm06Alg511BinaryValue (List.replicate n 0 ++ b) = 2 ^ n * gm06Alg511BinaryValue b := by
  rw [gm06Alg511BinaryValue_append, value_zero_digits, List.length_replicate, Nat.zero_add]

/-- The next lower-prefix value adds exactly the current bit's
place value. This is the multiplication loop's arithmetic invariant. -/
theorem gm06Alg511BinaryValue_take_succ (a : List ℕ) (i : ℕ) (hi : i < a.length) :
    gm06Alg511BinaryValue (a.take (i + 1)) = gm06Alg511BinaryValue (a.take i) + 2 ^ i * a[i] := by
  rw [List.take_succ_eq_append_getElem hi, gm06Alg511BinaryValue_append,
    List.length_take_of_le hi.le]
  simp only [gm06Alg511BinaryValue, Nat.mul_zero, Nat.add_zero]

/-- Shift the retained second operand into the adder's input row.
Register 2233 contains the shift and remains unchanged. -/
def gm06Alg511BinaryShiftOperandProg : Cmd :=
  .seq (.alloc 2001 (.op .add (.reg 2233) (.len 2301)))
    (gm06RotationSliceProg 2301 2001 (.len 2301) (.const 0) (.reg 2233))

/-- The actual shifted row is computed in linear time, with the
retained operand and shift register preserved. -/
theorem gm06Alg511BinaryShiftOperandProg_exec {w : ℕ} (b : List ℕ) (i : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hsize : i + b.length < 2 ^ w)
    (hbits : ∀ d ∈ b, d < 2) (hB : s.arrs 2301 = b) (hindex : s.regs 2233 = i) :
    ∃ t u, Exec w gm06Alg511BinaryShiftOperandProg s t u ∧ u ≤ 8 + i + 16 * b.length ∧
      Keeps [313] [2001] s t ∧ t.arrs 2001 = List.replicate i 0 ++ b := by
  have hi : i < 2 ^ w := by omega
  have hb : b.length < 2 ^ w := by omega
  let s₁ := s.setArr 2001 (List.replicate (i + b.length) 0)
  have he₁ : Exec w (.alloc 2001 (.op .add (.reg 2233) (.len 2301))) s s₁ (3 + (i + b.length)) :=
    .alloc (Crossing.eval_add (Crossing.eval_reg hindex hi) (Crossing.eval_len hB hb) hsize)
  have hk₁ : Keeps [313] [2001] s s₁ := (Keeps.refl _ _ s).setArr (by simp) _
  obtain ⟨t, u, he, ht, hk, hout⟩ := gm06RotationSliceProg_exec 2301 2001 (by decide)
    (.len 2301) (.const 0) (.reg 2233) b (List.replicate i 0) 0 b.length b.length s₁ hw hb
    (by omega) (fun d hd => (hbits d hd).trans_le (by omega)) le_rfl
    (by simpa only [List.length_replicate] using hsize) hB
    (by simp only [s₁, State.setArr_arrs_self]; rw [List.replicate_add])
    (fun st hk => Crossing.eval_len ((hk.2 2301 (by decide)).trans hB) hb)
    (fun st hk => Crossing.eval_const (Nat.two_pow_pos w))
    (fun st hk => by simpa only [List.length_replicate] using
      Crossing.eval_reg ((hk.1 2233 (by decide)).trans (by simpa [s₁] using hindex)) hi)
  refine ⟨t, 3 + (i + b.length) + u, .seq he₁ he, ?_, hk₁.trans hk (by simp) (by simp), ?_⟩
  · simp only [Expr.cost] at ht
    omega
  · simpa only [List.drop_zero, List.take_length, Nat.sub_self, List.replicate_zero,
      List.append_nil] using hout

/-- A set-bit multiplication pass adds the shifted retained second
operand to the accumulator, and stores the new accumulator. -/
def gm06Alg511BinaryMultiplyPassProg : Cmd :=
  .seq (gm06Alg511CopyRowProg 2302 2000)
    (.seq gm06Alg511BinaryShiftOperandProg
      (.seq gm06Alg511BinaryAddProg (gm06Alg511CopyRowProg 2002 2302)))

private theorem multiply_pass_frame {w : ℕ} {s t : State} {u : ℕ}
    (he : Exec w gm06Alg511BinaryMultiplyPassProg s t u) :
    Keeps [20, 313, 2100, 2101, 2102, 2103, 2104, 2105] [2000, 2001, 2002, 2302] s t := by
  have hr : gm06Alg511BinaryMultiplyPassProg.writtenRegs ⊆
      ([20, 313, 2100, 2101, 2102, 2103, 2104, 2105] : List ℕ).toFinset := by decide
  have ha : gm06Alg511BinaryMultiplyPassProg.writtenArrs ⊆
      ([2000, 2001, 2002, 2302] : List ℕ).toFinset := by decide
  exact ⟨fun r hn => he.regs_eq_of_not_mem_writtenRegs (fun hm => hn (List.mem_toFinset.mp (hr hm))),
    fun a hn => he.arrs_eq_of_not_mem_writtenArrs (fun hm => hn (List.mem_toFinset.mp (ha hm)))⟩

/-- One actual shifted-addition pass has a linear cost in the
current column and retained operand width. It returns a binary
accumulator for the exact sum and proves its next width bound. -/
theorem gm06Alg511BinaryMultiplyPassProg_exec {w : ℕ} (b acc : List ℕ) (i : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : i + b.length + 1 < 2 ^ w)
    (haccLen : acc.length ≤ i + b.length)
    (hbits : ∀ d ∈ b, d < 2) (haccBits : ∀ d ∈ acc, d < 2)
    (hB : s.arrs 2301 = b) (hAcc : s.arrs 2302 = acc) (hindex : s.regs 2233 = i) :
    ∃ t u out, Exec w gm06Alg511BinaryMultiplyPassProg s t u ∧
      u ≤ 100 + 100 * (i + b.length + 1) ∧
      Keeps [20, 313, 2100, 2101, 2102, 2103, 2104, 2105] [2000, 2001, 2002, 2302] s t ∧
      t.arrs 2302 = out ∧ out.length ≤ i + b.length + 1 ∧
      (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinaryValue out = gm06Alg511BinaryValue acc + 2 ^ i * gm06Alg511BinaryValue b := by
  let shifted := List.replicate i 0 ++ b
  have hshiftLen : shifted.length = i + b.length := by simp [shifted]
  have hshiftBits : ∀ d ∈ shifted, d < 2 := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · have hz := List.eq_of_mem_replicate hd
      subst d
      decide
    · exact hbits d hd
  have haccFit : acc.length < 2 ^ w := by omega
  have haccWords : ∀ d ∈ acc, d < 2 ^ w := fun d hd => (haccBits d hd).trans_le (by omega)
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hA₁⟩ := gm06Alg511CopyRowProg_exec 2302 2000 (by decide) acc s
    (by omega) haccFit haccWords hAcc
  obtain ⟨s₂, u₂, he₂, ht₂, hk₂, hB₂⟩ := gm06Alg511BinaryShiftOperandProg_exec (w := w) b i s₁ (by omega)
    (by omega) hbits ((hk₁.2 2301 (by decide)).trans hB) ((hk₁.1 2233 (by decide)).trans hindex)
  have hmax : max acc.length shifted.length ≤ i + b.length := by rw [hshiftLen]; omega
  obtain ⟨s₃, u₃, he₃, ht₃, hk₃, hsum⟩ := gm06Alg511BinaryAddProg_exec acc shifted s₂ hw
    (by omega) haccBits hshiftBits ((hk₂.2 2000 (by decide)).trans hA₁) hB₂
  let out := gm06Alg511BinaryAddDigits (max acc.length shifted.length) acc shifted 0
  have houtLen : out.length = max acc.length shifted.length + 1 := gm06Alg511BinaryAddDigits_length _ _ _ _
  have houtFit : out.length < 2 ^ w := by omega
  have houtBits : ∀ d ∈ out, d < 2 := gm06Alg511BinaryAddDigits_words _ acc shifted 0 haccBits hshiftBits (by decide)
  obtain ⟨t, u₄, he₄, ht₄, hk₄, hout⟩ := gm06Alg511CopyRowProg_exec 2002 2302 (by decide) out s₃
    (by omega) houtFit (fun d hd => (houtBits d hd).trans_le (by omega)) hsum
  have he : Exec w gm06Alg511BinaryMultiplyPassProg s t (u₁ + (u₂ + (u₃ + u₄))) :=
    .seq he₁ (.seq he₂ (.seq he₃ he₄))
  refine ⟨t, _, out, he, by omega, multiply_pass_frame he, hout, by omega, houtBits, ?_⟩
  have hval := gm06Alg511BinaryAddDigits_value (max acc.length shifted.length) acc shifted 0
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  simpa only [Nat.add_zero, shifted, gm06Alg511BinaryValue_shift] using hval

end GraphMinor.Compute
