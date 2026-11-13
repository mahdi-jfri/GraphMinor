module

public import GraphMinor.Compute.GM06Alg511BinaryAdd
public import GraphMinor.Compute.TwoPathsRotate
import Mathlib.Tactic

/-!
# Fixed-width complement for binary subtraction

Subtracting digit rows uses the complement of the second operand
and the adder's initial carry. Choose a width containing both
operands. Missing high digits are zero and their complements are
one. The complement row and the original operand sum to one less
than two to that width. The RAM program operates only on individual
bits and counters, and its running time is linear in the width.
This is arithmetic for the integer inputs of VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Invert the zero-extended digits through the prescribed width. -/
def gm06Alg511BinaryComplementDigits (n : ℕ) (b : List ℕ) : List ℕ :=
  (List.range n).map (fun i => 1 - b.getD i 0)

/-- The complement contains exactly the prescribed number of bits. -/
theorem gm06Alg511BinaryComplementDigits_length (n : ℕ) (b : List ℕ) :
    (gm06Alg511BinaryComplementDigits n b).length = n := by simp [gm06Alg511BinaryComplementDigits]

/-- Every complemented digit is a bit. -/
theorem gm06Alg511BinaryComplementDigits_words (n : ℕ) (b : List ℕ) :
    ∀ d ∈ gm06Alg511BinaryComplementDigits n b, d < 2 := by
  intro d hd
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
  omega

private theorem complement_cons (n : ℕ) (b : List ℕ) :
    gm06Alg511BinaryComplementDigits (n + 1) b =
      (1 - b.headD 0) :: gm06Alg511BinaryComplementDigits n b.tail := by
  rw [gm06Alg511BinaryComplementDigits, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · cases b <;> rfl
  · apply List.map_congr_left
    intro i hi
    cases b <;> rfl

/-- The exact fixed-width complement identity includes all zero
padding, and never assumes the represented integer fits a word. -/
theorem gm06Alg511BinaryComplementDigits_value (n : ℕ) (b : List ℕ)
    (hb : b.length ≤ n) (hbits : ∀ d ∈ b, d < 2) :
    gm06Alg511BinaryValue (gm06Alg511BinaryComplementDigits n b) +
      gm06Alg511BinaryValue b + 1 = 2 ^ n := by
  induction n generalizing b with
  | zero =>
    have he : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst b
    rfl
  | succ n ih =>
    have hbt : b.tail.length ≤ n := by cases b <;> simp_all
    have ht := ih b.tail hbt (fun d hd => hbits d (List.mem_of_mem_tail hd))
    have hhead : b.headD 0 < 2 := by cases b with
      | nil => decide
      | cons d b => exact hbits d (by simp)
    have hbal : 1 - b.headD 0 + b.headD 0 = 1 := Nat.sub_add_cancel (by omega)
    have hvalue : gm06Alg511BinaryValue b = b.headD 0 + 2 * gm06Alg511BinaryValue b.tail := by cases b <;> rfl
    rw [complement_cons, gm06Alg511BinaryValue, hvalue, Nat.pow_succ]
    omega

/-- Read a bit, with zero beyond the row, and store its complement. -/
def gm06Alg511BinaryComplementBody : Cmd :=
  .seq (gm06Alg511LoadBinaryDigitProg 2001 2104)
    (.write 2003 (.reg 2100) (.op .sub (.const 1) (.reg 2104)))

/-- Build the fixed-width complement of array 2001 in array 2003.
Register 2230 supplies the width and is preserved. -/
def gm06Alg511BinaryComplementProg : Cmd :=
  .seq (.alloc 2003 (.reg 2230))
    (.seq (.assign 2100 (.const 0))
      (forUp 2100 (.reg 2230) gm06Alg511BinaryComplementBody))

private theorem complement_body_exec {w : ℕ} (b out : List ℕ) (i : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hi : i < 2 ^ w) (hb : b.length < 2 ^ w)
    (hbits : ∀ d ∈ b, d < 2) (houti : i < out.length)
    (hB : s.arrs 2001 = b) (hO : s.arrs 2003 = out) (hindex : s.regs 2100 = i) :
    ∃ t u, Exec w gm06Alg511BinaryComplementBody s t u ∧ u ≤ 11 ∧
      Keeps [2104] [2003] s t ∧ t.arrs 2003 = out.set i (1 - b.getD i 0) := by
  obtain ⟨s₁, u₁, he₁, ht₁, hd₁, hk₁⟩ := gm06Alg511LoadBinaryDigitProg_exec 2001 2104 b s i
    hw hi hb hbits hB hindex
  let t := s₁.writeArr 2003 i (1 - b.getD i 0)
  have hdigit : b.getD i 0 < 2 ^ w := by
    by_cases hil : i < b.length
    · simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some] using
        (hbits b[i] (List.getElem_mem hil)).trans_le (by omega : 2 ≤ 2 ^ w)
    · simp [List.getD_eq_getElem?_getD, hil]
  have hwrite : Exec w (.write 2003 (.reg 2100) (.op .sub (.const 1) (.reg 2104))) s₁ t 5 :=
    .write (Crossing.eval_reg ((hk₁.1 2100 (by decide)).trans hindex) hi)
      (Crossing.eval_sub (Crossing.eval_const hw) (Crossing.eval_reg hd₁ hdigit))
      (by rw [hk₁.2 2003 (by simp), hO]; exact houti)
  refine ⟨t, u₁ + 5, .seq he₁ hwrite, by omega,
    (hk₁.mono (by simp) (by simp)).writeArr (by simp) _ _, ?_⟩
  simp only [t, State.writeArr, State.setArr_arrs_self, hk₁.2 2003 (by simp), hO]

/-- The zero-extended complement executes in linear time in its
width, retains the operand and all unrelated state, and computes
the exact supplied digit-row specification. -/
theorem gm06Alg511BinaryComplementProg_exec {w : ℕ} (n : ℕ) (b : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hb : b.length < 2 ^ w)
    (hbits : ∀ d ∈ b, d < 2) (hB : s.arrs 2001 = b) (hwidth : s.regs 2230 = n) :
    ∃ t u, Exec w gm06Alg511BinaryComplementProg s t u ∧ u ≤ 10 + 20 * n ∧
      Keeps [2100, 2104] [2003] s t ∧ t.arrs 2003 = gm06Alg511BinaryComplementDigits n b := by
  let f := fun i => 1 - b.getD i 0
  let s₁ := s.setArr 2003 (List.replicate n 0)
  let s₂ := s₁.setReg 2100 0
  have he₁ : Exec w (.alloc 2003 (.reg 2230)) s s₁ (n + 1) := by
    simpa only [Expr.cost, Nat.add_comm] using Exec.alloc (a := 2003) (Crossing.eval_reg hwidth hn)
  have he₂ : Exec w (.assign 2100 (.const 0)) s₁ s₂ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  let I : ℕ → State → Prop := fun i st => st.regs 2100 = i ∧ st.regs 2230 = n ∧
    st.arrs 2001 = b ∧ st.arrs 2003 = (List.range i).map f ++ List.replicate (n - i) 0 ∧
      Keeps [2100, 2104] [2003] s st
  have hk₂ : Keeps [2100, 2104] [2003] s s₂ :=
    ((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _
  have hI : I 0 s₂ := by
    refine ⟨by simp [s₂], (hk₂.1 2230 (by decide)).trans hwidth,
      (hk₂.2 2001 (by decide)).trans hB, ?_, hk₂⟩
    simp [s₂, s₁]
  obtain ⟨t, u, he, ht, hI'⟩ := Crossing.forUp_exec' I n 11 (r_i := 2100)
    (hi := .reg 2230) (body := gm06Alg511BinaryComplementBody) hw hn
    (fun i hi st h => ⟨h.1, Crossing.eval_reg h.2.1 hn⟩)
    (by
      intro i hi st h
      obtain ⟨hidx, hwidthst, hbSt, hoSt, hkeep⟩ := h
      have hlen : ((List.range i).map f ++ List.replicate (n - i) 0).length = n := by
        simp only [List.length_append, List.length_map, List.length_range, List.length_replicate]
        omega
      obtain ⟨su, tu, heu, htu, hku, hou⟩ := complement_body_exec b _ i st hw (hi.trans hn) hb hbits
        (by rw [hlen]; exact hi) hbSt hoSt hidx
      have htot := (hkeep.trans hku (by simp) (by simp)).setReg (show 2100 ∈ [2100, 2104] by simp) (i + 1)
      refine ⟨su, tu, heu, htu, ?_, (hku.1 2100 (by decide)).trans hidx⟩
      refine ⟨by simp, (htot.1 2230 (by decide)).trans hwidth,
        (htot.2 2001 (by decide)).trans hB, ?_, htot⟩
      change su.arrs 2003 = ((List.range i).map f ++ List.replicate (n - i) 0).set i (f i) at hou
      rw [set_range_map f hi] at hou
      exact hou) s₂ hI
  refine ⟨t, n + 1 + (2 + u), .seq he₁ (.seq he₂ he), ?_, hI'.2.2.2.2, ?_⟩
  · simp only [Expr.cost] at ht
    omega
  · simpa only [Nat.sub_self, List.replicate_zero, List.append_nil, gm06Alg511BinaryComplementDigits] using hI'.2.2.2.1

/-- Addition of the complemented subtrahend with initial carry
one. The final digit records whether unsigned subtraction borrows. -/
def gm06Alg511BinarySubtractColumns (n : ℕ) (a b : List ℕ) : List ℕ :=
  gm06Alg511BinaryAddDigits n a (gm06Alg511BinaryComplementDigits n b) 1

/-- A zero final carry is the borrow case of the subtraction pass. -/
def gm06Alg511BinarySubtractBorrow (n : ℕ) (a b : List ℕ) : ℕ :=
  1 - gm06Alg511BinaryCarryAfter a (gm06Alg511BinaryComplementDigits n b) 1 n

/-- The low subtraction columns and borrow satisfy the exact
integer subtraction identity, including the underflow case. -/
theorem gm06Alg511BinarySubtractColumns_balance (n : ℕ) (a b : List ℕ)
    (ha : a.length ≤ n) (hb : b.length ≤ n)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) :
    gm06Alg511BinaryValue ((gm06Alg511BinarySubtractColumns n a b).take n) + gm06Alg511BinaryValue b =
      gm06Alg511BinaryValue a + 2 ^ n * gm06Alg511BinarySubtractBorrow n a b := by
  let c := gm06Alg511BinaryComplementDigits n b
  let z := gm06Alg511BinarySubtractColumns n a b
  let q := gm06Alg511BinaryCarryAfter a c 1 n
  have hc : c.length = n := gm06Alg511BinaryComplementDigits_length n b
  have hcbits := gm06Alg511BinaryComplementDigits_words n b
  have hq : q < 2 := gm06Alg511BinaryCarryAfter_lt_two a c 1 n habits hcbits (by decide)
  have hsum : gm06Alg511BinaryValue z = gm06Alg511BinaryValue a + gm06Alg511BinaryValue c + 1 :=
    gm06Alg511BinaryAddDigits_value n a c 1 ha hc.le
  have hcomp := gm06Alg511BinaryComplementDigits_value n b hb hbbits
  have hbal : gm06Alg511BinaryValue z + gm06Alg511BinaryValue b = gm06Alg511BinaryValue a + 2 ^ n := by
    dsimp only [c] at hsum
    omega
  have hzlen : z.length = n + 1 := gm06Alg511BinaryAddDigits_length n a c 1
  have htake : (z.take n).length = n := by simp only [List.length_take, hzlen]; omega
  have hdrop : z.drop n = [q] := by
    change (gm06Alg511BinaryAddDigits n a c 1).drop n = [q]
    rw [gm06Alg511BinaryAddDigits_drop n n a c 1 le_rfl, Nat.sub_self, gm06Alg511BinaryAddDigits]
  have hz := gm06Alg511BinaryValue_append (z.take n) (z.drop n)
  rw [List.take_append_drop, htake, hdrop, gm06Alg511BinaryValue, gm06Alg511BinaryValue,
    Nat.mul_zero, Nat.add_zero] at hz
  rw [hz] at hbal
  change gm06Alg511BinaryValue (z.take n) + gm06Alg511BinaryValue b =
    gm06Alg511BinaryValue a + 2 ^ n * (1 - q)
  have hcases : q = 0 ∨ q = 1 := by omega
  rcases hcases with hzero | hone
  · rw [hzero] at hbal ⊢
    simp only [Nat.mul_zero, Nat.mul_one, Nat.sub_zero, Nat.add_zero] at hbal ⊢
    exact hbal
  · rw [hone] at hbal ⊢
    simp only [Nat.mul_one, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hbal ⊢
    omega

/-- The borrow bit is exactly strict comparison of the two
unsigned inputs. All sizes are measured by their digit widths. -/
theorem gm06Alg511BinarySubtractBorrow_eq_one_iff (n : ℕ) (a b : List ℕ)
    (ha : a.length ≤ n) (hb : b.length ≤ n)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) :
    gm06Alg511BinarySubtractBorrow n a b = 1 ↔ gm06Alg511BinaryValue a < gm06Alg511BinaryValue b := by
  let z := gm06Alg511BinarySubtractColumns n a b
  have hbits : ∀ d ∈ z.take n, d < 2 := by
    intro d hd
    exact gm06Alg511BinaryAddDigits_words n a _ 1 habits
      (gm06Alg511BinaryComplementDigits_words n b) (by decide) d (List.mem_of_mem_take hd)
  have hlen : (z.take n).length = n := by
    simp only [List.length_take, z, gm06Alg511BinarySubtractColumns, gm06Alg511BinaryAddDigits_length]
    omega
  have hlow := gm06Alg511BinaryValue_lt_pow (z.take n) hbits
  rw [hlen] at hlow
  have hbal := gm06Alg511BinarySubtractColumns_balance n a b ha hb habits hbbits
  have hborrow : gm06Alg511BinarySubtractBorrow n a b < 2 := by
    unfold gm06Alg511BinarySubtractBorrow
    omega
  have hcases : gm06Alg511BinarySubtractBorrow n a b = 0 ∨ gm06Alg511BinarySubtractBorrow n a b = 1 := by omega
  rcases hcases with hzero | hone
  · rw [hzero, Nat.mul_zero, Nat.add_zero] at hbal
    rw [hzero]
    change gm06Alg511BinaryValue (z.take n) + _ = _ at hbal
    omega
  · rw [hone, Nat.mul_one] at hbal
    rw [hone]
    change gm06Alg511BinaryValue (z.take n) + _ = _ at hbal
    omega

end GraphMinor.Compute
