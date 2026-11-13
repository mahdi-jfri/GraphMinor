module

public import GraphMinor.Compute.GM06Alg511WindingInput
public import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

/-!
# Binary integer input for the cylinder feasibility algorithm

The integer target pair and normalized edge turns in VI (5.11),
page 134, can have arbitrarily large magnitudes. Store a sign and
a list of binary digits, with the least significant digit first.
Every digit occupies one word. The finite input length therefore
counts the bits rather than the values of these integers. Decoding
below specifies their meaning and never serves as a RAM arithmetic
operation. Leading zero digits are permitted and still count toward
the supplied input length.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Value of a little-endian digit row. Binary rows have only
zero and one as entries, but the recurrence is defined for all rows. -/
def gm06Alg511BinaryValue : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 2 * gm06Alg511BinaryValue ds

/-- Binary digits of a natural number decode to that number. -/
theorem gm06Alg511BinaryValue_bits (n : ℕ) :
    gm06Alg511BinaryValue (n.bits.map Bool.toNat) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [gm06Alg511BinaryValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn, List.map_cons, gm06Alg511BinaryValue, ih]
    cases b <;> simp [Nat.bit, Nat.add_comm]

/-- A signed integer supplied as a sign and actual binary digits.
A true sign denotes a negative value. Both signs may represent zero. -/
structure GM06Alg511BinaryInteger where
  negative : Bool
  digits : List Bool
  deriving DecidableEq, Repr

/-- The mathematical integer interpreted by a supplied sign/digit pair. -/
def GM06Alg511BinaryInteger.value (z : GM06Alg511BinaryInteger) : ℤ :=
  if z.negative then -(gm06Alg511BinaryValue (z.digits.map Bool.toNat) : ℤ)
  else (gm06Alg511BinaryValue (z.digits.map Bool.toNat) : ℤ)

/-- The integer row has one sign word and one word for each bit. -/
def GM06Alg511BinaryInteger.words (z : GM06Alg511BinaryInteger) : List ℕ :=
  z.negative.toNat :: z.digits.map Bool.toNat

/-- Every integer word is a bit, independently of its magnitude. -/
theorem GM06Alg511BinaryInteger.words_lt_two (z : GM06Alg511BinaryInteger) :
    ∀ d ∈ z.words, d < 2 := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · cases z.negative <;> decide
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
    cases b <;> decide

/-- The row length counts exactly its sign and supplied bits. -/
theorem GM06Alg511BinaryInteger.words_length (z : GM06Alg511BinaryInteger) :
    z.words.length = 1 + z.digits.length := by simp [words, Nat.add_comm]

private theorem bool_toNat_injective : Function.Injective Bool.toNat := by
  intro a b h
  cases a <;> cases b <;> first | rfl | contradiction

/-- The supplied words retain the entire sign and digit list. -/
theorem GM06Alg511BinaryInteger.words_injective : Function.Injective GM06Alg511BinaryInteger.words := by
  intro a b h
  have hh := List.cons.inj h
  have hs := bool_toNat_injective hh.1
  have hd := (List.map_injective_iff.mpr bool_toNat_injective) hh.2
  cases a
  cases b
  cases hs
  cases hd
  rfl

/-- A deterministic binary representation of an integer. It
encodes that integer itself and computes no feasibility information. -/
def GM06Alg511BinaryInteger.ofInt (z : ℤ) : GM06Alg511BinaryInteger :=
  ⟨decide (z < 0), z.natAbs.bits⟩

/-- Every integer has a finite sign/digit representation. -/
theorem GM06Alg511BinaryInteger.value_ofInt (z : ℤ) : (ofInt z).value = z := by
  cases z with
  | ofNat n => simp [ofInt, value, gm06Alg511BinaryValue_bits]
  | negSucc n =>
    simp only [ofInt, value, decide_eq_true (Int.negSucc_lt_zero n), ite_true,
      Int.natAbs_negSucc, gm06Alg511BinaryValue_bits]
    omega

/-- Linkage-free drawing input whose three classes of integer
values are supplied in binary. Rotations contain both cuffs. -/
structure GM06Alg511BinaryInput where
  vertexCount : ℕ
  endpoints : List ℕ
  rotations : List (List ℕ)
  innerCuff : List ℕ
  outerCuff : List ℕ
  pathCount : ℕ
  numerator : GM06Alg511BinaryInteger
  denominator : GM06Alg511BinaryInteger
  edgeTurns : List GM06Alg511BinaryInteger
  deriving DecidableEq, Repr

/-- Interpret the binary integer fields in the existing geometric
input relation. This map is a specification, not a machine decoder. -/
def GM06Alg511BinaryInput.toWindingInput (x : GM06Alg511BinaryInput) : GM06Alg511WindingInput where
  drawing := {
    vertexCount := x.vertexCount
    endpoints := x.endpoints
    rotations := x.rotations
    regionBoundaries := []
    innerCuff := x.innerCuff
    outerCuff := x.outerCuff
    pathCount := x.pathCount
    numerator := x.numerator.value
    denominator := x.denominator.value }
  edgeTurns := x.edgeTurns.map GM06Alg511BinaryInteger.value

/-- All finite fields of the binary input, separated by length
prefixes. Each integer row holds its sign and one word per digit. -/
def GM06Alg511BinaryInput.rows (x : GM06Alg511BinaryInput) : List (List ℕ) :=
  [[x.vertexCount], x.endpoints, gm06EncodeRows x.rotations, x.innerCuff, x.outerCuff,
    [x.pathCount], x.numerator.words, x.denominator.words,
    gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)]

/-- The ordinary machine input, including every supplied integer bit. -/
def GM06Alg511BinaryInput.words (x : GM06Alg511BinaryInput) : List ℕ := gm06EncodeRows x.rows

/-- The binary input words determine all supplied fields. -/
theorem GM06Alg511BinaryInput.words_injective : Function.Injective GM06Alg511BinaryInput.words := by
  intro a b h
  have hh := gm06EncodeRows_injective h
  simp only [rows, List.cons.injEq, and_true] at hh
  obtain ⟨hn, he, hr, hi, ho, hk, hnum, hden, ht⟩ := hh
  have hr' := gm06EncodeRows_injective hr
  have hnum' := GM06Alg511BinaryInteger.words_injective hnum
  have hden' := GM06Alg511BinaryInteger.words_injective hden
  have ht' := (List.map_injective_iff.mpr GM06Alg511BinaryInteger.words_injective)
    (gm06EncodeRows_injective ht)
  cases a
  cases b
  cases hn
  cases he
  cases hr'
  cases hi
  cases ho
  cases hk
  cases hnum'
  cases hden'
  cases ht'
  rfl

/-- Appending a higher digit block shifts it by the lower block's
bit length. This equation is used for shifts and multiplication. -/
theorem gm06Alg511BinaryValue_append (a b : List ℕ) :
    gm06Alg511BinaryValue (a ++ b) = gm06Alg511BinaryValue a + 2 ^ a.length * gm06Alg511BinaryValue b := by
  induction a with
  | nil => simp [gm06Alg511BinaryValue]
  | cons d a ih => simp only [List.cons_append, gm06Alg511BinaryValue, ih, List.length_cons, Nat.pow_succ]; ring

/-- Binary rows have value strictly below two to their digit count.
The number itself is not required to fit in a machine word. -/
theorem gm06Alg511BinaryValue_lt_pow (a : List ℕ) (ha : ∀ d ∈ a, d < 2) :
    gm06Alg511BinaryValue a < 2 ^ a.length := by
  induction a with
  | nil => decide
  | cons d a ih =>
    have hd := ha d (by simp)
    have ht := ih (fun q hq => ha q (by simp [hq]))
    simp only [gm06Alg511BinaryValue, List.length_cons, Nat.pow_succ]
    omega

/-- Fixed-width unsigned addition with one final carry digit.
Missing input positions contain zero. This pure list describes the
rows produced by the digitwise machine loop. -/
def gm06Alg511BinaryAddDigits : ℕ → List ℕ → List ℕ → ℕ → List ℕ
  | 0, _, _, c => [c]
  | n + 1, a, b, c =>
    let v := a.headD 0 + b.headD 0 + c
    (v % 2) :: gm06Alg511BinaryAddDigits n a.tail b.tail (v / 2)

/-- The addition row has its prescribed width and final carry. -/
theorem gm06Alg511BinaryAddDigits_length (n : ℕ) (a b : List ℕ) (c : ℕ) :
    (gm06Alg511BinaryAddDigits n a b c).length = n + 1 := by
  induction n generalizing a b c with
  | zero => rfl
  | succ n ih => simpa only [gm06Alg511BinaryAddDigits, List.length_cons] using congrArg (fun k => k + 1) (ih a.tail b.tail _)

private theorem binary_value_head_tail (a : List ℕ) :
    gm06Alg511BinaryValue a = a.headD 0 + 2 * gm06Alg511BinaryValue a.tail := by
  cases a <;> rfl

/-- The complete addition row decodes to the sum, provided the
fixed width includes both supplied input rows. Values may be large. -/
theorem gm06Alg511BinaryAddDigits_value (n : ℕ) (a b : List ℕ) (c : ℕ)
    (ha : a.length ≤ n) (hb : b.length ≤ n) :
    gm06Alg511BinaryValue (gm06Alg511BinaryAddDigits n a b c) =
      gm06Alg511BinaryValue a + gm06Alg511BinaryValue b + c := by
  induction n generalizing a b c with
  | zero =>
    have haz : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hbz : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst a; subst b
    simp [gm06Alg511BinaryAddDigits, gm06Alg511BinaryValue]
  | succ n ih =>
    have hat : a.tail.length ≤ n := by cases a <;> simp_all
    have hbt : b.tail.length ≤ n := by cases b <;> simp_all
    rw [gm06Alg511BinaryAddDigits, gm06Alg511BinaryValue, ih a.tail b.tail _ hat hbt]
    have hv := Nat.mod_add_div (a.headD 0 + b.headD 0 + c) 2
    rw [binary_value_head_tail a, binary_value_head_tail b]
    omega

private theorem binary_head_lt_two (a : List ℕ) (ha : ∀ d ∈ a, d < 2) : a.headD 0 < 2 := by
  cases a with
  | nil => decide
  | cons d a => exact ha d (by simp)

/-- Adding two binary rows with a single carry yields only binary
digits. In particular, the final carry still occupies one word. -/
theorem gm06Alg511BinaryAddDigits_words (n : ℕ) (a b : List ℕ) (c : ℕ)
    (ha : ∀ d ∈ a, d < 2) (hb : ∀ d ∈ b, d < 2) (hc : c < 2) :
    ∀ d ∈ gm06Alg511BinaryAddDigits n a b c, d < 2 := by
  induction n generalizing a b c with
  | zero => simpa only [gm06Alg511BinaryAddDigits, List.mem_singleton] using fun d (hd : d = c) => hd ▸ hc
  | succ n ih =>
    have ha0 := binary_head_lt_two a ha
    have hb0 := binary_head_lt_two b hb
    have ht : (a.headD 0 + b.headD 0 + c) / 2 < 2 := by omega
    have htail := ih a.tail b.tail _ (fun d hd => ha d (List.mem_of_mem_tail hd))
      (fun d hd => hb d (List.mem_of_mem_tail hd)) ht
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Nat.mod_lt _ (by decide)
    · exact htail d hd

/-- Carry after the requested number of little-endian columns. -/
def gm06Alg511BinaryCarryAfter : List ℕ → List ℕ → ℕ → ℕ → ℕ
  | _, _, c, 0 => c
  | a, b, c, i + 1 => gm06Alg511BinaryCarryAfter a.tail b.tail
      ((a.headD 0 + b.headD 0 + c) / 2) i

/-- Every carry stays a bit, independently of the input magnitude. -/
theorem gm06Alg511BinaryCarryAfter_lt_two (a b : List ℕ) (c i : ℕ)
    (ha : ∀ d ∈ a, d < 2) (hb : ∀ d ∈ b, d < 2) (hc : c < 2) :
    gm06Alg511BinaryCarryAfter a b c i < 2 := by
  induction i generalizing a b c with
  | zero => exact hc
  | succ i ih =>
    have ha0 := binary_head_lt_two a ha
    have hb0 := binary_head_lt_two b hb
    exact ih a.tail b.tail _ (fun d hd => ha d (List.mem_of_mem_tail hd))
      (fun d hd => hb d (List.mem_of_mem_tail hd)) (by omega)

private theorem digit_tail (a : List ℕ) (i : ℕ) : a.tail.getD i 0 = a.getD (i + 1) 0 := by
  cases a <;> rfl

private theorem digit_head (a : List ℕ) : a.headD 0 = a.getD 0 0 := by
  cases a <;> rfl

private theorem drop_tail (a : List ℕ) (i : ℕ) : a.tail.drop i = a.drop (i + 1) := by
  cases a <;> simp

private theorem head_drop (a : List ℕ) (i : ℕ) : (a.drop i).headD 0 = a.getD i 0 := by
  induction i generalizing a with
  | zero => exact digit_head a
  | succ i ih => cases a with
    | nil => rfl
    | cons d a => exact ih a

/-- The next carry depends only on the two current digit words
and the previous one-bit carry. -/
theorem gm06Alg511BinaryCarryAfter_succ (a b : List ℕ) (c i : ℕ) :
    gm06Alg511BinaryCarryAfter a b c (i + 1) =
      (a.getD i 0 + b.getD i 0 + gm06Alg511BinaryCarryAfter a b c i) / 2 := by
  induction i generalizing a b c with
  | zero => simp only [gm06Alg511BinaryCarryAfter, digit_head]
  | succ i ih =>
    simpa only [gm06Alg511BinaryCarryAfter, digit_tail] using
      ih a.tail b.tail ((a.headD 0 + b.headD 0 + c) / 2)

/-- After dropping completed columns, the addition row is the
addition of the remaining input tails with the computed carry. -/
theorem gm06Alg511BinaryAddDigits_drop (n i : ℕ) (a b : List ℕ) (c : ℕ) (hi : i ≤ n) :
    (gm06Alg511BinaryAddDigits n a b c).drop i =
      gm06Alg511BinaryAddDigits (n - i) (a.drop i) (b.drop i) (gm06Alg511BinaryCarryAfter a b c i) := by
  induction i generalizing n a b c with
  | zero => simp only [List.drop_zero, Nat.sub_zero, gm06Alg511BinaryCarryAfter]
  | succ i ih =>
    cases n with
    | zero => omega
    | succ n =>
      simpa only [gm06Alg511BinaryAddDigits, List.drop_succ_cons, Nat.add_sub_add_right,
        gm06Alg511BinaryCarryAfter, drop_tail] using
        ih n a.tail b.tail ((a.headD 0 + b.headD 0 + c) / 2) (by omega)

/-- The word stored at a nonfinal column is the sum modulo two.
This identifies each RAM write with the complete addition row. -/
theorem gm06Alg511BinaryAddDigits_digit (n i : ℕ) (a b : List ℕ) (c : ℕ) (hi : i < n) :
    (gm06Alg511BinaryAddDigits n a b c).getD i 0 =
      (a.getD i 0 + b.getD i 0 + gm06Alg511BinaryCarryAfter a b c i) % 2 := by
  have hh := congrArg (fun xs : List ℕ => xs.headD 0) (gm06Alg511BinaryAddDigits_drop n i a b c (by omega))
  rw [head_drop] at hh
  have hrem : n - i = (n - i - 1) + 1 := by omega
  rw [hrem, gm06Alg511BinaryAddDigits] at hh
  change (gm06Alg511BinaryAddDigits n a b c).getD i 0 =
    ((a.drop i).headD 0 + (b.drop i).headD 0 + gm06Alg511BinaryCarryAfter a b c i) % 2 at hh
  simpa only [head_drop] using hh

/-- The final column is precisely the remaining one-bit carry. -/
theorem gm06Alg511BinaryAddDigits_final (n : ℕ) (a b : List ℕ) (c : ℕ) :
    (gm06Alg511BinaryAddDigits n a b c).getD n 0 = gm06Alg511BinaryCarryAfter a b c n := by
  have hh := congrArg (fun xs : List ℕ => xs.headD 0) (gm06Alg511BinaryAddDigits_drop n n a b c le_rfl)
  simpa only [head_drop, Nat.sub_self, gm06Alg511BinaryAddDigits, List.headD_cons] using hh

end GraphMinor.Compute
