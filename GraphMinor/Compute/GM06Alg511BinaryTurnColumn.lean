module

public import GraphMinor.Compute.GM06Alg511BinaryRowArithmetic
public import GraphMinor.Compute.GM06Alg511SelectField
import GraphMinor.Compute.CrossingOpsCycleTest
import GraphMinor.Compute.CrossingOpsReplLists
import Mathlib.Tactic

/-!
# Adding one supplied binary edge turn

For each dart of the first linkage path, select its edge's supplied
sign/digit row. Reverse the sign when the dart traverses the edge
backwards, then add the row to the retained binary turn sum. The
selection reads only the supplied edge index, and sign reversal
changes only one bit. The addition is the verified signed-row
program. No interpreted edge-turn magnitude occupies a word.
This is the winding computation in VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

private theorem flip_sign_value (sign : ℕ) (digits : List ℕ) (hs : sign < 2) :
    gm06Alg511BinarySignedValue (1 - sign) digits = -gm06Alg511BinarySignedValue sign digits := by
  interval_cases sign <;> simp [gm06Alg511BinarySignedValue]

/-- Negate a supplied binary row by replacing only its sign bit. -/
def gm06Alg511NegateBinaryRowProg (row : ℕ) : Cmd :=
  .write row (.const 0) (.op .sub (.const 1) (.read row (.const 0)))

private theorem negate_row_exec {w : ℕ} (row sign : ℕ) (digits : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hsign : sign < 2) (ha : s.arrs row = sign :: digits) :
    Exec w (gm06Alg511NegateBinaryRowProg row) s (s.writeArr row 0 (1 - sign)) 6 := by
  have hsf : sign < 2 ^ w := hsign.trans_le (by omega)
  have hread : (Expr.read row (.const 0)).eval w s = some sign := by
    exact (Crossing.eval_read (a := row) (Crossing.eval_const (Nat.two_pow_pos w))
      (by rw [ha]; exact Nat.zero_lt_succ _) (by simpa only [ha, List.getElem_cons_zero] using hsf)).trans (by simp [ha])
  exact .write (Crossing.eval_const (Nat.two_pow_pos w))
    (Crossing.eval_sub (Crossing.eval_const hw) hread) (by rw [ha]; exact Nat.zero_lt_succ _)

/-- An odd ordinary dart reverses its edge's supplied parameter. -/
def gm06Alg511OrientBinaryTurnProg : Cmd :=
  .ite (.op .mod (.reg 2911) (.const 2)) (gm06Alg511NegateBinaryRowProg 2901) .skip

/-- The actual orientation command changes precisely the sign
required by the dart, with constant cost and unchanged digits. -/
theorem gm06Alg511OrientBinaryTurnProg_exec {w : ℕ} (dart sign : ℕ) (digits : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hdart : dart < 2 ^ w) (hsign : sign < 2)
    (hr : s.regs 2911 = dart) (ha : s.arrs 2901 = sign :: digits) :
    ∃ t u sign', Exec w gm06Alg511OrientBinaryTurnProg s t u ∧ u ≤ 9 ∧
      Keeps [] [2901] s t ∧ t.arrs 2901 = sign' :: digits ∧ sign' < 2 ∧
      gm06Alg511BinaryRowValue (sign' :: digits) =
        if dart % 2 = 0 then gm06Alg511BinaryRowValue (sign :: digits)
        else -gm06Alg511BinaryRowValue (sign :: digits) := by
  have hmod := Crossing.eval_mod (Crossing.eval_reg hr hdart) (Crossing.eval_const hw) (by decide : 0 < 2)
  by_cases hz : dart % 2 = 0
  · refine ⟨s, 4, sign, .ite_false (by simpa only [hz] using hmod) (.skip _), by decide,
      Keeps.refl _ _ s, ha, hsign, ?_⟩
    simp only [hz, ite_true]
  · let t := s.writeArr 2901 0 (1 - sign)
    have he := negate_row_exec 2901 sign digits s (by omega : 1 < 2 ^ w) hsign ha
    refine ⟨t, 3 + 6, 1 - sign, .ite_true hmod hz he, le_rfl,
      (Keeps.refl _ _ s).writeArr (by simp) _ _, ?_, by omega, ?_⟩
    · change (s.arrs 2901).set 0 (1 - sign) = _
      rw [ha]; rfl
    · simpa only [hz, ite_false, gm06Alg511BinaryRowValue, List.headD_cons, List.tail_cons] using flip_sign_value sign digits hsign

/-- Select the supplied edge turn and add its oriented value to
the retained accumulator row. Register 2911 holds the ordinary dart. -/
def gm06Alg511BinaryTurnColumnProg : Cmd :=
  .seq (.assign 31 (.op .div (.reg 2911) (.const 2)))
    (.seq (gm06SelectRowProg 2900 2901)
      (.seq gm06Alg511OrientBinaryTurnProg (gm06Alg511BinaryRowAddProg 2902 2901 2902)))

/-- One actual turn column selects the supplied binary integer,
uses the dart's direction, and returns the exact updated signed sum
with a digit-count width bound and polynomial selection/addition cost. -/
theorem gm06Alg511BinaryTurnColumnProg_exec {w : ℕ} (turns : List GM06Alg511BinaryInteger)
    (dart sign : ℕ) (acc : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hdart : dart < 2 ^ w) (hd : dart < 2 * turns.length)
    (hsize : acc.length + (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 2 < 2 ^ w)
    (hwords : ∀ d ∈ gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words), d < 2 ^ w)
    (hsign : sign < 2) (hbits : ∀ d ∈ acc, d < 2)
    (hTurns : s.arrs 2900 = gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words))
    (hAcc : s.arrs 2902 = sign :: acc) (hDart : s.regs 2911 = dart) :
    ∃ t u out sign', Exec w gm06Alg511BinaryTurnColumnProg s t u ∧
      u ≤ 450 + 17 * (dart / 2) + 22 * (turns[dart / 2]'(by omega)).words.length +
        350 * (acc.length + (turns[dart / 2]'(by omega)).digits.length + 1) ∧
      Keeps [0, 7, 8, 9, 11, 20, 31, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2400, 2401, 2402, 2404]
        [2000, 2001, 2002, 2003, 2004, 2005, 2901, 2902] s t ∧
      t.arrs 2902 = sign' :: out ∧ sign' < 2 ∧
      out.length ≤ max acc.length (turns[dart / 2]'(by omega)).digits.length + 1 ∧
      (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinaryRowValue (sign' :: out) = gm06Alg511BinaryRowValue (sign :: acc) +
        (if dart % 2 = 0 then (turns[dart / 2]'(by omega)).value else -(turns[dart / 2]'(by omega)).value) := by
  let index := dart / 2
  have hi : index < turns.length := by dsimp only [index]; omega
  let z := turns[index]
  let rows := turns.map GM06Alg511BinaryInteger.words
  change acc.length + (gm06EncodeRows rows).length + 2 < 2 ^ w at hsize
  have hri : index < rows.length := by simpa only [rows, List.length_map] using hi
  have hrow : rows[index] = z.words := List.getElem_map _
  have hzi : z.words ∈ rows := by rw [← hrow]; exact List.getElem_mem (by simpa only [rows, List.length_map] using hi)
  have hzLen := gm06Alg511_encoded_row_length_le hzi
  have hzDigits : z.digits.length + 1 ≤ (gm06EncodeRows rows).length := by
    rw [GM06Alg511BinaryInteger.words_length] at hzLen
    omega
  have hzSign : z.negative.toNat < 2 := by cases z.negative <;> decide
  have hzBits : ∀ d ∈ z.digits.map Bool.toNat, d < 2 := by
    intro d hd
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
    cases b <;> decide
  let s₁ := s.setReg 31 index
  have he₁ : Exec w (.assign 31 (.op .div (.reg 2911) (.const 2))) s s₁ 4 :=
    .assign (Crossing.eval_div (Crossing.eval_reg hDart hdart) (Crossing.eval_const (by omega))
      (by decide) ((Nat.div_le_self dart 2).trans_lt hdart))
  obtain ⟨s₂, u₂, he₂, ht₂, hturn₂, _, _, hk₂⟩ := gm06SelectRowProg_exec (w := w) 2900 2901 (by decide) rows index
    (by simpa only [rows, List.length_map] using hi) s₁ (by omega) hTurns (by omega) hwords (by simp [s₁])
  have hturn₂' : s₂.arrs 2901 = z.negative.toNat :: z.digits.map Bool.toNat := hturn₂.trans hrow
  obtain ⟨s₃, u₃, oriented, he₃, ht₃, hk₃, hturn₃, hsign₃, hval₃⟩ :=
    gm06Alg511OrientBinaryTurnProg_exec (w := w) dart z.negative.toNat (z.digits.map Bool.toNat) s₂
      (by omega) hdart hzSign ((hk₂.1 2911 (by decide)).trans (by simpa [s₁] using hDart)) hturn₂'
  have hAcc₃ : s₃.arrs 2902 = sign :: acc := (hk₃.2 2902 (by decide)).trans
    ((hk₂.2 2902 (by decide)).trans (by simpa only [s₁, State.setReg_arrs] using hAcc))
  obtain ⟨t, u₄, out, sign', he₄, ht₄, hk₄, hout, hsign', hlen, hbits', hval₄⟩ :=
    gm06Alg511BinaryRowAddProg_exec (w := w) 2902 2901 2902 (by decide) (by decide) (by decide)
      acc (z.digits.map Bool.toNat) sign oriented s₃ hw (by simp only [List.length_map]; omega)
      hbits hzBits hsign hsign₃ hAcc₃ hturn₃
  let R := [0, 7, 8, 9, 11, 20, 31, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2400, 2401, 2402, 2404]
  let A := [2000, 2001, 2002, 2003, 2004, 2005, 2901, 2902]
  have hk₁ : Keeps R A s s₁ := (Keeps.refl _ _ s).setReg (by simp [R]) index
  have hk : Keeps R A s t := ((hk₁.trans hk₂ (by simp [R]) (by simp [A])).trans hk₃ (by simp [R]) (by simp [A])).trans hk₄
    (by simp [R]) (by simp [A])
  refine ⟨t, 4 + (u₂ + (u₃ + u₄)), out, sign', .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_, hk,
    hout, hsign', by simpa only [List.length_map] using hlen, hbits', ?_⟩
  · rw [hrow] at ht₂
    simp only [List.length_map] at ht₄
    dsimp only [index, z] at *
    omega
  · rw [hval₄, hval₃]
    change gm06Alg511BinaryRowValue (sign :: acc) +
        (if dart % 2 = 0 then gm06Alg511BinaryRowValue z.words else -gm06Alg511BinaryRowValue z.words) =
      gm06Alg511BinaryRowValue (sign :: acc) + (if dart % 2 = 0 then z.value else -z.value)
    rw [gm06Alg511BinaryRowValue_integer]

end GraphMinor.Compute
