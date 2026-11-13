module

public import GraphMinor.Compute.GM06Alg511TurnWords
public import GraphMinor.Compute.GM06ListEncoding
import Mathlib.Tactic

/-!
# Locating signed edge words in the supplied row code

The winding input of VI (5.11), page 134, stores each integer as a
row of two nonnegative parts. The row code adds a length word before
each pair. Removing these length words is a fixed arithmetic index
map. This identifies the flattened array used by the turn accumulator
with words already present in the supplied input.
-/

public section
namespace GraphMinor.Compute

private theorem turnPayload_getD (turns : List ℤ) (i : ℕ) (hi : i < turns.length) :
    (gm06EncodeRowsPayload (turns.map gm06Alg511IntegerWords)).getD (3 * i + 1) 0 =
      (turns.getD i 0).toNat ∧
    (gm06EncodeRowsPayload (turns.map gm06Alg511IntegerWords)).getD (3 * i + 2) 0 =
      (-(turns.getD i 0)).toNat := by
  induction turns generalizing i with
  | nil => simp at hi
  | cons t ts ih =>
    cases i with
    | zero => exact ⟨rfl, rfl⟩
    | succ i =>
      have hi' : i < ts.length := by simpa using hi
      simpa [gm06EncodeRowsPayload, gm06EncodeNatList, gm06Alg511IntegerWords,
        Nat.mul_succ, Nat.add_assoc] using ih i hi'

/-- The two magnitude words occupy consecutive positions after each
row-length header in the supplied integer row code. -/
theorem gm06Alg511TurnCode_getD (turns : List ℤ) (i : ℕ) (hi : i < turns.length) :
    (gm06EncodeRows (turns.map gm06Alg511IntegerWords)).getD (3 * i + 2) 0 =
      (turns.getD i 0).toNat ∧
    (gm06EncodeRows (turns.map gm06Alg511IntegerWords)).getD (3 * i + 3) 0 =
      (-(turns.getD i 0)).toNat := by
  simpa [gm06EncodeRows, Nat.add_assoc] using turnPayload_getD turns i hi

/-- Dropping the fixed row headers produces exactly the paired
magnitude words used by the signed-turn summation program. -/
theorem gm06Alg511TurnCode_flatten_getD (turns : List ℤ) (d : ℕ)
    (hd : d < 2 * turns.length) :
    (gm06EncodeRows (turns.map gm06Alg511IntegerWords)).getD
      (2 + 3 * (d / 2) + d % 2) 0 = (gm06Alg511TurnWords turns).getD d 0 := by
  have hi : d / 2 < turns.length := by omega
  obtain ⟨hp, hn⟩ := gm06Alg511TurnCode_getD turns (d / 2) hi
  obtain ⟨wp, wn⟩ := gm06Alg511TurnWords_getD turns (d / 2) hi
  by_cases he : d % 2 = 0
  · have hd' : d = 2 * (d / 2) := by omega
    have hk : 2 + 3 * (d / 2) + d % 2 = 3 * (d / 2) + 2 := by omega
    rw [hk, hp]
    exact wp.symm.trans (congrArg (fun j => (gm06Alg511TurnWords turns).getD j 0) hd'.symm)
  · have hd' : d = 2 * (d / 2) + 1 := by omega
    have hk : 2 + 3 * (d / 2) + d % 2 = 3 * (d / 2) + 3 := by omega
    rw [hk, hn]
    exact wn.symm.trans (congrArg (fun j => (gm06Alg511TurnWords turns).getD j 0) hd'.symm)

/-- The encoded turn array has one count word and three words per edge. -/
theorem gm06Alg511TurnCode_length (turns : List ℤ) :
    (gm06EncodeRows (turns.map gm06Alg511IntegerWords)).length = 1 + 3 * turns.length := by
  suffices (gm06EncodeRowsPayload (turns.map gm06Alg511IntegerWords)).length =
      3 * turns.length by simpa [gm06EncodeRows, Nat.add_comm] using congrArg Nat.succ this
  induction turns with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, gm06EncodeRowsPayload, List.flatMap_cons,
      gm06EncodeNatList, gm06Alg511IntegerWords, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append] at *
    omega

end GraphMinor.Compute
