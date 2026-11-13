module

public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Finite list encoding for the cylinder algorithms

The input of VI (5.7), page 133, consists of the embedded finite
graph and the given linkage. Encode a row by its length followed
by its entries, and encode a list of rows by its row count followed
by those row codes. The parsers recover each row and the remaining
input. These codes carry structural instance data, without an answer
or a reduction history.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Length-prefixed encoding of one row of natural-number labels. -/
def gm06EncodeNatList (xs : List ℕ) : List ℕ := xs.length :: xs

/-- Read a length-prefixed row and return the unused suffix. -/
def gm06ReadNatList : List ℕ → Option (List ℕ × List ℕ)
  | [] => none
  | n :: xs => if n ≤ xs.length then some (xs.take n, xs.drop n) else none

/-- A row code is read exactly, preserving the following input. -/
theorem gm06ReadNatList_encode_append (xs tail : List ℕ) :
    gm06ReadNatList (gm06EncodeNatList xs ++ tail) = some (xs, tail) := by
  simp [gm06ReadNatList, gm06EncodeNatList]

/-- Payload of the encoding of a list of rows. -/
def gm06EncodeRowsPayload (rows : List (List ℕ)) : List ℕ := rows.flatMap gm06EncodeNatList

/-- Read exactly n length-prefixed rows. -/
def gm06ReadRowsAux : ℕ → List ℕ → Option (List (List ℕ) × List ℕ)
  | 0, xs => some ([], xs)
  | n + 1, xs => do
      let (row, rest) ← gm06ReadNatList xs
      let (rows, tail) ← gm06ReadRowsAux n rest
      pure (row :: rows, tail)

/-- The row parser recovers all encoded rows and the unused suffix. -/
theorem gm06ReadRowsAux_encode_append (rows : List (List ℕ)) (tail : List ℕ) :
    gm06ReadRowsAux rows.length (gm06EncodeRowsPayload rows ++ tail) = some (rows, tail) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.length_cons, gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc]
    simp only [gm06ReadRowsAux, gm06ReadNatList_encode_append]
    change (do
      let (rs, rest) ← gm06ReadRowsAux rows.length (gm06EncodeRowsPayload rows ++ tail)
      pure (row :: rs, rest)) = _
    rw [ih]
    rfl

/-- A row-list code includes its row count. -/
def gm06EncodeRows (rows : List (List ℕ)) : List ℕ := rows.length :: gm06EncodeRowsPayload rows

/-- Read one row-list code and return the unused suffix. -/
def gm06ReadRows : List ℕ → Option (List (List ℕ) × List ℕ)
  | [] => none
  | n :: xs => gm06ReadRowsAux n xs

/-- A row-list code is read exactly, preserving the following input. -/
theorem gm06ReadRows_encode_append (rows : List (List ℕ)) (tail : List ℕ) :
    gm06ReadRows (gm06EncodeRows rows ++ tail) = some (rows, tail) :=
  gm06ReadRowsAux_encode_append rows tail

/-- Distinct row lists have distinct finite codes. -/
theorem gm06EncodeRows_injective : Function.Injective gm06EncodeRows := by
  intro rows rows' he
  have hh := congrArg gm06ReadRows he
  have h₁ := gm06ReadRows_encode_append rows []
  have h₂ := gm06ReadRows_encode_append rows' []
  simp only [List.append_nil] at h₁ h₂
  rw [h₁, h₂] at hh
  exact congrArg Prod.fst (Option.some.inj hh)

end GraphMinor.Compute
