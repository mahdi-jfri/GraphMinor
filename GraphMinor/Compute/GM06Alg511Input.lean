module

public import GraphMinor.Compute.GM06SuccessorInput
import Mathlib.Tactic

/-!
# Finite input fields for VI (5.11)

The decision problem on page 134 supplies a cylinder drawing and a target
winding number. The drawing fields agree with the successor procedure,
with its given linkage removed. The target is supplied as two integers.
Each integer is stored as its positive and negative parts. Length prefixes
separate the fields, so the finite code determines every supplied field.
This file proves serialization facts only. Interpreting the winding of the
embedded edges requires further geometric data.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Drawing labels and a rational target supplied to VI (5.11), page 134.
A valid rational target must have a nonzero denominator. -/
structure GM06Alg511Input where
  vertexCount : ℕ
  endpoints : List ℕ
  rotations : List (List ℕ)
  regionBoundaries : List (List ℕ)
  innerCuff : List ℕ
  outerCuff : List ℕ
  pathCount : ℕ
  numerator : ℤ
  denominator : ℤ
  deriving DecidableEq, Repr

/-- Store an integer using two nonnegative parts, without a word sign bit. -/
def gm06Alg511IntegerWords (z : ℤ) : List ℕ := [z.toNat, (-z).toNat]

/-- Both parts together determine the signed integer. -/
theorem gm06Alg511IntegerWords_injective :
    Function.Injective gm06Alg511IntegerWords := by
  intro a b h
  simp only [gm06Alg511IntegerWords, List.cons.injEq, and_true] at h
  omega

/-- Separate the supplied graph, path count and signed target into rows. -/
def gm06Alg511Rows (x : GM06Alg511Input) : List (List ℕ) :=
  [[x.vertexCount], x.endpoints, gm06EncodeRows x.rotations,
    gm06EncodeRows x.regionBoundaries, x.innerCuff, x.outerCuff,
    [x.pathCount], gm06Alg511IntegerWords x.numerator,
    gm06Alg511IntegerWords x.denominator]

/-- The plain word-array representation of these input fields. -/
def gm06Alg511Words (x : GM06Alg511Input) : List ℕ :=
  gm06EncodeRows (gm06Alg511Rows x)

/-- The field rows determine all the supplied fields. -/
theorem gm06Alg511Rows_injective : Function.Injective gm06Alg511Rows := by
  intro x y h
  cases x with
  | mk n e r f i o k a b =>
    cases y with
    | mk n' e' r' f' i' o' k' a' b' =>
      simp only [gm06Alg511Rows, List.cons.injEq, and_true] at h
      rcases h with ⟨hn, he, hr, hf, hi, ho, hk, ha, hb⟩
      have hn' : n = n' := hn
      have hk' : k = k' := hk
      have hr' := gm06EncodeRows_injective hr
      have hf' := gm06EncodeRows_injective hf
      have ha' := gm06Alg511IntegerWords_injective ha
      have hb' := gm06Alg511IntegerWords_injective hb
      cases hn'; cases he; cases hr'; cases hf'; cases hi; cases ho
      cases hk'; cases ha'; cases hb'
      rfl

/-- Distinct supplied field records have distinct word arrays. -/
theorem gm06Alg511Words_injective : Function.Injective gm06Alg511Words :=
  gm06EncodeRows_injective.comp gm06Alg511Rows_injective

/-- Attach a linkage found by the program to the original drawing fields. -/
def GM06Alg511Input.withLinkage (x : GM06Alg511Input)
    (paths : List (List ℕ)) : GM06SuccessorInput :=
  ⟨x.vertexCount, x.endpoints, x.rotations, x.innerCuff, x.outerCuff, paths⟩

/-- Attaching paths preserves the drawing fields and supplies exactly those paths. -/
theorem GM06Alg511Input.withLinkage_fields (x : GM06Alg511Input)
    (paths : List (List ℕ)) :
    (x.withLinkage paths).vertexCount = x.vertexCount ∧
    (x.withLinkage paths).endpoints = x.endpoints ∧
    (x.withLinkage paths).rotations = x.rotations ∧
    (x.withLinkage paths).innerCuff = x.innerCuff ∧
    (x.withLinkage paths).outerCuff = x.outerCuff ∧
    (x.withLinkage paths).linkage = paths := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end GraphMinor.Compute
