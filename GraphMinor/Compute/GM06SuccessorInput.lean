module

public import GraphMinor.Compute.GM06ListEncoding

/-!
# Finite structural input for VI (5.7)

The procedure on page 133 starts with a drawing and a given linkage.
The finite input records vertex labels, edge ends, the rotations at
vertices, the orders on the two cuffs, and the given paths. Edge ends
are listed consecutively. Rotations use directed edge labels, so the
two sides of a loop remain distinct.
Rotations include the auxiliary edges on both cuffs, with the original
edges first, the inner gaps next and the outer gaps last.

Length prefixes separate the fields. The encoding is injective. The
record contains only the instance data. In particular, it contains no
successor linkage or reduction sequence.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Finite labels and boundary walks supplied to the successor procedure. -/
structure GM06SuccessorInput where
  vertexCount : ℕ
  endpoints : List ℕ
  rotations : List (List ℕ)
  innerCuff : List ℕ
  outerCuff : List ℕ
  linkage : List (List ℕ)
  deriving DecidableEq, Repr

/-- Separate each structural field in its own length-prefixed row. -/
def gm06SuccessorRows (x : GM06SuccessorInput) : List (List ℕ) :=
  [[x.vertexCount], x.endpoints, gm06EncodeRows x.rotations,
    x.innerCuff, x.outerCuff,
    gm06EncodeRows x.linkage]

/-- The finite word-array code for a successor instance. -/
def gm06EncodeSuccessorInput (x : GM06SuccessorInput) : List ℕ :=
  gm06EncodeRows (gm06SuccessorRows x)

/-- The field rows determine all the supplied structural data. -/
theorem gm06SuccessorRows_injective : Function.Injective gm06SuccessorRows := by
  intro x y h
  cases x with
  | mk n e r i o p =>
    cases y with
    | mk n' e' r' i' o' p' =>
      simp only [gm06SuccessorRows, List.cons.injEq, and_true] at h
      rcases h with ⟨hn, he, hr, hi, ho, hp⟩
      have hn' : n = n' := hn
      have hr' := gm06EncodeRows_injective hr
      have hp' := gm06EncodeRows_injective hp
      cases hn'; cases he; cases hr'; cases hi; cases ho; cases hp'
      rfl

/-- Different structural instances have different word-array codes. -/
theorem gm06EncodeSuccessorInput_injective : Function.Injective gm06EncodeSuccessorInput :=
  gm06EncodeRows_injective.comp gm06SuccessorRows_injective

end GraphMinor.Compute
