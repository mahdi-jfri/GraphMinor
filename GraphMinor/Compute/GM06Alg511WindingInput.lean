module

public import GraphMinor.Compute.GM06Alg511Input
import Mathlib.Tactic

/-!
# Supplementary geometric edge data for VI (5.11)

Endpoint labels and rotations do not record the number of full turns
around a cylinder. Supply an integer turn for each oriented edge,
measured relative to reference angles at the vertices. These integers
are part of the drawing data, rather than a linkage or an answer.
The interpretation of a turn for a continuous edge curve is given in
`GraphMinor.GM06.Alg511NormalizedTurns`, with the prescribed cuff angles.
This file serializes the finite
extension and proves that its words determine all its supplied fields.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The linkage-free drawing fields together with supplied full-turn
labels in edge order. The representation relation must check the
number of labels and their geometric meaning. -/
structure GM06Alg511WindingInput where
  drawing : GM06Alg511Input
  edgeTurns : List ℤ
  deriving DecidableEq, Repr

/-- Encode the original field array and the signed edge-turn rows
as two separate length-prefixed fields. -/
def gm06Alg511WindingWords (x : GM06Alg511WindingInput) : List ℕ :=
  gm06EncodeRows [gm06Alg511Words x.drawing,
    gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)]

/-- The finite extension retains every supplied integer and drawing field. -/
theorem gm06Alg511WindingWords_injective : Function.Injective gm06Alg511WindingWords := by
  intro x y h
  have hr := gm06EncodeRows_injective h
  simp only [List.cons.injEq, and_true] at hr
  have hd := gm06Alg511Words_injective hr.1
  have ht := (List.map_injective_iff.mpr gm06Alg511IntegerWords_injective)
    (gm06EncodeRows_injective hr.2)
  cases x
  cases y
  cases hd
  cases ht
  rfl

end GraphMinor.Compute
