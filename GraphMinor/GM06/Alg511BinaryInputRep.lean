module

public import GraphMinor.Compute.GM06Alg511BinaryDigits
public import GraphMinor.GM06.Alg511PositiveDrawingInput

/-!
# Coverage and meaning of the binary decision input

VI (5.11), page 134, takes a cylinder drawing and a target value.
The finite input supplies the ordinary graph labels, positive
rotations with both cuffs, the ordered cuff vertices, the path
count, the target integer pair and normalized integer edge turns.
Each integer has a sign and one word for each supplied binary bit.
There is no supplied linkage or region row.

Interpret this input by the same vertex and edge bijections,
cuff equations, positive polar charts and normalized turns as
for the drawing input. Replacing integer fields by their binary
representations retains every one of those equations. Thus every
intended instance has binary data, and identical supplied words
determine the same feasibility answer. No program reads a decoded
large integer as a machine word.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- Replace the integer fields of a region-free drawing input by
signs and actual binary digit lists, retaining its drawing labels. -/
def alg511BinaryInputOfWinding (x : GM06Alg511WindingInput) : GM06Alg511BinaryInput where
  vertexCount := x.drawing.vertexCount
  endpoints := x.drawing.endpoints
  rotations := x.drawing.rotations
  innerCuff := x.drawing.innerCuff
  outerCuff := x.drawing.outerCuff
  pathCount := x.drawing.pathCount
  numerator := .ofInt x.drawing.numerator
  denominator := .ofInt x.drawing.denominator
  edgeTurns := x.edgeTurns.map GM06Alg511BinaryInteger.ofInt

/-- Interpreting the supplied binary integer fields recovers all
original data of a region-free drawing input exactly. -/
theorem alg511BinaryInputOfWinding_decode (x : GM06Alg511WindingInput)
    (hregions : x.drawing.regionBoundaries = []) :
    (alg511BinaryInputOfWinding x).toWindingInput = x := by
  cases x with
  | mk drawing turns =>
    cases drawing
    simp only at hregions
    simp only [alg511BinaryInputOfWinding, GM06Alg511BinaryInput.toWindingInput,
      GM06Alg511BinaryInteger.value_ofInt, List.map_map, Function.comp_def]
    cases hregions
    simp

/-- The binary representation relation has only the supplied
drawing interpretations: graph-label bijections, ordered cuffs,
normalized turns and positive rotations. It supplies no linkage. -/
abbrev GM06Alg511BinaryDrawingRep (x : GM06Alg511BinaryInput) (G : Drawing ClosedCylinder) :=
  GM06Alg511PositiveDrawingRep x.toWindingInput G

/-- Every intended VI (5.11) instance has a linkage-free binary
input for exactly its given numerator and nonzero denominator. -/
theorem alg511_exists_binary_drawing_input (k : ℕ) (G : Drawing ClosedCylinder)
    (hG : IsCylinderSection5Drawing k G) (numerator denominator : ℤ)
    (hden : denominator ≠ 0) :
    ∃ x : GM06Alg511BinaryInput, x.pathCount = k ∧ x.numerator.value = numerator ∧
      x.denominator.value = denominator ∧ Nonempty (GM06Alg511BinaryDrawingRep x G) := by
  obtain ⟨x, hk, hn, hd, ⟨rep⟩⟩ := alg511_exists_positive_drawing_input k G hG numerator denominator hden
  refine ⟨alg511BinaryInputOfWinding x, hk, ?_, ?_, ?_⟩
  · simpa only [alg511BinaryInputOfWinding, GM06Alg511BinaryInteger.value_ofInt] using hn
  · simpa only [alg511BinaryInputOfWinding, GM06Alg511BinaryInteger.value_ofInt] using hd
  · have heq := alg511BinaryInputOfWinding_decode x rep.regions_empty
    change Nonempty (GM06Alg511PositiveDrawingRep (alg511BinaryInputOfWinding x).toWindingInput G)
    rw [heq]
    exact ⟨rep⟩

/-- Equal supplied binary words determine the same winding
feasibility, for any two actual drawings realizing those words. -/
theorem alg511_binary_words_feasible_iff {x y : GM06Alg511BinaryInput}
    {G H : Drawing ClosedCylinder} (rep : GM06Alg511BinaryDrawingRep x G)
    (rep' : GM06Alg511BinaryDrawingRep y H) (hk : 0 < x.pathCount)
    (hwords : x.words = y.words) :
    IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target ↔
      IsThetaFeasible y.pathCount H y.toWindingInput.drawing.target := by
  have hxy := GM06Alg511BinaryInput.words_injective hwords
  subst y
  exact alg511_positive_drawing_words_feasible_iff rep rep' hk rfl

/-- Count all supplied integer bits in the input size, and count
vertices separately so that isolated vertices contribute as well. -/
def alg511BinaryInputSize (x : GM06Alg511BinaryInput) : ℕ := x.vertexCount + x.words.length

/-- Every target bit and sign is part of the supplied input length. -/
theorem alg511_binary_target_size_le (x : GM06Alg511BinaryInput) :
    x.numerator.words.length + x.denominator.words.length ≤ alg511BinaryInputSize x := by
  have hlen := gm06EncodeRows_length x.rows
  change x.words.length = _ at hlen
  simp only [GM06Alg511BinaryInput.rows, List.length_cons, List.length_nil,
    List.flatten_cons, List.flatten_nil, List.length_append] at hlen
  unfold alg511BinaryInputSize
  omega

end GraphMinor.GM06
