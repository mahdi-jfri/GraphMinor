module

public import GraphMinor.Compute.GM06Alg511WindingInput
public import GraphMinor.Compute.GM06Alg511ReflectCuff
public import GraphMinor.Compute.GM06DartMate
public import GraphMinor.Compute.GM06Alg511ReflectDrawing

/-!
# Finite drawing data under orientation reversal

For VI (5.11), page 134, reverse the local rotation and boundary
walk orientations, retain region headers, relabel the fixed cuff
markers, reorder both prescribed cuffs, and negate the
target. Whole edge turns also need the integer adjustment caused by
returning reflected cuff reference angles to the prescribed range.
The adjustment is one at each nonzero cuff index and zero elsewhere.
All of these operations use supplied finite labels only.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Reverse drawing orientation while keeping vertex and edge labels. -/
def GM06Alg511Input.reflected (x : GM06Alg511Input) : GM06Alg511Input where
  vertexCount := x.vertexCount
  endpoints := x.endpoints
  rotations := x.rotations.map (fun row => row.reverse.map
    (gm06Alg511ReflectAugmentedDart (x.endpoints.length / 2) x.pathCount))
  regionBoundaries := x.regionBoundaries.map
    (gm06Alg511ReflectRegionRow (x.endpoints.length / 2) x.pathCount)
  innerCuff := gm06Alg511ReflectCuffWords x.innerCuff
  outerCuff := gm06Alg511ReflectCuffWords x.outerCuff
  pathCount := x.pathCount
  numerator := -x.numerator
  denominator := x.denominator

/-- Whole-turn correction for a vertex at a nonzero prescribed cuff
index. The first label of each cuff has correction zero. -/
def gm06Alg511CuffOffset (x : GM06Alg511Input) (v : ℕ) : ℕ :=
  if v ∈ x.innerCuff.tail ∨ v ∈ x.outerCuff.tail then 1 else 0

/-- Reflect the supplied integer turns, including their endpoint
reference corrections. No geometric choice is used in this map. -/
def GM06Alg511WindingInput.reflected (x : GM06Alg511WindingInput) : GM06Alg511WindingInput where
  drawing := x.drawing.reflected
  edgeTurns := x.edgeTurns.mapIdx fun i t => -t +
    (gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (2 * i) 0) : ℤ) -
    (gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (2 * i + 1) 0) : ℤ)

/-- Every reference correction is a single bit. -/
theorem gm06Alg511CuffOffset_le_one (x : GM06Alg511Input) (v : ℕ) :
    gm06Alg511CuffOffset x v ≤ 1 := by
  unfold gm06Alg511CuffOffset
  split <;> decide

end GraphMinor.Compute
