module

public import GraphMinor.Compute.GM02RecursiveChildSize
public import GraphMinor.GM02.RecursiveSchedule

/-!
# Decreasing measure of the constructed recursive inputs

A1's exact compact children have fewer vertices above the exhaustive
bound. A2's children may keep the same count, but switch to A1. Thus
both actual calls decrease twice the vertex count plus the phase bit,
as required for the paper's alternating recursion.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.GM02

/-- Every non-base canonical child strictly decreases the alternating call measure. -/
theorem gm02RecursiveChosenInput_measure (phase : RecursivePhase) (right : Bool)
    (x : GM02SimpleTerminatedInput) (q : ℕ) (L R : Finset (Fin x.n))
    (C : (gm02CompressedBoundaryInput x L R).schemes) (hlarge : 4 * q < x.n)
    (hvalid : (gm02RecursiveSeparatorInput (match phase with | .A1 => true | .A2 => false) x).validSides
      (q : ℤ) (gm02VertexBits L) (gm02VertexBits R)) :
    (match phase with | .A1 => RecursivePhase.A2 | .A2 => RecursivePhase.A1).measure
      (gm02RecursiveChosenInput right x L R C).n < phase.measure x.n := by
  cases phase with
  | A1 =>
    exact recursive_measure_A1 (gm02RecursiveChosenInput_A1_shrink right x q L R C hlarge hvalid).2
  | A2 =>
    exact recursive_measure_A2 (gm02RecursiveChosenInput_size_le right false x q L R C hvalid)

/-- A1 may use the same three-quarter call bound for every input below a supplied vertex bound. -/
theorem gm02RecursiveChosenInput_A1_bound (right : Bool) (x : GM02SimpleTerminatedInput)
    (q n : ℕ) (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes)
    (hx : x.n ≤ n) (hlarge : 4 * q < x.n)
    (hvalid : (gm02RecursiveSeparatorInput true x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    (gm02RecursiveChosenInput right x L R C).n ≤ 3 * n / 4 := by
  have hs := (gm02RecursiveChosenInput_A1_shrink right x q L R C hlarge hvalid).1
  omega

end GraphMinor.Compute
