module

public import GraphMinor.Compute.GM06Alg34DiscDualData
public import GraphMinor.Compute.GM06Alg34UniformSize
import GraphMinor.Compute.GM06Alg34GapPositionCast

/-!
# Uniform size of the plain finite dual operation

Matching supplied cuff and gap lists determine the explicit region
lookup. The pure finite dual size bound applies to that lookup, so the
plain update has the same uniform quadratic bound without any geometric
witness or extra function in the executable input.
-/

public section
namespace GraphMinor.Compute

/-- The plain dual update has the uniform size bound on matching disc lists. -/
theorem gm06DiscDual_size_le_uniform (Q : ℕ) (X : GM06GapInput)
    (hQ : X.drawing.cellCount ≤ Q)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧
      R.length = L.length ∧ L.Nodup)
    (hR : 0 < X.drawing.regions.length) :
    X.discDualData.drawing.size ≤ 40 * (Q + 2) ^ 2 := by
  obtain ⟨L, R, hL, hgroups, hlen, hLN⟩ := hshape
  let g : Fin L.length → Fin X.drawing.regions.length := fun i => R.get (Fin.cast hlen.symm i)
  have hg : List.ofFn g = R := (gm06OfFn_cast hlen.symm R.get).trans (List.ofFn_get R)
  rw [X.discDualData_eq L R hL hgroups hR hlen g hg]
  exact gm06Dual_size_le_uniform Q X.drawing hQ L hLN hR g

end GraphMinor.Compute
