module

public import GraphMinor.Compute.GM06Alg34RootRanks
public import GraphMinor.Compute.GM06Alg34RegionBoundary

/-!
# Detecting new region boundaries from component marks

For an inactive source, every reached cell is inactive. Hence a cell
lies in the closure of its new region exactly when it occurs in the
supplied closure of some reached cell. The finite test scans the packed
cell labels and reads only reachability and closure-incidence bits.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

/-- For an inactive region source, the closure-hit test is the finite
scan over its reached cells and their supplied closure incidences. -/
theorem regionClosureHit_eq_any_reached (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (b : GM06CellIndex x)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false) :
    x.regionClosureHit vs a b =
      (List.finRange x.cellCount).any (fun c =>
        decide ((x.complementGraph vs).Reachable a c ∧ b ∈ x.cellClosure (x.cellNumbering.symm c))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [regionClosureHit, decide_eq_true_eq, List.any_eq_true, List.mem_finRange, true_and]
  constructor
  · rintro ⟨c, _, hac, hbc⟩
    exact ⟨x.cellNumbering c, hac, by simpa only [Equiv.symm_apply_apply] using hbc⟩
  · rintro ⟨c, hac, hbc⟩
    refine ⟨x.cellNumbering.symm c, x.complementGraph_reachable_inactive vs ha hac, ?_, hbc⟩
    simpa only [Equiv.apply_symm_apply] using hac

end GraphMinor.Compute.GM06DrawingData
