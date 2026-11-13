module

public import GraphMinor.Compute.GM06Alg34DualEndsProg
public import GraphMinor.Compute.GM06Alg34DualRegionsProg
public import GraphMinor.Compute.GM06Alg34DualCuffProg
public import GraphMinor.Compute.GM06Alg34DualDivisionProg

/-!
# Joining the computed dual payload sections

The transposed header, retained edge slots, transposed region records,
supplied cuff labels and canonical mapped classes form exactly the
word encoding of the finite dual drawing. This equality connects the
separately verified RAM section writers to one complete output array.
-/

public section
namespace GraphMinor.Compute

/-- The five computed output sections are precisely the finite dual drawing array. -/
theorem gm06DualPayloadSections_eq (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    [x.regions.length, x.ends.length, x.n] ++
      gm06DualEndpointWords x hR (List.finRange x.ends.length) ++
      gm06DualRegionWords x (List.finRange x.n) ++
      (1 :: L.length :: List.ofFn (fun i => (g i).val)) ++
      ((x.dualGapDivision L).length :: gm06DualDivisionRecordWords x L g (List.finRange L.length)) =
        (x.dualData L hR g).words := by
  rw [gm06DualEndpointWords_eq x hR L g, gm06DualRegionWords_eq x hR L g,
    ← gm06DualCuffWords_eq x L hR g, gm06DualDivisionRecordWords_eq x L hR g]
  have hc : [x.regions.length, x.ends.length, x.n] =
      [(x.dualData L hR g).n, (x.dualData L hR g).ends.length,
        (x.dualData L hR g).regions.length] := by
    exact congrArg₂ (fun m r => [x.regions.length, m, r])
      (x.dualData_edges_length L hR g).symm (x.dualData_regions_length L hR g).symm
  rw [hc]
  exact (x.dualData L hR g).words_layout.symm

end GraphMinor.Compute
