module

public import GraphMinor.Compute.GM06Alg34DualData
public import GraphMinor.Compute.GM06Alg34GapDiscLayout
public import GraphMinor.Compute.GM06Alg34CyclicShift

/-!
# Finite augmented dual input

The base dual drawing uses the supplied gap region labels as its cuff
vertices. Its following gaps are labelled by the next primal cuff
vertices, which index the transposed dual regions. All data are finite
functions of the original array and its explicit gap labels.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

/-- The dual region at a following dual gap is indexed by the next
primal boundary vertex. -/
def dualGapRegionLabel (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length)
    (i : Fin L.length) : Fin (x.dualData L hR g).regions.length :=
  Fin.cast (x.dualData_regions_length L hR g).symm (L.get (gm06CycleSucc i))

/-- The dual drawing together with its explicitly computed boundary-gap
region list, following VI Section 3, pages 119–120. -/
def dualGapInput (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) : GM06GapInput :=
  ⟨x.dualData L hR g, [List.ofFn (x.dualGapRegionLabel L hR g)]⟩

/-- The augmented dual retains exactly the assembled base dual drawing. -/
theorem dualGapInput_drawing (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualGapInput L hR g).drawing = x.dualData L hR g := rfl

/-- The computed augmented dual has matching single cuff and gap lists. -/
theorem dualGapInput_disc_layout (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    ∃ L' R', (x.dualGapInput L hR g).drawing.cuffs = [L'] ∧
      (x.dualGapInput L hR g).gapRegions = [R'] ∧ R'.length = L'.length := by
  exact ⟨List.ofFn g, List.ofFn (x.dualGapRegionLabel L hR g), rfl, rfl,
    (List.length_ofFn (f := x.dualGapRegionLabel L hR g)).trans
      (List.length_ofFn (f := g)).symm⟩

/-- The dual's internal gap array is the next-primal-vertex label at
each original cuff position. -/
theorem dualGapInput_discGapWords (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualGapInput L hR g).discGapWords =
      List.ofFn (fun i : Fin L.length => (L.get (gm06CycleSucc i)).val) := by
  refine ((x.dualGapInput L hR g).discGapWords_singleton
    (List.ofFn (x.dualGapRegionLabel L hR g)) rfl).trans ?_
  refine (List.map_ofFn (f := x.dualGapRegionLabel L hR g) (g := Fin.val)).trans ?_
  apply congrArg List.ofFn
  funext i
  rfl

end GraphMinor.Compute.GM06DrawingData
