module

public import GraphMinor.Compute.GM06Alg34DualRegions
public import GraphMinor.Compute.GM06Alg34DualGapDivision
import GraphMinor.GM06.Alg34Relabel

/-!
# Assembling a finite disc dual payload

The supplied primal regions become dual vertices and the primal vertices
become dual regions. Transpose the incidence lists and attach the gap
classes through their finite region labels. The gap-to-region map is
an explicit finite argument. This construction neither selects geometric
points nor extracts data from a correctness proof.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

open Set GM06

/-- The dual division transported from gap positions to their region labels. -/
def dualRegionDivision (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) : List (List (Fin x.regions.length)) :=
  (x.dualGapDivision L).map (List.map g)

/-- The assembled finite dual drawing, with an explicit gap-to-region labelling.
VI, Section 3, pages 119–120 identifies dual vertices with primal regions. -/
def dualData (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    GM06DrawingData where
  n := x.regions.length
  ends := x.dualEndsOfNonempty hR
  regions := List.ofFn (x.dualRegionBoundary hR)
  cuffs := [List.ofFn g]
  division := x.dualRegionDivision L g

/-- The dual has exactly as many edges as the supplied primal drawing. -/
theorem dualData_edges_length (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualData L hR g).ends.length = x.ends.length :=
  x.dualEndsOfNonempty_length hR

/-- The dual region count is the supplied primal vertex count. -/
theorem dualData_regions_length (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualData L hR g).regions.length = x.n := by
  simp only [dualData, List.length_ofFn]

/-- Mapping a listed block denotes the image of its label set. -/
theorem block_map {n m : ℕ} (g : Fin n → Fin m) (B : List (Fin n)) :
    block (B.map g) = g '' block B := by
  ext b
  simp only [block, mem_ofPred_eq, List.mem_map, mem_image]

/-- The assembled dual division is exactly the image of its gap classes. -/
theorem dualData_divisionSet (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualData L hR g).divisionSet = (Set.image g) '' x.dualGapDivisionSet L := by
  change block '' {B | B ∈ (x.dualGapDivision L).map (List.map g)} =
    (Set.image g) '' (block '' {B | B ∈ x.dualGapDivision L})
  ext B
  simp only [mem_image, mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨block A, ⟨A, hA, rfl⟩, (block_map g A).symm⟩
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.map g, ⟨A, hA, rfl⟩, block_map g A⟩

/-- Distinct gap region labels preserve the division in the assembled dual. -/
theorem dualData_isDivision (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length)
    (hg : Function.Injective g) : IsDivision (x.dualData L hR g).divisionSet := by
  rw [dualData_divisionSet]
  exact alg34_division_image (f := ⟨g, hg⟩) (x.dualGapDivision_isDivision L)

/-- The dual division covers exactly the supplied gap region labels. -/
theorem dualData_divisionUnion (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    divisionUnion (x.dualData L hR g).divisionSet = Set.range g := by
  rw [dualData_divisionSet]
  ext b
  constructor
  · rintro ⟨_, ⟨A, hA, rfl⟩, a, ha, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    have ha : a ∈ divisionUnion (x.dualGapDivisionSet L) := by
      rw [x.dualGapDivision_union L]; trivial
    obtain ⟨A, hA, ha⟩ := ha
    exact ⟨g '' A, ⟨A, hA, rfl⟩, a, ha, rfl⟩

end GraphMinor.Compute.GM06DrawingData
