module

public import GraphMinor.Compute.GM06Alg34DualGapClassWords
public import GraphMinor.Compute.GM06Alg34DualGapRootLoop
public import GraphMinor.Compute.GM06Alg34DualData
public import GraphMinor.Compute.GM06Alg34Layout

/-!
# Canonical output words for the dual division scan

Only least gap representatives contribute records. A complete source
scan therefore lists every finite dual block once, in the canonical
order already used by the dual data construction.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The length-prefixed class record selected at one source, or no words at a nonroot. -/
def gm06DualSelectedClassWords (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) (i : Fin L.length) : List ℕ :=
  if gm06GapIsRoot x L i then GM06DrawingData.listWords (gm06DualGapClassWords x L g i) else []

/-- The class records selected among the given source positions. -/
def gm06DualDivisionRecordWords (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) (V : List (Fin L.length)) : List ℕ :=
  (V.filter (gm06GapIsRoot x L)).flatMap
    (fun i => GM06DrawingData.listWords (gm06DualGapClassWords x L g i))

/-- Splitting the source scan splits its exact selected record words. -/
theorem gm06DualDivisionRecordWords_cons (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) (i : Fin L.length) (V : List (Fin L.length)) :
    gm06DualDivisionRecordWords x L g (i :: V) =
      gm06DualSelectedClassWords x L g i ++ gm06DualDivisionRecordWords x L g V := by
  cases hi : gm06GapIsRoot x L i <;>
    simp only [gm06DualDivisionRecordWords, gm06DualSelectedClassWords,
      List.filter_cons, hi, Bool.false_eq_true, ↓reduceIte, List.flatMap_cons, List.nil_append]

/-- The complete canonical class scan is the finite dual division section
following its block-count word. -/
theorem gm06DualDivisionRecordWords_eq (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualGapDivision L).length :: gm06DualDivisionRecordWords x L g (List.finRange L.length) =
      (x.dualData L hR g).divisionWords := by
  simp only [GM06DrawingData.divisionWords, GM06DrawingData.raw, GM06DrawingData.dualData,
    GM06DrawingData.dualRegionDivision, GM06DrawingData.dualGapDivision,
    gm06ClassBlocks, gm06ClassRoots, gm06DualDivisionRecordWords, gm06GapIsRoot,
    GM06DrawingData.listsWords, List.length_map, List.map_map, List.flatMap_map, Function.comp_def]
  rfl

end GraphMinor.Compute
