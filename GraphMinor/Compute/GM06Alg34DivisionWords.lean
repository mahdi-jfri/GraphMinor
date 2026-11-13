module

public import GraphMinor.Compute.GM06Alg34ListSection
public import GraphMinor.Compute.GM06Alg34InducedData
public import GraphMinor.Compute.GM06Alg34Layout

/-!
# Word sections for the restricted division

Restrict and renumber every supplied division block, then discard the
empty lists. These are exactly the blocks in the induced payload.
The retained block count and encoded word length are bounded by the
original supplied division section.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Nonempty restricted division blocks, as lists of natural words. -/
def gm06DivisionWordLists (x : GM06DrawingData) (vs : List (Fin x.n))
    (D : List (List (Fin x.n))) : List (List ℕ) :=
  (D.map (gm06RelabelVertexWords x vs)).filter (fun B => !B.isEmpty)

/-- The inner length-prefixed division section after empty blocks are discarded. -/
def gm06DivisionSectionWords (x : GM06DrawingData) (vs : List (Fin x.n))
    (D : List (List (Fin x.n))) : List ℕ :=
  (gm06DivisionWordLists x vs D).flatMap GM06DrawingData.listWords

/-- The computed natural-word blocks agree exactly with the induced division lists. -/
theorem gm06DivisionWordLists_eq (x : GM06DrawingData) (vs : List (Fin x.n)) :
    gm06DivisionWordLists x vs x.division = (x.inducedData vs).division.map (List.map Fin.val) := by
  simp only [gm06DivisionWordLists, gm06RelabelVertexWords_eq, GM06DrawingData.inducedData,
    List.filter_map, List.map_map, Function.comp_def, List.isEmpty_map]
  congr 1
  funext L
  exact gm06RelabelVertexWords_eq x vs L

/-- The supplied block count bounds the number of retained blocks. -/
theorem gm06DivisionWordLists_length_le (x : GM06DrawingData) (vs : List (Fin x.n))
    (D : List (List (Fin x.n))) : (gm06DivisionWordLists x vs D).length ≤ D.length := by
  exact (List.length_filter_le _ _).trans_eq (List.length_map _)

/-- A block contributes its new words precisely when its restriction is nonempty. -/
theorem gm06DivisionSectionWords_cons (x : GM06DrawingData) (vs : List (Fin x.n))
    (B : List (Fin x.n)) (D : List (List (Fin x.n))) :
    gm06DivisionSectionWords x vs (B :: D) =
      if (gm06RelabelVertexWords x vs B).isEmpty then gm06DivisionSectionWords x vs D
      else GM06DrawingData.listWords (gm06RelabelVertexWords x vs B) ++
        gm06DivisionSectionWords x vs D := by
  cases he : (gm06RelabelVertexWords x vs B).isEmpty <;>
    simp [gm06DivisionSectionWords, gm06DivisionWordLists, he]

/-- The restricted division section fits within the original section reservation. -/
theorem gm06DivisionSectionWords_length_le (x : GM06DrawingData) (vs : List (Fin x.n))
    (D : List (List (Fin x.n))) :
    (gm06DivisionSectionWords x vs D).length ≤ (gm06VertexSectionWords D).length := by
  induction D with
  | nil => exact le_rfl
  | cons B D ih =>
    have hB := gm06RelabelVertexWords_length_le x vs B
    rw [gm06DivisionSectionWords_cons, gm06VertexSectionWords_cons]
    split
    · omega
    · simp only [List.length_append, GM06DrawingData.listWords, List.length_cons]
      omega

/-- The payload division encoding consists of the retained count and its new section. -/
theorem GM06DrawingData.induced_divisionWords_eq (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).divisionWords = (gm06DivisionWordLists x vs x.division).length ::
      gm06DivisionSectionWords x vs x.division := by
  simp only [divisionWords, listsWords, gm06DivisionSectionWords, gm06DivisionWordLists_eq,
    List.length_map]

end GraphMinor.Compute
