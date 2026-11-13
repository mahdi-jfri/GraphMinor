module

public import GraphMinor.Compute.GM06Alg34Words

/-!
# Plain finite incidence data for cuff gaps

A drawing array records its regions and cuff vertices. For the dual
operation, also record the region adjacent to each cuff gap, in the
same cyclic order as the cuff vertices. These are ordinary finite
region labels, with one list per cuff, so the format also accommodates
two cuffs. A length prefix separates the original drawing array from
these extra boundary incidence lists.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A drawing input with explicit region labels for its cuff gaps.
The labels encode boundary incidence, as in VI Section 3, pages 119–120.
No geometric point, answer, or reduction certificate is part of this data. -/
structure GM06GapInput where
  drawing : GM06DrawingData
  gapRegions : List (List (Fin drawing.regions.length))

namespace GM06GapInput

/-- The region labels in natural-number form. -/
def gapWords (x : GM06GapInput) : List (List ℕ) :=
  x.gapRegions.map (List.map Fin.val)

/-- The original drawing array followed by the plain cuff gap incidence lists. -/
def words (x : GM06GapInput) : List ℕ :=
  GM06DrawingData.listWords x.drawing.words ++ GM06DrawingData.listsWords x.gapWords

/-- Count all vertices and words of the augmented drawing input. -/
def size (x : GM06GapInput) : ℕ := x.drawing.n + x.words.length

/-- The drawing section is read exactly from the augmented input. -/
theorem read_drawing (x : GM06GapInput) :
    (GM06RawDrawingData.readList x.words).1 = x.drawing.words := by
  simp [words, GM06RawDrawingData.readList, GM06DrawingData.listWords]

/-- The remaining words are exactly the explicit gap region section. -/
theorem read_gap_section (x : GM06GapInput) :
    (GM06RawDrawingData.readList x.words).2 = GM06DrawingData.listsWords x.gapWords := by
  simp [words, GM06RawDrawingData.readList, GM06DrawingData.listWords]

/-- The original drawing input fits within the augmented size. -/
theorem drawing_size_le (x : GM06GapInput) : x.drawing.size ≤ x.size := by
  simp only [GM06DrawingData.size, size, words, List.length_append,
    GM06DrawingData.listWords, List.length_cons]
  omega

/-- Equal augmented arrays describe the same underlying finite drawing data. -/
theorem drawing_eq_of_words_eq {x y : GM06GapInput} (hw : x.words = y.words) :
    x.drawing = y.drawing := by
  apply GM06DrawingData.words_injective
  rw [← x.read_drawing, ← y.read_drawing, hw]

end GM06GapInput
end GraphMinor.Compute
