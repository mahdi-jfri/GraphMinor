module

public import GraphMinor.Compute.GM06Alg34GapTaskData
import GraphMinor.Compute.GM06Alg34WordBounds

/-!
# Reading component work records exactly

Two length-prefixed reads recover the supplied parent drawing words and
gap region numbers, leaving the component source as the final word.
The round trips imply that equal record words contain the same finite
work request. No object is selected from a geometric interpretation.
-/

public section
namespace GraphMinor.Compute.GM06GapComponentTask

/-- Read the parent drawing words and leave the remaining work-record fields. -/
theorem read_drawing (T : GM06GapComponentTask) (tail : List ℕ) :
    GM06RawDrawingData.readList (T.words ++ tail) =
      (T.drawing.words, GM06DrawingData.listWords (T.gaps.map Fin.val) ++ T.root.val :: tail) := by
  simp [words, GM06RawDrawingData.readList, GM06DrawingData.listWords, List.append_assoc]

/-- The next read recovers precisely the supplied parent gap incidence labels. -/
theorem read_gaps (T : GM06GapComponentTask) (tail : List ℕ) :
    GM06RawDrawingData.readList (GM06RawDrawingData.readList (T.words ++ tail)).2 =
      (T.gaps.map Fin.val, T.root.val :: tail) := by
  rw [T.read_drawing]
  simp [GM06RawDrawingData.readList, GM06DrawingData.listWords]

/-- Every drawing word in a task fits within its complete finite record size. -/
theorem drawing_words_le_size (T : GM06GapComponentTask) (a : ℕ) (ha : a ∈ T.drawing.words) :
    a ≤ T.size := (gm06Words_le_size T.drawing a ha).trans T.drawing_size_le

/-- Every supplied gap region number fits within the finite work-record size. -/
theorem gap_words_lt_size (T : GM06GapComponentTask) (a : ℕ) (ha : a ∈ T.gaps.map Fin.val) :
    a < T.size := by
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
  exact r.isLt.trans_le (T.drawing.counts_le_size.2.2.trans T.drawing_size_le)

/-- Equal work-record arrays contain identical parent data and component source labels. -/
theorem words_injective : Function.Injective words := by
  rintro ⟨d, gs, r⟩ ⟨d', gs', r'⟩ hw
  have hdw := congrArg (fun w => (GM06RawDrawingData.readList (w ++ [])).1) hw
  simp only [read_drawing] at hdw
  have hd : d = d' := GM06DrawingData.words_injective hdw
  subst d'
  have hgw := congrArg (fun w =>
    (GM06RawDrawingData.readList (GM06RawDrawingData.readList (w ++ [])).2).1) hw
  simp only [read_gaps] at hgw
  have hg : gs = gs' := List.map_injective_iff.mpr Fin.val_injective hgw
  subst gs'
  have hrw := congrArg (fun w =>
    (GM06RawDrawingData.readList (GM06RawDrawingData.readList (w ++ [])).2).2.getD 0 0) hw
  simp only [read_gaps, List.getD_cons_zero] at hrw
  have hr : r = r' := Fin.val_injective hrw
  subst r'
  rfl

end GraphMinor.Compute.GM06GapComponentTask
