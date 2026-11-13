module

public import GraphMinor.Compute.GM06Alg34GapComponentData

/-!
# Finite work records for component branches

A queued branch stores the supplied parent drawing, its one disc gap
region list, and a component source label. Reading the record lets the
RAM materialize the exact component input. The record contains only
finite data and never stores a geometric witness or a feasibility answer.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A plain finite record requesting one component of a supplied disc input.
The record implements the component problems in VI (3.3)(iv), page 121. -/
structure GM06GapComponentTask where
  drawing : GM06DrawingData
  gaps : List (Fin drawing.regions.length)
  root : Fin drawing.n

namespace GM06GapComponentTask

/-- The supplied parent augmented input named by a component task. -/
def input (T : GM06GapComponentTask) : GM06GapInput := ⟨T.drawing, [T.gaps]⟩

/-- The finite component input to materialize when the task is read. -/
def target (T : GM06GapComponentTask) : GM06GapInput := T.input.componentGapData T.root

/-- Length-prefixed base words, length-prefixed gap labels, and the component source. -/
def words (T : GM06GapComponentTask) : List ℕ :=
  GM06DrawingData.listWords T.drawing.words ++
    GM06DrawingData.listWords (T.gaps.map Fin.val) ++ [T.root.val]

/-- The task size counts its parent vertices and all record words. -/
def size (T : GM06GapComponentTask) : ℕ := T.drawing.n + T.words.length

/-- Exact number of words in one component work record. -/
theorem words_length (T : GM06GapComponentTask) :
    T.words.length = T.drawing.words.length + T.gaps.length + 3 := by
  simp only [words, GM06DrawingData.listWords, List.length_append, List.length_cons,
    List.length_nil, List.length_map]
  omega

/-- The parent base input fits within its complete work-record size. -/
theorem drawing_size_le (T : GM06GapComponentTask) : T.drawing.size ≤ T.size := by
  rw [GM06DrawingData.size, size, T.words_length]
  omega

end GM06GapComponentTask
end GraphMinor.Compute
