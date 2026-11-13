module

public import GraphMinor.Compute.Basic

/-!
# Word layout of saved alternating-recursion frames

A frame stores three array lengths, five loop-state words, the parent
input, both vertex-side arrays, and a final pointer to its beginning.
The final pointer lets the return routine locate the previous frame
without scanning older frames. These are execution data, with no
correctness assertion stored inside the frame.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The eight words preceding the saved parent arrays. -/
def gm02SavedFrameHeader (parent left right : List ℕ)
    (mode code aggregate leftAnswer catalogue : ℕ) : List ℕ :=
  [parent.length, left.length, right.length, mode, code, aggregate, leftAnswer, catalogue]

/-- A saved call frame, ending with its starting offset in the stack buffer. -/
def gm02SavedFrameWords (parent left right : List ℕ)
    (mode code aggregate leftAnswer catalogue start : ℕ) : List ℕ :=
  gm02SavedFrameHeader parent left right mode code aggregate leftAnswer catalogue ++
    parent ++ left ++ right ++ [start]

/-- Header length is independent of graph size and the selected code. -/
theorem gm02SavedFrameHeader_length (parent left right : List ℕ)
    (mode code aggregate leftAnswer catalogue : ℕ) :
    (gm02SavedFrameHeader parent left right mode code aggregate leftAnswer catalogue).length = 8 := rfl

/-- A frame has nine overhead words in addition to its three saved arrays. -/
theorem gm02SavedFrameWords_length (parent left right : List ℕ)
    (mode code aggregate leftAnswer catalogue start : ℕ) :
    (gm02SavedFrameWords parent left right mode code aggregate leftAnswer catalogue start).length =
      9 + parent.length + left.length + right.length := by
  simp only [gm02SavedFrameWords, List.length_append, gm02SavedFrameHeader_length,
    List.length_singleton]
  omega

/-- The final frame word recovers its starting offset. -/
theorem gm02SavedFrameWords_getLast (parent left right : List ℕ)
    (mode code aggregate leftAnswer catalogue start : ℕ) :
    (gm02SavedFrameWords parent left right mode code aggregate leftAnswer catalogue start).getLast? =
      some start := by
  simp only [gm02SavedFrameWords, List.getLast?_append, List.getLast?_singleton]
  rfl

end GraphMinor.Compute
