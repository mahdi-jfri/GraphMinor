module

public import GraphMinor.Compute.GM06Alg34RegionRowData
public import GraphMinor.Compute.GM06Alg34Regions

/-!
# Finite updates for the supplied region stream

Each region contributes its own cell and two supplied boundary lists
to one closure-matrix row. Apply these updates at consecutive packed
region labels. The update preserves the allocated matrix size, and
the encoded stream contains two length words per region.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The exact matrix update for one supplied region at a packed row label. -/
def gm06RegionRowWrite (N n i : ℕ) (r : List ℕ × List ℕ) (dst : List ℕ) : List ℕ :=
  gm06MarkCells (N * i) n r.2
    (gm06MarkCells (N * i) 0 r.1 (dst.set (N * i + i) 1))

/-- The exact matrix updates for consecutive supplied region rows. -/
def gm06RegionRows (N n : ℕ) : ℕ → List (List ℕ × List ℕ) → List ℕ → List ℕ
  | _, [], dst => dst
  | i, r :: rs, dst => gm06RegionRows N n (i + 1) rs (gm06RegionRowWrite N n i r dst)

/-- One region update preserves matrix allocation. -/
theorem gm06RegionRowWrite_length (N n i : ℕ) (r : List ℕ × List ℕ) (dst : List ℕ) :
    (gm06RegionRowWrite N n i r dst).length = dst.length := by
  simp only [gm06RegionRowWrite, gm06MarkCells_length, List.length_set]

/-- All consecutive region updates preserve matrix allocation. -/
theorem gm06RegionRows_length (N n i : ℕ) (rs : List (List ℕ × List ℕ)) (dst : List ℕ) :
    (gm06RegionRows N n i rs dst).length = dst.length := by
  induction rs generalizing i dst with
  | nil => rfl
  | cons r rs ih => rw [gm06RegionRows, ih, gm06RegionRowWrite_length]

/-- A supplied region contributes two length words and both incidence lists. -/
theorem gm06RegionWords_cons_length (r : List ℕ × List ℕ) (rs : List (List ℕ × List ℕ)) :
    (gm06RegionWords (r :: rs)).length = 2 + r.1.length + r.2.length + (gm06RegionWords rs).length := by
  simp only [gm06RegionWords, List.length_append, GM06DrawingData.listWords, List.length_cons]
  omega

/-- The supplied region stream has at least two words per region. -/
theorem gm06RegionWords_count_le (rs : List (List ℕ × List ℕ)) :
    2 * rs.length ≤ (gm06RegionWords rs).length := by
  induction rs with
  | nil => exact le_rfl
  | cons r rs ih => rw [gm06RegionWords_cons_length]; simp only [List.length_cons]; omega

end GraphMinor.Compute
