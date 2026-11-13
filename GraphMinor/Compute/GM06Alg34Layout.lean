module

public import GraphMinor.Compute.GM06Alg34Words
public import GraphMinor.Compute.GM06Alg34Regions

/-!
# Sections and word bounds of the supplied disc array

The header is followed by endpoint pairs, region boundaries, cuff lists,
and division blocks. Their lengths bound the section offsets and the
three counts. Thus a logarithmic word size suffices for the initial RAM
parser, without a promise about scratch registers or proof-derived data.
-/

@[expose] public section
namespace GraphMinor.Compute

private theorem gm06_regionWords_flatMap (rs : List (List ℕ × List ℕ)) :
    gm06RegionWords rs = rs.flatMap (fun r =>
      GM06DrawingData.listWords r.1 ++ GM06DrawingData.listWords r.2) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [gm06RegionWords, List.flatMap_cons, ih]

private theorem gm06_endpointWords_length {n : ℕ} (es : List (Fin n × Fin n)) :
    (es.flatMap (fun e => [e.1.val, e.2.val])).length = 2 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

private theorem gm06_regionWords_length (rs : List (List ℕ × List ℕ)) :
    2 * rs.length ≤ (gm06RegionWords rs).length := by
  induction rs with
  | nil => simp only [gm06RegionWords, List.length_nil, Nat.mul_zero, le_refl]
  | cons r rs ih =>
    simp only [gm06RegionWords, List.length_append, GM06DrawingData.listWords, List.length_cons]
    omega

namespace GM06DrawingData

/-- The two endpoint words for every edge. -/
def endpointWords (x : GM06DrawingData) : List ℕ :=
  x.ends.flatMap (fun e => [e.1.val, e.2.val])

/-- The two boundary incidence lists for every region. -/
def regionWords (x : GM06DrawingData) : List ℕ := gm06RegionWords x.raw.regions

/-- The supplied cyclic lists, preceded by their count. -/
def cuffWords (x : GM06DrawingData) : List ℕ := listsWords (x.cuffs.map (List.map Fin.val))

/-- The supplied division blocks, preceded by their count. -/
def divisionWords (x : GM06DrawingData) : List ℕ := listsWords (x.division.map (List.map Fin.val))

/-- The array consists of exactly these five successive sections. -/
theorem words_layout (x : GM06DrawingData) :
    x.words = [x.n, x.ends.length, x.regions.length] ++ x.endpointWords ++
      x.regionWords ++ x.cuffWords ++ x.divisionWords := by
  simp only [words, endpointWords, regionWords, cuffWords, divisionWords,
    gm06_regionWords_flatMap, raw, List.flatMap_map]

theorem endpointWords_length (x : GM06DrawingData) :
    x.endpointWords.length = 2 * x.ends.length := gm06_endpointWords_length x.ends

theorem regionWords_length (x : GM06DrawingData) :
    2 * x.regions.length ≤ x.regionWords.length := by
  simpa only [regionWords, raw, List.length_map] using gm06_regionWords_length x.raw.regions

theorem words_length (x : GM06DrawingData) :
    x.words.length = 3 + 2 * x.ends.length + x.regionWords.length +
      x.cuffWords.length + x.divisionWords.length := by
  rw [words_layout]
  simp only [List.length_append, List.length_cons, List.length_nil, endpointWords_length]

theorem cuffWords_pos (x : GM06DrawingData) : 0 < x.cuffWords.length := by
  simp only [cuffWords, listsWords, List.length_cons, Nat.zero_lt_succ]

theorem divisionWords_pos (x : GM06DrawingData) : 0 < x.divisionWords.length := by
  simp only [divisionWords, listsWords, List.length_cons, Nat.zero_lt_succ]

/-- Cursor position immediately after all region boundary lists. -/
def cuffOffset (x : GM06DrawingData) : ℕ := 3 + 2 * x.ends.length + x.regionWords.length

theorem cuffOffset_lt_length (x : GM06DrawingData) : x.cuffOffset < x.words.length := by
  have h := x.words_length
  have hc := x.cuffWords_pos
  have hd := x.divisionWords_pos
  unfold cuffOffset
  omega

theorem regionOffset_lt_length (x : GM06DrawingData) :
    3 + 2 * x.ends.length < x.words.length :=
  lt_of_le_of_lt (Nat.le_add_right _ _) x.cuffOffset_lt_length

theorem five_le_words_length (x : GM06DrawingData) : 5 ≤ x.words.length := by
  have h := x.words_length
  have hc := x.cuffWords_pos
  have hd := x.divisionWords_pos
  omega

theorem words_length_le_size (x : GM06DrawingData) : x.words.length ≤ x.size :=
  Nat.le_add_left _ _

theorem counts_le_size (x : GM06DrawingData) :
    x.n ≤ x.size ∧ x.ends.length ≤ x.size ∧ x.regions.length ≤ x.size := by
  have h := x.words_length
  have hr := x.regionWords_length
  unfold size
  omega

/-- The entire array and each cursor into it fit in logarithmic words. -/
theorem words_length_lt_wordSize (x : GM06DrawingData) {c : ℕ} (hc : 1 ≤ c) :
    x.words.length < 2 ^ wordSize c x.size :=
  lt_two_pow_wordSize_of_le hc (x.words_length_le_size.trans (Nat.le_succ _))

end GM06DrawingData
end GraphMinor.Compute
