module

public import GraphMinor.Compute.GM06Alg34RegionRecordWords
public import GraphMinor.Compute.GM06Alg34CuffSection
public import GraphMinor.Compute.GM06Alg34DivisionWords

/-!
# Space bounds for an induced deletion payload

Each new region uses at most one old vertex-and-edge boundary record
per canonical root. Endpoint, cuff, and division sections do not grow.
Together these bounds give a quadratic bound on the complete new word
array and on its input size, independent of geometric representation.
-/

public section
namespace GraphMinor.Compute

private theorem flatMap_length_le {α : Type*} (L : List α) (f : α → List ℕ)
    (M : ℕ) (hf : ∀ a ∈ L, (f a).length ≤ M) :
    (L.flatMap f).length ≤ L.length * M := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := hf a (List.mem_cons_self ..)
    have ht := ih (fun b hb => hf b (List.mem_cons_of_mem a hb))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- The induced region section fits one old-size record per supplied cell. -/
theorem gm06Induced_regionWords_length_le (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).regionWords.length ≤ x.cellCount * (2 + x.n + x.ends.length) := by
  rw [gm06Induced_regionWords_eq_records]
  have hroots : (x.regionRoots vs).length ≤ x.cellCount := by
    rw [← gm06RootMask_sum]; exact gm06RootMask_sum_le x vs
  exact (flatMap_length_le (x.regionRoots vs) (gm06RegionRecordWords x vs) _
    (fun a _ => gm06RegionRecordWords_length_le x vs a)).trans
      (Nat.mul_le_mul_right _ hroots)

/-- Restricting cuff lists cannot enlarge their encoded section. -/
theorem gm06Induced_cuffWords_length_le (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).cuffWords.length ≤ x.cuffWords.length := by
  rw [x.induced_cuffWords_eq_section, x.cuffWords_eq_section, List.length_cons, List.length_cons]
  exact Nat.succ_le_succ (gm06RelabelSectionWords_length_le x vs x.cuffs)

/-- Restricting blocks and dropping empty blocks cannot enlarge the
encoded division section. -/
theorem gm06Induced_divisionWords_length_le (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).divisionWords.length ≤ x.divisionWords.length := by
  have hold : x.divisionWords = x.division.length :: gm06VertexSectionWords x.division := by
    simp only [GM06DrawingData.divisionWords, GM06DrawingData.listsWords, List.length_map,
      gm06VertexSectionWords, List.flatMap_map]
  rw [x.induced_divisionWords_eq, hold, List.length_cons, List.length_cons]
  exact Nat.succ_le_succ (gm06DivisionSectionWords_length_le x vs x.division)

/-- The complete induced word array has a uniform quadratic bound in
the original input size. -/
theorem gm06Induced_words_length_le (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).words.length ≤ x.size + x.size * (x.size + 2) := by
  have hregions := gm06Induced_regionWords_length_le x vs
  have hcuffs := gm06Induced_cuffWords_length_le x vs
  have hdivision := gm06Induced_divisionWords_length_le x vs
  have hedge : (x.inducedData vs).ends.length ≤ x.ends.length := by
    rw [x.inducedData_ends_length, ← gm06EdgeMask_sum]
    exact gm06EdgeMask_sum_le x vs
  have hN := x.cellCount_le_size
  have hrecord : 2 + x.n + x.ends.length ≤ x.size + 2 := by
    dsimp only [GM06DrawingData.cellCount] at hN
    omega
  have hproduct := Nat.mul_le_mul hN hrecord
  have hold := x.words_length
  have hnew := (x.inducedData vs).words_length
  have hsize := x.words_length_le_size
  omega

/-- Including the surviving vertex count, the induced input size is
still bounded by a fixed quadratic in the original size. -/
theorem gm06Induced_size_le (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).size ≤ 2 * x.size + x.size * (x.size + 2) := by
  have hwords := gm06Induced_words_length_le x vs
  have hvertices : (x.inducedData vs).n ≤ x.size := by
    rw [x.inducedData_n]
    exact ((List.length_filter_le _ _).trans_eq List.length_finRange).trans x.counts_le_size.1
  change (x.inducedData vs).n + (x.inducedData vs).words.length ≤ _
  omega

end GraphMinor.Compute
