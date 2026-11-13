module

public import GraphMinor.Compute.GM06Alg34DualPayloadSections
import Mathlib.Tactic.Ring

/-!
# Space bounds for the computed finite dual payload

Each transposed region record contains at most every old region and
every old edge. Each canonical dual block contains at most every old
gap. Summing these finite scans gives a quadratic payload bound. A
quartic reservation therefore contains the whole result and fits the
logarithmic words used by the constructor.
-/

public section
namespace GraphMinor.Compute

/-- One transposed region record contains at most all region and edge labels. -/
theorem gm06DualRegionRecordWords_length_le (x : GM06DrawingData) (v : Fin x.n) :
    (gm06DualRegionRecordWords x v).length ≤ 2 + x.regions.length + x.ends.length := by
  have hV := List.length_filter_le (fun r : Fin x.regions.length => decide (v ∈ x.regions[r].vertices))
    (List.finRange x.regions.length)
  have hE := List.length_filter_le (fun e : Fin x.ends.length => decide (x.ends[e].1 = v ∨ x.ends[e].2 = v))
    (List.finRange x.ends.length)
  simp only [List.length_finRange] at hV hE
  simp only [gm06DualRegionRecordWords, GM06DrawingData.listWords,
    GM06DrawingData.dualRegionVertices, GM06DrawingData.dualRegionEdges,
    List.length_append, List.length_cons, List.length_map]
  omega

/-- The transposed region section has one bounded record per source vertex. -/
theorem gm06DualRegionWords_length_le (x : GM06DrawingData) (V : List (Fin x.n)) :
    (gm06DualRegionWords x V).length ≤ V.length * (2 + x.regions.length + x.ends.length) := by
  induction V with
  | nil => simp only [gm06DualRegionWords, List.flatMap_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons v V ih =>
    have hv := gm06DualRegionRecordWords_length_le x v
    simp only [gm06DualRegionWords, List.flatMap_cons, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul] at *
    omega

/-- Each selected canonical class record contains at most all cuff gap labels. -/
theorem gm06DualSelectedClassWords_length_le (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) (i : Fin L.length) :
    (gm06DualSelectedClassWords x L g i).length ≤ 1 + L.length := by
  have hi := gm06DualGapClassWords_length_le x L g i
  cases hh : gm06GapIsRoot x L i <;>
    simp only [gm06DualSelectedClassWords, hh, Bool.false_eq_true, ↓reduceIte,
      GM06DrawingData.listWords, List.length_cons, List.length_nil] <;> omega

/-- The canonical class-record scan has a quadratic word bound. -/
theorem gm06DualDivisionRecordWords_length_le (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) (V : List (Fin L.length)) :
    (gm06DualDivisionRecordWords x L g V).length ≤ V.length * (1 + L.length) := by
  induction V with
  | nil => simp only [gm06DualDivisionRecordWords, List.filter_nil, List.flatMap_nil,
      List.length_nil, Nat.zero_mul, le_refl]
  | cons i V ih =>
    have hi := gm06DualSelectedClassWords_length_le x L g i
    rw [gm06DualDivisionRecordWords_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A complete finite dual payload is bounded by the two transposed
incidence products and the canonical gap-class product. -/
theorem gm06Dual_words_length_le (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualData L hR g).words.length ≤
      3 + 2 * x.ends.length + x.n * (2 + x.regions.length + x.ends.length) +
        2 + L.length + 1 + L.length * (1 + L.length) := by
  have he := congrArg List.length (gm06DualPayloadSections_eq x L hR g)
  have hend := gm06DualEndpointWords_length x hR (List.finRange x.ends.length)
  have hregion := gm06DualRegionWords_length_le x (List.finRange x.n)
  have hclass := gm06DualDivisionRecordWords_length_le x L g (List.finRange L.length)
  have hcount : (x.dualGapDivision L).length ≤ L.length := by
    simp only [GM06DrawingData.dualGapDivision, gm06ClassBlocks, List.length_map, gm06ClassRoots]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_ofFn] at he
  simp only [List.length_finRange] at hend hregion hclass
  omega

private theorem quadratic_budget (S : ℕ) :
    S + (3 + 2 * S + S * (2 + S + S) + 2 + S + 1 + S * (1 + S)) ≤ 10 * (S + 2) ^ 2 := by
  ring_nf
  omega

/-- With a cuff no longer than the input size, the complete dual size
has a quadratic bound in that original size. -/
theorem gm06Dual_size_le (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length)
    (hk : L.length ≤ x.size) :
    (x.dualData L hR g).size ≤ 10 * (x.size + 2) ^ 2 := by
  have hwords := gm06Dual_words_length_le x L hR g
  have hc := x.counts_le_size
  have hprod := Nat.mul_le_mul hc.1 (show
    2 + x.regions.length + x.ends.length ≤ 2 + x.size + x.size by omega)
  have hgap := Nat.mul_le_mul hk (show 1 + L.length ≤ 1 + x.size by omega)
  have hsum : (x.dualData L hR g).size ≤
      x.size + (3 + 2 * x.size + x.size * (2 + x.size + x.size) +
        2 + x.size + 1 + x.size * (1 + x.size)) := by
    change x.regions.length + (x.dualData L hR g).words.length ≤ _
    omega
  exact hsum.trans (quadratic_budget x.size)

private theorem quadratic_le_fourth (S : ℕ) (hS : 5 ≤ S) :
    10 * (S + 2) ^ 2 ≤ (S + 2) ^ 4 := by
  have hb : 7 ≤ S + 2 := by omega
  have hsq := Nat.mul_le_mul hb hb
  have h10 : 10 ≤ (S + 2) ^ 2 := by simpa only [Nat.pow_two] using (show 10 ≤ (S + 2) * (S + 2) by omega)
  calc
    10 * (S + 2) ^ 2 ≤ (S + 2) ^ 2 * (S + 2) ^ 2 := Nat.mul_le_mul_right _ h10
    _ = (S + 2) ^ 4 := by ring

/-- The quartic constructor reservation contains the entire finite dual size. -/
theorem gm06Dual_size_le_capacity (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length)
    (hk : L.length ≤ x.size) : (x.dualData L hR g).size ≤ (x.size + 2) ^ 4 := by
  have hS : 5 ≤ x.size := x.five_le_words_length.trans x.words_length_le_size
  exact (gm06Dual_size_le x L hR g hk).trans (quadratic_le_fourth x.size hS)

/-- The quartic reservation fits the constructor's logarithmic word size. -/
theorem gm06Dual_capacity_lt_wordSize (x : GM06DrawingData) {c : ℕ} (hc : 4 ≤ c) :
    (x.size + 2) ^ 4 < 2 ^ wordSize c x.size := by
  apply lt_two_pow_wordSize_of_lt_pow (by omega)
  exact Nat.pow_le_pow_right (by omega) hc

end GraphMinor.Compute
