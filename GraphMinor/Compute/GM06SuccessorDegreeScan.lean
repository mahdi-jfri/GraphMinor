module

public import GraphMinor.Compute.GM06UnpackSuccessor
public import GraphMinor.Compute.GM06DegreeOneScan

/-!
# Loading and scanning the initial cuff

Load the ordinary finite instance of VI (5.7), page 133, then query
valencies on its initial cuff. Length prefixes ensure that the row
lengths fit in a machine word whenever the input words do. The result
is a flag and, when set, a position of valency one in the supplied
endpoint list. The input array is preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Every entry of a field row occurs in the row-list code. -/
theorem gm06RowWord_mem_code {rows : List (List ℕ)} {row : List ℕ} {v : ℕ}
    (hr : row ∈ rows) (hv : v ∈ row) : v ∈ gm06EncodeRows rows := by
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  exact ⟨row, hr, List.mem_cons_of_mem _ hv⟩

/-- Every field length occurs as a prefix word of the row-list code. -/
theorem gm06RowLength_mem_code {rows : List (List ℕ)} {row : List ℕ}
    (hr : row ∈ rows) : row.length ∈ gm06EncodeRows rows := by
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  exact ⟨row, hr, List.mem_cons_self⟩

/-- A word bound on a row-list code bounds both field lengths and entries. -/
theorem gm06Row_word_bounds {rows : List (List ℕ)} {row : List ℕ} {b : ℕ}
    (hr : row ∈ rows) (hw : ∀ v ∈ gm06EncodeRows rows, v < b) :
    row.length < b ∧ ∀ v ∈ row, v < b :=
  ⟨hw _ (gm06RowLength_mem_code hr), fun v hv => hw v (gm06RowWord_mem_code hr hv)⟩

/-- Load the finite cylinder input and scan its initial cuff for valency one. -/
def gm06SuccessorDegreeScanProg : Cmd :=
  .seq gm06UnpackSuccessorProg (gm06DegreeOneScanProg 3 6)

/-- The composed front end returns the correct initial-cuff incidence test. -/
theorem gm06SuccessorDegreeScanProg_exec {w : ℕ} (x : GM06SuccessorInput) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs 0 = gm06EncodeSuccessorInput x)
    (hn : (gm06EncodeSuccessorInput x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06EncodeSuccessorInput x, v < 2 ^ w) :
    ∃ s' t, Exec w gm06SuccessorDegreeScanProg s s' t ∧
      t ≤ 10 + 22 * (gm06EncodeSuccessorInput x).length +
        x.innerCuff.length * (24 + 14 * x.endpoints.length) ∧
      s'.arrs 0 = s.arrs 0 ∧
      ((s'.regs 27 = 0 ∧ ∀ j (hj : j < x.innerCuff.length),
          x.endpoints.count x.innerCuff[j] ≠ 1) ∨
        (s'.regs 27 = 1 ∧ ∃ (j : ℕ) (hj : j < x.innerCuff.length),
          s'.regs 28 = j ∧ x.endpoints.count x.innerCuff[j] = 1)) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hf, _, hs⟩ := gm06UnpackSuccessorProg_exec x s hw ha hn hwords
  have hends : s₁.arrs 3 = x.endpoints := by
    simpa only [gm06SuccessorRows, List.getElem_cons_succ, List.getElem_cons_zero,
      Nat.reduceAdd, gm06SuccessorFieldArray, Nat.reduceLT, ite_true, ite_false] using hf ⟨1, by decide⟩
  have hcuff : s₁.arrs 6 = x.innerCuff := by
    simpa only [gm06SuccessorRows, List.getElem_cons_succ, List.getElem_cons_zero,
      Nat.reduceAdd, gm06SuccessorFieldArray, Nat.reduceLT, ite_true, ite_false] using hf ⟨3, by decide⟩
  have hbounds : ∀ row ∈ gm06SuccessorRows x,
      row.length < 2 ^ w ∧ ∀ v ∈ row, v < 2 ^ w := by
    intro row hr
    exact gm06Row_word_bounds hr hwords
  have heBounds := hbounds x.endpoints (by simp [gm06SuccessorRows])
  have hcBounds := hbounds x.innerCuff (by simp [gm06SuccessorRows])
  obtain ⟨s₂, t₂, he₂, ht₂, hk, hd⟩ := gm06DegreeOneScanProg_exec 3 6 x.endpoints
    x.innerCuff s₁ hw heBounds.1 hcBounds.1 heBounds.2 hcBounds.2 hends hcuff
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, ?_, hd⟩
  · omega
  · exact (hk.2 0 (by simp)).trans hs

end GraphMinor.Compute
