module

public import GraphMinor.Compute.GM06Alg34DualGapRowProg
public import GraphMinor.Compute.GM06Alg34FiniteClasses
public import GraphMinor.Compute.Algorithm99OrderPrefix

/-!
# Prefix counts in a dual gap class

Count the related labels below each gap. The count at the source is
zero precisely when that source is the least member of its class. The
verified exclusive prefix scan computes these counts from the row bits.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test a gap for being the least label in its dual class. -/
def gm06GapIsRoot (x : GM06DrawingData) (L : List (Fin x.n))
    (a : Fin L.length) : Bool :=
  decide (∀ b : Fin L.length, b < a → x.dualGapRelated L a b = false)

/-- The numeric root test selects precisely the canonical class roots. -/
theorem gm06GapIsRoot_iff (x : GM06DrawingData) (L : List (Fin x.n))
    (a : Fin L.length) :
    gm06GapIsRoot x L a = true ↔ a ∈ gm06ClassRoots (x.dualGapRelated L) := by
  rw [gm06MemClassRoots_iff]
  simp only [gm06GapIsRoot, decide_eq_true_eq]

/-- A relation row has one entry per supplied gap. -/
theorem gm06GapRow_length (x : GM06DrawingData) (L : List (Fin x.n))
    (a : Fin L.length) : (gm06GapRow x L a).length = L.length := by
  simp only [gm06GapRow, List.length_ofFn]

/-- The sum of a zero-one relation row is at most its length. -/
theorem gm06GapRow_sum_le (x : GM06DrawingData) (L : List (Fin x.n))
    (a : Fin L.length) : (gm06GapRow x L a).sum ≤ L.length := by
  have hb : ∀ v ∈ gm06GapRow x L a, v ≤ 1 := by
    intro v hv
    obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hv
    split <;> omega
  simpa only [gm06GapRow_length, smul_eq_mul, Nat.mul_one] using
    List.sum_le_length_nsmul (gm06GapRow x L a) 1 hb

/-- The prefix count is zero exactly when no smaller gap is related. -/
theorem gm06GapRow_prefix_zero_iff (x : GM06DrawingData) (L : List (Fin x.n))
    (a : Fin L.length) :
    ((gm06GapRow x L a).take a.val).sum = 0 ↔ gm06GapIsRoot x L a = true := by
  rw [gm06GapIsRoot, decide_eq_true_eq, List.sum_eq_zero_iff]
  have hlen := gm06GapRow_length x L a
  constructor
  · intro h b hba
    have hm : (gm06GapRow x L a)[b.val]'(by rw [hlen]; exact b.isLt) ∈
        (gm06GapRow x L a).take a.val := by
      apply List.mem_take_iff_getElem.mpr
      exact ⟨b.val, by rw [hlen]; exact lt_min hba b.isLt, rfl⟩
    have hz := h _ hm
    simp only [gm06GapRow, List.getElem_ofFn] at hz
    cases hr : x.dualGapRelated L a b with
    | false => rfl
    | true => simp only [hr, ↓reduceIte] at hz; cases hz
  · intro h v hv
    obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp hv
    have hjN : j < L.length := by rw [hlen] at hj; exact (lt_min_iff.mp hj).2
    have hjA : j < a.val := (lt_min_iff.mp hj).1
    have hn := h ⟨j, hjN⟩ hjA
    rw [← he]
    simp [gm06GapRow, List.getElem_ofFn, hn]

/-- Compute the exclusive relation counts in array 44. -/
def gm06GapRanksProg : Cmd := alg99BucketStartProg 43 44 270

/-- The linear prefix scan records the exact relation counts. -/
theorem gm06GapRanksProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (a : Fin L.length) (hw : 1 < 2 ^ w)
    (hk : L.length < 2 ^ w) {s : State} (hrow : s.arrs 43 = gm06GapRow x L a) :
    ∃ s' t, Exec w gm06GapRanksProg s s' t ∧ t ≤ 23 * L.length + 8 ∧
      s'.arrs 44 = List.ofFn (fun b : Fin L.length =>
        ((gm06GapRow x L a).take b.val).sum) ∧
      (∀ A : ℕ, A ≠ 44 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 270 → q ≠ 271 → s'.regs q = s.regs q) := by
  obtain ⟨s', t, he, ht, hout, _, harr, hreg⟩ :=
    alg99BucketStartProg_exec (gm06GapRow x L a) 43 44 270 (by decide) hw
      (by simpa only [gm06GapRow_length] using hk)
      ((gm06GapRow_sum_le x L a).trans_lt hk) s hrow
  refine ⟨s', t, he, by simpa only [gm06GapRow_length] using ht, ?_, harr, hreg⟩
  rw [hout]
  apply List.ext_getElem (by simp [gm06GapRow_length])
  intro i hi hi'
  simp only [List.getElem_ofFn]

end GraphMinor.Compute
