module

public import GraphMinor.Compute.GM06Alg34RootReach
public import GraphMinor.Compute.Algorithm99OrderPrefix

/-!
# Prefix counts of complement component marks

An exclusive prefix sum counts the reached labels below each packed
label. Its value at the BFS source is zero exactly when no smaller
label belongs to that component. The verified prefix-sum scan computes
these counts from the BFS marks in linear time.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Component marks have exactly one entry per supplied cell. -/
theorem gm06ComplementReachData_length (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) : (gm06ComplementReachData x vs a).length = x.cellCount := by
  simp only [gm06ComplementReachData, List.length_ofFn]

/-- The sum of the component's zero-one marks is at most the cell count. -/
theorem gm06ComplementReachData_sum_le (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) : (gm06ComplementReachData x vs a).sum ≤ x.cellCount := by
  have hb : ∀ v ∈ gm06ComplementReachData x vs a, v ≤ 1 := by
    intro v hv
    obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hv
    split <;> omega
  simpa only [gm06ComplementReachData_length, smul_eq_mul, Nat.mul_one] using
    List.sum_le_length_nsmul (gm06ComplementReachData x vs a) 1 hb

/-- A zero prefix count at the source means no smaller cell is reachable. -/
theorem gm06ComplementReachData_prefix_zero_iff (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) :
    ((gm06ComplementReachData x vs a).take a.val).sum = 0 ↔
      ∀ b : Fin x.cellCount, b < a → ¬ (x.complementGraph vs).Reachable a b := by
  have hlen := gm06ComplementReachData_length x vs a
  rw [List.sum_eq_zero_iff]
  constructor
  · intro h b hba hab
    have hmem : (gm06ComplementReachData x vs a)[b.val]'(by rw [hlen]; exact b.isLt) ∈
        (gm06ComplementReachData x vs a).take a.val := by
      apply List.mem_take_iff_getElem.mpr
      exact ⟨b.val, by rw [hlen]; exact lt_min hba b.isLt, rfl⟩
    have hz := h _ hmem
    simp only [gm06ComplementReachData, List.getElem_ofFn, hab, ↓reduceIte] at hz
    exact Nat.one_ne_zero hz
  · intro h v hv
    obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp hv
    have hjN : j < x.cellCount := by rw [hlen] at hj; exact (lt_min_iff.mp hj).2
    have hjA : j < a.val := (lt_min_iff.mp hj).1
    have hnot := h ⟨j, hjN⟩ hjA
    rw [← he]
    simp only [gm06ComplementReachData, List.getElem_ofFn, hnot, ↓reduceIte]

/-- Compute exclusive component prefix counts in array 35, with scratch
registers 197 and 198. -/
def gm06ReachRanksProg : Cmd := alg99BucketStartProg 33 35 197

/-- The component prefix-count scan is linear, preserves all other
arrays, and records the exact exclusive sums. -/
theorem gm06ReachRanksProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    {s : State} (hmarks : s.arrs 33 = gm06ComplementReachData x vs a) :
    ∃ s' t, Exec w gm06ReachRanksProg s s' t ∧ t ≤ 23 * x.cellCount + 8 ∧
      s'.arrs 35 = List.ofFn (fun b : Fin x.cellCount =>
        ((gm06ComplementReachData x vs a).take b.val).sum) ∧
      (∀ k : ℕ, k ≠ 35 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 197 → q ≠ 198 → s'.regs q = s.regs q) := by
  obtain ⟨s', t, hex, ht, hout, _, harr, hreg⟩ :=
    alg99BucketStartProg_exec (gm06ComplementReachData x vs a) 33 35 197 (by decide) hw
      (by simpa only [gm06ComplementReachData_length] using hN)
      ((gm06ComplementReachData_sum_le x vs a).trans_lt hN) s hmarks
  refine ⟨s', t, hex, by simpa only [gm06ComplementReachData_length] using ht, ?_, harr, hreg⟩
  rw [hout]
  apply List.ext_getElem (by simp [gm06ComplementReachData_length])
  intro i hi hi'
  simp only [List.getElem_ofFn]

end GraphMinor.Compute
