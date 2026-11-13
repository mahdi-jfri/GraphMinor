module

public import GraphMinor.Compute.GM06Alg34VertexBfs
public import GraphMinor.Compute.Algorithm99OrderPrefix

/-!
# Prefix counts of vertex component marks

An exclusive prefix sum counts the reached labels below each vertex
label. Its value at the BFS source is zero exactly when no smaller
label belongs to that component. The verified prefix-sum scan computes
these counts from the BFS marks in linear time.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Component marks have exactly one entry per supplied vertex. -/
theorem gm06VertexReachData_length (x : GM06DrawingData) (a : Fin x.n) : (gm06VertexReachData x a).length = x.n := by
  simp only [gm06VertexReachData, List.length_ofFn]

/-- The sum of the component's zero-one marks is at most the vertex count. -/
theorem gm06VertexReachData_sum_le (x : GM06DrawingData) (a : Fin x.n) : (gm06VertexReachData x a).sum ≤ x.n := by
  have hb : ∀ v ∈ gm06VertexReachData x a, v ≤ 1 := by
    intro v hv
    obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hv
    split <;> omega
  simpa only [gm06VertexReachData_length, smul_eq_mul, Nat.mul_one] using
    List.sum_le_length_nsmul (gm06VertexReachData x a) 1 hb

/-- A zero prefix count at the source means no smaller vertex is reachable. -/
theorem gm06VertexReachData_prefix_zero_iff (x : GM06DrawingData) (a : Fin x.n) :
    ((gm06VertexReachData x a).take a.val).sum = 0 ↔
      ∀ b : Fin x.n, b < a → ¬ x.vertexGraph.Reachable a b := by
  have hlen := gm06VertexReachData_length x a
  rw [List.sum_eq_zero_iff]
  constructor
  · intro h b hba hab
    have hmem : (gm06VertexReachData x a)[b.val]'(by rw [hlen]; exact b.isLt) ∈
        (gm06VertexReachData x a).take a.val := by
      apply List.mem_take_iff_getElem.mpr
      exact ⟨b.val, by rw [hlen]; exact lt_min hba b.isLt, rfl⟩
    have hz := h _ hmem
    simp only [gm06VertexReachData, List.getElem_ofFn, hab, ↓reduceIte] at hz
    exact Nat.one_ne_zero hz
  · intro h v hv
    obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp hv
    have hjN : j < x.n := by rw [hlen] at hj; exact (lt_min_iff.mp hj).2
    have hjA : j < a.val := (lt_min_iff.mp hj).1
    have hnot := h ⟨j, hjN⟩ hjA
    rw [← he]
    simp only [gm06VertexReachData, List.getElem_ofFn, hnot, ↓reduceIte]

/-- Compute exclusive component prefix counts in array 35, with scratch
registers 197 and 198. -/
def gm06VertexReachRanksProg : Cmd := alg99BucketStartProg 33 35 197

/-- The component prefix-count scan is linear, preserves all other
arrays, and records the exact exclusive sums. -/
theorem gm06VertexReachRanksProg_exec {w : ℕ} (x : GM06DrawingData) (a : Fin x.n) (hw : 1 < 2 ^ w) (hN : x.n < 2 ^ w)
    {s : State} (hmarks : s.arrs 33 = gm06VertexReachData x a) :
    ∃ s' t, Exec w gm06VertexReachRanksProg s s' t ∧ t ≤ 23 * x.n + 8 ∧
      s'.arrs 35 = List.ofFn (fun b : Fin x.n =>
        ((gm06VertexReachData x a).take b.val).sum) ∧
      (∀ k : ℕ, k ≠ 35 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 197 → q ≠ 198 → s'.regs q = s.regs q) := by
  obtain ⟨s', t, hex, ht, hout, _, harr, hreg⟩ :=
    alg99BucketStartProg_exec (gm06VertexReachData x a) 33 35 197 (by decide) hw
      (by simpa only [gm06VertexReachData_length] using hN)
      ((gm06VertexReachData_sum_le x a).trans_lt hN) s hmarks
  refine ⟨s', t, hex, by simpa only [gm06VertexReachData_length] using ht, ?_, harr, hreg⟩
  rw [hout]
  apply List.ext_getElem (by simp [gm06VertexReachData_length])
  intro i hi hi'
  simp only [List.getElem_ofFn]

end GraphMinor.Compute
