module

public import GraphMinor.Compute.GM06Alg34EdgeMaskData
public import GraphMinor.Compute.GM06Alg34LabelList
public import GraphMinor.Compute.Algorithm99OrderPrefix

/-!
# Numbering surviving edges on the RAM

Apply the same exclusive prefix-sum pass to the surviving-edge mask.
Its total is the new edge count, and each surviving old edge receives
the count of surviving edges before it. Array 7 stores these ranks.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The new numbering table for the original supplied edge labels. -/
def gm06EdgeRanks (x : GM06DrawingData) (vs : List (Fin x.n)) : List ℕ :=
  List.ofFn (fun e : Fin x.ends.length => ((gm06EdgeMask x vs).take e.val).sum)

/-- The total mask sum is exactly the number of surviving old edge labels. -/
theorem gm06EdgeMask_sum (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (gm06EdgeMask x vs).sum = (x.activeEdges vs).length := by
  rw [gm06EdgeMask, List.ofFn_eq_map]
  have hh := List.sum_map_ite (fun e => x.activeCell vs (.inr (.inl e)) = true)
    (fun _ => (1 : ℕ)) (fun _ => (0 : ℕ)) (List.finRange x.ends.length)
  simpa [GM06DrawingData.activeEdges] using hh

/-- The edge mask sum is bounded by the supplied edge count. -/
theorem gm06EdgeMask_sum_le (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (gm06EdgeMask x vs).sum ≤ x.ends.length := by
  rw [gm06EdgeMask_sum]
  exact (List.length_filter_le _ _).trans_eq (List.length_finRange)

/-- Build edge ranks in array 7, with total in register 137. -/
def gm06EdgeRanksProg : Cmd := alg99BucketStartProg 6 7 136

/-- Computing edge ranks takes linear time and preserves all arrays
other than the rank table, including the supplied input and both masks. -/
theorem gm06EdgeRanksProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (hw : 1 < 2 ^ w) (hm : x.ends.length < 2 ^ w)
    {s : State} (hmask : s.arrs 6 = gm06EdgeMask x vs) :
    ∃ s' t, Exec w gm06EdgeRanksProg s s' t ∧ t ≤ 23 * x.ends.length + 8 ∧
      s'.arrs 7 = gm06EdgeRanks x vs ∧ s'.regs 137 = (x.activeEdges vs).length ∧
      (∀ a : ℕ, a ≠ 7 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 136 → q ≠ 137 → s'.regs q = s.regs q) := by
  have hlen : (gm06EdgeMask x vs).length = x.ends.length := by simp [gm06EdgeMask]
  obtain ⟨s', t, hex, ht, hout, htotal, ha, hr⟩ :=
    alg99BucketStartProg_exec (gm06EdgeMask x vs) 6 7 136 (by decide) hw
      (hlen ▸ hm) ((gm06EdgeMask_sum_le x vs).trans_lt hm) s hmask
  refine ⟨s', t, hex, by simpa only [hlen] using ht, ?_, ?_, ha, hr⟩
  · rw [hout]
    apply List.ext_getElem (by simp [gm06EdgeRanks, hlen])
    intro i hi hi'
    simp only [gm06EdgeRanks, List.getElem_ofFn]
  · simpa only [gm06EdgeMask_sum] using htotal

end GraphMinor.Compute
