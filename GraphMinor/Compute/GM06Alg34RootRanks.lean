module

public import GraphMinor.Compute.GM06Alg34RootMaskProg

/-!
# Counting and numbering the canonical region roots

The sum of the root mask is exactly the number of retained canonical
region representatives. Its exclusive prefix sums give their order
among all original packed labels. The RAM computes these counts from
the completed mask, with no information extracted from a drawing proof.
-/

@[expose] public section
namespace GraphMinor.Compute

private theorem root_indicator_sum {α : Type*} (L : List α) (p : α → Bool) :
    (L.map (fun a => if p a then (1 : ℕ) else 0)).sum = (L.filter p).length := by
  induction L with
  | nil => rfl
  | cons a L ih => cases hp : p a <;> simp [hp, ih, Nat.add_comm]

/-- The completed mask counts exactly the canonical representatives. -/
theorem gm06RootMask_sum (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (gm06RootMask x vs).sum = (x.regionRoots vs).length := by
  rw [gm06RootMask, List.ofFn_eq_map]
  exact root_indicator_sum (List.finRange x.cellCount) (x.isRegionRoot vs)

/-- The number of canonical roots is at most the supplied cell count. -/
theorem gm06RootMask_sum_le (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (gm06RootMask x vs).sum ≤ x.cellCount := by
  rw [gm06RootMask_sum]
  simpa only [GM06DrawingData.regionRoots, List.length_finRange] using List.length_filter_le (x.isRegionRoot vs) (List.finRange x.cellCount)

/-- Compute root ranks in array 37 and the root count in register 203. -/
def gm06RootRanksProg : Cmd := alg99BucketStartProg 36 37 202

/-- Root numbering takes linear time and returns exactly the number
of regions of the induced drawing payload. -/
theorem gm06RootRanksProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    {s : State} (hmask : s.arrs 36 = gm06RootMask x vs) :
    ∃ s' t, Exec w gm06RootRanksProg s s' t ∧ t ≤ 23 * x.cellCount + 8 ∧
      s'.arrs 37 = List.ofFn (fun a : Fin x.cellCount => ((gm06RootMask x vs).take a.val).sum) ∧
      s'.regs 203 = (x.regionRoots vs).length ∧
      (∀ k : ℕ, k ≠ 37 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 202 → q ≠ 203 → s'.regs q = s.regs q) := by
  have hlen : (gm06RootMask x vs).length = x.cellCount := by simp [gm06RootMask]
  obtain ⟨s', t, hex, ht, hout, htotal, harr, hreg⟩ :=
    alg99BucketStartProg_exec (gm06RootMask x vs) 36 37 202 (by decide) hw
      (by simpa only [hlen] using hN) ((gm06RootMask_sum_le x vs).trans_lt hN) s hmask
  refine ⟨s', t, hex, by simpa only [hlen] using ht, ?_,
    htotal.trans (gm06RootMask_sum x vs), harr, hreg⟩
  rw [hout]
  apply List.ext_getElem (by simp [hlen])
  intro i hi hi'
  simp only [List.getElem_ofFn]

end GraphMinor.Compute
