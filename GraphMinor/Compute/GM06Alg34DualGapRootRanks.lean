module

public import GraphMinor.Compute.GM06Alg34DualGapRootProg

/-!
# Counting and numbering the canonical dual gap roots

The sum of the root mask is exactly the number of retained canonical
dual gap representatives. Its exclusive prefix sums give their order
among all supplied gap labels. The RAM computes these counts from
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
theorem gm06GapRootMask_sum (x : GM06DrawingData) (L : List (Fin x.n)) :
    (gm06GapRootMask x L).sum = (gm06ClassRoots (x.dualGapRelated L)).length := by
  rw [gm06GapRootMask, List.ofFn_eq_map]
  exact root_indicator_sum (List.finRange L.length) (gm06GapIsRoot x L)

/-- The number of canonical roots is at most the supplied gap count. -/
theorem gm06GapRootMask_sum_le (x : GM06DrawingData) (L : List (Fin x.n)) :
    (gm06GapRootMask x L).sum ≤ L.length := by
  rw [gm06GapRootMask_sum]
  change (List.filter (gm06GapIsRoot x L) (List.finRange L.length)).length ≤ L.length
  exact (List.length_filter_le _ _).trans_eq List.length_finRange

/-- Compute root ranks in array 46 and the root count in register 275. -/
def gm06GapRootRanksProg : Cmd := alg99BucketStartProg 45 46 274

/-- Root numbering takes linear time and returns exactly the number
of classes of the supplied dual gap relation. -/
theorem gm06GapRootRanksProg_exec {w : ℕ} (x : GM06DrawingData) (L : List (Fin x.n))
    (hw : 1 < 2 ^ w) (hN : L.length < 2 ^ w)
    {s : State} (hmask : s.arrs 45 = gm06GapRootMask x L) :
    ∃ s' t, Exec w gm06GapRootRanksProg s s' t ∧ t ≤ 23 * L.length + 8 ∧
      s'.arrs 46 = List.ofFn (fun a : Fin L.length => ((gm06GapRootMask x L).take a.val).sum) ∧
      s'.regs 275 = (gm06ClassRoots (x.dualGapRelated L)).length ∧
      (∀ k : ℕ, k ≠ 46 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 274 → q ≠ 275 → s'.regs q = s.regs q) := by
  have hlen : (gm06GapRootMask x L).length = L.length := by simp [gm06GapRootMask]
  obtain ⟨s', t, hex, ht, hout, htotal, harr, hreg⟩ :=
    alg99BucketStartProg_exec (gm06GapRootMask x L) 45 46 274 (by decide) hw
      (by simpa only [hlen] using hN) ((gm06GapRootMask_sum_le x L).trans_lt hN) s hmask
  refine ⟨s', t, hex, by simpa only [hlen] using ht, ?_,
    htotal.trans (gm06GapRootMask_sum x L), harr, hreg⟩
  rw [hout]
  apply List.ext_getElem (by simp [hlen])
  intro i hi hi'
  simp only [List.getElem_ofFn]

end GraphMinor.Compute
