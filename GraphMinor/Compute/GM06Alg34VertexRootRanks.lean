module

public import GraphMinor.Compute.GM06Alg34VertexRootMaskProg

/-!
# Counting and numbering the canonical component roots

The sum of the root mask is exactly the number of retained canonical
component representatives. Its exclusive prefix sums give their order
among all original vertex labels. The RAM computes these counts from
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
theorem gm06VertexRootMask_sum (x : GM06DrawingData)  :
    (gm06VertexRootMask x).sum = x.componentRoots.length := by
  rw [gm06VertexRootMask, List.ofFn_eq_map]
  exact root_indicator_sum (List.finRange x.n) x.isComponentRoot

/-- The number of canonical roots is at most the supplied cell count. -/
theorem gm06VertexRootMask_sum_le (x : GM06DrawingData)  :
    (gm06VertexRootMask x).sum ≤ x.n := by
  rw [gm06VertexRootMask_sum]
  simpa only [GM06DrawingData.componentRoots, List.length_finRange] using List.length_filter_le x.isComponentRoot (List.finRange x.n)

/-- Compute root ranks in array 37 and the root count in register 203. -/
def gm06VertexRootRanksProg : Cmd := alg99BucketStartProg 36 37 202

/-- Root numbering takes linear time and returns exactly the number
of components of the supplied drawing. -/
theorem gm06VertexRootRanksProg_exec {w : ℕ} (x : GM06DrawingData) 
    (hw : 1 < 2 ^ w) (hN : x.n < 2 ^ w)
    {s : State} (hmask : s.arrs 36 = gm06VertexRootMask x) :
    ∃ s' t, Exec w gm06VertexRootRanksProg s s' t ∧ t ≤ 23 * x.n + 8 ∧
      s'.arrs 37 = List.ofFn (fun a : Fin x.n => ((gm06VertexRootMask x).take a.val).sum) ∧
      s'.regs 203 = x.componentRoots.length ∧
      (∀ k : ℕ, k ≠ 37 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 202 → q ≠ 203 → s'.regs q = s.regs q) := by
  have hlen : (gm06VertexRootMask x).length = x.n := by simp [gm06VertexRootMask]
  obtain ⟨s', t, hex, ht, hout, htotal, harr, hreg⟩ :=
    alg99BucketStartProg_exec (gm06VertexRootMask x) 36 37 202 (by decide) hw
      (by simpa only [hlen] using hN) ((gm06VertexRootMask_sum_le x).trans_lt hN) s hmask
  refine ⟨s', t, hex, by simpa only [hlen] using ht, ?_,
    htotal.trans (gm06VertexRootMask_sum x), harr, hreg⟩
  rw [hout]
  apply List.ext_getElem (by simp [hlen])
  intro i hi hi'
  simp only [List.getElem_ofFn]

end GraphMinor.Compute
