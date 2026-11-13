module

public import GraphMinor.Compute.GM06Alg34VertexComponents

/-!
# The null and single-component cases of the finite driver

A valid division on an empty vertex range has no blocks and is feasible.
If a nonempty endpoint graph has at most one canonical component root,
every two vertices reach that same root and hence each other. These
facts justify the driver's acceptance and connected-dual branches.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

open Set GM06

/-- A valid finite division on a null graph is empty and feasible. -/
theorem feasible_of_n_eq_zero (x : GM06DrawingData) (hn : x.n = 0)
    (hD : IsDivision x.divisionSet) : IsFeasible x.graph x.divisionSet := by
  have he : x.divisionSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro A hA
    obtain ⟨v, _⟩ := hD.2.1 A hA
    have hv := v.isLt
    omega
  rw [he]
  exact isFeasible_empty x.graph

/-- A nonempty finite endpoint graph with at most one root is preconnected. -/
theorem preconnected_of_roots_length_le_one (x : GM06DrawingData)
    (hk : x.componentRoots.length ≤ 1) : x.vertexGraph.Preconnected := by
  intro a b
  obtain ⟨ra, hra, har⟩ := x.exists_componentRoot a
  obtain ⟨rb, hrb, hbr⟩ := x.exists_componentRoot b
  have he : ra = rb := by
    cases hl : x.componentRoots with
    | nil => rw [hl] at hra; exact False.elim (List.not_mem_nil hra)
    | cons r L =>
      have hL : L = [] := by
        have hh : (r :: L).length ≤ 1 := hl ▸ hk
        cases L with
        | nil => rfl
        | cons s M => simp only [List.length_cons] at hh; omega
      simp only [hl, hL, List.mem_singleton] at hra hrb
      exact hra.trans hrb.symm
  exact har.trans (he ▸ hbr.symm)

end GraphMinor.Compute.GM06DrawingData
