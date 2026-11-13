module

public import GraphMinor.Compute.Case3StepsSelectedCounts
public import GraphMinor.Compute.Case3StepsGroupMask
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Costs in the numeric candidate scan

The RAM scan uses contiguous candidate labels and skips unset mask bits.
The cost at a selected label is charged to its corresponding selected
member. Summing these numeric charges is exactly summing over the selected
members, so the page 106 estimates apply to the actual scan order.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- A selected member charge, extended by zero to every candidate label. -/
noncomputable def case3CandidateCost (x : Alg81Input) (Z : Finset (Fin x.n))
    (f : Case3SelectedGroup x Z → ℕ) (j : Fin (x.n + (case3InputEdges x).length)) : ℕ :=
  if h : case3GroupActive x Z ((case3GroupLabelEquiv x).symm j) then
    f ⟨(case3GroupLabelEquiv x).symm j, h⟩ else 0

/-- A selected candidate label receives exactly its member charge. -/
theorem case3CandidateCost_selected (x : Alg81Input) (Z : Finset (Fin x.n))
    (f : Case3SelectedGroup x Z → ℕ) (i : Case3SelectedGroup x Z) :
    case3CandidateCost x Z f (case3GroupLabelEquiv x i.1) = f i := by
  classical
  simp only [case3CandidateCost, Equiv.symm_apply_apply, i.2, ↓reduceDIte]

/-- Numeric scanning with zero charges for unselected candidates counts
exactly the selected-member sum. -/
theorem case3CandidateCost_sum (x : Alg81Input) (Z : Finset (Fin x.n))
    (f : Case3SelectedGroup x Z → ℕ) :
    (∑ j : Fin (x.n + (case3InputEdges x).length), case3CandidateCost x Z f j) =
      ∑ i : Case3SelectedGroup x Z, f i := by
  classical
  let g (i : Case3RawIndex x) := if h : case3GroupActive x Z i then f ⟨i, h⟩ else 0
  have hg : (∑ i : Case3SelectedGroup x Z, g i.1) = ∑ i : Case3SelectedGroup x Z, f i := by
    apply Finset.sum_congr rfl
    intro i _
    exact dite_eq_left i.2
  calc
    _ = ∑ i : Case3RawIndex x, g i :=
      Fintype.sum_equiv (case3GroupLabelEquiv x).symm _ _ (fun _ => rfl)
    _ = ∑ i : Case3SelectedGroup x Z, g i.1 := by
      rw [← Finset.sum_subtype (Finset.univ.filter (case3GroupActive x Z)) (by simp)]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : case3GroupActive x Z i
      · simp only [hi, ↓reduceIte]
      · simp only [g, hi, ↓reduceDIte, ↓reduceIte]
    _ = _ := hg

end GraphMinor.Compute
