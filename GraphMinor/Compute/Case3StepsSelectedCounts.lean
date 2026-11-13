module

public import GraphMinor.Compute.Case3StepsComponentOwner
public import GraphMinor.Compute.Case3StepsRoutedMember
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Counting private vertices and routed edges of selected members

Outside-core vertices occur in exactly one selected member. Directed
parallel classes are also assigned at most once, since selected labels are
distinct. These two counting bounds supply the sum of private contributions
in the running-time estimate of XIII (9.9), p. 106.
-/

public section

namespace GraphMinor.Compute

open scoped BigOperators

/-- The selected candidates form a finite type, independently of whether
any candidate is selected. -/
noncomputable instance instFintypeCase3SelectedGroup (x : Alg81Input) (Z : Finset (Fin x.n)) :
    Fintype (Case3SelectedGroup x Z) := Fintype.ofFinite _

/-- Distinct selected members have disjoint outside-core vertex sets. -/
theorem case3SelectedMember_outside_disjoint (x : Alg81Input) (Z : Finset (Fin x.n))
    (i j : Case3SelectedGroup x Z) (hne : i ≠ j) :
    Disjoint ((case3SelectedMember x Z i).verts \ Z) ((case3SelectedMember x Z j).verts \ Z) := by
  classical
  apply Finset.disjoint_left.mpr
  intro u hui huj
  have hi := (case3ComponentOwner_unique x Z u (Finset.mem_sdiff.mp hui).2 i).mp (Finset.mem_sdiff.mp hui).1
  have hj := (case3ComponentOwner_unique x Z u (Finset.mem_sdiff.mp hui).2 j).mp (Finset.mem_sdiff.mp huj).1
  exact hne (hi.trans hj.symm)

/-- The total private outside-core vertex contribution is at most the
number of compact compass vertices. -/
theorem case3SelectedMembers_sum_outside_card_le (x : Alg81Input) (Z : Finset (Fin x.n)) :
    (∑ i : Case3SelectedGroup x Z, ((case3SelectedMember x Z i).verts \ Z).card) ≤ x.n := by
  classical
  let f (i : Case3SelectedGroup x Z) := (case3SelectedMember x Z i).verts \ Z
  have hdisj : ((Finset.univ : Finset (Case3SelectedGroup x Z)) : Set (Case3SelectedGroup x Z)).PairwiseDisjoint f := by
    intro i _ j _ hij
    exact case3SelectedMember_outside_disjoint x Z i j hij
  have hcard := Finset.card_biUnion hdisj
  calc
    _ = (Finset.univ.biUnion f).card := hcard.symm
    _ ≤ Fintype.card (Fin x.n) := Finset.card_le_univ _
    _ = x.n := Fintype.card_fin _

private theorem routed_pair_sum_le (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (u v : Fin x.n) :
    (∑ i : Case3SelectedGroup x Z, (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).edgeMult u v) ≤
      D.edgeMult u v := by
  classical
  by_cases h : ∃ i : Case3SelectedGroup x Z, case3PairOwner x Z u v = case3RawIndexLabel x i.1
  · obtain ⟨i, hi⟩ := h
    have htest (j : Case3SelectedGroup x Z) :
        case3PairOwner x Z u v = case3RawIndexLabel x j.1 ↔ j = i := by
      constructor
      · intro hj
        exact Subtype.ext (case3RawIndexLabel_injective x (hj.symm.trans hi))
      · rintro rfl
        exact hi
    simp only [case3RoutedMember, htest]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, le_refl]
  · have hn : ∀ i : Case3SelectedGroup x Z, ¬ case3PairOwner x Z u v = case3RawIndexLabel x i.1 := by
      intro i hi
      exact h ⟨i, hi⟩
    simp only [case3RoutedMember, hn, ↓reduceIte, Finset.sum_const_zero, Nat.zero_le]

/-- Restoring the full multiplicity at its selected owner never counts a
directed copy twice. The total member edge count is at most the input count. -/
theorem case3SelectedMembers_sum_numEdges_le (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) :
    (∑ i : Case3SelectedGroup x Z, (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numEdges) ≤ D.numEdges := by
  classical
  change (∑ i : Case3SelectedGroup x Z, ∑ u : Fin x.n, ∑ v : Fin x.n,
      (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).edgeMult u v) ≤
    ∑ u : Fin x.n, ∑ v : Fin x.n, D.edgeMult u v
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro u _
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun v _ => routed_pair_sum_le x D Z u v)

/-- A selected member's vertex count splits into its private outside
vertices and its boundary key, exactly as in the page 106 estimate. -/
theorem case3SelectedMember_card_eq_outside_add_boundary (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) :
    (case3SelectedMember x Z i).verts.card = ((case3SelectedMember x Z i).verts \ Z).card +
      (case3GroupBoundary x Z i.1).card := by
  have h := Finset.card_sdiff_add_card_inter (case3SelectedMember x Z i).verts Z
  rw [case3SelectedMember_inter_core] at h
  exact h.symm

end GraphMinor.Compute
