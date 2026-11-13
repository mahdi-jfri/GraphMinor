module

public import GraphMinor.Compute.Case3StepsGroups
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The bitset of selected member labels

The two representative arrays use disjoint numeric ranges. Their entries
select a candidate exactly when its label is its own index. Concatenating
these tests gives the bitset used to scan the distinct merged members.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- The candidate sum type and the contiguous RAM label range are equivalent. -/
def case3GroupLabelEquiv (x : Alg81Input) :
    Case3RawIndex x ≃ Fin (x.n + (case3InputEdges x).length) := finSumFinEquiv

/-- The equivalence uses the labels stored by the representative programs. -/
theorem case3GroupLabelEquiv_val (x : Alg81Input) (i : Case3RawIndex x) :
    (case3GroupLabelEquiv x i).1 = case3RawIndexLabel x i := by cases i <;> rfl

/-- Selected candidates expressed as a set of contiguous labels. -/
noncomputable def case3GroupLabelSet (x : Alg81Input) (Z : Finset (Fin x.n)) :
    Finset (Fin (x.n + (case3InputEdges x).length)) :=
  (case3GroupSeeds x Z).image (case3GroupLabelEquiv x)

/-- Membership in the label set is exactly the self-representative test. -/
theorem mem_case3GroupLabelSet (x : Alg81Input) (Z : Finset (Fin x.n)) (i : Case3RawIndex x) :
    case3GroupLabelEquiv x i ∈ case3GroupLabelSet x Z ↔ case3GroupActive x Z i := by
  rw [case3GroupLabelSet, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    have heq := (case3GroupLabelEquiv x).injective hji
    subst j
    exact (mem_case3GroupSeeds x Z i).mp hj
  · intro hi
    exact ⟨i, (mem_case3GroupSeeds x Z i).mpr hi, rfl⟩

/-- Tests of the component labels followed by tests of the core-edge labels. -/
noncomputable def case3GroupMaskList (x : Alg81Input) (Z : Finset (Fin x.n)) : List ℕ :=
  List.ofFn (fun u : Fin x.n => if case3ComponentRepEntry x Z u = u.1 then 1 else 0) ++
    List.ofFn (fun j : Fin (case3InputEdges x).length =>
      if case3CoreEdgeRepEntry x Z j = x.n + j.1 then 1 else 0)

/-- The mask has one word per candidate label. -/
theorem case3GroupMaskList_length (x : Alg81Input) (Z : Finset (Fin x.n)) :
    (case3GroupMaskList x Z).length = x.n + (case3InputEdges x).length := by
  simp only [case3GroupMaskList, List.length_append, List.length_ofFn]

/-- At a candidate's numeric label the mask is its selection bit. -/
theorem case3GroupMaskList_getD (x : Alg81Input) (Z : Finset (Fin x.n)) (i : Case3RawIndex x) :
    (case3GroupMaskList x Z).getD (case3RawIndexLabel x i) 0 =
      if case3GroupActive x Z i then 1 else 0 := by
  cases i with
  | inl u =>
    unfold case3GroupMaskList
    change List.getD (_ ++ _) u.1 (0 : ℕ) = _
    rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact u.2)]
    rw [List.getD_eq_getElem _ 0 (by simp only [List.length_ofFn]; exact u.2)]
    simp only [List.getElem_ofFn, case3GroupActive]
    congr 1
  | inr j =>
    unfold case3GroupMaskList
    change List.getD (_ ++ _) (x.n + j.1) (0 : ℕ) = _
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega),
      List.length_ofFn, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ 0 (by simp only [List.length_ofFn]; exact j.2)]
    simp only [List.getElem_ofFn, case3GroupActive]
    congr 1

/-- The computed mask format is precisely the bitset of selected groups. -/
theorem case3GroupMaskList_eq_bitSetList (x : Alg81Input) (Z : Finset (Fin x.n)) :
    case3GroupMaskList x Z = bitSetList (case3GroupLabelSet x Z) := by
  apply List.ext_getElem (by rw [case3GroupMaskList_length, length_bitSetList])
  intro j hj hj'
  have hjL : j < x.n + (case3InputEdges x).length := by
    rw [← case3GroupMaskList_length x Z]
    exact hj
  let q : Fin (x.n + (case3InputEdges x).length) := ⟨j, hjL⟩
  let i := (case3GroupLabelEquiv x).symm q
  have hq : case3GroupLabelEquiv x i = q := Equiv.apply_symm_apply _ _
  have hval : case3RawIndexLabel x i = j := by
    rw [← case3GroupLabelEquiv_val, hq]
  have hbit := case3GroupMaskList_getD x Z i
  rw [hval, List.getD_eq_getElem _ 0 hj] at hbit
  rw [getElem_bitSetList _ j hjL]
  have hmem := mem_case3GroupLabelSet x Z i
  rw [hq] at hmem
  change (case3GroupMaskList x Z)[j] = if q ∈ case3GroupLabelSet x Z then 1 else 0
  simpa only [hmem] using hbit

end GraphMinor.Compute
