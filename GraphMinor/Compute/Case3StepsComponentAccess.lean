module

public import GraphMinor.Compute.Case3StepsComponentRows

/-!
# Reading the component table

The flat table stores a row per seed. An entry at the row-major index tests
membership in the corresponding outside component. The attachment computation
can therefore scan the graph's edges using these constant-time reads.
-/

public section

namespace GraphMinor.Compute

/-- Split the table into the preceding rows, one chosen row, and later rows. -/
theorem case3ComponentRows_split (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) :
    case3ComponentRows x Z =
      (((List.finRange x.n).take u.1).flatMap (case3ComponentRow x Z)) ++
        case3ComponentRow x Z u ++
          (((List.finRange x.n).drop (u.1 + 1)).flatMap (case3ComponentRow x Z)) := by
  conv_lhs =>
    unfold case3ComponentRows
    rw [← List.take_append_drop (u.1 + 1) (List.finRange x.n), List.flatMap_append,
      case3ComponentRows_prefix_succ x Z u.1 u.2]

/-- A row-major table read equals the read in the selected component row. -/
theorem case3ComponentRows_getD (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) :
    (case3ComponentRows x Z).getD (u.1 * x.n + v.1) 0 =
      (case3ComponentRow x Z u).getD v.1 0 := by
  let pre := ((List.finRange x.n).take u.1).flatMap (case3ComponentRow x Z)
  let suf := ((List.finRange x.n).drop (u.1 + 1)).flatMap (case3ComponentRow x Z)
  have hpre : pre.length = u.1 * x.n := case3ComponentRows_prefix_length x Z u.1 u.2.le
  have heq : case3ComponentRows x Z = pre ++ case3ComponentRow x Z u ++ suf := by
    unfold case3ComponentRows
    rw [← List.take_append_drop (u.1 + 1) (List.finRange x.n), List.flatMap_append,
      case3ComponentRows_prefix_succ x Z u.1 u.2]
  rw [heq, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hpre,
    Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by rw [case3ComponentRow_length]; exact v.2)]

/-- Outside the core, the row entry is the indicator of component membership. -/
theorem case3ComponentRows_getD_outside (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) (hu : u ∉ Z) :
    (case3ComponentRows x Z).getD (u.1 * x.n + v.1) 0 =
      if v ∈ compOutside x Z u then 1 else 0 := by
  rw [case3ComponentRows_getD]
  simp only [case3ComponentRow, hu, ↓reduceIte]
  rw [List.getD_eq_getElem _ 0 (by rw [length_bitSetList]; exact v.2)]
  exact getElem_bitSetList _ v.1 v.2

/-- Core rows contain only zeroes. -/
theorem case3ComponentRows_getD_core (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) (hu : u ∈ Z) :
    (case3ComponentRows x Z).getD (u.1 * x.n + v.1) 0 = 0 := by
  rw [case3ComponentRows_getD]
  simp only [case3ComponentRow, hu, ↓reduceIte, List.getD_replicate 0 v.2]

end GraphMinor.Compute
