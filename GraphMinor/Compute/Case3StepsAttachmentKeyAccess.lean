module

public import GraphMinor.Compute.Case3StepsAttachmentKeys

/-!
# Reading and comparing attachment keys

Each row has four words. Thus four row-major reads compare attachment sets
exactly, using the injectivity of the boundary-key encoding. These reads are
the constant-time tests used when merging component and core-edge members.
-/

public section

namespace GraphMinor.Compute

/-- Split the key table around one selected seed. -/
theorem case3AttachmentKeys_split (x : Alg81Input) (Z : Finset (Fin x.n)) (u : Fin x.n) :
    case3AttachmentKeys x Z =
      (((List.finRange x.n).take u.1).flatMap
        (fun v => case3BoundaryKey (case3AttachmentRowSet x Z v))) ++
      case3BoundaryKey (case3AttachmentRowSet x Z u) ++
      (((List.finRange x.n).drop (u.1 + 1)).flatMap
        (fun v => case3BoundaryKey (case3AttachmentRowSet x Z v))) := by
  conv_lhs =>
    unfold case3AttachmentKeys
    rw [← List.take_append_drop (u.1 + 1) (List.finRange x.n), List.flatMap_append,
      case3AttachmentKeys_prefix_succ x Z u.1 u.2]

/-- A word in the flat key table is the corresponding word in its seed's key. -/
theorem case3AttachmentKeys_getD (x : Alg81Input) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d) (u : Fin x.n) (j : Fin 4) :
    (case3AttachmentKeys x d.core.Z).getD (u.1 * 4 + j.1) 0 =
      (case3BoundaryKey (case3AttachmentRowSet x d.core.Z u)).getD j.1 0 := by
  let pre := ((List.finRange x.n).take u.1).flatMap
    (fun v => case3BoundaryKey (case3AttachmentRowSet x d.core.Z v))
  let suf := ((List.finRange x.n).drop (u.1 + 1)).flatMap
    (fun v => case3BoundaryKey (case3AttachmentRowSet x d.core.Z v))
  have hpre : pre.length = u.1 * 4 := case3AttachmentKeys_prefix_length x d hd u.1 u.2.le
  have heq : case3AttachmentKeys x d.core.Z =
      pre ++ case3BoundaryKey (case3AttachmentRowSet x d.core.Z u) ++ suf := by
    unfold case3AttachmentKeys
    rw [← List.take_append_drop (u.1 + 1) (List.finRange x.n), List.flatMap_append,
      case3AttachmentKeys_prefix_succ x d.core.Z u.1 u.2]
  rw [heq, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hpre,
    Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by
      rw [case3BoundaryKey_length _ (case3AttachmentRowSet_card_le_three x d hd u)]
      exact j.2)]

private theorem fourWords_eq_iff (L M : List ℕ) (hL : L.length = 4) (hM : M.length = 4) :
    (∀ j : Fin 4, L.getD j.1 0 = M.getD j.1 0) ↔ L = M := by
  constructor
  · intro h
    apply List.ext_getElem (hL.trans hM.symm)
    intro j hj hj'
    have hj4 : j < 4 := by rw [← hL]; exact hj
    have heq := h ⟨j, hj4⟩
    simpa only [List.getD_eq_getElem _ 0 hj, List.getD_eq_getElem _ 0 hj'] using heq
  · rintro rfl j
    rfl

/-- Four key-table reads test exactly whether a component has a given small
attachment set. -/
theorem case3AttachmentKeys_words_eq_iff (x : Alg81Input) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d) (u : Fin x.n)
    (bd : Finset (Fin x.n)) (hbd : bd.card ≤ 3) :
    (∀ j : Fin 4, (case3AttachmentKeys x d.core.Z).getD (u.1 * 4 + j.1) 0 =
      (case3BoundaryKey bd).getD j.1 0) ↔ case3AttachmentRowSet x d.core.Z u = bd := by
  simp only [case3AttachmentKeys_getD x d hd u]
  rw [fourWords_eq_iff _ _
    (case3BoundaryKey_length _ (case3AttachmentRowSet_card_le_three x d hd u))
    (case3BoundaryKey_length bd hbd)]
  exact ⟨case3BoundaryKey_injective _ _, fun h => congrArg case3BoundaryKey h⟩

end GraphMinor.Compute
