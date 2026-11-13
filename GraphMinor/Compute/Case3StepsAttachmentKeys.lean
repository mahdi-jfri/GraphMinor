module

public import GraphMinor.Compute.Case3StepsBoundaryKeys

/-!
# The table of attachment keys

The table stores one four-word key per vertex, in seed order. Core seeds
have the empty-set key. Component seeds with the same attachment set have
the same key, so grouping these keys implements the equivalence relation
in the description of XIII (8.6), page 96.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The attachment-key table in vertex order. -/
noncomputable def case3AttachmentKeys (x : Alg81Input) (Z : Finset (Fin x.n)) : List ℕ :=
  (List.finRange x.n).flatMap (fun u => case3BoundaryKey (case3AttachmentRowSet x Z u))

/-- The first `k` keys occupy four words per seed. -/
theorem case3AttachmentKeys_prefix_length (x : Alg81Input) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d) (k : ℕ) (hk : k ≤ x.n) :
    (((List.finRange x.n).take k).flatMap
      (fun u => case3BoundaryKey (case3AttachmentRowSet x d.core.Z u))).length = k * 4 := by
  have haux : ∀ L : List (Fin x.n),
      (L.flatMap (fun u => case3BoundaryKey (case3AttachmentRowSet x d.core.Z u))).length = L.length * 4 := by
    intro L
    induction L with
    | nil => rfl
    | cons u L ih =>
      rw [List.flatMap_cons, List.length_append,
        case3BoundaryKey_length _ (case3AttachmentRowSet_card_le_three x d hd u), ih,
        List.length_cons, Nat.add_mul]
      omega
  rw [haux, List.length_take, List.length_finRange, Nat.min_eq_left hk]

/-- The next prefix appends exactly one attachment key. -/
theorem case3AttachmentKeys_prefix_succ (x : Alg81Input) (Z : Finset (Fin x.n))
    (k : ℕ) (hk : k < x.n) :
    (((List.finRange x.n).take (k + 1)).flatMap
      (fun u => case3BoundaryKey (case3AttachmentRowSet x Z u))) =
      (((List.finRange x.n).take k).flatMap
        (fun u => case3BoundaryKey (case3AttachmentRowSet x Z u))) ++
          case3BoundaryKey (case3AttachmentRowSet x Z ⟨k, hk⟩) := by
  have hget : (List.finRange x.n)[k]'(by simpa only [List.length_finRange] using hk) = ⟨k, hk⟩ := by
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.val_cast]
  rw [take_add_one_eq_append_getElem (List.finRange x.n) k (by simpa only [List.length_finRange] using hk)]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, hget]

/-- Before the next write, split off the four zero slots for that seed. -/
theorem case3AttachmentKeys_storage_succ (x : Alg81Input) (Z : Finset (Fin x.n))
    (k : ℕ) (hk : k < x.n) :
    (((List.finRange x.n).take k).flatMap
      (fun u => case3BoundaryKey (case3AttachmentRowSet x Z u))) ++
        List.replicate ((x.n - k) * 4) 0 =
      (((List.finRange x.n).take k).flatMap
        (fun u => case3BoundaryKey (case3AttachmentRowSet x Z u))) ++
          List.replicate 4 0 ++ List.replicate ((x.n - (k + 1)) * 4) 0 := by
  rw [show x.n - k = 1 + (x.n - (k + 1)) by omega, Nat.add_mul, Nat.one_mul,
    List.replicate_add, List.append_assoc]

/-- At the last seed the completed prefix is the whole table. -/
theorem case3AttachmentKeys_storage_done (x : Alg81Input) (Z : Finset (Fin x.n)) :
    (((List.finRange x.n).take x.n).flatMap
      (fun u => case3BoundaryKey (case3AttachmentRowSet x Z u))) ++
        List.replicate ((x.n - x.n) * 4) 0 = case3AttachmentKeys x Z := by
  simp only [Nat.sub_self, Nat.zero_mul, List.replicate_zero, List.append_nil]
  rw [List.take_of_length_le (by simp only [List.length_finRange]; exact le_rfl)]
  rfl

end GraphMinor.Compute
