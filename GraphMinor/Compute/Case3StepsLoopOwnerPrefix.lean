module

public import GraphMinor.Compute.Case3StepsOrderedLoopOwner
public import GraphMinor.Compute.Case3StepsFirstSeen
public import GraphMinor.Compute.Case3StepsRecordOwnerProg

/-!
# The loop-owner table during the member scan

Each vertex stores the first containing selected member encountered so far.
A selected member changes precisely its still-missing entries. An unselected
candidate changes none. At the end the table gives the ordered loop
assignment used to restore multigraph edges.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Loop-owner words after visiting the candidate labels below `k`. -/
noncomputable def case3LoopOwnerPrefix (x : Alg81Input) (Z : Finset (Fin x.n))
    (k : ℕ) : List ℕ :=
  List.ofFn (fun u : Fin x.n => case3FirstSeen (case3GroupContains x Z u) k)

/-- There is one loop-owner word for every vertex. -/
theorem case3LoopOwnerPrefix_length (x : Alg81Input) (Z : Finset (Fin x.n)) (k : ℕ) :
    (case3LoopOwnerPrefix x Z k).length = x.n := by
  simp only [case3LoopOwnerPrefix, List.length_ofFn]

/-- All owner words initially hold the missing sentinel. -/
theorem case3LoopOwnerPrefix_zero (x : Alg81Input) (Z : Finset (Fin x.n)) :
    case3LoopOwnerPrefix x Z 0 = List.replicate x.n (x.n + (case3InputEdges x).length) := by
  apply List.ext_getElem (by simp [case3LoopOwnerPrefix_length])
  intro j hj hj'
  simp only [case3LoopOwnerPrefix, List.getElem_ofFn, case3FirstSeen, List.getElem_replicate]

/-- An owner word is the first successful containing-member label seen so far. -/
theorem case3LoopOwnerPrefix_getD (x : Alg81Input) (Z : Finset (Fin x.n)) (k : ℕ)
    (u : Fin x.n) :
    (case3LoopOwnerPrefix x Z k).getD u.1 0 =
      case3FirstSeen (case3GroupContains x Z u) k := by
  rw [List.getD_eq_getElem _ 0 (by rw [case3LoopOwnerPrefix_length]; exact u.2)]
  simp only [case3LoopOwnerPrefix, List.getElem_ofFn]

/-- A selected member produces precisely the next prefix of the owner table. -/
theorem case3LoopOwnerPrefix_selected (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) :
    case3RecordOwnerList (case3SelectedMember x Z i).verts
      (case3LoopOwnerPrefix x Z (case3RawIndexLabel x i.1))
      (case3RawIndexLabel x i.1) (x.n + (case3InputEdges x).length) =
      case3LoopOwnerPrefix x Z (case3RawIndexLabel x i.1 + 1) := by
  classical
  apply List.ext_getElem (by simp [case3RecordOwnerList, case3LoopOwnerPrefix_length])
  intro j hj hj'
  have hju : j < x.n := by simpa only [case3RecordOwnerList, List.length_ofFn] using hj
  let u : Fin x.n := ⟨j, hju⟩
  have htest := case3GroupContains_selected x Z u i
  have hq : (⟨case3RawIndexLabel x i.1, case3RawIndexLabel_lt x i.1⟩ :
      Fin (x.n + (case3InputEdges x).length)) = case3GroupLabelEquiv x i.1 := by
    apply Fin.ext
    exact (case3GroupLabelEquiv_val x i.1).symm
  simp only [case3RecordOwnerList, List.getElem_ofFn]
  rw [case3LoopOwnerPrefix_getD x Z (case3RawIndexLabel x i.1) u]
  simp only [case3LoopOwnerPrefix, List.getElem_ofFn]
  change (if u ∈ (case3SelectedMember x Z i).verts ∧
      case3FirstSeen (case3GroupContains x Z u) (case3RawIndexLabel x i.1) =
        x.n + (case3InputEdges x).length then case3RawIndexLabel x i.1 else
      case3FirstSeen (case3GroupContains x Z u) (case3RawIndexLabel x i.1)) =
    case3FirstSeen (case3GroupContains x Z u) (case3RawIndexLabel x i.1 + 1)
  simp only [case3FirstSeen, case3RawIndexLabel_lt, ↓reduceDIte, hq, htest, and_comm]

/-- Every partial owner word is bounded by the missing sentinel. -/
theorem case3LoopOwnerPrefix_words (x : Alg81Input) (Z : Finset (Fin x.n))
    (k : ℕ) (hk : k ≤ x.n + (case3InputEdges x).length) :
    ∀ z ∈ case3LoopOwnerPrefix x Z k, z ≤ x.n + (case3InputEdges x).length := by
  intro z hz
  obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hz
  exact (case3FirstSeen_invariant (case3GroupContains x Z u) k hk).1

/-- An unselected candidate cannot become a loop owner. -/
theorem case3LoopOwnerPrefix_unselected (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3RawIndex x) (hi : ¬ case3GroupActive x Z i) :
    case3LoopOwnerPrefix x Z (case3RawIndexLabel x i + 1) =
      case3LoopOwnerPrefix x Z (case3RawIndexLabel x i) := by
  classical
  apply List.ext_getElem (by simp only [case3LoopOwnerPrefix_length])
  intro j hj hj'
  have hq : (⟨case3RawIndexLabel x i, case3RawIndexLabel_lt x i⟩ :
      Fin (x.n + (case3InputEdges x).length)) = case3GroupLabelEquiv x i := by
    apply Fin.ext
    exact (case3GroupLabelEquiv_val x i).symm
  simp only [case3LoopOwnerPrefix, List.getElem_ofFn, case3FirstSeen,
    case3RawIndexLabel_lt, ↓reduceDIte]
  have hfalse (u : Fin x.n) : ¬ case3GroupContains x Z u (case3GroupLabelEquiv x i) := by
    simp only [case3GroupContains, Equiv.symm_apply_apply, hi, false_and, not_false_eq_true]
  simp only [hq, hfalse, and_false, ↓reduceIte]

/-- The completed table contains the numeric labels of the ordered loop owners. -/
theorem case3LoopOwnerPrefix_done (x : Alg81Input) (Z : Finset (Fin x.n)) :
    case3LoopOwnerPrefix x Z (x.n + (case3InputEdges x).length) =
      List.ofFn (case3OrderedLoopLabel x Z) := by
  apply List.ext_getElem (by simp [case3LoopOwnerPrefix_length])
  intro j hj hj'
  simp only [case3LoopOwnerPrefix, List.getElem_ofFn, case3FirstSeen_done, case3OrderedLoopLabel]

end GraphMinor.Compute
