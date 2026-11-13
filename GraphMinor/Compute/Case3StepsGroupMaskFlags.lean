module

public import GraphMinor.Compute.Case3StepsGroupMask
public import GraphMinor.Compute.Case3StepsSelfFlagsProg

/-!
# The two self-label blocks of the selected-group mask

The representative arrays supply exactly the source labels of the generic
flag scans. Their words are bounded by the vertex count or the combined
candidate count, and their self-label flags are the two blocks of the
selected-group bitset.
-/

public section

namespace GraphMinor.Compute

/-- Component representative words fit whenever the vertex-count sentinel fits. -/
theorem case3ComponentRepList_words {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (hn : x.n < 2 ^ w) : ∀ z ∈ case3ComponentRepList x Z, z < 2 ^ w := by
  intro z hz
  change z ∈ List.ofFn (fun u => if u ∈ Z then x.n else case3ComponentRepresentative x Z u) at hz
  obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hz
  split_ifs
  · exact hn
  · exact (case3FirstIndex_le _).trans_lt hn

/-- Core-edge representative words fit whenever the common sentinel fits. -/
theorem case3CoreEdgeRepList_words {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) :
    ∀ z ∈ case3CoreEdgeRepList x Z, z < 2 ^ w := by
  intro z hz
  change z ∈ List.ofFn (case3CoreEdgeRepEntry x Z) at hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  exact (case3CoreEdgeRepEntry_le x Z j).trans_lt hsize

private theorem component_selfFlags (x : Alg81Input) (Z : Finset (Fin x.n)) :
    case3SelfFlagList (case3ComponentRepList x Z) 0 =
      List.ofFn (fun u : Fin x.n => if case3ComponentRepEntry x Z u = u.1 then 1 else 0) := by
  apply List.ext_getElem (by rw [case3SelfFlagList_length, case3ComponentRepList_length, List.length_ofFn])
  intro j hj hj'
  have hjn : j < x.n := by
    rw [case3SelfFlagList_length, case3ComponentRepList_length] at hj
    exact hj
  rw [getElem_case3SelfFlagList _ 0 j (by rw [case3ComponentRepList_length]; exact hjn)]
  simp only [case3ComponentRepList, List.getElem_ofFn, case3ComponentRepEntry, Nat.zero_add]
  congr 1

private theorem coreEdge_selfFlags (x : Alg81Input) (Z : Finset (Fin x.n)) :
    case3SelfFlagList (case3CoreEdgeRepList x Z) x.n =
      List.ofFn (fun j : Fin (case3InputEdges x).length =>
        if case3CoreEdgeRepEntry x Z j = x.n + j.1 then 1 else 0) := by
  apply List.ext_getElem (by rw [case3SelfFlagList_length, case3CoreEdgeRepList_length, List.length_ofFn])
  intro j hj hj'
  have hjm : j < (case3InputEdges x).length := by
    rw [case3SelfFlagList_length, case3CoreEdgeRepList_length] at hj
    exact hj
  rw [getElem_case3SelfFlagList _ x.n j (by rw [case3CoreEdgeRepList_length]; exact hjm)]
  simp only [case3CoreEdgeRepList, List.getElem_ofFn]

/-- Concatenating the two label scans gives exactly the selected-group mask. -/
theorem case3GroupMaskList_eq_selfFlags (x : Alg81Input) (Z : Finset (Fin x.n)) :
    case3GroupMaskList x Z =
      case3SelfFlagList (case3ComponentRepList x Z) 0 ++
        case3SelfFlagList (case3CoreEdgeRepList x Z) x.n := by
  rw [component_selfFlags, coreEdge_selfFlags]
  rfl

end GraphMinor.Compute
