module

public import GraphMinor.Compute.Case3StepsBranchRecord

/-!
# Bounds on copied branch records

Validity of the supplied branch code gives the parent and leaf bounds
required by the case (iii) block parser. The at-most-one-edge convention
becomes a one-vertex placeholder, while every other tree is copied exactly.
The record length is linear in the member's vertices and directed edges.
-/

public section

namespace GraphMinor.Compute

/-- A valid branch code supplies every tree-list bound checked by the
case (iii) parser, including its one-vertex convention for small graphs. -/
theorem case3BranchRecord_tree_bounds {n B : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) :
    let r := case3BranchRecord G f g code
    1 ≤ r.t_len ∧ r.t_len ≤ 2 * r.eList.length + 1 ∧
      r.parList.getD 0 0 < r.t_len ∧
      (∀ z, 0 < z → z < r.t_len → r.parList.getD z 0 < z) ∧
      (∀ u ∈ r.tauList, u < r.t_len) := by
  classical
  let r := case3BranchRecord G f g code
  rcases hcode with ⟨hm, htle, _, hcase⟩
  have hsize : r.t_len ≤ 2 * r.eList.length + 1 := by
    change max (bdNumTreeVerts code) 1 ≤ 2 * (G.multiEdgeTriples.map g).length + 1
    rw [List.length_map, G.length_multiEdgeTriples]
    rw [hm] at htle
    exact max_le (by omega) (by omega)
  refine ⟨Nat.le_max_right _ _, hsize, ?_, ?_, ?_⟩
  · rcases hcase with ⟨_, ht0, _⟩ | ⟨_, ht, hp0, _⟩
    · change (List.ofFn (fun z : Fin (max (bdNumTreeVerts code) 1) =>
        if z.1 < bdNumTreeVerts code then bdParent code z.1 else 0)).getD 0 0 < max (bdNumTreeVerts code) 1
      simp only [ht0, Nat.zero_max, List.ofFn_succ, List.ofFn_zero,
        List.getD_cons_zero, Nat.not_lt_zero, ↓reduceIte]
      decide
    · change (case3BranchRecord G f g code).parList.getD 0 0 < max (bdNumTreeVerts code) 1
      rw [case3BranchRecord_parent G f g code ht 0 ht]
      change code.getD (2 + 0) 0 < _
      rw [Nat.add_zero, hp0]
      exact lt_of_lt_of_le ht (Nat.le_max_left _ _)
  · intro z hz hzlen
    by_cases ht : 0 < bdNumTreeVerts code
    · have hzl : z < bdNumTreeVerts code := by
        change z < max (bdNumTreeVerts code) 1 at hzlen
        rwa [Nat.max_eq_left ht] at hzlen
      rw [case3BranchRecord_parent G f g code ht z hzl]
      rcases hcase with ⟨_, ht0, _⟩ | ⟨_, _, _, hp, _⟩
      · omega
      · exact hp z hz hzl
    · have ht0 : bdNumTreeVerts code = 0 := by omega
      change z < max (bdNumTreeVerts code) 1 at hzlen
      rw [ht0, Nat.zero_max] at hzlen
      omega
  · intro u hu
    obtain ⟨e, he⟩ := List.mem_ofFn.mp hu
    subst u
    change code.getD (2 + bdNumTreeVerts code + e.1) 0 < max (bdNumTreeVerts code) 1
    rcases hcase with ⟨_, ht0, htau⟩ | ⟨_, ht, _, _, htau, _⟩
    · rw [ht0, Nat.add_zero, htau e.1 (by rw [hm]; exact e.2)]
      exact Nat.zero_lt_one
    · exact lt_of_lt_of_le (htau e) (Nat.le_max_left _ _)

/-- Each expanded edge triple occupies three words in a member record. -/
theorem case3Length_encEdgeTriples (es : List (ℕ × ℕ × ℕ)) :
    (encEdgeTriples es).length = 3 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [encEdgeTriples, List.length_cons, ih]; omega

/-- Serializing the record adds only the vertex list, four words per edge,
and at most twice the edge count plus one tree words. -/
theorem case3BranchRecord_enc_length_le {n B : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) :
    (case3BranchRecord G f g code).enc.length ≤ n + 6 * G.numEdges + 4 := by
  have htree := (case3BranchRecord_tree_bounds G f g code hcode).2.1
  simp only [case3BranchRecord, List.length_map, G.length_multiEdgeTriples] at htree
  simp only [Case3MemberRecord.enc, case3BranchRecord, List.length_cons,
    List.length_append, List.length_map, List.length_finRange, List.length_ofFn,
    case3Length_encEdgeTriples, List.length_map, G.length_multiEdgeTriples]
  omega

end GraphMinor.Compute
