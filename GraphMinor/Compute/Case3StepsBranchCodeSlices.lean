module

public import GraphMinor.Compute.Case3StepsBranchRecord

/-!
# Locating the two lists in a branch code

The branch code consists of its two header words, its parent list, and its
leaf list. Its exact length makes the two slices exact, including the empty
parent list in the at-most-one-edge case. Nontrivial records copy the parent
slice, while every record copies the leaf slice.
-/

public section

namespace GraphMinor.Compute

/-- A valid branch code splits at exactly its declared parent and leaf lengths. -/
theorem case3BranchCode_slices {n B : ℕ} (G : MultiDigraph n) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) :
    code = [bdNumTreeVerts code, G.numEdges] ++
      (code.drop 2).take (bdNumTreeVerts code) ++ code.drop (2 + bdNumTreeVerts code) ∧
      ((code.drop 2).take (bdNumTreeVerts code)).length = bdNumTreeVerts code ∧
      (code.drop (2 + bdNumTreeVerts code)).length = G.numEdges := by
  have hm := hcode.1
  have hlen := hcode.2.2.1
  rw [hm] at hlen
  cases code with
  | nil => simp only [List.length_nil, bdNumTreeVerts, List.getD_nil] at hlen; omega
  | cons a tail =>
    cases tail with
    | nil => simp only [List.length_cons, List.length_nil, bdNumTreeVerts, List.getD_cons_zero] at hlen; omega
    | cons b rest =>
      have hb : b = G.numEdges := hm
      simp only [bdNumTreeVerts, List.getD_cons_zero] at hlen ⊢
      have hr : rest.length = a + G.numEdges := by
        simp only [List.length_cons] at hlen
        omega
      rw [← List.drop_drop]
      simp only [List.drop_succ_cons, List.drop_zero]
      change a :: b :: rest = [a, G.numEdges] ++ (rest.take a) ++ rest.drop a ∧
        (rest.take a).length = a ∧ (rest.drop a).length = G.numEdges
      refine ⟨?_, ?_, ?_⟩
      · rw [hb, List.append_assoc, List.take_append_drop]
        rfl
      · rw [List.length_take, hr, Nat.min_eq_left (by omega)]
      · rw [List.length_drop, hr]
        omega

/-- For a nontrivial code, the record's parent list is exactly its contiguous
parent slice in the supplied output. -/
theorem case3BranchRecord_parent_slice {n B : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) (ht : 0 < bdNumTreeVerts code) :
    (case3BranchRecord G f g code).parList = (code.drop 2).take (bdNumTreeVerts code) := by
  have hmax := Nat.max_eq_left ht
  have hs := case3BranchCode_slices G code hcode
  apply List.ext_getElem (by simpa only [case3BranchRecord, List.length_ofFn, hmax] using hs.2.1.symm)
  intro i hi hi'
  have hit : i < bdNumTreeVerts code := by simpa only [hs.2.1] using hi'
  rw [← List.getD_eq_getElem _ 0 hi, case3BranchRecord_parent G f g code ht i hit,
    List.getElem_take, List.getElem_drop]
  exact List.getD_eq_getElem _ _ _

/-- The record's leaf list is exactly the supplied code's final slice. -/
theorem case3BranchRecord_tau_slice {n B : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) :
    (case3BranchRecord G f g code).tauList = code.drop (2 + bdNumTreeVerts code) := by
  have hs := case3BranchCode_slices G code hcode
  apply List.ext_getElem (by simpa only [case3BranchRecord, List.length_ofFn] using hs.2.2.symm)
  intro i hi hi'
  have him : i < G.numEdges := by simpa only [hs.2.2] using hi'
  rw [← List.getD_eq_getElem _ 0 hi, case3BranchRecord_tau_word G f g code ⟨i, him⟩,
    List.getElem_drop]
  exact List.getD_eq_getElem _ _ _

end GraphMinor.Compute
