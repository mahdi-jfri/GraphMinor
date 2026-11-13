module

public import GraphMinor.Compute.Case3StepsBranchRecordWords
import Mathlib.Data.List.GetD

/-!
# The one-vertex record for noninterior members

Step (7) of XIII (9.9), p. 105, returns decompositions only for interior
members. The case (iii) format also lists the other division members. As
specified by that format, their record has tree size one, parent list
`[0]`, and a zero leaf word for every directed copy. A raw zero tree size
uses the record writer's normalization to give exactly these data.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Auxiliary code words producing the prescribed noninterior record. -/
def case3PlaceholderCode (m : ℕ) : List ℕ := [0, m] ++ List.replicate m 0

/-- The raw tree size normalizes to one in a member record. -/
theorem case3PlaceholderCode_tree (m : ℕ) : bdNumTreeVerts (case3PlaceholderCode m) = 0 := rfl

/-- The graph-edge header retains every directed copy. -/
theorem case3PlaceholderCode_edges (m : ℕ) : bdNumGraphEdges (case3PlaceholderCode m) = m := rfl

/-- All leaf words and the default beyond them are zero. -/
theorem case3PlaceholderCode_tail (m i : ℕ) : (case3PlaceholderCode m).getD (2 + i) 0 = 0 := by
  rw [show 2 + i = (i + 1) + 1 by omega]
  simp only [case3PlaceholderCode, List.cons_append, List.nil_append,
    List.getD_cons_succ]
  rw [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq]

/-- Every auxiliary code word fits the directed-copy count's word bound. -/
theorem case3PlaceholderCode_words {w m : ℕ} (hm : m < 2 ^ w) :
    ∀ z ∈ case3PlaceholderCode m, z < 2 ^ w := by
  intro z hz
  simp only [case3PlaceholderCode, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with (rfl | rfl) | hz
  · exact Nat.two_pow_pos _
  · exact hm
  · have hz0 := (List.mem_replicate.mp hz).2
    subst z
    exact Nat.two_pow_pos _

/-- The noninterior record has the exact tree fields required by the format. -/
theorem case3BranchRecord_placeholder_fields {n : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) :
    let r := case3BranchRecord G f g (case3PlaceholderCode G.numEdges)
    r.t_len = 1 ∧ r.parList = [0] ∧ r.tauList = List.replicate G.numEdges 0 := by
  refine ⟨by simp only [case3BranchRecord, case3PlaceholderCode_tree, Nat.zero_max], ?_, ?_⟩
  · simp only [case3BranchRecord, case3PlaceholderCode_tree, Nat.zero_max,
      Nat.not_lt_zero, ↓reduceIte, List.ofFn_const, List.replicate_succ, List.replicate_zero]
  · simp only [case3BranchRecord, case3PlaceholderCode_tree, Nat.add_zero,
      case3PlaceholderCode_tail, List.ofFn_const]

/-- The uniform serialized length when the tree and leaf lengths match
those in the record headers. -/
theorem case3MemberRecord_enc_length (r : Case3MemberRecord)
    (hp : r.parList.length = r.t_len) (ht : r.tauList.length = r.eList.length) :
    r.enc.length = r.vList.length + 4 * r.eList.length + r.t_len + 3 := by
  simp only [Case3MemberRecord.enc, List.length_cons, List.length_append,
    case3Length_encEdgeTriples, hp, ht]
  omega

/-- The noninterior record is linear in vertices and full edge copies. -/
theorem case3BranchRecord_placeholder_length {n : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) :
    (case3BranchRecord G f g (case3PlaceholderCode G.numEdges)).enc.length =
      n + 4 * G.numEdges + 4 := by
  let r := case3BranchRecord G f g (case3PlaceholderCode G.numEdges)
  have hlengths := case3BranchRecord_lengths G f g (case3PlaceholderCode G.numEdges)
  rw [case3MemberRecord_enc_length r hlengths.1 hlengths.2]
  simp only [r, case3BranchRecord, List.length_map, List.length_finRange,
    G.length_multiEdgeTriples, case3PlaceholderCode_tree, Nat.zero_max]

end GraphMinor.Compute
