module

public import GraphMinor.Compute.Case3StepsBranchRecordDataProg
import Mathlib.Data.List.GetD

/-!
# Word bounds for the renamed branch record

Original vertex labels fit in an original-vertex word, and copy numbers
are smaller than the member's total edge count. Parent and leaf words are
copied from the supplied code. The one-vertex convention adds only zero and
one, so every serialized record word fits under these same bounds.
-/

public section

namespace GraphMinor.Compute

/-- Reading past a bounded list adds only the zero default. -/
theorem case3GetD_word_lt {w : ℕ} (l : List ℕ) (hwords : ∀ x ∈ l, x < 2 ^ w) (i : ℕ) :
    l.getD i 0 < 2 ^ w := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hwords _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.two_pow_pos _

/-- Flattening bounded edge triples keeps every endpoint and copy number bounded. -/
theorem case3EncEdgeTriples_words_lt {w : ℕ} (es : List (ℕ × ℕ × ℕ))
    (hwords : ∀ e ∈ es, e.1 < 2 ^ w ∧ e.2.1 < 2 ^ w ∧ e.2.2 < 2 ^ w) :
    ∀ x ∈ encEdgeTriples es, x < 2 ^ w := by
  induction es with
  | nil => intro x hx; exact False.elim (List.not_mem_nil hx)
  | cons e es ih =>
    rcases e with ⟨u, v, k⟩
    intro x hx
    simp only [encEdgeTriples, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact (hwords _ List.mem_cons_self).1
    · exact (hwords _ List.mem_cons_self).2.1
    · exact (hwords _ List.mem_cons_self).2.2
    · exact ih (fun e he => hwords e (List.mem_cons_of_mem _ he)) x hx

/-- Every word of a renamed branch record fits using the member and original
size bounds and the checked words of the returned branch code. -/
theorem case3BranchRecord_enc_words_lt {w n N : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig) (code : List ℕ)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w) (he : G.numEdges < 2 ^ w)
    (hcodewords : ∀ x ∈ code, x < 2 ^ w) :
    ∀ x ∈ (case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code).enc,
      x < 2 ^ w := by
  let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
  have htw : bdNumTreeVerts code < 2 ^ w := case3GetD_word_lt code hcodewords 0
  have htreew : r.t_len < 2 ^ w := max_lt htw hw
  have hvlen : r.vList.length = n := by simp only [r, case3BranchRecord, List.length_map, List.length_finRange]
  have helen : r.eList.length = G.numEdges := by simp only [r, case3BranchRecord, List.length_map, G.length_multiEdgeTriples]
  have hvw : ∀ x ∈ r.vList, x < 2 ^ w := by
    rw [case3BranchRecord_orig_vList G orig hinj code]
    intro x hx
    obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hx
    exact (orig u).2.trans hN
  have hew : ∀ x ∈ encEdgeTriples r.eList, x < 2 ^ w := by
    apply case3EncEdgeTriples_words_lt
    intro e he'
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he'
    have hedge := (G.mem_multiEdgeTriples_iff e₀).mp he₀
    rcases e₀ with ⟨u, v, k⟩
    obtain ⟨hu, hv, hk⟩ := hedge
    change (origVertexEmb orig hinj u) < 2 ^ w ∧ (origVertexEmb orig hinj v) < 2 ^ w ∧ k < 2 ^ w
    rw [origVertexEmb_apply_val orig hinj ⟨u, hu⟩, origVertexEmb_apply_val orig hinj ⟨v, hv⟩]
    exact ⟨(orig ⟨u, hu⟩).2.trans hN, (orig ⟨v, hv⟩).2.trans hN,
      hk.trans_le (G.edgeMult_le_numEdges _ _) |>.trans he⟩
  have hpw : ∀ x ∈ r.parList, x < 2 ^ w := by
    intro x hx
    obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hx
    split_ifs
    · exact case3GetD_word_lt code hcodewords _
    · exact Nat.two_pow_pos _
  have hleafw : ∀ x ∈ r.tauList, x < 2 ^ w := by
    intro x hx
    obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hx
    exact case3GetD_word_lt code hcodewords _
  intro x hx
  change x ∈ r.enc at hx
  simp only [Case3MemberRecord.enc, List.mem_append, List.mem_cons] at hx
  rcases hx with ((rfl | hx) | (rfl | hx)) | ((rfl | hx) | hx)
  · rw [hvlen]; exact hn
  · exact hvw x hx
  · rw [helen]; exact he
  · exact hew x hx
  · exact htreew
  · exact hpw x hx
  · exact hleafw x hx

end GraphMinor.Compute
