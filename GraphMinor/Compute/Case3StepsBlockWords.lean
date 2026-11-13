module

public import GraphMinor.Compute.Case3StepsBranchRecordWords

/-!
# Word bounds for completed case (iii) blocks

The parser checks bound the record headers, parents, and leaf labels.
Compass and member labels lie in the ambient vertex range, and a parallel
copy number is below the ambient edge count. Together with the fixed wall
headers, these facts bound every serialized word independently of unused
words in a returned branch code.
-/

public section

namespace GraphMinor.Compute

/-- Valid wall encodings have bounded label and length words. -/
theorem case3Wall_encList_words {w h n : ℕ} {D : MultiDigraph n}
    (W : WallOfHeight h D) (hW : W.IsValid) (hn : n < 2 ^ w)
    (hh : h < 2 ^ w) (hv : elemWallNumVerts h < 2 ^ w)
    (he : (elemWallEdges h).length < 2 ^ w) :
    ∀ z ∈ W.encList, z < 2 ^ w := by
  intro z hz
  simp only [WallOfHeight.encList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with ((rfl | rfl | rfl) | hz) | hz
  · exact hh
  · exact hv
  · exact he
  · obtain ⟨u, _, rfl⟩ := List.mem_map.mp hz
    exact (W.branchVert u).2.trans hn
  · obtain ⟨k, _, hz⟩ := List.mem_flatMap.mp hz
    rcases List.mem_cons.mp hz with rfl | hz
    · have hl := (WallOfHeight.nodup_internalVerts_of_isValid hW k).length_le_card
      rw [Fintype.card_fin] at hl
      exact hl.trans_lt hn
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      exact v.2.trans hn

/-- Parser-valid member records have bounded serialized words using only
the compass label bounds and the ambient size bounds. -/
theorem case3ValidMemberRecord_words {w N m : ℕ} (Kv : List ℕ)
    (Ke : List (ℕ × ℕ × ℕ)) (r : Case3MemberRecord)
    (hvalid : isValidMemberRecord N m Kv Ke r = true)
    (hN : N < 2 ^ w) (hm : m < 2 ^ w) (ht : 2 * m + 1 < 2 ^ w)
    (hKv : ∀ x ∈ Kv, x < 2 ^ w)
    (hKe : ∀ a ∈ Ke, a.1 < 2 ^ w ∧ a.2.1 < 2 ^ w ∧ a.2.2 < 2 ^ w) :
    ∀ x ∈ r.enc, x < 2 ^ w := by
  simp only [isValidMemberRecord, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hvalid
  rcases hvalid with ⟨hvlen, _, hvsub, helen, _, hesub, htpos, htlen, hplen,
    hroot, hparent, _, hτ⟩
  have htw : r.t_len < 2 ^ w := lt_of_le_of_lt htlen (lt_of_le_of_lt (by omega) ht)
  have hvw : ∀ x ∈ r.vList, x < 2 ^ w := fun x hx => hKv x (hvsub x hx)
  have hew := case3EncEdgeTriples_words_lt r.eList (fun a ha => hKe a (hesub a ha).1)
  have hpw : ∀ x ∈ r.parList, x < 2 ^ w := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [← List.getD_eq_getElem _ 0 hi]
    by_cases hi0 : i = 0
    · subst i
      exact hroot.trans htw
    · have hit : i < r.t_len := by omega
      exact (hparent i (List.mem_range.mpr hit) (by omega)).trans (hit.trans htw)
  have hτw : ∀ x ∈ r.tauList, x < 2 ^ w := fun x hx => (hτ x hx).trans htw
  intro x hx
  simp only [Case3MemberRecord.enc, List.mem_append, List.mem_cons] at hx
  rcases hx with ((rfl | hx) | (rfl | hx)) | ((rfl | hx) | hx)
  · exact hvlen.trans_lt hN
  · exact hvw x hx
  · exact helen.trans_lt hm
  · exact hew x hx
  · exact htw
  · exact hpw x hx
  · exact hτw x hx

/-- Every word of a parsed block is bounded by its ambient counts and the
three fixed wall headers. -/
theorem case3ParsedBlock_words {w N : ℕ} (G : MultiDigraph N) (X : Finset (Fin N))
    (p : ParsedCase3Block (G.deleteVertices X) X)
    (hN : N < 2 ^ w) (hm : (G.deleteVertices X).numEdges < 2 ^ w)
    (ht : 2 * (G.deleteVertices X).numEdges + 1 < 2 ^ w)
    (hc : N + (G.deleteVertices X).numEdges + 1 < 2 ^ w)
    (hh : p.wallSec.h < 2 ^ w) (hv : elemWallNumVerts p.wallSec.h < 2 ^ w)
    (he : (elemWallEdges p.wallSec.h).length < 2 ^ w) :
    ∀ z ∈ encCase3Block p.wallSec.W p.K_vList p.K_eList p.corners p.members, z < 2 ^ w := by
  have hKv : ∀ z ∈ p.K_vList, z < 2 ^ w := by
    intro z hz
    have hmem := isDelGraphVert_eq_true_iff (G := G) |>.mp (p.hK_v_valid z hz)
    exact ((mem_vertexSet_delGraph_iff G X z).mp hmem).choose.trans hN
  have hKe : ∀ a ∈ p.K_eList, a.1 < 2 ^ w ∧ a.2.1 < 2 ^ w ∧ a.2.2 < 2 ^ w := by
    intro a ha
    have hb := isDelGraphEdge_eq_true_iff_mem_toGMDigraph.mp (p.hK_e_valid a ha).1
    rcases a with ⟨u, v, q⟩
    obtain ⟨hu, hv', hq⟩ := hb
    exact ⟨hu.trans hN, hv'.trans hN,
      (hq.trans_le ((G.deleteVertices X).edgeMult_le_numEdges ⟨u, hu⟩ ⟨v, hv'⟩)).trans hm⟩
  have hcorners : ∀ z ∈ p.corners, z < 2 ^ w := fun z hz => hKv z (p.hcorners_mem z hz)
  intro z hz
  simp only [encCase3Block, List.mem_append, List.mem_cons] at hz
  rcases hz with (((hz | (rfl | hz)) | (rfl | hz)) | hz) | (rfl | hz)
  · exact case3Wall_encList_words p.wallSec.W p.wallSec.hW hN hh hv he z hz
  · exact p.hK_v_len.trans_lt hN
  · exact hKv z hz
  · exact p.hK_e_len.trans_lt hm
  · exact case3EncEdgeTriples_words_lt _ hKe z hz
  · exact hcorners z hz
  · exact p.hmembers_len.trans_lt hc
  · obtain ⟨r, hr, hz⟩ := List.mem_flatMap.mp hz
    exact case3ValidMemberRecord_words _ _ r (p.hmembers_valid r hr) hN hm ht hKv hKe z hz

end GraphMinor.Compute
