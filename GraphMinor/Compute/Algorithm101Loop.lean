module

public import GraphMinor.Compute.Algorithm101Interior
public import GraphMinor.Compute.Algorithm101Menger

/-!
# Member Iteration Loop for Graph Minors XIII, Algorithm (10.1)

This file assembles the per-member subroutines from `Algorithm101TildeA`, `Algorithm101Member`,
`Algorithm101Step2`, `Algorithm101Step3`, `Algorithm101Interior`, and `Algorithm101Menger` into
the complete member iteration body (`alg101MemberStepProg`) of **Graph Minors XIII,
Algorithm (10.1)** (Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), pages 106–107):
1. Concrete array (`a101_* p`) and register (`r101_*`) layout and member record validity lemmas.
2. Part A (`alg101MemberStep14Prog`): stream read, interior check, and Steps 1 & 4.
3. Part B (`alg101MemberStep2Prog`): Step 2 $\tilde{A}$ vertex and edge list construction.
4. Part C (`alg101MemberStep3AndAppendProg`): Step 3 folio code, buffer append, and summary writes.
5. Combined per-member step (`alg101MemberStepProg` and `alg101MemberStepProg_exec`).
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-! ### Section 1: Concrete Memory Layout and Member Record Validity -/

macro "a101_G" p:term:max : term => `(alg105ArrBase $p + 0)
macro "a101_X" p:term:max : term => `(alg105ArrBase $p + 1)
macro "a101_visBuf" p:term:max : term => `(alg105ArrBase $p + 2)
macro "a101_block" p:term:max : term => `(alg105ArrBase $p + 3)
macro "a101_xSeq" p:term:max : term => `(alg105ArrBase $p + 4)
macro "a101_xInd" p:term:max : term => `(alg105ArrBase $p + 5)
macro "a101_W_br" p:term:max : term => `(alg105ArrBase $p + 6)
macro "a101_W_brOf" p:term:max : term => `(alg105ArrBase $p + 7)
macro "a101_W_edgeOf" p:term:max : term => `(alg105ArrBase $p + 8)
macro "a101_perim" p:term:max : term => `(alg105ArrBase $p + 9)
macro "a101_WH" p:term:max : term => `(alg105ArrBase $p + 10)
macro "a101_KV" p:term:max : term => `(alg105ArrBase $p + 11)
macro "a101_KE" p:term:max : term => `(alg105ArrBase $p + 12)
macro "a101_corners" p:term:max : term => `(alg105ArrBase $p + 13)
macro "a101_KInd" p:term:max : term => `(alg105ArrBase $p + 14)
macro "a101_isCorner" p:term:max : term => `(alg105ArrBase $p + 15)
macro "a101_degK" p:term:max : term => `(alg105ArrBase $p + 16)
macro "a101_start" p:term:max : term => `(alg105ArrBase $p + 17)
macro "a101_end" p:term:max : term => `(alg105ArrBase $p + 18)
macro "a101_entries" p:term:max : term => `(alg105ArrBase $p + 19)
macro "a101_owner" p:term:max : term => `(alg105ArrBase $p + 20)
macro "a101_memIsInt" p:term:max : term => `(alg105ArrBase $p + 21)
macro "a101_memVOf" p:term:max : term => `(alg105ArrBase $p + 22)
macro "a101_memFolioCode" p:term:max : term => `(alg105ArrBase $p + 23)
macro "a101_rV" p:term:max : term => `(alg105ArrBase $p + 24)
macro "a101_rE" p:term:max : term => `(alg105ArrBase $p + 25)
macro "a101_rPar" p:term:max : term => `(alg105ArrBase $p + 26)
macro "a101_rTau" p:term:max : term => `(alg105ArrBase $p + 27)
macro "a101_degR" p:term:max : term => `(alg105ArrBase $p + 28)
macro "a101_bList" p:term:max : term => `(alg105ArrBase $p + 29)
macro "a101_sSeq" p:term:max : term => `(alg105ArrBase $p + 30)
macro "a101_P1" p:term:max : term => `(alg105ArrBase $p + 31)
macro "a101_P2" p:term:max : term => `(alg105ArrBase $p + 32)
macro "a101_P3" p:term:max : term => `(alg105ArrBase $p + 33)
macro "a101_vOfPath" p:term:max : term => `(alg105ArrBase $p + 34)
macro "a101_sInd" p:term:max : term => `(alg105ArrBase $p + 35)
macro "a101_tildeV" p:term:max : term => `(alg105ArrBase $p + 36)
macro "a101_tildeE" p:term:max : term => `(alg105ArrBase $p + 37)
macro "a101_zA" p:term:max : term => `(alg105ArrBase $p + 38)
macro "a101_vIdx" p:term:max : term => `(alg105ArrBase $p + 39)
macro "a101_mult" p:term:max : term => `(alg105ArrBase $p + 40)
macro "a101_buf" p:term:max : term => `(alg105ArrBase $p + 41)
macro "a101_folioWords" p:term:max : term => `(alg105ArrBase $p + 42)
macro "a101_Q0" p:term:max : term => `(alg105ArrBase $p + 43)
macro "a101_Q1" p:term:max : term => `(alg105ArrBase $p + 44)
macro "a101_Q2" p:term:max : term => `(alg105ArrBase $p + 45)
macro "a101_ps" p:term:max : term => `(alg105ArrBase $p + 46)
macro "a101_visOut" p:term:max : term => `(alg105ArrBase $p + 50)
macro "a101_A_off" p:term:max : term => `(alg105ArrBase $p + 60)

macro "r101_n" : term => `((52 : ℕ))
macro "r101_m" : term => `((53 : ℕ))
macro "r101_xLen" : term => `((54 : ℕ))
macro "r101_M" : term => `((55 : ℕ))
macro "r101_j" : term => `((56 : ℕ))
macro "r101_off" : term => `((57 : ℕ))
macro "r101_vLen" : term => `((60 : ℕ))
macro "r101_rELen" : term => `((61 : ℕ))
macro "r101_rT" : term => `((62 : ℕ))
macro "r101_isInt" : term => `((63 : ℕ))
macro "r101_bLen" : term => `((64 : ℕ))
macro "r101_sLen" : term => `((65 : ℕ))
macro "r101_P1Len" : term => `((66 : ℕ))
macro "r101_P2Len" : term => `((67 : ℕ))
macro "r101_P3Len" : term => `((68 : ℕ))
macro "r101_vOf" : term => `((69 : ℕ))
macro "r101_vOfPathLen" : term => `((70 : ℕ))
macro "r101_nA" : term => `((71 : ℕ))
macro "r101_mA" : term => `((72 : ℕ))
macro "r101_kA" : term => `((73 : ℕ))
macro "r101_folioLen" : term => `((74 : ℕ))
macro "r101_folioCode" : term => `((75 : ℕ))
macro "r101_visPos" : term => `((76 : ℕ))
macro "r101_base" : term => `((80 : ℕ))
macro "r101_R_off" : term => `((110 : ℕ))

/-- Upper bound on `m.enc.length` for any member record `m` of `G`. -/
def memberPerCap (C41 n m : ℕ) : ℕ :=
  C41 * (n + m + 1) + 18 * (n + m + 1)

theorem length_le_numEdges_of_nodup_isDelGraphEdge {n : ℕ} (G : MultiDigraph n)
    {eList : List (ℕ × ℕ × ℕ)} (hnd : eList.Nodup)
    (he : ∀ e ∈ eList, isDelGraphEdge G e = true) :
    eList.length ≤ G.numEdges := by
  have hsub : (eList.toFinset : Set (ℕ × ℕ × ℕ)) ⊆ G.toGMDigraph.edgeSet := by
    intro e he_mem
    exact isDelGraphEdge_eq_true_iff_mem_toGMDigraph.mp (he e (List.mem_toFinset.mp he_mem))
  have hle := Set.ncard_le_ncard hsub G.isFinite_toGMDigraph.finite_E
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, G.ncard_edgeSet_toGMDigraph] at hle
  exact hle

theorem length_memberTildeAEList_le_numEdges {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') blk.toGMWall blk.toSociety)
    (hRD : GM13.IsRuralDivision blk.toSociety blk.toDivision)
    {xSeq : List ℕ} (hx_set : xSeq.toFinset = X'.image Fin.val)
    (j : Fin blk.members.length) :
    (memberTildeAEList G blk xSeq j).length ≤ G.numEdges := by
  have hnd := nodup_memberTildeAEList G blk hx_set j
  have hends := memberTildeAEList_valid_ends G blk hWS hRD xSeq j [] (fun _ h => nomatch h)
  exact length_le_numEdges_of_nodup_isDelGraphEdge G hnd (fun e he => (hends e he).1)

theorem length_flatten_memberTildeAEList_le_numEdges {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') blk.toGMWall blk.toSociety)
    (hRD : GM13.IsRuralDivision blk.toSociety blk.toDivision)
    {xSeq : List ℕ} (hx_set : xSeq.toFinset = X'.image Fin.val) :
    (((List.finRange blk.members.length).map (memberTildeAEList G blk xSeq)).flatten).length ≤
      G.numEdges := by
  have hnd := flatten_memberTildeAEList_nodup G blk hRD hx_set
  refine length_le_numEdges_of_nodup_isDelGraphEdge G hnd ?_
  intro e he
  rcases List.mem_flatten.mp he with ⟨l, hl, he_l⟩
  rcases List.mem_map.mp hl with ⟨j, _, rfl⟩
  exact (memberTildeAEList_valid_ends G blk hWS hRD xSeq j [] (fun _ h => nomatch h) e he_l).1

theorem length_memberTildeAVList_le_n {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    {xSeq : List ℕ} (hx_nd : xSeq.Nodup) (hx_set : xSeq.toFinset = X'.image Fin.val)
    {r : Case3MemberRecord} (hr : r ∈ blk.members)
    {sSeq : List ℕ} (hs_nd : sSeq.Nodup) (hs_sub : ∀ s ∈ sSeq, s ∈ r.vList) :
    (memberTildeAVList xSeq r sSeq).length ≤ n := by
  have hr_val := blk.member_valid_iff hr
  have hr_disj : ∀ v ∈ r.vList, v ∉ xSeq := by
    intro v hv hx
    have hv_del := blk.K_vList_mem_delGraph (hr_val.2.2.1 v hv)
    rcases (mem_vertexSet_delGraph_iff G X' v).mp hv_del with ⟨_, hnotX⟩
    have hv_fin : v ∈ X'.image Fin.val := hx_set ▸ List.mem_toFinset.mpr hx
    rcases Finset.mem_image.mp hv_fin with ⟨u, hu, heq⟩
    exact hnotX (heq ▸ hu)
  have hnd := nodup_memberTildeAVList xSeq r sSeq hx_nd hr_val.2.1 hs_nd hs_sub hr_disj
  have hsub : (memberTildeAVList xSeq r sSeq).toFinset ⊆ Finset.range n := by
    intro v hv
    rw [List.mem_toFinset, mem_memberTildeAVList_iff xSeq r sSeq hs_sub] at hv
    rw [Finset.mem_range]
    rcases hv with hvr | hvx
    · exact blk.member_vList_lt hr hvr
    · have hv_fin : v ∈ X'.image Fin.val := hx_set ▸ List.mem_toFinset.mpr hvx
      rcases Finset.mem_image.mp hv_fin with ⟨u, _, rfl⟩
      exact u.2
  have hle := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at hle

theorem isValidVisionMemberRecord_of_interior {w n q δ C41 : ℕ}
    {G : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') blk.toGMWall blk.toSociety)
    (hRD : GM13.IsRuralDivision blk.toSociety blk.toDivision)
    {xSeq : List ℕ} (hx_nd : xSeq.Nodup) (hx_set : xSeq.toFinset = X'.image Fin.val)
    (j : Fin blk.members.length)
    (hInt : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true)
    {sSeq P₁ P₂ P₃ : List ℕ}
    (hstep1 : Step1AttachmentValid blk (blk.members[j.1]'j.2) sSeq P₁ P₂ P₃)
    {vOf : ℕ} {vOfPath : List ℕ}
    (hstep4 : Step4VOfValid blk (blk.members[j.1]'j.2) vOf vOfPath)
    {folioWords : List ℕ} {folioCode : ℕ}
    {out : ParsedFolioAndModels
      (tildeAMultiDigraph (memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq)
        (memberTildeAEList G blk xSeq j))
      (prefixRootFinset (memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length
        (sSeq ++ xSeq).length) δ}
    (hparse : parseFolioAndModelsFull
      (tildeAMultiDigraph (memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq)
        (memberTildeAEList G blk xSeq j))
      (prefixRootFinset (memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length
        (sSeq ++ xSeq).length) δ folioWords = some out)
    (hcode : folioCode = folioRepCode q out.folio)
    (hfw_len : folioWords.length ≤
      C41 * ((memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length +
        (memberTildeAEList G blk xSeq j).length + 1))
    (hw3 : 3 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hfw_len_w : folioWords.length < 2 ^ w)
    (hfw_w : ∀ x ∈ folioWords, x < 2 ^ w) (hfc_w : folioCode < 2 ^ w) :
    let r := blk.members[j.1]'j.2
    let m : VisionMemberRecord :=
      ⟨1, sSeq, P₁, P₂, P₃, memberTildeAVList xSeq r sSeq,
        memberTildeAEList G blk xSeq j, folioWords, folioCode, vOf, vOfPath⟩
    isValidVisionMemberRecord G X' blk q δ xSeq r m = true ∧
    m.enc.length ≤ memberPerCap C41 n G.numEdges ∧
    (∀ x ∈ m.enc, x < 2 ^ w) := by
  dsimp only
  let m : VisionMemberRecord :=
    ⟨1, sSeq, P₁, P₂, P₃, memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq,
      memberTildeAEList G blk xSeq j, folioWords, folioCode, vOf, vOfPath⟩
  have hn_w : n < 2 ^ w := by omega
  have hr : (blk.members[j.1]'j.2) ∈ blk.members := List.getElem_mem j.2
  rcases hstep1 with ⟨hs_nd, hs_fin, hs_len, hs_lt, hP1_len, hP1_lt, hP2_len, hP2_lt,
    hP3_len, hP3_lt, hcw3⟩
  rcases hstep4 with ⟨hvOf_lt, hvP_len, hvP_lt, hvOf_mem, hvP_path, hs0_cond, hvP_hit⟩
  have hs_sub : ∀ s ∈ sSeq, s ∈ (blk.members[j.1]'j.2).vList := by
    intro s hs
    have hmem : s ∈ (memberBoundaryList blk.corners blk.K_eList (blk.members[j.1]'j.2)).toFinset := by
      rw [← hs_fin]; exact List.mem_toFinset.mpr hs
    exact List.mem_of_mem_filter (List.mem_toFinset.mp hmem)
  have he_nd := nodup_memberTildeAEList G blk hx_set j
  have he_len := length_memberTildeAEList_le_numEdges G blk hWS hRD hx_set j
  have he_ends := memberTildeAEList_valid_ends G blk hWS hRD xSeq j sSeq hs_sub
  have he_filt := filter_memberTildeAEList G blk hx_set j
  have hv_len := length_memberTildeAVList_le_n blk hx_nd hx_set hr hs_nd hs_sub
  have hval : isValidVisionMemberRecord G X' blk q δ xSeq (blk.members[j.1]'j.2) m = true := by
    unfold isValidVisionMemberRecord isValidMemberFolioWords
    dsimp only [m]
    simp only [hInt, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      he_nd, he_len, he_filt,
      hs_nd, hs_fin, hs_len,
      hvOf_mem, hvP_path, hs0_cond,
      hparse, hcode, true_and, and_true]
    refine ⟨he_ends, ?_, hvP_hit⟩
    split_ifs with h3
    · rw [ite_eq_left h3] at hcw3
      rcases hcw3 with ⟨h1, h2, h3', h4, h5, h6, h7, h8⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3'⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    · rfl
  have hlen_enc : m.enc.length ≤ memberPerCap C41 n G.numEdges := by
    rw [m.length_enc]
    unfold memberPerCap
    dsimp only [m]
    have hfw_le' : folioWords.length ≤ C41 * (n + G.numEdges + 1) :=
      le_trans hfw_len (Nat.mul_le_mul_left C41 (by omega))
    omega
  have hwords : ∀ x ∈ m.enc, x < 2 ^ w := by
    intro x hx
    unfold VisionMemberRecord.enc at hx
    dsimp only [m] at hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    have h1_w : 1 < 2 ^ w := by omega
    have hv_lt : ∀ v ∈ memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq, v < n := by
      intro v hv
      rw [mem_memberTildeAVList_iff xSeq (blk.members[j.1]'j.2) sSeq hs_sub] at hv
      rcases hv with hvr | hvx
      · exact blk.member_vList_lt hr hvr
      · have hv_fin : v ∈ X'.image Fin.val := hx_set ▸ List.mem_toFinset.mpr hvx
        rcases Finset.mem_image.mp hv_fin with ⟨u, _, rfl⟩
        exact u.2
    have he_w : ∀ y ∈ encEdgeTriples (memberTildeAEList G blk xSeq j), y < 2 ^ w := by
      intro y hy
      rcases (mem_encEdgeTriples_iff _ y).mp hy with ⟨e, he, rfl | rfl | rfl⟩
      · exact lt_trans (hv_lt e.1 (he_ends e he).2.1) hn_w
      · exact lt_trans (hv_lt e.2.1 (he_ends e he).2.2) hn_w
      · have heG := isDelGraphEdge_eq_true_iff_mem_toGMDigraph.mp (he_ends e he).1
        have hk_le : e.2.2 < G.numEdges :=
          lt_of_lt_of_le heG.2.2 (G.edgeMult_le_numEdges ⟨e.1, heG.1⟩ ⟨e.2.1, heG.2.1⟩)
        exact lt_trans hk_le hm_w
    rcases hx with (((((((((rfl | (rfl | hx)) | (rfl | hx)) | (rfl | hx)) | (rfl | hx)) |
        (rfl | hx)) | (rfl | hx)) | (rfl | hx)) | (rfl | rfl)) | (rfl | hx))
    · exact h1_w
    · omega
    · exact lt_trans (hs_lt x hx) hn_w
    · omega
    · exact lt_trans (hP1_lt x hx) hn_w
    · omega
    · exact lt_trans (hP2_lt x hx) hn_w
    · omega
    · exact lt_trans (hP3_lt x hx) hn_w
    · omega
    · exact lt_trans (hv_lt x hx) hn_w
    · omega
    · exact he_w x hx
    · exact hfw_len_w
    · exact hfw_w x hx
    · exact hfc_w
    · exact lt_trans hvOf_lt hn_w
    · omega
    · exact lt_trans (hvP_lt x hx) hn_w
  exact ⟨hval, hlen_enc, hwords⟩

/-- Semantic `δ`-folio representation property for a `VisionMemberRecord` `m` of member `r`. -/
def VisionMemberRecordFolioValid {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (δ : ℕ) (xSeq : List ℕ) (r : Case3MemberRecord) (m : VisionMemberRecord) : Prop :=
  isMemberInterior W r = true →
    ∀ (folioOut : ParsedFolioAndModels (tildeAMultiDigraph m.tildeA_vList m.tildeA_eList)
        (prefixRootFinset m.tildeA_vList.length (m.sSeq ++ xSeq).length) δ),
      parseFolioAndModelsFull (tildeAMultiDigraph m.tildeA_vList m.tildeA_eList)
        (prefixRootFinset m.tildeA_vList.length (m.sSeq ++ xSeq).length) δ m.folioWords = some folioOut →
      IsDeltaFolioRep δ (tildeAMultiDigraph m.tildeA_vList m.tildeA_eList)
        (prefixRootFinset m.tildeA_vList.length (m.sSeq ++ xSeq).length) folioOut.folio

theorem isValidVisionMemberRecord_of_nonInterior {w n q δ C41 : ℕ}
    {G : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') blk.toGMWall blk.toSociety)
    (hRD : GM13.IsRuralDivision blk.toSociety blk.toDivision)
    {xSeq : List ℕ} (hx_nd : xSeq.Nodup) (hx_set : xSeq.toFinset = X'.image Fin.val)
    (j : Fin blk.members.length)
    (hNotInt : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = false)
    (hn_w : n < 2 ^ w) (hm_w : G.numEdges < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    let r := blk.members[j.1]'j.2
    let m : VisionMemberRecord :=
      ⟨0, [], [], [], [], memberTildeAVList xSeq r [],
        memberTildeAEList G blk xSeq j, [], 0, 0, []⟩
    isValidVisionMemberRecord G X' blk q δ xSeq r m = true ∧
    m.enc.length ≤ memberPerCap C41 n G.numEdges ∧
    (∀ x ∈ m.enc, x < 2 ^ w) := by
  dsimp only
  let m : VisionMemberRecord :=
    ⟨0, [], [], [], [], memberTildeAVList xSeq (blk.members[j.1]'j.2) [],
      memberTildeAEList G blk xSeq j, [], 0, 0, []⟩
  have hr : (blk.members[j.1]'j.2) ∈ blk.members := List.getElem_mem j.2
  have hs_sub : ∀ s ∈ ([] : List ℕ), s ∈ (blk.members[j.1]'j.2).vList := by simp
  have he_nd := nodup_memberTildeAEList G blk hx_set j
  have he_len := length_memberTildeAEList_le_numEdges G blk hWS hRD hx_set j
  have he_ends := memberTildeAEList_valid_ends G blk hWS hRD xSeq j [] hs_sub
  have he_filt := filter_memberTildeAEList G blk hx_set j
  have hv_len := length_memberTildeAVList_le_n blk hx_nd hx_set hr List.nodup_nil hs_sub
  have hval : isValidVisionMemberRecord G X' blk q δ xSeq (blk.members[j.1]'j.2) m = true := by
    unfold isValidVisionMemberRecord
    dsimp only [m]
    simp only [hNotInt, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      he_nd, he_len, he_filt, true_and, and_true, and_self]
    exact he_ends
  have hlen_enc : m.enc.length ≤ memberPerCap C41 n G.numEdges := by
    rw [m.length_enc]
    unfold memberPerCap
    dsimp only [m]
    simp only [List.length_nil]
    omega
  have hwords : ∀ x ∈ m.enc, x < 2 ^ w := by
    intro x hx
    unfold VisionMemberRecord.enc at hx
    dsimp only [m] at hx
    simp only [List.length_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    have h0_w : 0 < 2 ^ w := by omega
    have hv_lt : ∀ v ∈ memberTildeAVList xSeq (blk.members[j.1]'j.2) [], v < n := by
      intro v hv
      rw [mem_memberTildeAVList_iff xSeq (blk.members[j.1]'j.2) [] hs_sub] at hv
      rcases hv with hvr | hvx
      · exact blk.member_vList_lt hr hvr
      · have hv_fin : v ∈ X'.image Fin.val := hx_set ▸ List.mem_toFinset.mpr hvx
        rcases Finset.mem_image.mp hv_fin with ⟨u, _, rfl⟩
        exact u.2
    have he_w : ∀ y ∈ encEdgeTriples (memberTildeAEList G blk xSeq j), y < 2 ^ w := by
      intro y hy
      rcases (mem_encEdgeTriples_iff _ y).mp hy with ⟨e, he, rfl | rfl | rfl⟩
      · exact lt_trans (hv_lt e.1 (he_ends e he).2.1) hn_w
      · exact lt_trans (hv_lt e.2.1 (he_ends e he).2.2) hn_w
      · have heG := isDelGraphEdge_eq_true_iff_mem_toGMDigraph.mp (he_ends e he).1
        have hk_le : e.2.2 < G.numEdges :=
          lt_of_lt_of_le heG.2.2 (G.edgeMult_le_numEdges ⟨e.1, heG.1⟩ ⟨e.2.1, heG.2.1⟩)
        exact lt_trans hk_le hm_w
    rcases hx with (((((((((rfl | rfl) | rfl) | rfl) | rfl) | (rfl | hx)) | (rfl | hx)) | rfl) | (rfl | rfl)) | rfl)
    · exact h0_w
    · exact h0_w
    · exact h0_w
    · exact h0_w
    · exact h0_w
    · omega
    · exact lt_trans (hv_lt x hx) hn_w
    · omega
    · exact he_w x hx
    · exact h0_w
    · exact h0_w
    · exact h0_w
    · exact h0_w
  exact ⟨hval, hlen_enc, hwords⟩

/-! ### Section 2, Part A: Member Stream Read, Interior Check, and Steps 1 & 4 -/

/-- Empty initialization of Step 1 and Step 4 arrays/registers when `r` is non-interior. -/
def initNonInteriorStep14Prog (p : ℕ) : Cmd :=
  .seq (allocEmptyArrProg (a101_sSeq p) r101_sLen)
    (.seq (allocEmptyArrProg (a101_P1 p) r101_P1Len)
      (.seq (allocEmptyArrProg (a101_P2 p) r101_P2Len)
        (.seq (allocEmptyArrProg (a101_P3 p) r101_P3Len)
          (.seq (.assign r101_vOf (.const 0))
            (allocEmptyArrProg (a101_vOfPath p) r101_vOfPathLen)))))

/-- Part A of member iteration: reads `r.enc` from `(a101_block p, r101_off)`, checks whether `r` is
an interior member in `r101_isInt`, and computes `(sSeq, P₁, P₂, P₃, vOf, vOfPath)`. -/
def alg101MemberStep14Prog (p : ℕ) : Cmd :=
  .seq (readOneMemberRecordProg (a101_block p) r101_off
      (a101_rV p) (a101_rE p) (a101_rPar p) (a101_rTau p)
      r101_vLen r101_rELen r101_rT r101_base)
    (.seq (checkMemberInteriorProg (a101_perim p) (a101_rV p) r101_vLen r101_isInt r101_base)
      (.ite (.op .eq (.reg r101_isInt) (.const 1))
        (.seq (countIncEdgesProg (a101_rE p) (a101_degR p) r101_rELen r101_n r101_base)
          (.seq (buildMemberBoundaryProg (a101_degK p) (a101_degR p) (a101_isCorner p)
              (a101_rV p) (a101_buf p) (a101_bList p) r101_vLen r101_bLen r101_base)
            (.seq (buildStep1AttachmentProg (a101_start p) (a101_end p) (a101_entries p)
                (a101_corners p) (a101_isCorner p) (a101_bList p)
                (a101_sSeq p) (a101_P1 p) (a101_P2 p) (a101_P3 p)
                (a101_zA p) (a101_buf p) (a101_Q0 p) (a101_Q1 p) (a101_Q2 p) (a101_ps p)
                r101_n r101_bLen r101_sLen r101_P1Len r101_P2Len r101_P3Len r101_base)
              (buildStep4VOfProg (a101_start p) (a101_end p) (a101_entries p)
                (a101_WH p) (a101_bList p) (a101_rV p)
                (a101_vOfPath p) (a101_zA p) (a101_buf p) (a101_ps p)
                r101_n r101_bLen r101_vLen r101_vOf r101_vOfPathLen r101_base))))
        (initNonInteriorStep14Prog p)))

theorem alg101MemberStep14Prog_exec {w n p q : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph q X'.toNatSet blk.toGMWall blk.toSociety blk.toDivision)
    (j : Fin blk.members.length)
    (lists : Fin n → List ℕ) (rest : List ℕ) (off : ℕ)
    (hw6 : 6 < 2 ^ w) (h2n_w : 2 * n + 2 < 2 ^ w)
    (h3m_w : 3 * G.numEdges + 1 < 2 ^ w)
    (hwords : ∀ x ∈ (blk.members[j.1]'j.2).enc, x < 2 ^ w)
    (hoff_w : off + (blk.members[j.1]'j.2).enc.length < 2 ^ w)
    {s : State}
    (hstream : AtStream (a101_block p) off ((blk.members[j.1]'j.2).enc ++ rest) s)
    (hroff : s.regs r101_off = off)
    (hrn : s.regs r101_n = n)
    (hperim : s.arrs (a101_perim p) = bitSetList blk.wallSec.W.perimFinset)
    (hWH : s.arrs (a101_WH p) = bitSetList blk.wallSec.W.vertexFinset)
    (hcor : s.arrs (a101_corners p) = blk.corners)
    (hisC : s.arrs (a101_isCorner p) =
      bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ blk.corners)))
    (hdegK : s.arrs (a101_degK p) = List.ofFn (fun v : Fin n => incEdgeCount blk.K_eList v.1))
    (hadj : IsAdjList (G.deleteVertices (Z_notK blk)).toSimpleGraph
      (a101_start p) (a101_end p) (a101_entries p) lists s)
    (hent_w : (s.arrs (a101_entries p)).length < 2 ^ w) :
    let r := blk.members[j.1]'j.2
    let isInt := if isMemberInterior blk.wallSec.W r then 1 else 0
    ∃ s' t sSeq P₁ P₂ P₃ vOf vOfPath,
      Exec w (alg101MemberStep14Prog p) s s' t ∧
      t ≤ 1384 * n + 109 * r.vList.length + 106 * r.eList.length + 18 * r.t_len +
        124 * totalAdjEntries lists + 1000 ∧
      AtStream (a101_block p) (off + r.enc.length) rest s' ∧
      s'.regs r101_off = off + r.enc.length ∧
      s'.arrs (a101_rV p) = r.vList ∧
      s'.regs r101_vLen = r.vList.length ∧
      s'.arrs (a101_rE p) = encEdgeTriples r.eList ∧
      s'.regs r101_rELen = r.eList.length ∧
      s'.arrs (a101_rPar p) = r.parList ∧
      s'.regs r101_rT = r.t_len ∧
      s'.arrs (a101_rTau p) = r.tauList ∧
      s'.regs r101_isInt = isInt ∧
      s'.arrs (a101_sSeq p) = sSeq ∧
      s'.arrs (a101_P1 p) = P₁ ∧
      s'.arrs (a101_P2 p) = P₂ ∧
      s'.arrs (a101_P3 p) = P₃ ∧
      s'.arrs (a101_vOfPath p) = vOfPath ∧
      s'.regs r101_sLen = sSeq.length ∧
      s'.regs r101_P1Len = P₁.length ∧
      s'.regs r101_P2Len = P₂.length ∧
      s'.regs r101_P3Len = P₃.length ∧
      s'.regs r101_vOf = vOf ∧
      s'.regs r101_vOfPathLen = vOfPath.length ∧
      (∀ s₀ ∈ sSeq, s₀ ∈ r.vList) ∧
      sSeq.length ≤ 3 ∧
      (if isMemberInterior blk.wallSec.W r then
        Step1AttachmentValid blk r sSeq P₁ P₂ P₃ ∧
        Step4VOfValid blk r vOf vOfPath
      else
        sSeq = [] ∧ P₁ = [] ∧ P₂ = [] ∧ P₃ = [] ∧ vOf = 0 ∧ vOfPath = []) ∧
      (∀ a < a101_rV p, s'.arrs a = s.arrs a) ∧
      (∀ reg < r101_base, reg ≠ r101_off → (reg < 60 ∨ reg = r101_visPos) → s'.regs reg = s.regs reg) := by
  dsimp only
  let isInt := if isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) then 1 else 0
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hr : (blk.members[j.1]'j.2) ∈ blk.members := List.getElem_mem j.2
  have hr_val := blk.member_valid_iff hr
  have hv_lt : ∀ v ∈ (blk.members[j.1]'j.2).vList, v < n := fun v hv => blk.member_vList_lt hr hv
  have hv_len_le : (blk.members[j.1]'j.2).vList.length ≤ n := hr_val.1
  have hdel_le : (G.deleteVertices X').numEdges ≤ G.numEdges :=
    G.numEdges_deleteVertices_le X'
  have hrE_le : (blk.members[j.1]'j.2).eList.length ≤ G.numEdges := le_trans hr_val.2.2.2.1 hdel_le
  have hKE_le : blk.K_eList.length ≤ G.numEdges := le_trans blk.hK_e_len hdel_le
  have hpar_len : (blk.members[j.1]'j.2).parList.length = (blk.members[j.1]'j.2).t_len := hr_val.2.2.2.2.2.2.2.2.1
  have htau_len : (blk.members[j.1]'j.2).tauList.length = (blk.members[j.1]'j.2).eList.length := hr_val.2.2.2.2.2.2.2.2.2.2.1
  -- 1. readOneMemberRecordProg
  rcases readOneMemberRecordProg_exec (a101_block p) r101_off
      (a101_rV p) (a101_rE p) (a101_rPar p) (a101_rTau p)
      r101_vLen r101_rELen r101_rT r101_base
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (blk.members[j.1]'j.2) rest off hpar_len htau_len hwords hw3 hoff_w hstream hroff with
    ⟨s₁, t₁, hex₁, ht₁, hstream₁, hroff₁, hrV₁, hrvLen₁, hrE₁, hrrELen₁, hrPar₁, hrrT₁, hrTau₁,
      harr₁, hreg₁⟩
  -- 2. checkMemberInteriorProg
  have hperim₁ : s₁.arrs (a101_perim p) = bitSetList blk.wallSec.W.perimFinset := by
    rw [harr₁ (a101_perim p) (by omega) (by omega) (by omega) (by omega), hperim]
  rcases checkMemberInteriorProg_exec blk.wallSec.W (blk.members[j.1]'j.2) hv_lt
      (a101_perim p) (a101_rV p) r101_vLen r101_isInt r101_base
      (by decide) (by decide) (by decide) hw2 hn_w (by omega) hperim₁ hrV₁ hrvLen₁ with
    ⟨s₂, t₂, hex₂, ht₂, hrisInt₂, harr₂, hreg₂⟩
  change s₂.regs r101_isInt = isInt at hrisInt₂
  have harr_s₂ : ∀ a : ℕ, a ≠ a101_rV p → a ≠ a101_rE p → a ≠ a101_rPar p → a ≠ a101_rTau p →
      s₂.arrs a = s.arrs a := fun a h1 h2 h3 h4 =>
    (harr₂ a).trans (harr₁ a h1 h2 h3 h4)
  have hreg_s₂ : ∀ reg < r101_base, reg ≠ r101_off → reg ≠ r101_vLen → reg ≠ r101_rELen →
      reg ≠ r101_rT → reg ≠ r101_isInt → s₂.regs reg = s.regs reg :=
    fun reg hlt h1 h2 h3 h4 h5 => (hreg₂ reg hlt h5).trans (hreg₁ reg hlt h1 h2 h3 h4)
  -- 3. Branch on isMemberInterior
  by_cases hInt : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true
  · have hisInt1 : isInt = 1 := by simp [isInt, hInt]
    have hcond : (Expr.op .eq (.reg r101_isInt) (.const 1)).eval w s₂ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrisInt₂, hisInt1, hw]
    have he_endpoints : ∀ e ∈ (blk.members[j.1]'j.2).eList, e.1 < n ∧ e.2.1 < n := by
      intro e he
      rcases hr_val.2.2.2.2.2.1 e he with ⟨_, he1, he2⟩
      exact ⟨hv_lt e.1 he1, hv_lt e.2.1 he2⟩
    rcases countIncEdgesProg_exec (blk.members[j.1]'j.2).eList he_endpoints
        (a101_rE p) (a101_degR p) r101_rELen r101_n r101_base
        (by omega) (by decide) (by decide) hw3 hn_w (by omega)
        (by rw [harr₂, hrE₁])
        (by rw [hreg₂ r101_rELen (by decide) (by decide), hrrELen₁])
        (by rw [hreg_s₂ r101_n (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrn]) with
      ⟨s₃, t₃, hex₃, ht₃, hdegR₃, harr₃, hreg₃⟩
    rcases buildMemberBoundaryProg_exec blk hr hv_lt
        (a101_degK p) (a101_degR p) (a101_isCorner p) (a101_rV p) (a101_buf p) (a101_bList p)
        r101_vLen r101_bLen r101_base
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by decide) (by decide) (by decide) hw2 hn_w (by omega) (by omega) (by omega)
        (by rw [harr₃, harr_s₂, hdegK] <;> omega)
        hdegR₃
        (by rw [harr₃, harr_s₂, hisC] <;> omega)
        (by rw [harr₃ _ (by omega), harr₂, hrV₁])
        (by rw [hreg₃ r101_vLen (by decide), hreg₂ r101_vLen (by decide) (by decide), hrvLen₁]) with
      ⟨s₄, t₄, hex₄, ht₄, hbL₄, hrbL₄, harr₄, hreg₄⟩
    have harr_s₄ : ∀ a < a101_sSeq p,
        a ≠ a101_rV p → a ≠ a101_rE p → a ≠ a101_rPar p → a ≠ a101_rTau p →
        a ≠ a101_degR p → a ≠ a101_bList p → s₄.arrs a = s.arrs a := by
      intro a ha h1 h2 h3 h4 h5 h6
      rw [harr₄ a (by omega) h6, harr₃ a h5, harr_s₂ a h1 h2 h3 h4]
    have hadj₄ : IsAdjList (G.deleteVertices (Z_notK blk)).toSimpleGraph
        (a101_start p) (a101_end p) (a101_entries p) lists s₄ :=
      hadj.of_arrs_eq
        (by rw [harr_s₄] <;> omega)
        (by rw [harr_s₄] <;> omega)
        (by rw [harr_s₄] <;> omega)
    have hent₄_w : (s₄.arrs (a101_entries p)).length < 2 ^ w := by
      rw [harr_s₄] <;> [exact hent_w; omega; omega; omega; omega; omega; omega; omega]
    have hrn₄ : s₄.regs r101_n = n := by
      rw [hreg₄ r101_n (by decide) (by decide), hreg₃ r101_n (by decide),
        hreg_s₂ r101_n (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrn]
    rcases buildStep1AttachmentProg_exec blk hC hr lists
        (a101_start p) (a101_end p) (a101_entries p) (a101_corners p) (a101_isCorner p) (a101_bList p)
        (a101_sSeq p) (a101_P1 p) (a101_P2 p) (a101_P3 p)
        (a101_zA p) (a101_buf p) (a101_Q0 p) (a101_Q1 p) (a101_Q2 p) (a101_ps p)
        r101_n r101_bLen r101_sLen r101_P1Len r101_P2Len r101_P3Len r101_base
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
        (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩
        hw6 h2n_w hadj₄ hent₄_w
        (by rw [harr_s₄, hcor] <;> omega)
        (by rw [harr_s₄, hisC] <;> omega)
        hbL₄ hrn₄ hrbL₄ with
      ⟨s₅, t₅, sSeq, P₁, P₂, P₃, hex₅, ht₅, hsSeq₅, hP1_5, hP2_5, hP3_5,
        hrsLen₅, hrP1_5, hrP2_5, hrP3_5, hstep1, harr₅, hreg₅⟩
    have hadj₅ : IsAdjList (G.deleteVertices (Z_notK blk)).toSimpleGraph
        (a101_start p) (a101_end p) (a101_entries p) lists s₅ :=
      hadj₄.of_arrs_eq (by rw [harr₅ _ (by omega)]) (by rw [harr₅ _ (by omega)]) (by rw [harr₅ _ (by omega)])
    have hent₅_w : (s₅.arrs (a101_entries p)).length < 2 ^ w := by
      rw [harr₅ _ (by omega)]; exact hent₄_w
    rcases buildStep4VOfProg_exec blk hC hr hInt lists
        (a101_start p) (a101_end p) (a101_entries p) (a101_WH p) (a101_bList p) (a101_rV p)
        (a101_vOfPath p) (a101_zA p) (a101_buf p) (a101_ps p)
        r101_n r101_bLen r101_vLen r101_vOf r101_vOfPathLen r101_base
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ⟨by omega, by omega, by omega⟩
        (by decide) (by decide) (by decide) ⟨by decide, by decide⟩
        hw2 h2n_w hadj₅ hent₅_w
        (by rw [harr₅, harr_s₄, hWH] <;> omega)
        (by rw [harr₅ _ (by omega), hbL₄])
        (by rw [harr₅, harr₄, harr₃, harr₂, hrV₁] <;> omega)
        (by rw [hreg₅ r101_n (by decide) (by decide) (by decide) (by decide) (by decide), hrn₄])
        (by rw [hreg₅ r101_bLen (by decide) (by decide) (by decide) (by decide) (by decide), hrbL₄])
        (by rw [hreg₅ r101_vLen (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg₄ r101_vLen (by decide) (by decide), hreg₃ r101_vLen (by decide),
              hreg₂ r101_vLen (by decide) (by decide), hrvLen₁]) with
      ⟨s₆, t₆, vOf, vOfPath, hex₆, ht₆, hvOfP₆, hrvOf₆, hrvOfPLen₆, hstep4, harr₆, hreg₆⟩
    have harr_lt30 : ∀ a < a101_sSeq p,
        a ≠ a101_rV p → a ≠ a101_rE p → a ≠ a101_rPar p → a ≠ a101_rTau p →
        a ≠ a101_degR p → a ≠ a101_bList p → s₆.arrs a = s.arrs a := by
      intro a ha h1 h2 h3 h4 h5 h6
      rw [harr₆ a (by omega), harr₅ a ha, harr_s₄ a ha h1 h2 h3 h4 h5 h6]
    have hreg_lt64 : ∀ reg < r101_base,
        reg ≠ r101_off → reg ≠ r101_vLen → reg ≠ r101_rELen → reg ≠ r101_rT → reg ≠ r101_isInt →
        (reg < 64 ∨ reg = r101_visPos) → s₆.regs reg = s.regs reg := by
      intro reg hlt h1 h2 h3 h4 h5 hcase
      rw [hreg₆ reg hlt (by omega) (by omega),
        hreg₅ reg hlt (by omega) (by omega) (by omega) (by omega),
        hreg₄ reg hlt (by omega), hreg₃ reg hlt,
        hreg_s₂ reg hlt h1 h2 h3 h4 h5]
    have hs_sub : ∀ s₀ ∈ sSeq, s₀ ∈ (blk.members[j.1]'j.2).vList := by
      intro s₀ hs₀
      have hmem : s₀ ∈ (memberBoundaryList blk.corners blk.K_eList (blk.members[j.1]'j.2)).toFinset := by
        rw [← hstep1.2.1]; exact List.mem_toFinset.mpr hs₀
      exact List.mem_of_mem_filter (List.mem_toFinset.mp hmem)
    refine ⟨s₆, t₁ + (t₂ + (3 + (t₃ + (t₄ + (t₅ + t₆))))), sSeq, P₁, P₂, P₃, vOf, vOfPath,
      .seq hex₁ (.seq hex₂ (.ite_true hcond (by omega) (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆))))),
      by omega,
      hstream₁.of_arr_eq (by rw [harr₆, harr₅, harr₄, harr₃, harr₂] <;> omega),
      by rw [hreg₆ r101_off (by decide) (by decide) (by decide),
           hreg₅ r101_off (by decide) (by decide) (by decide) (by decide) (by decide),
           hreg₄ r101_off (by decide) (by decide), hreg₃ r101_off (by decide),
           hreg₂ r101_off (by decide) (by decide), hroff₁],
      by rw [harr₆, harr₅, harr₄, harr₃, harr₂, hrV₁] <;> omega,
      by rw [hreg₆ r101_vLen (by decide) (by decide) (by decide),
           hreg₅ r101_vLen (by decide) (by decide) (by decide) (by decide) (by decide),
           hreg₄ r101_vLen (by decide) (by decide), hreg₃ r101_vLen (by decide),
           hreg₂ r101_vLen (by decide) (by decide), hrvLen₁],
      by rw [harr₆, harr₅, harr₄, harr₃, harr₂, hrE₁] <;> omega,
      by rw [hreg₆ r101_rELen (by decide) (by decide) (by decide),
           hreg₅ r101_rELen (by decide) (by decide) (by decide) (by decide) (by decide),
           hreg₄ r101_rELen (by decide) (by decide), hreg₃ r101_rELen (by decide),
           hreg₂ r101_rELen (by decide) (by decide), hrrELen₁],
      by rw [harr₆, harr₅, harr₄, harr₃, harr₂, hrPar₁] <;> omega,
      by rw [hreg₆ r101_rT (by decide) (by decide) (by decide),
           hreg₅ r101_rT (by decide) (by decide) (by decide) (by decide) (by decide),
           hreg₄ r101_rT (by decide) (by decide), hreg₃ r101_rT (by decide),
           hreg₂ r101_rT (by decide) (by decide), hrrT₁],
      by rw [harr₆, harr₅, harr₄, harr₃, harr₂, hrTau₁] <;> omega,
      by rw [hreg₆ r101_isInt (by decide) (by decide) (by decide),
           hreg₅ r101_isInt (by decide) (by decide) (by decide) (by decide) (by decide),
           hreg₄ r101_isInt (by decide) (by decide), hreg₃ r101_isInt (by decide), hrisInt₂],
      by rw [harr₆ _ (by omega), hsSeq₅],
      by rw [harr₆ _ (by omega), hP1_5],
      by rw [harr₆ _ (by omega), hP2_5],
      by rw [harr₆ _ (by omega), hP3_5],
      hvOfP₆,
      by rw [hreg₆ r101_sLen (by decide) (by decide) (by decide), hrsLen₅],
      by rw [hreg₆ r101_P1Len (by decide) (by decide) (by decide), hrP1_5],
      by rw [hreg₆ r101_P2Len (by decide) (by decide) (by decide), hrP2_5],
      by rw [hreg₆ r101_P3Len (by decide) (by decide) (by decide), hrP3_5],
      hrvOf₆, hrvOfPLen₆, hs_sub, hstep1.2.2.1,
      by simp [hInt, hstep1, hstep4],
      fun a ha => harr_lt30 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      fun reg hlt hne hcase =>
        hreg_lt64 reg hlt hne (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · simp only [Bool.not_eq_true] at hInt
    have hisInt0 : isInt = 0 := by simp [isInt, hInt]
    have hcond : (Expr.op .eq (.reg r101_isInt) (.const 1)).eval w s₂ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrisInt₂, hisInt0, hw, h0_w]
    rcases allocEmptyArrProg_exec (a101_sSeq p) r101_sLen hw s₂ with
      ⟨s₃, t₃, hex₃, ht₃, hsSeq₃, hrsLen₃, harr₃, hreg₃⟩
    rcases allocEmptyArrProg_exec (a101_P1 p) r101_P1Len hw s₃ with
      ⟨s₄, t₄, hex₄, ht₄, hP1_4, hrP1_4, harr₄, hreg₄⟩
    rcases allocEmptyArrProg_exec (a101_P2 p) r101_P2Len hw s₄ with
      ⟨s₅, t₅, hex₅, ht₅, hP2_5, hrP2_5, harr₅, hreg₅⟩
    rcases allocEmptyArrProg_exec (a101_P3 p) r101_P3Len hw s₅ with
      ⟨s₆, t₆, hex₆, ht₆, hP3_6, hrP3_6, harr₆, hreg₆⟩
    let s₇ := s₆.setReg r101_vOf 0
    have hex₇ : Exec w (.assign r101_vOf (.const 0)) s₆ s₇ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    rcases allocEmptyArrProg_exec (a101_vOfPath p) r101_vOfPathLen hw s₇ with
      ⟨s₈, t₈, hex₈, ht₈, hvOfP₈, hrvOfPLen₈, harr₈, hreg₈⟩
    have harr_lt30 : ∀ a < a101_sSeq p, s₈.arrs a = s₂.arrs a := by
      intro a ha
      rw [harr₈ a (by omega)]
      simp only [s₇, State.setReg_arrs]
      rw [harr₆ a (by omega), harr₅ a (by omega), harr₄ a (by omega), harr₃ a (by omega)]
    have hreg_lt65 : ∀ reg < r101_base, (reg < r101_sLen ∨ reg = r101_visPos) → s₈.regs reg = s₂.regs reg := by
      intro reg hlt hcase
      rw [hreg₈ reg (by omega)]
      simp only [s₇, State.setReg, Function.update, eq_rec_constant, dite_eq_ite,
        ite_eq_right (show ¬(reg = r101_vOf) by omega)]
      rw [hreg₆ reg (by omega), hreg₅ reg (by omega), hreg₄ reg (by omega), hreg₃ reg (by omega)]
    refine ⟨s₈, t₁ + (t₂ + (3 + (t₃ + (t₄ + (t₅ + (t₆ + (2 + t₈))))))),
      [], [], [], [], 0, [],
      .seq hex₁ (.seq hex₂ (.ite_false hcond
        (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈))))))),
      by omega,
      hstream₁.of_arr_eq (by rw [harr_lt30 _ (by omega), harr₂]),
      by rw [hreg_lt65 r101_off (by decide) (by decide), hreg₂ r101_off (by decide) (by decide), hroff₁],
      by rw [harr_lt30 _ (by omega), harr₂, hrV₁],
      by rw [hreg_lt65 r101_vLen (by decide) (by decide), hreg₂ r101_vLen (by decide) (by decide), hrvLen₁],
      by rw [harr_lt30 _ (by omega), harr₂, hrE₁],
      by rw [hreg_lt65 r101_rELen (by decide) (by decide), hreg₂ r101_rELen (by decide) (by decide), hrrELen₁],
      by rw [harr_lt30 _ (by omega), harr₂, hrPar₁],
      by rw [hreg_lt65 r101_rT (by decide) (by decide), hreg₂ r101_rT (by decide) (by decide), hrrT₁],
      by rw [harr_lt30 _ (by omega), harr₂, hrTau₁],
      by rw [hreg_lt65 r101_isInt (by decide) (by decide), hrisInt₂],
      by rw [harr₈ _ (by omega)]; simp only [s₇, State.setReg_arrs]; rw [harr₆ _ (by omega), harr₅ _ (by omega), harr₄ _ (by omega), hsSeq₃],
      by rw [harr₈ _ (by omega)]; simp only [s₇, State.setReg_arrs]; rw [harr₆ _ (by omega), harr₅ _ (by omega), hP1_4],
      by rw [harr₈ _ (by omega)]; simp only [s₇, State.setReg_arrs]; rw [harr₆ _ (by omega), hP2_5],
      by rw [harr₈ _ (by omega)]; simp [s₇, hP3_6],
      hvOfP₈,
      by rw [hreg₈ r101_sLen (by decide)]; simp only [s₇, State.setReg_regs]; rw [ite_eq_right (by decide), hreg₆ r101_sLen (by decide), hreg₅ r101_sLen (by decide), hreg₄ r101_sLen (by decide), hrsLen₃]; rfl,
      by rw [hreg₈ r101_P1Len (by decide)]; simp only [s₇, State.setReg_regs]; rw [ite_eq_right (by decide), hreg₆ r101_P1Len (by decide), hreg₅ r101_P1Len (by decide), hrP1_4]; rfl,
      by rw [hreg₈ r101_P2Len (by decide)]; simp only [s₇, State.setReg_regs]; rw [ite_eq_right (by decide), hreg₆ r101_P2Len (by decide), hrP2_5]; rfl,
      by rw [hreg₈ r101_P3Len (by decide)]; simp [s₇, hrP3_6],
      by rw [hreg₈ r101_vOf (by decide)]; simp [s₇],
      hrvOfPLen₈,
      by simp,
      by simp,
      by simp [hInt],
      fun a ha => by rw [harr_lt30 a (by omega), harr_s₂ a (by omega) (by omega) (by omega) (by omega)],
      fun reg hlt hne hcase => by
        rw [hreg_lt65 reg hlt (by omega), hreg_s₂ reg hlt hne (by omega) (by omega) (by omega) (by omega)]⟩

/-! ### Section 3, Part B: Step 2 $\tilde{A}$ Construction (`alg101MemberStep2Prog`) -/

/-- Part B of member iteration: builds `a101_sInd p`, `a101_tildeV p`, `r101_nA`, `a101_tildeE p`,
and `r101_mA`. -/
def alg101MemberStep2Prog (p : ℕ) : Cmd :=
  .seq (buildListIndProg (a101_sSeq p) (a101_sInd p) r101_sLen r101_n r101_base)
    (.seq (buildTildeAVListProg (a101_sSeq p) (a101_xSeq p) (a101_rV p)
        (a101_sInd p) (a101_buf p) (a101_tildeV p)
        r101_sLen r101_xLen r101_vLen r101_nA r101_base)
      (buildTildeAEListProg (a101_G p) (a101_xInd p) (a101_KInd p) (a101_owner p)
        (a101_rE p) (a101_buf p) (a101_tildeE p)
        r101_rELen r101_j r101_m r101_mA r101_base))

theorem alg101MemberStep2Prog_exec {w n p : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (xSeq : List ℕ) (hx_lt : ∀ v ∈ xSeq, v < n) (hx_len : xSeq.length ≤ n)
    (j : Fin blk.members.length)
    (sSeq : List ℕ) (hs_sub : ∀ s₀ ∈ sSeq, s₀ ∈ (blk.members[j.1]'j.2).vList)
    (hs_len : sSeq.length ≤ 3)
    (hw3 : 3 < 2 ^ w) (h2n_w : 2 * n + 4 < 2 ^ w)
    (hM_w : blk.members.length < 2 ^ w)
    (henc_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hcapE_w : 6 * G.numEdges + 1 < 2 ^ w)
    (hwords : ∀ x ∈ (blk.members[j.1]'j.2).enc, x < 2 ^ w)
    {s : State}
    (hG : s.arrs (a101_G p) = G.enc)
    (hxSeq : s.arrs (a101_xSeq p) = xSeq)
    (hxInd : s.arrs (a101_xInd p) = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ xSeq)))
    (hKInd : s.arrs (a101_KInd p) = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ blk.K_vList)))
    (howner : s.arrs (a101_owner p) = List.ofFn (fun u : Fin n => vertOwner blk u.1))
    (hrV : s.arrs (a101_rV p) = (blk.members[j.1]'j.2).vList)
    (hrE : s.arrs (a101_rE p) = encEdgeTriples (blk.members[j.1]'j.2).eList)
    (hsSeq : s.arrs (a101_sSeq p) = sSeq)
    (hrn : s.regs r101_n = n)
    (hrm : s.regs r101_m = G.numEdges)
    (hrxLen : s.regs r101_xLen = xSeq.length)
    (hrj : s.regs r101_j = j.1)
    (hrvLen : s.regs r101_vLen = (blk.members[j.1]'j.2).vList.length)
    (hrrELen : s.regs r101_rELen = (blk.members[j.1]'j.2).eList.length)
    (hrsLen : s.regs r101_sLen = sSeq.length) :
    let r := blk.members[j.1]'j.2
    let vList := memberTildeAVList xSeq r sSeq
    let eList_A := memberTildeAEList G blk xSeq j
    ∃ s' t,
      Exec w (alg101MemberStep2Prog p) s s' t ∧
      t ≤ 2 * n + 65 * (xSeq.length + r.vList.length + 4) +
        102 * r.eList.length + 172 * G.numEdges + 120 ∧
      s'.arrs (a101_tildeV p) = vList ∧
      s'.regs r101_nA = vList.length ∧
      s'.arrs (a101_tildeE p) = encEdgeTriples eList_A ∧
      s'.regs r101_mA = eList_A.length ∧
      (∀ a < a101_sInd p, s'.arrs a = s.arrs a) ∧
      (∀ reg < r101_base, reg ≠ r101_nA → reg ≠ r101_mA → s'.regs reg = s.regs reg) := by
  dsimp only
  have hw : 1 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hr : (blk.members[j.1]'j.2) ∈ blk.members := List.getElem_mem j.2
  have hr_val := blk.member_valid_iff hr
  have hv_lt : ∀ v ∈ (blk.members[j.1]'j.2).vList, v < n := fun v hv => blk.member_vList_lt hr hv
  have hs_lt : ∀ v ∈ sSeq, v < n := fun v hv => hv_lt v (hs_sub v hv)
  have hv_len_le : (blk.members[j.1]'j.2).vList.length ≤ n := hr_val.1
  have hrE_le : (blk.members[j.1]'j.2).eList.length ≤ G.numEdges :=
    le_trans hr_val.2.2.2.1 (G.numEdges_deleteVertices_le X')
  have hrE_w : ∀ x ∈ encEdgeTriples (blk.members[j.1]'j.2).eList, x < 2 ^ w := fun x hx =>
    hwords x (by rw [(blk.members[j.1]'j.2).enc_eq_append]; simp [hx])
  -- 1. buildListIndProg for sSeq
  rcases buildListIndProg_exec sSeq hs_lt
      (a101_sSeq p) (a101_sInd p) r101_sLen r101_n r101_base
      (by omega) (by decide) (by decide) hw hn_w (by omega) hsSeq hrsLen hrn with
    ⟨s₁, t₁, hex₁, ht₁, hsInd₁, harr₁, hreg₁⟩
  -- 2. buildTildeAVListProg
  have hcapV_w : sSeq.length + xSeq.length + (blk.members[j.1]'j.2).vList.length < 2 ^ w := by omega
  rcases buildTildeAVListProg_exec xSeq (blk.members[j.1]'j.2) sSeq hs_lt hx_lt hv_lt
      (a101_sSeq p) (a101_xSeq p) (a101_rV p) (a101_sInd p) (a101_buf p) (a101_tildeV p)
      r101_sLen r101_xLen r101_vLen r101_nA r101_base
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hw hn_w hcapV_w
      (by rw [harr₁ _ (by omega), hsSeq])
      (by rw [harr₁ _ (by omega), hxSeq])
      (by rw [harr₁ _ (by omega), hrV])
      hsInd₁
      (by rw [hreg₁ r101_sLen (by decide), hrsLen])
      (by rw [hreg₁ r101_xLen (by decide), hrxLen])
      (by rw [hreg₁ r101_vLen (by decide), hrvLen]) with
    ⟨s₂, t₂, hex₂, ht₂, htildeV₂, hrnA₂, harr₂, hreg₂⟩
  -- 3. buildTildeAEListProg
  have hG₂ : s₂.arrs (a101_G p) = G.enc ++ [] := by
    rw [List.append_nil, harr₂, harr₁, hG] <;> omega
  rcases buildTildeAEListProg_exec G blk xSeq j []
      (a101_G p) (a101_xInd p) (a101_KInd p) (a101_owner p) (a101_rE p)
      (a101_buf p) (a101_tildeE p)
      r101_rELen r101_j r101_m r101_mA r101_base
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hw3 hn_w hM_w henc_w (by omega) hrE_w
      hG₂
      (by rw [harr₂, harr₁, hxInd] <;> omega)
      (by rw [harr₂, harr₁, hKInd] <;> omega)
      (by rw [harr₂, harr₁, howner] <;> omega)
      (by rw [harr₂, harr₁, hrE] <;> omega)
      (by rw [hreg₂ r101_rELen (by decide) (by decide), hreg₁ r101_rELen (by decide), hrrELen])
      (by rw [hreg₂ r101_j (by decide) (by decide), hreg₁ r101_j (by decide), hrj])
      (by rw [hreg₂ r101_m (by decide) (by decide), hreg₁ r101_m (by decide), hrm]) with
    ⟨s₃, t₃, hex₃, ht₃, htildeE₃, hrmA₃, harr₃, hreg₃⟩
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by rw [harr₃, htildeV₂] <;> omega,
    by rw [hreg₃ r101_nA (by decide) (by decide), hrnA₂],
    htildeE₃, hrmA₃,
    fun a ha => by
      rw [harr₃ a (by omega) (by omega), harr₂ a (by omega) (by omega), harr₁ a (by omega)],
    fun reg hlt h1 h2 => by
      rw [hreg₃ reg hlt h2, hreg₂ reg hlt h1, hreg₁ reg hlt]⟩

/-! ### Section 4, Part C: Step 3 Folio Code, Vision Record Append, and Summary Table Writes -/

/-- Unpacked program specification for `Alg41Spec101 p (q + 3) δ (max ω 2 + q)` with fixed
program `prog41` and constants `c41, C41`. -/
def Alg41ProgSpec (p q δ ω : ℕ) (prog41 : Cmd) (c41 C41 : ℕ) : Prop :=
  ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
    (t : ℕ) (par f_tau : ℕ → ℕ) (s₀ : State),
    let b := alg105ArrBase p
    let N := n_i + G_i.numEdges + 1
    wordSize c41 N ≤ w →
    Z_i.card ≤ q + 3 →
    IsWrittenDigraphBD (max ω 2 + q) G_i.toComputeDigraph t par f_tau →
    s₀.arrs b = G_i.enc →
    s₀.arrs (b + 1) = bitSetList Z_i →
    s₀.regs 26 = n_i →
    s₀.regs 28 = G_i.numEdges →
    s₀.regs 52 = t →
    (s₀.arrs (b + 2)).length = t →
    (∀ z < t, (s₀.arrs (b + 2)).getD z 0 = par z) →
    (s₀.arrs (b + 3)).length = G_i.numEdges →
    (∀ e < G_i.numEdges, (s₀.arrs (b + 3)).getD e 0 = f_tau e) →
    s₀.arrs (b + 5) =
      List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.tail e).1) →
    s₀.arrs (b + 6) =
      List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.head e).1) →
    ∃ (s₀' : State) (time : ℕ) (out : ParsedFolioAndModels G_i Z_i δ),
      Exec w prog41 s₀ s₀' time ∧
      time ≤ C41 * N ∧
      (s₀'.arrs outArr).length ≤ C41 * N ∧
      (∀ x ∈ s₀'.arrs outArr, x < 2 ^ w) ∧
      parseFolioAndModelsFull G_i Z_i δ (s₀'.arrs outArr) = some out ∧
      IsDeltaFolioRep δ G_i Z_i out.folio

/-- Branch-decomposition validity for member `r` of a parsed Case 3 block. -/
def MemberBranchDecompValid {n : ℕ} (G : MultiDigraph n) (X' : Finset (Fin n)) (ω : ℕ)
    (r : Case3MemberRecord) : Prop :=
  let A := r.toSubgraph (delGraph G X')
  let bd := r.toBranchDecomp
  E(A).ncard ≤ 1 ∨
    (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
      GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω)

/-- Work-size upper bound `(blk.members[j.1]'j.2).vList.length + (memberTildeAEList G blk xSeq j).length + (q + 4)`
for member `j : Fin blk.members.length`. -/
def memberWorkSize {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X') (q : ℕ) (xSeq : List ℕ)
    (j : Fin blk.members.length) : ℕ :=
  (blk.members[j.1]'j.2).vList.length + (memberTildeAEList G blk xSeq j).length + (q + 4)

theorem length_memberTildeA_le_memberWorkSize {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X') (q : ℕ)
    (xSeq : List ℕ) (hx_len : xSeq.length ≤ q)
    (j : Fin blk.members.length)
    (sSeq : List ℕ) (hs_len : sSeq.length ≤ 3) :
    (memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length +
      (memberTildeAEList G blk xSeq j).length + 1 ≤
      memberWorkSize G blk q xSeq j := by
  unfold memberTildeAVList memberWorkSize
  simp only [List.length_append]
  have hfilt := List.length_filter_le (fun v => decide (v ∉ sSeq)) (blk.members[j.1]'j.2).vList
  omega

/-- Part C of member iteration: if `r101_isInt == 1`, assigns `r101_kA := r101_sLen + r101_xLen` and
runs `runInteriorStep3Prog`; otherwise initializes `a101_folioWords p = []`, `r101_folioLen = 0`,
`r101_folioCode = 0`. Then appends `m.enc` to `a101_visBuf p` at `r101_visPos` and writes
`(r101_isInt, r101_vOf, r101_folioCode)` into `(a101_memIsInt p, a101_memVOf p, a101_memFolioCode p)`
at index `r101_j`. -/
def alg101MemberStep3AndAppendProg (p q δ : ℕ) (prog41 : Cmd) : Cmd :=
  .seq
    (.ite (.op .eq (.reg r101_isInt) (.const 1))
      (.seq (.assign r101_kA (.op .add (.reg r101_sLen) (.reg r101_xLen)))
        (runInteriorStep3Prog p q δ prog41
          (a101_tildeV p) (a101_tildeE p) (a101_rE p) (a101_rPar p) (a101_rTau p) (a101_xInd p)
          (a101_zA p) (a101_vIdx p) (a101_mult p) (a101_buf p) (a101_folioWords p)
          r101_n r101_nA r101_mA r101_kA r101_rELen r101_rT r101_folioLen r101_folioCode r101_base
          r101_R_off (a101_A_off p)))
      (.seq (allocEmptyArrProg (a101_folioWords p) r101_folioLen)
        (.assign r101_folioCode (.const 0))))
    (.seq
      (appendVisionMemberRecordProg
        (a101_sSeq p) (a101_P1 p) (a101_P2 p) (a101_P3 p)
        (a101_tildeV p) (a101_tildeE p) (a101_folioWords p) (a101_vOfPath p) (a101_visBuf p)
        r101_isInt r101_sLen r101_P1Len r101_P2Len r101_P3Len r101_nA r101_mA
        r101_folioLen r101_folioCode r101_vOf r101_vOfPathLen r101_visPos r101_base)
      (.seq (.write (a101_memIsInt p) (.reg r101_j) (.reg r101_isInt))
        (.seq (.write (a101_memVOf p) (.reg r101_j) (.reg r101_vOf))
          (.write (a101_memFolioCode p) (.reg r101_j) (.reg r101_folioCode)))))

theorem alg101MemberStep3AndAppendProg_exec {w n p q δ ω c41 C41 : ℕ}
    {prog41 : Cmd}
    (h41 : Alg41ProgSpec p q δ ω prog41 c41 C41)
    (G : MultiDigraph n) {X' : Finset (Fin n)} (hx_card : X'.card ≤ q)
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hWS : GM13.IsWallSociety (delGraph G X') blk.toGMWall blk.toSociety)
    (hRD : GM13.IsRuralDivision blk.toSociety blk.toDivision)
    (xSeq : List ℕ) (hx_nd : xSeq.Nodup) (hx_set : xSeq.toFinset = X'.image Fin.val)
    (j : Fin blk.members.length)
    (sSeq P₁ P₂ P₃ : List ℕ) (vOf : ℕ) (vOfPath : List ℕ)
    (hs_sub : ∀ s₀ ∈ sSeq, s₀ ∈ (blk.members[j.1]'j.2).vList)
    (hs_len : sSeq.length ≤ 3)
    (hstep14 :
      if isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) then
        Step1AttachmentValid blk (blk.members[j.1]'j.2) sSeq P₁ P₂ P₃ ∧
        Step4VOfValid blk (blk.members[j.1]'j.2) vOf vOfPath
      else
        sSeq = [] ∧ P₁ = [] ∧ P₂ = [] ∧ P₃ = [] ∧ vOf = 0 ∧ vOfPath = [])
    (hbd_in : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true →
      MemberBranchDecompValid G X' ω (blk.members[j.1]'j.2))
    (pfx : List ℕ) (rem_cap : ℕ)
    (recs_pfx : List VisionMemberRecord) (hrecs_len : recs_pfx.length = j.1) (rem_m : ℕ)
    (hw6 : 6 < 2 ^ w) (h2n_w : 2 + 6 * (n * n) < 2 ^ w)
    (h3m_w : 3 * G.numEdges + 1 < 2 ^ w)
    (hM_w : blk.members.length < 2 ^ w)
    (hwords : ∀ x ∈ (blk.members[j.1]'j.2).enc, x < 2 ^ w)
    (hw41 : wordSize c41 (n + G.numEdges + 1) ≤ w)
    (h41_len_w : C41 * (n + G.numEdges + 1) < 2 ^ w)
    (hpfx_w : pfx.length + memberPerCap C41 n G.numEdges < 2 ^ w)
    (hw_code : maxFolioRepCode q δ < 2 ^ w)
    (hw_len : maxFolioEncLen101 q δ < 2 ^ w)
    (hw_word : maxFolioEncWord q δ + 1 < 2 ^ w)
    (hw_q : q + 4 < 2 ^ w)
    {s : State}
    (hvisBuf : IsPrefixBuffer (a101_visBuf p) pfx (memberPerCap C41 n G.numEdges + rem_cap) s)
    (hrvisPos : s.regs r101_visPos = pfx.length)
    (hmemInt : s.arrs (a101_memIsInt p) =
      recs_pfx.map VisionMemberRecord.isInterior ++ List.replicate (rem_m + 1) 0)
    (hmemVOf : s.arrs (a101_memVOf p) =
      recs_pfx.map VisionMemberRecord.vOf ++ List.replicate (rem_m + 1) 0)
    (hmemFCode : s.arrs (a101_memFolioCode p) =
      recs_pfx.map VisionMemberRecord.folioCode ++ List.replicate (rem_m + 1) 0)
    (hxInd : s.arrs (a101_xInd p) = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ xSeq)))
    (hrE : s.arrs (a101_rE p) = encEdgeTriples (blk.members[j.1]'j.2).eList)
    (hrPar : s.arrs (a101_rPar p) = (blk.members[j.1]'j.2).parList)
    (hrTau : s.arrs (a101_rTau p) = (blk.members[j.1]'j.2).tauList)
    (hsSeq : s.arrs (a101_sSeq p) = sSeq)
    (hP1 : s.arrs (a101_P1 p) = P₁)
    (hP2 : s.arrs (a101_P2 p) = P₂)
    (hP3 : s.arrs (a101_P3 p) = P₃)
    (hvOfP : s.arrs (a101_vOfPath p) = vOfPath)
    (htildeV : s.arrs (a101_tildeV p) = memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq)
    (htildeE : s.arrs (a101_tildeE p) = encEdgeTriples (memberTildeAEList G blk xSeq j))
    (hrn : s.regs r101_n = n)
    (hrxLen : s.regs r101_xLen = xSeq.length)
    (hrj : s.regs r101_j = j.1)
    (hrrELen : s.regs r101_rELen = (blk.members[j.1]'j.2).eList.length)
    (hrrT : s.regs r101_rT = (blk.members[j.1]'j.2).t_len)
    (hrisInt : s.regs r101_isInt = if isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) then 1 else 0)
    (hrsLen : s.regs r101_sLen = sSeq.length)
    (hrP1Len : s.regs r101_P1Len = P₁.length)
    (hrP2Len : s.regs r101_P2Len = P₂.length)
    (hrP3Len : s.regs r101_P3Len = P₃.length)
    (hrvOf : s.regs r101_vOf = vOf)
    (hrvOfPLen : s.regs r101_vOfPathLen = vOfPath.length)
    (hrnA : s.regs r101_nA = (memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length)
    (hrmA : s.regs r101_mA = (memberTildeAEList G blk xSeq j).length) :
    let r := blk.members[j.1]'j.2
    ∃ (s' : State) (t : ℕ) (m : VisionMemberRecord),
      Exec w (alg101MemberStep3AndAppendProg p q δ prog41) s s' t ∧
      t ≤ n + 600 * (memberWorkSize G blk q xSeq j) ^ 2 +
        35 * (C41 * (n + G.numEdges + 1)) + 324 * (n + G.numEdges + 1) +
        ((maxFolioEncLen101 q δ + 1) * (4 * maxFolioEncWord q δ + 10) + 4 * (q + 4)) + 40 ∧
      isValidVisionMemberRecord G X' blk q δ xSeq r m = true ∧
      VisionMemberRecordFolioValid blk.wallSec.W δ xSeq r m ∧
      m.tildeA_eList = memberTildeAEList G blk xSeq j ∧
      m.enc.length ≤ memberPerCap C41 n G.numEdges ∧
      IsPrefixBuffer (a101_visBuf p) (pfx ++ m.enc)
        ((memberPerCap C41 n G.numEdges - m.enc.length) + rem_cap) s' ∧
      s'.regs r101_visPos = (pfx ++ m.enc).length ∧
      s'.arrs (a101_memIsInt p) =
        (recs_pfx ++ [m]).map VisionMemberRecord.isInterior ++ List.replicate rem_m 0 ∧
      s'.arrs (a101_memVOf p) =
        (recs_pfx ++ [m]).map VisionMemberRecord.vOf ++ List.replicate rem_m 0 ∧
      s'.arrs (a101_memFolioCode p) =
        (recs_pfx ++ [m]).map VisionMemberRecord.folioCode ++ List.replicate rem_m 0 ∧
      (∀ a < a101_zA p,
        a ≠ a101_visBuf p → a ≠ a101_memIsInt p → a ≠ a101_memVOf p → a ≠ a101_memFolioCode p →
          s'.arrs a = s.arrs a) ∧
      (∀ reg < 60, reg ≠ r101_visPos → s'.regs reg = s.regs reg) := by
  dsimp only
  have hw1 : 1 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn1_w : n + 1 < 2 ^ w := by have := Nat.le_mul_self n; omega
  have hn_w : n < 2 ^ w := by omega
  have hm_w : G.numEdges < 2 ^ w := by omega
  have hj_w : j.1 < 2 ^ w := Nat.lt_trans j.2 hM_w
  have hr : (blk.members[j.1]'j.2) ∈ blk.members := List.getElem_mem j.2
  have hr_val := blk.member_valid_iff hr
  have hx_len_q : xSeq.length ≤ q := by
    rw [← List.toFinset_card_of_nodup hx_nd, hx_set,
      Finset.card_image_of_injective _ Fin.val_injective]
    exact hx_card
  have he_len_le : (memberTildeAEList G blk xSeq j).length ≤ G.numEdges :=
    length_memberTildeAEList_le_numEdges G blk hWS hRD hx_set j
  have hwork_le := length_memberTildeA_le_memberWorkSize G blk q xSeq hx_len_q j sSeq hs_len
  have hwork_sq := Nat.pow_le_pow_left hwork_le 2
  have hStep3 :
      ∃ (s₁ : State) (t₁ : ℕ) (m : VisionMemberRecord),
        Exec w
          (.ite (.op .eq (.reg r101_isInt) (.const 1))
            (.seq (.assign r101_kA (.op .add (.reg r101_sLen) (.reg r101_xLen)))
              (runInteriorStep3Prog p q δ prog41
                (a101_tildeV p) (a101_tildeE p) (a101_rE p) (a101_rPar p) (a101_rTau p) (a101_xInd p)
                (a101_zA p) (a101_vIdx p) (a101_mult p) (a101_buf p) (a101_folioWords p)
                r101_n r101_nA r101_mA r101_kA r101_rELen r101_rT r101_folioLen r101_folioCode r101_base
                r101_R_off (a101_A_off p)))
            (.seq (allocEmptyArrProg (a101_folioWords p) r101_folioLen)
              (.assign r101_folioCode (.const 0))))
          s s₁ t₁ ∧
        t₁ ≤ n + 600 * (memberWorkSize G blk q xSeq j) ^ 2 +
          17 * (C41 * (n + G.numEdges + 1)) +
          ((maxFolioEncLen101 q δ + 1) * (4 * maxFolioEncWord q δ + 10) + 4 * (q + 4)) + 20 ∧
        isValidVisionMemberRecord G X' blk q δ xSeq (blk.members[j.1]'j.2) m = true ∧
        VisionMemberRecordFolioValid blk.wallSec.W δ xSeq (blk.members[j.1]'j.2) m ∧
        m.tildeA_eList = memberTildeAEList G blk xSeq j ∧
        m.enc.length ≤ memberPerCap C41 n G.numEdges ∧
        (∀ x ∈ m.enc, x < 2 ^ w) ∧
        s₁.arrs (a101_sSeq p) = m.sSeq ∧ s₁.arrs (a101_P1 p) = m.P₁ ∧
        s₁.arrs (a101_P2 p) = m.P₂ ∧ s₁.arrs (a101_P3 p) = m.P₃ ∧
        s₁.arrs (a101_tildeV p) = m.tildeA_vList ∧
        s₁.arrs (a101_tildeE p) = encEdgeTriples m.tildeA_eList ∧
        s₁.arrs (a101_folioWords p) = m.folioWords ∧ s₁.arrs (a101_vOfPath p) = m.vOfPath ∧
        s₁.regs r101_isInt = m.isInterior ∧ s₁.regs r101_sLen = m.sSeq.length ∧
        s₁.regs r101_P1Len = m.P₁.length ∧ s₁.regs r101_P2Len = m.P₂.length ∧
        s₁.regs r101_P3Len = m.P₃.length ∧ s₁.regs r101_nA = m.tildeA_vList.length ∧
        s₁.regs r101_mA = m.tildeA_eList.length ∧ s₁.regs r101_folioLen = m.folioWords.length ∧
        s₁.regs r101_folioCode = m.folioCode ∧ s₁.regs r101_vOf = m.vOf ∧
        s₁.regs r101_vOfPathLen = m.vOfPath.length ∧
        (∀ a < a101_zA p, s₁.arrs a = s.arrs a) ∧
        (∀ reg < r101_base, (reg < r101_kA ∨ reg = r101_visPos) → s₁.regs reg = s.regs reg) := by
    by_cases hInt : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true
    · simp only [hInt, ↓reduceIte] at hstep14 hrisInt
      rcases hstep14 with ⟨hstep1, hstep4⟩
      have hs_nd : sSeq.Nodup := hstep1.1
      have hv_len_le : (memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length ≤ n :=
        length_memberTildeAVList_le_n blk hx_nd hx_set hr hs_nd hs_sub
      have hcond : (Expr.op .eq (.reg r101_isInt) (.const 1)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrisInt, hw1]
      have hsx_w : (sSeq ++ xSeq).length < 2 ^ w := by rw [List.length_append]; omega
      let s₀ := s.setReg r101_kA (sSeq ++ xSeq).length
      have hex₀ : Exec w (.assign r101_kA (.op .add (.reg r101_sLen) (.reg r101_xLen))) s s₀ 4 :=
        .assign (by
          rw [List.length_append] at hsx_w
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrsLen, hrxLen,
            show sSeq.length < 2 ^ w by omega, show xSeq.length < 2 ^ w by omega, hsx_w])
      have hcap_enc_w :
          2 + 6 * ((memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length *
            (memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length) < 2 ^ w := by
        have := Nat.mul_le_mul hv_len_le hv_len_le; omega
      have hrT_w : (blk.members[j.1]'j.2).t_len < 2 ^ w :=
        hwords (blk.members[j.1]'j.2).t_len (by rw [(blk.members[j.1]'j.2).enc_eq_append]; simp)
      have hrE_w : ∀ x ∈ encEdgeTriples (blk.members[j.1]'j.2).eList, x < 2 ^ w := fun x hx =>
        hwords x (by rw [(blk.members[j.1]'j.2).enc_eq_append]; simp [hx])
      have hrPar_w : ∀ x ∈ (blk.members[j.1]'j.2).parList, x < 2 ^ w := fun x hx =>
        hwords x (by rw [(blk.members[j.1]'j.2).enc_eq_append]; simp [hx])
      have hrTau_w : ∀ x ∈ (blk.members[j.1]'j.2).tauList, x < 2 ^ w := fun x hx =>
        hwords x (by rw [(blk.members[j.1]'j.2).enc_eq_append]; simp [hx])
      have hw41' : wordSize c41 ((memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length +
          (memberTildeAEList G blk xSeq j).length + 1) ≤ w :=
        (wordSize_mono_right c41 (by omega)).trans hw41
      have h41_len_w' : C41 * ((memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length +
          (memberTildeAEList G blk xSeq j).length + 1) < 2 ^ w :=
        lt_of_le_of_lt (Nat.mul_le_mul_left C41 (by omega)) h41_len_w
      rcases runInteriorStep3Prog_exec G blk xSeq sSeq j prog41 (@h41 w) hWS hRD
          hx_nd hx_set hx_card hs_nd hs_sub hs_len (hbd_in hInt)
          (a101_tildeV p) (a101_tildeE p) (a101_rE p) (a101_rPar p) (a101_rTau p) (a101_xInd p)
          (a101_zA p) (a101_vIdx p) (a101_mult p) (a101_buf p) (a101_folioWords p)
          r101_n r101_nA r101_mA r101_kA r101_rELen r101_rT r101_folioLen r101_folioCode r101_base
          r101_R_off (a101_A_off p)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
          hw6 hn_w hcap_enc_w (by omega) hrT_w hrE_w hrPar_w hrTau_w
          hw41' h41_len_w' hw_code hw_len hw_word hw_q (s := s₀)
          (by simp [s₀, htildeV]) (by simp [s₀, htildeE]) (by simp [s₀, hrE])
          (by simp [s₀, hrPar]) (by simp [s₀, hrTau]) (by simp [s₀, hxInd])
          (by simp [s₀, hrn]) (by simp [s₀, hrnA]) (by simp [s₀, hrmA])
          (by simp [s₀]) (by simp [s₀, hrrELen]) (by simp [s₀, hrrT]) with
        ⟨s₁, t₁, folioWords, folioCode, out, hex₁, ht₁, hfw₁, hrfLen₁, hrfCode₁,
          hfw_len, hfw_w, hfc_w, hparse, hrep, hcode_eq, harr₁, hreg₁⟩
      let m : VisionMemberRecord :=
        ⟨1, sSeq, P₁, P₂, P₃, memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq,
          memberTildeAEList G blk xSeq j, folioWords, folioCode, vOf, vOfPath⟩
      rcases isValidVisionMemberRecord_of_interior blk hWS hRD hx_nd hx_set j hInt
          hstep1 hstep4 hparse hcode_eq hfw_len hw3 hn1_w hm_w
          (lt_of_le_of_lt hfw_len h41_len_w') hfw_w hfc_w with
        ⟨hm_val, hm_len, hm_w⟩
      have hm_fval : VisionMemberRecordFolioValid blk.wallSec.W δ xSeq (blk.members[j.1]'j.2) m :=
        fun _ folioOut hp => Option.some.inj (hp.symm.trans hparse) ▸ hrep
      have harr_lt40 : ∀ a < a101_zA p, s₁.arrs a = s.arrs a := fun a ha => by
        rw [harr₁ a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; rfl
      have hreg_lt72 : ∀ reg < r101_base, (reg < r101_kA ∨ reg = r101_visPos) → s₁.regs reg = s.regs reg :=
        fun reg hlt hcase => by
          rw [hreg₁ reg hlt (by omega) (by omega)]
          simp [s₀, State.setReg, show reg ≠ r101_kA by omega]
      have ht_bound :
          3 + (4 + t₁) ≤
            n + 600 * (memberWorkSize G blk q xSeq j) ^ 2 +
              17 * (C41 * (n + G.numEdges + 1)) +
              ((maxFolioEncLen101 q δ + 1) * (4 * maxFolioEncWord q δ + 10) + 4 * (q + 4)) + 20 := by
        have hlin :
            17 * C41 * ((memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length +
              (memberTildeAEList G blk xSeq j).length + 1) ≤
              17 * (C41 * (n + G.numEdges + 1)) := by
          rw [Nat.mul_assoc]
          exact Nat.mul_le_mul_left 17 (Nat.mul_le_mul_left C41 (by omega))
        have hquad := Nat.mul_le_mul_left 600 hwork_sq
        omega
      refine ⟨s₁, 3 + (4 + t₁), m, .ite_true hcond (by decide) (.seq hex₀ hex₁),
        ht_bound, hm_val, hm_fval, rfl, hm_len, hm_w,
        by rw [harr_lt40 _ (by omega), hsSeq], by rw [harr_lt40 _ (by omega), hP1],
        by rw [harr_lt40 _ (by omega), hP2], by rw [harr_lt40 _ (by omega), hP3],
        by rw [harr_lt40 _ (by omega), htildeV], by rw [harr_lt40 _ (by omega), htildeE],
        hfw₁, by rw [harr_lt40 _ (by omega), hvOfP],
        by rw [hreg_lt72 r101_isInt (by decide) (by decide), hrisInt],
        by rw [hreg_lt72 r101_sLen (by decide) (by decide), hrsLen],
        by rw [hreg_lt72 r101_P1Len (by decide) (by decide), hrP1Len],
        by rw [hreg_lt72 r101_P2Len (by decide) (by decide), hrP2Len],
        by rw [hreg_lt72 r101_P3Len (by decide) (by decide), hrP3Len],
        by rw [hreg_lt72 r101_nA (by decide) (by decide), hrnA],
        by rw [hreg_lt72 r101_mA (by decide) (by decide), hrmA],
        hrfLen₁, hrfCode₁,
        by rw [hreg_lt72 r101_vOf (by decide) (by decide), hrvOf],
        by rw [hreg_lt72 r101_vOfPathLen (by decide) (by decide), hrvOfPLen],
        harr_lt40, hreg_lt72⟩
    · simp only [Bool.not_eq_true] at hInt
      simp only [hInt, Bool.false_eq_true, ↓reduceIte] at hstep14 hrisInt
      rcases hstep14 with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hcond : (Expr.op .eq (.reg r101_isInt) (.const 1)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrisInt, hw1, h0_w]
      rcases allocEmptyArrProg_exec (a101_folioWords p) r101_folioLen hw1 s with
        ⟨s₀, t₀, hex₀, ht₀, hfw₀, hrfLen₀, harr₀, hreg₀⟩
      let s₁ := s₀.setReg r101_folioCode 0
      have hex₁ : Exec w (.assign r101_folioCode (.const 0)) s₀ s₁ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      let m : VisionMemberRecord :=
        ⟨0, [], [], [], [], memberTildeAVList xSeq (blk.members[j.1]'j.2) [],
          memberTildeAEList G blk xSeq j, [], 0, 0, []⟩
      rcases isValidVisionMemberRecord_of_nonInterior blk hWS hRD hx_nd hx_set j hInt hn_w hm_w hw1 with
        ⟨hm_val, hm_len, hm_w⟩
      have hm_fval : VisionMemberRecordFolioValid blk.wallSec.W δ xSeq (blk.members[j.1]'j.2) m :=
        fun h => by rw [hInt] at h; nomatch h
      have harr_lt40 : ∀ a < a101_zA p, s₁.arrs a = s.arrs a := fun a ha =>
        harr₀ a (by omega)
      have hreg_lt72 : ∀ reg < r101_base, (reg < r101_kA ∨ reg = r101_visPos) → s₁.regs reg = s.regs reg :=
        fun reg hlt hcase => by
          dsimp only [s₁]
          rw [State.setReg_regs_ne _ _ (show reg ≠ r101_folioCode by omega), hreg₀ reg (by omega)]
      refine ⟨s₁, 3 + (t₀ + 2), m, .ite_false hcond (.seq hex₀ hex₁),
        by omega, hm_val, hm_fval, rfl, hm_len, hm_w,
        by rw [harr_lt40 _ (by omega), hsSeq], by rw [harr_lt40 _ (by omega), hP1],
        by rw [harr_lt40 _ (by omega), hP2], by rw [harr_lt40 _ (by omega), hP3],
        by rw [harr_lt40 _ (by omega), htildeV], by rw [harr_lt40 _ (by omega), htildeE],
        by simp [s₁, hfw₀, m], by rw [harr_lt40 _ (by omega), hvOfP],
        by rw [hreg_lt72 r101_isInt (by decide) (by decide), hrisInt],
        by rw [hreg_lt72 r101_sLen (by decide) (by decide), hrsLen],
        by rw [hreg_lt72 r101_P1Len (by decide) (by decide), hrP1Len],
        by rw [hreg_lt72 r101_P2Len (by decide) (by decide), hrP2Len],
        by rw [hreg_lt72 r101_P3Len (by decide) (by decide), hrP3Len],
        by rw [hreg_lt72 r101_nA (by decide) (by decide), hrnA],
        by rw [hreg_lt72 r101_mA (by decide) (by decide), hrmA],
        by simp [s₁, hrfLen₀, m], by simp [s₁, m],
        by rw [hreg_lt72 r101_vOf (by decide) (by decide), hrvOf],
        by rw [hreg_lt72 r101_vOfPathLen (by decide) (by decide), hrvOfPLen],
        harr_lt40, hreg_lt72⟩
  rcases hStep3 with
    ⟨s₁, t₁, m, hex₁, ht₁, hm_val, hm_fval, hm_eList, hm_len, hm_w,
      hsSeq₁, hP1_1, hP2_1, hP3_1, htildeV₁, htildeE₁, hfw₁, hvOfP₁,
      hrInt₁, hrsLen₁, hrP1Len₁, hrP2Len₁, hrP3Len₁, hrnA₁, hrmA₁,
      hrfLen₁, hrfCode₁, hrvOf₁, hrvOfPLen₁, harr₁, hreg₁⟩
  -- 2. appendVisionMemberRecordProg
  let rem_cap' := (memberPerCap C41 n G.numEdges - m.enc.length) + rem_cap
  have hvisBuf₁ : IsPrefixBuffer (a101_visBuf p) pfx (m.enc.length + rem_cap') s₁ := by
    unfold IsPrefixBuffer at hvisBuf ⊢
    rw [harr₁ (a101_visBuf p) (by omega), hvisBuf]
    have hrep : memberPerCap C41 n G.numEdges + rem_cap = m.enc.length + rem_cap' := by
      dsimp [rem_cap']; omega
    rw [hrep]
  rcases appendVisionMemberRecordProg_exec (cap := rem_cap') m
      (a101_sSeq p) (a101_P1 p) (a101_P2 p) (a101_P3 p)
      (a101_tildeV p) (a101_tildeE p) (a101_folioWords p) (a101_vOfPath p) (a101_visBuf p)
      r101_isInt r101_sLen r101_P1Len r101_P2Len r101_P3Len r101_nA r101_mA
      r101_folioLen r101_folioCode r101_vOf r101_vOfPathLen r101_visPos r101_base
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw3 hm_w (by omega) hvisBuf₁
      (by rw [hreg₁ r101_visPos (by decide) (by decide), hrvisPos])
      hsSeq₁ hP1_1 hP2_1 hP3_1 htildeV₁ htildeE₁ hfw₁ hvOfP₁
      hrInt₁ hrsLen₁ hrP1Len₁ hrP2Len₁ hrP3Len₁ hrnA₁ hrmA₁ hrfLen₁ hrfCode₁ hrvOf₁ hrvOfPLen₁ with
    ⟨s₂, t₂, hex₂, ht₂, hvisBuf₂, hrvisPos₂, harr₂, hreg₂⟩
  -- 3. Three .write commands to a101_memIsInt, a101_memVOf, a101_memFolioCode
  have hrj₂ : s₂.regs r101_j = j.1 := by
    rw [hreg₂ r101_j (by decide) (by decide), hreg₁ r101_j (by decide) (by decide), hrj]
  have hrInt₂ : s₂.regs r101_isInt = m.isInterior := by
    rw [hreg₂ r101_isInt (by decide) (by decide), hrInt₁]
  have hrvOf₂ : s₂.regs r101_vOf = m.vOf := by
    rw [hreg₂ r101_vOf (by decide) (by decide), hrvOf₁]
  have hrfCode₂ : s₂.regs r101_folioCode = m.folioCode := by
    rw [hreg₂ r101_folioCode (by decide) (by decide), hrfCode₁]
  have hint_w : m.isInterior < 2 ^ w := hm_w _ (by unfold VisionMemberRecord.enc; simp)
  have hvOf_w : m.vOf < 2 ^ w := hm_w _ (by unfold VisionMemberRecord.enc; simp)
  have hfc_w : m.folioCode < 2 ^ w := hm_w _ (by unfold VisionMemberRecord.enc; simp)
  have hmemInt₂ :
      s₂.arrs (a101_memIsInt p) =
        recs_pfx.map VisionMemberRecord.isInterior ++ List.replicate (rem_m + 1) 0 := by
    rw [harr₂ (a101_memIsInt p) (by omega), harr₁ (a101_memIsInt p) (by omega), hmemInt]
  have hlen_Int₂ : j.1 < (s₂.arrs (a101_memIsInt p)).length := by
    rw [hmemInt₂, List.length_append, List.length_map, hrecs_len, List.length_replicate]; omega
  let s₃ := s₂.writeArr (a101_memIsInt p) j.1 m.isInterior
  have hex₃ : Exec w (.write (a101_memIsInt p) (.reg r101_j) (.reg r101_isInt)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, hrj₂, hj_w])
      (by simp [Expr.eval, checkWord, hrInt₂, hint_w]) hlen_Int₂
  have hmemVOf₃ :
      s₃.arrs (a101_memVOf p) =
        recs_pfx.map VisionMemberRecord.vOf ++ List.replicate (rem_m + 1) 0 := by
    dsimp only [s₃]
    rw [State.writeArr_arrs_ne _ _ _ (show a101_memVOf p ≠ a101_memIsInt p by omega),
      harr₂ (a101_memVOf p) (by omega), harr₁ (a101_memVOf p) (by omega), hmemVOf]
  have hlen_VOf₃ : j.1 < (s₃.arrs (a101_memVOf p)).length := by
    rw [hmemVOf₃, List.length_append, List.length_map, hrecs_len, List.length_replicate]; omega
  let s₄ := s₃.writeArr (a101_memVOf p) j.1 m.vOf
  have hex₄ : Exec w (.write (a101_memVOf p) (.reg r101_j) (.reg r101_vOf)) s₃ s₄ 3 :=
    .write (by simp [s₃, Expr.eval, checkWord, hrj₂, hj_w])
      (by simp [s₃, Expr.eval, checkWord, hrvOf₂, hvOf_w]) hlen_VOf₃
  have hmemFCode₄ :
      s₄.arrs (a101_memFolioCode p) =
        recs_pfx.map VisionMemberRecord.folioCode ++ List.replicate (rem_m + 1) 0 := by
    dsimp only [s₄, s₃]
    rw [State.writeArr_arrs_ne _ _ _ (show a101_memFolioCode p ≠ a101_memVOf p by omega),
      State.writeArr_arrs_ne _ _ _ (show a101_memFolioCode p ≠ a101_memIsInt p by omega),
      harr₂ (a101_memFolioCode p) (by omega), harr₁ (a101_memFolioCode p) (by omega), hmemFCode]
  have hlen_FCode₄ : j.1 < (s₄.arrs (a101_memFolioCode p)).length := by
    rw [hmemFCode₄, List.length_append, List.length_map, hrecs_len, List.length_replicate]; omega
  let s₅ := s₄.writeArr (a101_memFolioCode p) j.1 m.folioCode
  have hex₅ : Exec w (.write (a101_memFolioCode p) (.reg r101_j) (.reg r101_folioCode)) s₄ s₅ 3 :=
    .write (by simp [s₄, s₃, Expr.eval, checkWord, hrj₂, hj_w])
      (by simp [s₄, s₃, Expr.eval, checkWord, hrfCode₂, hfc_w]) hlen_FCode₄
  have ht₂_le : t₂ ≤ 18 * (C41 * (n + G.numEdges + 1)) + 324 * (n + G.numEdges + 1) := by
    have h1 := Nat.mul_le_mul_left 18 hm_len; dsimp [memberPerCap] at h1; omega
  refine ⟨s₅, t₁ + (t₂ + (3 + (3 + 3))), m,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hm_val, hm_fval, hm_eList, hm_len,
    hvisBuf₂.of_arr_eq (by
      dsimp only [s₅, s₄, s₃]
      rw [State.writeArr_arrs_ne _ _ _ (show a101_visBuf p ≠ a101_memFolioCode p by omega),
        State.writeArr_arrs_ne _ _ _ (show a101_visBuf p ≠ a101_memVOf p by omega),
        State.writeArr_arrs_ne _ _ _ (show a101_visBuf p ≠ a101_memIsInt p by omega)]),
    by simp [s₅, s₄, s₃, hrvisPos₂],
    by dsimp only [s₅, s₄, s₃]
       rw [State.writeArr_arrs_ne _ _ _ (show a101_memIsInt p ≠ a101_memFolioCode p by omega),
         State.writeArr_arrs_ne _ _ _ (show a101_memIsInt p ≠ a101_memVOf p by omega),
         State.writeArr_arrs_self, hmemInt₂]
       have hlen_eq : (recs_pfx.map VisionMemberRecord.isInterior).length = j.1 := by
         rw [List.length_map, hrecs_len]
       rw [← hlen_eq, set_append_replicate_succ, List.map_append, List.map_singleton],
    by dsimp only [s₅, s₄]
       rw [State.writeArr_arrs_ne _ _ _ (show a101_memVOf p ≠ a101_memFolioCode p by omega),
         State.writeArr_arrs_self, hmemVOf₃]
       have hlen_eq : (recs_pfx.map VisionMemberRecord.vOf).length = j.1 := by
         rw [List.length_map, hrecs_len]
       rw [← hlen_eq, set_append_replicate_succ, List.map_append, List.map_singleton],
    by dsimp only [s₅]
       rw [State.writeArr_arrs_self, hmemFCode₄]
       have hlen_eq : (recs_pfx.map VisionMemberRecord.folioCode).length = j.1 := by
         rw [List.length_map, hrecs_len]
       rw [← hlen_eq, set_append_replicate_succ, List.map_append, List.map_singleton],
    fun a ha h1 h2 h3 h4 => by
      dsimp only [s₅, s₄, s₃]
      rw [State.writeArr_arrs_ne _ _ _ h4, State.writeArr_arrs_ne _ _ _ h3,
        State.writeArr_arrs_ne _ _ _ h2, harr₂ a h1, harr₁ a ha],
    fun reg hlt hne => by
      simp only [s₅, s₄, s₃, State.writeArr_regs]
      rw [hreg₂ reg (by omega) hne, hreg₁ reg (by omega) (by omega)]⟩

/-! ### Section 5: Complete Member Step (`alg101MemberStepProg`) -/

/-- Complete body of the member loop for a single member `j`: runs Part A (stream read, interior
check, Steps 1 & 4), Part B (Step 2 $\tilde{A}$ construction), and Part C (Step 3 folio code,
vision record append, and summary table writes). -/
def alg101MemberStepProg (p q δ : ℕ) (prog41 : Cmd) : Cmd :=
  .seq (alg101MemberStep14Prog p)
    (.seq (alg101MemberStep2Prog p)
      (alg101MemberStep3AndAppendProg p q δ prog41))

/-- Linear per-member time bound component (independent of `j`). -/
def memberLinearCost (n m q δ C41 : ℕ) : ℕ :=
  35 * (C41 * (n + m + 1)) + 1950 * (n + m + 1) +
    ((maxFolioEncLen101 q δ + 1) * (4 * maxFolioEncWord q δ + 10) + 4 * (q + 4))

theorem alg101MemberStepProg_exec {w n p q q_C δ ω c41 C41 : ℕ}
    {prog41 : Cmd}
    (h41 : Alg41ProgSpec p q δ ω prog41 c41 C41)
    (G : MultiDigraph n) {X' : Finset (Fin n)} (hx_card : X'.card ≤ q)
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph q_C X'.toNatSet blk.toGMWall blk.toSociety blk.toDivision)
    (xSeq : List ℕ) (hx_nd : xSeq.Nodup) (hx_set : xSeq.toFinset = X'.image Fin.val)
    (lists : Fin n → List ℕ) (htot_lists : totalAdjEntries lists ≤ 2 * G.numEdges)
    (j : Fin blk.members.length)
    (hbd_in : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true →
      MemberBranchDecompValid G X' ω (blk.members[j.1]'j.2))
    (rest : List ℕ) (off : ℕ)
    (pfx : List ℕ) (rem_cap : ℕ)
    (recs_pfx : List VisionMemberRecord) (hrecs_len : recs_pfx.length = j.1) (rem_m : ℕ)
    (hw6 : 6 < 2 ^ w) (h2n_w : 2 * n + 4 < 2 ^ w)
    (h2nsq_w : 2 + 6 * (n * n) < 2 ^ w)
    (hcapE_w : 6 * G.numEdges + 1 < 2 ^ w)
    (hM_w : blk.members.length < 2 ^ w)
    (henc_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hwords : ∀ x ∈ (blk.members[j.1]'j.2).enc, x < 2 ^ w)
    (hoff_w : off + (blk.members[j.1]'j.2).enc.length < 2 ^ w)
    (hw41 : wordSize c41 (n + G.numEdges + 1) ≤ w)
    (h41_len_w : C41 * (n + G.numEdges + 1) < 2 ^ w)
    (hpfx_w : pfx.length + memberPerCap C41 n G.numEdges < 2 ^ w)
    (hw_code : maxFolioRepCode q δ < 2 ^ w)
    (hw_len : maxFolioEncLen101 q δ < 2 ^ w)
    (hw_word : maxFolioEncWord q δ + 1 < 2 ^ w)
    (hw_q : q + 4 < 2 ^ w)
    {s : State}
    (hstream : AtStream (a101_block p) off ((blk.members[j.1]'j.2).enc ++ rest) s)
    (hroff : s.regs r101_off = off)
    (hvisBuf : IsPrefixBuffer (a101_visBuf p) pfx (memberPerCap C41 n G.numEdges + rem_cap) s)
    (hrvisPos : s.regs r101_visPos = pfx.length)
    (hmemInt : s.arrs (a101_memIsInt p) =
      recs_pfx.map VisionMemberRecord.isInterior ++ List.replicate (rem_m + 1) 0)
    (hmemVOf : s.arrs (a101_memVOf p) =
      recs_pfx.map VisionMemberRecord.vOf ++ List.replicate (rem_m + 1) 0)
    (hmemFCode : s.arrs (a101_memFolioCode p) =
      recs_pfx.map VisionMemberRecord.folioCode ++ List.replicate (rem_m + 1) 0)
    (hG : s.arrs (a101_G p) = G.enc)
    (hxSeq : s.arrs (a101_xSeq p) = xSeq)
    (hxInd : s.arrs (a101_xInd p) = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ xSeq)))
    (hperim : s.arrs (a101_perim p) = bitSetList blk.wallSec.W.perimFinset)
    (hWH : s.arrs (a101_WH p) = bitSetList blk.wallSec.W.vertexFinset)
    (hcor : s.arrs (a101_corners p) = blk.corners)
    (hKInd : s.arrs (a101_KInd p) = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ blk.K_vList)))
    (hisC : s.arrs (a101_isCorner p) =
      bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ blk.corners)))
    (hdegK : s.arrs (a101_degK p) = List.ofFn (fun v : Fin n => incEdgeCount blk.K_eList v.1))
    (hadj : IsAdjList (G.deleteVertices (Z_notK blk)).toSimpleGraph
      (a101_start p) (a101_end p) (a101_entries p) lists s)
    (hent_w : (s.arrs (a101_entries p)).length < 2 ^ w)
    (howner : s.arrs (a101_owner p) = List.ofFn (fun u : Fin n => vertOwner blk u.1))
    (hrn : s.regs r101_n = n)
    (hrm : s.regs r101_m = G.numEdges)
    (hrxLen : s.regs r101_xLen = xSeq.length)
    (hrj : s.regs r101_j = j.1) :
    let r := blk.members[j.1]'j.2
    ∃ (s' : State) (t : ℕ) (m : VisionMemberRecord),
      Exec w (alg101MemberStepProg p q δ prog41) s s' t ∧
      t + 7 ≤ memberLinearCost n G.numEdges q δ C41 + 600 * (memberWorkSize G blk q xSeq j) ^ 2 ∧
      AtStream (a101_block p) (off + r.enc.length) rest s' ∧
      s'.regs r101_off = off + r.enc.length ∧
      isValidVisionMemberRecord G X' blk q δ xSeq r m = true ∧
      VisionMemberRecordFolioValid blk.wallSec.W δ xSeq r m ∧
      m.tildeA_eList = memberTildeAEList G blk xSeq j ∧
      m.enc.length ≤ memberPerCap C41 n G.numEdges ∧
      IsPrefixBuffer (a101_visBuf p) (pfx ++ m.enc)
        ((memberPerCap C41 n G.numEdges - m.enc.length) + rem_cap) s' ∧
      s'.regs r101_visPos = (pfx ++ m.enc).length ∧
      s'.arrs (a101_memIsInt p) =
        (recs_pfx ++ [m]).map VisionMemberRecord.isInterior ++ List.replicate rem_m 0 ∧
      s'.arrs (a101_memVOf p) =
        (recs_pfx ++ [m]).map VisionMemberRecord.vOf ++ List.replicate rem_m 0 ∧
      s'.arrs (a101_memFolioCode p) =
        (recs_pfx ++ [m]).map VisionMemberRecord.folioCode ++ List.replicate rem_m 0 ∧
      (∀ a < a101_rV p,
        a ≠ a101_visBuf p → a ≠ a101_memIsInt p → a ≠ a101_memVOf p → a ≠ a101_memFolioCode p →
          s'.arrs a = s.arrs a) ∧
      (∀ reg < 60, reg ≠ r101_off → reg ≠ r101_visPos → s'.regs reg = s.regs reg) := by
  dsimp only
  have hw3 : 3 < 2 ^ w := by omega
  have hr : (blk.members[j.1]'j.2) ∈ blk.members := List.getElem_mem j.2
  have hr_val := blk.member_valid_iff hr
  have hv_len_le : (blk.members[j.1]'j.2).vList.length ≤ n := hr_val.1
  have hdel_le : (G.deleteVertices X').numEdges ≤ G.numEdges := G.numEdges_deleteVertices_le X'
  have hrE_le : (blk.members[j.1]'j.2).eList.length ≤ G.numEdges := le_trans hr_val.2.2.2.1 hdel_le
  have hrT_le : (blk.members[j.1]'j.2).t_len ≤ 2 * G.numEdges + 1 := by have := hr_val.2.2.2.2.2.2.2.1; omega
  have hx_lt : ∀ v ∈ xSeq, v < n := fun v hv => by
    have hv_fin : v ∈ X'.image Fin.val := hx_set ▸ List.mem_toFinset.mpr hv
    rcases Finset.mem_image.mp hv_fin with ⟨u, _, rfl⟩; exact u.2
  have hx_len_n : xSeq.length ≤ n := by
    rw [← List.toFinset_card_of_nodup hx_nd, hx_set,
      Finset.card_image_of_injective _ Fin.val_injective]
    exact le_trans (Finset.card_le_univ X') (by simp)
  -- 1. Part A: alg101MemberStep14Prog
  rcases alg101MemberStep14Prog_exec blk hC j lists rest off
      hw6 (by omega) (by omega) hwords hoff_w
      hstream hroff hrn hperim hWH hcor hisC hdegK hadj hent_w with
    ⟨s₁, t₁, sSeq, P₁, P₂, P₃, vOf, vOfPath, hex₁, ht₁,
      hstream₁, hroff₁, hrV₁, hrvLen₁, hrE₁, hrrELen₁, hrPar₁, hrrT₁, hrTau₁,
      hrisInt₁, hsSeq₁, hP1_1, hP2_1, hP3_1, hvOfP₁,
      hrsLen₁, hrP1Len₁, hrP2Len₁, hrP3Len₁, hrvOf₁, hrvOfPLen₁,
      hs_sub, hs_len, hstep14, harr₁, hreg₁⟩
  -- 2. Part B: alg101MemberStep2Prog
  rcases alg101MemberStep2Prog_exec G blk xSeq hx_lt hx_len_n j sSeq hs_sub hs_len
      hw3 h2n_w hM_w henc_w hcapE_w hwords (s := s₁)
      (by rw [harr₁ _ (by omega), hG]) (by rw [harr₁ _ (by omega), hxSeq])
      (by rw [harr₁ _ (by omega), hxInd]) (by rw [harr₁ _ (by omega), hKInd])
      (by rw [harr₁ _ (by omega), howner]) hrV₁ hrE₁ hsSeq₁
      (by rw [hreg₁ r101_n (by decide) (by decide) (by decide), hrn])
      (by rw [hreg₁ r101_m (by decide) (by decide) (by decide), hrm])
      (by rw [hreg₁ r101_xLen (by decide) (by decide) (by decide), hrxLen])
      (by rw [hreg₁ r101_j (by decide) (by decide) (by decide), hrj])
      hrvLen₁ hrrELen₁ hrsLen₁ with
    ⟨s₂, t₂, hex₂, ht₂, htildeV₂, hrnA₂, htildeE₂, hrmA₂, harr₂, hreg₂⟩
  -- 3. Part C: alg101MemberStep3AndAppendProg
  have hWS : GM13.IsWallSociety (delGraph G X') blk.toGMWall blk.toSociety := by
    rw [delGraph_eq]; exact hC.isWallSociety
  have hRD : GM13.IsRuralDivision blk.toSociety blk.toDivision := hC.isRuralDivision
  rcases alg101MemberStep3AndAppendProg_exec h41 G hx_card blk hWS hRD
      xSeq hx_nd hx_set j sSeq P₁ P₂ P₃ vOf vOfPath hs_sub hs_len hstep14 hbd_in
      pfx rem_cap recs_pfx hrecs_len rem_m
      hw6 h2nsq_w (by omega) hM_w hwords hw41 h41_len_w hpfx_w hw_code hw_len hw_word hw_q
      (s := s₂)
      (hvisBuf.of_arr_eq (by rw [harr₂ _ (by omega), harr₁ _ (by omega)]))
      (by rw [hreg₂ r101_visPos (by decide) (by decide) (by decide),
            hreg₁ r101_visPos (by decide) (by decide) (by decide), hrvisPos])
      (by rw [harr₂ _ (by omega), harr₁ _ (by omega), hmemInt])
      (by rw [harr₂ _ (by omega), harr₁ _ (by omega), hmemVOf])
      (by rw [harr₂ _ (by omega), harr₁ _ (by omega), hmemFCode])
      (by rw [harr₂ _ (by omega), harr₁ _ (by omega), hxInd])
      (by rw [harr₂ _ (by omega), hrE₁]) (by rw [harr₂ _ (by omega), hrPar₁])
      (by rw [harr₂ _ (by omega), hrTau₁]) (by rw [harr₂ _ (by omega), hsSeq₁])
      (by rw [harr₂ _ (by omega), hP1_1]) (by rw [harr₂ _ (by omega), hP2_1])
      (by rw [harr₂ _ (by omega), hP3_1]) (by rw [harr₂ _ (by omega), hvOfP₁])
      htildeV₂ htildeE₂
      (by rw [hreg₂ r101_n (by decide) (by decide) (by decide),
            hreg₁ r101_n (by decide) (by decide) (by decide), hrn])
      (by rw [hreg₂ r101_xLen (by decide) (by decide) (by decide),
            hreg₁ r101_xLen (by decide) (by decide) (by decide), hrxLen])
      (by rw [hreg₂ r101_j (by decide) (by decide) (by decide),
            hreg₁ r101_j (by decide) (by decide) (by decide), hrj])
      (by rw [hreg₂ r101_rELen (by decide) (by decide) (by decide), hrrELen₁])
      (by rw [hreg₂ r101_rT (by decide) (by decide) (by decide), hrrT₁])
      (by rw [hreg₂ r101_isInt (by decide) (by decide) (by decide), hrisInt₁])
      (by rw [hreg₂ r101_sLen (by decide) (by decide) (by decide), hrsLen₁])
      (by rw [hreg₂ r101_P1Len (by decide) (by decide) (by decide), hrP1Len₁])
      (by rw [hreg₂ r101_P2Len (by decide) (by decide) (by decide), hrP2Len₁])
      (by rw [hreg₂ r101_P3Len (by decide) (by decide) (by decide), hrP3Len₁])
      (by rw [hreg₂ r101_vOf (by decide) (by decide) (by decide), hrvOf₁])
      (by rw [hreg₂ r101_vOfPathLen (by decide) (by decide) (by decide), hrvOfPLen₁])
      hrnA₂ hrmA₂ with
    ⟨s₃, t₃, m, hex₃, ht₃, hm_val, hm_fval, hm_eList, hm_len, hvisBuf₃, hrvisPos₃,
      hmemInt₃, hmemVOf₃, hmemFCode₃, harr₃, hreg₃⟩
  have ht_total :
      t₁ + (t₂ + t₃) + 7 ≤
        memberLinearCost n G.numEdges q δ C41 + 600 * (memberWorkSize G blk q xSeq j) ^ 2 := by
    unfold memberLinearCost; omega
  refine ⟨s₃, t₁ + (t₂ + t₃), m, .seq hex₁ (.seq hex₂ hex₃), ht_total,
    hstream₁.of_arr_eq (by rw [harr₃, harr₂] <;> omega),
    by rw [hreg₃ r101_off (by decide) (by decide),
         hreg₂ r101_off (by decide) (by decide) (by decide), hroff₁],
    hm_val, hm_fval, hm_eList, hm_len, hvisBuf₃, hrvisPos₃, hmemInt₃, hmemVOf₃, hmemFCode₃,
    fun a ha h1 h2 h3 h4 => by
      rw [harr₃ a (by omega) h1 h2 h3 h4, harr₂ a (by omega), harr₁ a ha],
    fun reg hlt h1 h2 => by
      rw [hreg₃ reg hlt h2, hreg₂ reg (by omega) (by omega) (by omega),
          hreg₁ reg (by omega) h1 (by omega)]⟩

end GraphMinor.Compute

