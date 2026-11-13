module

public import GraphMinor.Compute.GM13VisionInput

/-!
# A uniform program for Graph Minors XIII, (10.1)

The wall-input pre-pass has no height parameter. The program then reads the
rural division, initializes the vision stream, and runs the four steps of
(10.1) over its members. The existing attachment, extension, folio, and path
proofs apply to this stream. The time bound is quadratic in the graph size,
with a constant depending only on the fixed root, detail, and width bounds.
-/

@[expose] public section
namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-- The single vision program for all wall heights in XIII (10.1), pages 106–107.
The wall's vertex and perimeter bitsets are part of the wall input representation. -/
def alg101UniformProg (p q δ C41 : ℕ) (prog41 : Cmd) : Cmd :=
  .seq (.seq (alg101WallInputPrePass p) (alg101PrePassPart2Prog p))
    (.seq (alg101InitVisProg p C41)
      (forUp r101_j (.reg r101_M) (alg101MemberStepProg p q δ prog41)))

set_option maxHeartbeats 800000 in
/-- The four member computations of XIII (10.1), pages 106–107, with the
height-independent pre-pass and the quadratic total-work bound. The folio
subroutine specification is discharged in the final algorithm theorem. -/
theorem alg101UniformProg_exec {w n p q q_C δ ω c41 C41 : ℕ} {prog41 : Cmd}
    (h41 : Alg41ProgSpec p q δ ω prog41 c41 C41)
    (G : MultiDigraph n) {X' : Finset (Fin n)} (hx_card : X'.card ≤ q)
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph q_C X'.toNatSet blk.toGMWall blk.toSociety blk.toDivision)
    (hbd_all : ∀ j : Fin blk.members.length,
      isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true →
      MemberBranchDecompValid G X' ω (blk.members[j.1]'j.2))
    (block : List ℕ) (hparse_blk : parseCase3Block (G.deleteVertices X') X' block = some blk)
    (h2nsq_w : 2 + 6 * (n * n) < 2 ^ w) (hN_w : 24 * (n + G.numEdges + 1) < 2 ^ w)
    (hw41 : wordSize c41 (n + G.numEdges + 1) ≤ w) (hC41_w : C41 < 2 ^ w)
    (hvis_cap_w : (2 + n) + (n + G.numEdges + 1) * memberPerCap C41 n G.numEdges < 2 ^ w)
    (hw_code : maxFolioRepCode q δ < 2 ^ w) (hw_len : maxFolioEncLen101 q δ < 2 ^ w)
    (hw_word : maxFolioEncWord q δ + 1 < 2 ^ w) (hw_q : q + 4 < 2 ^ w)
    {s : State} (hG : s.arrs (a101_G p) = G.enc) (hX : s.arrs (a101_X p) = bitSetList X')
    (hblock : s.arrs (a101_block p) = block)
    (hperim : s.arrs (a101_perim p) = bitSetList blk.wallSec.W.perimFinset)
    (hWH : s.arrs (a101_WH p) = bitSetList blk.wallSec.W.vertexFinset) :
    ∃ (s' : State) (t : ℕ) (vOut : ParsedVisionOutput G X' blk q δ),
      Exec w (alg101UniformProg p q δ C41 prog41) s s' t ∧
      t ≤ alg101TimeConst q δ C41 * (n + G.numEdges + 1) ^ 2 ∧
      parseVisionOutput G X' blk q δ (s'.arrs (a101_visBuf p)) = some vOut ∧
      vOut.xSeq = xSeqOf X' ∧
      (∀ (j : Fin blk.members.length)
        (_ : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true)
        (folioOut : ParsedFolioAndModels
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length) δ),
        parseFolioAndModelsFull
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
          δ (vOut.recordAt j).folioWords = some folioOut →
        IsDeltaFolioRep δ
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
          folioOut.folio) ∧
      s'.regs r101_n = n ∧ s'.regs r101_M = blk.members.length ∧
      s'.arrs (a101_W_br p) =
        (List.finRange (elemWallNumVerts blk.wallSec.h)).map
          (fun u => (blk.wallSec.W.branchVert u).1) ∧
      s'.arrs (a101_W_brOf p) = List.ofFn (wallBrOf blk.wallSec.W) ∧
      s'.arrs (a101_W_edgeOf p) = List.ofFn (wallEdgeOf blk.wallSec.W) ∧
      s'.arrs (a101_memIsInt p) = vOut.records.map VisionMemberRecord.isInterior ∧
      s'.arrs (a101_memVOf p) = vOut.records.map VisionMemberRecord.vOf ∧
      s'.arrs (a101_memFolioCode p) = vOut.records.map VisionMemberRecord.folioCode ∧
      (∀ a < alg105ArrBase p, s'.arrs a = s.arrs a) ∧
      (∀ (r : ℕ), r < 50 → s'.regs r = s.regs r) := by
  let N := n + G.numEdges + 1
  have hWS : GM13.IsWallSociety (delGraph G X') blk.toGMWall blk.toSociety := by
    rw [delGraph_eq]; exact hC.isWallSociety
  have hRD : GM13.IsRuralDivision blk.toSociety blk.toDivision := hC.isRuralDivision
  have hDiv : GM13.IsSocietyDivision blk.toSociety blk.toDivision := hRD.1
  have hw18 : 18 < 2 ^ w := by omega
  have hw6 : 6 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm_w : G.numEdges < 2 ^ w := by omega
  have hact_le_m : G.numActivePairs ≤ G.numEdges := G.numActivePairs_le_numEdges
  have hact_le_nsq : G.numActivePairs ≤ n * n := G.numActivePairs_le_sq
  have hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w := by omega
  have hwall_len_le : blk.wallSec.W.encList.length ≤ 3 + 3 * n :=
    blk.wallSec.W.length_encList_le blk.wallSec.hW
  have hKVL_le : blk.K_vList.length ≤ n := blk.hK_v_len
  have hKEL_le : blk.K_eList.length ≤ G.numEdges :=
    le_trans blk.hK_e_len (G.numEdges_deleteVertices_le X')
  have hM_le : blk.members.length ≤ n + G.numEdges + 1 := by
    have := blk.hmembers_len; have := G.numEdges_deleteVertices_le X'; omega
  have hflat_mem_le : (blk.members.flatMap Case3MemberRecord.enc).length ≤ 14 * (n + G.numEdges + 1) :=
    blk.length_flatMap_member_enc_le hDiv
  have hper_ge : 18 ≤ memberPerCap C41 n G.numEdges := by unfold memberPerCap; omega
  have hper_w : memberPerCap C41 n G.numEdges < 2 ^ w := by
    have := Nat.mul_le_mul_right (memberPerCap C41 n G.numEdges) (show 1 ≤ n + G.numEdges + 1 by omega)
    omega
  have h41_len_w : C41 * (n + G.numEdges + 1) < 2 ^ w := by
    have : C41 * (n + G.numEdges + 1) ≤ memberPerCap C41 n G.numEdges := by unfold memberPerCap; omega
    omega
  rcases eq_encCase3Block_append_of_parseCase3Block hparse_blk with ⟨rest, hblock_eq⟩
  have hblock_split :
      s.arrs (a101_block p) =
        blk.wallSec.W.encList ++
          ((blk.K_vList.length :: blk.K_vList) ++
            (blk.K_eList.length :: encEdgeTriples blk.K_eList) ++
            blk.corners ++
            (blk.members.length :: blk.members.flatMap Case3MemberRecord.enc) ++ rest) := by
    rw [hblock, hblock_eq]; unfold encCase3Block; simp [List.append_assoc]
  -- 1. Pre-pass Part 1 & Part 2
  rcases alg101WallInputPrePass_exec G X' blk
      ((blk.K_vList.length :: blk.K_vList) ++
        (blk.K_eList.length :: encEdgeTriples blk.K_eList) ++
        blk.corners ++
        (blk.members.length :: blk.members.flatMap Case3MemberRecord.enc) ++ rest)
      hw3 (by omega) hm3_w hm_w (by omega) hG hX hblock_split hperim hWH with
    ⟨s₁, t₁, hex₁, ht₁, hrn₁, hrm₁, hrxLen₁, hroff₁,
      hG₁, _, hxSeq₁, hxInd₁, hWbr₁, hWbrOf₁, hWedgeOf₁, hperim₁, hWH₁,
      hstream₁, harr₁, hreg₁⟩
  have hoff₂_w :
      blk.wallSec.W.encList.length + (1 + blk.K_vList.length) +
        (1 + 3 * blk.K_eList.length) + 4 + 1 +
        (blk.members.flatMap Case3MemberRecord.enc).length < 2 ^ w := by omega
  rcases alg101PrePassPart2Prog_exec G blk hDiv rest
      hw6 hn_w hm3_w (by omega) (by omega) hoff₂_w
      hG₁ hrn₁ hroff₁ hstream₁ with
    ⟨s₂, t₂, hex₂, ht₂, hrM₂, hroff₂, hstream₂,
      hKV₂, hKE₂, hcor₂, hKInd₂, hisC₂, hdegK₂, hadj₂, hent_len₂, htot_lists,
      howner₂, harr₂, hreg₂⟩
  -- 3. Vision Buffer & Summary Initialization
  let xSeq := xSeqOf X'
  have hx_nd : xSeq.Nodup := nodup_xSeqOf X'
  have hx_set : xSeq.toFinset = X'.image Fin.val := toFinset_xSeqOf X'
  have hx_lt : ∀ x ∈ xSeq, x < n := fun _ hx => mem_xSeqOf_lt X' hx
  have hx_len_le : xSeq.length ≤ n := length_xSeqPrefix_le X'
  have hcap_vis_w :
      (2 + xSeq.length) + blk.members.length * memberPerCap C41 n G.numEdges < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add (by omega) (Nat.mul_le_mul_right _ hM_le)) hvis_cap_w
  rcases alg101InitVisProg_exec xSeq hx_lt hw18 hn_w hm_w (by omega)
      hC41_w hcap_vis_w hper_w (s := s₂)
      (by rw [harr₂ (a101_xSeq p) (by omega), hxSeq₁])
      (by rw [hreg₂ r101_n (by decide), hrn₁])
      (by rw [hreg₂ r101_m (by decide), hrm₁])
      (by rw [hreg₂ r101_xLen (by decide), hrxLen₁])
      hrM₂ with
    ⟨s₃, t₃, hex₃, ht₃, hvisBuf₃, hrvisPos₃, hmemInt₃, hmemVOf₃, hmemFCode₃, hrj₃, harr₃, hreg₃⟩
  -- 4. Member Iteration Loop
  have harr_s₃_s₂ : ∀ a < a101_memIsInt p, a ≠ a101_visBuf p → s₃.arrs a = s₂.arrs a :=
    fun a ha hne => harr₃ a hne (by omega) (by omega) (by omega)
  have hreg_s₃_s₂ : ∀ (r : ℕ), r < r101_base → r ≠ r101_visPos → r ≠ r101_j → s₃.regs r = s₂.regs r :=
    hreg₃
  have hwords_all : ∀ r ∈ blk.members, ∀ x ∈ r.enc, x < 2 ^ w := fun r hr x hx =>
    lt_of_le_of_lt (blk.member_enc_le r hr x hx) (by omega)
  rcases alg101MemberLoop_aux h41 G hx_card blk hC hbd_all xSeq hx_nd hx_set
      (edgeNeighbors (edgeListOf (G.deleteVertices (Z_notK blk)).toSimpleGraph))
      (le_trans htot_lists (Nat.mul_le_mul_left 2 hact_le_m)) rest
      hw6 (by omega) h2nsq_w (by omega) (by omega) hm3_w hwords_all
      hw41 h41_len_w hw_code hw_len hw_word hw_q
      blk.members.length 0 (by omega)
      (blk.wallSec.W.encList.length + (1 + blk.K_vList.length) +
        (1 + 3 * blk.K_eList.length) + 4 + 1)
      (by simpa using hoff₂_w) ((xSeq.length :: xSeq) ++ [blk.members.length])
      (blk.members.length * memberPerCap C41 n G.numEdges)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (le_rfl) [] rfl (s := s₃)
      (hstream₂.of_arr_eq (harr_s₃_s₂ (a101_block p) (by omega) (by omega)))
      (by rw [hreg_s₃_s₂ r101_off (by decide) (by decide) (by decide), hroff₂])
      hvisBuf₃ hrvisPos₃ (by simpa using hmemInt₃) (by simpa using hmemVOf₃)
      (by simpa using hmemFCode₃)
      (by rw [harr_s₃_s₂ (a101_G p) (by omega) (by omega), harr₂ (a101_G p) (by omega), hG₁])
      (by rw [harr_s₃_s₂ (a101_xSeq p) (by omega) (by omega), harr₂ (a101_xSeq p) (by omega), hxSeq₁])
      (by rw [harr_s₃_s₂ (a101_xInd p) (by omega) (by omega), harr₂ (a101_xInd p) (by omega), hxInd₁])
      (by rw [harr_s₃_s₂ (a101_perim p) (by omega) (by omega), harr₂ (a101_perim p) (by omega), hperim₁])
      (by rw [harr_s₃_s₂ (a101_WH p) (by omega) (by omega), harr₂ (a101_WH p) (by omega), hWH₁])
      (by rw [harr_s₃_s₂ (a101_corners p) (by omega) (by omega), hcor₂])
      (by rw [harr_s₃_s₂ (a101_KInd p) (by omega) (by omega), hKInd₂])
      (by rw [harr_s₃_s₂ (a101_isCorner p) (by omega) (by omega), hisC₂])
      (by rw [harr_s₃_s₂ (a101_degK p) (by omega) (by omega), hdegK₂])
      (hadj₂.of_arrs_eq (harr_s₃_s₂ (a101_start p) (by omega) (by omega))
        (harr_s₃_s₂ (a101_end p) (by omega) (by omega))
        (harr_s₃_s₂ (a101_entries p) (by omega) (by omega)))
      (by rw [harr_s₃_s₂ (a101_entries p) (by omega) (by omega)]; exact lt_of_le_of_lt hent_len₂ (by omega))
      (by rw [harr_s₃_s₂ (a101_owner p) (by omega) (by omega), howner₂])
      (by rw [hreg_s₃_s₂ r101_n (by decide) (by decide) (by decide), hreg₂ r101_n (by decide), hrn₁])
      (by rw [hreg_s₃_s₂ r101_m (by decide) (by decide) (by decide), hreg₂ r101_m (by decide), hrm₁])
      (by rw [hreg_s₃_s₂ r101_xLen (by decide) (by decide) (by decide), hreg₂ r101_xLen (by decide), hrxLen₁])
      (by rw [hreg_s₃_s₂ r101_M (by decide) (by decide) (by decide), hrM₂])
      hrj₃ with
    ⟨s₄, t₄, records, rem_cap', hex₄, ht₄, hrec_len, hrec_props, hvisBuf₄,
      hmemInt₄, hmemVOf₄, hmemFCode₄, harr₄, hreg₄⟩
  simp only [Nat.zero_add, List.drop_zero, List.nil_append] at ht₄ hrec_props hmemInt₄ hmemVOf₄ hmemFCode₄
  -- 5. Assemble ParsedVisionOutput
  have hmap_eList :
      records.map VisionMemberRecord.tildeA_eList =
        (List.finRange blk.members.length).map (memberTildeAEList G blk xSeq) := by
    apply List.ext_getElem (by simp [hrec_len])
    intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_finRange]
    exact (hrec_props i (by simpa using hi₂) (by simpa [hrec_len] using hi₂)).2.2
  let vOut : ParsedVisionOutput G X' blk q δ :=
    { xSeq := xSeq, records := records, hx_nodup := hx_nd, hx_set := hx_set
      hmembers_ne := blk.members_ne_nil_of_isRuralDivision hWS hRD, hrecords_len := hrec_len
      hrecords_valid := fun j => (hrec_props j.1 j.2 (by rw [hrec_len]; exact j.2)).1
      hedges_nodup := by rw [hmap_eList]; exact flatten_memberTildeAEList_nodup G blk hRD hx_set
      hedges_cover := by rw [hmap_eList]; exact flatten_memberTildeAEList_cover G blk hWS hRD hx_set }
  have hvis_arr :
      s₄.arrs (a101_visBuf p) =
        encVisionOutput vOut.xSeq vOut.records ++ List.replicate rem_cap' 0 := by
    unfold IsPrefixBuffer at hvisBuf₄
    rw [hvisBuf₄]; unfold encVisionOutput; dsimp [vOut]; rw [hrec_len]; simp [List.append_assoc]
  have hparse_vis :
      parseVisionOutput G X' blk q δ (s₄.arrs (a101_visBuf p)) = some vOut := by
    rw [hvis_arr]; exact parseVisionOutput_encVisionOutput vOut (List.replicate rem_cap' 0)
  have hrep_out :
      ∀ (j : Fin blk.members.length)
        (_ : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true)
        (folioOut : ParsedFolioAndModels
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length) δ),
        parseFolioAndModelsFull
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
          δ (vOut.recordAt j).folioWords = some folioOut →
        IsDeltaFolioRep δ
          (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
          (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
            ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
          folioOut.folio := by
    intro j hInt folioOut hp
    exact (hrec_props j.1 j.2 (by rw [hrec_len]; exact j.2)).2.1 hInt folioOut hp
  -- 6. Total time bound
  have hsum_sq := sum_memberWorkSize_sq_le G blk hWS hRD hx_set (q := q)
  have ht_total :
      (t₁ + t₂) + (t₃ + t₄) ≤ alg101TimeConst q δ C41 * N ^ 2 := by
    let F := (maxFolioEncLen101 q δ + 1) * (4 * maxFolioEncWord q δ + 10) + 4 * (q + 4)
    have hN_pos : 1 ≤ N := by dsimp [N]; omega
    have hN_le_sq : N ≤ N * N := Nat.le_mul_self N
    have ht12_sq : t₁ + t₂ ≤ 1560 * (N * N) :=
      le_trans (show t₁ + t₂ ≤ 1560 * N by dsimp [N] at *; omega) (Nat.mul_le_mul_left 1560 hN_le_sq)
    have hM_cap : blk.members.length * memberPerCap C41 n G.numEdges ≤ N * ((C41 + 18) * N) := by
      unfold memberPerCap
      have h1 : blk.members.length * ((C41 + 18) * N) ≤ N * ((C41 + 18) * N) :=
        Nat.mul_le_mul_right ((C41 + 18) * N) hM_le
      have h2 : (C41 + 18) * N = C41 * (n + G.numEdges + 1) + 18 * (n + G.numEdges + 1) := by
        dsimp [N]; ring
      rw [← h2]
      exact h1
    have ht3_le : t₃ ≤ N * ((C41 + 18) * N) + 75 * (N * N) := by
      have : (2 + xSeq.length) + 18 * xSeq.length + 3 * blk.members.length + 50 ≤ 75 * N := by
        dsimp [N] at *; omega
      have := le_trans this (Nat.mul_le_mul_left 75 hN_le_sq); omega
    have hM_lin :
        blk.members.length * memberLinearCost n G.numEdges q δ C41 ≤
          N * (35 * (C41 * N) + 1950 * N + F) := by
      simpa [memberLinearCost, N, F] using
        Nat.mul_le_mul_right (memberLinearCost n G.numEdges q δ C41) hM_le
    have hF_sq : N * F ≤ F * (N * N) := by
      rw [Nat.mul_comm N F]; exact Nat.mul_le_mul_left F hN_le_sq
    have h600_sq :
        600 * (((List.finRange blk.members.length).map
          (fun j => (memberWorkSize G blk q xSeq j) ^ 2)).sum) ≤
          600 * ((q + 10) ^ 2 * (N * N)) := by
      have h1 := Nat.mul_le_mul_left 600 hsum_sq
      have h2 : ((q + 10) * (n + G.numEdges + 1)) ^ 2 = (q + 10) ^ 2 * (N * N) := by
        dsimp [N]; ring
      rwa [h2] at h1
    have h3_sq : 3 ≤ 3 * (N * N) := by have := le_trans hN_pos hN_le_sq; omega
    have halg_eq :
        alg101TimeConst q δ C41 * N ^ 2 =
          600 * ((q + 10) ^ 2 * (N * N)) + N * ((C41 + 18) * N) +
            N * (35 * (C41 * N) + 1950 * N) + F * (N * N) + 2032 * (N * N) := by
      change (600 * (q + 10) ^ 2 + 36 * C41 + 4000 + F) * N ^ 2 = _; ring
    rw [halg_eq]
    have hN_dist := Nat.mul_add N (35 * (C41 * N) + 1950 * N) F
    omega
  have harr_s₄_s₁ : ∀ a < a101_KV p, a ≠ a101_visBuf p → s₄.arrs a = s₁.arrs a :=
    fun a ha hne => by
      rw [harr₄ a (by omega) hne (by omega) (by omega) (by omega),
        harr_s₃_s₂ a (by omega) hne, harr₂ a ha]
  refine ⟨s₄, (t₁ + t₂) + (t₃ + t₄), vOut, .seq (.seq hex₁ hex₂) (.seq hex₃ hex₄), ht_total,
    hparse_vis, rfl, hrep_out,
    by rw [hreg₄ r101_n (by decide), hreg_s₃_s₂ r101_n (by decide) (by decide) (by decide),
         hreg₂ r101_n (by decide), hrn₁],
    by rw [hreg₄ r101_M (by decide), hreg_s₃_s₂ r101_M (by decide) (by decide) (by decide), hrM₂],
    by rw [harr_s₄_s₁ (a101_W_br p) (by omega) (by omega), hWbr₁],
    by rw [harr_s₄_s₁ (a101_W_brOf p) (by omega) (by omega), hWbrOf₁],
    by rw [harr_s₄_s₁ (a101_W_edgeOf p) (by omega) (by omega), hWedgeOf₁],
    hmemInt₄, hmemVOf₄, hmemFCode₄,
    fun a ha => by rw [harr_s₄_s₁ a (by omega) (by omega), harr₁ a ha],
    fun r hr => by
      rw [hreg₄ r (by omega), hreg_s₃_s₂ r (by omega) (by omega) (by omega),
        hreg₂ r (by omega), hreg₁ r hr]⟩


end GraphMinor.Compute
