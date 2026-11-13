module

public import GraphMinor.Compute.Algorithm101Step3

/-!
# Step 3 Interior Folio Computation and Vision Record Serializer for Algorithm (10.1)

This file implements:
1. **Step 3 Interior Member Folio Computation (`runInteriorStep3Prog`):**
   Given `vList = memberTildeAVList xSeq r sSeq` and `eList_A = memberTildeAEList G p xSeq j` for an
   interior member `r = p.members[j]`, constructs `G_A.enc` and `memberFTau0`, runs
   `(convertBDProg b).shiftMem R_off A_off` to extend the branch-decomposition of `G_A \ X_A` of
   width `≤ ω` to a branch-decomposition of `G_A` of width `≤ max ω 2 + q`, invokes
   `prog41.shiftMem R_off A_off` (`Alg41Spec101 p (q + 3) δ (max ω 2 + q)`), copies the resulting
   `folioWords`, and runs `computeFolioRepCodeProg` to compute `folioRepCode q out.folio`.
2. **Vision Member Record Serializer (`appendVisionMemberRecordProg`):**
   Appends the serialized `VisionMemberRecord.enc m` of a member `j < p.members.length` to the
   output buffer `a_visBuf` at cursor `r_visPos`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical Graph

/-! ### Section 1: Step 3 Interior Member Folio Computation (`runInteriorStep3Prog`) -/

theorem numEdges_tildeAMultiDigraph_of_nodup (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ))
    (hv_nd : vList.Nodup) (he_nd : eList.Nodup)
    (he_ends : ∀ e ∈ eList, e.1 ∈ vList ∧ e.2.1 ∈ vList) :
    (tildeAMultiDigraph vList eList).numEdges = eList.length := by
  let D₀ := listDigraph vList eList he_ends
  exact numEdges_tildeAMultiDigraph D₀ vList eList hv_nd rfl he_nd rfl
    (fun e he => ⟨rfl, rfl, (he_ends e he).1, (he_ends e he).2⟩)

theorem bitSetList_words_lt {w n : ℕ} (Z : Finset (Fin n)) (hw : 1 < 2 ^ w) :
    ∀ x ∈ bitSetList Z, x < 2 ^ w := by
  intro x hx
  rcases List.mem_iff_getElem.mp hx with ⟨idx, hidx, rfl⟩
  have hle1 := getElem_bitSetList_le_one Z idx hidx
  omega

/-- Complete Word RAM subprogram for Step 3 of GM XIII Algorithm (10.1) on an interior member `r`:
builds `G_A.enc`, `Z_A`, `X_A`, and `memberFTau0`, runs `(convertBDProg b).shiftMem R_off A_off`,
runs `prog41.shiftMem R_off A_off`, copies `folioWords`, and computes `folioCode`. -/
def runInteriorStep3Prog (p q δ : ℕ) (prog41 : Cmd)
    (a_tildeV a_tildeE a_rE a_rPar a_rTau a_xInd : Arr)
    (a_zA a_vIdx a_mult a_buf a_folioWords : Arr)
    (r_n r_nA r_mA r_kA r_rELen r_rT r_folioLen r_folioCode r_base : Reg)
    (R_off A_off : ℕ) : Cmd :=
  let b := alg105ArrBase p
  .seq (buildTildeABitSetsProg a_tildeV a_xInd a_zA (A_off + (b + 1)) r_nA r_kA r_base)
    (.seq (buildVIdxProg a_tildeV a_vIdx r_n r_nA r_base)
      (.seq (buildEdgeMultMatProg a_vIdx a_tildeE a_mult r_nA r_mA r_base)
        (.seq (buildEncFromMultMatProg a_mult a_buf (A_off + b) r_nA r_folioLen r_base)
          (.seq (buildFTau0Prog a_tildeV a_vIdx a_rE a_rTau a_mult a_buf (A_off + (b + 3))
              r_nA r_rELen r_base)
            (.seq (copyBufPrefixProg a_rPar (A_off + (b + 2)) r_rT r_base)
              (.seq (.assign (R_off + 26) (.reg r_nA))
                (.seq (.assign (R_off + 27) (.reg r_folioLen))
                  (.seq (.assign (R_off + 28) (.reg r_mA))
                    (.seq (.assign (R_off + 52) (.reg r_rT))
                      (.seq ((convertBDProg b).shiftMem R_off A_off)
                        (.seq (.assign r_folioLen (.reg (R_off + 52)))
                          (.seq (copyBufPrefixProg a_zA (A_off + (b + 1)) r_nA r_base)
                            (.seq (.assign (R_off + 26) (.reg r_nA))
                              (.seq (.assign (R_off + 28) (.reg r_mA))
                                (.seq (.assign (R_off + 52) (.reg r_folioLen))
                                  (.seq (prog41.shiftMem R_off A_off)
                                    (.seq (.assign r_folioLen (.len (A_off + outArr)))
                                      (.seq (copyBufPrefixProg (A_off + outArr) a_folioWords r_folioLen r_base)
                                        (computeFolioRepCodeProg q δ a_folioWords r_kA r_folioCode r_base)))))))))))))))))))

private theorem step3_poly_bound (n n_A m_A r_e r_t : ℕ)
    (hr_e : r_e ≤ m_A) (hr_t : r_t ≤ 2 * r_e + 1) :
    (28 * n_A + 20) + (n + 11 * n_A + 10) + (n_A * n_A + 39 * m_A + 12) +
    (135 * (n_A * n_A) + 32 * n_A + 78) +
    (42 * (n_A * n_A) + 15 * n_A + 36 * (r_e * r_e) + 66 * r_e + 34) +
    (16 * r_t + 9) + 350 * (n_A + m_A + 1) ^ 2 + (16 * n_A + 9) + 27 ≤
      n + 600 * (n_A + m_A + 1) ^ 2 := by
  have hre_sq : r_e * r_e ≤ m_A * m_A := Nat.mul_le_mul hr_e hr_e
  have hsq1 : (n_A + m_A + 1) ^ 2 = n_A * n_A + m_A * m_A + 2 * (n_A * m_A) + 2 * n_A + 2 * m_A + 1 := by ring
  rw [hsq1]
  omega

private theorem step3_time_bound {n n_A m_A r_e r_t C41 T_trie : ℕ}
    {t₁ t₂ t₃ t₄ t₅ t₆ t₈ t₉ t₁₀ t₁₁ t₁₂ : ℕ}
    (hr_e : r_e ≤ m_A)
    (hr_t : r_t ≤ 2 * r_e + 1)
    (ht₁ : t₁ ≤ 28 * n_A + 20)
    (ht₂ : t₂ ≤ n + 11 * n_A + 10)
    (ht₃ : t₃ ≤ n_A * n_A + 39 * m_A + 12)
    (ht₄ : t₄ ≤ 135 * (n_A * n_A) + 32 * n_A + 78)
    (ht₅ : t₅ ≤ 42 * (n_A * n_A) + 15 * n_A + 36 * (r_e * r_e) + 66 * r_e + 34)
    (ht₆ : t₆ ≤ 16 * r_t + 9)
    (ht₈ : t₈ ≤ 350 * (n_A + m_A + 1) ^ 2)
    (ht₉ : t₉ ≤ 16 * n_A + 9)
    (ht₁₀ : t₁₀ ≤ C41 * (n_A + m_A + 1))
    (ht₁₁ : t₁₁ ≤ 16 * (C41 * (n_A + m_A + 1)) + 9)
    (ht₁₂ : t₁₂ ≤ T_trie) :
    t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (2 + (2 + (2 + (2 + (t₈ + (2 + (t₉ +
      (2 + (2 + (2 + (t₁₀ + (2 + (t₁₁ + t₁₂)))))))))))))))))) ≤
      n + 600 * (n_A + m_A + 1) ^ 2 +
      17 * C41 * (n_A + m_A + 1) +
      T_trie := by
  have hpoly := step3_poly_bound n n_A m_A r_e r_t hr_e hr_t
  have hmul : 17 * C41 * (n_A + m_A + 1) = 17 * (C41 * (n_A + m_A + 1)) :=
    Nat.mul_assoc 17 C41 (n_A + m_A + 1)
  linarith

theorem runInteriorStep3Prog_exec {w n p q δ ω C41 c41 : ℕ}
    (G : MultiDigraph n) {X' : Finset (Fin n)}
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (xSeq sSeq : List ℕ) (j : Fin blk.members.length)
    (prog41 : Cmd)
    (h41 : ∀ {n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
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
        IsDeltaFolioRep δ G_i Z_i out.folio)
    (hWS : GM13.IsWallSociety (delGraph G X') blk.toGMWall blk.toSociety)
    (hRD : GM13.IsRuralDivision blk.toSociety blk.toDivision)
    (hx_nd : xSeq.Nodup)
    (hx_set : xSeq.toFinset = X'.image Fin.val)
    (hx_card : X'.card ≤ q)
    (hs_nd : sSeq.Nodup)
    (hs_sub : ∀ v ∈ sSeq, v ∈ (blk.members[j.1]'j.2).vList)
    (hs_len : sSeq.length ≤ 3)
    (hbd_in :
      let r := blk.members[j.1]'j.2
      let A := r.toSubgraph (delGraph G X')
      let bd := r.toBranchDecomp
      E(A).ncard ≤ 1 ∨
        (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
          GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω))
    (a_tildeV a_tildeE a_rE a_rPar a_rTau a_xInd : ℕ)
    (a_zA a_vIdx a_mult a_buf a_folioWords : ℕ)
    (r_n r_nA r_mA r_kA r_rELen r_rT r_folioLen r_folioCode r_base : ℕ)
    (R_off A_off : ℕ)
    (ha_tildeV : a_tildeV < a_zA) (ha_tildeE : a_tildeE < a_zA)
    (ha_rE : a_rE < a_zA) (ha_rPar : a_rPar < a_zA)
    (ha_rTau : a_rTau < a_zA) (ha_xInd : a_xInd < a_zA)
    (ha_zA : a_zA < a_vIdx) (ha_vIdx : a_vIdx < a_mult)
    (ha_mult : a_mult < a_buf) (ha_buf : a_buf < a_folioWords)
    (ha_folio : a_folioWords < A_off)
    (hr_n : r_n < r_folioLen) (hr_nA : r_nA < r_folioLen)
    (hr_mA : r_mA < r_folioLen) (hr_kA : r_kA < r_folioLen)
    (hr_rELen : r_rELen < r_folioLen) (hr_rT : r_rT < r_folioLen)
    (hr_flen : r_folioLen < r_folioCode) (hr_fcode : r_folioCode < r_base)
    (hr_off : r_base + 10 ≤ R_off)
    (hw6 : 6 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hcap_enc_w :
      let vList := memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq
      2 + 6 * (vList.length * vList.length) < 2 ^ w)
    (hmA_w :
      let eList_A := memberTildeAEList G blk xSeq j
      3 * eList_A.length + 1 < 2 ^ w)
    (hrT_w : (blk.members[j.1]'j.2).t_len < 2 ^ w)
    (hrE_w : ∀ x ∈ encEdgeTriples (blk.members[j.1]'j.2).eList, x < 2 ^ w)
    (hrPar_w : ∀ x ∈ (blk.members[j.1]'j.2).parList, x < 2 ^ w)
    (hrTau_w : ∀ x ∈ (blk.members[j.1]'j.2).tauList, x < 2 ^ w)
    (hw41 :
      let vList := memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq
      let eList_A := memberTildeAEList G blk xSeq j
      wordSize c41 (vList.length + eList_A.length + 1) ≤ w)
    (h41_len_w :
      let vList := memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq
      let eList_A := memberTildeAEList G blk xSeq j
      C41 * (vList.length + eList_A.length + 1) < 2 ^ w)
    (hw_code : maxFolioRepCode q δ < 2 ^ w)
    (hw_len : maxFolioEncLen101 q δ < 2 ^ w)
    (hw_word : maxFolioEncWord q δ + 1 < 2 ^ w)
    (hw_q : q + 4 < 2 ^ w)
    {s : State}
    (hvList : s.arrs a_tildeV = memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq)
    (heListA : s.arrs a_tildeE = encEdgeTriples (memberTildeAEList G blk xSeq j))
    (hrE : s.arrs a_rE = encEdgeTriples (blk.members[j.1]'j.2).eList)
    (hrPar : s.arrs a_rPar = (blk.members[j.1]'j.2).parList)
    (hrTau : s.arrs a_rTau = (blk.members[j.1]'j.2).tauList)
    (hxInd : s.arrs a_xInd = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ xSeq)))
    (hrn : s.regs r_n = n)
    (hrnA : s.regs r_nA = (memberTildeAVList xSeq (blk.members[j.1]'j.2) sSeq).length)
    (hrmA : s.regs r_mA = (memberTildeAEList G blk xSeq j).length)
    (hrkA : s.regs r_kA = (sSeq ++ xSeq).length)
    (hrrELen : s.regs r_rELen = (blk.members[j.1]'j.2).eList.length)
    (hrrT : s.regs r_rT = (blk.members[j.1]'j.2).t_len) :
    let r := blk.members[j.1]'j.2
    let vList := memberTildeAVList xSeq r sSeq
    let eList_A := memberTildeAEList G blk xSeq j
    let G_A := tildeAMultiDigraph vList eList_A
    let Z_A := prefixRootFinset vList.length (sSeq ++ xSeq).length
    ∃ (s' : State) (time : ℕ) (folioWords : List ℕ) (folioCode : ℕ)
      (out : ParsedFolioAndModels G_A Z_A δ),
      Exec w
        (runInteriorStep3Prog p q δ prog41
          a_tildeV a_tildeE a_rE a_rPar a_rTau a_xInd
          a_zA a_vIdx a_mult a_buf a_folioWords
          r_n r_nA r_mA r_kA r_rELen r_rT r_folioLen r_folioCode r_base
          R_off A_off)
        s s' time ∧
      time ≤
        n + 600 * (vList.length + eList_A.length + 1) ^ 2 +
        17 * C41 * (vList.length + eList_A.length + 1) +
        ((maxFolioEncLen101 q δ + 1) * (4 * maxFolioEncWord q δ + 10) + 4 * (q + 4)) ∧
      s'.arrs a_folioWords = folioWords ∧
      s'.regs r_folioLen = folioWords.length ∧
      s'.regs r_folioCode = folioCode ∧
      folioWords.length ≤ C41 * (vList.length + eList_A.length + 1) ∧
      (∀ x ∈ folioWords, x < 2 ^ w) ∧
      folioCode < 2 ^ w ∧
      parseFolioAndModelsFull G_A Z_A δ folioWords = some out ∧
      IsDeltaFolioRep δ G_A Z_A out.folio ∧
      folioCode = folioRepCode q out.folio ∧
      (∀ a < A_off,
        a ≠ a_zA → a ≠ a_vIdx → a ≠ a_mult → a ≠ a_buf → a ≠ a_folioWords →
          s'.arrs a = s.arrs a) ∧
      (∀ reg < r_base, reg ≠ r_folioLen → reg ≠ r_folioCode → s'.regs reg = s.regs reg) := by
  intro r vList eList_A G_A Z_A
  generalize h_mcode : maxFolioRepCode q δ = M_code at hw_code
  generalize h_mlen : maxFolioEncLen101 q δ = M_len at hw_len ⊢
  generalize h_mword : maxFolioEncWord q δ = M_word at hw_word ⊢
  let b := alg105ArrBase p
  let n_A := vList.length
  let m_A := eList_A.length
  let k_A := (sSeq ++ xSeq).length
  let X_A := tildeAXFinset vList xSeq
  change 2 + 6 * (n_A * n_A) < 2 ^ w at hcap_enc_w
  change 3 * m_A + 1 < 2 ^ w at hmA_w
  change r.t_len < 2 ^ w at hrT_w
  change wordSize c41 (n_A + m_A + 1) ≤ w at hw41
  change C41 * (n_A + m_A + 1) < 2 ^ w at h41_len_w
  have ha_zA_off : a_zA < A_off := by omega
  have hr_nA_off : r_nA < R_off := by omega
  have hr_mA_off : r_mA < R_off := by omega
  have hr_kA_off : r_kA < R_off := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hr_mem : r ∈ blk.members := List.getElem_mem j.2
  rcases blk.member_valid_iff hr_mem with
    ⟨_, hr_v_nd, hr_v_sub, _, hr_e_nd, hr_e_valid, _, hr_t_le, hr_par_len, _, hr_tau_len, _⟩
  have hr_lt_n : ∀ v ∈ r.vList, v < n ∧ v ∉ xSeq := by
    intro v hv
    have hv_del := blk.K_vList_mem_delGraph (hr_v_sub v hv)
    rcases (mem_vertexSet_delGraph_iff G X' v).mp hv_del with ⟨h1, h2⟩
    refine ⟨h1, fun hx => h2 ?_⟩
    have hv_fin : v ∈ X'.image Fin.val := hx_set ▸ List.mem_toFinset.mpr hx
    rcases Finset.mem_image.mp hv_fin with ⟨u, hu, heq⟩
    have hu_eq : u = ⟨v, h1⟩ := Fin.ext heq
    rwa [← hu_eq]
  have hx_lt_n : ∀ v ∈ xSeq, v < n := by
    intro v hv
    have hv_fin : v ∈ X'.image Fin.val := hx_set ▸ List.mem_toFinset.mpr hv
    rcases Finset.mem_image.mp hv_fin with ⟨u, _, rfl⟩
    exact u.2
  have hv_nd : vList.Nodup :=
    nodup_memberTildeAVList xSeq r sSeq hx_nd hr_v_nd hs_nd hs_sub
      (fun v hv => (hr_lt_n v hv).2)
  have hv_lt : ∀ v ∈ vList, v < n := by
    intro v hv
    rcases (mem_memberTildeAVList_iff xSeq r sSeq hs_sub v).mp hv with h1 | h2
    · exact (hr_lt_n v h1).1
    · exact hx_lt_n v h2
  have hk_le_nA : k_A ≤ n_A := le_length_memberTildeAVList xSeq r sSeq
  have hx_len_le_q : xSeq.length ≤ q := by
    rw [← List.toFinset_card_of_nodup hx_nd, hx_set,
      Finset.card_image_of_injective _ Fin.val_injective]
    exact hx_card
  have hk_le_q3 : k_A ≤ q + 3 := by
    dsimp [k_A]
    rw [List.length_append]
    omega
  have heA_nd : eList_A.Nodup := nodup_memberTildeAEList G blk hx_set j
  have heA_ends_full := memberTildeAEList_valid_ends G blk hWS hRD xSeq j sSeq hs_sub
  have heA_ends : ∀ e ∈ eList_A, e.1 ∈ vList ∧ e.2.1 ∈ vList :=
    fun e he => ⟨(heA_ends_full e he).2.1, (heA_ends_full e he).2.2⟩
  have hr_sub_v : ∀ v ∈ r.vList, v ∈ vList :=
    fun v hv => (mem_memberTildeAVList_iff xSeq r sSeq hs_sub v).mpr (Or.inl hv)
  have hr_e_ends : ∀ e ∈ r.eList, e.1 ∈ vList ∧ e.2.1 ∈ vList := by
    intro e he
    rcases hr_e_valid e he with ⟨_, h1, h2⟩
    exact ⟨hr_sub_v e.1 h1, hr_sub_v e.2.1 h2⟩
  have hr_e_le : r.eList.length ≤ m_A := by
    dsimp [m_A, eList_A, r, memberTildeAEList]
    rw [List.length_append]
    omega
  have hnA_sq_w : n_A * n_A < 2 ^ w := by omega
  have hnA_w : n_A < 2 ^ w := by
    have := Nat.le_mul_self n_A
    omega
  have hmA_len_w : m_A < 2 ^ w := by omega
  have hnum_GA : G_A.numEdges = m_A :=
    numEdges_tildeAMultiDigraph_of_nodup vList eList_A hv_nd heA_nd heA_ends
  -- 1. buildTildeABitSetsProg
  rcases buildTildeABitSetsProg_exec vList xSeq k_A hv_lt hk_le_nA
      a_tildeV a_xInd a_zA (A_off + (b + 1)) r_nA r_kA r_base
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw1 hn_w hnA_w hvList hxInd hrnA hrkA with
    ⟨s₁, t₁, hex₁, ht₁, hzA₁, hxIndA₁, harr₁, hreg₁⟩
  -- 2. buildVIdxProg
  rcases buildVIdxProg_exec vList hv_nd hv_lt a_tildeV a_vIdx r_n r_nA r_base
      (by omega) (by omega) (by omega) hw1 hn_w hnA_w (s := s₁)
      (by rw [harr₁ a_tildeV (by omega) (by omega), hvList])
      (by rw [hreg₁ r_n (by omega), hrn])
      (by rw [hreg₁ r_nA (by omega), hrnA]) with
    ⟨s₂, t₂, hex₂, ht₂, hvIdx_len₂, hvIdx_get₂, harr₂, hreg₂⟩
  -- 3. buildEdgeMultMatProg
  rcases buildEdgeMultMatProg_exec vList eList_A hv_nd hv_lt heA_ends
      a_vIdx a_tildeE a_mult r_nA r_mA r_base
      (by omega) (by omega) (by omega) (by omega)
      hw3 hn_w hnA_sq_w hmA_w hvIdx_len₂ hvIdx_get₂
      (by rw [harr₂ a_tildeE (by omega), harr₁ a_tildeE (by omega) (by omega), heListA])
      (by rw [hreg₂ r_nA (by omega), hreg₁ r_nA (by omega), hrnA])
      (by rw [hreg₂ r_mA (by omega), hreg₁ r_mA (by omega), hrmA]) with
    ⟨s₃, t₃, hex₃, ht₃, hmult_len₃, hmult_get₃, harr₃, hreg₃⟩
  -- 4. buildEncFromMultMatProg
  have hm_GA_w : ∀ x y : Fin n_A, G_A.edgeMult x y < 2 ^ w := by
    intro x y
    have hle := G_A.edgeMult_le_numEdges x y
    rw [hnum_GA] at hle
    omega
  rcases buildEncFromMultMatProg_exec G_A a_mult a_buf (A_off + b) r_nA r_folioLen r_base
      (by omega) (by omega) (by omega) (by omega) (by omega)
      hw6 hcap_enc_w hm_GA_w hmult_len₃ hmult_get₃
      (by rw [hreg₃ r_nA (by omega), hreg₂ r_nA (by omega), hreg₁ r_nA (by omega), hrnA]) with
    ⟨s₄, t₄, hex₄, ht₄, henc₄, hrnumP₄, harr₄, hreg₄⟩
  -- 5. buildFTau0Prog
  rcases buildFTau0Prog_exec vList hv_nd hv_lt r hr_e_nd hr_tau_len hr_e_ends hrE_w hrTau_w
      a_tildeV a_vIdx a_rE a_rTau a_mult a_buf (A_off + (b + 3)) r_nA r_rELen r_base
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      hw3 hn_w hnA_sq_w (by omega) (s := s₄)
      (by rw [harr₄ a_tildeV (by omega) (by omega), harr₃ a_tildeV (by omega),
            harr₂ a_tildeV (by omega), harr₁ a_tildeV (by omega) (by omega), hvList])
      (by rw [harr₄ a_vIdx (by omega) (by omega), harr₃ a_vIdx (by omega), hvIdx_len₂])
      (fun i => by
        rw [harr₄ a_vIdx (by omega) (by omega), harr₃ a_vIdx (by omega)]
        exact hvIdx_get₂ i)
      (by rw [harr₄ a_rE (by omega) (by omega), harr₃ a_rE (by omega),
            harr₂ a_rE (by omega), harr₁ a_rE (by omega) (by omega), hrE])
      (by rw [harr₄ a_rTau (by omega) (by omega), harr₃ a_rTau (by omega),
            harr₂ a_rTau (by omega), harr₁ a_rTau (by omega) (by omega), hrTau])
      (by rw [hreg₄ r_nA (by omega) (by omega), hreg₃ r_nA (by omega),
            hreg₂ r_nA (by omega), hreg₁ r_nA (by omega), hrnA])
      (by rw [hreg₄ r_rELen (by omega) (by omega), hreg₃ r_rELen (by omega),
            hreg₂ r_rELen (by omega), hreg₁ r_rELen (by omega), hrrELen]) with
    ⟨s₅, t₅, hex₅, ht₅, hftau₅, harr₅, hreg₅⟩
  -- 6. copyBufPrefixProg a_rPar (A_off + (b + 2)) r_rT r_base
  have hrPar_buf₅ : IsPrefixBuffer a_rPar r.parList 0 s₅ := by
    unfold IsPrefixBuffer
    rw [List.replicate_zero, List.append_nil,
      harr₅ a_rPar (by omega) (by omega) (by omega),
      harr₄ a_rPar (by omega) (by omega), harr₃ a_rPar (by omega),
      harr₂ a_rPar (by omega), harr₁ a_rPar (by omega) (by omega), hrPar]
  have hrrT₅ : s₅.regs r_rT = r.parList.length := by
    rw [hreg₅ r_rT (by omega), hreg₄ r_rT (by omega) (by omega),
      hreg₃ r_rT (by omega), hreg₂ r_rT (by omega), hreg₁ r_rT (by omega),
      hrrT, hr_par_len]
  rcases copyBufPrefixProg_exec a_rPar (A_off + (b + 2)) r_rT r_base
      (by omega) (by omega) hrPar_w hw1 (by rw [hr_par_len]; exact hrT_w)
      hrPar_buf₅ hrrT₅ with
    ⟨s₆, t₆, hex₆, ht₆, hpar₆, harr₆, hreg₆⟩
  rw [hr_par_len] at ht₆
  -- 7. Assign R_off + 26, R_off + 27, R_off + 28, R_off + 52
  have hrnA₆ : s₆.regs r_nA = n_A := by
    rw [hreg₆ r_nA (by omega), hreg₅ r_nA (by omega), hreg₄ r_nA (by omega) (by omega),
      hreg₃ r_nA (by omega), hreg₂ r_nA (by omega), hreg₁ r_nA (by omega), hrnA]
  have hrnumP₆ : s₆.regs r_folioLen = G_A.numActivePairs := by
    rw [hreg₆ r_folioLen (by omega), hreg₅ r_folioLen (by omega), hrnumP₄]
  have hrmA₆ : s₆.regs r_mA = m_A := by
    rw [hreg₆ r_mA (by omega), hreg₅ r_mA (by omega), hreg₄ r_mA (by omega) (by omega),
      hreg₃ r_mA (by omega), hreg₂ r_mA (by omega), hreg₁ r_mA (by omega), hrmA]
  have hrrT₆ : s₆.regs r_rT = r.t_len := by
    rw [hreg₆ r_rT (by omega), hrrT₅, hr_par_len]
  have hnumP_w : G_A.numActivePairs < 2 ^ w :=
    Nat.lt_of_le_of_lt G_A.numActivePairs_le_sq hnA_sq_w
  let s₇_1 := s₆.setReg (R_off + 26) n_A
  have hex₇_1 : Exec w (.assign (R_off + 26) (.reg r_nA)) s₆ s₇_1 2 :=
    .assign (by simp [Expr.eval, checkWord, hrnA₆, hnA_w])
  let s₇_2 := s₇_1.setReg (R_off + 27) G_A.numActivePairs
  have hex₇_2 : Exec w (.assign (R_off + 27) (.reg r_folioLen)) s₇_1 s₇_2 2 :=
    .assign (by simp [s₇_1, State.setReg, show r_folioLen ≠ R_off + 26 by omega,
      Expr.eval, checkWord, hrnumP₆, hnumP_w])
  let s₇_3 := s₇_2.setReg (R_off + 28) m_A
  have hex₇_3 : Exec w (.assign (R_off + 28) (.reg r_mA)) s₇_2 s₇_3 2 :=
    .assign (by simp [s₇_2, s₇_1, State.setReg, show r_mA ≠ R_off + 27 by omega,
      show r_mA ≠ R_off + 26 by omega, Expr.eval, checkWord, hrmA₆, hmA_len_w])
  let s₇ := s₇_3.setReg (R_off + 52) r.t_len
  have hex₇_4 : Exec w (.assign (R_off + 52) (.reg r_rT)) s₇_3 s₇ 2 :=
    .assign (by simp [s₇_3, s₇_2, s₇_1, State.setReg, show r_rT ≠ R_off + 28 by omega,
      show r_rT ≠ R_off + 27 by omega, show r_rT ≠ R_off + 26 by omega,
      Expr.eval, checkWord, hrrT₆, hrT_w])
  -- 8. Run (convertBDProg b).shiftMem R_off A_off
  have hXA_card : X_A.card ≤ q := by
    calc X_A.card ≤ xSeq.toFinset.card := card_tildeAXFinset_le vList xSeq hv_nd
      _ = X'.card := by rw [hx_set, Finset.card_image_of_injective _ Fin.val_injective]
      _ ≤ q := hx_card
  have hdel_eq : G_A.deleteVertices X_A = tildeAMultiDigraph vList r.eList :=
    tildeAMultiDigraph_deleteVertices_eq G blk hx_set j vList
  have hbd₀ :
      IsWrittenDigraphBD ω (G_A.deleteVertices X_A).toComputeDigraph
        r.t_len (fun z => r.parList.getD z 0) (memberFTau0 vList r) := by
    rw [hdel_eq]
    exact isWrittenDigraphBD_of_member blk hr_mem vList hv_nd hr_sub_v hbd_in
  have henc_GA_w : 2 + 3 * G_A.numActivePairs < 2 ^ w := by
    have : G_A.numActivePairs ≤ n_A * n_A := G_A.numActivePairs_le_sq
    omega
  have hm_GA_2w : 2 * G_A.numEdges + 1 < 2 ^ w := by
    rw [hnum_GA]; omega
  have hb_s₇ : (s₇.shiftDown R_off A_off).arrs b = G_A.enc := by
    simp only [State.arrs_shiftDown, s₇, s₇_3, s₇_2, s₇_1, State.setReg_arrs]
    rw [harr₆ (A_off + b) (by dsimp [b]; omega),
      harr₅ (A_off + b) (by omega) (by omega) (by dsimp [b]; omega), henc₄]
  have hb1_s₇ : (s₇.shiftDown R_off A_off).arrs (b + 1) = bitSetList X_A := by
    simp only [State.arrs_shiftDown, s₇, s₇_3, s₇_2, s₇_1, State.setReg_arrs]
    rw [harr₆ (A_off + (b + 1)) (by dsimp [b]; omega),
      harr₅ (A_off + (b + 1)) (by omega) (by omega) (by dsimp [b]; omega),
      harr₄ (A_off + (b + 1)) (by omega) (by dsimp [b]; omega),
      harr₃ (A_off + (b + 1)) (by omega),
      harr₂ (A_off + (b + 1)) (by omega), hxIndA₁]
  have hb2_s₇ :
      (s₇.shiftDown R_off A_off).arrs (b + 2) =
        List.ofFn (fun z : Fin r.t_len => r.parList.getD z.1 0) := by
    simp only [State.arrs_shiftDown, s₇, s₇_3, s₇_2, s₇_1, State.setReg_arrs, hpar₆]
    exact eq_ofFn_of_getD_eq hr_par_len (fun _ _ => rfl)
  have hb3_s₇ :
      (s₇.shiftDown R_off A_off).arrs (b + 3) =
        List.ofFn (fun e : Fin (G_A.deleteVertices X_A).toComputeDigraph.numEdges =>
          memberFTau0 vList r e.1) := by
    simp only [State.arrs_shiftDown, s₇, s₇_3, s₇_2, s₇_1, State.setReg_arrs]
    rw [harr₆ (A_off + (b + 3)) (by dsimp [b]; omega), hftau₅, hdel_eq]
  rcases convertBDProg_exec G_A X_A b (fun z => r.parList.getD z 0) (memberFTau0 vList r)
      hXA_card hw3 hnA_sq_w henc_GA_w hm_GA_2w hbd₀
      (s := s₇.shiftDown R_off A_off)
      hb_s₇ hb1_s₇
      (by simp [s₇, s₇_3, s₇_2, s₇_1, State.setReg, n_A])
      (by simp [s₇, s₇_3, s₇_2, s₇_1, State.setReg])
      (by simp [s₇, s₇_3, s₇_2, s₇_1, State.setReg, hnum_GA, m_A])
      (by simp [s₇, s₇_3, s₇_2, s₇_1, State.setReg])
      hb2_s₇ hb3_s₇ with
    ⟨s₀_8, t₈, t_bd, par_bd, f_tau_bd, hex₈_0, ht₈, hr52_8, hb2_8, hb3_8, hb5_8, hb6_8,
      hbd₈, harr₈_0, _hreg₈_0⟩
  let s₈ := s₇.shiftUp R_off A_off s₀_8
  have hex₈ : Exec w ((convertBDProg b).shiftMem R_off A_off) s₇ s₈ t₈ :=
    hex₈_0.shiftMem
  -- 9. Save R_off + 52 into r_folioLen, copy a_zA to A_off + (b + 1), restore R_off + 26, 28, 52
  have hm_eq_GA : G_A.toComputeDigraph.numEdges = G_A.numEdges := G_A.length_directedEdgesList
  have ht_bd_w : t_bd < 2 ^ w := by
    have hle := hbd₈.2.1
    rw [hm_eq_GA] at hle
    omega
  let s₈_1 := s₈.setReg r_folioLen t_bd
  have hex₈_1 : Exec w (.assign r_folioLen (.reg (R_off + 52))) s₈ s₈_1 2 :=
    .assign (by simp [s₈, State.regs_shiftUp_add, Expr.eval, checkWord, hr52_8, ht_bd_w])
  have hzA_s₈ : s₈_1.arrs a_zA = bitSetList Z_A := by
    simp only [s₈_1, State.setReg_arrs, s₈]
    rw [State.arrs_shiftUp_lt R_off A_off s₇ s₀_8 ha_zA_off]
    simp only [s₇, s₇_3, s₇_2, s₇_1, State.setReg_arrs]
    rw [harr₆ a_zA (by omega), harr₅ a_zA (by omega) (by omega) (by omega),
      harr₄ a_zA (by omega) (by omega), harr₃ a_zA (by omega),
      harr₂ a_zA (by omega), hzA₁]
  have hzA_buf₈ : IsPrefixBuffer a_zA (bitSetList Z_A) 0 s₈_1 := by
    unfold IsPrefixBuffer
    rw [List.replicate_zero, List.append_nil, hzA_s₈]
  have hrnA_s₈ : s₈_1.regs r_nA = (bitSetList Z_A).length := by
    simp only [s₈_1, State.setReg, show r_nA ≠ r_folioLen by omega, Function.update_apply, ↓reduceIte, s₈]
    rw [State.regs_shiftUp_lt R_off A_off s₇ s₀_8 hr_nA_off, length_bitSetList]
    simp [s₇, s₇_3, s₇_2, s₇_1, State.setReg,
      show r_nA ≠ R_off + 52 by omega, show r_nA ≠ R_off + 28 by omega,
      show r_nA ≠ R_off + 27 by omega, show r_nA ≠ R_off + 26 by omega, hrnA₆, n_A]
  rcases copyBufPrefixProg_exec a_zA (A_off + (b + 1)) r_nA r_base
      (by omega) (by omega) (bitSetList_words_lt Z_A hw1) hw1
      (by rw [length_bitSetList]; exact hnA_w) hzA_buf₈ hrnA_s₈ with
    ⟨s₉_0, t₉, hex₉_0, ht₉, hb1_9, harr₉_0, hreg₉_0⟩
  rw [length_bitSetList] at ht₉
  have hrnA_9 : s₉_0.regs r_nA = n_A := by
    rw [hreg₉_0 r_nA (by omega), hrnA_s₈, length_bitSetList]
  have hrmA_9 : s₉_0.regs r_mA = m_A := by
    rw [hreg₉_0 r_mA (by omega)]
    simp only [s₈_1, State.setReg, show r_mA ≠ r_folioLen by omega, Function.update_apply, ↓reduceIte, s₈]
    rw [State.regs_shiftUp_lt R_off A_off s₇ s₀_8 hr_mA_off]
    simp [s₇, s₇_3, s₇_2, s₇_1, State.setReg,
      show r_mA ≠ R_off + 52 by omega, show r_mA ≠ R_off + 28 by omega,
      show r_mA ≠ R_off + 27 by omega, show r_mA ≠ R_off + 26 by omega, hrmA₆]
  have hrt_9 : s₉_0.regs r_folioLen = t_bd := by
    rw [hreg₉_0 r_folioLen (by omega)]
    simp [s₈_1]
  let s₉_1 := s₉_0.setReg (R_off + 26) n_A
  have hex₉_1 : Exec w (.assign (R_off + 26) (.reg r_nA)) s₉_0 s₉_1 2 :=
    .assign (by simp [Expr.eval, checkWord, hrnA_9, hnA_w])
  let s₉_2 := s₉_1.setReg (R_off + 28) m_A
  have hex₉_2 : Exec w (.assign (R_off + 28) (.reg r_mA)) s₉_1 s₉_2 2 :=
    .assign (by simp [s₉_1, State.setReg, show r_mA ≠ R_off + 26 by omega,
      Expr.eval, checkWord, hrmA_9, hmA_len_w])
  let s₉ := s₉_2.setReg (R_off + 52) t_bd
  have hex₉_3 : Exec w (.assign (R_off + 52) (.reg r_folioLen)) s₉_2 s₉ 2 :=
    .assign (by simp [s₉_2, s₉_1, State.setReg, show r_folioLen ≠ R_off + 28 by omega,
      show r_folioLen ≠ R_off + 26 by omega, Expr.eval, checkWord, hrt_9, ht_bd_w])
  -- 10. Run prog41.shiftMem R_off A_off
  have hZA_card : Z_A.card ≤ q + 3 := by
    rw [card_prefixRootFinset hk_le_nA]
    exact hk_le_q3
  have hw41' : wordSize c41 (n_A + G_A.numEdges + 1) ≤ w := by
    rwa [hnum_GA]
  have hb_9 : (s₉.shiftDown R_off A_off).arrs b = G_A.enc := by
    simp only [State.arrs_shiftDown, s₉, s₉_2, s₉_1, State.setReg_arrs]
    rw [harr₉_0 (A_off + b) (by dsimp [b]; omega)]
    simp only [s₈_1, State.setReg_arrs, s₈, State.arrs_shiftUp_add]
    exact (harr₈_0 b (by dsimp [b, Arr]; omega)).trans hb_s₇
  have hb1_9' : (s₉.shiftDown R_off A_off).arrs (b + 1) = bitSetList Z_A := by
    simp only [State.arrs_shiftDown, s₉, s₉_2, s₉_1, State.setReg_arrs, hb1_9]
  have hb2_9 : (s₉.shiftDown R_off A_off).arrs (b + 2) = List.ofFn (fun z : Fin t_bd => par_bd z.1) := by
    simp only [State.arrs_shiftDown, s₉, s₉_2, s₉_1, State.setReg_arrs]
    rw [harr₉_0 (A_off + (b + 2)) (by dsimp [b]; omega)]
    simp [s₈_1, s₈, hb2_8]
  have hb3_9 :
      (s₉.shiftDown R_off A_off).arrs (b + 3) =
        List.ofFn (fun e : Fin G_A.toComputeDigraph.numEdges => f_tau_bd e.1) := by
    simp only [State.arrs_shiftDown, s₉, s₉_2, s₉_1, State.setReg_arrs]
    rw [harr₉_0 (A_off + (b + 3)) (by dsimp [b]; omega)]
    simp [s₈_1, s₈, hb3_8]
  have hb5_9 :
      (s₉.shiftDown R_off A_off).arrs (b + 5) =
        List.ofFn (fun e : Fin G_A.toComputeDigraph.numEdges => (G_A.toComputeDigraph.tail e).1) := by
    simp only [State.arrs_shiftDown, s₉, s₉_2, s₉_1, State.setReg_arrs]
    rw [harr₉_0 (A_off + (b + 5)) (by dsimp [b]; omega)]
    simp [s₈_1, s₈, hb5_8]
  have hb6_9 :
      (s₉.shiftDown R_off A_off).arrs (b + 6) =
        List.ofFn (fun e : Fin G_A.toComputeDigraph.numEdges => (G_A.toComputeDigraph.head e).1) := by
    simp only [State.arrs_shiftDown, s₉, s₉_2, s₉_1, State.setReg_arrs]
    rw [harr₉_0 (A_off + (b + 6)) (by dsimp [b]; omega)]
    simp [s₈_1, s₈, hb6_8]
  rcases h41 G_A Z_A t_bd par_bd f_tau_bd (s₉.shiftDown R_off A_off)
      hw41' hZA_card hbd₈ hb_9 hb1_9'
      (by simp [s₉, s₉_2, s₉_1, State.setReg, n_A])
      (by simp [s₉, s₉_2, s₉_1, State.setReg, hnum_GA, m_A])
      (by simp [s₉, s₉_2, s₉_1, State.setReg])
      (by rw [hb2_9, List.length_ofFn])
      (fun z hz => by rw [hb2_9, List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [hz])
      (by rw [hb3_9, List.length_ofFn, hm_eq_GA])
      (fun e he => by
        rw [hb3_9, List.getD_eq_getElem _ _ (by rw [List.length_ofFn, hm_eq_GA]; exact he),
          List.getElem_ofFn])
      hb5_9 hb6_9 with
    ⟨s₀_10, t₁₀, out, hex₁₀_0, ht₁₀, hlen_out, hwords_out, hparse_out, hrep_out⟩
  let s₁₀ := s₉.shiftUp R_off A_off s₀_10
  have hex₁₀ : Exec w (prog41.shiftMem R_off A_off) s₉ s₁₀ t₁₀ :=
    hex₁₀_0.shiftMem
  -- 11. Copy A_off + outArr to a_folioWords
  let folioWords := s₀_10.arrs outArr
  have hout_s₁₀ : s₁₀.arrs (A_off + outArr) = folioWords := by
    simp [s₁₀, folioWords]
  have hlen_fw_le : folioWords.length ≤ C41 * (n_A + m_A + 1) := by
    rw [← hnum_GA]; exact hlen_out
  have hlen_fw_w : folioWords.length < 2 ^ w := by omega
  let s₁₀_1 := s₁₀.setReg r_folioLen folioWords.length
  have hex₁₀_1 : Exec w (.assign r_folioLen (.len (A_off + outArr))) s₁₀ s₁₀_1 2 :=
    .assign (by simp [Expr.eval, checkWord, hout_s₁₀, hlen_fw_w])
  have hfw_buf : IsPrefixBuffer (A_off + outArr) folioWords 0 s₁₀_1 := by
    unfold IsPrefixBuffer
    rw [List.replicate_zero, List.append_nil]
    exact hout_s₁₀
  rcases copyBufPrefixProg_exec (pfx := folioWords) (A_off + outArr) a_folioWords r_folioLen r_base
      (by omega) (by omega) hwords_out hw1 hlen_fw_w hfw_buf (by simp [s₁₀_1, folioWords]) with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hfw₁₁, harr₁₁, hreg₁₁⟩
  -- 12. Run computeFolioRepCodeProg
  rcases parseFolioSetRep_of_parseFolioAndModelsFull hparse_out with ⟨rest_fw, hfw_enc, _⟩
  have hZA_eq_kA : Z_A.card = k_A := card_prefixRootFinset hk_le_nA
  have hrkA₁₁ : s₁₁.regs r_kA = Z_A.card := by
    rw [hZA_eq_kA, hreg₁₁ r_kA (by omega)]
    simp only [s₁₀_1, State.setReg, show r_kA ≠ r_folioLen by omega, Function.update_apply, ↓reduceIte, s₁₀]
    rw [State.regs_shiftUp_lt R_off A_off s₉ s₀_10 hr_kA_off]
    simp only [s₉, s₉_2, s₉_1, State.setReg,
      show r_kA ≠ R_off + 52 by omega, show r_kA ≠ R_off + 28 by omega,
      show r_kA ≠ R_off + 26 by omega, Function.update_apply, ↓reduceIte]
    rw [hreg₉_0 r_kA (by omega)]
    simp only [s₈_1, State.setReg, show r_kA ≠ r_folioLen by omega, Function.update_apply, ↓reduceIte, s₈]
    rw [State.regs_shiftUp_lt R_off A_off s₇ s₀_8 hr_kA_off]
    simp only [s₇, s₇_3, s₇_2, s₇_1, State.setReg,
      show r_kA ≠ R_off + 52 by omega, show r_kA ≠ R_off + 28 by omega,
      show r_kA ≠ R_off + 27 by omega, show r_kA ≠ R_off + 26 by omega,
      Function.update_apply, ↓reduceIte]
    rw [hreg₆ r_kA (by omega), hreg₅ r_kA (by omega), hreg₄ r_kA (by omega) (by omega),
      hreg₃ r_kA (by omega), hreg₂ r_kA (by omega), hreg₁ r_kA (by omega), hrkA]
  rcases computeFolioRepCodeProg_exec a_folioWords r_kA r_folioCode r_base
      hZA_card out.folio rest_fw (h_mcode ▸ hw_code) (h_mlen ▸ hw_len) (h_mword ▸ hw_word) hw_q s₁₁ hrkA₁₁
      (by rw [hfw₁₁]; exact hfw_enc) with
    ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hcode₁₂, hreg₁₂, harr₁₂⟩
  rw [h_mlen, h_mword] at ht₁₂
  have hcode_w : folioRepCode q out.folio < 2 ^ w :=
    Nat.lt_of_le_of_lt (h_mcode ▸ folioRepCode_le_maxFolioRepCode hZA_card out.folio) hw_code
  clear h_mcode h_mlen h_mword
  rw [hnum_GA] at ht₈ ht₁₀
  have htime := step3_time_bound hr_e_le hr_t_le ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₈ ht₉ ht₁₀
    (le_trans ht₁₁ (Nat.add_le_add_right (Nat.mul_le_mul_left 16 hlen_fw_le) 9)) ht₁₂
  refine ⟨s₁₂, _, folioWords, folioRepCode q out.folio, out,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇_1 (.seq hex₇_2 (.seq hex₇_3 (.seq hex₇_4
        (.seq hex₈ (.seq hex₈_1 (.seq hex₉_0 (.seq hex₉_1 (.seq hex₉_2 (.seq hex₉_3
          (.seq hex₁₀ (.seq hex₁₀_1 (.seq hex₁₁ hex₁₂)))))))))))))))))),
    htime,
    by rw [harr₁₂, hfw₁₁],
    by rw [hreg₁₂ r_folioLen (ne_of_lt hr_flen) (ne_of_lt (lt_trans hr_flen hr_fcode)),
         hreg₁₁ r_folioLen (by omega)]; simp [s₁₀_1],
    hcode₁₂, hlen_fw_le, hwords_out, hcode_w, hparse_out, hrep_out, rfl,
    fun a ha_lt h1 h2 h3 h4 h5 => ?_,
    fun reg hlt hne_len hne_code => ?_⟩
  · rw [harr₁₂, harr₁₁ a h5]
    simp only [s₁₀_1, State.setReg_arrs, s₁₀]
    rw [State.arrs_shiftUp_lt R_off A_off s₉ s₀_10 ha_lt]
    simp only [s₉, s₉_2, s₉_1, State.setReg_arrs]
    rw [harr₉_0 a (by omega)]
    simp only [s₈_1, State.setReg_arrs, s₈]
    rw [State.arrs_shiftUp_lt R_off A_off s₇ s₀_8 ha_lt]
    simp only [s₇, s₇_3, s₇_2, s₇_1, State.setReg_arrs]
    rw [harr₆ a (by omega), harr₅ a h3 h4 (by omega), harr₄ a h4 (by omega),
      harr₃ a h3, harr₂ a h2, harr₁ a h1 (by omega)]
  · have hreg_off : reg < R_off := by omega
    rw [hreg₁₂ reg hne_code (ne_of_lt hlt), hreg₁₁ reg hlt]
    simp only [s₁₀_1, State.setReg, hne_len, Function.update_apply, ↓reduceIte, s₁₀]
    rw [State.regs_shiftUp_lt R_off A_off s₉ s₀_10 hreg_off]
    simp only [s₉, s₉_2, s₉_1, State.setReg,
      show reg ≠ R_off + 52 by omega, show reg ≠ R_off + 28 by omega,
      show reg ≠ R_off + 26 by omega, Function.update_apply, ↓reduceIte]
    rw [hreg₉_0 reg hlt]
    simp only [s₈_1, State.setReg, hne_len, Function.update_apply, ↓reduceIte, s₈]
    rw [State.regs_shiftUp_lt R_off A_off s₇ s₀_8 hreg_off]
    simp only [s₇, s₇_3, s₇_2, s₇_1, State.setReg,
      show reg ≠ R_off + 52 by omega, show reg ≠ R_off + 28 by omega,
      show reg ≠ R_off + 27 by omega, show reg ≠ R_off + 26 by omega,
      Function.update_apply, ↓reduceIte]
    rw [hreg₆ reg hlt, hreg₅ reg hlt, hreg₄ reg hlt hne_len,
      hreg₃ reg hlt, hreg₂ reg hlt, hreg₁ reg hlt]

/-! ### Section 2: Vision Member Record Serializer (`appendVisionMemberRecordProg`) -/

/-- Append `m.enc` for a `VisionMemberRecord` `m` stored across arrays
`(a_sSeq, a_P₁, a_P₂, a_P₃, a_tildeV, a_tildeE, a_folioWords, a_vOfPath)` and registers
`(r_isInt, r_sLen, r_P₁Len, r_P₂Len, r_P₃Len, r_nA, r_mA, r_folioLen, r_folioCode, r_vOf, r_vOfPathLen)`
to the output buffer `a_visBuf` at cursor `r_visPos`. -/
def appendVisionMemberRecordProg
    (a_sSeq a_P₁ a_P₂ a_P₃ a_tildeV a_tildeE a_folioWords a_vOfPath a_visBuf : Arr)
    (r_isInt r_sLen r_P₁Len r_P₂Len r_P₃Len r_nA r_mA
      r_folioLen r_folioCode r_vOf r_vOfPathLen r_visPos r_base : Reg) : Cmd :=
  .seq (appendWordProg a_visBuf r_visPos (.reg r_isInt))
    (.seq (appendLengthPrefixedProg a_sSeq a_visBuf r_sLen r_visPos r_base)
      (.seq (appendLengthPrefixedProg a_P₁ a_visBuf r_P₁Len r_visPos r_base)
        (.seq (appendLengthPrefixedProg a_P₂ a_visBuf r_P₂Len r_visPos r_base)
          (.seq (appendLengthPrefixedProg a_P₃ a_visBuf r_P₃Len r_visPos r_base)
            (.seq (appendLengthPrefixedProg a_tildeV a_visBuf r_nA r_visPos r_base)
              (.seq (appendWordProg a_visBuf r_visPos (.reg r_mA))
                (.seq (.assign r_base (.op .mul (.const 3) (.reg r_mA)))
                  (.seq (appendBufSliceProg a_tildeE a_visBuf r_base r_visPos (r_base + 1))
                    (.seq (appendLengthPrefixedProg a_folioWords a_visBuf r_folioLen r_visPos r_base)
                      (.seq (appendWordProg a_visBuf r_visPos (.reg r_folioCode))
                        (.seq (appendWordProg a_visBuf r_visPos (.reg r_vOf))
                          (appendLengthPrefixedProg a_vOfPath a_visBuf r_vOfPathLen r_visPos r_base))))))))))))

theorem VisionMemberRecord.length_enc (m : VisionMemberRecord) :
    m.enc.length =
      11 + m.sSeq.length + m.P₁.length + m.P₂.length + m.P₃.length +
      m.tildeA_vList.length + 3 * m.tildeA_eList.length +
      m.folioWords.length + m.vOfPath.length := by
  unfold VisionMemberRecord.enc
  simp only [List.length_append, List.length_cons, List.length_nil, length_encEdgeTriples]
  omega

theorem appendVisionMemberRecordProg_exec {w cap : ℕ} {pfx : List ℕ} (m : VisionMemberRecord)
    (a_sSeq a_P₁ a_P₂ a_P₃ a_tildeV a_tildeE a_folioWords a_vOfPath a_visBuf : ℕ)
    (r_isInt r_sLen r_P₁Len r_P₂Len r_P₃Len r_nA r_mA
      r_folioLen r_folioCode r_vOf r_vOfPathLen r_visPos r_base : ℕ)
    (ha_s : a_sSeq ≠ a_visBuf) (ha_1 : a_P₁ ≠ a_visBuf) (ha_2 : a_P₂ ≠ a_visBuf)
    (ha_3 : a_P₃ ≠ a_visBuf) (ha_v : a_tildeV ≠ a_visBuf) (ha_e : a_tildeE ≠ a_visBuf)
    (ha_fw : a_folioWords ≠ a_visBuf) (ha_vp : a_vOfPath ≠ a_visBuf)
    (_hr_int : r_isInt < r_visPos) (hr_s : r_sLen < r_visPos)
    (hr_1 : r_P₁Len < r_visPos) (hr_2 : r_P₂Len < r_visPos) (hr_3 : r_P₃Len < r_visPos)
    (hr_nA : r_nA < r_visPos) (hr_mA : r_mA < r_visPos)
    (hr_fl : r_folioLen < r_visPos) (hr_fc : r_folioCode < r_visPos)
    (hr_vOf : r_vOf < r_visPos) (hr_vpl : r_vOfPathLen < r_visPos)
    (hr_vp : r_visPos < r_base)
    (hw3 : 3 < 2 ^ w)
    (hm_w : ∀ x ∈ m.enc, x < 2 ^ w)
    (hlen_w : pfx.length + m.enc.length < 2 ^ w)
    {s : State}
    (hbuf : IsPrefixBuffer a_visBuf pfx (m.enc.length + cap) s)
    (hrpos : s.regs r_visPos = pfx.length)
    (hsSeq : s.arrs a_sSeq = m.sSeq)
    (hP₁ : s.arrs a_P₁ = m.P₁)
    (hP₂ : s.arrs a_P₂ = m.P₂)
    (hP₃ : s.arrs a_P₃ = m.P₃)
    (htildeV : s.arrs a_tildeV = m.tildeA_vList)
    (htildeE : s.arrs a_tildeE = encEdgeTriples m.tildeA_eList)
    (hfw : s.arrs a_folioWords = m.folioWords)
    (hvOfP : s.arrs a_vOfPath = m.vOfPath)
    (hrInt : s.regs r_isInt = m.isInterior)
    (hrsLen : s.regs r_sLen = m.sSeq.length)
    (hrP₁Len : s.regs r_P₁Len = m.P₁.length)
    (hrP₂Len : s.regs r_P₂Len = m.P₂.length)
    (hrP₃Len : s.regs r_P₃Len = m.P₃.length)
    (hrnA : s.regs r_nA = m.tildeA_vList.length)
    (hrmA : s.regs r_mA = m.tildeA_eList.length)
    (hrfLen : s.regs r_folioLen = m.folioWords.length)
    (hrfCode : s.regs r_folioCode = m.folioCode)
    (hrvOf : s.regs r_vOf = m.vOf)
    (hrvOfPLen : s.regs r_vOfPathLen = m.vOfPath.length) :
    ∃ s' t,
      Exec w
        (appendVisionMemberRecordProg
          a_sSeq a_P₁ a_P₂ a_P₃ a_tildeV a_tildeE a_folioWords a_vOfPath a_visBuf
          r_isInt r_sLen r_P₁Len r_P₂Len r_P₃Len r_nA r_mA
          r_folioLen r_folioCode r_vOf r_vOfPathLen r_visPos r_base)
        s s' t ∧
      t ≤ 18 * m.enc.length ∧
      IsPrefixBuffer a_visBuf (pfx ++ m.enc) cap s' ∧
      s'.regs r_visPos = (pfx ++ m.enc).length ∧
      (∀ a : ℕ, a ≠ a_visBuf → s'.arrs a = s.arrs a) ∧
      (∀ reg < r_base, reg ≠ r_visPos → s'.regs reg = s.regs reg) := by
  have hw1 : 1 < 2 ^ w := by omega
  have henc_len := m.length_enc
  have hint_w : m.isInterior < 2 ^ w := hm_w _ (by unfold VisionMemberRecord.enc; simp)
  have hs_w : ∀ x ∈ m.sSeq, x < 2 ^ w := fun x hx => hm_w x (by unfold VisionMemberRecord.enc; simp [hx])
  have h1_w : ∀ x ∈ m.P₁, x < 2 ^ w := fun x hx => hm_w x (by unfold VisionMemberRecord.enc; simp [hx])
  have h2_w : ∀ x ∈ m.P₂, x < 2 ^ w := fun x hx => hm_w x (by unfold VisionMemberRecord.enc; simp [hx])
  have h3_w : ∀ x ∈ m.P₃, x < 2 ^ w := fun x hx => hm_w x (by unfold VisionMemberRecord.enc; simp [hx])
  have hv_w : ∀ x ∈ m.tildeA_vList, x < 2 ^ w := fun x hx => hm_w x (by unfold VisionMemberRecord.enc; simp [hx])
  have he_w : ∀ x ∈ encEdgeTriples m.tildeA_eList, x < 2 ^ w := fun x hx => hm_w x (by unfold VisionMemberRecord.enc; simp [hx])
  have hfw_w : ∀ x ∈ m.folioWords, x < 2 ^ w := fun x hx => hm_w x (by unfold VisionMemberRecord.enc; simp [hx])
  have hfc_w : m.folioCode < 2 ^ w := hm_w _ (by unfold VisionMemberRecord.enc; simp)
  have hvOf_w : m.vOf < 2 ^ w := hm_w _ (by unfold VisionMemberRecord.enc; simp)
  have hvp_w : ∀ x ∈ m.vOfPath, x < 2 ^ w := fun x hx => hm_w x (by unfold VisionMemberRecord.enc; simp [hx])
  have hmA_w : m.tildeA_eList.length < 2 ^ w := by omega
  have h3mA_w : 3 * m.tildeA_eList.length < 2 ^ w := by omega
  -- 1. appendWordProg isInterior
  let rem₁ := 10 + m.sSeq.length + m.P₁.length + m.P₂.length + m.P₃.length +
    m.tildeA_vList.length + 3 * m.tildeA_eList.length + m.folioWords.length + m.vOfPath.length + cap
  have hbuf₀ : IsPrefixBuffer a_visBuf pfx (rem₁ + 1) s := by
    unfold IsPrefixBuffer at hbuf ⊢
    have hrep : m.enc.length + cap = rem₁ + 1 := by dsimp [rem₁]; omega
    rwa [← hrep]
  rcases appendWordProg_exec (val := m.isInterior) a_visBuf r_visPos (.reg r_isInt)
      hw1 (by omega) hbuf₀ hrpos (by simp [Expr.eval, checkWord, hrInt, hint_w]) with
    ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hrpos₁, harr₁, hreg₁⟩
  -- 2. appendLengthPrefixedProg sSeq
  let rem₂ := 9 + m.P₁.length + m.P₂.length + m.P₃.length +
    m.tildeA_vList.length + 3 * m.tildeA_eList.length + m.folioWords.length + m.vOfPath.length + cap
  have hbuf₁' : IsPrefixBuffer a_visBuf (pfx ++ [m.isInterior]) (1 + m.sSeq.length + rem₂) s₁ := by
    unfold IsPrefixBuffer at hbuf₁ ⊢
    have hrep : rem₁ = 1 + m.sSeq.length + rem₂ := by dsimp [rem₁, rem₂]; omega
    rwa [← hrep]
  rcases appendLengthPrefixedProg_exec (chunk := m.sSeq) a_sSeq a_visBuf r_sLen r_visPos r_base
      (by omega) (by omega) hr_vp (by omega) hs_w hw1 (by simp; omega)
      (by rw [harr₁ a_sSeq (by omega), hsSeq]) hbuf₁'
      (by rw [hreg₁ r_sLen (by omega), hrsLen]) hrpos₁ with
    ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hrpos₂, _, harr₂, hreg₂⟩
  -- 3. appendLengthPrefixedProg P₁
  let rem₃ := 8 + m.P₂.length + m.P₃.length +
    m.tildeA_vList.length + 3 * m.tildeA_eList.length + m.folioWords.length + m.vOfPath.length + cap
  have hbuf₂' : IsPrefixBuffer a_visBuf ((pfx ++ [m.isInterior]) ++ (m.sSeq.length :: m.sSeq))
      (1 + m.P₁.length + rem₃) s₂ := by
    unfold IsPrefixBuffer at hbuf₂ ⊢
    have hrep : rem₂ = 1 + m.P₁.length + rem₃ := by dsimp [rem₂, rem₃]; omega
    rwa [← hrep]
  rcases appendLengthPrefixedProg_exec (chunk := m.P₁) a_P₁ a_visBuf r_P₁Len r_visPos r_base
      (by omega) (by omega) hr_vp (by omega) h1_w hw1 (by simp; omega)
      (by rw [harr₂ a_P₁ (by omega), harr₁ a_P₁ (by omega), hP₁]) hbuf₂'
      (by rw [hreg₂ r_P₁Len (by omega) (by omega), hreg₁ r_P₁Len (by omega), hrP₁Len]) hrpos₂ with
    ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hrpos₃, _, harr₃, hreg₃⟩
  -- 4. appendLengthPrefixedProg P₂
  let rem₄ := 7 + m.P₃.length +
    m.tildeA_vList.length + 3 * m.tildeA_eList.length + m.folioWords.length + m.vOfPath.length + cap
  have hbuf₃' : IsPrefixBuffer a_visBuf
      (((pfx ++ [m.isInterior]) ++ (m.sSeq.length :: m.sSeq)) ++ (m.P₁.length :: m.P₁))
      (1 + m.P₂.length + rem₄) s₃ := by
    unfold IsPrefixBuffer at hbuf₃ ⊢
    have hrep : rem₃ = 1 + m.P₂.length + rem₄ := by dsimp [rem₃, rem₄]; omega
    rwa [← hrep]
  rcases appendLengthPrefixedProg_exec (chunk := m.P₂) a_P₂ a_visBuf r_P₂Len r_visPos r_base
      (by omega) (by omega) hr_vp (by omega) h2_w hw1 (by simp; omega)
      (by rw [harr₃ a_P₂ (by omega), harr₂ a_P₂ (by omega), harr₁ a_P₂ (by omega), hP₂]) hbuf₃'
      (by rw [hreg₃ r_P₂Len (by omega) (by omega), hreg₂ r_P₂Len (by omega) (by omega),
            hreg₁ r_P₂Len (by omega), hrP₂Len]) hrpos₃ with
    ⟨s₄, t₄, hex₄, ht₄, hbuf₄, hrpos₄, _, harr₄, hreg₄⟩
  -- 5. appendLengthPrefixedProg P₃
  let rem₅ := 6 + m.tildeA_vList.length + 3 * m.tildeA_eList.length +
    m.folioWords.length + m.vOfPath.length + cap
  have hbuf₄' : IsPrefixBuffer a_visBuf
      ((((pfx ++ [m.isInterior]) ++ (m.sSeq.length :: m.sSeq)) ++ (m.P₁.length :: m.P₁)) ++
        (m.P₂.length :: m.P₂))
      (1 + m.P₃.length + rem₅) s₄ := by
    unfold IsPrefixBuffer at hbuf₄ ⊢
    have hrep : rem₄ = 1 + m.P₃.length + rem₅ := by dsimp [rem₄, rem₅]; omega
    rwa [← hrep]
  rcases appendLengthPrefixedProg_exec (chunk := m.P₃) a_P₃ a_visBuf r_P₃Len r_visPos r_base
      (by omega) (by omega) hr_vp (by omega) h3_w hw1 (by simp; omega)
      (by rw [harr₄ a_P₃ (by omega), harr₃ a_P₃ (by omega), harr₂ a_P₃ (by omega),
            harr₁ a_P₃ (by omega), hP₃]) hbuf₄'
      (by rw [hreg₄ r_P₃Len (by omega) (by omega), hreg₃ r_P₃Len (by omega) (by omega),
            hreg₂ r_P₃Len (by omega) (by omega), hreg₁ r_P₃Len (by omega), hrP₃Len]) hrpos₄ with
    ⟨s₅, t₅, hex₅, ht₅, hbuf₅, hrpos₅, _, harr₅, hreg₅⟩
  -- 6. appendLengthPrefixedProg tildeA_vList
  let rem₆ := 5 + 3 * m.tildeA_eList.length + m.folioWords.length + m.vOfPath.length + cap
  have hbuf₅' : IsPrefixBuffer a_visBuf
      (((((pfx ++ [m.isInterior]) ++ (m.sSeq.length :: m.sSeq)) ++ (m.P₁.length :: m.P₁)) ++
        (m.P₂.length :: m.P₂)) ++ (m.P₃.length :: m.P₃))
      (1 + m.tildeA_vList.length + rem₆) s₅ := by
    unfold IsPrefixBuffer at hbuf₅ ⊢
    have hrep : rem₅ = 1 + m.tildeA_vList.length + rem₆ := by dsimp [rem₅, rem₆]; omega
    rwa [← hrep]
  rcases appendLengthPrefixedProg_exec (chunk := m.tildeA_vList) a_tildeV a_visBuf r_nA r_visPos r_base
      (by omega) (by omega) hr_vp (by omega) hv_w hw1 (by simp; omega)
      (by rw [harr₅ a_tildeV (by omega), harr₄ a_tildeV (by omega), harr₃ a_tildeV (by omega),
            harr₂ a_tildeV (by omega), harr₁ a_tildeV (by omega), htildeV]) hbuf₅'
      (by rw [hreg₅ r_nA (by omega) (by omega), hreg₄ r_nA (by omega) (by omega),
            hreg₃ r_nA (by omega) (by omega), hreg₂ r_nA (by omega) (by omega),
            hreg₁ r_nA (by omega), hrnA]) hrpos₅ with
    ⟨s₆, t₆, hex₆, ht₆, hbuf₆, hrpos₆, _, harr₆, hreg₆⟩
  -- 7. appendWordProg mA, assign (r_base + 2) := 3 * mA, appendBufSliceProg tildeE
  let rem₇ := 4 + 3 * m.tildeA_eList.length + m.folioWords.length + m.vOfPath.length + cap
  have hbuf₆' : IsPrefixBuffer a_visBuf
      ((((((pfx ++ [m.isInterior]) ++ (m.sSeq.length :: m.sSeq)) ++ (m.P₁.length :: m.P₁)) ++
        (m.P₂.length :: m.P₂)) ++ (m.P₃.length :: m.P₃)) ++
        (m.tildeA_vList.length :: m.tildeA_vList))
      (rem₇ + 1) s₆ := by
    unfold IsPrefixBuffer at hbuf₆ ⊢
    have hrep : rem₆ = rem₇ + 1 := by dsimp [rem₆, rem₇]; omega
    rwa [← hrep]
  have hrmA₆ : s₆.regs r_mA = m.tildeA_eList.length := by
    rw [hreg₆ r_mA (by omega) (by omega), hreg₅ r_mA (by omega) (by omega),
      hreg₄ r_mA (by omega) (by omega), hreg₃ r_mA (by omega) (by omega),
      hreg₂ r_mA (by omega) (by omega), hreg₁ r_mA (by omega), hrmA]
  rcases appendWordProg_exec (val := m.tildeA_eList.length) a_visBuf r_visPos (.reg r_mA)
      hw1 (by simp; omega) hbuf₆' hrpos₆ (by simp [Expr.eval, checkWord, hrmA₆, hmA_w]) with
    ⟨s₇_0, t₇_0, hex₇_0, ht₇_0, hbuf₇_0, hrpos₇_0, harr₇_0, hreg₇_0⟩
  have hrmA₇_0 : s₇_0.regs r_mA = m.tildeA_eList.length := by
    rw [hreg₇_0 r_mA (by omega), hrmA₆]
  let s₇_1 := s₇_0.setReg r_base (3 * m.tildeA_eList.length)
  have hex₇_1 : Exec w (.assign r_base (.op .mul (.const 3) (.reg r_mA))) s₇_0 s₇_1 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrmA₇_0, hw3, hmA_w, h3mA_w])
  let rem₈ := 4 + m.folioWords.length + m.vOfPath.length + cap
  have hbuf₇_1 : IsPrefixBuffer a_visBuf
      (((((((pfx ++ [m.isInterior]) ++ (m.sSeq.length :: m.sSeq)) ++ (m.P₁.length :: m.P₁)) ++
        (m.P₂.length :: m.P₂)) ++ (m.P₃.length :: m.P₃)) ++
        (m.tildeA_vList.length :: m.tildeA_vList)) ++ [m.tildeA_eList.length])
      ((encEdgeTriples m.tildeA_eList).length + rem₈) s₇_1 := by
    unfold IsPrefixBuffer at hbuf₇_0 ⊢
    simp only [s₇_1, State.setReg_arrs, length_encEdgeTriples]
    have hrep : rem₇ = 3 * m.tildeA_eList.length + rem₈ := by dsimp [rem₇, rem₈]; omega
    rwa [← hrep]
  rcases appendBufSliceProg_exec (chunk := encEdgeTriples m.tildeA_eList)
      a_tildeE a_visBuf r_base r_visPos (r_base + 1)
      (by omega) (by omega) (by omega) (by omega) he_w hw1
      (by simp [length_encEdgeTriples]; omega)
      (by simp only [s₇_1, State.setReg_arrs]
          rw [harr₇_0 a_tildeE (by omega), harr₆ a_tildeE (by omega), harr₅ a_tildeE (by omega),
            harr₄ a_tildeE (by omega), harr₃ a_tildeE (by omega), harr₂ a_tildeE (by omega),
            harr₁ a_tildeE (by omega), htildeE])
      hbuf₇_1
      (by simp [s₇_1, length_encEdgeTriples])
      (by simp [s₇_1, State.setReg, show r_visPos ≠ r_base by omega, hrpos₇_0]) with
    ⟨s₇, t₇_2, hex₇_2, ht₇_2, hbuf₇, hrpos₇, _, harr₇, hreg₇⟩
  rw [length_encEdgeTriples] at ht₇_2
  -- 8. appendLengthPrefixedProg folioWords
  let rem₉ := 3 + m.vOfPath.length + cap
  have hbuf₇' : IsPrefixBuffer a_visBuf
      ((((((((pfx ++ [m.isInterior]) ++ (m.sSeq.length :: m.sSeq)) ++ (m.P₁.length :: m.P₁)) ++
        (m.P₂.length :: m.P₂)) ++ (m.P₃.length :: m.P₃)) ++
        (m.tildeA_vList.length :: m.tildeA_vList)) ++ [m.tildeA_eList.length]) ++
        encEdgeTriples m.tildeA_eList)
      (1 + m.folioWords.length + rem₉) s₇ := by
    unfold IsPrefixBuffer at hbuf₇ ⊢
    have hrep : rem₈ = 1 + m.folioWords.length + rem₉ := by dsimp [rem₈, rem₉]; omega
    rwa [← hrep]
  rcases appendLengthPrefixedProg_exec (chunk := m.folioWords)
      a_folioWords a_visBuf r_folioLen r_visPos r_base
      (by omega) (by omega) hr_vp (by omega) hfw_w hw1 (by simp [length_encEdgeTriples]; omega)
      (by rw [harr₇ a_folioWords (by omega)]; simp only [s₇_1, State.setReg_arrs]
          rw [harr₇_0 a_folioWords (by omega), harr₆ a_folioWords (by omega),
            harr₅ a_folioWords (by omega), harr₄ a_folioWords (by omega),
            harr₃ a_folioWords (by omega), harr₂ a_folioWords (by omega),
            harr₁ a_folioWords (by omega), hfw])
      hbuf₇'
      (by rw [hreg₇ r_folioLen (by omega) (by omega)]
          simp only [s₇_1, State.setReg, show r_folioLen ≠ r_base by omega, Function.update_apply, ↓reduceIte]
          rw [hreg₇_0 r_folioLen (by omega), hreg₆ r_folioLen (by omega) (by omega),
            hreg₅ r_folioLen (by omega) (by omega), hreg₄ r_folioLen (by omega) (by omega),
            hreg₃ r_folioLen (by omega) (by omega), hreg₂ r_folioLen (by omega) (by omega),
            hreg₁ r_folioLen (by omega), hrfLen])
      hrpos₇ with
    ⟨s₈, t₈, hex₈, ht₈, hbuf₈, hrpos₈, _, harr₈, hreg₈⟩
  -- 9. appendWordProg folioCode, appendWordProg vOf, appendLengthPrefixedProg vOfPath
  let rem₁₀ := 2 + m.vOfPath.length + cap
  have hbuf₈' : IsPrefixBuffer a_visBuf
      (((((((((pfx ++ [m.isInterior]) ++ (m.sSeq.length :: m.sSeq)) ++ (m.P₁.length :: m.P₁)) ++
        (m.P₂.length :: m.P₂)) ++ (m.P₃.length :: m.P₃)) ++
        (m.tildeA_vList.length :: m.tildeA_vList)) ++ [m.tildeA_eList.length]) ++
        encEdgeTriples m.tildeA_eList) ++ (m.folioWords.length :: m.folioWords))
      (rem₁₀ + 1) s₈ := by
    unfold IsPrefixBuffer at hbuf₈ ⊢
    have hrep : rem₉ = rem₁₀ + 1 := by dsimp [rem₉, rem₁₀]; omega
    rwa [← hrep]
  have hrfCode₈ : s₈.regs r_folioCode = m.folioCode := by
    rw [hreg₈ r_folioCode (by omega) (by omega), hreg₇ r_folioCode (by omega) (by omega)]
    simp only [s₇_1, State.setReg, show r_folioCode ≠ r_base by omega, Function.update_apply, ↓reduceIte]
    rw [hreg₇_0 r_folioCode (by omega), hreg₆ r_folioCode (by omega) (by omega),
      hreg₅ r_folioCode (by omega) (by omega), hreg₄ r_folioCode (by omega) (by omega),
      hreg₃ r_folioCode (by omega) (by omega), hreg₂ r_folioCode (by omega) (by omega),
      hreg₁ r_folioCode (by omega), hrfCode]
  rcases appendWordProg_exec (val := m.folioCode) a_visBuf r_visPos (.reg r_folioCode)
      hw1 (by simp [length_encEdgeTriples]; omega) hbuf₈' hrpos₈
      (by simp [Expr.eval, checkWord, hrfCode₈, hfc_w]) with
    ⟨s₉, t₉, hex₉, ht₉, hbuf₉, hrpos₉, harr₉, hreg₉⟩
  let rem₁₁ := 1 + m.vOfPath.length + cap
  have hbuf₉' : IsPrefixBuffer a_visBuf
      ((((((((((pfx ++ [m.isInterior]) ++ (m.sSeq.length :: m.sSeq)) ++ (m.P₁.length :: m.P₁)) ++
        (m.P₂.length :: m.P₂)) ++ (m.P₃.length :: m.P₃)) ++
        (m.tildeA_vList.length :: m.tildeA_vList)) ++ [m.tildeA_eList.length]) ++
        encEdgeTriples m.tildeA_eList) ++ (m.folioWords.length :: m.folioWords)) ++ [m.folioCode])
      (rem₁₁ + 1) s₉ := by
    unfold IsPrefixBuffer at hbuf₉ ⊢
    have hrep : rem₁₀ = rem₁₁ + 1 := by dsimp [rem₁₀, rem₁₁]; omega
    rwa [← hrep]
  have hrvOf₉ : s₉.regs r_vOf = m.vOf := by
    rw [hreg₉ r_vOf (by omega), hreg₈ r_vOf (by omega) (by omega), hreg₇ r_vOf (by omega) (by omega)]
    simp only [s₇_1, State.setReg, show r_vOf ≠ r_base by omega, Function.update_apply, ↓reduceIte]
    rw [hreg₇_0 r_vOf (by omega), hreg₆ r_vOf (by omega) (by omega),
      hreg₅ r_vOf (by omega) (by omega), hreg₄ r_vOf (by omega) (by omega),
      hreg₃ r_vOf (by omega) (by omega), hreg₂ r_vOf (by omega) (by omega),
      hreg₁ r_vOf (by omega), hrvOf]
  rcases appendWordProg_exec (val := m.vOf) a_visBuf r_visPos (.reg r_vOf)
      hw1 (by simp [length_encEdgeTriples]; omega) hbuf₉' hrpos₉
      (by simp [Expr.eval, checkWord, hrvOf₉, hvOf_w]) with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hbuf₁₀, hrpos₁₀, harr₁₀, hreg₁₀⟩
  rcases appendLengthPrefixedProg_exec (chunk := m.vOfPath)
      a_vOfPath a_visBuf r_vOfPathLen r_visPos r_base
      (by omega) (by omega) hr_vp (by omega) hvp_w hw1 (by simp [length_encEdgeTriples]; omega)
      (by rw [harr₁₀ a_vOfPath (by omega), harr₉ a_vOfPath (by omega),
            harr₈ a_vOfPath (by omega), harr₇ a_vOfPath (by omega)]
          simp only [s₇_1, State.setReg_arrs]
          rw [harr₇_0 a_vOfPath (by omega), harr₆ a_vOfPath (by omega),
            harr₅ a_vOfPath (by omega), harr₄ a_vOfPath (by omega),
            harr₃ a_vOfPath (by omega), harr₂ a_vOfPath (by omega),
            harr₁ a_vOfPath (by omega), hvOfP])
      hbuf₁₀
      (by rw [hreg₁₀ r_vOfPathLen (by omega), hreg₉ r_vOfPathLen (by omega),
            hreg₈ r_vOfPathLen (by omega) (by omega), hreg₇ r_vOfPathLen (by omega) (by omega)]
          simp only [s₇_1, State.setReg, show r_vOfPathLen ≠ r_base by omega, Function.update_apply, ↓reduceIte]
          rw [hreg₇_0 r_vOfPathLen (by omega), hreg₆ r_vOfPathLen (by omega) (by omega),
            hreg₅ r_vOfPathLen (by omega) (by omega), hreg₄ r_vOfPathLen (by omega) (by omega),
            hreg₃ r_vOfPathLen (by omega) (by omega), hreg₂ r_vOfPathLen (by omega) (by omega),
            hreg₁ r_vOfPathLen (by omega), hrvOfPLen])
      hrpos₁₀ with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hbuf₁₁, hrpos₁₁, _, harr₁₁, hreg₁₁⟩
  have henc_eq :
      (((((((((((pfx ++ [m.isInterior]) ++ (m.sSeq.length :: m.sSeq)) ++ (m.P₁.length :: m.P₁)) ++
        (m.P₂.length :: m.P₂)) ++ (m.P₃.length :: m.P₃)) ++
        (m.tildeA_vList.length :: m.tildeA_vList)) ++ [m.tildeA_eList.length]) ++
        encEdgeTriples m.tildeA_eList) ++ (m.folioWords.length :: m.folioWords)) ++ [m.folioCode]) ++
        [m.vOf]) ++ (m.vOfPath.length :: m.vOfPath) =
      pfx ++ m.enc := by
    unfold VisionMemberRecord.enc
    simp [List.append_assoc]
  rw [henc_eq] at hbuf₁₁ hrpos₁₁
  refine ⟨s₁₁,
    t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇_0 + (4 + (t₇_2 + (t₈ + (t₉ + (t₁₀ + t₁₁))))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇_0 (.seq hex₇_1 (.seq hex₇_2 (.seq hex₈
        (.seq hex₉ (.seq hex₁₀ hex₁₁))))))))))),
    by dsimp [Expr.cost] at ht₁ ht₇_0 ht₉ ht₁₀; omega,
    hbuf₁₁, hrpos₁₁,
    fun a ha => by
      rw [harr₁₁ a ha, harr₁₀ a ha, harr₉ a ha, harr₈ a ha, harr₇ a ha]
      simp only [s₇_1, State.setReg_arrs]
      rw [harr₇_0 a ha, harr₆ a ha, harr₅ a ha, harr₄ a ha, harr₃ a ha, harr₂ a ha, harr₁ a ha],
    fun reg hlt hne => by
      rw [hreg₁₁ reg hlt hne, hreg₁₀ reg hne, hreg₉ reg hne,
        hreg₈ reg hlt hne, hreg₇ reg (by omega) hne]
      simp only [s₇_1, State.setReg, show reg ≠ r_base by omega, Function.update_apply, ↓reduceIte]
      rw [hreg₇_0 reg hne, hreg₆ reg hlt hne, hreg₅ reg hlt hne, hreg₄ reg hlt hne,
        hreg₃ reg hlt hne, hreg₂ reg hlt hne, hreg₁ reg hne]⟩

end GraphMinor.Compute

