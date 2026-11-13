module

public import GraphMinor.Compute.Join13Adapter101Defs

/-!
# Converting branch-set bit vectors to model lists

The loops read the raw (4.1) certificates one model at a time. Each branch set
is written as a sorted list of vertex and edge indices, with a length prefix.
The proofs follow the unread source and the unused destination capacity.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 4: Full-Entry and Full-Table Model Conversion Loops and `alg41Spec101_of_claim41` -/

/-- Convert `r_vrem` vertex branch-set bit-vector pairs `(bitSetList verts, bitSetList edges)`
from `a_src` (at `r_src`) into length-prefixed sorted index lists in `a_dst` (at `r_dst`). -/
def convertVertModelsLoop (a_src a_dst : Arr) (r_src r_dst r_n r_m r_vrem r_base : Reg) : Cmd :=
  .while (.reg r_vrem)
    (.seq (bitListToLenListProg a_src a_dst r_src r_dst r_n r_base)
    (.seq (bitListToLenListProg a_src a_dst r_src r_dst r_m r_base)
          (.assign r_vrem (.op .sub (.reg r_vrem) (.const 1)))))

theorem length_encLengthPrefixed_vert_le {n m v_H : ℕ}
    (vertVerts : Fin v_H → Finset (Fin n)) (vertEdges : Fin v_H → Finset (Fin m))
    (us : List (Fin v_H)) :
    (encLengthPrefixedLists (us.flatMap (fun u =>
      [finsetToList (vertVerts u), finsetToList (vertEdges u)]))).length ≤
      us.length * (n + m + 2) := by
  induction us with
  | nil => simp [encLengthPrefixedLists]
  | cons u us ih =>
    have hv_le : (finsetToList (vertVerts u)).length ≤ n := by
      rw [length_finsetToList]
      exact Finset.card_le_univ _ |>.trans (by simp)
    have he_le : (finsetToList (vertEdges u)).length ≤ m := by
      rw [length_finsetToList]
      exact Finset.card_le_univ _ |>.trans (by simp)
    have hcons :
        encLengthPrefixedLists ((u :: us).flatMap (fun x =>
          [finsetToList (vertVerts x), finsetToList (vertEdges x)])) =
        ((finsetToList (vertVerts u)).length :: finsetToList (vertVerts u)) ++
        ((finsetToList (vertEdges u)).length :: finsetToList (vertEdges u)) ++
        encLengthPrefixedLists (us.flatMap (fun x =>
          [finsetToList (vertVerts x), finsetToList (vertEdges x)])) := by
      simp [encLengthPrefixedLists, List.append_assoc]
    rw [hcons, List.length_append, List.length_append, List.length_cons, List.length_cons,
      List.length_cons, Nat.succ_mul]
    omega

theorem convertVertModelsLoop_exec {w n m v_H : ℕ} (a_src a_dst : Arr) (r_base : Reg)
    (hne_arr : a_src ≠ a_dst)
    (hw : 1 < 2 ^ w)
    (vertVerts : Fin v_H → Finset (Fin n)) (vertEdges : Fin v_H → Finset (Fin m))
    (us : List (Fin v_H))
    (pre_src post_src pre_dst : List ℕ) (rem_dst : ℕ)
    (hrem_le : us.length * (n + m + 2) ≤ rem_dst)
    (hsrc_w : (pre_src ++ us.flatMap (fun u =>
      bitSetList (vertVerts u) ++ bitSetList (vertEdges u)) ++ post_src).length < 2 ^ w)
    (hdst_w : pre_dst.length + rem_dst < 2 ^ w)
    {s : State}
    (ha_src : s.arrs a_src = pre_src ++ us.flatMap (fun u =>
      bitSetList (vertVerts u) ++ bitSetList (vertEdges u)) ++ post_src)
    (ha_dst : s.arrs a_dst = pre_dst ++ List.replicate rem_dst 0)
    (hr_src : s.regs (r_base + 1) = pre_src.length)
    (hr_dst : s.regs (r_base + 2) = pre_dst.length)
    (hr_n : s.regs (r_base + 3) = n)
    (hr_m : s.regs (r_base + 4) = m)
    (hr_vrem : s.regs (r_base + 7) = us.length) :
    let rawChunk := us.flatMap (fun u => bitSetList (vertVerts u) ++ bitSetList (vertEdges u))
    let outChunk := encLengthPrefixedLists (us.flatMap (fun u =>
      [finsetToList (vertVerts u), finsetToList (vertEdges u)]))
    ∃ s' t,
      Exec w (convertVertModelsLoop a_src a_dst (r_base + 1) (r_base + 2) (r_base + 3)
        (r_base + 4) (r_base + 7) (r_base + 9)) s s' t ∧
      t ≤ us.length * (28 * (n + m) + 50) + 1 ∧
      s'.arrs a_dst = (pre_dst ++ outChunk) ++ List.replicate (rem_dst - outChunk.length) 0 ∧
      s'.regs (r_base + 1) = (pre_src ++ rawChunk).length ∧
      s'.regs (r_base + 2) = (pre_dst ++ outChunk).length ∧
      s'.regs (r_base + 3) = n ∧
      s'.regs (r_base + 4) = m ∧
      s'.regs (r_base + 7) = 0 ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < r_base + 9 → r ≠ r_base + 1 → r ≠ r_base + 2 → r ≠ r_base + 7 →
        s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction us generalizing pre_src pre_dst rem_dst s with
  | nil =>
    refine ⟨s, (Expr.reg (r_base + 7)).cost,
      .while_false (by simp [Expr.eval, checkWord, hr_vrem, h0_w]),
      by simp [Expr.cost], ?_, ?_, ?_, hr_n, hr_m, ?_,
      fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
    · simp [encLengthPrefixedLists, ha_dst]
    · simp [hr_src]
    · simp [encLengthPrefixedLists, hr_dst]
    · simp [hr_vrem]
  | cons u us ih =>
    have hrem_u : (n + m + 2) + us.length * (n + m + 2) ≤ rem_dst := by
      simpa [List.length_cons, Nat.succ_mul, Nat.add_comm] using hrem_le
    have hv_len_le : 1 + (indicesOfOnes 0 (bitSetList (vertVerts u))).length ≤ n + 1 := by
      have := length_indicesOfOnes_le 0 (bitSetList (vertVerts u))
      rw [length_bitSetList] at this
      omega
    have he_len_le : 1 + (indicesOfOnes 0 (bitSetList (vertEdges u))).length ≤ m + 1 := by
      have := length_indicesOfOnes_le 0 (bitSetList (vertEdges u))
      rw [length_bitSetList] at this
      omega
    have hv_bits_w : ∀ b ∈ bitSetList (vertVerts u), b < 2 ^ w := by
      intro b hb
      rcases List.getElem_of_mem hb with ⟨i, hi, rfl⟩
      have := getElem_bitSetList_le_one (vertVerts u) i hi
      omega
    have he_bits_w : ∀ b ∈ bitSetList (vertEdges u), b < 2 ^ w := by
      intro b hb
      rcases List.getElem_of_mem hb with ⟨i, hi, rfl⟩
      have := getElem_bitSetList_le_one (vertEdges u) i hi
      omega
    let restRaw := us.flatMap (fun x => bitSetList (vertVerts x) ++ bitSetList (vertEdges x))
    have ha_src_v : s.arrs a_src =
        pre_src ++ bitSetList (vertVerts u) ++ (bitSetList (vertEdges u) ++ restRaw ++ post_src) := by
      rw [ha_src]
      simp [restRaw, List.append_assoc]
    rcases bitListToLenListProg_exec a_src a_dst (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 9)
      hne_arr (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      hw (bitSetList (vertVerts u))
      pre_src (bitSetList (vertEdges u) ++ restRaw ++ post_src) pre_dst rem_dst
      (by omega)
      (by simpa [restRaw, List.append_assoc] using hsrc_w)
      hdst_w hv_bits_w ha_src_v ha_dst hr_src hr_dst
      (by simp [hr_n, length_bitSetList]) with
      ⟨s₁, t₁, hex₁, ht₁, hdst₁, hsrc₁, hr_dst₁, harr₁, hreg₁⟩
    let vOut := (finsetToList (vertVerts u)).length :: finsetToList (vertVerts u)
    have hvOut_eq :
        (indicesOfOnes 0 (bitSetList (vertVerts u))).length ::
          indicesOfOnes 0 (bitSetList (vertVerts u)) = vOut := by
      simp [vOut]
    have hvOut_len : vOut.length ≤ n + 1 := by
      rw [← hvOut_eq, List.length_cons]
      omega
    rw [hvOut_eq] at hdst₁ hr_dst₁
    have ha_src_e : s₁.arrs a_src =
        (pre_src ++ bitSetList (vertVerts u)) ++ bitSetList (vertEdges u) ++ (restRaw ++ post_src) := by
      rw [harr₁ a_src hne_arr, ha_src]
      simp [restRaw, List.append_assoc]
    rcases bitListToLenListProg_exec a_src a_dst (r_base + 1) (r_base + 2) (r_base + 4) (r_base + 9)
      hne_arr (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      hw (bitSetList (vertEdges u))
      (pre_src ++ bitSetList (vertVerts u)) (restRaw ++ post_src) (pre_dst ++ vOut)
      (rem_dst - vOut.length)
      (by omega)
      (by simpa [restRaw, List.append_assoc] using hsrc_w)
      (by rw [List.length_append]; omega)
      he_bits_w ha_src_e hdst₁ hsrc₁ hr_dst₁
      (by
        rw [hreg₁ (r_base + 4) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
        simp [hr_m, length_bitSetList]) with
      ⟨s₂, t₂, hex₂, ht₂, hdst₂, hsrc₂, hr_dst₂, harr₂, hreg₂⟩
    let eOut := (finsetToList (vertEdges u)).length :: finsetToList (vertEdges u)
    have heOut_eq :
        (indicesOfOnes 0 (bitSetList (vertEdges u))).length ::
          indicesOfOnes 0 (bitSetList (vertEdges u)) = eOut := by
      simp [eOut]
    have heOut_len : eOut.length ≤ m + 1 := by
      rw [← heOut_eq, List.length_cons]
      omega
    rw [heOut_eq] at hdst₂ hr_dst₂
    have hr_vrem₂ : s₂.regs (r_base + 7) = us.length + 1 := by
      rw [hreg₂ (r_base + 7) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₁ (r_base + 7) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
      simpa using hr_vrem
    have hvrem_w : us.length + 1 < 2 ^ w := by
      have h1 : us.length * 1 ≤ us.length * (n + m + 2) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hvrem0_w : us.length < 2 ^ w := by omega
    let s₃ := s₂.setReg (r_base + 7) us.length
    have hex₃ : Exec w (.assign (r_base + 7) (.op .sub (.reg (r_base + 7)) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_vrem₂, hvrem_w, hw, hvrem0_w])
    have hex_body : Exec w
        (.seq (bitListToLenListProg a_src a_dst (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 9))
        (.seq (bitListToLenListProg a_src a_dst (r_base + 1) (r_base + 2) (r_base + 4) (r_base + 9))
              (.assign (r_base + 7) (.op .sub (.reg (r_base + 7)) (.const 1)))))
        s s₃ (t₁ + (t₂ + 4)) :=
      .seq hex₁ (.seq hex₂ hex₃)
    have ha_src₃ : s₃.arrs a_src =
        (pre_src ++ (bitSetList (vertVerts u) ++ bitSetList (vertEdges u))) ++ restRaw ++ post_src := by
      have h1 : s₃.arrs a_src = s.arrs a_src :=
        (harr₂ a_src hne_arr).trans (harr₁ a_src hne_arr)
      rw [h1, ha_src]
      simp [restRaw, List.append_assoc]
    have ha_dst₃ : s₃.arrs a_dst =
        (pre_dst ++ (vOut ++ eOut)) ++ List.replicate (rem_dst - (vOut ++ eOut).length) 0 := by
      have hsub : rem_dst - vOut.length - eOut.length = rem_dst - (vOut ++ eOut).length := by
        simp; omega
      simpa [s₃, List.append_assoc, hsub] using hdst₂
    have hr_n₃ : s₃.regs (r_base + 3) = n := by
      simp only [s₃]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          hreg₂ (r_base + 3) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₁ (r_base + 3) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
      exact hr_n
    have hr_m₃ : s₃.regs (r_base + 4) = m := by
      simp only [s₃]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          hreg₂ (r_base + 4) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₁ (r_base + 4) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
      exact hr_m
    rcases ih
      (pre_src ++ (bitSetList (vertVerts u) ++ bitSetList (vertEdges u)))
      (pre_dst ++ (vOut ++ eOut))
      (rem_dst - (vOut ++ eOut).length)
      (by rw [List.length_append]; omega)
      (by simpa [restRaw, List.append_assoc] using hsrc_w)
      (by rw [List.length_append, List.length_append]; omega)
      ha_src₃ ha_dst₃
      (by
        simp only [s₃]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega), hsrc₂]
        simp [List.append_assoc])
      (by
        simp only [s₃]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega), hr_dst₂]
        simp [List.append_assoc])
      hr_n₃ hr_m₃ (by simp [s₃]) with
      ⟨s', t_rest, hex_rest, ht_rest, hdst', hsrc', hdst_reg', hn', hm', hvrem', harr', hreg'⟩
    have hout_cons :
        encLengthPrefixedLists ((u :: us).flatMap (fun x =>
          [finsetToList (vertVerts x), finsetToList (vertEdges x)])) =
        (vOut ++ eOut) ++ encLengthPrefixedLists (us.flatMap (fun x =>
          [finsetToList (vertVerts x), finsetToList (vertEdges x)])) := by
      simp [encLengthPrefixedLists, vOut, eOut, List.append_assoc]
    have hcond_vrem : (Expr.reg (r_base + 7)).eval w s = some (us.length + 1) := by
      simp [Expr.eval, checkWord, hr_vrem, hvrem_w]
    refine ⟨s', (Expr.reg (r_base + 7)).cost + (t₁ + (t₂ + 4)) + t_rest,
      .while_true hcond_vrem (by omega) hex_body hex_rest,
      ?_, ?_, ?_, ?_, hn', hm', hvrem',
      fun a ha => (harr' a ha).trans ((harr₂ a ha).trans (harr₁ a ha)),
      fun r hr h1 h2 h7 => (hreg' r hr h1 h2 h7).trans
        (by
          simp only [s₃]
          rw [State.setReg_regs_ne _ _ h7]
          exact (hreg₂ r hr h1 h2).trans (hreg₁ r hr h1 h2))⟩
    · simp only [length_bitSetList, Expr.cost] at ht₁ ht₂ ⊢
      rw [List.length_cons, Nat.succ_mul]
      omega
    · rw [hout_cons]
      have hsub : rem_dst - (vOut ++ eOut).length -
          (encLengthPrefixedLists (us.flatMap (fun x =>
            [finsetToList (vertVerts x), finsetToList (vertEdges x)]))).length =
          rem_dst - ((vOut ++ eOut) ++ encLengthPrefixedLists (us.flatMap (fun x =>
            [finsetToList (vertVerts x), finsetToList (vertEdges x)]))).length := by
        simp; omega
      simpa [List.append_assoc, Nat.sub_sub, List.length_append, Nat.add_assoc] using hdst'
    · simpa [List.append_assoc] using hsrc'
    · rw [hout_cons]
      simpa [List.append_assoc] using hdst_reg'

/-- Convert all `r_krem` raw model entries from `a_src` (reading `(c_len, v_H, m_H)` headers at
`r_hdr = r_base` and raw model data at `r_src = r_base + 1`) into `encModelFull` blocks in `a_dst`
(at `r_dst = r_base + 2`). -/
def convertAllModelsLoop (a_src a_dst : Arr) (r_base : Reg) : Cmd :=
  let r_hdr := r_base
  let r_src := r_base + 1
  let r_dst := r_base + 2
  let r_n := r_base + 3
  let r_m := r_base + 4
  let r_krem := r_base + 5
  let r_clen := r_base + 6
  let r_vH := r_base + 7
  let r_mH := r_base + 8
  .while (.reg r_krem)
    (.seq (.assign r_clen (.read a_src (.reg r_hdr)))
    (.seq (.assign r_hdr (.op .add (.reg r_hdr) (.const 1)))
    (.seq (.assign r_vH (.read a_src (.reg r_hdr)))
    (.seq (.assign r_mH (.op .add (.reg r_hdr) (.const 1)))
    (.seq (.assign r_mH (.read a_src (.reg r_mH)))
    (.seq (.assign r_hdr (.op .add (.reg r_hdr) (.reg r_clen)))
    (.seq (copyWordsLoop a_src a_dst r_src r_dst r_mH (r_base + 9))
    (.seq (convertVertModelsLoop a_src a_dst r_src r_dst r_n r_m r_vH (r_base + 9))
          (.assign r_krem (.op .sub (.reg r_krem) (.const 1)))))))))))

theorem length_rawCertEntry_toRaw {n δ q : ℕ} {G : MultiDigraph n}
    {r_fn : Fin q → Fin G.toComputeDigraph.numVerts}
    (e : CertFolioEntry G.toComputeDigraph Finset.univ Finset.univ r_fn δ) :
    (encRawCertEntry e.toRaw).length =
      e.H.digraph.numEdges +
        e.H.digraph.numVerts * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges) := by
  unfold encRawCertEntry CertFolioEntry.toRaw
  rw [List.length_append, List.length_map, List.length_finRange, List.length_flatMap]
  simp [length_bitSetList, List.map_const', List.sum_replicate]

theorem words_encModelFull_lt {k w : ℕ} {H G : ComputeRootedDigraph k}
    (M : RootedDigraphModel H G)
    (hn_w : G.digraph.numVerts < 2 ^ w) (hm_w : G.digraph.numEdges < 2 ^ w) :
    ∀ x ∈ encModelFull M, x < 2 ^ w := by
  intro x hx
  unfold encModelFull encLengthPrefixedLists at hx
  simp only [List.mem_append, List.mem_ofFn, List.mem_flatMap, List.mem_finRange,
    List.mem_cons, List.not_mem_nil, or_false, true_and] at hx
  rcases hx with ⟨e, rfl⟩ | ⟨l, ⟨u, rfl | rfl⟩, rfl | hx_mem⟩
  · exact Nat.lt_trans (M.edgeMap e).2 hm_w
  · have hle : (finsetToList (M.vertMap u).verts).length ≤ G.digraph.numVerts := by
      rw [length_finsetToList]
      exact (Finset.card_le_univ _).trans (by simp)
    omega
  · rw [mem_finsetToList_iff] at hx_mem
    rcases hx_mem with ⟨v, _, rfl⟩
    exact Nat.lt_trans v.2 hn_w
  · have hle : (finsetToList (M.vertMap u).edges).length ≤ G.digraph.numEdges := by
      rw [length_finsetToList]
      exact (Finset.card_le_univ _).trans (by simp)
    omega
  · rw [mem_finsetToList_iff] at hx_mem
    rcases hx_mem with ⟨e, _, rfl⟩
    exact Nat.lt_trans e.2 hm_w

theorem convertAllModelsLoop_exec {w n δ q : ℕ} {G : MultiDigraph n}
    {r_fn : Fin q → Fin G.toComputeDigraph.numVerts}
    (a_src a_dst : Arr) (r_base : Reg)
    (hne_arr : a_src ≠ a_dst)
    (hw : 1 < 2 ^ w)
    (es : List (CertFolioEntry G.toComputeDigraph Finset.univ Finset.univ r_fn δ))
    (pre_hdr post_hdr pre_src post_src pre_dst : List ℕ) (rem_dst : ℕ)
    (hrem_le :
      (encRawCertModels (es.map CertFolioEntry.toRaw)).length + es.length * ((q + δ) * 2 + 1) ≤ rem_dst)
    (hhdr_w : (pre_hdr ++ es.flatMap (fun e => (encRootedDigraph e.H).length :: encRootedDigraph e.H) ++ post_hdr).length < 2 ^ w)
    (hsrc_w : (pre_src ++ encRawCertModels (es.map CertFolioEntry.toRaw) ++ post_src).length < 2 ^ w)
    (hdst_w : pre_dst.length + rem_dst < 2 ^ w)
    (hcodes_w : ∀ e ∈ es, ∀ u ∈ (encRootedDigraph e.H).length :: encRootedDigraph e.H, u < 2 ^ w)
    (hraw_w : ∀ u ∈ encRawCertModels (es.map CertFolioEntry.toRaw), u < 2 ^ w)
    {s : State}
    (ha_hdr : s.arrs a_src = pre_hdr ++ es.flatMap (fun e => (encRootedDigraph e.H).length :: encRootedDigraph e.H) ++ post_hdr)
    (ha_src : s.arrs a_src = pre_src ++ encRawCertModels (es.map CertFolioEntry.toRaw) ++ post_src)
    (ha_dst : s.arrs a_dst = pre_dst ++ List.replicate rem_dst 0)
    (hr_hdr : s.regs r_base = pre_hdr.length)
    (hr_src : s.regs (r_base + 1) = pre_src.length)
    (hr_dst : s.regs (r_base + 2) = pre_dst.length)
    (hr_n : s.regs (r_base + 3) = G.toComputeDigraph.numVerts)
    (hr_m : s.regs (r_base + 4) = G.toComputeDigraph.numEdges)
    (hr_krem : s.regs (r_base + 5) = es.length) :
    let outModels := es.flatMap (fun e => encModelFull e.model.toRootedDigraphModel)
    ∃ s' t,
      Exec w (convertAllModelsLoop a_src a_dst r_base) s s' t ∧
      t ≤ es.length * ((q + δ) * (28 * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges) + 50) + 19 * δ + 30) + 1 ∧
      s'.arrs a_dst = (pre_dst ++ outModels) ++ List.replicate (rem_dst - outModels.length) 0 ∧
      s'.regs (r_base + 2) = (pre_dst ++ outModels).length ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction es generalizing pre_hdr pre_src pre_dst rem_dst s with
  | nil =>
    refine ⟨s, (Expr.reg (r_base + 5)).cost,
      .while_false (by simp [Expr.eval, checkWord, hr_krem, h0_w]),
      by simp [Expr.cost], ?_, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    · simp [ha_dst]
    · simp [hr_dst]
  | cons e es ih =>
    let v_H := e.H.digraph.numVerts
    let m_H := e.H.digraph.numEdges
    let c := encRootedDigraph e.H
    have hv_le : v_H ≤ q + δ := e.H.numVerts_le_of_hasDetailLe e.hdet
    have hm_le : m_H ≤ δ := e.hdet.1
    have hc_decomp :
        c.length :: c =
          [c.length, v_H, m_H] ++
            (List.ofFn (fun i : Fin q => (e.H.roots i).1) ++
              (List.finRange m_H).flatMap (fun x => [(e.H.digraph.head x).1, (e.H.digraph.tail x).1])) := by
      dsimp [c, v_H, m_H, encRootedDigraph]
    have hclen_w : c.length < 2 ^ w := hcodes_w e List.mem_cons_self c.length List.mem_cons_self
    have hvH_w : v_H < 2 ^ w := by
      apply hcodes_w e List.mem_cons_self v_H
      rw [hc_decomp]; simp
    have hmH_w : m_H < 2 ^ w := by
      apply hcodes_w e List.mem_cons_self m_H
      rw [hc_decomp]; simp
    have hc_len2 : 2 ≤ c.length := by
      dsimp [c, encRootedDigraph]
      simp
    have hhdr_len_bound : pre_hdr.length + 1 + c.length + es.length ≤
        (pre_hdr ++ (e :: es).flatMap (fun e' => (encRootedDigraph e'.H).length :: encRootedDigraph e'.H) ++ post_hdr).length := by
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hes_len : es.length ≤ (es.flatMap (fun e' => (encRootedDigraph e'.H).length :: encRootedDigraph e'.H)).length := by
        clear * -
        induction es with
        | nil => simp
        | cons x xs ihx =>
          simp only [List.flatMap_cons, List.length_append, List.length_cons]
          omega
      dsimp [c]
      omega
    have hhdr0_w : pre_hdr.length < 2 ^ w := by omega
    have hhdr1_w : pre_hdr.length + 1 < 2 ^ w := by omega
    have hhdr2_w : pre_hdr.length + 2 < 2 ^ w := by omega
    have hhdr_end_w : pre_hdr.length + 1 + c.length < 2 ^ w := by omega
    let restHdr := es.flatMap (fun e' => (encRootedDigraph e'.H).length :: encRootedDigraph e'.H) ++ post_hdr
    let tailCode := List.ofFn (fun i : Fin q => (e.H.roots i).1) ++
      (List.finRange m_H).flatMap (fun x => [(e.H.digraph.head x).1, (e.H.digraph.tail x).1])
    have ha_hdr_flat :
        s.arrs a_src = pre_hdr ++ ([c.length, v_H, m_H] ++ tailCode ++ restHdr) := by
      rw [ha_hdr]
      simp only [List.flatMap_cons, List.append_assoc]
      congr 1
    have hget0 : (s.arrs a_src).getD pre_hdr.length 0 = c.length := by
      rw [ha_hdr_flat, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp
    have hget1 : (s.arrs a_src).getD (pre_hdr.length + 1) 0 = v_H := by
      rw [ha_hdr_flat, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by omega)]
      have hsub : pre_hdr.length + 1 - pre_hdr.length = 1 := by omega
      simp [hsub]
    have hget2 : (s.arrs a_src).getD (pre_hdr.length + 2) 0 = m_H := by
      rw [ha_hdr_flat, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by omega)]
      have hsub : pre_hdr.length + 2 - pre_hdr.length = 2 := by omega
      simp [hsub]
    let s₁ := s.setReg (r_base + 6) c.length
    have hex₁ : Exec w (.assign (r_base + 6) (.read a_src (.reg r_base))) s s₁ 3 :=
      exec_assign_read_getD (r_base + 6) a_src r_base hr_hdr hhdr0_w
        (by rw [ha_hdr_flat]; simp) hget0 hclen_w
    let s₂ := s₁.setReg r_base (pre_hdr.length + 1)
    have hex₂ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_hdr, hhdr0_w, hw, hhdr1_w])
    let s₃ := s₂.setReg (r_base + 7) v_H
    have hex₃ : Exec w (.assign (r_base + 7) (.read a_src (.reg r_base))) s₂ s₃ 3 :=
      exec_assign_read_getD (r_base + 7) a_src r_base (by simp [s₂]) hhdr1_w
        (by change pre_hdr.length + 1 < (s.arrs a_src).length; rw [ha_hdr_flat]; simp)
        hget1 hvH_w
    let s₄ := s₃.setReg (r_base + 8) (pre_hdr.length + 2)
    have hex₄ : Exec w (.assign (r_base + 8) (.op .add (.reg r_base) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hhdr1_w, hw, hhdr2_w])
    let s₅ := s₄.setReg (r_base + 8) m_H
    have hex₅ : Exec w (.assign (r_base + 8) (.read a_src (.reg (r_base + 8)))) s₄ s₅ 3 :=
      exec_assign_read_getD (r_base + 8) a_src (r_base + 8) (by simp [s₄]) hhdr2_w
        (by change pre_hdr.length + 2 < (s.arrs a_src).length; rw [ha_hdr_flat]; simp)
        hget2 hmH_w
    let s₆ := s₅.setReg r_base (pre_hdr.length + 1 + c.length)
    have hrs₅_base : s₅.regs r_base = pre_hdr.length + 1 := by
      simp only [s₅, s₄, s₃, s₂]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp
    have hrs₅_6 : s₅.regs (r_base + 6) = c.length := by
      simp only [s₅, s₄, s₃, s₂, s₁]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp
    have hex₆ : Exec w (.assign r_base (.op .add (.reg r_base) (.reg (r_base + 6)))) s₅ s₆ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs₅_base, hrs₅_6,
        hhdr1_w, hclen_w, hhdr_end_w])
    let edgeWords := List.ofFn (fun e' : Fin m_H => (e.model.edgeMap e').1)
    have hedgeWords_map : (List.finRange m_H).map (fun e' => (e.model.edgeMap e').1) = edgeWords :=
      List.ofFn_eq_map.symm
    let vertRaw := (List.finRange v_H).flatMap (fun u =>
      bitSetList (e.model.vertMap u).verts ++ bitSetList (e.model.vertMap u).edges)
    let restRaw := encRawCertModels (es.map CertFolioEntry.toRaw) ++ post_src
    have he_raw_decomp : encRawCertEntry e.toRaw = edgeWords ++ vertRaw := by
      unfold encRawCertEntry CertFolioEntry.toRaw
      dsimp only
      rw [hedgeWords_map]
    have ha_src₆ : s₆.arrs a_src = pre_src ++ edgeWords ++ (vertRaw ++ restRaw) := by
      change s.arrs a_src = _
      rw [ha_src]
      simp only [List.map_cons, encRawCertModels, List.flatMap_cons, he_raw_decomp,
        restRaw, List.append_assoc]
    have hraw_cons :
        (encRawCertModels ((e :: es).map CertFolioEntry.toRaw)).length =
          m_H + v_H * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges) +
            (encRawCertModels (es.map CertFolioEntry.toRaw)).length := by
      unfold encRawCertModels
      rw [List.map_cons, List.flatMap_cons, List.length_append, length_rawCertEntry_toRaw]
    have hv_two : v_H * 2 ≤ (q + δ) * 2 := Nat.mul_le_mul_right 2 hv_le
    have hrem_e :
        m_H + v_H * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges + 2) +
          (encRawCertModels (es.map CertFolioEntry.toRaw)).length +
          es.length * ((q + δ) * 2 + 1) ≤ rem_dst := by
      rw [hraw_cons, List.length_cons, Nat.succ_mul] at hrem_le
      nlinarith
    have hedge_w : ∀ x ∈ edgeWords, x < 2 ^ w := by
      intro x hx
      apply hraw_w x
      unfold encRawCertModels
      rw [List.map_cons, List.flatMap_cons, he_raw_decomp]
      exact List.mem_append_left _ (List.mem_append_left _ hx)
    rcases copyWordsLoop_exec (s := s₆) a_src a_dst (r_base + 1) (r_base + 2) (r_base + 8) (r_base + 9)
      hne_arr (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      hw edgeWords pre_src (vertRaw ++ restRaw) pre_dst rem_dst
      (by simp only [edgeWords, List.length_ofFn]; omega)
      (by
        have h1 : pre_src ++ edgeWords ++ (vertRaw ++ restRaw) =
            pre_src ++ encRawCertModels ((e :: es).map CertFolioEntry.toRaw) ++ post_src := by
          unfold encRawCertModels
          rw [List.map_cons, List.flatMap_cons, he_raw_decomp]
          simp [restRaw, encRawCertModels, List.append_assoc]
        rwa [h1])
      hdst_w hedge_w ha_src₆ ha_dst
      (by
        simp only [s₆, s₅, s₄, s₃, s₂, s₁]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
        exact hr_src)
      (by
        simp only [s₆, s₅, s₄, s₃, s₂, s₁]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
        exact hr_dst)
      (by
        simp only [s₆, s₅, edgeWords]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
        simp) with
      ⟨s₇, t₇, hex₇, ht₇, hdst₇, hsrc₇, hr_dst₇, _, harr₇, hreg₇⟩
    have ha_src₇ : s₇.arrs a_src = (pre_src ++ edgeWords) ++ vertRaw ++ restRaw := by
      rw [harr₇ a_src hne_arr, ha_src₆]
      simp [List.append_assoc]
    rcases convertVertModelsLoop_exec
      (n := G.toComputeDigraph.numVerts) (m := G.toComputeDigraph.numEdges) (v_H := v_H)
      (s := s₇) a_src a_dst r_base hne_arr hw
      (fun u => (e.model.vertMap u).verts) (fun u => (e.model.vertMap u).edges)
      (List.finRange v_H) (pre_src ++ edgeWords) restRaw (pre_dst ++ edgeWords)
      (rem_dst - edgeWords.length)
      (by
        simp only [edgeWords, List.length_ofFn, List.length_finRange]
        have hmul := Nat.mul_le_mul_right 2 hv_le
        dsimp only [MultiDigraph.toComputeDigraph] at hrem_e ⊢
        have heq : v_H * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges + 2) = v_H * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges) + v_H * 2 := by rw [Nat.mul_add]
        omega)
      (by
        have h1 : (pre_src ++ edgeWords) ++ vertRaw ++ restRaw =
            pre_src ++ encRawCertModels ((e :: es).map CertFolioEntry.toRaw) ++ post_src := by
          unfold encRawCertModels
          rw [List.map_cons, List.flatMap_cons, he_raw_decomp]
          simp [restRaw, encRawCertModels, List.append_assoc]
        rwa [h1])
      (by
        simp only [edgeWords, List.length_ofFn, List.length_append]
        dsimp only [MultiDigraph.toComputeDigraph] at hrem_e ⊢
        omega)
      ha_src₇ hdst₇ hsrc₇ hr_dst₇
      (by
        rw [hreg₇ (r_base + 3) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
        simp only [s₆, s₅, s₄, s₃, s₂, s₁]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
        exact hr_n)
      (by
        rw [hreg₇ (r_base + 4) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
        simp only [s₆, s₅, s₄, s₃, s₂, s₁]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
        exact hr_m)
      (by
        rw [hreg₇ (r_base + 7) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
        simp only [s₆, s₅, s₄, s₃]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
        simp) with
      ⟨s₈, t₈, hex₈, ht₈, hdst₈, hsrc₈, hr_dst₈, hn₈, hm₈, _, harr₈, hreg₈⟩
    have hr_krem₈ : s₈.regs (r_base + 5) = es.length + 1 := by
      rw [hreg₈ (r_base + 5) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₇ (r_base + 5) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
      simp only [s₆, s₅, s₄, s₃, s₂, s₁]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simpa using hr_krem
    have hkrem_w : es.length + 1 < 2 ^ w := by omega
    have hkrem0_w : es.length < 2 ^ w := by omega
    let s₉ := s₈.setReg (r_base + 5) es.length
    have hex₉ : Exec w (.assign (r_base + 5) (.op .sub (.reg (r_base + 5)) (.const 1))) s₈ s₉ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_krem₈, hkrem_w, hw, hkrem0_w])
    have hex_body : Exec w
        (.seq (.assign (r_base + 6) (.read a_src (.reg r_base)))
        (.seq (.assign r_base (.op .add (.reg r_base) (.const 1)))
        (.seq (.assign (r_base + 7) (.read a_src (.reg r_base)))
        (.seq (.assign (r_base + 8) (.op .add (.reg r_base) (.const 1)))
        (.seq (.assign (r_base + 8) (.read a_src (.reg (r_base + 8))))
        (.seq (.assign r_base (.op .add (.reg r_base) (.reg (r_base + 6))))
        (.seq (copyWordsLoop a_src a_dst (r_base + 1) (r_base + 2) (r_base + 8) (r_base + 9))
        (.seq (convertVertModelsLoop a_src a_dst (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 7) (r_base + 9))
              (.assign (r_base + 5) (.op .sub (.reg (r_base + 5)) (.const 1)))))))))))
        s s₉ (3 + (4 + (3 + (4 + (3 + (4 + (t₇ + (t₈ + 4)))))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ hex₉)))))))
    let mFull := encModelFull e.model.toRootedDigraphModel
    have hmFull_eq :
        edgeWords ++ encLengthPrefixedLists ((List.finRange v_H).flatMap (fun u =>
          [finsetToList (e.model.vertMap u).verts, finsetToList (e.model.vertMap u).edges])) =
        mFull := rfl
    have hmFull_len_le : mFull.length ≤ m_H + v_H * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges + 2) := by
      rw [← hmFull_eq, List.length_append]
      have h1 := length_encLengthPrefixed_vert_le
        (n := G.toComputeDigraph.numVerts) (m := G.toComputeDigraph.numEdges) (v_H := v_H)
        (fun u => (e.model.vertMap u).verts) (fun u => (e.model.vertMap u).edges) (List.finRange v_H)
      rw [List.length_finRange] at h1
      rw [show edgeWords.length = m_H by simp [edgeWords]]
      exact Nat.add_le_add_left h1 m_H
    have ha_hdr₉ : s₉.arrs a_src =
        (pre_hdr ++ (c.length :: c)) ++
          es.flatMap (fun e' => (encRootedDigraph e'.H).length :: encRootedDigraph e'.H) ++ post_hdr := by
      have h1 : s₉.arrs a_src = s.arrs a_src :=
        (harr₈ a_src hne_arr).trans (harr₇ a_src hne_arr)
      rw [h1, ha_hdr]
      simp [c, List.append_assoc]
    have ha_src₉ : s₉.arrs a_src =
        (pre_src ++ encRawCertEntry e.toRaw) ++ encRawCertModels (es.map CertFolioEntry.toRaw) ++ post_src := by
      have h1 : s₉.arrs a_src = s.arrs a_src :=
        (harr₈ a_src hne_arr).trans (harr₇ a_src hne_arr)
      rw [h1, ha_src]
      simp [encRawCertModels, List.append_assoc]
    have ha_dst₉ : s₉.arrs a_dst =
        (pre_dst ++ mFull) ++ List.replicate (rem_dst - mFull.length) 0 := by
      have hsub : rem_dst - edgeWords.length -
          (encLengthPrefixedLists ((List.finRange v_H).flatMap (fun u =>
            [finsetToList (e.model.vertMap u).verts, finsetToList (e.model.vertMap u).edges]))).length =
          rem_dst - mFull.length := by
        rw [← hmFull_eq, List.length_append]; omega
      simpa [s₉, mFull, edgeWords, encModelFull, List.append_assoc, Nat.sub_sub, List.length_append, Nat.add_assoc] using hdst₈
    rcases ih (pre_hdr ++ (c.length :: c)) (pre_src ++ encRawCertEntry e.toRaw) (pre_dst ++ mFull)
      (rem_dst - mFull.length)
      (by omega)
      (by simpa [c, List.append_assoc] using hhdr_w)
      (by simpa [encRawCertModels, List.append_assoc] using hsrc_w)
      (by simp only [List.length_append]; omega)
      (fun e' he' u hu => hcodes_w e' (List.mem_cons_of_mem e he') u hu)
      (fun u hu => hraw_w u (by
        unfold encRawCertModels at hu ⊢
        rw [List.map_cons, List.flatMap_cons]
        exact List.mem_append_right _ hu))
      ha_hdr₉ ha_src₉ ha_dst₉
      (by
        simp only [s₉]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            hreg₈ r_base (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
            hreg₇ r_base (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
        simp only [s₆, State.setReg_regs_self, List.length_append, List.length_cons]
        omega)
      (by
        simp only [s₉]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega), he_raw_decomp]
        simpa [vertRaw, List.append_assoc] using hsrc₈)
      (by
        simp only [s₉]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
        simpa [mFull, edgeWords, encModelFull, List.append_assoc] using hr_dst₈)
      (by
        simp only [s₉]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
        exact hn₈)
      (by
        simp only [s₉]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
        exact hm₈)
      (by simp [s₉]) with
      ⟨s', t_rest, hex_rest, ht_rest, hdst', hdst_reg', harr', hreg'⟩
    have hcond_krem : (Expr.reg (r_base + 5)).eval w s = some (es.length + 1) := by
      simp [Expr.eval, checkWord, hr_krem, hkrem_w]
    refine ⟨s', (Expr.reg (r_base + 5)).cost + (3 + (4 + (3 + (4 + (3 + (4 + (t₇ + (t₈ + 4)))))))) + t_rest,
      .while_true hcond_krem (by omega) hex_body hex_rest,
      ?_, ?_, ?_,
      fun a ha => (harr' a ha).trans ((harr₈ a ha).trans (harr₇ a ha)),
      fun r hr => (hreg' r hr).trans
        (by
          simp only [s₉]
          rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
              hreg₈ r (by dsimp [Reg] at hr ⊢; omega) (by dsimp [Reg] at hr ⊢; omega)
                (by dsimp [Reg] at hr ⊢; omega) (by dsimp [Reg] at hr ⊢; omega),
              hreg₇ r (by dsimp [Reg] at hr ⊢; omega) (by dsimp [Reg] at hr ⊢; omega)
                (by dsimp [Reg] at hr ⊢; omega) (by dsimp [Reg] at hr ⊢; omega)]
          simp only [s₆, s₅, s₄, s₃, s₂, s₁]
          rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
              State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
              State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
              State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
              State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
              State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega)])⟩
    · simp only [edgeWords, List.length_ofFn, List.length_finRange, Expr.cost] at ht₇ ht₈ ⊢
      have hmul_t :
          v_H * (28 * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges) + 50) ≤
            (q + δ) * (28 * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges) + 50) :=
        Nat.mul_le_mul_right _ hv_le
      rw [List.length_cons, Nat.succ_mul]
      dsimp only [MultiDigraph.toComputeDigraph] at ht₇ ht₈ ht_rest hmul_t ⊢
      omega
    · have hsub : rem_dst - mFull.length -
          (es.flatMap (fun e' => encModelFull e'.model.toRootedDigraphModel)).length =
          rem_dst - (mFull ++ es.flatMap (fun e' => encModelFull e'.model.toRootedDigraphModel)).length := by
        rw [List.length_append]; omega
      rw [hsub, List.append_assoc] at hdst'
      simpa only [List.flatMap_cons, mFull, List.append_assoc] using hdst'
    · simpa [List.flatMap_cons, mFull, List.append_assoc] using hdst_reg'


end GraphMinor.Compute
