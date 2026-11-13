module

public import GraphMinor.Compute.CrossingOpsReplPre
public import GraphMinor.Compute.CrossingOpsReplEncode
public import GraphMinor.Compute.CrossingOpsReplRebuild
public import GraphMinor.Compute.CrossingOpsReplFrames

/-!
# The replacement program with buffered records

The program follows the five phases of replacement: copy and mark the input, encode its
record, append it to the record buffer, rebuild the adjacency lists, and clear the deleted
vertices from the alive array. The cycle is preserved.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

private theorem moveRecBuf {N x r k : ℕ} {recs : List (CrossRecord (Fin N))} {s s' : State}
    (h : IsRecBufAt x r recs k s) (ha : s'.arrs x = s.arrs x) (hr : s'.regs r = s.regs r) :
    IsRecBufAt x r recs k s' := by
  obtain ⟨ls, hls, harr, hreg⟩ := h
  exact ⟨ls, hls, ha.trans harr, hr.trans hreg⟩

/-- The five-phase replacement program meets the buffered-record interface. -/
theorem replaceRecProgClaim_proved : ReplaceRecProgClaim := by
  intro a a_del a_bd a_rep a_rec r_rec A R hok hrr
  refine ⟨replaceBufProg a a_del a_bd a_rep a_rec r_rec A R, 1000, 4,
    fun w N G S D r recs S' k s hw hinst hcyc hgraph hverts hv hS' hdel hbd hrep hrec hk => ?_⟩
  subst G
  have hsz : instSize N r.graph = N + r.graph.edgeSet.ncard + 1 := rfl
  have hw' : 16 * (instSize N r.graph + (s.arrs a_rec).length) + 16 < 2 ^ w := by
    have h1 := pow_lt_two_pow_wordSize (c := 4) (by omega)
      (instSize N r.graph + (s.arrs a_rec).length)
    have h2 : 2 ^ wordSize 4 (instSize N r.graph + (s.arrs a_rec).length) ≤ 2 ^ w :=
      Nat.pow_le_pow_right (by omega) hw
    have h3 := sixteen_le_pow (instSize N r.graph + (s.arrs a_rec).length)
    omega
  have hokA : ArrsOk a.list A := ⟨hok.1.sublist (List.sublist_append_left _ _),
    fun x hx => hok.2 x (List.mem_append_left _ hx)⟩
  have hdelA : a_del < A := hok.2 a_del (by simp)
  have hbdA : a_bd < A := hok.2 a_bd (by simp)
  have hrepA : a_rep < A := hok.2 a_rep (by simp)
  have hrecA : a_rec < A := hok.2 a_rec (by simp)
  have hal : a.alive < A := hokA.2 _ (by simp [InstArrs.list])
  have hst : a.st < A := hokA.2 _ (by simp [InstArrs.list])
  have hen : a.en < A := hokA.2 _ (by simp [InstArrs.list])
  have hent : a.ent < A := hokA.2 _ (by simp [InstArrs.list])
  have hcy : a.cyc < A := hokA.2 _ (by simp [InstArrs.list])
  have hnd := hok.1
  simp only [InstArrs.list, List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h12, h13, h14, h15, h1d, h1b, h1p, h1r⟩,
    ⟨h23, h24, h25, h2d, h2b, h2p, h2r⟩,
    ⟨h34, h35, h3d, h3b, h3p, h3r⟩,
    ⟨h45, h4d, h4b, h4p, h4r⟩,
    ⟨h5d, h5b, h5p, h5r⟩, ⟨hdb, hdp, hdr⟩, ⟨hbp, hbr⟩, hpr⟩ := hnd
  obtain ⟨Dl, hDn, hDm, hDa⟩ := hdel
  obtain ⟨B, hBn, hBm, hBa⟩ := hbd
  obtain ⟨Rp, hRn, hRm, hRa⟩ := hrep
  let dl := Dl.map Fin.val
  let bl := B.map Fin.val
  let rp := Rp.map Fin.val
  have hblsmall : bl.length ≤ 3 := by
    have hset : B.toFinset = r.boundary := by ext y; simp [hBm]
    have hcard := List.toFinset_card_of_nodup hBn
    rw [hset] at hcard
    simpa only [bl, List.length_map, ← hcard] using hv.2.2.1
  have hDN : D.length ≤ N := by simpa using hcyc.2.1.length_le_card
  obtain ⟨s1, t1, hex1, ht1, hi1, hN1, hd1, hb1, hu1, hm1, ha1⟩ := replPreProg_exec (w := w)
    a a_del a_bd a_rep A R hokA hdelA hbdA hrepA hinst hDN hDa hBa hRa
    (hDn.map Fin.val_injective) (hBn.map Fin.val_injective) (hRn.map Fin.val_injective)
    (vals_lt Dl) (vals_lt B) (vals_lt Rp) (by omega)
  obtain ⟨lists, hadj1⟩ := hi1.2.2.1
  have hent1 : (s1.arrs (A + 2)).length = 2 * r.graph.edgeSet.ncard := hi1.2.2.2.1
  obtain ⟨s2, t2, hex2, ht2, he2, henc2, ha2⟩ := replEncodeProg_exec (w := w)
    a_bd a_rep A R hbdA hrepA hN1 ((ha1 a_bd hbdA).trans hBa)
    ((ha1 a_rep hrepA).trans hRa) hu1 hm1 hadj1 hent1 hv hBn hBm hRn hRm (by omega)
  let enc := replRecordWords lists bl rp
  have hdisj : ∀ y ∈ Rp, y ∉ B := by
    intro y hy hB
    exact (hv.2.2.2.1 ((hBm y).mp hB)).2 (hv.2.2.2.2.2.1 ((hRm y).mp hy))
  have hndu : (rp ++ bl).Nodup := by
    rw [← List.map_append]
    exact (List.Nodup.append hRn hBn hdisj).map Fin.val_injective
  have hltu : ∀ x ∈ rp ++ bl, x < N := by simpa only [List.map_append] using vals_lt (Rp ++ B)
  have hlenU : bl.length + rp.length ≤ N := by
    have := length_le_of_nodup_lt hndu hltu
    simp only [List.length_append] at this
    omega
  have hpairs := length_flatMap_pairsOf_le hadj1.2 (rb := rp ++ bl) hndu hltu
  have hencLen : enc.length ≤ 5 * instSize N r.graph := by
    simp only [enc, replRecordWords, replHead, withLength, List.length_append,
      List.length_cons, List.length_nil]
    omega
  have hrec2 : IsRecBufAt a_rec r_rec recs k s2 := moveRecBuf hrec
    ((ha2 a_rec (by omega) (by omega)).trans (ha1 a_rec hrecA))
    ((repl_encode_regs_eq a_bd a_rep A R hex2 (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)).trans
      (repl_pre_regs_eq a a_del a_bd a_rep A R hex1 (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)))
  have hN2 : s2.regs (R + 8) = N :=
    (repl_encode_regs_eq a_bd a_rep A R hex2 (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)).trans hN1
  have he2' : s2.arrs (A + 7) = enc := he2
  have hreclen2 : (s2.arrs a_rec).length = (s.arrs a_rec).length := by
    rw [ha2 a_rec (by omega) (by omega), ha1 a_rec hrecA]
  obtain ⟨s3, t3, hex3, ht3, hrec3, hreclen3⟩ := contrAppBuf_exec (w := w)
    a_rec r_rec A R hrecA hrr hrec2 henc2 hN2 (by rw [he2']; omega)
    (by rw [he2', hreclen2]; omega)
  have ha3 : ∀ b, b ≠ a_rec → s3.arrs b = s2.arrs b := fun b hb =>
    repl_append_arrs_eq a_rec r_rec A R hex3 (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
  have hN3 : s3.regs (R + 8) = N :=
    (repl_append_regs_eq a_rec r_rec A R hex3 (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)).trans hN2
  have hadj3 : IsAdjList r.graph A (A + 1) (A + 2) lists s3 := hadj1.of_arrs_eq
    ((ha3 A (by omega)).trans (ha2 A (by omega) (by omega)))
    ((ha3 (A + 1) (by omega)).trans (ha2 (A + 1) (by omega) (by omega)))
    ((ha3 (A + 2) (by omega)).trans (ha2 (A + 2) (by omega) (by omega)))
  have hfamily : IsAdjListFamily r.newGraph (fun x => replList lists dl bl x) :=
    isAdjListFamily_replList hadj1.2
      (fun y => by simpa only [dl, val_mem_map] using hDm y)
      (fun y => by simpa only [bl, val_mem_map, Finset.mem_coe] using hBm y)
      (vals_lt B) (hBn.map Fin.val_injective) (fun y hy => (hv.2.2.2.1 hy).2)
  obtain ⟨s4, t4, hex4, ht4, hst4, hen4, hent4⟩ := replRebuildProg_exec (w := w)
    a_bd a.st a.en a.ent A R hbdA hst hen hent h23 h24 h34 (Ne.symm h2b) (Ne.symm h3b) hadj3
    (by rw [ha3 (A + 2) (by omega), ha2 (A + 2) (by omega) (by omega)]; exact hent1)
    ((ha3 a_bd hbr).trans ((ha2 a_bd (by omega) (by omega)).trans ((ha1 a_bd hbdA).trans hBa)))
    hblsmall (hBn.map Fin.val_injective) (vals_lt B)
    ((ha3 (A + 3) (by omega)).trans ((ha2 (A + 3) (by omega) (by omega)).trans hd1))
    ((ha3 (A + 9) (by omega)).trans ((ha2 (A + 9) (by omega) (by omega)).trans hb1))
    hN3 hfamily (by omega)
  have hex04 : Exec w (replacePrefixProg a a_del a_bd a_rep a_rec r_rec A R)
      s s4 (t1 + (t2 + (t3 + t4))) := .seq hex1 (.seq hex2 (.seq hex3 hex4))
  have hal4 : s4.arrs a.alive = List.ofFn (fun y : Fin N => if y ∈ S then 1 else 0) :=
    (replacePrefix_arrs_eq_of_lt a a_del a_bd a_rep a_rec r_rec A R hex04 hal h12 h13 h14 h1r).trans
      hinst.2.1
  have hdel4 : IsSetListAt a_del r.deleted s4 :=
    ⟨Dl, hDn, hDm, (replacePrefix_arrs_eq_of_lt a a_del a_bd a_rep a_rec r_rec A R hex04
      hdelA (Ne.symm h2d) (Ne.symm h3d) (Ne.symm h4d) hdr).trans hDa⟩
  obtain ⟨s5, t5, hex5, ht5, hal5, ha5, hr5⟩ := writeAll_alive_exec (w := w)
    a.alive a_del (R + 5) (R + 6) (R + 7) h1d (by omega) (by omega) (by omega) (by omega) (by omega)
    S S' r.deleted (by simpa only [ReplRecord.newVerts, hverts] using hS') hal4 hdel4
  have hex : Exec w (replaceBufProg a a_del a_bd a_rep a_rec r_rec A R) s s5
      (t1 + (t2 + (t3 + (t4 + t5)))) := .seq hex1 (.seq hex2 (.seq hex3 (.seq hex4 hex5)))
  refine ⟨s5, _, hex, ?_, replaceBuf_keeps a a_del a_bd a_rep a_rec r_rec A R hex, ?_,
    k - enc.length, ?_, ?_, ?_⟩
  · rw [he2'] at ht3
    omega
  · refine ⟨?_, hal5, ⟨fun x => replList lists dl bl x, ?_, hfamily⟩, ?_, ?_⟩
    · intro u v huv
      change (r.graph.Adj u v ∧ u ∉ r.deleted ∧ v ∉ r.deleted) ∨
        (u ∈ r.boundary ∧ v ∈ r.boundary ∧ u ≠ v) at huv
      have hnew : ∀ y, y ∈ r.verts → y ∉ r.deleted → y ∈ S' := by
        intro y hy hd
        change y ∈ (S' : Set (Fin N))
        rw [hS']
        exact ⟨hy, hd⟩
      rcases huv with ⟨huv, hu, hv'⟩ | ⟨hu, hv', -⟩
      · have hsupp := hinst.1 huv
        exact hnew u (by rw [hverts]; exact hsupp) hu
      · exact hnew u (hv.2.2.2.1 hu).1 (hv.2.2.2.1 hu).2
    · apply isListFamily_flatUpTo
      · rw [ha5 a.st (Ne.symm h12)]; exact hst4
      · rw [ha5 a.en (Ne.symm h13)]; exact hen4
      · rw [ha5 a.ent (Ne.symm h14)]; exact hent4
    · rw [ha5 a.ent (Ne.symm h14), hent4]
      exact length_flatUpTo_eq hfamily
    · rw [ha5 a.cyc (Ne.symm h15),
        repl_rebuild_arrs_eq_of_lt a_bd a.st a.en a.ent A R hex4 hcy
          (Ne.symm h25) (Ne.symm h35) (Ne.symm h45),
        ha3 a.cyc h5r, ha2 a.cyc (by omega) (by omega), ha1 a.cyc hcy]
      exact hinst.2.2.2.2
  · apply moveRecBuf (by simpa only [he2'] using hrec3)
    · rw [ha5 a_rec (Ne.symm h1r)]
      exact repl_rebuild_arrs_eq_of_lt a_bd a.st a.en a.ent A R hex4 hrecA (Ne.symm h2r) (Ne.symm h3r) (Ne.symm h4r)
    · rw [hr5 r_rec (by omega) (by omega) (by omega)]
      exact repl_rebuild_regs_eq_of_lt a_bd a.st a.en a.ent A R hex4 hrr
  · rw [ha5 a_rec (Ne.symm h1r), repl_rebuild_arrs_eq_of_lt a_bd a.st a.en a.ent A R hex4 hrecA (Ne.symm h2r) (Ne.symm h3r) (Ne.symm h4r),
      hreclen3, hreclen2]
  · omega

end GraphMinor.Compute.Crossing
