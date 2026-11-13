module

public import GraphMinor.Compute.CrossingOpsReplEnc

/-!
# The body of the replacement record encoder

The encoder writes the header, scans the recorded vertices, patches the number of pairs,
and appends the length of the body. The input source array contains the recorded component
followed by the boundary. Its marks allow each adjacency-list scan to test the other endpoint.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Fill an existing buffer with the replacement record and its closing length word. -/
def replRecordBodyProg (a_bd a_rep a_rb a_s a_e a_ent a_mark buf R : ℕ) : Cmd :=
  .seq (replHeaderProg a_bd a_rep buf R)
    (.seq (emitPairsProg a_rb a_s a_e a_ent a_mark buf R)
      (.seq (patchPairCountProg buf (R + 4) (R + 9) (R + 10))
        (emitLengthProg buf (R + 4))))

/-- The list encoded by the replacement record body. -/
def replRecordWords {N : ℕ} (lists : Fin N → List ℕ) (bd rep : List ℕ) : List ℕ :=
  let pairs := (rep ++ bd).flatMap (pairsOf lists (rep ++ bd))
  withLength (replHead bd rep ++ (pairs.length / 2) :: pairs)

/-- The encoder uses linear time, given distinct recorded vertices, their adjacency lists,
marks for those vertices, sufficient buffer capacity, and the stated word bound. -/
theorem replRecordBodyProg_exec {w N : ℕ} (a_bd a_rep a_rb a_s a_e a_ent a_mark buf R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {bd rep : List ℕ}
    {s : State} {k : ℕ}
    (hbd : a_bd ≠ buf) (hrep : a_rep ≠ buf) (hrb : a_rb ≠ buf)
    (hs : a_s ≠ buf) (he : a_e ≠ buf) (hent : a_ent ≠ buf) (hm : a_mark ≠ buf)
    (hB : s.arrs a_bd = bd) (hR : s.arrs a_rep = rep) (hRB : s.arrs a_rb = rep ++ bd)
    (hnd : (rep ++ bd).Nodup) (hlt : ∀ x ∈ rep ++ bd, x < N)
    (hadj : IsAdjList G a_s a_e a_ent lists s)
    (hmark : s.arrs a_mark = setAt (List.replicate N 0) (rep ++ bd) 1)
    (hb : IsBuf buf (R + 4) [] k s)
    (hk : bd.length + rep.length +
      ((rep ++ bd).flatMap (pairsOf lists (rep ++ bd))).length + 5 ≤ k)
    (hw : N + (s.arrs a_ent).length + k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (replRecordBodyProg a_bd a_rep a_rb a_s a_e a_ent a_mark buf R) s s' t ∧
      t ≤ 67 + 36 * N + 56 * G.edgeSet.ncard ∧
      IsBuf buf (R + 4) (replRecordWords lists bd rep)
        (k - (replRecordWords lists bd rep).length) s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) := by
  classical
  let pairs := (rep ++ bd).flatMap (pairsOf lists (rep ++ bd))
  change bd.length + rep.length + pairs.length + 5 ≤ k at hk
  have hlen : bd.length + rep.length ≤ N := by
    have := length_le_of_nodup_lt hnd hlt
    simp only [List.length_append] at this
    omega
  obtain ⟨s1, t1, hex1, ht1, hb1, hpos1, hstart1, ha1⟩ :=
    replHeaderProg_exec (w := w) a_bd a_rep buf R hbd hrep hB hR hb (by omega)
      (fun x hx => by have := hlt x (List.mem_append_right rep hx); omega)
      (fun x hx => by have := hlt x (List.mem_append_left bd hx); omega) (by omega)
  have hhead : (replHead bd rep).length = bd.length + rep.length + 3 := by
    simp [replHead]; omega
  have hadj1 := hadj.of_arrs_eq (ha1 a_s hs) (ha1 a_e he) (ha1 a_ent hent)
  obtain ⟨s2, t2, hex2, ht2, hb2, ha2, hr2⟩ := emitPairsProg_linear_exec (w := w)
    a_rb a_s a_e a_ent a_mark buf R hrb hs he hent hm
    ((ha1 a_rb hrb).trans hRB) hnd hlt hadj1
    ((ha1 a_mark hm).trans hmark) hb1 (by
      change pairs.length ≤ _
      omega)
    (by rw [ha1 a_ent hent]; simp only [List.length_append, List.length_singleton, List.length_nil, hhead]; omega)
  have hpos2 : s2.regs (R + 9) = (replHead bd rep).length :=
    (hr2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hpos1
  have hstart2 : s2.regs (R + 10) = (replHead bd rep).length + 1 :=
    (hr2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hstart1
  have hb2' : IsBuf buf (R + 4) (replHead bd rep ++ 0 :: pairs)
      (k - (bd.length + rep.length + 4) - pairs.length) s2 := by
    simpa only [List.append_assoc, List.singleton_append] using hb2
  obtain ⟨s3, hex3, hb3, ha3, hr3⟩ := patchPairCountProg_exec (w := w) buf (R + 4) (R + 9) (R + 10)
    hb2' hpos2 hstart2 (by rw [hhead]; omega)
  obtain ⟨s4, hex4, hb4, ha4, hr4⟩ := emitLengthProg_exec (w := w) buf (R + 4) hb3
    (by omega) (by simp only [List.length_append, List.length_cons, hhead]; omega)
  refine ⟨s4, t1 + (t2 + (7 + 7)), .seq hex1 (.seq hex2 (.seq hex3 hex4)), by omega, ?_,
    fun a ha => (ha4 a ha).trans ((ha3 a ha).trans ((ha2 a ha).trans (ha1 a ha)))⟩
  have hlength : (replRecordWords lists bd rep).length =
      bd.length + rep.length + pairs.length + 5 := by
    simp only [replRecordWords, withLength, List.length_append, List.length_cons,
      List.length_singleton, List.length_nil, hhead]
    dsimp only [pairs]
    omega
  rw [hlength]
  have hcap : k - (bd.length + rep.length + pairs.length + 5) =
      k - (bd.length + rep.length + 4) - pairs.length - 1 := by omega
  rw [hcap]
  exact hb4

/-- For a valid replacement, the emitted words are the required record encoding. -/
theorem isRecordEnc_replRecordWords {N : ℕ} {r : GraphMinor.Crossing.ReplRecord (Fin N)}
    {lists : Fin N → List ℕ} (h : IsAdjListFamily r.graph lists)
    {D : List (Fin N)} (hv : r.IsValid D) (B Rp : List (Fin N))
    (hBn : B.Nodup) (hBm : ∀ y, y ∈ B ↔ y ∈ r.boundary)
    (hRn : Rp.Nodup) (hRm : ∀ y, y ∈ Rp ↔ y ∈ r.rep) :
    IsRecordEnc (GraphMinor.Crossing.CrossRecord.repl r)
      (replRecordWords lists (B.map Fin.val) (Rp.map Fin.val)) := by
  simpa [replRecordWords, replHead, List.append_assoc] using
    isRecordEnc_repl_pairsOf h hv B Rp hBn hBm hRn hRm

end GraphMinor.Compute.Crossing
