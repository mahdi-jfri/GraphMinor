module

public import GraphMinor.Compute.PlanarityRamOutgoingFresh

/-!
# Traversing one bucket's edge chain

The cursor reads the next bucket link before appending the current edge.
The outgoing writes cannot change the bucket links. Distinct pending
identifiers provide freshness throughout the loop, including identifiers
reserved for later buckets. Each visited edge costs at most 33 steps.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Read the next bucket link and append the current edge. -/
def outgoingBucketStepProg : Cmd :=
  .seq (.assign 51 (.op .sub (.reg 55) (.const 1)))
    (.seq (.assign 55 (.read Field.bucketNext.array (.reg 51))) appendOutgoingProg)

/-- Follow a bucket's null-terminated chain. -/
def outgoingBucketProg : Cmd := .while (.reg 55) outgoingBucketStepProg

/-- The append program leaves the bucket-link array and cursor unchanged. -/
theorem appendOutgoingProg_bucket_keep {w t : ℕ} {s s' : State}
    (h : Exec w appendOutgoingProg s s' t) :
    s'.arrs Field.bucketNext.array = s.arrs Field.bucketNext.array ∧ s'.regs 55 = s.regs 55 := by
  constructor
  · apply h.arrs_eq_of_not_mem_writtenArrs
    simp [appendOutgoingProg, appendOutgoingLinksProg, Cmd.writtenArrs, Field.array]
  · apply h.regs_eq_of_not_mem_writtenRegs
    simp [appendOutgoingProg, appendOutgoingLinksProg, Cmd.writtenRegs]

/-- The inner bucket traversal computes the exact source-list fold and
keeps future identifiers fresh. Hypotheses concern the represented input
chain and source lists, valid distinct pending identifiers, and word size. -/
theorem outgoingBucketProg_refines {N M w : ℕ} (search : Search) (ids future : List ℕ)
    (outgoing : Array (List ℕ)) (s : State) (p : ℕ)
    (hs : SearchAt N M s search) (hb : SearchBounded N search)
    (hm : search.edges.size ≤ M) (ho : OutgoingReadyAt N M s outgoing)
    (howned : SourceOwned search.edges outgoing)
    (hchain : EdgeChain s Field.bucketNext.array p ids) (hcursor : s.regs 55 = p)
    (hvalid : ∀ i ∈ ids, i < search.edges.size)
    (hnd : (ids ++ future).Nodup) (hfresh : OutgoingFresh N (ids ++ future) outgoing)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    ∃ s' t, Exec w outgoingBucketProg s s' t ∧ t ≤ 33 * ids.length + 1 ∧
      SearchAt N M s' search ∧
      OutgoingReadyAt N M s' (distributeEdges search.edges ids outgoing) ∧
      SourceOwned search.edges (distributeEdges search.edges ids outgoing) ∧
      OutgoingFresh N future (distributeEdges search.edges ids outgoing) ∧ s'.regs 55 = 0 := by
  induction ids generalizing outgoing s p with
  | nil =>
    have hpzero := EdgeChain.nil_iff.mp hchain
    refine ⟨s, 1, ?_, by simp, hs, ho, howned, ?_, hcursor.trans hpzero⟩
    · apply Exec.while_false
      simp [Expr.eval, hcursor, hpzero, checkWord_of_lt (show 0 < 2 ^ w by omega)]
    · simpa only [List.nil_append, distributeEdges, List.foldl_nil] using hfresh
  | cons i ids ih =>
    obtain ⟨hpi, q, hnext, htail⟩ := EdgeChain.cons_iff.mp hchain
    have hi := hvalid i (by simp)
    have hiM : i < M := Nat.lt_of_lt_of_le hi hm
    have hiw : i < 2 ^ w := by omega
    have hpw : p < 2 ^ w := by omega
    have hqw : q < 2 ^ w := by
      have hqM := htail.pointer_le (by
        intro j hj
        exact Nat.lt_of_lt_of_le (hvalid j (by simp [hj])) hm)
      omega
    have hone : 1 < 2 ^ w := by omega
    let s1 := s.setReg 51 i
    let s2 := s1.setReg 55 q
    have hx1 : Exec w (.assign 51 (.op .sub (.reg 55) (.const 1))) s s1 4 := by
      apply Exec.assign
      simp [Expr.eval, hcursor, hpi, BinOp.eval, BinOp.raw,
        checkWord_of_lt (show i + 1 < 2 ^ w by omega), checkWord_of_lt hone, checkWord_of_lt hiw]
    have hx2 : Exec w (.assign 55 (.read Field.bucketNext.array (.reg 51))) s1 s2 3 :=
      Exec.assign (read_reg_of_getElem? hnext (by simp [s1]) hiw hqw)
    have hs2 : SearchAt N M s2 search := (hs.setReg 51 i (by decide) (by decide)).setReg 55 q (by decide) (by decide)
    have ho2 : OutgoingReadyAt N M s2 outgoing := (ho.setReg 51 i).setReg 55 q
    obtain ⟨s3, t3, hx3, ht3, hs3, ho3⟩ := appendOutgoingProg_refines hs2 hb ho2 howned
      hi hiM (by simp [s2, s1]) (hfresh i (by simp)) hw
    have hkeep := appendOutgoingProg_bucket_keep hx3
    have htail3 : EdgeChain s3 Field.bucketNext.array q ids :=
      htail.of_arr_eq hkeep.1
    have hcursor3 : s3.regs 55 = q := by simpa [s2] using hkeep.2
    have hv : search.edges[i]!.source < outgoing.size := by
      rw [ho.1]
      exact (hb.2.2.2.2.2.2 i hi).1
    have howned3 := howned.prepend i hv
    have hnd3 : (ids ++ future).Nodup := (List.nodup_cons.mp hnd).2
    have hfresh3 : OutgoingFresh N (ids ++ future) (prependSource search.edges outgoing i) :=
      hfresh.prepend hnd hv
    obtain ⟨s4, t4, hx4, ht4, hs4, ho4, howned4, hfresh4, hcursor4⟩ :=
      ih (prependSource search.edges outgoing i) s3 q hs3 ho3 howned3 htail3 hcursor3
        (fun j hj => hvalid j (by simp [hj])) hnd3 hfresh3
    have hcond : (Expr.reg 55).eval w s = some p := by
      simp [Expr.eval, hcursor, checkWord_of_lt hpw]
    refine ⟨s4, 1 + (4 + (3 + t3)) + t4,
      Exec.while_true hcond (by omega) (Exec.seq hx1 (Exec.seq hx2 hx3)) hx4,
      by simp only [List.length_cons]; omega, hs4, ho4, howned4, hfresh4, hcursor4⟩

end GraphMinor.Compute.PlanarityRam
