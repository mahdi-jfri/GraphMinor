module

public import GraphMinor.Compute.PlanarityRamOutgoingLoop
public import GraphMinor.Compute.PlanarityRamBucketBuild

/-!
# Scanning the global key array once

The outer loop reads each bucket head and calls the edge-chain traversal.
Its work is the number of buckets plus the total length of those chains.
The exact pending-list invariant connects consecutive bucket traversals
without charging any per-source scan of the key array.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The one global key range has length 2N+1. -/
def bucketLimitExpr : Expr := .op .add (.op .mul (.const 2) (.reg 30)) (.const 1)

/-- Visit the bucket at the current key. -/
def scanBucketProg : Cmd :=
  .seq (.assign 55 (.read Field.bucket.array (.reg 50))) outgoingBucketProg

/-- Advance once through the global bucket array. -/
def scanBucketsProg : Cmd := forUp 50 bucketLimitExpr scanBucketProg

/-- The key-range endpoint fits in a word, with all intermediate values. -/
theorem bucketLimitExpr_eval {N M w : ℕ} {s : State} (hN : s.regs 30 = N)
    (hw : 2 * (N + M + 1) < 2 ^ w) : bucketLimitExpr.eval w s = some (2 * N + 1) := by
  have h0 : N < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hp : 2 * N < 2 ^ w := by omega
  have hlast : 2 * N + 1 < 2 ^ w := by omega
  simp [bucketLimitExpr, Expr.eval, hN, BinOp.eval, BinOp.raw,
    checkWord_of_lt h0, checkWord_of_lt h1, checkWord_of_lt h2,
    checkWord_of_lt hp, checkWord_of_lt hlast]

/-- The edge-chain loop keeps both bucket arrays and the outer-loop registers. -/
theorem outgoingBucketProg_keeps {w t : ℕ} {s s' : State}
    (h : Exec w outgoingBucketProg s s' t) :
    s'.arrs Field.bucket.array = s.arrs Field.bucket.array ∧
    s'.arrs Field.bucketNext.array = s.arrs Field.bucketNext.array ∧
    s'.regs 30 = s.regs 30 ∧ s'.regs 50 = s.regs 50 := by
  refine ⟨h.arrs_eq_of_not_mem_writtenArrs ?_, h.arrs_eq_of_not_mem_writtenArrs ?_,
    h.regs_eq_of_not_mem_writtenRegs ?_, h.regs_eq_of_not_mem_writtenRegs ?_⟩ <;>
    simp [outgoingBucketProg, outgoingBucketStepProg, appendOutgoingProg,
      appendOutgoingLinksProg, Cmd.writtenArrs, Cmd.writtenRegs, Field.array]

/-- The remaining global scan computes the exact flattened traversal.
The bucket segment, its represented chains, valid distinct pending edges,
source ownership/freshness, current key and count, and word bound are its
only hypotheses. -/
theorem scanBucketsProg_refines {N M w : ℕ} (search : Search) (buckets : Array (List ℕ))
    (pending : List (List ℕ)) (start : ℕ) (outgoing : Array (List ℕ)) (s : State)
    (hs : SearchAt N M s search) (hb : SearchBounded N search) (hm : search.edges.size ≤ M)
    (hbs : BucketsAt N M s buckets) (ho : OutgoingReadyAt N M s outgoing)
    (howned : SourceOwned search.edges outgoing)
    (hN : s.regs 30 = N) (hstart : s.regs 50 = start)
    (hend : start + pending.length = buckets.size)
    (hsegment : ∀ j < pending.length, buckets[start + j]! = pending[j]!)
    (hvalid : ∀ i ∈ pending.flatten, i < search.edges.size)
    (hnd : pending.flatten.Nodup) (hfresh : OutgoingFresh N pending.flatten outgoing)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    ∃ s' t, Exec w scanBucketsProg s s' t ∧
      t ≤ 15 * pending.length + 33 * pending.flatten.length + 7 ∧
      SearchAt N M s' search ∧
      OutgoingReadyAt N M s' (distributeEdges search.edges pending.flatten outgoing) ∧
      SourceOwned search.edges (distributeEdges search.edges pending.flatten outgoing) ∧
      s'.regs 30 = N ∧ s'.regs 50 = 2 * N + 1 := by
  induction pending generalizing start outgoing s with
  | nil =>
    have hkey : start = 2 * N + 1 := by simpa only [List.length_nil, Nat.add_zero, hbs.1] using hend
    refine ⟨s, 7, ?_, by simp, hs, ho, howned, hN, hstart.trans hkey⟩
    apply Exec.while_false
    simp only [Expr.eval, hstart, hkey, bucketLimitExpr_eval hN hw,
      checkWord_of_lt (show 2 * N + 1 < 2 ^ w by omega), BinOp.eval, BinOp.raw,
      Nat.lt_irrefl, ↓reduceIte, checkWord_of_lt (show 0 < 2 ^ w by omega)]
  | cons ids pending ih =>
    have hkey : start < buckets.size := by simp only [List.length_cons] at hend; omega
    have hkeyN : start < 2 * N + 1 := by simpa only [hbs.1] using hkey
    have hhead : buckets[start]! = ids := by simpa using hsegment 0 (by simp)
    obtain ⟨p, hp, hc⟩ := hbs.2.2.2 start hkey
    rw [hhead] at hc
    have hidValid : ∀ i ∈ ids, i < search.edges.size := by
      intro i hi
      exact hvalid i (by simp [hi])
    have hpM := hc.pointer_le (fun i hi => Nat.lt_of_lt_of_le (hidValid i hi) hm)
    have hpw : p < 2 ^ w := by omega
    have hkw : start < 2 ^ w := by omega
    let s1 := s.setReg 55 p
    have hx1 : Exec w (.assign 55 (.read Field.bucket.array (.reg 50))) s s1 3 :=
      Exec.assign (read_reg_of_getElem? hp hstart hkw hpw)
    have hs1 : SearchAt N M s1 search := hs.setReg 55 p (by decide) (by decide)
    have ho1 : OutgoingReadyAt N M s1 outgoing := ho.setReg 55 p
    have hc1 : EdgeChain s1 Field.bucketNext.array p ids := hc.of_arr_eq rfl
    obtain ⟨s2, t2, hx2, ht2, hs2, ho2, howned2, hfresh2, hcursor2⟩ :=
      outgoingBucketProg_refines search ids pending.flatten outgoing s1 p hs1 hb hm ho1 howned hc1
        (by simp [s1]) hidValid (by simpa only [List.flatten_cons] using hnd)
        (by simpa only [List.flatten_cons] using hfresh) hw
    have hkeep := outgoingBucketProg_keeps hx2
    have hbs2 : BucketsAt N M s2 buckets := hbs.of_memory_eq hkeep.1 hkeep.2.1
    have hN2 : s2.regs 30 = N := hkeep.2.2.1.trans hN
    have hstart2 : s2.regs 50 = start := hkeep.2.2.2.trans hstart
    let s3 := s2.setReg 50 (start + 1)
    have hs3 : SearchAt N M s3 search := hs2.setReg 50 _ (by decide) (by decide)
    have hbs3 : BucketsAt N M s3 buckets := hbs2.setReg 50 _
    have ho3 : OutgoingReadyAt N M s3 (distributeEdges search.edges ids outgoing) := ho2.setReg 50 _
    have hN3 : s3.regs 30 = N := by simpa [s3] using hN2
    have hstart3 : s3.regs 50 = start + 1 := by simp [s3]
    have hend3 : start + 1 + pending.length = buckets.size := by simp only [List.length_cons] at hend; omega
    have hsegment3 : ∀ j < pending.length, buckets[start + 1 + j]! = pending[j]! := by
      intro j hj
      have he := hsegment (j + 1) (by simp; omega)
      simpa only [List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using he
    have hvalid3 : ∀ i ∈ pending.flatten, i < search.edges.size := by
      intro i hi; exact hvalid i (by simp [hi])
    have hnd3 : pending.flatten.Nodup := (List.nodup_append.mp (by simpa only [List.flatten_cons] using hnd)).2.1
    obtain ⟨s4, t4, hx4, ht4, hs4, ho4, howned4, hN4, hstart4⟩ :=
      ih (start + 1) (distributeEdges search.edges ids outgoing) s3 hs3 hbs3 ho3 howned2
        hN3 hstart3 hend3 hsegment3 hvalid3 hnd3 hfresh2
    have hone : 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 50) bucketLimitExpr).eval w s = some 1 := by
      simp only [Expr.eval, hstart, bucketLimitExpr_eval hN hw, checkWord_of_lt hkw]
      simp [BinOp.eval, BinOp.raw, hkeyN, checkWord_of_lt hone]
    have hx3 : Exec w (.assign 50 (.op .add (.reg 50) (.const 1))) s2 s3 4 := by
      apply Exec.assign
      simp [Expr.eval, hstart2, BinOp.eval, BinOp.raw, checkWord_of_lt hkw,
        checkWord_of_lt hone, checkWord_of_lt (show start + 1 < 2 ^ w by omega)]
    refine ⟨s4, 7 + (3 + t2 + 4) + t4,
      Exec.while_true hcond (by decide) (Exec.seq (Exec.seq hx1 hx2) hx3) hx4, ?_, hs4, ?_, ?_, hN4, hstart4⟩
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
    · simpa only [distributeEdges, List.flatten_cons, List.foldl_append] using ho4
    · simpa only [distributeEdges, List.flatten_cons, List.foldl_append] using howned4

end GraphMinor.Compute.PlanarityRam
