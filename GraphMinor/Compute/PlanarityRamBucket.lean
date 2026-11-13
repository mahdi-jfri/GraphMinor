module

public import GraphMinor.Compute.PlanarityRamBucketScan

/-!
# The complete linear-time global bucket phase

The program allocates five fixed arenas, inserts each live edge once,
and scans each key and edge chain once. The resulting outgoing pointers
represent exactly `bucketOrder`, including the order of equal-key edges.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The entire bucket phase, using the DFS counters and field layout. -/
def bucketSortProg : Cmd :=
  .seq (allocateFields bucketFields)
    (.seq (.assign 51 (.const 0))
      (.seq (forUp 51 (.reg 37) pushBucketProg)
        (.seq (.assign 50 (.const 0)) scanBucketsProg)))

/-- Bucket insertion changes none of the outgoing arrays or input registers. -/
theorem fillBucketsProg_keeps {w t : ℕ} {s s' : State}
    (h : Exec w (forUp 51 (.reg 37) pushBucketProg) s s' t) :
    s'.arrs Field.outgoingFirst.array = s.arrs Field.outgoingFirst.array ∧
    s'.arrs Field.outgoingLast.array = s.arrs Field.outgoingLast.array ∧
    s'.arrs Field.outgoingNext.array = s.arrs Field.outgoingNext.array ∧
    s'.regs 30 = s.regs 30 := by
  refine ⟨h.arrs_eq_of_not_mem_writtenArrs ?_, h.arrs_eq_of_not_mem_writtenArrs ?_,
    h.arrs_eq_of_not_mem_writtenArrs ?_, h.regs_eq_of_not_mem_writtenRegs ?_⟩ <;>
    simp [forUp, pushBucketProg, Cmd.writtenRegs, Cmd.writtenArrs, Field.array]

/-- Preparation, insertion and the global traversal compute the solver's
exact outgoing lists in linear time. The hypotheses are the existing
search encoding and field bounds, incidence capacity, N/M header registers,
and a linear word bound. -/
theorem bucketSortProg_refines {N M w : ℕ} (search : Search) (s : State)
    (hs : SearchAt N M s search) (hb : SearchBounded N search) (hm : search.edges.size ≤ M)
    (hN : s.regs 30 = N) (hM : s.regs 36 = M)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    ∃ s' t, Exec w bucketSortProg s s' t ∧ t ≤ 150 * (N + M + 1) ∧
      SearchAt N M s' search ∧ OutgoingAt N s' (bucketOrder N search.edges) := by
  let s1 := allocatedState N M bucketFields s
  obtain ⟨hx1, ht1⟩ := allocateBuckets_exec N M w s hN hM hw
  have hs1 : SearchAt N M s1 search := hs.allocate_buckets
  have hbs1 := allocated_bucketsAt N M s
  have ho1 : OutgoingReadyAt N M s1 (Array.replicate N []) := (allocated_emptyOutgoingAt N M s).ready
  let s2 := s1.setReg 51 0
  have hs2 : SearchAt N M s2 search := hs1.setReg 51 0 (by decide) (by decide)
  have hbs2 := hbs1.setReg 51 0
  have hx2 : Exec w (.assign 51 (.const 0)) s1 s2 2 :=
    Exec.assign (checkWord_of_lt (by omega))
  obtain ⟨s3, t3, hx3, ht3, hs3, hbs3, hc3, hcounter3⟩ :=
    fillBucketsProg_refines search 0 (Array.replicate (2 * N + 1) []) s2 (Nat.zero_le _)
      (by simp [s2]) hs2 hb hm hbs2 (BucketContents.empty _ _) hw
  let buckets := fillBuckets search.edges (List.range search.edges.size) (Array.replicate (2 * N + 1) [])
  have hbs : BucketsAt N M s3 buckets := by
    simpa only [Nat.sub_zero, ← List.range_eq_range'] using hbs3
  have hc : BucketContents search.edges search.edges.size buckets := by
    simpa only [Nat.sub_zero, ← List.range_eq_range'] using hc3
  have hkeep := fillBucketsProg_keeps hx3
  have ho3 : OutgoingReadyAt N M s3 (Array.replicate N []) :=
    (ho1.setReg 51 0).of_memory_eq hkeep.1 hkeep.2.1 hkeep.2.2.1
  have hN3 : s3.regs 30 = N := hkeep.2.2.2.trans
    (by simpa [s2, s1, allocatedState_regs] using hN)
  let s4 := s3.setReg 50 0
  have hs4 : SearchAt N M s4 search := hs3.setReg 50 0 (by decide) (by decide)
  have hbs4 := hbs.setReg 50 0
  have ho4 := ho3.setReg 50 0
  have hN4 : s4.regs 30 = N := by simpa [s4] using hN3
  have hx4 : Exec w (.assign 50 (.const 0)) s3 s4 2 :=
    Exec.assign (checkWord_of_lt (by omega))
  have hvalid : ∀ i ∈ buckets.toList.flatten, i < search.edges.size := by
    intro i hi
    obtain ⟨xs, hxs, hix⟩ := List.mem_flatten.mp hi
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hxs
    have hkb : k < buckets.size := by simpa using hk
    have hx : buckets[k]! = xs := by simpa [getElem!_pos, hkb] using he
    rw [← hx] at hix
    exact ((hc.mem_iff hkb).mp hix).1
  obtain ⟨s5, t5, hx5, ht5, hs5, ho5, howned5, hN5, hkey5⟩ :=
    scanBucketsProg_refines search buckets buckets.toList 0 (Array.replicate N []) s4
      hs4 hb hm hbs4 ho4 (SourceOwned.empty _ _) hN4 (by simp [s4])
      (by simp) (by
        intro j hj
        have hj' : j < buckets.size := by simpa using hj
        simp [getElem!_pos, hj']) hvalid hc.flatten_nodup (OutgoingFresh.empty _ _) hw
  have ht3' : t3 ≤ 21 * M + 3 := by simp only [Nat.sub_zero] at ht3; omega
  have ht5' : t5 ≤ 15 * (2 * N + 1) + 33 * M + 7 := by
    have hlen := hc.flatten_length_le
    simp only [Array.length_toList, hbs.1] at ht5
    omega
  refine ⟨s5, allocationTime N M bucketFields + (2 + (t3 + (2 + t5))),
    Exec.seq hx1 (Exec.seq hx2 (Exec.seq hx3 (Exec.seq hx4 hx5))), by omega, hs5, ?_⟩
  rw [bucketOrder_eq_folds]
  exact ho5.outgoingAt

end GraphMinor.Compute.PlanarityRam
