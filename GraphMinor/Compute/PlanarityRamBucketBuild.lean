module

public import GraphMinor.Compute.PlanarityRamBucketContents
public import GraphMinor.Compute.Logic

/-!
# The complete global bucket insertion loop

Each loop iteration inserts one fresh edge identifier in fourteen steps.
The exact filtered-range invariant proves freshness of every next edge.
There are as many iterations as live search records, with no scan of the
key range inside the insertion loop.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Bucket representation depends only on the two bucket arrays. -/
theorem BucketsAt.of_memory_eq {N M : ℕ} {s s' : State} {buckets : Array (List ℕ)}
    (h : BucketsAt N M s buckets)
    (hh : s'.arrs Field.bucket.array = s.arrs Field.bucket.array)
    (hn : s'.arrs Field.bucketNext.array = s.arrs Field.bucketNext.array) :
    BucketsAt N M s' buckets := by
  refine ⟨h.1, by simpa only [hh] using h.2.1,
    by simpa only [hn] using h.2.2.1, ?_⟩
  intro k hk
  obtain ⟨p, hp, hc⟩ := h.2.2.2 k hk
  exact ⟨p, by simpa only [hh] using hp, hc.of_arr_eq hn⟩

/-- Counter assignments do not change bucket representation. -/
theorem BucketsAt.setReg {N M : ℕ} {s : State} {buckets : Array (List ℕ)}
    (h : BucketsAt N M s buckets) (r v : ℕ) : BucketsAt N M (s.setReg r v) buckets :=
  h.of_memory_eq rfl rfl

/-- The entire unprocessed interval is inserted in linear time. All
hypotheses concern current data, current counter, capacities and words. -/
theorem fillBucketsProg_refines {N M w : ℕ} (search : Search) (start : ℕ)
    (buckets : Array (List ℕ)) (s : State)
    (hstart : start ≤ search.edges.size) (hreg : s.regs 51 = start)
    (hs : SearchAt N M s search) (hb : SearchBounded N search)
    (hm : search.edges.size ≤ M) (hbs : BucketsAt N M s buckets)
    (hc : BucketContents search.edges start buckets)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    ∃ s' t,
      Exec w (forUp 51 (.reg 37) pushBucketProg) s s' t ∧
      t ≤ 21 * (search.edges.size - start) + 3 ∧
      SearchAt N M s' search ∧
      BucketsAt N M s'
        (fillBuckets search.edges (List.range' start (search.edges.size - start)) buckets) ∧
      BucketContents search.edges search.edges.size
        (fillBuckets search.edges (List.range' start (search.edges.size - start)) buckets) ∧
      s'.regs 51 = search.edges.size := by
  induction hd : search.edges.size - start generalizing start buckets s with
  | zero =>
    have heq : start = search.edges.size := by omega
    refine ⟨s, 3, ?_, by simp, hs, ?_, ?_, hreg.trans heq⟩
    · apply Exec.while_false
      simp [Expr.eval, hreg, heq, hs.2.2.2.1, BinOp.eval, BinOp.raw,
        checkWord_of_lt (show search.edges.size < 2 ^ w by omega),
        checkWord_of_lt (show 0 < 2 ^ w by omega)]
    · simpa [fillBuckets] using hbs
    · simpa [fillBuckets, heq] using hc
  | succ remaining ih =>
    have hlt : start < search.edges.size := by omega
    have hkey := (hb.2.2.2.2.2.2 start hlt).2.2.2.2
    have hkey' : search.edges[start].key ≤ 2 * N := by
      simpa only [getElem!_pos search.edges start hlt] using hkey
    have hk : search.edges[start].key < buckets.size := by rw [hbs.1]; omega
    have hkbang : search.edges[start]!.key < buckets.size := by
      simpa only [getElem!_pos search.edges start hlt] using hk
    have hfresh : ∀ j < buckets.size, start ∉ buckets[j]! := by
      intro j hj hi
      have := ((hc.mem_iff hj).mp hi).1
      omega
    have hbounded : ∀ j < buckets.size, ∀ e ∈ buckets[j]!, e < M := by
      intro j hj e he
      have := ((hc.mem_iff hj).mp he).1
      omega
    obtain ⟨s1, hx1, hbs1, hs1⟩ :=
      pushBucketProg_refines hs hbs hlt (by omega) hreg hk hfresh hbounded hw
    have hr1 : s1.regs 51 = start :=
      (hx1.regs_eq_of_not_mem_writtenRegs (by simp [pushBucketProg, Cmd.writtenRegs])).trans hreg
    let bs1 := pushBucket buckets search.edges[start].key start
    have hc1 : BucketContents search.edges (start + 1) bs1 := by
      simpa only [getElem!_pos search.edges start hlt] using hc.push hkbang
    let s2 := s1.setReg 51 (start + 1)
    have hs2 : SearchAt N M s2 search := hs1.setReg 51 _ (by decide) (by decide)
    have hbs2 : BucketsAt N M s2 bs1 := hbs1.setReg 51 _
    have hsreg : s2.regs 51 = start + 1 := by simp [s2]
    have hnext : search.edges.size - (start + 1) = remaining := by omega
    obtain ⟨s3, t3, hx3, ht3, hs3, hbs3, hc3, hr3⟩ :=
      ih (start + 1) bs1 s2 (by omega) hsreg hs2 hbs2 hc1 hnext
    have hsw : start < 2 ^ w := by omega
    have hmw : search.edges.size < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 51) (.reg 37)).eval w s = some 1 := by
      simp [Expr.eval, hreg, hs.2.2.2.1, BinOp.eval, BinOp.raw, hlt,
        checkWord_of_lt hsw, checkWord_of_lt hmw, checkWord_of_lt hone]
    have hx2 : Exec w (.assign 51 (.op .add (.reg 51) (.const 1))) s1 s2 4 := by
      apply Exec.assign
      simp [Expr.eval, hr1, BinOp.eval, BinOp.raw, checkWord_of_lt hsw,
        checkWord_of_lt hone, checkWord_of_lt (show start + 1 < 2 ^ w by omega)]
    refine ⟨s3, 3 + (14 + 4) + t3,
      Exec.while_true hcond (by decide) (Exec.seq hx1 hx2) hx3, by omega, hs3, ?_, ?_, hr3⟩
    · simpa only [List.range'_succ, fillBuckets_cons, getElem!_pos search.edges start hlt] using hbs3
    · simpa only [List.range'_succ, fillBuckets_cons, getElem!_pos search.edges start hlt] using hc3

end GraphMinor.Compute.PlanarityRam
