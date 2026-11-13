module

public import GraphMinor.Compute.PlanarityRamBucketInit
public import GraphMinor.Compute.PlanarityRamRead

/-!
# Prepending an edge to its global bucket

The insertion in lines 226–228 of `docs/planarity/planarity_linear.py` reads the edge key and
current bucket head, then writes two pointers. Ownership of the unprocessed edge
ensures that its new link cannot change any previously built bucket.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- Insert edge i at the head of key k in the functional bucket array. -/
def pushBucket (buckets : Array (List ℕ)) (k i : ℕ) : Array (List ℕ) :=
  buckets.set! k (i :: buckets[k]!)

/-- The two pointer writes of a bucket insertion. -/
def pushBucketState (s : State) (k i old : ℕ) : State :=
  (s.writeArr Field.bucketNext.array i old).writeArr Field.bucket.array k (i + 1)

/-- The pointer to a chain is bounded whenever its edge identifiers are. -/
theorem EdgeChain.pointer_le {s : State} {a p L : ℕ} {xs : List ℕ}
    (h : EdgeChain s a p xs) (hb : ∀ i ∈ xs, i < L) : p ≤ L := by
  cases h with
  | nil => exact Nat.zero_le _
  | @cons i q rest hn ht => exact Nat.succ_le_of_lt (hb i (by simp))

/-- The pointer writes represent functional prepending. No new node is
allocated, and every old chain remains represented. -/
theorem BucketsAt.push {N M : ℕ} {s : State} {buckets : Array (List ℕ)}
    (h : BucketsAt N M s buckets) {k i p : ℕ}
    (hk : k < buckets.size) (hi : i < M)
    (hfresh : ∀ j < buckets.size, i ∉ buckets[j]!)
    (hp : (s.arrs Field.bucket.array)[k]? = some p) :
    BucketsAt N M (pushBucketState s k i p) (pushBucket buckets k i) := by
  rcases h with ⟨hsize, hheadlen, hnextlen, hchains⟩
  refine ⟨by simpa [pushBucket] using hsize,
    by simpa [pushBucketState, Field.array] using hheadlen,
    by simpa [pushBucketState, Field.array] using hnextlen, ?_⟩
  intro j hj
  have hj' : j < buckets.size := by simpa [pushBucket] using hj
  obtain ⟨q, hq, hc⟩ := hchains j hj'
  by_cases he : j = k
  · subst j
    have hqp : q = p := Option.some.inj (hq.symm.trans hp)
    subst q
    refine ⟨i + 1, ?_, ?_⟩
    · have hslot : k < (s.arrs 45).length := by change k < (s.arrs Field.bucket.array).length; omega
      simp [pushBucketState, Field.array, hslot]
    · have hnew := hc.prepend (hfresh k hk) (hnextlen.symm ▸ hi)
      have htransport := hnew.of_arr_eq (show
        (pushBucketState s k i p).arrs Field.bucketNext.array =
        (s.writeArr Field.bucketNext.array i p).arrs Field.bucketNext.array by
          simp [pushBucketState, Field.array])
      simpa only [pushBucket, Array.getElem!_set!_self buckets k (i :: buckets[k]!) hk] using htransport
  · refine ⟨q, ?_, ?_⟩
    · simpa only [pushBucketState, State.writeArr_arrs_self, State.writeArr_arrs_ne _ _ _
        (show Field.bucket.array ≠ Field.bucketNext.array by decide),
        List.getElem?_set, ite_eq_right (Ne.symm he)] using hq
    · have hnew := (hc.write_other (hfresh j hj')).of_arr_eq (show
        (pushBucketState s k i p).arrs Field.bucketNext.array =
        (s.writeArr Field.bucketNext.array i p).arrs Field.bucketNext.array by
          simp [pushBucketState, Field.array])
      simpa only [pushBucket, Array.getElem!_set!_ne buckets k j (i :: buckets[k]!) (Ne.symm he)] using hnew

/-- The actual insertion command, with the edge index in register 51.
Registers 52 and 53 hold its key and the old bucket head. -/
def pushBucketProg : Cmd :=
  .seq (.assign 52 (.read Field.key.array (.reg 51)))
    (.seq (.assign 53 (.read Field.bucket.array (.reg 52)))
      (.seq (.write Field.bucketNext.array (.reg 51) (.reg 53))
        (.write Field.bucket.array (.reg 52) (.op .add (.reg 51) (.const 1)))))

/-- The exact optional lookup supplies a RAM read, with explicit index and
value word bounds. -/
theorem read_reg_of_getElem? {s : State} {a r i v w : ℕ}
    (h : (s.arrs a)[i]? = some v) (hr : s.regs r = i)
    (hi : i < 2 ^ w) (hv : v < 2 ^ w) :
    (Expr.read a (.reg r)).eval w s = some v := by
  have hbound : i < (s.arrs a).length := List.getElem?_eq_some_iff.mp h |>.1
  have hval : (s.arrs a)[i] = v := by
    simpa only [List.getElem?_eq_getElem hbound, Option.some.injEq] using h
  simp only [Expr.eval, hr, checkWord_of_lt hi, hbound, ↓reduceDIte, hval, checkWord_of_lt hv]

/-- Each bucket insertion executes in fourteen steps. The hypotheses are
local data representation, freshness, valid edge/key slots, the index
register, and bounds on the words read or written. -/
theorem pushBucketProg_refines {N M w : ℕ} {s : State} {search : LRPlanarity.Search}
    {buckets : Array (List ℕ)} {i : ℕ}
    (hsearch : SearchAt N M s search) (hb : BucketsAt N M s buckets)
    (hi : i < search.edges.size) (hiM : i < M) (hr : s.regs 51 = i)
    (hk : search.edges[i].key < buckets.size)
    (hfresh : ∀ j < buckets.size, i ∉ buckets[j]!)
    (hbounded : ∀ j < buckets.size, ∀ e ∈ buckets[j]!, e < M)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    ∃ s', Exec w pushBucketProg s s' 14 ∧
      BucketsAt N M s' (pushBucket buckets search.edges[i].key i) ∧
      SearchAt N M s' search := by
  let k := search.edges[i].key
  have hkw : k < 2 ^ w := by have := hb.1; omega
  have hiw : i < 2 ^ w := by omega
  obtain ⟨p, hp, hc⟩ := hb.2.2.2 k hk
  have hpM := hc.pointer_le (hbounded k hk)
  have hpw : p < 2 ^ w := by omega
  let s1 := s.setReg 52 k
  let s2 := s1.setReg 53 p
  let s3 := s2.writeArr Field.bucketNext.array i p
  let s4 := s3.writeArr Field.bucket.array k (i + 1)
  have hx1 : Exec w (.assign 52 (.read Field.key.array (.reg 51))) s s1 3 :=
    Exec.assign (hsearch.read_key hi hr hiw hkw)
  have hx2 : Exec w (.assign 53 (.read Field.bucket.array (.reg 52))) s1 s2 3 :=
    Exec.assign (read_reg_of_getElem? hp (by simp [s1]) hkw hpw)
  have hx3 : Exec w (.write Field.bucketNext.array (.reg 51) (.reg 53)) s2 s3 3 :=
    Exec.write (by simp [Expr.eval, s2, s1, hr, checkWord_of_lt hiw])
      (by simp [Expr.eval, s2, checkWord_of_lt hpw]) (by simpa [s2, s1, hb.2.2.1] using hiM)
  have hipw : i + 1 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hx4 : Exec w (.write Field.bucket.array (.reg 52)
      (.op .add (.reg 51) (.const 1))) s3 s4 5 :=
    Exec.write (by simp [Expr.eval, s3, s2, s1, checkWord_of_lt hkw])
      (by simp [Expr.eval, s3, s2, s1, hr, checkWord_of_lt hiw,
        checkWord_of_lt hone, BinOp.eval, BinOp.raw, checkWord_of_lt hipw])
      (by
        change k < (s.arrs Field.bucket.array).length
        rw [hb.2.1, ← hb.1]
        exact hk)
  have hb2 : BucketsAt N M s2 buckets := by
    refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_⟩
    intro j hj
    obtain ⟨q, hq, hchain⟩ := hb.2.2.2 j hj
    exact ⟨q, hq, hchain.of_arr_eq rfl⟩
  have hp2 : (s2.arrs Field.bucket.array)[k]? = some p := hp
  refine ⟨s4, Exec.seq hx1 (Exec.seq hx2 (Exec.seq hx3 hx4)),
    hb2.push hk hiM hfresh hp2, ?_⟩
  apply hsearch.of_memory_eq
  · simp [s4, s3, s2, s1]
  · simp [s4, s3, s2, s1]
  · intro a ha
    have h45 : a ≠ Field.bucket.array := Nat.ne_of_lt ha
    have h46 : a ≠ Field.bucketNext.array := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
    simp [s4, s3, s2, s1, h45, h46]

end GraphMinor.Compute.PlanarityRam
