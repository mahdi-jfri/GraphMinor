module

public import GraphMinor.Compute.PlanarityRamBucketChain
public import GraphMinor.Compute.PlanarityRamInit

/-!
# Allocating the global buckets and outgoing links

The five arrays of lines 224–231 of `docs/planarity/planarity_linear.py` have capacities
determined by N and the adjacency-entry bound M. Allocating them once clears every head and link
word. The existing search representation is unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- The five arrays allocated before the global bucket pass. -/
def bucketFields : List Field :=
  [.bucket, .bucketNext, .outgoingFirst, .outgoingLast, .outgoingNext]

/-- Bucket lists, with their heads in the global key array. -/
def BucketsAt (N M : ℕ) (s : State) (buckets : Array (List ℕ)) : Prop :=
  buckets.size = 2 * N + 1 ∧
  (s.arrs Field.bucket.array).length = 2 * N + 1 ∧
  (s.arrs Field.bucketNext.array).length = M ∧
  ∀ k < buckets.size, ∃ p, (s.arrs Field.bucket.array)[k]? = some p ∧
    EdgeChain s Field.bucketNext.array p buckets[k]!

/-- The outgoing heads and tails are allocated, and no edge has yet been
appended. All next pointers are zero, including unprocessed edge slots. -/
def EmptyOutgoingAt (N M : ℕ) (s : State) : Prop :=
  s.arrs Field.outgoingFirst.array = List.replicate N 0 ∧
  s.arrs Field.outgoingLast.array = List.replicate N 0 ∧
  s.arrs Field.outgoingNext.array = List.replicate M 0

/-- Memory transport for the search uses only its two counters and the
arrays through the postorder array. -/
theorem SearchAt.of_memory_eq {N M : ℕ} {s s' : State} {q : LRPlanarity.Search}
    (h : SearchAt N M s q) (hr37 : s'.regs 37 = s.regs 37)
    (hr39 : s'.regs 39 = s.regs 39)
    (ha : ∀ a < 45, s'.arrs a = s.arrs a) : SearchAt N M s' q := by
  rcases h with ⟨hd, hp, hpe, hc, ho, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  refine ⟨hd, hp, hpe, hr37.trans hc, hr39.trans ho, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h1.of_arr_eq (ha _ (by decide))
  · exact h2.of_arr_eq (ha _ (by decide))
  · exact h3.of_arr_eq (ha _ (by decide))
  · exact h4.of_arr_eq (ha _ (by decide))
  · exact h5.of_arr_eq (ha _ (by decide))
  · exact h6.of_arr_eq (ha _ (by decide))
  · exact h7.of_arr_eq (ha _ (by decide))
  · exact h8.of_arr_eq (ha _ (by decide))
  · exact h9.of_arr_eq (ha _ (by decide))
  · exact h10.of_arr_eq (ha _ (by decide))

/-- Bucket allocation leaves all existing search data intact. -/
theorem SearchAt.allocate_buckets {N M : ℕ} {s : State} {q : LRPlanarity.Search}
    (h : SearchAt N M s q) : SearchAt N M (allocatedState N M bucketFields s) q := by
  apply h.of_memory_eq
  · exact congrFun (allocatedState_regs N M bucketFields s) 37
  · exact congrFun (allocatedState_regs N M bucketFields s) 39
  · intro a ha
    apply allocatedState_arrs_of_not_mem
    intro f hf
    simp only [bucketFields, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;>
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))

/-- The initial global key array represents empty lists. -/
theorem allocated_bucketsAt (N M : ℕ) (s : State) :
    BucketsAt N M (allocatedState N M bucketFields s)
      (Array.replicate (2 * N + 1) ([] : List ℕ)) := by
  have hb := allocatedState_arrs_of_mem N M bucketFields s .bucket (by simp [bucketFields])
  have hn := allocatedState_arrs_of_mem N M bucketFields s .bucketNext (by simp [bucketFields])
  refine ⟨by simp, by simpa [Field.capacity] using congrArg List.length hb,
    by simpa [Field.capacity] using congrArg List.length hn, ?_⟩
  intro k hk
  have hk' : k < 2 * N + 1 := by simpa using hk
  refine ⟨0, ?_, ?_⟩
  · simp [hb, Field.capacity, hk']
  · simpa [getElem!_pos, hk'] using
      (EdgeChain.nil : EdgeChain (allocatedState N M bucketFields s) Field.bucketNext.array 0 [])

/-- All outgoing fields start zero after the same allocation. -/
theorem allocated_emptyOutgoingAt (N M : ℕ) (s : State) :
    EmptyOutgoingAt N M (allocatedState N M bucketFields s) := by
  constructor
  · exact allocatedState_arrs_of_mem N M bucketFields s .outgoingFirst (by simp [bucketFields])
  constructor
  · exact allocatedState_arrs_of_mem N M bucketFields s .outgoingLast (by simp [bucketFields])
  · exact allocatedState_arrs_of_mem N M bucketFields s .outgoingNext (by simp [bucketFields])

/-- In particular the initial outgoing lists satisfy the solver's encoding. -/
theorem EmptyOutgoingAt.outgoingAt {N M : ℕ} {s : State} (h : EmptyOutgoingAt N M s) :
    OutgoingAt N s (Array.replicate N ([] : List ℕ)) := by
  intro v hv
  refine ⟨0, ?_, ?_⟩
  · simp [h.1, hv]
  · simpa [getElem!_pos, hv] using (OutgoingChain.nil : OutgoingChain s 0 [])

/-- All five allocations together have linear cost and keep every register. -/
theorem allocateBuckets_exec (N M w : ℕ) (s : State)
    (hN : s.regs 30 = N) (hM : s.regs 36 = M)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    Exec w (allocateFields bucketFields) s (allocatedState N M bucketFields s)
      (allocationTime N M bucketFields) ∧
    allocationTime N M bucketFields ≤ 46 * (N + M + 1) := by
  refine ⟨allocateFields_exec bucketFields N M w s hN hM hw, ?_⟩
  have ht := allocationTime_le bucketFields N M
  have hlen : bucketFields.length = 5 := rfl
  rw [hlen] at ht
  omega

end GraphMinor.Compute.PlanarityRam
