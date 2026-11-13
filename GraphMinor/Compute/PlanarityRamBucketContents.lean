module

public import GraphMinor.Compute.PlanarityRamBucketFunction

/-!
# Ownership and total size of the global buckets

After inserting the first i edges, bucket k contains exactly those edge
identifiers below i with key k, in decreasing identifier order. This
invariant gives freshness for the next insertion, disjoint ownership for
the outgoing pass, and a bound on all bucket traversals together.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Exact contents of each bucket after the first count insertions. -/
def BucketContents (edges : Array EdgeRecord) (count : ℕ) (buckets : Array (List ℕ)) : Prop :=
  ∀ k < buckets.size,
    buckets[k]! = (List.range count).reverse.filter (fun i => edges[i]!.key == k)

/-- Empty buckets represent zero insertions. -/
theorem BucketContents.empty (edges : Array EdgeRecord) (capacity : ℕ) :
    BucketContents edges 0 (Array.replicate capacity []) := by
  intro k hk
  have hk' : k < capacity := by simpa using hk
  simp [getElem!_pos, hk']

/-- Inserting the next identifier preserves the exact decreasing order in
its bucket and leaves every other bucket unchanged. -/
theorem BucketContents.push {edges : Array EdgeRecord} {count : ℕ} {buckets : Array (List ℕ)}
    (h : BucketContents edges count buckets) (hk : edges[count]!.key < buckets.size) :
    BucketContents edges (count + 1) (pushBucket buckets edges[count]!.key count) := by
  intro k hkb
  have hkb' : k < buckets.size := by simpa [pushBucket] using hkb
  by_cases he : edges[count]!.key = k
  · subst k
    simp only [pushBucket, Array.getElem!_set!_self buckets _ _ hk,
      List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.filter_cons, beq_self_eq_true, ↓reduceIte]
    rw [h _ hk]
  · simp only [pushBucket, Array.getElem!_set!_ne buckets _ _ _ he,
      List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.filter_cons, beq_eq_false_iff_ne.mpr he]
    exact h k hkb'

/-- Every represented member is an already inserted edge with the bucket's key. -/
theorem BucketContents.mem_iff {edges : Array EdgeRecord} {count : ℕ} {buckets : Array (List ℕ)}
    (h : BucketContents edges count buckets) {k i : ℕ} (hk : k < buckets.size) :
    i ∈ buckets[k]! ↔ i < count ∧ edges[i]!.key = k := by
  rw [h k hk]
  simp

/-- Each bucket is free of repeated edge identifiers. -/
theorem BucketContents.nodup {edges : Array EdgeRecord} {count : ℕ} {buckets : Array (List ℕ)}
    (h : BucketContents edges count buckets) {k : ℕ} (hk : k < buckets.size) :
    buckets[k]!.Nodup := by
  rw [h k hk]
  exact List.Nodup.filter _ (List.nodup_reverse.mpr List.nodup_range)

/-- Distinct keys have disjoint edge ownership. -/
theorem BucketContents.disjoint {edges : Array EdgeRecord} {count : ℕ} {buckets : Array (List ℕ)}
    (h : BucketContents edges count buckets) {k j : ℕ}
    (hk : k < buckets.size) (hj : j < buckets.size) (hne : k ≠ j) :
    List.Disjoint buckets[k]! buckets[j]! := by
  rw [List.disjoint_left]
  intro i hi hjmem
  exact hne (((h.mem_iff hk).mp hi).2.symm.trans ((h.mem_iff hj).mp hjmem).2)

/-- No edge identifier occurs twice in the whole global traversal. -/
theorem BucketContents.flatten_nodup {edges : Array EdgeRecord} {count : ℕ} {buckets : Array (List ℕ)}
    (h : BucketContents edges count buckets) : buckets.toList.flatten.Nodup := by
  rw [List.nodup_flatten]
  constructor
  · intro xs hxs
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hxs
    have hkb : k < buckets.size := by simpa using hk
    have hx : buckets[k]! = xs := by simpa [getElem!_pos, hkb] using he
    rw [← hx]
    exact h.nodup hkb
  · rw [List.pairwise_iff_getElem]
    intro k j hk hj hkj
    have hkb : k < buckets.size := by simpa using hk
    have hjb : j < buckets.size := by simpa using hj
    simpa [getElem!_pos, hkb, hjb] using h.disjoint hkb hjb (Nat.ne_of_lt hkj)

/-- The global traversal has at most count edges. This bound charges all
bucket chains together, rather than charging a scan once per vertex. -/
theorem BucketContents.flatten_length_le {edges : Array EdgeRecord} {count : ℕ}
    {buckets : Array (List ℕ)} (h : BucketContents edges count buckets) :
    buckets.toList.flatten.length ≤ count := by
  have hsub : buckets.toList.flatten ⊆ List.range count := by
    intro i hi
    obtain ⟨xs, hxs, hix⟩ := List.mem_flatten.mp hi
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hxs
    have hkb : k < buckets.size := by simpa using hk
    have hx : buckets[k]! = xs := by simpa [getElem!_pos, hkb] using he
    rw [← hx] at hix
    exact List.mem_range.mpr ((h.mem_iff hkb).mp hix).1
  simpa using h.flatten_nodup.length_le_of_subset hsub

end GraphMinor.Compute.PlanarityRam
