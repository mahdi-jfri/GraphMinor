module

public import GraphMinor.Compute.PlanarityRamBucketPush
import Init.Data.Range.Lemmas

/-!
# The two folds of the functional bucket pass

The first fold prepends every edge to its key bucket. The second scans
those buckets in array order and prepends to the source lists. Reversing
each source list gives exactly the append order used by the RAM program.
These equations expose the loops without changing their traversal order.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The global insertion loop on an explicit sequence of edge identifiers. -/
def fillBuckets (edges : Array EdgeRecord) (ids : List ℕ) (buckets : Array (List ℕ)) :
    Array (List ℕ) :=
  ids.foldl (fun bs i => pushBucket bs edges[i]!.key i) buckets

/-- One source-list prepend in the specification. -/
def prependSource (edges : Array EdgeRecord) (outgoing : Array (List ℕ)) (i : ℕ) :
    Array (List ℕ) :=
  outgoing.set! edges[i]!.source (i :: outgoing[edges[i]!.source]!)

/-- The source-list loop before the final per-source reversal. -/
def distributeEdges (edges : Array EdgeRecord) (ids : List ℕ) (outgoing : Array (List ℕ)) :
    Array (List ℕ) := ids.foldl (prependSource edges) outgoing

/-- The insertion loop processes its first edge and then the remaining list. -/
theorem fillBuckets_cons (edges : Array EdgeRecord) (i : ℕ) (ids : List ℕ)
    (buckets : Array (List ℕ)) :
    fillBuckets edges (i :: ids) buckets =
      fillBuckets edges ids (pushBucket buckets edges[i]!.key i) := rfl

/-- The source loop has the same explicit-list recursion. -/
theorem distributeEdges_cons (edges : Array EdgeRecord) (i : ℕ) (ids : List ℕ)
    (outgoing : Array (List ℕ)) :
    distributeEdges edges (i :: ids) outgoing =
      distributeEdges edges ids (prependSource edges outgoing i) := rfl

/-- Bucket insertion never changes the number of buckets. -/
theorem fillBuckets_size (edges : Array EdgeRecord) (ids : List ℕ)
    (buckets : Array (List ℕ)) : (fillBuckets edges ids buckets).size = buckets.size := by
  induction ids generalizing buckets with
  | nil => rfl
  | cons i ids ih => simpa only [fillBuckets_cons, pushBucket, Array.size_set!] using
        (ih (pushBucket buckets edges[i]!.key i))

/-- Source insertion never changes the number of source lists. -/
theorem distributeEdges_size (edges : Array EdgeRecord) (ids : List ℕ)
    (outgoing : Array (List ℕ)) : (distributeEdges edges ids outgoing).size = outgoing.size := by
  induction ids generalizing outgoing with
  | nil => rfl
  | cons i ids ih => simpa only [distributeEdges_cons, prependSource, Array.size_set!] using
        (ih (prependSource edges outgoing i))

/-- The frozen functional bucket pass is exactly global insertion followed
by traversal of all bucket members and final source-list reversal. -/
theorem bucketOrder_eq_folds (N : ℕ) (edges : Array EdgeRecord) :
    bucketOrder N edges =
      (distributeEdges edges
        (fillBuckets edges (List.range edges.size) (Array.replicate (2 * N + 1) [])).toList.flatten
        (Array.replicate N [])).map List.reverse := by
  simp only [bucketOrder, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range', List.forIn_pure_yield_eq_foldl, Id.run_bind, pure_bind]
  rw [← Array.forIn_toList]
  simp only [List.forIn_pure_yield_eq_foldl]
  rw [← List.foldl_flatten]
  rfl

end GraphMinor.Compute.PlanarityRam
