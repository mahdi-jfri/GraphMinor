module

public import GraphMinor.Compute.Case3StepsActivePairOwners
public import GraphMinor.Compute.Case3StepsRoutedMember
public import GraphMinor.Compute.Case3StepsIndexedTriples
public import GraphMinor.Compute.Case3StepsBucketLists

/-!
# Ordered pair buckets encode precisely the routed multigraph member

The bucket indices are the canonical input indices filtered by owner. Reading
their triples in that order gives exactly the active-pair filter of the
routed member. Both the count header and every multiplicity word therefore
match its canonical multigraph encoding.
-/

public section

namespace GraphMinor.Compute

open Classical

private theorem bucket_pairs (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (label : ℕ) :
    (((List.finRange D.numActivePairs).filter
      (fun j => decide (case3ActivePairOwner x D Z j = label))).map
        (fun j => D.activePairsList[j.1])) =
      D.activePairsList.filter (fun p => decide (case3PairOwner x Z p.1 p.2 = label)) := by
  have hm : (List.finRange D.numActivePairs).map (fun j => D.activePairsList[j.1]) =
      D.activePairsList := List.map_get_finRange D.activePairsList
  have hf := congrArg (List.filter (fun p : Fin x.n × Fin x.n =>
    decide (case3PairOwner x Z p.1 p.2 = label))) hm
  rw [List.filter_map] at hf
  exact hf

private theorem flatTriples_map_indices {n : ℕ} (D : MultiDigraph n)
    (js : List (Fin D.numActivePairs)) :
    MultiDigraph.flatTriples D (js.map (fun j => D.activePairsList[j.1])) =
      js.flatMap (case3PairTriple D) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons, MultiDigraph.flatTriples, List.flatMap_cons,
      case3PairTriple, List.cons_append, List.nil_append]
    rw [ih]

/-- Bucket counts equal the number of positive pairs in the routed member. -/
theorem case3BucketIndices_length_eq_routed (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (label : ℕ) :
    (case3BucketIndices (case3ActivePairOwner x D Z) label 0).length =
      (case3RoutedMember x D Z label).numActivePairs := by
  change _ = (case3RoutedMember x D Z label).activePairsList.length
  rw [case3RoutedMember_activePairs, ← bucket_pairs x D Z label]
  simp only [case3BucketIndices, List.drop_zero, List.length_map]

/-- Bucket traversal copies exactly the routed member's ordered full input triples. -/
theorem case3IndexedTriples_bucket (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (label : ℕ) :
    case3IndexedTriples D (case3BucketIndices (case3ActivePairOwner x D Z) label 0) =
      MultiDigraph.flatTriples D
        (D.activePairsList.filter (fun p => decide (case3PairOwner x Z p.1 p.2 = label))) := by
  rw [← bucket_pairs x D Z label, flatTriples_map_indices]
  simp only [case3IndexedTriples, case3BucketIndices, List.drop_zero, List.flatMap_map]
  apply List.flatMap_congr
  intro j _
  exact case3EncodedPairTriple_eq D j

/-- The counted bucket buffer is the exact canonical routed-member encoding. -/
theorem case3BucketEncoding_eq (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (label : ℕ) :
    [x.n, (case3BucketIndices (case3ActivePairOwner x D Z) label 0).length] ++
      case3IndexedTriples D (case3BucketIndices (case3ActivePairOwner x D Z) label 0) =
      (case3RoutedMember x D Z label).enc := by
  rw [case3RoutedMember_enc, case3IndexedTriples_bucket]
  congr 2
  rw [case3BucketIndices_length_eq_routed, MultiDigraph.numActivePairs,
    case3RoutedMember_activePairs]

end GraphMinor.Compute
