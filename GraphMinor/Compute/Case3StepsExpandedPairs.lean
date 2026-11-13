module

public import GraphMinor.Compute.Case3StepsParallelCopies

/-!
# The expanded edge prefix of a member record

The outer scan visits positive directed pairs in the compact graph's order.
For each pair it appends all copies in increasing copy number. The resulting
list is precisely the renamed edge list used by the branch record, and the
sum of multiplicities bounds both its length and the scan time.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Expanded flat triples of a pair list after changing its endpoint labels. -/
def case3ExpandedPairs {n : ℕ} (G : MultiDigraph n) (f : ℕ → ℕ)
    (pairs : List (Fin n × Fin n)) : List ℕ :=
  pairs.flatMap (fun p => case3ParallelCopies (f p.1.1) (f p.2.1) (G.edgeMult p.1 p.2))

/-- Expanded prefix length is three times its full edge multiplicity. -/
theorem case3ExpandedPairs_length {n : ℕ} (G : MultiDigraph n) (f : ℕ → ℕ)
    (pairs : List (Fin n × Fin n)) :
    (case3ExpandedPairs G f pairs).length = 3 * MultiDigraph.sumEdgeMult G pairs := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    simp only [case3ExpandedPairs, List.flatMap_cons, List.length_append,
      case3ParallelCopies_length, MultiDigraph.sumEdgeMult] at *
    omega

/-- Advancing the pair scan appends exactly the next whole parallel class. -/
theorem case3ExpandedPairs_take_succ {n : ℕ} (G : MultiDigraph n) (f : ℕ → ℕ)
    (k : ℕ) (hk : k < G.numActivePairs) :
    case3ExpandedPairs G f (G.activePairsList.take (k + 1)) =
      case3ExpandedPairs G f (G.activePairsList.take k) ++
        case3ParallelCopies (f (G.activePairsList[k]).1.1) (f (G.activePairsList[k]).2.1)
          (G.edgeMult (G.activePairsList[k]).1 (G.activePairsList[k]).2) := by
  rw [List.take_succ_eq_append_getElem hk]
  simp only [case3ExpandedPairs, List.flatMap_append, List.flatMap_singleton]

private theorem encEdgeTriples_flatMap {α : Type*} (l : List α) (F : α → List (ℕ × ℕ × ℕ)) :
    encEdgeTriples (l.flatMap F) = l.flatMap (fun x => encEdgeTriples (F x)) := by
  have happ (a b : List (ℕ × ℕ × ℕ)) : encEdgeTriples (a ++ b) = encEdgeTriples a ++ encEdgeTriples b := by
    induction a with
    | nil => rfl
    | cons e a ih => rcases e with ⟨u, v, k⟩; simp only [List.cons_append, encEdgeTriples, ih]
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, happ, ih]

/-- Completing the pair scan yields exactly the record's expanded edge
list, with endpoint renaming and copy numbers unchanged. -/
theorem case3ExpandedPairs_full {n : ℕ} (G : MultiDigraph n) (f : ℕ → ℕ) :
    case3ExpandedPairs G f G.activePairsList =
      encEdgeTriples (G.multiEdgeTriples.map (fun e => (f e.1, f e.2.1, e.2.2))) := by
  rw [MultiDigraph.multiEdgeTriples, List.map_flatMap, encEdgeTriples_flatMap]
  unfold case3ExpandedPairs
  apply List.flatMap_congr
  intro p _
  rw [List.map_map]
  rfl

/-- Multiplicity sums add over concatenated pair lists. -/
theorem case3SumEdgeMult_append {n : ℕ} (G : MultiDigraph n)
    (a b : List (Fin n × Fin n)) :
    MultiDigraph.sumEdgeMult G (a ++ b) = MultiDigraph.sumEdgeMult G a + MultiDigraph.sumEdgeMult G b := by
  rw [MultiDigraph.sumEdgeMult_eq_map_sum, MultiDigraph.sumEdgeMult_eq_map_sum,
    MultiDigraph.sumEdgeMult_eq_map_sum, List.map_append, List.sum_append]

/-- A prefix's summed multiplicity never exceeds the input edge count. -/
theorem case3PairPrefix_edges_le {n : ℕ} (G : MultiDigraph n) (k : ℕ) :
    MultiDigraph.sumEdgeMult G (G.activePairsList.take k) ≤ G.numEdges := by
  have hsum := G.sumEdgeMult_activePairsList
  conv_lhs at hsum => rw [← List.take_append_drop k G.activePairsList]
  rw [case3SumEdgeMult_append] at hsum
  omega

/-- The prefix count advances by the full multiplicity of the next pair. -/
theorem case3PairPrefix_edges_succ {n : ℕ} (G : MultiDigraph n)
    (k : ℕ) (hk : k < G.numActivePairs) :
    MultiDigraph.sumEdgeMult G (G.activePairsList.take (k + 1)) =
      MultiDigraph.sumEdgeMult G (G.activePairsList.take k) +
        G.edgeMult (G.activePairsList[k]).1 (G.activePairsList[k]).2 := by
  rw [List.take_succ_eq_append_getElem hk, case3SumEdgeMult_append]
  rfl

end GraphMinor.Compute
