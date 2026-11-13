module

public import GraphMinor.Compute.MultiDigraph

/-!
# The full triple of a stored positive pair

A stored record contains two endpoint labels and the complete multiplicity.
Splitting the input encoding at a pair index isolates these three words,
so a member can copy the record unchanged rather than expand its edges.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The complete endpoint and multiplicity record at a positive pair index. -/
def case3PairTriple {n : ℕ} (D : MultiDigraph n) (j : Fin D.numActivePairs) : List ℕ :=
  let p := D.activePairsList[j.1]
  [p.1.1, p.2.1, D.edgeMult p.1 p.2]

/-- Each positive pair record occupies three words. -/
theorem case3PairTriple_length {n : ℕ} (D : MultiDigraph n) (j : Fin D.numActivePairs) :
    (case3PairTriple D j).length = 3 := rfl

/-- Endpoint and full multiplicity words fit when vertices and edge count fit. -/
theorem case3PairTriple_words {n w : ℕ} (D : MultiDigraph n) (j : Fin D.numActivePairs)
    (hn : n < 2 ^ w) (he : D.numEdges < 2 ^ w) :
    ∀ z ∈ case3PairTriple D j, z < 2 ^ w := by
  intro z hz
  simp only [case3PairTriple, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact (D.activePairsList[j.1]).1.2.trans hn
  · exact (D.activePairsList[j.1]).2.2.trans hn
  · exact (D.edgeMult_le_numEdges _ _).trans_lt he

/-- Splitting the canonical input at one pair exposes exactly its full triple. -/
theorem case3PairTriple_enc_split {n : ℕ} (D : MultiDigraph n) (j : Fin D.numActivePairs) :
    D.enc =
      ([n, D.numActivePairs] ++ MultiDigraph.flatTriples D (D.activePairsList.take j.1)) ++
        case3PairTriple D j ++ MultiDigraph.flatTriples D (D.activePairsList.drop (j.1 + 1)) := by
  have hs : D.activePairsList = D.activePairsList.take j.1 ++
      D.activePairsList[j.1] :: D.activePairsList.drop (j.1 + 1) := by
    conv_lhs => rw [← List.take_append_drop j.1 D.activePairsList]
    rw [List.drop_eq_getElem_cons j.2]
    rfl
  unfold MultiDigraph.enc
  conv_lhs => rw [hs, MultiDigraph.flatTriples_append]
  simp only [MultiDigraph.flatTriples, case3PairTriple, List.append_assoc,
    List.cons_append, List.nil_append]

/-- The source prefix has the address used by the triple-copy program. -/
theorem case3PairTriple_prefix_length {n : ℕ} (D : MultiDigraph n) (j : Fin D.numActivePairs) :
    ([n, D.numActivePairs] ++ MultiDigraph.flatTriples D (D.activePairsList.take j.1)).length =
      2 + 3 * j.1 := by
  have hjle : j.1 ≤ D.activePairsList.length := j.2.le
  simp only [List.length_append, List.length_cons, List.length_nil,
    MultiDigraph.length_flatTriples, List.length_take, Nat.min_eq_left hjle]

end GraphMinor.Compute
