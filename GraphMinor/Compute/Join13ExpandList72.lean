module

public import GraphMinor.Compute.Join13Expand72
public import GraphMinor.Compute.Join13Read72

/-!
# The endpoint stream used by the (7.2) input wrapper

Expanding the active pairs in their input order gives exactly the individual
edge order of the caller's multigraph decomposition. These identities connect
the repetition loop to the core graph encoding.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Expand a list of endpoint pairs according to their multiplicities. -/
def expandedPairs72 {n : ℕ} (G : MultiDigraph n) (ps : List (Fin n × Fin n)) : List ℕ :=
  ps.flatMap (fun p => (List.replicate (G.edgeMult p.1 p.2) [p.1.1, p.2.1]).flatten)

/-- Two endpoint words are written for each individual edge. -/
theorem length_expandedPairs72 {n : ℕ} (G : MultiDigraph n) (ps : List (Fin n × Fin n)) :
    (expandedPairs72 G ps).length = 2 * G.sumEdgeMult ps := by
  induction ps with
  | nil => simp [expandedPairs72, MultiDigraph.sumEdgeMult]
  | cons p ps ih =>
    simp only [expandedPairs72, List.flatMap_cons, List.length_append] at ih ⊢
    simp only [List.length_flatten, List.map_replicate, List.length_cons, List.length_nil,
      List.sum_replicate, smul_eq_mul, MultiDigraph.sumEdgeMult, Nat.mul_add]
    omega

/-- The endpoint stream has the caller's exact edge order. -/
theorem endpointWords72_toMultiComputeDigraph {n : ℕ} (G : MultiDigraph n) :
    endpointWords72 G.toMultiComputeDigraph = expandedPairs72 G G.activePairsList := by
  have hlist : (List.finRange G.numEdges).map G.edgeEndpoints = G.edgeListWithMult := by
    rw [← List.ofFn_eq_map]
    apply List.ext_getElem (by simp [G.length_edgeListWithMult])
    intro i hi hj
    simp only [List.getElem_ofFn, MultiDigraph.edgeEndpoints]
  have h := congrArg (List.flatMap (fun p : Fin n × Fin n => [p.1.1, p.2.1])) hlist
  calc
    _ = G.edgeListWithMult.flatMap (fun p => [p.1.1, p.2.1]) := by
      simpa only [endpointWords72, List.flatMap_map] using h
    _ = _ := by
      simp only [MultiDigraph.edgeListWithMult, List.flatMap_assoc, List.flatMap_replicate,
        expandedPairs72]

/-- For active pairs the number of triples is at most the number of edges. -/
theorem length_activePairs_le_sum72 {n : ℕ} (G : MultiDigraph n)
    (ps : List (Fin n × Fin n)) (hpos : ∀ p ∈ ps, 0 < G.edgeMult p.1 p.2) :
    ps.length ≤ G.sumEdgeMult ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := hpos p List.mem_cons_self
    have ht := ih (fun p' hp' => hpos p' (List.mem_cons_of_mem p hp'))
    simp only [List.length_cons, MultiDigraph.sumEdgeMult]
    omega

end GraphMinor.Compute
