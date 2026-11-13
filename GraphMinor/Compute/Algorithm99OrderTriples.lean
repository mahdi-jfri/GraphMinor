module

public import GraphMinor.Compute.Bridge3
public import GraphMinor.Compute.Algorithm99OrderPairs

/-!
# Individual edge order in each tail bucket

The row identity for active pairs remains true when each pair is expanded into
its individual edges. Parallel-edge indices run from zero to the multiplicity
minus one on both sides. Grouping the input triple stream by tail therefore
gives exactly the caller's lexicographic triple stream.
-/

@[expose] public section
namespace GraphMinor.Compute

private theorem filter_triple_rows99 {n : ℕ} (G : MultiDigraph n)
    (ps : List (Fin n × Fin n)) (u : Fin n) :
    (ps.flatMap (fun p => (List.range (G.edgeMult p.1 p.2)).map
      (fun k => (p.1.1, p.2.1, k)))).filter (fun e => decide (e.1 = u.1)) =
    (ps.filter (fun p => decide (p.1 = u))).flatMap
      (fun p => (List.range (G.edgeMult p.1 p.2)).map (fun k => (p.1.1, p.2.1, k))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.filter_append, List.filter_map, List.filter_cons]
    by_cases h : p.1 = u
    · simp [h, ih, Function.comp_def]
    · have hv : p.1.1 ≠ u.1 := fun he => h (Fin.ext he)
      simp [h, hv, ih, Function.comp_def]

private theorem flatMap_positive_rows99 {n : ℕ} (G : MultiDigraph n)
    (ps : List (Fin n)) (u : Fin n) :
    (ps.filter (fun v => decide (0 < G.edgeMult u v))).flatMap
      (fun v => (List.range (G.edgeMult u v)).map (fun k => (u.1, v.1, k))) =
    ps.flatMap (fun v => (List.range (G.edgeMult u v)).map (fun k => (u.1, v.1, k))) := by
  induction ps with
  | nil => rfl
  | cons v ps ih =>
    by_cases hp : 0 < G.edgeMult u v
    · simp [hp, ih]
    · have hz : G.edgeMult u v = 0 := by omega
      simp [hz, ih]

/-- The individual edges of a fixed tail occur in head order and then in
parallel-edge-index order in the active-pair stream. -/
theorem MultiDigraph.filter_multiEdgeTriples_tail99 {n : ℕ} (G : MultiDigraph n)
    (u : Fin n) :
    G.multiEdgeTriples.filter (fun e => decide (e.1 = u.1)) =
      (List.finRange n).flatMap (fun v =>
        (List.range (G.edgeMult u v)).map (fun k => (u.1, v.1, k))) := by
  rw [MultiDigraph.multiEdgeTriples, filter_triple_rows99,
    G.filter_activePairsList_tail99, List.flatMap_map]
  exact flatMap_positive_rows99 G (List.finRange n) u

/-- Stable grouping by tail produces the caller's exact triple stream, with
the same index for each parallel edge. -/
theorem MultiDigraph.group_multiEdgeTriples_tail99 {n : ℕ} (G : MultiDigraph n) :
    (List.finRange n).flatMap (fun u =>
      G.multiEdgeTriples.filter (fun e => decide (e.1 = u.1))) = G.directedEdgeTriples := by
  unfold MultiDigraph.directedEdgeTriples
  apply List.flatMap_congr
  intro u _
  exact G.filter_multiEdgeTriples_tail99 u

end GraphMinor.Compute
