module

public import GraphMinor.Compute.GM13WallThreshold

/-!
# The high-width certificate used in Graph Minors XIII, (7.1)

For integer rounding in (7.1), we use the two failure cases of the (3.3)
program. Both show that its original input has width greater than its search
parameter. In the density case this is (3.2). In Step (6), the graph before
edge deletion has no balanced separation, so (3.1) gives the claim.
-/

public section
namespace GraphMinor.Compute

open GraphMinor GM13 Graph Set SimpleGraph Classical

/-- Choose one original directed edge for each adjacency of the underlying simple
graph, as in the first operation of XIII (3.3), page 72. -/
noncomputable def simpleSubgraph71 {n : ℕ} (G : MultiDigraph n) : MultiDigraph n where
  edgeMult u v :=
    if u ≠ v ∧ 0 < G.edgeMult u v ∧ (u.1 < v.1 ∨ G.edgeMult v u = 0) then 1 else 0

private theorem simpleSubgraph71_le {n : ℕ} (G : MultiDigraph n) : simpleSubgraph71 G ≤ G := by
  intro u v
  change (if u ≠ v ∧ 0 < G.edgeMult u v ∧ (u.1 < v.1 ∨ G.edgeMult v u = 0) then 1 else 0) ≤ _
  split_ifs with hc
  · exact hc.2.1
  · exact Nat.zero_le _

private theorem simpleSubgraph71_noLoops {n : ℕ} (G : MultiDigraph n) (u : Fin n) :
    (simpleSubgraph71 G).edgeMult u u = 0 := by simp [simpleSubgraph71]

private theorem simpleSubgraph71_oneEdge {n : ℕ} (G : MultiDigraph n) (u v : Fin n) :
    (simpleSubgraph71 G).edgeMult u v + (simpleSubgraph71 G).edgeMult v u ≤ 1 := by
  change (if u ≠ v ∧ 0 < G.edgeMult u v ∧ (u.1 < v.1 ∨ G.edgeMult v u = 0) then 1 else 0) +
    (if v ≠ u ∧ 0 < G.edgeMult v u ∧ (v.1 < u.1 ∨ G.edgeMult u v = 0) then 1 else 0) ≤ 1
  split_ifs with hc hd
  · rcases hc.2.2 with hlt | hz <;> rcases hd.2.2 with hlt' | hz' <;> omega
  all_goals omega

private theorem simpleSubgraph71_underlying {n : ℕ} (G : MultiDigraph n) :
    (simpleSubgraph71 G).toSimpleGraph = G.toSimpleGraph := by
  ext u v
  constructor
  · rintro ⟨hne, hp | hp⟩
    · exact ⟨hne, Or.inl (hp.trans_le (simpleSubgraph71_le G u v))⟩
    · exact ⟨hne, Or.inr (hp.trans_le (simpleSubgraph71_le G v u))⟩
  · rintro ⟨hne, hp⟩
    refine ⟨hne, ?_⟩
    have hex :
        (u ≠ v ∧ 0 < G.edgeMult u v ∧ (u.1 < v.1 ∨ G.edgeMult v u = 0)) ∨
        (v ≠ u ∧ 0 < G.edgeMult v u ∧ (v.1 < u.1 ∨ G.edgeMult u v = 0)) := by
      by_cases huv : u.1 < v.1
      · by_cases hpos : 0 < G.edgeMult u v
        · exact Or.inl ⟨hne, hpos, Or.inl huv⟩
        · exact Or.inr ⟨hne.symm, by omega, Or.inr (by omega)⟩
      · have hvu : v.1 < u.1 := by
          have hvne : u.1 ≠ v.1 := fun hh => hne (Fin.ext hh)
          omega
        by_cases hpos : 0 < G.edgeMult v u
        · exact Or.inr ⟨hne.symm, hpos, Or.inl hvu⟩
        · exact Or.inl ⟨hne, by omega, Or.inr (by omega)⟩
    rcases hex with hc | hc
    · left
      simp only [simpleSubgraph71, ite_eq_left hc]
      decide
    · right
      simp only [simpleSubgraph71, ite_eq_left hc]
      decide

/-- Passing to the underlying simple graph does not increase branch-width when
its given upper bound is at least two. The selected edges are original edges. -/
theorem graphBranchWidthLE_underlying71 {n k : ℕ} (G : MultiDigraph n) (hk : 2 ≤ k)
    (hbw : GraphBranchWidthLE G.toGMDigraph.toGraph k) :
    GraphBranchWidthLE G.toSimpleGraph.toGMGraph k := by
  have hsub : (simpleSubgraph71 G).toGMDigraph.toGraph ≤ G.toGMDigraph.toGraph := by
    refine ⟨Subset.rfl, ?_⟩
    intro e x y he
    rcases he with ⟨⟨hu, hv, he⟩, hends⟩
    exact ⟨⟨hu, hv, he.trans_le (simpleSubgraph71_le G _ _)⟩, hends⟩
  have hsmall := GraphBranchWidthLE.mono G.isFinite_toGMDigraph.finite_V
    G.isFinite_toGMDigraph.finite_E hsub hk hbw
  have hs := graphBranchWidthLE_toSimpleGraph_of_toGMDigraph (simpleSubgraph71 G)
    (simpleSubgraph71_noLoops G) (simpleSubgraph71_oneEdge G) hsmall
  simpa only [simpleSubgraph71_underlying] using hs

private theorem simpleGraph_width_mono71 {n k : ℕ} {H G : SimpleGraph (Fin n)}
    (h : H ≤ G) (hk : 2 ≤ k) (hbw : GraphBranchWidthLE G.toGMGraph k) :
    GraphBranchWidthLE H.toGMGraph k := by
  have hsub : H.toGMGraph ≤ G.toGMGraph := by
    refine ⟨Subset.rfl, ?_⟩
    intro e x y he
    rw [Graph.ofSimpleGraph_isLink] at he ⊢
    rcases he with ⟨rfl, he⟩
    rw [SimpleGraph.mem_edgeSet] at he
    exact ⟨rfl, by rw [SimpleGraph.mem_edgeSet]; exact h he⟩
  exact GraphBranchWidthLE.mono (Set.toFinite _) (Set.toFinite _) hsub hk hbw

private theorem edge_density_nat71 {n k E : ℕ} (hk : 2 ≤ k)
    (hgt : ((3 : ℚ) / 2 * (k : ℚ) - 1) * (n : ℚ) < (E : ℚ)) :
    (3 * k - 2) * n < 2 * E := by
  have hcast : ((3 * k - 2 : ℕ) : ℚ) = (3 : ℚ) * (k : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hq : ((3 * k - 2 : ℕ) : ℚ) * (n : ℚ) < 2 * (E : ℚ) := by
    rw [hcast]
    linarith
  exact_mod_cast hq

/-- The failure certificate of XIII (3.3), pages 72–74, forces width greater
than the search parameter in the original input. This is the form needed to
round the numerical parameter in (7.1) without enlarging the output width. -/
theorem not_width_original_of_high71 {n k : ℕ} {G G' : MultiDigraph n}
    (hk : 2 ≤ k) (hle : G' ≤ G) (hhigh : IsAlg33HighWidthCase k G G') :
    ¬ GraphBranchWidthLE G.toGMDigraph.toGraph k := by
  classical
  intro hbw
  have hs := graphBranchWidthLE_underlying71 G hk hbw
  rcases hhigh with ⟨_, _, hcase⟩
  rcases hcase with ⟨_, hgt⟩ | ⟨Gstep, g, Z, hstep, _, _, _, _, hno⟩
  · letI := Classical.decRel G'.toSimpleGraph.Adj
    have hsub : G'.toSimpleGraph ≤ G.toSimpleGraph := by
      intro u v huv
      exact ⟨huv.1, huv.2.imp (fun hp => hp.trans_le (hle u v)) (fun hp => hp.trans_le (hle v u))⟩
    exact not_graphBranchWidthLE_of_edge_gt hk G'.toSimpleGraph (edge_density_nat71 hk (by simpa using hgt))
      (simpleGraph_width_mono71 hsub hk hs)
  · exact not_graphBranchWidthLE_of_no_balanced_sep hk Gstep Z hno
      (simpleGraph_width_mono71 hstep hk hs)

end GraphMinor.Compute
