module

public import GraphMinor.Compute.Case3StepsCompass
public import GraphMinor.Compute.Algorithm99TransportOrig

/-!
# The compact multigraph of a compass

Step (5) of XIII (9.9), page 104, uses the compass with its vertices numbered
consecutively. We restrict the edge multiplicities along the increasing list
of compass vertices. Its underlying simple graph is the compact graph used
by (8.6). Renaming its vertices and edge triples gives exactly the original
compass subgraph, including loops and all parallel copies.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph GraphMinor.GM09 GraphMinor.Transport Classical

/-- The multigraph on the consecutively numbered compass vertices. -/
noncomputable def case3CompactCompassMultigraph {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) : MultiDigraph (compassCard W) :=
  D.induce (compassEmb W)

/-- Compact numbering keeps each directed edge multiplicity. -/
theorem case3CompactCompassMultigraph_edgeMult {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (u v : Fin (compassCard W)) :
    (case3CompactCompassMultigraph D W).edgeMult u v =
      D.edgeMult (compassEmb W u) (compassEmb W v) := by
  rfl

/-- The simple graph of the compact multigraph is the input graph for (8.6). -/
theorem case3CompactCompassMultigraph_toSimpleGraph {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) :
    (case3CompactCompassMultigraph D W).toSimpleGraph = compactCompassGraph D W := by
  ext u v
  rw [MultiDigraph.toSimpleGraph_adj, compactCompassGraph_adj, MultiDigraph.toSimpleGraph_adj,
    case3CompactCompassMultigraph_edgeMult, case3CompactCompassMultigraph_edgeMult]
  exact and_congr (not_congr (compassEmb W).injective.eq_iff).symm Iff.rfl

/-- Renaming the compact compass gives exactly the induced multigraph compass. -/
theorem case3CompactCompassMultigraph_relabel {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) :
    relabelGraph (origVertexEmb (compassEmb W) (compassEmb W).injective)
      (origEdgeEmb (compassEmb W) (compassEmb W).injective)
      (case3CompactCompassMultigraph D W).toGMDigraph.toGraph =
        D.toGMDigraph.toGraph.induce W.compassFinset.toNatSet := by
  let f := origVertexEmb (compassEmb W) (compassEmb W).injective
  let g := origEdgeEmb (compassEmb W) (compassEmb W).injective
  let K := (case3CompactCompassMultigraph D W).toGMDigraph.toGraph
  have hsub : relabelGraph f g K ≤ D.toGMDigraph.toGraph :=
    relabelGraph_toGMGraph_le (compassEmb W).injective (fun _ _ => Or.inr rfl)
  have hcomp : W.compassFinset.toNatSet ⊆ V(D.toGMDigraph.toGraph) := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2
  have hV : V(relabelGraph f g K) = W.compassFinset.toNatSet := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : u < compassCard W := hu
      change f u ∈ W.compassFinset.toNatSet
      rw [origVertexEmb_apply_val (compassEmb W) (compassEmb W).injective ⟨u, hu'⟩]
      exact ⟨compassEmb W ⟨u, hu'⟩, compassEmb_mem_compassFinset W _, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, hi⟩ := (mem_range_compassEmb_iff W u).mpr hu
      refine ⟨i.1, i.2, ?_⟩
      change origVertexEmb (compassEmb W) (compassEmb W).injective i.1 = u.1
      rw [origVertexEmb_apply_val, hi]
  refine (Compatible.of_le_le hsub (Graph.induce_le hcomp)).ext hV ?_
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨a, b, hl⟩ := (relabelGraph f g K).exists_isLink_of_mem_edgeSet he
    exact ⟨a, b, hl.mono hsub, hV ▸ hl.left_mem, hV ▸ hl.right_mem⟩
  · rintro e ⟨a, b, hl, ha, hb⟩
    have he := hl.edge_mem
    have ht : e.1 < n := he.choose
    have hh : e.2.1 < n := he.choose_spec.choose
    have hends : e.1 ∈ W.compassFinset.toNatSet ∧ e.2.1 ∈ W.compassFinset.toNatSet := by
      rcases hl.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hb, ha⟩
      · exact ⟨ha, hb⟩
    have htail : (⟨e.1, ht⟩ : Fin n) ∈ W.compassFinset := by
      obtain ⟨u, hu, heq⟩ := hends.1
      exact (show u = (⟨e.1, ht⟩ : Fin n) from Fin.ext heq) ▸ hu
    have hhead : (⟨e.2.1, hh⟩ : Fin n) ∈ W.compassFinset := by
      obtain ⟨u, hu, heq⟩ := hends.2
      exact (show u = (⟨e.2.1, hh⟩ : Fin n) from Fin.ext heq) ▸ hu
    obtain ⟨i, hi⟩ := (mem_range_compassEmb_iff W ⟨e.1, ht⟩).mpr htail
    obtain ⟨j, hj⟩ := (mem_range_compassEmb_iff W ⟨e.2.1, hh⟩).mpr hhead
    have hk : e.2.2 < (case3CompactCompassMultigraph D W).edgeMult i j := by
      rw [case3CompactCompassMultigraph_edgeMult, hi, hj]
      exact he.choose_spec.choose_spec
    refine ⟨(i.1, j.1, e.2.2), ⟨i.2, j.2, hk⟩, ?_⟩
    change (origVertexEmb (compassEmb W) (compassEmb W).injective i.1,
      origVertexEmb (compassEmb W) (compassEmb W).injective j.1, e.2.2) = e
    rw [origVertexEmb_apply_val, origVertexEmb_apply_val, hi, hj]

end GraphMinor.Compute
