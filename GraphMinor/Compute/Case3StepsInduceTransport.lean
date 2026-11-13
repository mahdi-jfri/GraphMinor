module

public import GraphMinor.Compute.Case3StepsCompassGraph

/-!
# Restoring the labels of an ordered induced multigraph

Renaming consecutive labels through the increasing vertex list restores
exactly the original induced graph, including all directed parallel copies.
This identifies the compact member used in XIII (9.9), step 6, with the
member graph to which its branch-decomposition will be assigned.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport Classical

/-- The ordered induced multigraph, renamed through its vertex list, is
exactly the original graph restricted to that list's vertex set. -/
theorem case3Induce_relabel_eq {n : ℕ} (D : MultiDigraph n) (S : Finset (Fin n)) :
    relabelGraph (origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
      (origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
      (D.induce (S.orderEmbOfFin rfl)).toGMDigraph.toGraph =
        D.toGMDigraph.toGraph.induce S.toNatSet := by
  let f := origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective
  let g := origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective
  let K := (D.induce (S.orderEmbOfFin rfl)).toGMDigraph.toGraph
  have hsub : relabelGraph f g K ≤ D.toGMDigraph.toGraph :=
    relabelGraph_toGMGraph_le (S.orderEmbOfFin rfl).injective (fun _ _ => Or.inr rfl)
  have hcomp : S.toNatSet ⊆ V(D.toGMDigraph.toGraph) := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2
  have hV : V(relabelGraph f g K) = S.toNatSet := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : u < S.card := hu
      change f u ∈ S.toNatSet
      rw [origVertexEmb_apply_val (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective ⟨u, hu'⟩]
      exact ⟨S.orderEmbOfFin rfl ⟨u, hu'⟩, S.orderEmbOfFin_mem rfl _, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, hi⟩ := (show u ∈ Set.range (S.orderEmbOfFin rfl) from (S.range_orderEmbOfFin rfl).symm ▸ hu)
      refine ⟨i.1, i.2, ?_⟩
      change origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective i.1 = u.1
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
    have hends : e.1 ∈ S.toNatSet ∧ e.2.1 ∈ S.toNatSet := by
      rcases hl.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hb, ha⟩
      · exact ⟨ha, hb⟩
    have htail : (⟨e.1, ht⟩ : Fin n) ∈ S := by
      obtain ⟨u, hu, heq⟩ := hends.1
      exact (show u = (⟨e.1, ht⟩ : Fin n) from Fin.ext heq) ▸ hu
    have hhead : (⟨e.2.1, hh⟩ : Fin n) ∈ S := by
      obtain ⟨u, hu, heq⟩ := hends.2
      exact (show u = (⟨e.2.1, hh⟩ : Fin n) from Fin.ext heq) ▸ hu
    obtain ⟨i, hi⟩ := (show (⟨e.1, ht⟩ : Fin n) ∈ Set.range (S.orderEmbOfFin rfl) from (S.range_orderEmbOfFin rfl).symm ▸ htail)
    obtain ⟨j, hj⟩ := (show (⟨e.2.1, hh⟩ : Fin n) ∈ Set.range (S.orderEmbOfFin rfl) from (S.range_orderEmbOfFin rfl).symm ▸ hhead)
    have hk : e.2.2 < (D.induce (S.orderEmbOfFin rfl)).edgeMult i j := by
      change e.2.2 < D.edgeMult ((S.orderEmbOfFin rfl) i) ((S.orderEmbOfFin rfl) j)
      rw [hi, hj]
      exact he.choose_spec.choose_spec
    refine ⟨(i.1, j.1, e.2.2), ⟨i.2, j.2, hk⟩, ?_⟩
    change (origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective i.1,
      origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective j.1, e.2.2) = e
    rw [origVertexEmb_apply_val, origVertexEmb_apply_val, hi, hj]


end GraphMinor.Compute
