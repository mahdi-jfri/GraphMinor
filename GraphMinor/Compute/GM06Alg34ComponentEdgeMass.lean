module

public import GraphMinor.Compute.GM06Alg34ComponentVertexMass

/-!
# Edge mass of component branching

Both ends of every supplied edge lie in one component. Distinct root
components therefore retain disjoint edge lists, and their concatenation
permutes the original edge range. This includes loops and parallel
edges because the partition uses edge labels, not endpoint pairs.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

/-- Both endpoints of every supplied edge are reachable, including a loop. -/
theorem vertexGraph_reachable_ends (x : GM06DrawingData) (e : Fin x.ends.length) :
    x.vertexGraph.Reachable x.ends[e].1 x.ends[e].2 := by
  by_cases he : x.ends[e].1 = x.ends[e].2
  · exact he ▸ SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ⟨he, e, Or.inl ⟨rfl, rfl⟩⟩

/-- The edge lists retained by two distinct canonical root components are disjoint. -/
theorem componentEdges_disjoint (x : GM06DrawingData) {a b : Fin x.n}
    (ha : a ∈ x.componentRoots) (hb : b ∈ x.componentRoots) (hne : a ≠ b) :
    (x.activeEdges (x.componentVertices a)).Disjoint
      (x.activeEdges (x.componentVertices b)) := by
  apply List.disjoint_left.mpr
  intro e hea heb
  have ha' := ((x.mem_activeEdges_iff _ e).mp hea).1
  have hb' := ((x.mem_activeEdges_iff _ e).mp heb).1
  exact (List.disjoint_left.mp (x.componentVertices_disjoint ha hb hne)) ha' hb'

/-- The canonical component edge lists partition all original edge labels. -/
theorem componentEdges_flatMap_perm (x : GM06DrawingData) :
    (x.componentRoots.flatMap (fun a => x.activeEdges (x.componentVertices a))).Perm
      (List.finRange x.ends.length) := by
  have hn : x.componentRoots.Nodup := (List.nodup_finRange _).filter _
  have hp : List.Pairwise
      (Function.onFun List.Disjoint (fun a => x.activeEdges (x.componentVertices a))) x.componentRoots :=
    List.Pairwise.imp_of_mem (fun ha hb hne => x.componentEdges_disjoint ha hb hne) hn
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_flatMap.mpr ⟨fun a _ => x.activeEdges_nodup _, hp⟩)
    (List.nodup_finRange _)).mpr
  intro e
  simp only [List.mem_finRange, iff_true]
  obtain ⟨r, hr, har⟩ := x.exists_componentRoot x.ends[e].1
  apply List.mem_flatMap.mpr
  refine ⟨r, hr, (x.mem_activeEdges_iff _ e).mpr ⟨?_, ?_⟩⟩
  · exact (x.mem_componentVertices_iff _ _).mpr har.symm
  · exact (x.mem_componentVertices_iff _ _).mpr (har.symm.trans (x.vertexGraph_reachable_ends e))

/-- The total child edge count is exactly the original edge count. -/
theorem componentData_sum_edges (x : GM06DrawingData) :
    (x.componentRoots.map (fun a => (x.componentData a).ends.length)).sum = x.ends.length := by
  have hh := (x.componentEdges_flatMap_perm).length_eq
  simpa only [componentData, x.inducedData_ends_length, List.length_flatMap, List.length_finRange] using hh

end GraphMinor.Compute.GM06DrawingData
