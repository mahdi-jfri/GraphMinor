module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.Cylinder
import GraphMinor.GM06.Section4
import GraphMinor.Surface.DiscMerge
import GraphMinor.GM06.Section4ArcCrossing
import GraphMinor.GM06.Section4ComponentSeparation
import GraphMinor.GM06.Section4InitialInterval

/-!
# Components inside a cuff arc stay on that cuff

In the minimum-size argument of Graph Minors VI (4.2), claim (2), a
component with a vertex between the ends of another component's
homotopic cuff path cannot reach the other cuff. A path to that cuff
would cross the first path. Distinct components have disjoint point
sets, which excludes this crossing.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- A distinct component meeting the cuff arc of a path cannot also
meet the other cuff. This is the nesting constraint used in Graph
Minors VI (4.2), claim (2), page 126. -/
theorem other_cuff_vertex_excluded_of_component_meeting_arc
    {H P : Drawing ClosedCylinder}
    {K L : Graph ClosedCylinder (Set ClosedCylinder)}
    (hK : IsGraphComponent K H.toGraph) (hL : IsGraphComponent L H.toGraph) (hne : K ≠ L)
    (outer : Bool) {A : Set ClosedCylinder}
    (hAC : closure A ⊆ if outer then cylinderCuff2 else cylinderCuff1)
    {a b x z : ClosedCylinder} (ha : a ∈ Graph.vertexSet K)
    (hP : IsSubpathOf H P a b) (hPA : PathHomotopicToArc P a b A)
    (hx : x ∈ Graph.vertexSet L ∩ A) (hz : z ∈ Graph.vertexSet L)
    (hzC : z.1.1 = (if outer then 1 else 2)) : False := by
  have hxC : x.1.1 = (if outer then 2 else 1) := by
    have hxC := hAC (subset_closure hx.2)
    cases outer <;> exact hxC
  have hneR : (if outer then (2 : ℝ) else 1) ≠ (if outer then 1 else 2) := by
    cases outer <;> norm_num
  have hxz : x ≠ z := fun he => hneR
    (hxC.symm.trans ((congrArg (fun p : ClosedCylinder => p.1.1) he).trans hzC))
  obtain ⟨Q, hQ⟩ := exists_subpath_of_mem_component hL hx.1 hz hxz
  obtain ⟨f, k, hf, hk, hfk⟩ := hPA
  obtain ⟨g, hg⟩ := hQ.2.2.2
  have hkr : ∀ v, (k v).1.1 = (if outer then 2 else 1) := by
    intro v
    have hv := hAC (hk.2.1 ▸ mem_range_self v)
    cases outer <;> exact hv
  have hgk : g 0 ∈ range k := by
    rw [hg.2.2.1, hk.2.1]
    exact subset_closure hx.2
  have hdisj : Disjoint (range f) (range g) :=
    (disjoint_compPointSet_of_ne H hK hL hne).mono
      (by rw [hf.2.1]; exact path_U_subset_compPointSet_of_start hK hP ha)
      (by rw [hg.2.1]; exact path_U_subset_compPointSet_of_start hL hQ hx.1)
  exact not_disjoint_crosscurve_of_homotopic_cuff_arc outer hk.1 hkr hfk hgk
    (by rw [hg.2.2.2]; exact hzC) hdisj

/-- A distinct component with a vertex inside the cuff arc of a
homotopic path has all its boundary vertices inside that arc. It cannot
reach the other cuff, and noncrossing confines the vertices on this one.
This is the component replacement used in VI (4.2), claim (2). -/
theorem component_boundary_subset_arc_of_mem
    {H P : Drawing ClosedCylinder}
    {K L : Graph ClosedCylinder (Set ClosedCylinder)}
    (hK : IsGraphComponent K H.toGraph) (hL : IsGraphComponent L H.toGraph) (hne : K ≠ L)
    {C A : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder)
    {a b x : ClosedCylinder} (hab : a ≠ b)
    (ha : a ∈ Graph.vertexSet K ∩ C) (hb : b ∈ Graph.vertexSet K ∩ C)
    (hA : A ∈ componentsIn (C \ {a, b}))
    (hP : IsSubpathOf H P a b) (hPA : PathHomotopicToArc P a b A)
    (hx : x ∈ Graph.vertexSet L ∩ A) :
    Graph.vertexSet L ∩ bd ClosedCylinder ⊆ A := by
  have hsame := component_cuff_vertices_subset_arc_of_mem hK hL hne hC hab ha hb hA hx
  have hcases : C = cylinderCuff1 ∨ C = cylinderCuff2 := by
    rw [cuffs_closedCylinder] at hC
    exact hC
  have hCO : IsOArc C := hcases.elim
    (fun h => h ▸ isOArc_cylinderCuff1) (fun h => h ▸ isOArc_cylinderCuff2)
  have hAsub : A ⊆ C := by
    obtain ⟨o, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ o).trans sdiff_subset
  have hclA : closure A ⊆ C := closure_minimal hAsub hCO.isCompact.isClosed
  obtain ⟨outer, houter⟩ : ∃ outer : Bool,
      C = if outer then cylinderCuff2 else cylinderCuff1 := by
    rcases hcases with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  intro z hz
  by_cases hzC : z ∈ C
  · exact hsame ⟨hz.1, hzC⟩
  have hzbd : z ∈ cylinderCuff1 ∪ cylinderCuff2 := bd_closedCylinder ▸ hz.2
  have hzother : z.1.1 = (if outer then 1 else 2) := by
    cases outer
    · rcases hzbd with hz1 | hz2
      · exact (hzC (by rw [houter]; exact hz1)).elim
      · exact hz2
    · rcases hzbd with hz1 | hz2
      · exact hz1
      · exact (hzC (by rw [houter]; exact hz2)).elim
  exact (other_cuff_vertex_excluded_of_component_meeting_arc hK hL hne outer
    (by simpa only [houter] using hclA) ha.1 hP hPA hx hz.1 hzother).elim

end GraphMinor.GM06
