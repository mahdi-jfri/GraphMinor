module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.Cylinder
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4SpanningRegion
import GraphMinor.GM06.Section4CuffInterval
import GraphMinor.GM06.Section4OpenSubarc
import GraphMinor.GM06.Section4CrosscutHomotopy
import GraphMinor.GM06.Section5Red
import GraphMinor.GM11.Walks
import GraphMinor.GM11.Section4b
import GraphMinor.Surface.CutCyl
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.AddCrosscap

/-!
# The initial interval in VI (4.2), claim (2)

If a component meets only one cuff, choose a region reaching both cuffs
and two nearby points of that cuff in the region. The complementary
interval contains every boundary vertex of the component. Its paths
are homotopic to the corresponding subarcs because they avoid the
crossing curve in the chosen region. These are conditions (i) and (ii)
before the paper takes a minimum on page 126.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Distinct vertices of a graph component are joined by a path drawing
in the original drawing. -/
theorem exists_subpath_of_mem_component
    {S : Type} [TopologicalSpace S] [T1Space S]
    {H : Drawing S} {H' : Graph S (Set S)}
    (hH' : IsGraphComponent H' H.toGraph) {a b : S}
    (ha : a ∈ Graph.vertexSet H') (hb : b ∈ Graph.vertexSet H') (hab : a ≠ b) :
    ∃ P : Drawing S, IsSubpathOf H P a b := by
  classical
  obtain ⟨W⟩ := hH'.2.1.2 a ha b hb
  obtain ⟨W', hW', _, _⟩ := GM11.GraphWalk.exists_isSimple (W.mono hH'.1)
  have hsub := walkDrawing_isSubdrawing H W'
  exact ⟨walkDrawing H W', hsub, hsub.U_subset,
    isPathDrawing_walkDrawing_of_isSimple H hW' hab⟩

/-- Graph Minors VI (4.2), claim (2), page 126: a component has a cuff
interval containing its vertices on that cuff, with their subarc
homotopies. Other components may still have vertices in this interval. -/
theorem exists_initial_interval_on_cuff
    {H : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph)
    {H' : Graph ClosedCylinder (Set ClosedCylinder)}
    (hH' : IsGraphComponent H' H.toGraph)
    {C : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder) :
    ∃ s ∈ C \ H.V, ∃ t ∈ C \ H.V, s ≠ t ∧
      ∃ A ∈ componentsIn (C \ {s, t}),
        Graph.vertexSet H' ∩ C ⊆ A ∧
        ∀ a ∈ Graph.vertexSet H' ∩ A, ∀ b ∈ Graph.vertexSet H' ∩ A, a ≠ b →
          ∃ P : Drawing ClosedCylinder, IsSubpathOf H P a b ∧
            PathHomotopicToArc P a b (cuffSubArc C A a b) := by
  have hLC : LocallyConnectedSpace ClosedCylinder := by
    obtain ⟨m⟩ := nonempty_cyl_homeo
    exact (isSurface_of_homeo m (isSurface_model 0 0 2).1).locallyConnected
  have := hLC
  have hcases : C = cylinderCuff1 ∨ C = cylinderCuff2 := by
    rw [cuffs_closedCylinder] at hC
    exact hC
  have hCO : IsOArc C := hcases.elim
    (fun h => h ▸ isOArc_cylinderCuff1) (fun h => h ▸ isOArc_cylinderCuff2)
  obtain ⟨outer, houter⟩ : ∃ outer : Bool,
      C = if outer then cylinderCuff2 else cylinderCuff1 := by
    rcases hcases with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  obtain ⟨δ, hδ0, hδ1, hδU⟩ := exists_curve_between_cuffs_off_forest hH
  obtain ⟨g, hg0, hg1, hgU⟩ : ∃ g : Curve ClosedCylinder,
      (g 0).1.1 = (if outer then 2 else 1) ∧
      (g 1).1.1 = (if outer then 1 else 2) ∧ range g ⊆ H.Uᶜ := by
    cases outer
    · exact ⟨δ, hδ0, hδ1, hδU⟩
    · exact ⟨GM07.subPathSeg δ 1 0,
        by
          change (GM07.subPathSeg δ 1 0 0).1.1 = (2 : ℝ)
          rw [GM07.subPathSeg_zero]
          exact hδ1,
        by
          change (GM07.subPathSeg δ 1 0 1).1.1 = (1 : ℝ)
          rw [GM07.subPathSeg_one]
          exact hδ0,
        (GM07.range_subPathSeg_subset δ 1 0).trans hδU⟩
  let O := connectedComponentIn H.Uᶜ (g 0)
  have hOo : IsOpen O := H.isClosed_U.isOpen_compl.connectedComponentIn
  have hOU : O ⊆ H.Uᶜ := connectedComponentIn_subset _ _
  have hgO : g 0 ∈ O := mem_connectedComponentIn (hgU (mem_range_self 0))
  have hgC : g 0 ∈ C := by rw [houter]; cases outer <;> exact hg0
  have hWO : Disjoint (Graph.vertexSet H' ∩ C) O := by
    refine disjoint_left.mpr ?_
    intro x hx hxO
    exact hOU hxO (H.V_subset_U (hH'.1.vertexSet_mono hx.1))
  obtain ⟨s, hs, t, ht, hst, A, hA, hWA, hgA, hline⟩ :=
    exists_cuff_interval_cover_avoiding_point hCO hOo hgC hgO inter_subset_right hWO
  have hAsub : A ⊆ C := by
    obtain ⟨x, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ x).trans sdiff_subset
  refine ⟨s, ⟨hs.1, fun hsV => hOU hs.2 (H.V_subset_U hsV)⟩,
    t, ⟨ht.1, fun htV => hOU ht.2 (H.V_subset_U htV)⟩, hst, A, hA, hWA, ?_⟩
  intro a ha b hb hab
  obtain ⟨P, hP⟩ := exists_subpath_of_mem_component hH' ha.1 hb.1 hab
  obtain ⟨f, hf⟩ := hP.2.2.2
  obtain ⟨k, hk, hkA⟩ := exists_parametrizesSet_cuffSubArc hCO hA hline ha.2 hb.2 hab
  have hkr : ∀ v, (k v).1.1 = (if outer then 2 else 1) := by
    intro v
    have hv := hAsub (hkA (mem_range_self v))
    rw [houter] at hv
    cases outer <;> exact hv
  have hfg : Disjoint (range f) (range g) := by
    refine disjoint_left.mpr ?_
    intro x hx hxg
    have hxH : x ∈ H.U := hP.2.1 (hf.2.1 ▸ hx)
    exact hgU hxg hxH
  have hhom := curvesHomotopic_of_disjoint_crosscurve outer hkr
    (hf.2.2.1.trans hk.2.2.1.symm) (hf.2.2.2.trans hk.2.2.2.symm)
    hg0 hg1 hfg (fun v he => hgA (he ▸ subset_closure (hkA (mem_range_self v))))
  exact ⟨P, hP, f, k, hf, hk, hhom⟩

/-- The initial conditions (i) and (ii) in the one-cuff case of Graph
Minors VI (4.2), claim (2), page 126. -/
theorem exists_initial_interval_of_component_on_one_cuff
    {H : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph)
    {H' : Graph ClosedCylinder (Set ClosedCylinder)}
    (hH' : IsGraphComponent H' H.toGraph)
    {C : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder)
    (honly : Graph.vertexSet H' ∩ bd ClosedCylinder ⊆ C) :
    ∃ s ∈ C \ H.V, ∃ t ∈ C \ H.V, s ≠ t ∧
      ∃ A ∈ componentsIn (C \ {s, t}),
        Graph.vertexSet H' ∩ bd ClosedCylinder ⊆ A ∧
        ∀ a ∈ Graph.vertexSet H' ∩ A, ∀ b ∈ Graph.vertexSet H' ∩ A, a ≠ b →
          ∃ P : Drawing ClosedCylinder, IsSubpathOf H P a b ∧
            PathHomotopicToArc P a b (cuffSubArc C A a b) := by
  obtain ⟨s, hs, t, ht, hst, A, hA, hKA, hpaths⟩ := exists_initial_interval_on_cuff hH hH' hC
  exact ⟨s, hs, t, ht, hst, A, hA, fun x hx => hKA ⟨hx.1, honly hx⟩, hpaths⟩

end GraphMinor.GM06
