module

public import GraphMinor.LRPlanarity.DefsContour
public import GraphMinor.HP25.Embedding
import GraphMinor.LRPlanarity.TreeNeighborhoodDrawingPolygons
import GraphMinor.LRPlanarity.TreeNeighborhoodSymmetricStrips
import GraphMinor.LRPlanarity.TreeNeighborhoodPathTubeDisc
import GraphMinor.LRPlanarity.TreeNeighborhoodPathTubeInterior
import GraphMinor.LRPlanarity.TreeNeighborhoodPathTubeSeparation
import GraphMinor.LRPlanarity.TreeNeighborhoodSubdivisionSeparation
import GraphMinor.LRPlanarity.TreeNeighborhoodParentTubes
import GraphMinor.LRPlanarity.TreeNeighborhoodParentFamily
import GraphMinor.LRPlanarity.TreeNeighborhoodUnion
import GraphMinor.LRPlanarity.TreeNeighborhoodLeafOrder
import GraphMinor.LRPlanarity.TreeNeighborhoodPathPorts
import GraphMinor.LRPlanarity.TreeNeighborhoodPorts
import GraphMinor.LRPlanarity.TreeNeighborhoodArcCut
import GraphMinor.Surface.DiscUnion
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.Surface.PlaneOrientation

/-!
# Tree neighborhoods from exact straight subdivision paths

Part IV, Section 7b of the planarity note subdivides the tree at its bends
without changing its image. Construct polygons and symmetric strips in
the straight subdivision. For each original parent edge, join its strips
and internal bend polygons into a tube. Distinct original edges give
disjoint tubes, so the original DFS forest controls the leaf gluing.
Cotree paths miss these tubes and all nonendpoint polygons. Their two
unique polygon-frontier ports survive on the final boundary and cut out
one exterior middle arc.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: exact simple straight subdivision paths give the
full rooted tree neighborhood, including injective cotree ports and exterior
arcs. The subdivision data are its drawing, original-vertex coordinates,
and exact simple paths for the original edges. -/
theorem exists_subdivided_tree_neighborhood {N : ℕ} {V : Type*} [Finite V]
    {G : SimpleGraph (Fin N)} {H : SimpleGraph V} {T : Forest N}
    (original : HP25.PlaneEmbedding G univ) (subdivision : HP25.PlaneEmbedding H univ)
    (hstraight : ∀ u v, H.Adj u v →
      subdivision.line u v = segment ℝ (subdivision.pt u) (subdivision.pt v))
    (vertex : Fin N → V) (hpoint : ∀ u, subdivision.pt (vertex u) = original.pt u)
    (paths : ∀ u v, G.Adj u v → H.Walk (vertex u) (vertex v))
    (hpath : ∀ u v h, (paths u v h).IsPath)
    (himage : ∀ u v h, subdivision.pathImage (paths u v h).support = original.line u v)
    (hT : T.IsDFS G) (root : Fin N) (hroot : T.parent root = none) :
    ∃ (D : Set ℂ) (port : Port N → ℂ), IsClosedDisc D ∧
      (∀ v, T.Ancestor root v → original.pt v ∈ interior D) ∧
      (∀ e, T.TreeEdge e → T.Ancestor root e.1 → original.line e.1 e.2 ⊆ interior D) ∧
      InjOn port {p | T.BackEdge G p.edge ∧ T.Ancestor root p.edge.1} ∧
      (∀ b, T.BackEdge G b → T.Ancestor root b.1 →
        port ⟨b,true⟩ ∈ frontier D ∧ port ⟨b,false⟩ ∈ frontier D ∧
        IsLineWithEnds (original.line b.1 b.2 \ interior D) (port ⟨b,true⟩) (port ⟨b,false⟩) ∧
        (original.line b.1 b.2 \ interior D) ∩ D = {port ⟨b,true⟩,port ⟨b,false⟩}) := by
  classical
  obtain ⟨angle, directions, r, hangle, _, hmem, hPdata, hPsep, hlength, hPaway⟩ :=
    exists_straight_drawing_vertex_polygons subdivision hstraight
  let P := fun v => vertexPolygonAt (subdivision.pt v) (directions v) (r v)
  obtain ⟨Rs, hcomm, hlocal, hRsep, hRaway, hRother⟩ := exists_symmetric_straight_strips
    subdivision hstraight angle directions r hangle hmem (fun v => (hPdata v).1) hlength hPaway
  let L := fun u v => Rs u v ∩ P u
  have hinter : ∀ u v, H.Adj u v → Rs u v ∩ P u = L u v ∧ Rs u v ∩ P v = L v u := by
    intro u v _
    exact ⟨rfl, by dsimp only [L]; rw [hcomm u v]⟩
  have hbd : ∀ u v, H.Adj u v → L u v ⊆ discBd (P u) ∧
      L u v ⊆ discBd (Rs u v) ∧ L v u ⊆ discBd (Rs u v) := by
    intro u v h
    exact ⟨(hlocal u v h).2.2.1, (hlocal u v h).2.2.2.1,
      by rw [hcomm u v]; exact (hlocal v u h.symm).2.2.2.1⟩
  have hvinj : Function.Injective vertex := by
    intro u v he
    exact original.injOn (mem_univ _) (mem_univ _)
      ((hpoint u).symm.trans ((congrArg subdivision.pt he).trans (hpoint v)))
  have hnil : ∀ u v (h : G.Adj u v), ¬(paths u v h).Nil := by
    intro u v h hn
    exact (G.ne_of_adj h) (hvinj ((hpath u v h).nil_iff_eq.mp hn))
  let E := {e : Fin N × Fin N // T.parent e.2 = some e.1}
  let edge : ∀ e : E, G.Adj e.val.1 e.val.2 := fun e => (hT.2.1 _ _ e.property).1
  let path := fun e : E => paths e.val.1 e.val.2 (edge e)
  let tube := fun e : E => walkTube P Rs (path e)
  let Po := fun v => P (vertex v)
  have htube : ∀ e : E, IsClosedDisc (tube e) ∧ ∃ a b c d,
      IsLineWithEnds (Po e.val.1 ∩ tube e) a b ∧
      IsLineWithEnds (tube e ∩ Po e.val.2) c d ∧
      Po e.val.1 ∩ tube e ⊆ discBd (Po e.val.1) ∧
      Po e.val.1 ∩ tube e ⊆ discBd (tube e) ∧
      tube e ∩ Po e.val.2 ⊆ discBd (tube e) ∧
      tube e ∩ Po e.val.2 ⊆ discBd (Po e.val.2) := by
    intro e
    exact walkTube_isClosedDisc P Rs L (fun v => (hPdata v).2.1) hPsep
      (fun u v h => (hlocal u v h).1) (fun u v h => (hlocal u v h).2.1)
      hinter hbd hRsep hRaway (path e) (hpath _ _ _) (hnil _ _ _)
  have htubesep : Pairwise (fun e f => Disjoint (tube e) (tube f)) := by
    intro e f hef
    have hne : s(e.val.1,e.val.2) ≠ s(f.val.1,f.val.2) :=
      fun he => hef (parent_edge_unordered_injective hT he)
    obtain ⟨hfirst, hlast, hedges⟩ := original_edge_subdivision_paths_separated
      original subdivision vertex hpoint (edge e) (edge f) hne (path e) (path f)
      (hpath _ _ _) (hpath _ _ _) (himage _ _ _) (himage _ _ _)
    exact walkTubes_disjoint P Rs hPsep hRsep hRaway (path e) (path f) hfirst hlast hedges
  have htubeaway : ∀ e : E, ∀ w, w ≠ e.val.1 → w ≠ e.val.2 → Disjoint (tube e) (Po w) := by
    intro e w hws hwt
    apply walkTube_disjoint_polygon P Rs hPsep hRaway (path e)
    intro hw
    have hm := path_vertex_mem_pathImage subdivision (path e) (hpath _ _ _) (hnil _ _ _) hw
    rw [himage, hpoint] at hm
    exact (original.avoid _ (mem_univ _) _ (mem_univ _) (edge e) w (mem_univ _) hm).elim hws hwt
  let R := parentEdgeFamily T ∅ tube
  let S := Finset.univ.filter (T.Ancestor root)
  obtain ⟨hD, hboundary⟩ := parent_tube_union_isClosedDisc hT Po tube
    (fun v => (hPdata (vertex v)).2.1)
    (fun u v huv => hPsep (fun he => huv (hvinj he))) htubesep htubeaway htube root hroot
  have hS : ∀ v, v ∈ S ↔ T.Ancestor root v := by
    intro v
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hPsub : ∀ v ∈ S, Po v ⊆ forestCellUnion Po R S := by
    intro v hv x hx
    exact mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, Or.inl hx⟩⟩
  have hRsub : ∀ v ∈ S, R v ⊆ forestCellUnion Po R S := by
    intro v hv x hx
    exact mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, Or.inr hx⟩⟩
  let I := {e : Fin N × Fin N // G.Adj e.1 e.2}
  have hports : ∀ e : I, ∃ a : ℂ, a ≠ original.pt e.val.1 ∧
      Po e.val.1 ∩ original.line e.val.1 e.val.2 = segment ℝ (original.pt e.val.1) a ∧
      frontier (Po e.val.1) ∩ original.line e.val.1 e.val.2 = {a} := by
    intro e
    obtain ⟨a, hnot, htail, hfront⟩ := exists_path_source_polygon_port subdivision hstraight
      angle directions r hangle hmem (fun v => (hPdata v).1) hlength hPaway
      (paths e.val.1 e.val.2 e.property) (hpath _ _ _) (hnil _ _ _)
    change a ≠ subdivision.pt (vertex e.val.1) at hnot
    change Po e.val.1 ∩ subdivision.pathImage (paths e.val.1 e.val.2 e.property).support =
      segment ℝ (subdivision.pt (vertex e.val.1)) a at htail
    change frontier (Po e.val.1) ∩ subdivision.pathImage
      (paths e.val.1 e.val.2 e.property).support = {a} at hfront
    rw [hpoint] at hnot
    rw [himage, hpoint] at htail
    rw [himage] at hfront
    exact ⟨a,hnot,htail,hfront⟩
  choose incidence hincdata using hports
  have hincfront : ∀ e : I, incidence e ∈ frontier (Po e.val.1) ∩ original.line e.val.1 e.val.2 := by
    intro e
    rw [(hincdata e).2.2]
    exact mem_singleton _
  have hincP : ∀ e : I, incidence e ∈ Po e.val.1 := by
    intro e
    have hc : IsClosed (Po e.val.1) := (hPdata (vertex e.val.1)).2.1.isCompact.isClosed
    rw [← hc.closure_eq]
    exact frontier_subset_closure (hincfront e).1
  have hPsepO : Pairwise (fun u v => Disjoint (Po u) (Po v)) :=
    fun u v huv => hPsep (fun he => huv (hvinj he))
  have hincinj := incidence_tail_points_injective original Po incidence hPsepO hincP
    (fun e => (hincfront e).2) (fun e => (hincdata e).1)
  let incidenceArc := fun e : Arc N => if h : G.Adj e.1 e.2 then incidence ⟨e,h⟩ else original.pt e.1
  let orientation := fun p : Port N => if p.source then p.edge else (p.edge.2,p.edge.1)
  let port := fun p : Port N => incidenceArc (orientation p)
  have hport : ∀ p (h : G.Adj (orientation p).1 (orientation p).2),
      port p = incidence ⟨orientation p,h⟩ := by
    intro p h
    exact dite_eq_left h
  refine ⟨forestCellUnion Po R S, port, hD, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hm := interior_mono (hPsub v ((hS v).mpr hv)) (hPdata (vertex v)).2.2
    rw [hpoint] at hm
    exact hm
  · intro e hvp hu
    obtain ⟨u,v⟩ := e
    change T.parent v = some u at hvp
    have hv : T.Ancestor root v := hu.tail hvp
    have hinside := walk_pathImage_subset_interior_cells subdivision P Rs
      (fun a b h => (hlocal a b h).2.2.2.2) (paths u v (hT.2.1 _ _ hvp).1)
      (hnil _ _ _)
    rw [himage] at hinside
    apply hinside.trans
    apply interior_mono
    apply union_subset
    · apply union_subset (hPsub u ((hS u).mpr hu))
      have he : R v = tube ⟨(u,v),hvp⟩ := parentEdgeFamily_some T ∅ tube hvp
      have hs := hRsub v ((hS v).mpr hv)
      rw [he] at hs
      exact hs
    · exact hPsub v ((hS v).mpr hv)

  · intro p hp q hq he
    have hadj : ∀ p : Port N, T.BackEdge G p.edge → G.Adj (orientation p).1 (orientation p).2 := by
      intro p hb
      cases hs : p.source
      · simpa only [orientation, hs, Bool.false_eq_true, ite_false] using hb.1.symm
      · simpa only [orientation, hs, ite_true] using hb.1
    have hsame := (hport p (hadj p hp.1)).symm.trans (he.trans (hport q (hadj q hq.1)))
    have hi := @hincinj ⟨orientation p,hadj p hp.1⟩ ⟨orientation q,hadj q hq.1⟩ hsame
    exact backEdge_port_incidence_injOn hp.1 hq.1 (congrArg Subtype.val hi)
  · intro b hb hroots
    have hroott := root_ancestor_of_ancestor hroot hroots hb.2.1
    let e : I := ⟨b,hb.1⟩
    let f : I := ⟨(b.2,b.1),hb.1.symm⟩
    have htailA := (hincdata e).2.1
    have htailB := (hincdata f).2.1
    have hfrontA := (hincdata e).2.2
    have hfrontB := (hincdata f).2.2
    change Po b.1 ∩ original.line b.1 b.2 = segment ℝ (original.pt b.1) (incidence e) at htailA
    change Po b.2 ∩ original.line b.2 b.1 = segment ℝ (original.pt b.2) (incidence f) at htailB
    change frontier (Po b.1) ∩ original.line b.1 b.2 = {incidence e} at hfrontA
    change frontier (Po b.2) ∩ original.line b.2 b.1 = {incidence f} at hfrontB
    rw [original.line_comm b.2 b.1] at htailB hfrontB
    have hRavoid : ∀ v ∈ S, Disjoint (R v) (original.line b.1 b.2) := by
      intro v _
      cases hp : T.parent v with
      | none => rw [show R v = ∅ from parentEdgeFamily_none T ∅ tube hp]; exact empty_disjoint _
      | some u =>
        have heR : R v = tube ⟨(u,v),hp⟩ := parentEdgeFamily_some T ∅ tube hp
        rw [heR, ← himage b.1 b.2 hb.1]
        obtain ⟨hinternal, _, hedges⟩ := original_edge_subdivision_paths_separated original subdivision
          vertex hpoint (edge ⟨(u,v),hp⟩) hb.1 (backEdge_ne_parent_unordered hT hb hp).symm
          (path ⟨(u,v),hp⟩) (paths b.1 b.2 hb.1)
          (hpath _ _ _) (hpath _ _ _) (himage _ _ _) (himage _ _ _)
        exact walkTube_disjoint_pathImage subdivision P Rs hRother hPaway
          (path ⟨(u,v),hp⟩) (paths b.1 b.2 hb.1) hinternal hedges
    have hPoavoid : ∀ v, v ≠ b.1 → v ≠ b.2 → Disjoint (Po v) (original.line b.1 b.2) := by
      intro v hvs hvt
      rw [← himage b.1 b.2 hb.1]
      apply polygon_disjoint_walk_image subdivision P hPaway
      intro hvpath
      have hm := path_vertex_mem_pathImage subdivision (paths b.1 b.2 hb.1)
        (hpath _ _ _) (hnil _ _ _) hvpath
      rw [himage, hpoint] at hm
      exact (original.avoid _ (mem_univ _) _ (mem_univ _) hb.1 v (mem_univ _) hm).elim hvs hvt
    have hmeet : forestCellUnion Po R S ∩ original.line b.1 b.2 =
        (Po b.1 ∪ Po b.2) ∩ original.line b.1 b.2 := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨v,hv'⟩ := mem_iUnion.mp hx.1
        obtain ⟨hvS,hxv⟩ := mem_iUnion.mp hv'
        refine ⟨?_,hx.2⟩
        rcases hxv with hxP | hxR
        · by_cases hvs : v = b.1
          · exact Or.inl (hvs ▸ hxP)
          · by_cases hvt : v = b.2
            · exact Or.inr (hvt ▸ hxP)
            · exact (disjoint_left.mp (hPoavoid v hvs hvt) hxP hx.2).elim
        · exact (disjoint_left.mp (hRavoid v hvS) hxR hx.2).elim
      · intro x hx
        exact ⟨hx.1.elim (fun h => hPsub b.1 ((hS b.1).mpr hroots) h)
          (fun h => hPsub b.2 ((hS b.2).mpr hroott) h),hx.2⟩
    have hportBd : ∀ i : I, T.Ancestor root i.val.1 → original.line i.val.1 i.val.2 = original.line b.1 b.2 →
        incidence i ∈ frontier (forestCellUnion Po R S) := by
      intro i hi hline
      have hdisc := (hPdata (vertex i.val.1)).2.1
      have hbdP : discBd (Po i.val.1) = frontier (Po i.val.1) :=
        (subBd_eq_discBd_complex hdisc).symm.trans (Surface.subBd_eq_frontier _)
      have hm : incidence i ∈ discBd (forestCellUnion Po R S) := by
        apply hboundary i.val.1 ((hS _).mpr hi) {incidence i} ?_ ?_ (mem_singleton _)
        · rw [singleton_subset_iff,hbdP]
          exact (hincfront i).1
        · intro v hv
          rw [disjoint_singleton_left]
          intro hmem
          have hpL := (hincfront i).2
          rw [hline] at hpL
          exact disjoint_left.mp (hRavoid v hv) hmem hpL
      exact ((subBd_eq_discBd_complex hD).symm.trans (Surface.subBd_eq_frontier _)) ▸ hm
    have hAD := hPsub b.1 ((hS b.1).mpr hroots)
    have hBD := hPsub b.2 ((hS b.2).mpr hroott)
    have hsource : original.pt b.1 ∈ Po b.1 := by
      have hm := interior_subset (hPdata (vertex b.1)).2.2
      change subdivision.pt (vertex b.1) ∈ Po b.1 at hm
      rw [hpoint] at hm
      exact hm
    have htarget : original.pt b.2 ∈ Po b.2 := by
      have hm := interior_subset (hPdata (vertex b.2)).2.2
      change subdivision.pt (vertex b.2) ∈ Po b.2 at hm
      rw [hpoint] at hm
      exact hm
    have haD := hportBd e hroots rfl
    have hbD := hportBd f hroott (original.line_comm _ _)
    have hcut := cut_arc_at_polygon_ports
      (original.isLine _ (mem_univ _) _ (mem_univ _) hb.1)
      (hPdata (vertex b.1)).2.1.isCompact.isClosed (hPdata (vertex b.2)).2.1.isCompact.isClosed
      (hPsepO (G.ne_of_adj hb.1)) hsource htarget hAD hBD
      (by rw [htailA]; exact (convex_segment _ _).isPreconnected)
      (by rw [htailB]; exact (convex_segment _ _).isPreconnected)
      hfrontA hfrontB haD hbD hmeet
    have hps : port ⟨b,true⟩ = incidence e := hport ⟨b,true⟩ hb.1
    have hpt : port ⟨b,false⟩ = incidence f := hport ⟨b,false⟩ hb.1.symm
    rw [hps,hpt]
    exact ⟨haD,hbD,hcut.1,hcut.2⟩

/-- The tree-containment part of the exact subdivision neighborhood theorem. -/
theorem exists_subdivided_tree_disc {N : ℕ} {V : Type*} [Finite V]
    {G : SimpleGraph (Fin N)} {H : SimpleGraph V} {T : Forest N}
    (original : HP25.PlaneEmbedding G univ) (subdivision : HP25.PlaneEmbedding H univ)
    (hstraight : ∀ u v, H.Adj u v → subdivision.line u v = segment ℝ (subdivision.pt u) (subdivision.pt v))
    (vertex : Fin N → V) (hpoint : ∀ u, subdivision.pt (vertex u) = original.pt u)
    (paths : ∀ u v, G.Adj u v → H.Walk (vertex u) (vertex v))
    (hpath : ∀ u v h, (paths u v h).IsPath)
    (himage : ∀ u v h, subdivision.pathImage (paths u v h).support = original.line u v)
    (hT : T.IsDFS G) (root : Fin N) (hroot : T.parent root = none) :
    ∃ D : Set ℂ, IsClosedDisc D ∧
      (∀ v, T.Ancestor root v → original.pt v ∈ interior D) ∧
      (∀ u v, T.Ancestor root u → T.parent v = some u → original.line u v ⊆ interior D) := by
  obtain ⟨D,_,hD,hvertices,hlines,_,_⟩ := exists_subdivided_tree_neighborhood original subdivision
    hstraight vertex hpoint paths hpath himage hT root hroot
  exact ⟨D,hD,hvertices,fun u v hu hv => hlines (u,v) hv hu⟩

end GraphMinor.LRPlanarity
