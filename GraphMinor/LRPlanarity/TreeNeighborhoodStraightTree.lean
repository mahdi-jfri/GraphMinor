module

public import GraphMinor.LRPlanarity.DefsContour
public import GraphMinor.HP25.Web
import GraphMinor.LRPlanarity.TreeNeighborhoodParentFamily
import GraphMinor.LRPlanarity.TreeNeighborhoodDrawingPolygons
import GraphMinor.LRPlanarity.TreeNeighborhoodDrawingStrips
import GraphMinor.LRPlanarity.TreeNeighborhoodLeafOrder
import GraphMinor.LRPlanarity.TreeNeighborhoodUnion
import GraphMinor.LRPlanarity.TreeNeighborhoodPorts
import GraphMinor.LRPlanarity.TreeNeighborhoodCotree
import GraphMinor.LRPlanarity.TreeNeighborhoodCut
import GraphMinor.LRPlanarity.TreeNeighborhoodCenterlines
import GraphMinor.Surface.DiscUnion
import GraphMinor.Surface.PlaneOrientation
import Mathlib.Tactic.Linarith

/-!
# A neighborhood of a straight drawn search tree

Part IV, Section 7b of the planarity note places vertex polygons and
parent strips, then glues them in tree order. Here the polygons and strips
are constructed from the straight drawing, so the disc conclusion has no
local geometric configuration hypotheses. Each vertex lies in its polygon
interior, and each parent edge lies inside its two polygons and strip.
Cotree edges miss all strips and nonincident polygons. Their facet ports
survive on the final boundary, and cutting at those ports leaves one
exterior line.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b, for straight drawings: a closed disc contains the
rooted drawn tree in its interior, and its boundary cuts each cotree edge
at two distinct ports, leaving one exterior line. -/
theorem exists_straight_tree_neighborhood {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (drawing : HP25.PlaneEmbedding G univ) (hT : T.IsDFS G)
    (hstraight : ∀ u v, G.Adj u v →
      drawing.line u v = segment ℝ (drawing.pt u) (drawing.pt v))
    (root : Fin N) (hroot : T.parent root = none) :
    ∃ (D : Set ℂ) (port : Port N → ℂ), IsClosedDisc D ∧
      (∀ v, T.Ancestor root v → drawing.pt v ∈ interior D) ∧
      (∀ e, T.TreeEdge e → T.Ancestor root e.1 → drawing.line e.1 e.2 ⊆ interior D) ∧
      InjOn port {p | T.BackEdge G p.edge ∧ T.Ancestor root p.edge.1} ∧
      (∀ b, T.BackEdge G b → T.Ancestor root b.1 →
        port ⟨b, true⟩ ∈ frontier D ∧ port ⟨b, false⟩ ∈ frontier D ∧
        IsLineWithEnds (drawing.line b.1 b.2 \ interior D)
          (port ⟨b, true⟩) (port ⟨b, false⟩) ∧
        (drawing.line b.1 b.2 \ interior D) ∩ D =
          {port ⟨b, true⟩, port ⟨b, false⟩}) := by
  classical
  obtain ⟨angle, directions, r, hangle, hnormal, hmem, hPdata, hPsep, hlength, hPaway⟩ :=
    exists_straight_drawing_vertex_polygons drawing hstraight
  let P := fun v => vertexPolygonAt (drawing.pt v) (directions v) (r v)
  let E := {e : Fin N × Fin N // T.parent e.2 = some e.1}
  let source : E → Fin N := fun e => e.val.1
  let target : E → Fin N := fun e => e.val.2
  have hedge : ∀ e : E, G.Adj (source e) (target e) :=
    fun e => (hT.2.1 e.val.1 e.val.2 e.property).1
  obtain ⟨width, hw, hsep, haway, hlineavoid, hlocal⟩ := exists_straight_drawing_strips
    drawing hstraight source target hedge (parent_edge_unordered_injective hT)
    angle directions r hangle hmem (fun v => (hPdata v).1) hlength
    (fun e w hws hwt => hPaway w _ _ (hedge e) hws.symm hwt.symm)
  let Rf := fun e : E => orientedStrip (drawing.pt (source e))
    (angle (source e) ⟨target e, hedge e⟩) (r (source e))
    (‖drawing.pt (target e) - drawing.pt (source e)‖ - r (target e)) (width e)
  choose Lf Kf af bf cf df hgeometry using hlocal
  let R := parentEdgeFamily T ∅ Rf
  let L := parentEdgeFamily T ∅ Lf
  let K := parentEdgeFamily T ∅ Kf
  let a := parentEdgeFamily T 0 af
  let b := parentEdgeFamily T 0 bf
  let c := parentEdgeFamily T 0 cf
  let d := parentEdgeFamily T 0 df
  have hR : ∀ v p (hp : T.parent v = some p), R v = Rf ⟨(p, v), hp⟩ := by
    intro v p hp
    exact parentEdgeFamily_some T ∅ Rf hp
  have hRsep : Pairwise (fun u v => Disjoint (R u) (R v)) := by
    intro u v huv
    cases hu : T.parent u with
    | none => rw [show R u = ∅ from parentEdgeFamily_none T ∅ Rf hu]; exact empty_disjoint _
    | some p =>
      cases hv : T.parent v with
      | none => rw [show R v = ∅ from parentEdgeFamily_none T ∅ Rf hv]; exact disjoint_empty _
      | some q =>
        rw [hR u p hu, hR v q hv]
        apply hsep
        intro he
        exact huv (congrArg (fun e : E => e.val.2) he)
  have hlocal' : ∀ v p, T.parent v = some p →
      IsClosedDisc (R v) ∧ IsLineWithEnds (L v) (a v) (b v) ∧
      IsLineWithEnds (K v) (c v) (d v) ∧ P p ∩ R v = L v ∧ R v ∩ P v = K v ∧
      L v ⊆ discBd (P p) ∧ L v ⊆ discBd (R v) ∧
      K v ⊆ discBd (R v) ∧ K v ⊆ discBd (P v) := by
    intro v p hp
    dsimp only [L, K, a, b, c, d]
    rw [hR v p hp, parentEdgeFamily_some T ∅ Lf hp, parentEdgeFamily_some T ∅ Kf hp,
      parentEdgeFamily_some T 0 af hp, parentEdgeFamily_some T 0 bf hp,
      parentEdgeFamily_some T 0 cf hp, parentEdgeFamily_some T 0 df hp]
    have h := hgeometry (⟨(p,v), hp⟩ : E)
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩
  let S := Finset.univ.filter (T.Ancestor root)
  have hS : ∀ v, v ∈ S ↔ T.Ancestor root v := by intro v; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hrootS : root ∈ S := (hS root).mpr Relation.ReflTransGen.refl
  have hparentS : ∀ v ∈ S, v ≠ root → ∃ p ∈ S, T.parent v = some p := by
    intro v hv hvr
    obtain ⟨p, hp, hvp⟩ := ancestor_parent_of_ne ((hS v).mp hv) hvr
    exact ⟨p, (hS p).mpr hp, hvp⟩
  have haway' : ∀ v p, T.parent v = some p → ∀ w, w ≠ v → w ≠ p → Disjoint (R v) (P w) := by
    intro v p hp w hwv hwp
    rw [hR v p hp]
    exact haway (⟨(p,v), hp⟩ : E) w hwp hwv
  obtain ⟨hD, hboundary⟩ := forestCellUnion_isClosedDisc hT root P R L K a b c d
    (fun v => (hPdata v).2.1) hPsep (parentEdgeFamily_none T ∅ Rf hroot)
    hRsep hlocal' haway' S hrootS (fun v hv => (hS v).mp hv) hparentS
  have hPsub : ∀ v ∈ S, P v ⊆ forestCellUnion P R S := by
    intro v hv x hx
    exact mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, Or.inl hx⟩⟩
  have hRsub : ∀ v ∈ S, R v ⊆ forestCellUnion P R S := by
    intro v hv x hx
    exact mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, Or.inr hx⟩⟩
  let incidence : Arc N → ℂ := fun e => if h : G.Adj e.1 e.2 then
    drawing.pt e.1 + r e.1 • eC (angle e.1 ⟨e.2, h⟩) else drawing.pt e.1
  let orientation := fun p : Port N => if p.source then p.edge else (p.edge.2, p.edge.1)
  let port := fun p : Port N => incidence (orientation p)
  have hincidence : ∀ e (h : G.Adj e.1 e.2), incidence e =
      drawing.pt e.1 + r e.1 • eC (angle e.1 ⟨e.2, h⟩) := by
    intro e h
    exact dite_eq_left h
  refine ⟨forestCellUnion P R S, port, hD, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact interior_mono (hPsub v ((hS v).mpr hv)) (hPdata v).2.2
  · intro e hvu hu
    obtain ⟨u,v⟩ := e
    change T.parent v = some u at hvu
    have hv : T.Ancestor root v := hu.tail hvu
    have h := (hgeometry (⟨(u,v), hvu⟩ : E)).2.2.2.2.2.2.2.2.2
    apply h.trans
    apply interior_mono
    apply union_subset
    · exact union_subset (hPsub u ((hS u).mpr hu))
        (by
          change Rf ⟨(u,v), hvu⟩ ⊆ forestCellUnion P R S
          rw [← hR v u hvu]
          exact hRsub v ((hS v).mpr hv))
    · exact hPsub v ((hS v).mpr hv)

  · intro p hp q hq he
    have hadj : ∀ p : Port N, T.BackEdge G p.edge →
        G.Adj (orientation p).1 (orientation p).2 := by
      intro p hb
      cases hs : p.source
      · simpa only [orientation, hs, Bool.false_eq_true, ite_false] using hb.1.symm
      · simpa only [orientation, hs, ite_true] using hb.1
    have hpi := hincidence (orientation p) (hadj p hp.1)
    have hqi := hincidence (orientation q) (hadj q hq.1)
    have hsame := hpi.symm.trans (he.trans hqi)
    have hinj := vertex_facet_points_injective drawing.pt angle directions r
      (fun v => (hPdata v).1) hmem hnormal hPsep
    have hindex := @hinj ⟨orientation p, hadj p hp.1⟩ ⟨orientation q, hadj q hq.1⟩ hsame
    exact backEdge_port_incidence_injOn hp.1 hq.1 (congrArg Subtype.val hindex)
  · intro b hb hroots
    have hroott := root_ancestor_of_ancestor hroot hroots hb.2.1
    let μ := angle b.1 ⟨b.2, hb.1⟩
    let ν := angle b.2 ⟨b.1, hb.1.symm⟩
    let len := ‖drawing.pt b.2 - drawing.pt b.1‖
    have hptne : drawing.pt b.1 ≠ drawing.pt b.2 := by
      intro he
      exact (G.ne_of_adj hb.1) (drawing.injOn (mem_univ _) (mem_univ _) he)
    have hlen : 0 < len := norm_pos_iff.mpr (sub_ne_zero.mpr hptne.symm)
    have hsum : r b.1 + r b.2 < len := by
      simpa only [len, dist_eq_norm, norm_sub_rev] using hlength b.1 b.2 (G.ne_of_adj hb.1)
    have hcoord : drawing.pt b.1 + eC μ * (len : ℂ) = drawing.pt b.2 :=
      endpoint_eq_direction_length hptne (hangle _ _)
    have hop : eC ν = -eC μ := by
      have h := opposite_normal_angles (hangle b.1 ⟨b.2, hb.1⟩)
        (hangle b.2 ⟨b.1, hb.1.symm⟩)
      change eC ν = eC (μ + Real.pi) at h
      rw [h]
      apply Complex.ext
      · rw [eC_re, Complex.neg_re, eC_re, Real.cos_add_pi]
      · rw [eC_im, Complex.neg_im, eC_im, Real.sin_add_pi]
    have havoid : ∀ v ∈ S, Disjoint (R v) (drawing.line b.1 b.2) := by
      intro v _
      cases hp : T.parent v with
      | none => rw [show R v = ∅ from parentEdgeFamily_none T ∅ Rf hp]; exact empty_disjoint _
      | some p =>
        rw [hR v p hp]
        exact hlineavoid (⟨(p,v), hp⟩ : E) b.1 b.2 hb.1
          (backEdge_ne_parent_unordered hT hb hp)
    have hsource : drawing.pt b.1 + r b.1 • eC μ ∈ drawing.line b.1 b.2 := by
      rw [hstraight _ _ hb.1, ← hcoord]
      have he : drawing.pt b.1 + r b.1 • eC μ = drawing.pt b.1 + eC μ * (r b.1 : ℂ) := by
        rw [Complex.real_smul, mul_comm]
      rw [he]
      exact stripCenterline_subset_segment (drawing.pt b.1) μ hlen le_rfl le_rfl
        ⟨r b.1, ⟨(hPdata b.1).1.le, by linarith [(hPdata b.2).1]⟩, rfl⟩
    have htargeteq : drawing.pt b.1 + eC μ * ((len - r b.2 : ℝ) : ℂ) =
        drawing.pt b.2 + r b.2 • eC ν := by
      rw [← hcoord, hop, Complex.real_smul]
      push_cast
      ring
    have htarget : drawing.pt b.2 + r b.2 • eC ν ∈ drawing.line b.1 b.2 := by
      rw [← htargeteq, hstraight _ _ hb.1, ← hcoord]
      exact stripCenterline_subset_segment _ _ hlen le_rfl le_rfl
        ⟨len - r b.2, ⟨by linarith [(hPdata b.1).1], sub_le_self _ (hPdata b.2).1.le⟩, rfl⟩
    have hportBd : ∀ u ∈ S, ∀ θ, θ ∈ directions u →
        drawing.pt u + r u • eC θ ∈ drawing.line b.1 b.2 →
        drawing.pt u + r u • eC θ ∈ discBd (forestCellUnion P R S) := by
      intro u hu θ hθ hline
      apply hboundary u hu {drawing.pt u + r u • eC θ} ?_ ?_ (mem_singleton _)
      · exact singleton_subset_iff.mpr
          (vertexPolygonAt_direction_mem_discBd _ _ (hPdata u).1 hθ)
      · intro v hv
        rw [disjoint_singleton_left]
        exact fun hm => disjoint_left.mp (havoid v hv) hm hline
    have hfront : discBd (forestCellUnion P R S) = frontier (forestCellUnion P R S) :=
      (subBd_eq_discBd_complex hD).symm.trans (Surface.subBd_eq_frontier _)
    have hfronts := hportBd b.1 ((hS b.1).mpr hroots) μ (hmem _ _) hsource
    have hfrontt := hportBd b.2 ((hS b.2).mpr hroott) ν (hmem _ _) htarget
    rw [hfront] at hfronts hfrontt
    have hsrc : drawing.pt b.1 + eC μ * (r b.1 : ℂ) = drawing.pt b.1 + r b.1 • eC μ := by
      rw [Complex.real_smul, mul_comm]
    obtain ⟨hmeet, hinside⟩ := cotree_edge_union_coordinates drawing.pt directions r R S
      b.1 b.2 ((hS b.1).mpr hroots) ((hS b.2).mpr hroott) μ ν len hlen hcoord hop
      (hmem _ _) (hmem _ _)
      (by simpa only [← hstraight _ _ hb.1] using havoid)
      (fun v hv hvs hvt => by
        rw [← hstraight _ _ hb.1]
        exact hPaway v b.1 b.2 hb.1 hvs.symm hvt.symm)
    have hcut := cut_straight_edge_at_ports (forestCellUnion P R S) (drawing.pt b.1)
      μ len (r b.1) (len - r b.2) hD.isCompact.isClosed (hPdata b.1).1.le
      (by linarith) (sub_le_self _ (hPdata b.2).1.le)
      (hsrc.symm ▸ hfronts) (htargeteq.symm ▸ hfrontt) hmeet hinside
    rw [hcoord, ← hstraight _ _ hb.1, hsrc, htargeteq] at hcut
    have hps : port ⟨b, true⟩ = drawing.pt b.1 + r b.1 • eC μ := by
      change incidence b = _
      exact hincidence b hb.1
    have hpt : port ⟨b, false⟩ = drawing.pt b.2 + r b.2 • eC ν := by
      change incidence (b.2,b.1) = _
      exact hincidence (b.2,b.1) hb.1.symm
    rw [hps, hpt]
    exact ⟨hfronts, hfrontt, hcut.1, hcut.2⟩

/-- The tree-containment part of the straight neighborhood construction. -/
theorem exists_straight_tree_disc {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (drawing : HP25.PlaneEmbedding G univ) (hT : T.IsDFS G)
    (hstraight : ∀ u v, G.Adj u v →
      drawing.line u v = segment ℝ (drawing.pt u) (drawing.pt v))
    (root : Fin N) (hroot : T.parent root = none) :
    ∃ D : Set ℂ, IsClosedDisc D ∧
      (∀ v, T.Ancestor root v → drawing.pt v ∈ interior D) ∧
      (∀ u v, T.Ancestor root u → T.parent v = some u →
        drawing.line u v ⊆ interior D) := by
  obtain ⟨D, _, hD, hvertices, hlines, _, _⟩ :=
    exists_straight_tree_neighborhood drawing hT hstraight root hroot
  exact ⟨D, hD, hvertices, fun u v hu hv => hlines (u,v) hv hu⟩

end GraphMinor.LRPlanarity
