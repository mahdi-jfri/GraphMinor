module

public import GraphMinor.HP25.Web
public import GraphMinor.Surface.ArcTools
public import Mathlib.Analysis.Convex.Segment
import GraphMinor.LRPlanarity.PolygonalizationMiddle
import GraphMinor.LRPlanarity.PolygonalizationRadial
import GraphMinor.LRPlanarity.PolygonalizationNeighborhoods
import GraphMinor.LRPlanarity.PolygonalizationTails
import GraphMinor.Surface.SurfaceGraph
import Mathlib.Topology.Algebra.Affine

/-!
# Simultaneous polygonal replacement of all edge images

Part IV, Section 7a of the planarity note uses the vertex discs to separate
radial tails, then separates the middle arcs from the other tails and all
vertices. Each edge is replaced inside its two tails and its own middle
neighborhood. These sets meet only at common original endpoints, so loop
erasure and polygonal approximation preserve all drawing conditions.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Metric Surface

/-- Part IV, Section 7a: replace all edge images by polygonal lines while
preserving the vertex points and the intersections permitted by the graph. -/
theorem exists_polygonal_edge_family {N : ℕ} {G : SimpleGraph (Fin N)}
    (drawing : HP25.PlaneEmbedding G univ) :
    let E := {e : Fin N × Fin N // G.Adj e.1 e.2 ∧ e.1 < e.2}
    ∃ L : E → Set ℂ,
      (∀ e, IsLineWithEnds (L e) (drawing.pt e.val.1) (drawing.pt e.val.2) ∧
        ∃ pieces : Finset (ℂ × ℂ), L e = ⋃ p ∈ pieces, segment ℝ p.1 p.2) ∧
      (∀ e f, e ≠ f → L e ∩ L f ⊆
        drawing.pt '' (({e.val.1, e.val.2} : Set (Fin N)) ∩ {f.val.1, f.val.2})) ∧
      ∀ e w, drawing.pt w ∈ L e → w = e.val.1 ∨ w = e.val.2 := by
  classical
  let E := {e : Fin N × Fin N // G.Adj e.1 e.2 ∧ e.1 < e.2}
  obtain ⟨r, source, target, M, hr, hdiscs, hdata, havoid, hMM, hnonincident⟩ :=
    exists_drawing_middle_arcs drawing
  let endpoint : E → Bool → Fin N := fun e side => if side then e.val.1 else e.val.2
  let port : E → Bool → ℂ := fun e side => if side then source e else target e
  let radial : E → Bool → Set ℂ := fun e side => segment ℝ (drawing.pt (endpoint e side)) (port e side)
  have end_mem : ∀ e side, endpoint e side ∈ ({e.val.1, e.val.2} : Set (Fin N)) := by
    intro e side
    cases side <;> simp [endpoint]
  have hport : ∀ e side, port e side ∈ sphere (drawing.pt (endpoint e side)) (r (endpoint e side)) := by
    intro e side
    cases side
    · exact (hdata e).2.1
    · exact (hdata e).1
  have hportM : ∀ e side, port e side ∈ M e := by
    intro e side
    cases side
    · exact (hdata e).2.2.1.right_mem
    · exact (hdata e).2.2.1.left_mem
  have hradD : ∀ e side, radial e side ⊆ closedBall (drawing.pt (endpoint e side)) (r (endpoint e side)) :=
    fun e side => radial_segment_subset_disc (hr _) (hport e side)
  have hradAvoid : ∀ e side w, drawing.pt w ∈ radial e side → w = endpoint e side := by
    intro e side w hw
    by_contra hne
    exact disjoint_left.mp (hdiscs w (endpoint e side) hne)
      (mem_closedBall_self (hr w).le) (hradD e side hw)
  have hradCross : ∀ e f : E, e ≠ f → ∀ side side', radial e side ∩ radial f side' ⊆
      drawing.pt '' (({e.val.1, e.val.2} : Set (Fin N)) ∩ {f.val.1, f.val.2}) := by
    intro e f hef side side' x hx
    by_cases he : endpoint e side = endpoint f side'
    · have hpneq : port e side ≠ port f side' := by
        intro hp
        exact disjoint_left.mp (hMM hef) (hportM e side) (hp ▸ hportM f side')
      have hsphere := hport f side'
      rw [← he] at hsphere
      have hi := radial_segments_inter (hr (endpoint e side)) (hport e side) hsphere hpneq
      have hm : x ∈ segment ℝ (drawing.pt (endpoint e side)) (port e side) ∩
          segment ℝ (drawing.pt (endpoint e side)) (port f side') := by
        simpa only [radial, he] using hx
      have hxcenter : x = drawing.pt (endpoint e side) := mem_singleton_iff.mp (hi ▸ hm)
      exact ⟨endpoint e side, ⟨end_mem e side, he ▸ end_mem f side'⟩, hxcenter.symm⟩
    · exact (disjoint_left.mp (hdiscs _ _ he) (hradD e side hx.1) (hradD f side' hx.2)).elim
  have hMrad : ∀ e f : E, e ≠ f → ∀ side, Disjoint (M e) (radial f side) := by
    intro e f hef side
    have hqM : port f side ∉ M e := fun hx => disjoint_left.mp (hMM hef) hx (hportM f side)
    have hq := hport f side
    by_cases hs : e.val.1 = endpoint f side
    · rw [← hs] at hq
      change Disjoint (M e) (segment ℝ (drawing.pt (endpoint f side)) (port f side))
      rw [← hs]
      exact disjoint_middle_radial_segment (hr _) (hdata e).1 hq (hdata e).2.2.2.2.1 hqM
    · by_cases ht : e.val.2 = endpoint f side
      · rw [← ht] at hq
        change Disjoint (M e) (segment ℝ (drawing.pt (endpoint f side)) (port f side))
        rw [← ht]
        exact disjoint_middle_radial_segment (hr _) (hdata e).2.1 hq (hdata e).2.2.2.2.2 hqM
      · exact (hnonincident e (endpoint f side) hs ht).mono_right (hradD f side)
  have hradCompact : ∀ e side, IsCompact (radial e side) := by
    intro e side
    change IsCompact (segment ℝ _ _)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  let F : E → Set ℂ := fun e => range drawing.pt ∪ ⋃ f : E, ⋃ side : Bool,
    if f = e then ∅ else radial f side
  have hFc : ∀ e, IsClosed (F e) := by
    intro e
    apply IsCompact.isClosed
    apply (finite_range drawing.pt).isCompact.union
    apply isCompact_iUnion
    intro f
    apply isCompact_iUnion
    intro side
    split_ifs
    · exact isCompact_empty
    · exact hradCompact f side
  have hMF : ∀ e, Disjoint (M e) (F e) := by
    intro e
    apply disjoint_left.mpr
    rintro x hx (⟨w, rfl⟩ | hy)
    · exact havoid e w hx
    · obtain ⟨f, hy⟩ := mem_iUnion.mp hy
      obtain ⟨side, hy⟩ := mem_iUnion.mp hy
      by_cases he : f = e
      · simp only [he, ↓reduceIte, mem_empty_iff_false] at hy
      · have hm : x ∈ radial f side := by simpa only [he, ↓reduceIte] using hy
        exact disjoint_left.mp (hMrad e f (fun h => he h.symm) side) hx hm
  obtain ⟨δ, hδ, hUU⟩ := exists_disjoint_middle_neighborhoods M F
    (fun e => (hdata e).2.2.1.isCompact) hMM hFc hMF
  let U : E → Set ℂ := fun e => thickening (δ e) (M e)
  have hUM : ∀ e, M e ⊆ U e := fun e => self_subset_thickening (hδ e).1 _
  have hUvertices : ∀ e w, drawing.pt w ∉ U e := by
    intro e w hw
    exact disjoint_left.mp (hδ e).2 hw (Or.inl (mem_range_self w))
  have hUrad : ∀ e f : E, e ≠ f → ∀ side, Disjoint (U e) (radial f side) := by
    intro e f hef side
    apply (hδ e).2.mono_right
    intro x hx
    exact Or.inr (mem_iUnion.mpr ⟨f, mem_iUnion.mpr
      ⟨side, by simpa only [hef.symm, ↓reduceIte] using hx⟩⟩)
  let support : E → Set ℂ := fun e => radial e true ∪ U e ∪ radial e false
  have hsupportAvoid : ∀ e w, drawing.pt w ∈ support e → w = e.val.1 ∨ w = e.val.2 := by
    intro e w hw
    rcases hw with (hw | hw) | hw
    · exact Or.inl (hradAvoid e true w hw)
    · exact (hUvertices e w hw).elim
    · exact Or.inr (hradAvoid e false w hw)
  have hsupportCross : ∀ e f : E, e ≠ f → support e ∩ support f ⊆
      drawing.pt '' (({e.val.1, e.val.2} : Set (Fin N)) ∩ {f.val.1, f.val.2}) := by
    intro e f hef x hx
    rcases hx with ⟨(hx | hx) | hx, (hy | hy) | hy⟩
    · exact hradCross e f hef true true ⟨hx, hy⟩
    · exact (disjoint_left.mp (hUrad f e hef.symm true) hy hx).elim
    · exact hradCross e f hef true false ⟨hx, hy⟩
    · exact (disjoint_left.mp (hUrad e f hef true) hx hy).elim
    · exact (disjoint_left.mp (hUU hef) hx hy).elim
    · exact (disjoint_left.mp (hUrad e f hef false) hx hy).elim
    · exact hradCross e f hef false true ⟨hx, hy⟩
    · exact (disjoint_left.mp (hUrad f e hef.symm false) hy hx).elim
    · exact hradCross e f hef false false ⟨hx, hy⟩
  have hreplace : ∀ e : E, ∃ L : Set ℂ,
      IsLineWithEnds L (drawing.pt e.val.1) (drawing.pt e.val.2) ∧ L ⊆ support e ∧
      ∃ pieces : Finset (ℂ × ℂ), L = ⋃ p ∈ pieces, segment ℝ p.1 p.2 := by
    intro e
    obtain ⟨f, hf, hrange, hf0, hf1⟩ := (hdata e).2.2.1.exists_arc
    have hfU : range f ⊆ U e := hrange ▸ hUM e
    have hne : drawing.pt e.val.1 ≠ drawing.pt e.val.2 := fun he =>
      e.property.2.ne (drawing.injOn (mem_univ _) (mem_univ _) he)
    obtain ⟨L, hL, hsub, pieces, hpieces⟩ := exists_polygonal_arc_with_tails hf.1
      isOpen_thickening hfU (drawing.pt e.val.1) (drawing.pt e.val.2) hne
    refine ⟨L, hL, ?_, pieces, hpieces⟩
    simpa [hf0, hf1, support, radial, endpoint, port, U,
      segment_symm ℝ (target e) (drawing.pt e.val.2)] using hsub
  choose L hL hsub pieces hpieces using hreplace
  refine ⟨L, fun e => ⟨hL e, pieces e, hpieces e⟩, ?_, ?_⟩
  · intro e f hef x hx
    exact hsupportCross e f hef ⟨hsub e hx.1, hsub f hx.2⟩
  · intro e w hw
    exact hsupportAvoid e w (hsub e hw)

end GraphMinor.LRPlanarity
