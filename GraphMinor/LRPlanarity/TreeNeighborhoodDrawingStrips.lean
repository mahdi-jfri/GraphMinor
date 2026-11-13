module

public import GraphMinor.LRPlanarity.TreeNeighborhoodStripCoordinates
public import GraphMinor.HP25.Web
import GraphMinor.LRPlanarity.TreeNeighborhoodTwoEnds
import GraphMinor.LRPlanarity.TreeNeighborhoodInteriors
import GraphMinor.LRPlanarity.TreeNeighborhoodCenterlines
import GraphMinor.LRPlanarity.TreeNeighborhoodStripSeparation
import GraphMinor.Surface.DiscUnion
import Mathlib.Topology.Algebra.Affine

/-!
# Separated strips along a straight drawing

Part IV, Section 7b of the planarity note chooses all strip widths at once.
The centerlines are shortened straight edges. Their compactness and their
separation from other edges and nonincident polygons give disjoint metric
neighborhoods. Widths below both endpoint facet bounds then give exact
attachment intervals at both ends and no other intersections.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: from vertex polygons with the stated normal and
separation properties, construct all thin strips. The output includes exact
attachment data and avoidance of every other drawing edge. -/
theorem exists_straight_drawing_strips {V ι : Type*} [Finite V] [Finite ι]
    {G : SimpleGraph V} (drawing : HP25.PlaneEmbedding G univ)
    (hstraight : ∀ u v, G.Adj u v →
      drawing.line u v = segment ℝ (drawing.pt u) (drawing.pt v))
    (source target : ι → V) (hedge : ∀ i, G.Adj (source i) (target i))
    (hindex : Function.Injective (fun i => s(source i, target i)))
    (angle : ∀ u, {v // G.Adj u v} → ℝ) (directions : V → Finset ℝ) (r : V → ℝ)
    (hangle : ∀ u v, eC (angle u v) =
      ‖drawing.pt v.val - drawing.pt u‖⁻¹ • (drawing.pt v.val - drawing.pt u))
    (hmem : ∀ u v, angle u v ∈ directions u) (hr : ∀ u, 0 < r u)
    (hlength : ∀ u v, u ≠ v → r u + r v < dist (drawing.pt u) (drawing.pt v))
    (haway : ∀ i w, w ≠ source i → w ≠ target i → Disjoint
      (vertexPolygonAt (drawing.pt w) (directions w) (r w))
      (drawing.line (source i) (target i))) :
    let μ := fun i => angle (source i) ⟨target i, hedge i⟩
    let len := fun i => ‖drawing.pt (target i) - drawing.pt (source i)‖
    ∃ width : ι → ℝ,
      (∀ i, 0 < width i) ∧
      Pairwise (fun i j => Disjoint
        (orientedStrip (drawing.pt (source i)) (μ i) (r (source i))
          (len i - r (target i)) (width i))
        (orientedStrip (drawing.pt (source j)) (μ j) (r (source j))
          (len j - r (target j)) (width j))) ∧
      (∀ i w, w ≠ source i → w ≠ target i → Disjoint
        (orientedStrip (drawing.pt (source i)) (μ i) (r (source i))
          (len i - r (target i)) (width i))
        (vertexPolygonAt (drawing.pt w) (directions w) (r w))) ∧
      (∀ i u v, G.Adj u v → s(u, v) ≠ s(source i, target i) → Disjoint
        (orientedStrip (drawing.pt (source i)) (μ i) (r (source i))
          (len i - r (target i)) (width i)) (drawing.line u v)) ∧
      ∀ i, ∃ (L K : Set ℂ) (a b c d : ℂ),
        IsClosedDisc (orientedStrip (drawing.pt (source i)) (μ i) (r (source i))
          (len i - r (target i)) (width i)) ∧
        IsLineWithEnds L a b ∧ IsLineWithEnds K c d ∧
        vertexPolygonAt (drawing.pt (source i)) (directions (source i)) (r (source i)) ∩
          orientedStrip (drawing.pt (source i)) (μ i) (r (source i))
            (len i - r (target i)) (width i) = L ∧
        orientedStrip (drawing.pt (source i)) (μ i) (r (source i))
          (len i - r (target i)) (width i) ∩
          vertexPolygonAt (drawing.pt (target i)) (directions (target i)) (r (target i)) = K ∧
        L ⊆ discBd (vertexPolygonAt (drawing.pt (source i)) (directions (source i)) (r (source i))) ∧
        L ⊆ discBd (orientedStrip (drawing.pt (source i)) (μ i) (r (source i))
          (len i - r (target i)) (width i)) ∧
        K ⊆ discBd (orientedStrip (drawing.pt (source i)) (μ i) (r (source i))
          (len i - r (target i)) (width i)) ∧
        K ⊆ discBd (vertexPolygonAt (drawing.pt (target i)) (directions (target i)) (r (target i))) ∧
        drawing.line (source i) (target i) ⊆ interior
          (vertexPolygonAt (drawing.pt (source i)) (directions (source i)) (r (source i)) ∪
            orientedStrip (drawing.pt (source i)) (μ i) (r (source i))
              (len i - r (target i)) (width i) ∪
            vertexPolygonAt (drawing.pt (target i)) (directions (target i)) (r (target i))) := by
  classical
  intro μ len
  let ν := fun i => angle (target i) ⟨source i, (hedge i).symm⟩
  let P := fun u => vertexPolygonAt (drawing.pt u) (directions u) (r u)
  let C := fun i => stripCenterline (drawing.pt (source i)) (μ i)
    (r (source i)) (len i - r (target i))
  have hpt : ∀ i, drawing.pt (source i) ≠ drawing.pt (target i) := by
    intro i he
    exact (G.ne_of_adj (hedge i)) (drawing.injOn (mem_univ _) (mem_univ _) he)
  have hlen : ∀ i, r (source i) + r (target i) < len i := by
    intro i
    simpa only [len, dist_eq_norm, norm_sub_rev] using
      hlength (source i) (target i) (G.ne_of_adj (hedge i))
  have hcoord : ∀ i, drawing.pt (source i) + eC (μ i) * (len i : ℂ) = drawing.pt (target i) :=
    fun i => endpoint_eq_direction_length (hpt i) (hangle _ _)
  have hbounds : ∀ i, ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 < w → w ≤ δ →
      ∃ (L K : Set ℂ) (a b c d : ℂ),
        IsClosedDisc (orientedStrip (drawing.pt (source i)) (μ i) (r (source i)) (len i - r (target i)) w) ∧
        IsLineWithEnds L a b ∧ IsLineWithEnds K c d ∧
        P (source i) ∩ orientedStrip (drawing.pt (source i)) (μ i) (r (source i)) (len i - r (target i)) w = L ∧
        orientedStrip (drawing.pt (source i)) (μ i) (r (source i)) (len i - r (target i)) w ∩ P (target i) = K ∧
        L ⊆ discBd (P (source i)) ∧
        L ⊆ discBd (orientedStrip (drawing.pt (source i)) (μ i) (r (source i)) (len i - r (target i)) w) ∧
        K ⊆ discBd (orientedStrip (drawing.pt (source i)) (μ i) (r (source i)) (len i - r (target i)) w) ∧
        K ⊆ discBd (P (target i)) := by
    intro i
    have h := exists_two_end_attachment_bound (drawing.pt (source i)) (μ i) (ν i) (len i)
      (directions (source i)) (directions (target i)) (hr _) (hr _) (hlen i)
      (hmem _ _) (hmem _ _) (opposite_normal_angles (hangle _ _) (hangle _ _))
    rw [hcoord i] at h
    exact h
  choose bound₀ hbound₀ hlocal using hbounds
  have hinside : ∀ i, ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 < w → w ≤ δ →
      drawing.line (source i) (target i) ⊆ interior
        (P (source i) ∪ orientedStrip (drawing.pt (source i)) (μ i)
          (r (source i)) (len i - r (target i)) w ∪ P (target i)) := by
    intro i
    have h := exists_two_end_interior_bound (drawing.pt (source i)) (μ i) (ν i) (len i)
      (directions (source i)) (directions (target i)) (hr _) (hr _) (hlen i)
      (hmem _ _) (hmem _ _) (opposite_normal_angles (hangle _ _) (hangle _ _))
    rw [hcoord i, ← hstraight _ _ (hedge i)] at h
    exact h
  choose bound₁ hbound₁ hinterior using hinside
  let bound := fun i => min (bound₀ i) (bound₁ i)
  have hbound : ∀ i, 0 < bound i := fun i => lt_min (hbound₀ i) (hbound₁ i)
  have hCline : ∀ i, C i ⊆ drawing.line (source i) (target i) := by
    intro i
    rw [hstraight _ _ (hedge i), ← hcoord i]
    exact stripCenterline_subset_segment _ _
      (norm_pos_iff.mpr (sub_ne_zero.mpr (hpt i).symm)) (hr _).le (sub_le_self _ (hr _).le)
  have hCends : ∀ i, drawing.pt (source i) ∉ C i ∧ drawing.pt (target i) ∉ C i := by
    intro i
    rw [← hcoord i]
    exact stripCenterline_avoids_ends _ _ (hr _) (sub_lt_self _ (hr _))
  have hCsep := shortened_drawing_edges_disjoint drawing source target hedge hindex C hCline
    (fun i => (hCends i).1) (fun i => (hCends i).2)
  let F := fun i => (⋃ w : {w // w ≠ source i ∧ w ≠ target i}, P w.val) ∪
    ⋃ e : {e : V × V // G.Adj e.1 e.2 ∧ s(e.1, e.2) ≠ s(source i, target i)},
      drawing.line e.val.1 e.val.2
  have hF : ∀ i, IsClosed (F i) := by
    intro i
    apply IsClosed.union
    · apply isClosed_iUnion_of_finite
      intro w
      exact (vertexPolygonAt_isClosedDisc _ _ (hr w.val)).isCompact.isClosed
    · apply isClosed_iUnion_of_finite
      intro e
      rw [hstraight _ _ e.property.1, segment_eq_image]
      exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hCF : ∀ i, Disjoint (C i) (F i) := by
    intro i
    rw [disjoint_left]
    intro x hx hFmem
    rcases hFmem with hpoly | hedge'
    · obtain ⟨w, hw⟩ := mem_iUnion.mp hpoly
      exact disjoint_left.mp (haway i w.val w.property.1 w.property.2) hw (hCline i hx)
    · obtain ⟨e, he⟩ := mem_iUnion.mp hedge'
      have hm := drawing.inter _ (mem_univ _) _ (mem_univ _) _ (mem_univ _) _ (mem_univ _)
        (hedge i) e.property.1 e.property.2.symm ⟨hCline i hx, he⟩
      obtain ⟨v, hv, hvx⟩ := hm
      rcases hv.1 with hv | hv
      · subst v
        exact (hCends i).1 (hvx ▸ hx)
      · subst v
        exact (hCends i).2 (hvx ▸ hx)
  obtain ⟨width, hw, hsep⟩ := exists_separated_thin_strips
    (fun i => drawing.pt (source i)) μ (fun i => r (source i))
    (fun i => len i - r (target i)) bound F
    (fun i => lt_sub_iff_add_lt.mpr (hlen i)) hbound hCsep hF hCF
  refine ⟨width, fun i => (hw i).1, hsep, ?_, ?_, ?_⟩
  · intro i w hws hwt
    apply (hw i).2.2.2.mono_right
    intro x hx
    exact Or.inl (mem_iUnion.mpr
      ⟨(⟨w, hws, hwt⟩ : {w // w ≠ source i ∧ w ≠ target i}), hx⟩)
  · intro i u v huv hne
    apply (hw i).2.2.2.mono_right
    intro x hx
    exact Or.inr (mem_iUnion.mpr
      ⟨(⟨(u,v), huv, hne⟩ : {e : V × V // G.Adj e.1 e.2 ∧
        s(e.1, e.2) ≠ s(source i, target i)}), hx⟩)
  · intro i
    have hw₀ : width i ≤ bound₀ i := (hw i).2.1.trans (min_le_left _ _)
    have hw₁ : width i ≤ bound₁ i := (hw i).2.1.trans (min_le_right _ _)
    obtain ⟨L, K, a, b, c, d, hS, hL, hK, hI, hJ, hLP, hLS, hKS, hKP⟩ :=
      hlocal i (width i) (hw i).1 hw₀
    exact ⟨L, K, a, b, c, d, hS, hL, hK, hI, hJ, hLP, hLS, hKS, hKP,
      hinterior i (width i) (hw i).1 hw₁⟩

end GraphMinor.LRPlanarity
