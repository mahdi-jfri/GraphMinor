module

public import GraphMinor.LRPlanarity.TreeNeighborhoodStripCoordinates
import GraphMinor.LRPlanarity.TreeNeighborhoodGluing

/-!
# One strip attached at both vertex polygons

Part IV, Section 7b of the planarity note makes each strip thin enough for
both endpoint facets. Take the smaller of the two local width bounds.
Reversing the coordinates identifies the second local rectangle with the
first. The strip then meets both polygons in boundary intervals, and the
two disc gluings give a closed disc whenever the two polygons are disjoint.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: one common positive width bound makes a straight
strip join two disjoint endpoint polygons into a closed disc. -/
theorem exists_two_vertex_strip_bound (center : ℂ) (μ d : ℝ)
    (directions₀ directions₁ : Finset ℝ) {r₀ r₁ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hlength : r₀ + r₁ < d)
    (hμ₀ : μ ∈ directions₀) (hμ₁ : μ + Real.pi ∈ directions₁)
    (hdisjoint : Disjoint (vertexPolygonAt center directions₀ r₀)
      (vertexPolygonAt (center + eC μ * (d : ℂ)) directions₁ r₁)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ width : ℝ, 0 < width → width ≤ δ →
      IsClosedDisc (vertexPolygonAt center directions₀ r₀ ∪
        orientedStrip center μ r₀ (d - r₁) width ∪
        vertexPolygonAt (center + eC μ * (d : ℂ)) directions₁ r₁) := by
  have hlen₀ : r₀ < d - r₁ := lt_sub_iff_add_lt.mpr hlength
  have hlen₁ : r₁ < d - r₀ := lt_sub_iff_add_lt.mpr (by simpa only [add_comm] using hlength)
  obtain ⟨δ₀, hδ₀, hsource⟩ :=
    exists_translated_strip_attachment_bound center directions₀ hr₀ hlen₀ hμ₀
  obtain ⟨δ₁, hδ₁, htarget⟩ := exists_translated_strip_attachment_bound
    (center + eC μ * (d : ℂ)) directions₁ hr₁ hlen₁ hμ₁
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro width hw hwidth
  obtain ⟨hstrip, hline₀, hinter₀, hL₀strip, hL₀polygon⟩ :=
    hsource width hw (hwidth.trans (min_le_left _ _))
  obtain ⟨_, hline₁, hinter₁, hL₁strip, hL₁polygon⟩ :=
    htarget width hw (hwidth.trans (min_le_right _ _))
  have hreverse : orientedStrip (center + eC μ * (d : ℂ)) (μ + Real.pi) r₁ (d - r₀) width =
      orientedStrip center μ r₀ (d - r₁) width := by
    simpa only [sub_sub_cancel] using orientedStrip_reverse center μ d r₁ (d - r₀) width
  rw [hreverse] at hinter₁ hL₁strip
  have hfirst : vertexPolygonAt center directions₀ r₀ ∩
      orientedStrip center μ r₀ (d - r₁) width =
      (fun z => center + z) '' vertexFacetInterval μ r₀ width := by
    rw [inter_comm]
    exact hinter₀
  exact (attach_tree_leaf_discs (vertexPolygonAt_isClosedDisc _ _ hr₀) hstrip
    (vertexPolygonAt_isClosedDisc _ _ hr₁) hline₀ hline₁ hfirst hinter₁ hdisjoint
    hL₀polygon hL₀strip hL₁strip hL₁polygon).1

/-- Part IV, Section 7b: opposite unit normals, with any representatives
as real angles, give the complete two-end attachment data for every small
positive width. The intersection intervals and their endpoints are produced
by the local facet constructions. -/
theorem exists_two_end_attachment_bound (center : ℂ) (μ ν d : ℝ)
    (directions₀ directions₁ : Finset ℝ) {r₀ r₁ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hlength : r₀ + r₁ < d)
    (hμ : μ ∈ directions₀) (hν : ν ∈ directions₁)
    (hopposite : eC ν = eC (μ + Real.pi)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ width : ℝ, 0 < width → width ≤ δ →
      ∃ (L K : Set ℂ) (a b c e : ℂ),
        IsClosedDisc (orientedStrip center μ r₀ (d - r₁) width) ∧
        IsLineWithEnds L a b ∧ IsLineWithEnds K c e ∧
        vertexPolygonAt center directions₀ r₀ ∩
          orientedStrip center μ r₀ (d - r₁) width = L ∧
        orientedStrip center μ r₀ (d - r₁) width ∩
          vertexPolygonAt (center + eC μ * (d : ℂ)) directions₁ r₁ = K ∧
        L ⊆ discBd (vertexPolygonAt center directions₀ r₀) ∧
        L ⊆ discBd (orientedStrip center μ r₀ (d - r₁) width) ∧
        K ⊆ discBd (orientedStrip center μ r₀ (d - r₁) width) ∧
        K ⊆ discBd (vertexPolygonAt (center + eC μ * (d : ℂ)) directions₁ r₁) := by
  have hlen₀ : r₀ < d - r₁ := lt_sub_iff_add_lt.mpr hlength
  have hlen₁ : r₁ < d - r₀ := lt_sub_iff_add_lt.mpr (by simpa only [add_comm] using hlength)
  obtain ⟨δ₀, hδ₀, hs⟩ :=
    exists_translated_strip_attachment_bound center directions₀ hr₀ hlen₀ hμ
  obtain ⟨δ₁, hδ₁, ht⟩ := exists_translated_strip_attachment_bound
    (center + eC μ * (d : ℂ)) directions₁ hr₁ hlen₁ hν
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro width hw hwidth
  obtain ⟨hstrip, hL, hLI, hLS, hLP⟩ := hs width hw (hwidth.trans (min_le_left _ _))
  obtain ⟨_, hK, hKI, hKS, hKP⟩ := ht width hw (hwidth.trans (min_le_right _ _))
  have hreverse : orientedStrip (center + eC μ * (d : ℂ)) ν r₁ (d - r₀) width =
      orientedStrip center μ r₀ (d - r₁) width := by
    rw [orientedStrip_angle_congr _ hopposite]
    simpa only [sub_sub_cancel] using orientedStrip_reverse center μ d r₁ (d - r₀) width
  rw [hreverse] at hKI hKS
  refine ⟨_, _, _, _, _, _, hstrip, hL, hK, ?_, hKI, hLP, hLS, hKS, hKP⟩
  rw [inter_comm]
  exact hLI

end GraphMinor.LRPlanarity
