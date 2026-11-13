module

public import GraphMinor.GM06.Alg57OnePathRaySides
public import GraphMinor.GM06.Alg57OnePathFind4
import GraphMinor.GM06.Section5CutStripProjection
import GraphMinor.GM06.Section5CutEdgePreimage
import GraphMinor.GM06.Alg57SubdrawingRegions
import GraphMinor.GM07.Section46DeficientSeam

/-!
# Points and edges of the cut disc named by the cut slots

For one path the cut disc `D` holds two copies of `P₁`: the lift `Γ₁` (left) and the lift `Γ₂`
(right). The cut tables name a copy of a vertex by a slot `2v` (left) or `2v + 1` (right), and a
copy of an edge in the same way. Here we give each slot a point or a set of `D`:

* `cutPointLabel left c` is the point of `D` over `c` that is not on the other lift. Over a point
  `P₁(t)` it is `Γ₁(t)` for `left` and `Γ₂(t)` otherwise (`cutPointLabel_curve`). Over a point
  off `P₁` it is the only point of `D` over it (`cutPointLabel_off`).
* `cutEdgeLabel left f` is the set of points of `D` over `f` that are not on the other lift. For an
  edge off `P₁` this is the whole preimage (`cutEdgeLabel_off`), an edge of the cut drawing `F`
  (`preimage_off_path_mem_E`). For an edge of `P₁` it is its copy on the chosen lift, again an edge
  of `F` (`cutEdgeLabel_path_mem_E`), whose ends are the copies of the ends of the edge
  (`cutEdgeLabel_path_isLink`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

section Labels

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)

/-- A point of `D` on a lift lies over `P₁`. -/
theorem cutProj_mem_path_of_mem_side {m : ℤ} {p : D} (hp : p ∈ cutSideSet L hG D m) :
    cutProj D p ∈ (L.pathDrawing 0).U := by
  obtain ⟨t, ht⟩ := hp
  change radialCylinderProjection p.1 ∈ _
  rw [← ht, radialCylinderProjection_lift_one, ← (L.curve_parametrizes 0).2.1]
  exact mem_range_self t

theorem cutSidePoint_mem_side (hBd : discBd D = liftedStripBoundary hG.1 L 1) (left : Bool)
    (t : I) : cutSidePoint L hG hBd left t ∈ cutSideSet L hG D (if left then 1 else 2) :=
  ⟨t, rfl⟩

theorem cutSidePoint_notMem_other (hBd : discBd D = liftedStripBoundary hG.1 L 1) (left : Bool)
    (t : I) : cutSidePoint L hG hBd left t ∉ cutSideSet L hG D (if left then 2 else 1) := by
  intro h
  have hne : (if left then (1 : ℤ) else 2) ≠ (if left then 2 else 1) := by cases left <;> decide
  exact disjoint_left.mp (disjoint_range_liftedLinkageCurve hG.1 L hne) ⟨t, rfl⟩ h

/-- The two lifts are disjoint in `D`. -/
theorem notMem_other_of_mem_side (left : Bool) {p : D}
    (hp : p ∈ cutSideSet L hG D (if left then 1 else 2)) :
    p ∉ cutSideSet L hG D (if left then 2 else 1) := by
  intro h
  have hne : (if left then (1 : ℤ) else 2) ≠ (if left then 2 else 1) := by cases left <;> decide
  exact disjoint_left.mp (disjoint_range_liftedLinkageCurve hG.1 L hne) hp h

theorem isClosed_cutSideSet' (m : ℤ) : IsClosed (cutSideSet L hG D m) :=
  isClosed_cutSideSet L hG m

open Classical in
/-- The point of `D` over `c` that is not on the other lift (on `Γ₂` for `left`, on `Γ₁`
otherwise), or `p₀` if there is none. -/
noncomputable def cutPointLabel (p₀ : D) (left : Bool) (c : ClosedCylinder) : D :=
  if h : ∃ p : D, cutProj D p = c ∧ p ∉ cutSideSet L hG D (if left then 2 else 1) then h.choose
  else p₀

theorem cutPointLabel_spec {p₀ : D} {left : Bool} {c : ClosedCylinder}
    (h : ∃ p : D, cutProj D p = c ∧ p ∉ cutSideSet L hG D (if left then 2 else 1)) :
    cutProj D (cutPointLabel L hG p₀ left c) = c ∧
      cutPointLabel L hG p₀ left c ∉ cutSideSet L hG D (if left then 2 else 1) := by
  unfold cutPointLabel
  rw [dif_pos h]
  exact h.choose_spec

/-- The points of `D` over curve points, for a set of `D` over a set of the cylinder. -/
@[expose] def cutEdgeLabel (left : Bool) (f : Set ClosedCylinder) : Set D :=
  cutProj D ⁻¹' f \ cutSideSet L hG D (if left then 2 else 1)

variable {θ : ℝ} (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
  (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})

include hθ hD hstrip in
/-- A point of `D` over `P₁(t)` that is not on the other lift is the point of the chosen lift. -/
theorem eq_cutSidePoint_of_proj (left : Bool) {t : I} {p : D} (hp : cutProj D p = L.curve 0 t)
    (hpo : p ∉ cutSideSet L hG D (if left then 2 else 1)) : p = cutSidePoint L hG hBd left t := by
  rcases eq_lift_of_proj_eq_curve L hG hθ hD hBd hstrip p.2 hp with h | h
  · cases left
    · exact absurd ⟨t, h.symm⟩ hpo
    · exact Subtype.ext h
  · cases left
    · exact Subtype.ext h
    · exact absurd ⟨t, h.symm⟩ hpo

include hθ hD hstrip in
/-- **The label over a point of `P₁`.** -/
theorem cutPointLabel_curve (p₀ : D) (left : Bool) (t : I) :
    cutPointLabel L hG p₀ left (L.curve 0 t) = cutSidePoint L hG hBd left t := by
  have hex : ∃ p : D, cutProj D p = L.curve 0 t ∧ p ∉ cutSideSet L hG D (if left then 2 else 1) :=
    ⟨_, cutProj_cutSidePoint L hG hBd left t, cutSidePoint_notMem_other L hG hBd left t⟩
  obtain ⟨h1, h2⟩ := cutPointLabel_spec L hG (p₀ := p₀) hex
  exact eq_cutSidePoint_of_proj L hG hθ hD hBd hstrip left h1 h2

include hθ hD hBd hstrip in
/-- **The label over a point off `P₁`** is its only preimage. -/
theorem cutPointLabel_off (p₀ : D) (left : Bool) {c : ClosedCylinder}
    (hc : c ∉ (L.pathDrawing 0).U) {p : D} (hp : cutProj D p = c) :
    cutPointLabel L hG p₀ left c = p := by
  have hnot : ∀ q : D, cutProj D q = c → ∀ m, q ∉ cutSideSet L hG D m :=
    fun q hq m hm => hc (hq ▸ cutProj_mem_path_of_mem_side L hG hm)
  obtain ⟨h1, -⟩ := cutPointLabel_spec L hG (p₀ := p₀) ⟨p, hp, hnot p hp _⟩
  exact single_strip_projection_inj_off_path L hG hθ hD hBd hstrip
    (show cutProj D _ ∉ _ by rw [h1]; exact hc) (h1.trans hp.symm)

include hθ hD hBd hstrip in
/-- Every label lies over its point. -/
theorem cutProj_cutPointLabel (p₀ : D) (left : Bool) (c : ClosedCylinder) :
    cutProj D (cutPointLabel L hG p₀ left c) = c := by
  by_cases hc : c ∈ (L.pathDrawing 0).U
  · rw [← (L.curve_parametrizes 0).2.1] at hc
    obtain ⟨t, rfl⟩ := hc
    rw [cutPointLabel_curve L hG hθ hD hBd hstrip]
    exact cutProj_cutSidePoint L hG hBd left t
  · obtain ⟨p, hp⟩ := surjective_single_strip_projection L hG hθ hD hBd hstrip c
    rw [cutPointLabel_off L hG hθ hD hBd hstrip p₀ left hc hp]
    exact hp

include hG in
/-- An edge of `G` off `P₁`: the label is the whole preimage. -/
theorem cutEdgeLabel_off (left : Bool) {f : Set ClosedCylinder} (hf : f ∈ G.E)
    (hfP : f ∉ (L.pathDrawing 0).E) : cutEdgeLabel L hG left f = cutProj D ⁻¹' f := by
  ext p
  refine ⟨fun h => h.1, fun hp => ⟨hp, fun hs => ?_⟩⟩
  exact disjoint_left.mp (deleted_edge_disjoint_subdrawing (L.isSubdrawing 0).1 hf hfP) hp
    (cutProj_mem_path_of_mem_side L hG hs)

include hθ hD hstrip in
/-- An edge of `P₁`: the label is the copy of the edge on the chosen lift. -/
theorem cutEdgeLabel_path_eq (left : Bool) {f : Set ClosedCylinder}
    (hf : f ⊆ (L.pathDrawing 0).U) :
    cutEdgeLabel L hG left f = cutSidePoint L hG hBd left '' (L.curve 0 ⁻¹' f) := by
  ext p
  constructor
  · rintro ⟨hpf, hpo⟩
    have hpP := hf hpf
    rw [← (L.curve_parametrizes 0).2.1] at hpP
    obtain ⟨t, ht⟩ := hpP
    refine ⟨t, show L.curve 0 t ∈ f by rw [ht]; exact hpf, ?_⟩
    exact (eq_cutSidePoint_of_proj L hG hθ hD hBd hstrip left ht.symm hpo).symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, cutSidePoint_notMem_other L hG hBd left t⟩
    change cutProj D (cutSidePoint L hG hBd left t) ∈ f
    rw [cutProj_cutSidePoint]
    exact ht

theorem continuous_cutSidePoint (left : Bool) : Continuous (cutSidePoint L hG hBd left) :=
  (liftedLinkageCurve hG.1 L _).continuous.subtype_mk _

include hθ hD hBd hstrip in
/-- The copy of a path-connected subset of `P₁` on a lift is path-connected. -/
theorem isPathConnected_cutEdgeLabel (left : Bool) {f : Set ClosedCylinder}
    (hf : f ⊆ (L.pathDrawing 0).U) (hfc : IsPathConnected f) :
    IsPathConnected (cutEdgeLabel (D := D) L hG left f) := by
  rw [cutEdgeLabel_path_eq L hG hθ hD hBd hstrip left hf]
  have hemb : IsClosedEmbedding (L.curve 0) :=
    (L.curve 0).continuous.isClosedEmbedding (L.curve_parametrizes 0).1
  have hA : IsPathConnected (L.curve 0 ⁻¹' f) := by
    rw [hemb.isInducing.isPathConnected_iff, image_preimage_eq_inter_range,
      (L.curve_parametrizes 0).2.1, inter_eq_left.mpr hf]
    exact hfc
  exact hA.image (continuous_cutSidePoint L hG hBd left)

variable (F : Drawing D)
  (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
  (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
  (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
    ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)

include hθ hD hBd hstrip hFV in
/-- A label of a vertex of `G` is a vertex of `F`. -/
theorem cutPointLabel_mem_V (p₀ : D) (left : Bool) {c : ClosedCylinder} (hc : c ∈ G.V) :
    cutPointLabel L hG p₀ left c ∈ F.V := by
  rw [hFV]
  change cutProj D _ ∈ G.V
  rw [cutProj_cutPointLabel L hG hθ hD hBd hstrip]
  exact hc

include hFU hFV in
/-- A point of `D` over a point of an edge of `G` is in `F` and is not a vertex. -/
theorem mem_U_sdiff_V_of_proj_mem_edge {f : Set ClosedCylinder} (hf : f ∈ G.E) {p : D}
    (hp : cutProj D p ∈ f) : p ∈ F.U ∧ p ∉ F.V := by
  refine ⟨?_, ?_⟩
  · rw [hFU]
    exact Or.inl (hf.2.1 hp).1
  · rw [hFV]
    exact (hf.2.1 hp).2

include hθ hD hBd hstrip hFU hFV hEdges in
/-- **The preimage of an edge off `P₁` is an edge of `F`.** -/
theorem preimage_off_path_mem_E {f : Set ClosedCylinder} (hf : f ∈ G.E)
    (hfP : f ∉ (L.pathDrawing 0).E) : cutProj D ⁻¹' f ∈ F.E := by
  obtain ⟨c, hc⟩ := hf.2.2.1.nonempty
  obtain ⟨p, hp⟩ := surjective_single_strip_projection L hG hθ hD hBd hstrip c
  have hp' : cutProj D p = c := hp
  have hpf : cutProj D p ∈ f := by rw [hp']; exact hc
  obtain ⟨hpU, hpV⟩ := mem_U_sdiff_V_of_proj_mem_edge F hFU hFV hf hpf
  obtain ⟨ec, hec, hpec⟩ := F.exists_edge_of_mem hpU hpV
  rcases hEdges ec hec with hbd | ⟨f', hf', rfl⟩
  · exact absurd (hbd hpec) (disjoint_left.mp
      (preimage_non_seam_edge_disjoint_boundary L hG hθ hD hBd hstrip hf hfP) hpf)
  · have hff : f' = f := G.edge_eq_of_mem hf'.1 hf hpec hpf
    rw [← hff]
    exact hec

include hθ hD hBd hstrip hFU hFV hEdges in
/-- **The copy of an edge of `P₁` on a lift is an edge of `F`.** -/
theorem cutEdgeLabel_path_mem_E (left : Bool) {f : Set ClosedCylinder}
    (hf : f ∈ (L.pathDrawing 0).E) : cutEdgeLabel L hG left f ∈ F.E := by
  have hfG : f ∈ G.E := (L.isSubdrawing 0).1.2 hf
  have hfP : f ⊆ (L.pathDrawing 0).U := fun c hc => (hf.2.1 hc).1
  obtain ⟨c, hc⟩ := hf.2.2.1.nonempty
  have hcP := hfP hc
  rw [← (L.curve_parametrizes 0).2.1] at hcP
  obtain ⟨t, rfl⟩ := hcP
  set p := cutSidePoint L hG hBd left t
  have hpf : cutProj D p ∈ f := by rw [cutProj_cutSidePoint]; exact hc
  obtain ⟨hpU, hpV⟩ := mem_U_sdiff_V_of_proj_mem_edge F hFU hFV hfG hpf
  obtain ⟨ec, hec, hpec⟩ := F.exists_edge_of_mem hpU hpV
  have hmn : ((if left then (1 : ℤ) else 2) = 1 ∧ (if left then (2 : ℤ) else 1) = 2) ∨
      ((if left then (1 : ℤ) else 2) = 2 ∧ (if left then (2 : ℤ) else 1) = 1) := by
    cases left <;> simp
  have hside : ec ⊆ cutSideSet L hG D (if left then 1 else 2) :=
    cut_edge_subset_side L hG hθ hD hBd hstrip F hFV hEdges hmn hec
      ⟨p, hpec, cutSidePoint_mem_side L hG hBd left t⟩
  -- the edge `ec` lies over `f`
  have hproj : cutProj D '' ec ⊆ f := by
    have hsub : f ∪ cutProj D '' ec ⊆ G.U \ G.V := by
      apply union_subset hfG.2.1
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨(L.isSubdrawing 0).1.U_subset (cutProj_mem_path_of_mem_side L hG (hside hq)), ?_⟩
      have hqV := (hec.2.1 hq).2
      rw [hFV] at hqV
      exact hqV
    have hconn : IsPathConnected (f ∪ cutProj D '' ec) :=
      hfG.2.2.1.union (hec.2.2.1.image continuous_cutProj) ⟨_, hc, p, hpec, cutProj_cutSidePoint L hG hBd left t⟩
    have := hfG.2.2.2 _ hsub hconn subset_union_left
    rw [← this]
    exact subset_union_right
  have hecL : ec ⊆ cutEdgeLabel L hG left f := fun q hq =>
    ⟨hproj ⟨q, hq, rfl⟩, notMem_other_of_mem_side L hG left (hside hq)⟩
  -- the copy lies in `ec`
  have hLconn := isPathConnected_cutEdgeLabel L hG hθ hD hBd hstrip left hfP hfG.2.2.1
  have hLsub : cutEdgeLabel L hG left f ⊆ F.U \ F.V := fun q hq =>
    let h := mem_U_sdiff_V_of_proj_mem_edge F hFU hFV hfG hq.1
    ⟨h.1, h.2⟩
  have hLe : cutEdgeLabel L hG left f ⊆ ec :=
    GM07.subset_edge_of_meets hec hLconn hLsub ⟨p, ⟨hpf, cutSidePoint_notMem_other L hG hBd left t⟩, hpec⟩
  rw [subset_antisymm hLe hecL]
  exact hec

include hθ hD hBd hstrip hFU hFV hEdges in
/-- **The ends of the copy of an edge of `P₁`.** If `f` joins `P₁(a)` and `P₁(b)`, its copy on a
lift joins the copies of `P₁(a)` and `P₁(b)` on that lift. -/
theorem cutEdgeLabel_path_isLink (left : Bool) {f : Set ClosedCylinder}
    (hf : f ∈ (L.pathDrawing 0).E) {a b : I}
    (hl : G.toGraph.IsLink f (L.curve 0 a) (L.curve 0 b)) :
    F.toGraph.IsLink (cutEdgeLabel L hG left f) (cutSidePoint L hG hBd left a)
      (cutSidePoint L hG hBd left b) := by
  have hfP : f ⊆ (L.pathDrawing 0).U := fun c hc => (hf.2.1 hc).1
  have hemb : IsClosedEmbedding (L.curve 0) :=
    (L.curve 0).continuous.isClosedEmbedding (L.curve_parametrizes 0).1
  have hcont := continuous_cutSidePoint L hG hBd left
  have hVa : cutSidePoint L hG hBd left a ∈ F.V := by
    rw [hFV]
    change cutProj D _ ∈ G.V
    rw [cutProj_cutSidePoint]
    exact hl.2.1
  have hVb : cutSidePoint L hG hBd left b ∈ F.V := by
    rw [hFV]
    change cutProj D _ ∈ G.V
    rw [cutProj_cutSidePoint]
    exact hl.2.2.1
  -- the ends of `f` are limits of `f` along `P₁`
  have hcl : ∀ s : I, L.curve 0 s ∈ closure f →
      cutSidePoint L hG hBd left s ∈ closure (cutEdgeLabel L hG left f) := by
    intro s hs
    have himg : L.curve 0 '' (L.curve 0 ⁻¹' f) = f := by
      rw [image_preimage_eq_inter_range, (L.curve_parametrizes 0).2.1, inter_eq_left.mpr hfP]
    rw [← himg, hemb.closure_image_eq] at hs
    obtain ⟨s', hs', hss⟩ := hs
    rw [(L.curve_parametrizes 0).1 hss] at hs'
    rw [cutEdgeLabel_path_eq L hG hθ hD hBd hstrip left hfP]
    exact image_closure_subset_closure_image hcont ⟨s, hs', rfl⟩
  have hab : closure f ∩ G.V = {L.curve 0 a, L.curve 0 b} := hl.2.2.2
  have hca : L.curve 0 a ∈ closure f := by
    have h : L.curve 0 a ∈ closure f ∩ G.V := by rw [hab]; exact mem_insert _ _
    exact h.1
  have hcb : L.curve 0 b ∈ closure f := by
    have h : L.curve 0 b ∈ closure f ∩ G.V := by rw [hab]; exact mem_insert_of_mem _ rfl
    exact h.1
  refine ⟨cutEdgeLabel_path_mem_E L hG hθ hD hBd hstrip F hFU hFV hEdges left hf, hVa, hVb, ?_⟩
  apply subset_antisymm
  · rintro q ⟨hq, hqV⟩
    -- `q` lies on the chosen lift and over an end of `f`
    have hside : closure (cutEdgeLabel L hG left f) ⊆ cutSideSet L hG D (if left then 1 else 2) := by
      apply closure_minimal _ (isClosed_cutSideSet L hG _)
      rw [cutEdgeLabel_path_eq L hG hθ hD hBd hstrip left hfP]
      rintro _ ⟨s, -, rfl⟩
      exact cutSidePoint_mem_side L hG hBd left s
    have hqf : cutProj D q ∈ closure f := by
      have h := image_closure_subset_closure_image (continuous_cutProj (D := D)) ⟨q, hq, rfl⟩
      refine closure_mono ?_ h
      rintro _ ⟨q', hq', rfl⟩
      exact hq'.1
    have hqGV : cutProj D q ∈ G.V := by rw [hFV] at hqV; exact hqV
    have hqab : cutProj D q ∈ ({L.curve 0 a, L.curve 0 b} : Set ClosedCylinder) := by
      rw [← hab]; exact ⟨hqf, hqGV⟩
    have hqo := notMem_other_of_mem_side L hG left (hside hq)
    rcases hqab with h | h
    · exact Or.inl (eq_cutSidePoint_of_proj L hG hθ hD hBd hstrip left h hqo)
    · exact Or.inr (eq_cutSidePoint_of_proj L hG hθ hD hBd hstrip left h hqo)
  · rintro q (rfl | rfl)
    · exact ⟨hcl a hca, hVa⟩
    · exact ⟨hcl b hcb, hVb⟩

end Labels

end GraphMinor.GM06
