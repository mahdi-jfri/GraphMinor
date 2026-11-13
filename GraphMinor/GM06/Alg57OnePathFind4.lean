module

public import GraphMinor.GM06.Alg57Find4Generic
public import GraphMinor.GM06.Alg57OnePathReduction4
import GraphMinor.GM06.Section5CutEdgePreimage
import GraphMinor.GM06.Section5LiftedPaths
import GraphMinor.GM06.Section5CoverRegion
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Alg57Reduction4Complete
import GraphMinor.GM11.Walks

/-!
# `FIND_4` for one path

For `k = 1`, `FIND_4` runs in the cut disc `D` on the cut drawing `F`. The searched path is the
left copy of `P₁`, the lift `Γ₁`; the opposite boundary is the right copy, the lift `Γ₂`. We keep
the two copies apart as two subdrawings of `F`, `cutSide F Γ₁` and `cutSide F Γ₂`: each consists
of the vertices and edges of `F` on that lift (`wholeSubdrawing`). An edge of `F` that meets a lift
lies in it (`cut_edge_subset_side`), since it lies in the boundary circle of `D`, misses the ends of
the lift (which are vertices), and the rest of the circle is closed.

The representation structure is `Find4Rep1`: the program's lists represent the setting of
`Alg57Find4Generic` with
* the drawing `F` and the path `cutSide F Γ₁` from `Γ₁ 0` to `Γ₁ 1`,
* the closed set `cutRc`: the points of `D` over the closure of the lifted region,
* the opposite boundary `cutSide F Γ₂`,
* the allowed edges `cutEok`: edges of `F` over an edge of `G`.

`genReduction4At_iff_onePathReduction4At` says that Reduction 4 in this setting is
`OnePathReduction4At`. With `exists_reduction4Step_one_iff` this gives the two summary statements
`exists_reduction4Step_one_of_find4_some` and `not_exists_reduction4Step_one_of_find4_none`.
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

local notation "𝕀" => unitInterval

/-! ### Subdrawings made of whole edges -/

section Whole

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- The vertices of `F` in `T` and the edges of `F` inside `T`. -/
@[expose] def wholeSubdrawing (F : Drawing S) (T : Set S) : Drawing S :=
  F.span (F.V ∩ T) {e | e ∈ F.E ∧ e ⊆ T}

theorem wholeSubdrawing_isSubdrawing (F : Drawing S) (T : Set S) :
    (wholeSubdrawing F T).IsSubdrawing F :=
  Drawing.span_isSubdrawing F _ _

/-- If `T` is closed, in `F`, and every edge meeting `T` lies in `T`, then the points of
`wholeSubdrawing F T` are `T` and its vertices are the vertices of `F` in `T`. This is the
construction of `exists_subdrawing_on_closed_union_of_edges`. -/
theorem wholeSubdrawing_V_U (F : Drawing S) {T : Set S} (hT : IsClosed T) (hTF : T ⊆ F.U)
    (hwhole : ∀ e ∈ F.E, (e ∩ T).Nonempty → e ⊆ T) :
    (wholeSubdrawing F T).V = F.V ∩ T ∧ (wholeSubdrawing F T).U = T := by
  let E := {e : Set S | e ∈ F.E ∧ e ⊆ T}
  let B := wholeSubdrawing F T
  have hBF : B.IsSubdrawing F := wholeSubdrawing_isSubdrawing F T
  have hBE : B.E = E := by
    change (F.span (F.V ∩ T) E).E = E
    rw [Drawing.span_E]
    exact inter_eq_left.mpr (fun e he => he.1)
  have hBV : B.V = F.V ∩ T := by
    apply subset_antisymm
    · intro x hx
      refine ⟨hBF.1 hx, ?_⟩
      change x ∈ F.spanV (F.V ∩ T) E at hx
      rcases hx with hx | hx
      · exact hx.1.2
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        exact closure_minimal he.1.2 hT hxe.1
    · intro x hx
      change x ∈ F.spanV (F.V ∩ T) E
      exact Or.inl ⟨hx, hx.1⟩
  refine ⟨hBV, ?_⟩
  apply subset_antisymm
  · rw [B.U_eq]
    apply union_subset
    · rw [hBV]
      exact inter_subset_right
    · apply iUnion₂_subset
      intro e he
      have heE : e ∈ E := hBE ▸ he
      exact closure_minimal heE.2 hT
  · intro x hx
    by_cases hxV : x ∈ F.V
    · exact B.V_subset_U (hBV.symm ▸ ⟨hxV, hx⟩)
    · obtain ⟨e, he, hxe⟩ := F.exists_edge_of_mem (hTF hx) hxV
      have heB : e ∈ B.E := hBE.symm ▸ ⟨he, hwhole e he ⟨x, hxe, hx⟩⟩
      exact (heB.2.1 hxe).1

end Whole

/-- A preconnected subset `e` of `Bd ⊆ A ∪ C`, with `A` and `C` closed, that meets `A` and whose
points in `A` are not in `C`, lies in `A`. -/
theorem subset_of_isPreconnected_of_cover {X : Type*} [TopologicalSpace X] {e A C Bd : Set X}
    (hA : IsClosed A) (hC : IsClosed C) (hBd : Bd ⊆ A ∪ C) (he : IsPreconnected e)
    (heB : e ⊆ Bd) (hne : (e ∩ A).Nonempty) (hAC : ∀ x ∈ e, x ∈ A → x ∉ C) : e ⊆ A := by
  have hcover : e ⊆ Cᶜ ∪ Aᶜ := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl (hAC x hx hxA)
    · exact Or.inr hxA
  have hdisj : e ∩ (Cᶜ ∩ Aᶜ) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hx hxC hxA
    rcases hBd (heB hx) with h | h
    · exact hxA h
    · exact hxC h
  rcases isPreconnected_iff_subset_of_disjoint.mp he _ _ hC.isOpen_compl hA.isOpen_compl
    hcover hdisj with h | h
  · intro x hx
    rcases hBd (heB hx) with h' | h'
    · exact h'
    · exact absurd h' (h hx)
  · obtain ⟨x, hx, hxA⟩ := hne
    exact absurd hxA (h hx)

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-! ### The two copies of `P₁` -/

/-- The points of the cut disc on the lift `Γₘ`. -/
@[expose] def cutSideSet (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (D : Set (ℝ × ℝ))
    (m : ℤ) : Set D :=
  {p | p.1 ∈ range (liftedLinkageCurve hG.1 L m)}

/-- The copy of `P₁` along the lift `Γₘ`: the vertices and edges of `F` on it. -/
@[expose] def cutSide (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (F : Drawing D)
    (m : ℤ) : Drawing D :=
  wholeSubdrawing F (cutSideSet L hG D m)

/-- The points of the cut disc over the closure of the lifted region. -/
@[expose] def cutRc (G : Drawing ClosedCylinder) (D : Set (ℝ × ℝ)) : Set D :=
  cutCov D ⁻¹' closure (cylinderCoverRegion 1 G 0)

/-- The edges of the cut drawing that lie over an edge of `G`. -/
@[expose] def cutEok (G : Drawing ClosedCylinder) (D : Set (ℝ × ℝ)) : Set (Set D) :=
  {ec | cutProj D '' ec ∈ G.E}

theorem isClosed_cutRc : IsClosed (cutRc G D) :=
  isClosed_closure.preimage continuous_cutCov

theorem isClosed_cutSideSet (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (m : ℤ) : IsClosed (cutSideSet L hG D m) :=
  (isCompact_range (liftedLinkageCurve hG.1 L m).continuous).isClosed.preimage
    continuous_subtype_val

/-- The boundary circle of `D` is the two lifts and two pieces of the lines of radius `1` and `2`. -/
theorem bd_subset_cutSideSet_union (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1) {m n : ℤ}
    (hmn : (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1)) :
    bd D ⊆ cutSideSet L hG D m ∪ Subtype.val ⁻¹'
      (range (liftedLinkageCurve hG.1 L n) ∪ {p : ℝ × ℝ | p.1 = 1 ∨ p.1 = 2}) := by
  intro x hx
  have hx' : x.1 ∈ liftedStripBoundary hG.1 L 1 := by
    rw [← hBd]
    exact ⟨x, hx, rfl⟩
  have h12 : liftedLinkageCurve hG.1 L (1 + 1) = liftedLinkageCurve hG.1 L 2 := rfl
  rw [liftedStripBoundary, h12] at hx'
  rcases hx' with ((h1 | h2) | ⟨h3, -⟩) | ⟨h4, -⟩
  · rcases hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · rcases hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl h2)
    · exact Or.inl h2
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))

/-- **An edge of the cut drawing that meets a lift lies in it.** The edge is in the boundary circle
(edges off the boundary are lifts of edges off `P₁`), it misses the two ends of the lift (they are
vertices), and inner points of the lift are off the other lift and off the radius-`1` and
radius-`2` lines. -/
theorem cut_edge_subset_side (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hθ : L.HasTheta θ) (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {m n : ℤ} (hmn : (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1))
    {ec : Set D} (hec : ec ∈ F.E) (hne : (ec ∩ cutSideSet L hG D m).Nonempty) :
    ec ⊆ cutSideSet L hG D m := by
  have hmD : ∀ t, liftedLinkageCurve hG.1 L m t ∈ discBd D := by
    intro t
    have h12 : liftedLinkageCurve hG.1 L (1 + 1) = liftedLinkageCurve hG.1 L 2 := rfl
    rw [hBd, liftedStripBoundary, h12]
    rcases hmn with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl (Or.inl (Or.inl (mem_range_self t)))
    · exact Or.inl (Or.inl (Or.inr (mem_range_self t)))
  have hsideBd : cutSideSet L hG D m ⊆ bd D := by
    rintro p ⟨t, ht⟩
    exact (val_mem_discBd_iff p).mp (ht ▸ hmD t)
  have hecBd : ec ⊆ bd D := by
    rcases hEdges ec hec with h | ⟨e, he, rfl⟩
    · exact h
    · exfalso
      obtain ⟨p, hp, hpS⟩ := hne
      exact disjoint_left.mp (preimage_non_seam_edge_disjoint_boundary L hG hθ hD hBd hstrip
        he.1 he.2) hp (hsideBd hpS)
  have hC : IsClosed (Subtype.val ⁻¹'
      (range (liftedLinkageCurve hG.1 L n) ∪ {p : ℝ × ℝ | p.1 = 1 ∨ p.1 = 2}) : Set D) := by
    apply IsClosed.preimage continuous_subtype_val
    apply (isCompact_range (liftedLinkageCurve hG.1 L n).continuous).isClosed.union
    exact (isClosed_eq continuous_fst continuous_const).union
      (isClosed_eq continuous_fst continuous_const)
  have hconn : IsPreconnected ec :=
    (hec.2.2.1 : IsPathConnected ec).isConnected.isPreconnected
  refine subset_of_isPreconnected_of_cover (isClosed_cutSideSet L hG m) hC
    (bd_subset_cutSideSet_union L hG hBd hmn) hconn hecBd hne ?_
  rintro x hx ⟨τ, hτ⟩ hxC
  have hxV : x ∉ F.V := edge_notMem_V hec hx
  have hendV : ∀ r : 𝕀, (r = 0 ∨ r = 1) → x.1 = liftedLinkageCurve hG.1 L m r → x ∈ F.V := by
    intro r hr hxr
    rw [hFV]
    change radialCylinderProjection x.1 ∈ G.V
    rw [hxr, radialCylinderProjection_lift_one]
    have hPG : (L.pathDrawing 0).IsSubdrawing G := (L.isSubdrawing 0).1
    rcases hr with rfl | rfl
    · rw [(L.curve_parametrizes 0).2.2.1]
      exact hPG.1 (isPathDrawing_end_vertices (L.isPath 0)).1
    · rw [(L.curve_parametrizes 0).2.2.2]
      have := (L.isSubdrawing 0).1.1 (isPathDrawing_end_vertices (L.isPath 0)).2
      rwa [(L.curve_parametrizes 0).2.2.2] at this
  have hτ0 : τ ≠ 0 := fun h => hxV (hendV τ (Or.inl h) hτ.symm)
  have hτ1 : τ ≠ 1 := fun h => hxV (hendV τ (Or.inr h) hτ.symm)
  have hrad := liftedLinkageCurve_interior_radius L hG m
    ⟨unitInterval.pos_iff_ne_zero.mpr hτ0, unitInterval.lt_one_iff_ne_one.mpr hτ1⟩
  rcases hxC with hn | hr
  · have hmn' : m ≠ n := by rcases hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
    exact disjoint_left.mp (disjoint_range_liftedLinkageCurve hG.1 L hmn') ⟨τ, hτ⟩ hn
  · rw [← hτ] at hr
    rcases hr with hr | hr
    · rw [hr] at hrad; exact lt_irrefl _ hrad.1
    · rw [hr] at hrad; exact lt_irrefl _ hrad.2

/-- The vertices and points of a copy of `P₁`. -/
theorem cutSide_V_U (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hθ : L.HasTheta θ) (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {m n : ℤ} (hmn : (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1)) :
    (cutSide L hG F m).V = F.V ∩ cutSideSet L hG D m ∧
      (cutSide L hG F m).U = cutSideSet L hG D m := by
  apply wholeSubdrawing_V_U F (isClosed_cutSideSet L hG m)
  · intro p hp
    rw [hFU]
    refine Or.inr ?_
    have hbd := bd_subset_cutSideSet_union L hG hBd hmn
    obtain ⟨τ, hτ⟩ := hp
    have h12 : liftedLinkageCurve hG.1 L (1 + 1) = liftedLinkageCurve hG.1 L 2 := rfl
    have hmD : p.1 ∈ discBd D := by
      rw [hBd, liftedStripBoundary, h12, ← hτ]
      rcases hmn with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl (Or.inl (Or.inl (mem_range_self τ)))
      · exact Or.inl (Or.inl (Or.inr (mem_range_self τ)))
    exact (val_mem_discBd_iff p).mp hmD
  · intro e he hne
    exact cut_edge_subset_side L hG hθ hD hBd hstrip F hFV hEdges hmn he hne

/-- The lift `Γ₁` as a curve in the cut disc. -/
@[expose] noncomputable def cutLiftCurve (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1) : C(𝕀, D) :=
  ⟨fun t => ⟨liftedLinkageCurve hG.1 L 1 t, Surface.discBd_subset D (by
    rw [hBd]; exact Or.inl (Or.inl (Or.inl (mem_range_self t))))⟩,
    (liftedLinkageCurve hG.1 L 1).continuous.subtype_mk _⟩

section Lift

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
  (hBd : discBd D = liftedStripBoundary hG.1 L 1)

theorem cutLiftCurve_val (t : 𝕀) : (cutLiftCurve L hG hBd t).1 = liftedLinkageCurve hG.1 L 1 t :=
  rfl

theorem cutLiftCurve_injective : Function.Injective (cutLiftCurve L hG hBd) := fun a b h =>
  (isArcMap_liftedLinkageCurve hG.1 L 1).2 (congrArg Subtype.val h)

theorem range_cutLiftCurve : range (cutLiftCurve L hG hBd) = cutSideSet L hG D 1 := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, Subtype.ext ht⟩

theorem cutCov_cutLiftCurve (t : 𝕀) : cutCov D (cutLiftCurve L hG hBd t) =
    cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 t :=
  (cylinderCurveLiftAt_linkage_one L hG.1 t).symm

theorem cutProj_cutLiftCurve (t : 𝕀) : cutProj D (cutLiftCurve L hG hBd t) = L.curve 0 t :=
  radialCylinderProjection_lift_one L hG.1 1 t

theorem cutLiftCurve_zero : (cutLiftCurve L hG hBd 0).1 = (1, 2 * π) := by
  rw [cutLiftCurve_val]
  apply Prod.ext
  · exact (liftedLinkageCurve_props_raw hG.1 L 1).2.1
  · simpa using (liftedLinkageCurve_props_raw hG.1 L 1).2.2.2.1

/-- A path of the cut disc along `Γ₁` from `Γ₁ a` to `Γ₁ b` is `Γ₁` on the interval between. -/
theorem cutLift_subarc {A : Drawing D} {a b : 𝕀}
    (hA : IsPathDrawing A (cutLiftCurve L hG hBd a) (cutLiftCurve L hG hBd b))
    (hAS : A.U ⊆ cutSideSet L hG D 1) : A.U = cutLiftCurve L hG hBd '' uIcc a b := by
  obtain ⟨g, hgi, hgr, hg0, hg1⟩ := hA.2
  rw [← hgr]
  exact range_eq_image_uIcc_of_subarc (cutLiftCurve_injective L hG hBd) hgi
    (by rw [hgr, range_cutLiftCurve]; exact hAS) hg0 hg1

end Lift

/-- A path of `P₁` from `P₁(a)` to `P₁(b)` is `P₁` on the interval between. -/
theorem linkage_subarc (L : CylinderLinkage 1 G) {A : Drawing ClosedCylinder} {a b : 𝕀}
    (hA : IsPathDrawing A (L.curve 0 a) (L.curve 0 b)) (hAP : A.U ⊆ (L.pathDrawing 0).U) :
    A.U = L.curve 0 '' uIcc a b := by
  obtain ⟨hfi, hfr, -, -⟩ := L.curve_parametrizes 0
  obtain ⟨g, hgi, hgr, hg0, hg1⟩ := hA.2
  rw [← hgr]
  exact range_eq_image_uIcc_of_subarc hfi hgi (by rw [hgr, hfr]; exact hAP) hg0 hg1

/-- Each vertex of `P₁` has a tail. -/
theorem exists_section5Tail (L : CylinderLinkage 1 G) {u : 𝕀}
    (huV : L.curve 0 u ∈ (L.pathDrawing 0).V) :
    ∃ T : Drawing ClosedCylinder,
      IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1) := by
  have htP : L.curve 0 1 ∈ (L.pathDrawing 0).V := by
    rw [← (L.curve_parametrizes 0).2.2.2]
    exact (isPathDrawing_end_vertices (L.isPath 0)).2
  by_cases hu1 : L.curve 0 u = L.curve 0 1
  · let T := walkDrawing (L.pathDrawing 0) (GraphWalk.nil htP)
    have hTV : T.V = {L.curve 0 1} := by
      rw [walkDrawing_V]
      ext x
      simp [GraphWalk.support]
    have hTU : T.U = {L.curve 0 1} := by
      ext x
      rw [mem_walkDrawing_U]
      simp [GraphWalk.support, GraphWalk.edges]
    exact ⟨T, Or.inl ⟨hu1, by rw [hTU, hu1], by rw [hTV, hu1]⟩⟩
  · obtain ⟨T, hT⟩ := exists_subpath_of_isPathDrawing (L.isPath 0) huV htP hu1
    exact ⟨T, Or.inr hT⟩

/-- A tail of `P₁` from `P₁(u)` is `P₁` on `[u, 1]`. -/
theorem section5Tail_U (L : CylinderLinkage 1 G) {u : 𝕀} {T : Drawing ClosedCylinder}
    (hT : IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1)) :
    T.U = L.curve 0 '' Icc u 1 := by
  rcases hT with ⟨hu1, hU, -⟩ | ⟨-, hTP, hTpath⟩
  · have hu : u = 1 := (L.curve_parametrizes 0).1 hu1
    rw [hU, hu, Icc_self, image_singleton]
  · rw [linkage_subarc L hTpath hTP, uIcc_of_le unitInterval.le_one']

/-- A walk splits at each vertex of its support. -/
theorem walk_exists_split_of_mem {α β : Type*} {Gr : Graph α β} {a b x : α}
    (W : GraphWalk Gr a b) (hx : x ∈ W.support) :
    ∃ (W₁ : GraphWalk Gr a x) (W₂ : GraphWalk Gr x b), W = W₁.append W₂ := by
  induction W with
  | nil h =>
    have hx' : x = _ := List.mem_singleton.mp hx
    subst hx'
    exact ⟨GraphWalk.nil h, GraphWalk.nil h, rfl⟩
  | @cons u y w e hlink rest ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨GraphWalk.nil hlink.left_mem, GraphWalk.cons hlink rest, rfl⟩
    · obtain ⟨W₁, W₂, hW⟩ := ih hx
      exact ⟨GraphWalk.cons hlink W₁, W₂, by rw [hW]; rfl⟩

/-! ### Reduction 4 in the setting is one-path Reduction 4 -/

/-- **Reduction 4 at the left copy is one-path Reduction 4.** Let `W` be a simple walk of the left
copy from `Γ₁ 0` to `Γ₁ 1` through all its vertices. Reduction 4 in the setting of
`Alg57Find4Generic` (path the left copy, region closure `cutRc`, opposite boundary the right copy,
allowed edges `cutEok`) holds exactly when `OnePathReduction4At` holds. Subpaths and tails along
`Γ₁` are `Γ₁` on intervals (`cutLift_subarc`), and tails of `P₁` are `P₁` on intervals
(`section5Tail_U`); the two tail conditions match through the projection. -/
theorem genReduction4At_iff_onePathReduction4At (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {s t : D} (hs : s.1 = (1, 2 * π)) (ht : t = cutLiftCurve L hG hBd 1)
    {W : GraphWalk (cutSide L hG F 1).toGraph s t} (hW : W.IsSimple)
    (hWV : (cutSide L hG F 1).V = {x | x ∈ W.support}) :
    GenReduction4At F (cutSide L hG F 1) s t (cutRc G D) (cutSide L hG F 2) (cutEok G D) ↔
      OnePathReduction4At L hG D F := by
  obtain ⟨hP1V, hP1U⟩ := cutSide_V_U L hG hθ hD hBd hstrip F hFU hFV hEdges
    (m := 1) (n := 2) (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨-, hP2U⟩ := cutSide_V_U L hG hθ hD hBd hstrip F hFU hFV hEdges
    (m := 2) (n := 1) (Or.inr ⟨rfl, rfl⟩)
  have hsf : s = cutLiftCurve L hG hBd 0 := Subtype.ext (by rw [hs, cutLiftCurve_zero])
  subst hsf ht
  have hfi := cutLiftCurve_injective L hG hBd
  have hPG : (L.pathDrawing 0).IsSubdrawing G := (L.isSubdrawing 0).1
  have hci := (L.curve_parametrizes 0).1
  have hcr := (L.curve_parametrizes 0).2.1
  constructor
  · rintro ⟨w, P_sw, T', Q, hw, hwR, hsw, hpre, hT', hQG, hQ, hQR, hQT, hQB, hQE⟩
    rw [hP1V] at hw
    have hwr : w ∈ range (cutLiftCurve L hG hBd) := by
      rw [range_cutLiftCurve]; exact hw.2
    obtain ⟨u, rfl⟩ := hwr
    have hsw' : cutLiftCurve L hG hBd 0 ≠ cutLiftCurve L hG hBd u := isPathDrawing_start_ne_end hQ
    have hu0 : 0 < u := lt_of_le_of_ne unitInterval.nonneg' fun h => hsw' (by rw [h])
    have huV : L.curve 0 u ∈ (L.pathDrawing 0).V := by
      have h1 : cutProj D (cutLiftCurve L hG hBd u) ∈ G.V := by
        have := hw.1
        rw [hFV] at this
        exact this
      rw [cutProj_cutLiftCurve] at h1
      exact mem_V_of_mem_U_of_isSubdrawing hPG (by rw [← hcr]; exact mem_range_self u) h1
    have hpre' : ¬ (cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 '' Icc 0 u ⊆
        closure (cylinderCoverRegion 1 G 0)) := by
      intro H
      apply hpre
      rw [cutLift_subarc L hG hBd hsw.2.2 (hP1U ▸ hsw.2.1), uIcc_of_le unitInterval.nonneg']
      rintro _ ⟨τ, hτ, rfl⟩
      change cutCov D (cutLiftCurve L hG hBd τ) ∈ closure (cylinderCoverRegion 1 G 0)
      rw [cutCov_cutLiftCurve]
      exact H ⟨τ, hτ, rfl⟩
    obtain ⟨T, hT⟩ := exists_section5Tail L huV
    have hright : ∀ p ∈ Q.U, p.1 ∉ range (liftedLinkageCurve hG.1 L 2) := fun p hp h =>
      disjoint_left.mp hQB hp (by rw [hP2U]; exact h)
    have hQT' : cutProj D '' Q.U ∩ T.U ⊆ {L.curve 0 u} := by
      rintro _ ⟨⟨p, hp, rfl⟩, hxT⟩
      rw [section5Tail_U L hT] at hxT
      obtain ⟨τ, hτ, hτp⟩ := hxT
      rcases mem_lifts_of_cutProj_mem_path L hG hθ hD hBd hstrip (p := p)
          (by rw [← hτp, ← hcr]; exact mem_range_self τ) with h1 | h2
      · obtain ⟨σ, hσ⟩ := h1
        have hpf : p = cutLiftCurve L hG hBd σ := Subtype.ext hσ.symm
        have hστ : σ = τ := hci (by rw [← cutProj_cutLiftCurve L hG hBd σ, ← hpf, hτp])
        subst hστ hpf
        suffices hpu : cutLiftCurve L hG hBd σ = cutLiftCurve L hG hBd u by
          rw [hpu, cutProj_cutLiftCurve]
          exact mem_singleton _
        rcases hT' with ⟨hwt, -, -⟩ | ⟨-, hT'P, hT'path⟩
        · have hu1 : u = 1 := hfi hwt
          have hσu : σ = u := le_antisymm (hu1 ▸ hτ.2) hτ.1
          rw [hσu]
        · have hmem : cutLiftCurve L hG hBd σ ∈ T'.U := by
            rw [cutLift_subarc L hG hBd hT'path (hP1U ▸ hT'P), uIcc_of_le unitInterval.le_one']
            exact ⟨σ, hτ, rfl⟩
          exact hQT ⟨hp, hmem⟩
      · exact absurd h2 (hright p hp)
    refine ⟨u, hu0, huV, hpre', cutLiftCurve L hG hBd 0, cutLiftCurve L hG hBd u, Q,
      ⟨hQG, hQG.U_subset, hQ⟩, cutLiftCurve_zero L hG hBd, rfl, hright, hQE, ?_, T, hT, hQT'⟩
    rintro _ ⟨p, hp, rfl⟩
    exact hQR hp
  · rintro ⟨u, hu, huV, hpre, s', w, Q, hQ, hs', hw, hright, hE, hR, T, hT, hQT⟩
    have hs'f : s' = cutLiftCurve L hG hBd 0 :=
      Subtype.ext (by rw [hs', cutLiftCurve_zero])
    have hwf : w = cutLiftCurve L hG hBd u := Subtype.ext hw
    subst hs'f hwf
    have hwV : cutLiftCurve L hG hBd u ∈ (cutSide L hG F 1).V := by
      rw [hP1V]
      refine ⟨?_, ⟨u, rfl⟩⟩
      rw [hFV]
      change cutProj D (cutLiftCurve L hG hBd u) ∈ G.V
      rw [cutProj_cutLiftCurve]
      exact hPG.1 huV
    have hwW : cutLiftCurve L hG hBd u ∈ W.support := by
      rw [hWV] at hwV
      exact hwV
    obtain ⟨W₁, W₂, hsplit⟩ := walk_exists_split_of_mem W hwW
    have hn : (W₁.support ++ W₂.support.tail).Nodup := by
      have h := hW
      change W.support.Nodup at h
      rwa [hsplit, GraphWalk.support_append] at h
    have hW₁ : W₁.IsSimple := hn.of_append_left
    have hW₂ : W₂.IsSimple := by
      change W₂.support.Nodup
      rw [W₂.support_eq_cons]
      exact List.nodup_cons.mpr
        ⟨fun hmem => List.disjoint_of_nodup_append hn W₁.end_mem_support hmem,
          hn.of_append_right⟩
    have hsw : cutLiftCurve L hG hBd 0 ≠ cutLiftCurve L hG hBd u := fun h => hu.ne (hfi h)
    have hsub : IsSubpathOf (cutSide L hG F 1) (walkDrawing (cutSide L hG F 1) W₁)
        (cutLiftCurve L hG hBd 0) (cutLiftCurve L hG hBd u) :=
      ⟨walkDrawing_isSubdrawing _ W₁, walkDrawing_U_subset _ W₁,
        isPathDrawing_walkDrawing_of_isSimple _ hW₁ hsw⟩
    have hpre' : ¬ (walkDrawing (cutSide L hG F 1) W₁).U ⊆ cutRc G D := by
      intro H
      apply hpre
      rintro _ ⟨τ, hτ, rfl⟩
      have hmem : cutLiftCurve L hG hBd τ ∈ (walkDrawing (cutSide L hG F 1) W₁).U := by
        rw [cutLift_subarc L hG hBd hsub.2.2 (hP1U ▸ hsub.2.1), uIcc_of_le unitInterval.nonneg']
        exact ⟨τ, hτ, rfl⟩
      have h := H hmem
      change cutCov D (cutLiftCurve L hG hBd τ) ∈ closure (cylinderCoverRegion 1 G 0) at h
      rwa [cutCov_cutLiftCurve] at h
    have h1V : cutLiftCurve L hG hBd 1 ∈ (cutSide L hG F 1).V := by
      rw [hWV]; exact W.end_mem_support
    obtain ⟨T', hT', hT'U⟩ : ∃ T' : Drawing D,
        IsGenTail (cutSide L hG F 1) T' (cutLiftCurve L hG hBd u) (cutLiftCurve L hG hBd 1) ∧
          T'.U ⊆ cutLiftCurve L hG hBd '' Icc u 1 := by
      by_cases hwt : cutLiftCurve L hG hBd u = cutLiftCurve L hG hBd 1
      · let T' := walkDrawing (cutSide L hG F 1) (GraphWalk.nil h1V)
        have hTV : T'.V = {cutLiftCurve L hG hBd 1} := by
          rw [walkDrawing_V]
          ext x
          simp [GraphWalk.support]
        have hTU : T'.U = {cutLiftCurve L hG hBd 1} := by
          ext x
          rw [mem_walkDrawing_U]
          simp [GraphWalk.support, GraphWalk.edges]
        refine ⟨T', Or.inl ⟨hwt, by rw [hTU, hwt], by rw [hTV, hwt]⟩, ?_⟩
        rw [hTU]
        exact singleton_subset_iff.mpr ⟨1, ⟨unitInterval.le_one', le_rfl⟩, rfl⟩
      · have hpath := isPathDrawing_walkDrawing_of_isSimple (cutSide L hG F 1) hW₂ hwt
        refine ⟨walkDrawing (cutSide L hG F 1) W₂,
          Or.inr ⟨walkDrawing_isSubdrawing _ W₂, walkDrawing_U_subset _ W₂, hpath⟩, ?_⟩
        rw [cutLift_subarc L hG hBd hpath (hP1U ▸ walkDrawing_U_subset _ W₂),
          uIcc_of_le unitInterval.le_one']
    have hQT' : Q.U ∩ T'.U ⊆ {cutLiftCurve L hG hBd u} := by
      rintro p ⟨hp, hpT⟩
      obtain ⟨τ, hτ, rfl⟩ := hT'U hpT
      have hmem : cutProj D (cutLiftCurve L hG hBd τ) ∈ cutProj D '' Q.U ∩ T.U :=
        ⟨⟨_, hp, rfl⟩, by rw [cutProj_cutLiftCurve, section5Tail_U L hT]; exact ⟨τ, hτ, rfl⟩⟩
      have h := hQT hmem
      rw [cutProj_cutLiftCurve, mem_singleton_iff] at h
      rw [hci h]
      exact mem_singleton _
    have hwQ : cutLiftCurve L hG hBd u ∈ Q.U :=
      Q.V_subset_U (isPathDrawing_end_vertices hQ.2.2).2
    refine ⟨cutLiftCurve L hG hBd u, walkDrawing (cutSide L hG F 1) W₁, T', Q, hwV,
      hR ⟨_, hwQ, rfl⟩, hsub, hpre', hT', hQ.1, hQ.2.2, fun p hp => hR ⟨p, hp, rfl⟩, hQT', ?_, hE⟩
    rw [hP2U, disjoint_left]
    exact fun p hp h => hright p hp h

/-- The soundness half of `exists_reduction4Step_one_iff`, which needs no hypothesis on
Reductions 1 and 2. -/
theorem exists_reduction4Step_one_of_onePathReduction4At (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) {F : Drawing D}
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (h : OnePathReduction4At L hG D F) :
    ∃ L' : CylinderLinkage 1 G, Section5Reduction4Step 1 G L G L' := by
  obtain ⟨u, hu, huV, hpre, s, w, Q, hQ, hs, hw, hright, hE, hR, T, hT, hQT⟩ := h
  exact exists_reduction4Step_one_of_cut_path L hG hθ hD hBd hstrip hFV hQ hs hu huV hw hright
    hE hR hpre hT hQT

/-- **The region closure of the one-path setting is the closure of a region of `F`.** The points of
the cut disc over the closure of the lifted region are the closure of the region `Z` of the cut
drawing that is the preimage of the lifted region, off the boundary. So the incidence fields of
`Find4Rep1` and `TerminalRep1` are incidence with one region of `F`. -/
theorem cutRc_eq_closure_region (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hθ : L.HasTheta θ) (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D) :
    (cutCov D ⁻¹' cylinderCoverRegion 1 G 0) \ bd D ∈ F.R ∧
      cutRc G D = closure ((cutCov D ⁻¹' cylinderCoverRegion 1 G 0) \ bd D) := by
  obtain ⟨hZR, hZcl⟩ := preimage_coverRegion_sdiff_boundary_mem_regions L hG hθ hD hBd hstrip F hFU
  refine ⟨hZR, ?_⟩
  have hinj : Function.Injective (cutCov D) := (isClosedEmbedding_single_strip_coverMap hD hstrip).injective
  have hZcl' : cutCov D '' closure ((cutCov D ⁻¹' cylinderCoverRegion 1 G 0) \ bd D) =
      closure (cylinderCoverRegion 1 G 0) := hZcl
  change cutCov D ⁻¹' closure (cylinderCoverRegion 1 G 0) = _
  rw [← hZcl', hinj.preimage_image]

/-! ### The representation and the summary statements -/

/-- **The lists of `FIND_4` represent the one-path search.** The program's lists, with vertex
labels in the cut disc, represent the setting of `Alg57Find4Generic` with the drawing `F`, the left
copy `cutSide L hG F 1` of `P₁` from `s` to `t`, the region closure `cutRc G D`, the right copy
`cutSide L hG F 2` as opposite boundary, and the allowed edges `cutEok G D` (edges over an edge of
`G`). The two copies are different subdrawings, so their labels stay apart. -/
abbrev Find4Rep1 (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (F : Drawing D)
    (s t : D) {n : ℕ} (ends : List (ℕ × ℕ)) (ordinary : List Bool) (incV incE upper : List ℕ)
    (start : Fin n) (steps : List (ℕ × Fin n)) (lab : Fin n → D) (edgeLab : ℕ → Set D) : Prop :=
  Find4GenRep F (cutSide L hG F 1) s t (cutRc G D) (cutSide L hG F 2) (cutEok G D)
    ends ordinary incV incE upper start steps lab edgeLab

section Summary

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
  (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
  (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
  (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
    ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)

include hθ hD hstrip hFU hFV hEdges in
/-- The side conditions of the one-path setting. -/
theorem onePath_setting :
    (cutSide L hG F 1).IsSubdrawing F ∧ (cutSide L hG F 2).IsSubdrawing F ∧
      ParametrizesSet (cutLiftCurve L hG hBd) (cutSide L hG F 1).U
        (cutLiftCurve L hG hBd 0) (cutLiftCurve L hG hBd 1) ∧
      IsClosed (cutRc G D) ∧ cutLiftCurve L hG hBd 0 ∈ cutRc G D ∧
      Disjoint (cutSide L hG F 1).U (cutSide L hG F 2).U := by
  obtain ⟨-, hP1U⟩ := cutSide_V_U L hG hθ hD hBd hstrip F hFU hFV hEdges
    (m := 1) (n := 2) (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨-, hP2U⟩ := cutSide_V_U L hG hθ hD hBd hstrip F hFU hFV hEdges
    (m := 2) (n := 1) (Or.inr ⟨rfl, rfl⟩)
  refine ⟨wholeSubdrawing_isSubdrawing _ _, wholeSubdrawing_isSubdrawing _ _,
    ⟨cutLiftCurve_injective L hG hBd, by rw [hP1U, range_cutLiftCurve], rfl, rfl⟩,
    isClosed_cutRc, ?_, ?_⟩
  · change cutCov D (cutLiftCurve L hG hBd 0) ∈ closure (cylinderCoverRegion 1 G 0)
    rw [cutCov_cutLiftCurve, cylinderCurveLiftAt_zero, (L.curve_parametrizes 0).2.2.1]
    exact cylinderInitialLift_mem_closure_coverRegion hG 0
  · rw [hP1U, hP2U, disjoint_left]
    exact fun p h1 h2 => disjoint_left.mp
      (disjoint_range_liftedLinkageCurve hG.1 L (show (1 : ℤ) ≠ 2 by norm_num)) h1 h2

include hθ hD hstrip hFU hFV hEdges in
/-- **`FIND_4` returns a witness ⇒ a Reduction 4 step exists** (`k = 1`). -/
theorem exists_reduction4Step_one_of_find4_some {s t : D} (hs : s = cutLiftCurve L hG hBd 0)
    (ht : t = cutLiftCurve L hG hBd 1) {n : ℕ} {ends : List (ℕ × ℕ)} {ordinary : List Bool}
    {incV incE upper : List ℕ} {start : Fin n} {steps : List (ℕ × Fin n)}
    {lab : Fin n → D} {edgeLab : ℕ → Set D}
    (rep : Find4Rep1 L hG F s t ends ordinary incV incE upper start steps lab edgeLab)
    {j : ℕ} {path : List ℕ}
    (h : gm06Find4 ends ordinary incV incE upper start steps = some (j, path)) :
    ∃ L' : CylinderLinkage 1 G, Section5Reduction4Step 1 G L G L' := by
  subst hs ht
  obtain ⟨hP1F, hP2F, hf, hRc, hsR, hPB⟩ :=
    onePath_setting L hG hθ hD hBd hstrip F hFU hFV hEdges
  have hgen := genReduction4At_of_find4_some rep hP1F hP2F hf hRc hsR hPB h
  obtain ⟨W, hW, hWV, -, -⟩ := rep.path_walk
  exact exists_reduction4Step_one_of_onePathReduction4At L hG hθ hD hBd hstrip hFV
    ((genReduction4At_iff_onePathReduction4At L hG hθ hD hBd hstrip F hFU hFV hEdges
      (cutLiftCurve_zero L hG hBd) rfl hW hWV).mp hgen)

include hθ hD hstrip hFU hFV hEdges in
/-- **`FIND_4` returns none ⇒ no Reduction 4 applies** (`k = 1`), when Reductions 1 and 2 do not
apply and `s₁` does not have valency one. -/
theorem not_exists_reduction4Step_one_of_find4_none
    (hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction1Step 1 G L H M)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction2Step 1 G L H M)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    {s t : D} (hs : s = cutLiftCurve L hG hBd 0)
    (ht : t = cutLiftCurve L hG hBd 1) {n : ℕ} {ends : List (ℕ × ℕ)} {ordinary : List Bool}
    {incV incE upper : List ℕ} {start : Fin n} {steps : List (ℕ × Fin n)}
    {lab : Fin n → D} {edgeLab : ℕ → Set D}
    (rep : Find4Rep1 L hG F s t ends ordinary incV incE upper start steps lab edgeLab)
    (h : gm06Find4 ends ordinary incV incE upper start steps = none) :
    ¬ ∃ L' : CylinderLinkage 1 G, Section5Reduction4Step 1 G L G L' := by
  subst hs ht
  obtain ⟨hP1F, hP2F, hf, hRc, hsR, hPB⟩ :=
    onePath_setting L hG hθ hD hBd hstrip F hFU hFV hEdges
  have hEdges' : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
    intro ec hec
    rcases hEdges ec hec with h | ⟨e, he, heq⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, he.1, heq⟩
  intro hex
  have hone := (exists_reduction4Step_one_iff L hG hθ hno1 hno2 hval hD hBd hstrip F hFU hFV
    hEdges').mp hex
  obtain ⟨W, hW, hWV, -, -⟩ := rep.path_walk
  exact not_genReduction4At_of_find4_none rep hP1F hP2F hf hRc hsR hPB h
    ((genReduction4At_iff_onePathReduction4At L hG hθ hD hBd hstrip F hFU hFV hEdges
      (cutLiftCurve_zero L hG hBd) rfl hW hWV).mpr hone)

end Summary

end GraphMinor.GM06
