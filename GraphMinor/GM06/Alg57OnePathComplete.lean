module

public import GraphMinor.GM06.Alg57OnePathSound
public import GraphMinor.GM06.Alg57OnePathCrosscut
import GraphMinor.GM06.Section5CutSheetComponent
import GraphMinor.GM06.Section5CutRegion
import GraphMinor.GM06.Section5CutRegionCoordinates
import GraphMinor.GM06.Section5CoverCurve
import GraphMinor.GM06.Section5CutStripProjection
import GraphMinor.GM06.Section5SingleStripFibers
import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CutEdgePreimage
import GraphMinor.GM06.Section5CutLinks
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5IncidentPrefixValency
import GraphMinor.GM06.Section5CutInitialArcExclusion
import GraphMinor.GM06.Section5CutBoundaryEdgeExclusion
import GraphMinor.GM06.Section5SidedReduction4
import GraphMinor.GM06.Alg57Reduction4Complete
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks
import GraphMinor.GM11.CircuitRegions

/-!
# Every one-path Reduction 4 gives a path that `FIND_4` finds

This is Lemma 12 and the completeness half of Lemma 13 of our proof of VI (5.7)
(outlined in `Alg57Algorithm.lean`), for `k = 1`,
in the cut disc `D` between the chosen lift `Γ₁` of the sole linkage path `P₁` and its translate
`Γ₂`. We assume what holds when `FIND_4` runs: Reductions 1 and 2 do not apply, and `s₁` does not
have valency one.

Given a one-path Reduction 4 (`Section5Reduction4SideCondition`) with new path `Q`, we lift `Q`
into `D` along its lift in the cover (`exists_cut_lift`) and cut it at its first vertex `w` whose
lift lies on `Γ₁` after `s̃₁` or on `Γ₂`. The part before `w` misses the boundary of `D`
(`IsCarry` of the lift), so it is a path of the cut drawing `F` with interior inside `D`.

* If the lift of `w` is on `Γ₂`, this part is a crosscut of `D` from `s̃₁` to `Γ₂`. The lifted region
  lies beside the inner cuff, so by Lemma 2 (`le_of_mem_closure_of_crosscut`) its closure meets
  `Γ₁` only at `s̃₁`. But the contact of the reduction is a later point of `Γ₁` in that closure.
  This is Lemma 12.
* So the lift of `w` is a point `Γ₁ u'` with `u' > 0`. Since Reductions 1 and 2 do not apply and
  `s₁` has valency at least two, the lift of the prefix `P₁[s₁, w]` is not in the closure of the
  lifted region (`cut_initial_boundary_arc_not_subset_region_closure_of_no_reductions12`),
  so `w` is a contact that `FIND_4` tests, and the cut path is a path of the graph `A_{1,j}`.

The main result is `exists_cut_walk_of_reduction4Step_one`.
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- Projection of the cut disc is projection of its cover point. -/
theorem cutProj_eq_cover (p : D) : cutProj D p = cylinderCoverProjection (cutCov D p) := rfl

/-- A curve whose aligned lift stays in the closure of the lifted region lifts into the cut disc. -/
theorem exists_cut_lift (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hθ : L.HasTheta θ) (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (q : Curve ClosedCylinder) (a : ℝ)
    (hqR : range (cylinderCurveLiftAt q a) ⊆ closure (cylinderCoverRegion 1 G 0)) :
    ∃ c : C(𝕀, D), ∀ t, cutCov D (c t) = cylinderCurveLiftAt q a t := by
  have hsub := closure_cylinderCoverRegion_subset_single_strip L hG hθ hD hBd hstrip
  have hmem : ∀ t, ∃ p : D, cutCov D p = cylinderCurveLiftAt q a t := by
    intro t
    obtain ⟨x, hx, hxe⟩ := hsub (hqR (mem_range_self t))
    exact ⟨⟨x, hx⟩, hxe⟩
  choose c hc using hmem
  have hemb := isClosedEmbedding_single_strip_coverMap hD hstrip
  have hcont : Continuous c := by
    rw [hemb.isEmbedding.continuous_iff]
    have : (fun p : D => planeToCylinderCover p.1) ∘ c = cylinderCurveLiftAt q a :=
      funext hc
    rw [this]
    exact (cylinderCurveLiftAt q a).continuous
  exact ⟨⟨c, hcont⟩, hc⟩

/-- **Lifting a path of `G` into the cut drawing.** Let `g` lift the points of a subdrawing `Q₁` of
`G` into the cut disc, continuously and injectively. If `Q₁` has no edge of the linkage path and no
loop, then `g` carries `Q₁` into the cut drawing `F`: each edge `e` goes to the full preimage of
`e`, which is an edge of `F`. -/
theorem isCarry_cut_lift (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hθ : L.HasTheta θ) (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {Q₁ : Drawing ClosedCylinder} (hQ₁G : Q₁.IsSubdrawing G) {g : ClosedCylinder → D}
    (hg : ContinuousOn g Q₁.U) (hginj : InjOn g Q₁.U) (hpg : ∀ y ∈ Q₁.U, cutProj D (g y) = y)
    (hnoP : ∀ e ∈ Q₁.E, e ∉ (L.pathDrawing 0).E) (hnoloop : ∀ e ∈ Q₁.E, ∀ x, ¬ Q₁.toGraph.IsLink e x x) :
    GM07.IsCarry Q₁ F g Q₁.V := by
  refine ⟨hg, hginj, fun x hx => ⟨hx, ?_⟩, ?_⟩
  · rw [hFV]
    change cutProj D (g x) ∈ G.V
    rw [hpg x (Q₁.V_subset_U hx)]
    exact hQ₁G.1 hx
  intro e he x y hcap hx
  have hy : y ∈ Q₁.V :=
    (show y ∈ closure e ∩ Q₁.V from hcap.symm ▸ mem_insert_of_mem x rfl).2
  have heG : e ∈ G.E := hQ₁G.2 he
  have heU : closure e ⊆ Q₁.U := Q₁.closure_subset_U he
  have hcl : g '' closure e ⊆ closure (g '' e) := (hg.mono heU).image_closure
  have hdisj : Disjoint e (L.pathDrawing 0).U :=
    GM11.edge_disjoint_U (L.isSubdrawing 0).1 heG (hnoP e he)
  have hpre : g '' e = cutProj D ⁻¹' e := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      change cutProj D (g z) ∈ e
      rw [hpg z (subset_closure.trans heU hz)]
      exact hz
    · intro hp
      have hpe : cutProj D p ∈ e := hp
      have hpQ : cutProj D p ∈ Q₁.U := subset_closure.trans heU hpe
      refine ⟨cutProj D p, hpe, ?_⟩
      exact (single_strip_projection_inj_off_path L hG hθ hD hBd hstrip
        (fun h => disjoint_left.mp hdisj hpe h) (hpg _ hpQ).symm).symm
  have heF : g '' e ∈ F.E := by
    rw [hpre]
    exact full_preimage_non_seam_edge_mem L hG hθ hD hBd hstrip F hFU hFV hEdges heG (hnoP e he)
  have hxy : x ≠ y := by
    intro h
    subst h
    exact hnoloop e he x ⟨he, hx, hx, by rw [hcap, pair_eq_singleton]⟩
  have hgx : g x ∈ F.V := by
    rw [hFV]; change cutProj D (g x) ∈ G.V; rw [hpg x (Q₁.V_subset_U hx)]; exact hQ₁G.1 hx
  have hgy : g y ∈ F.V := by
    rw [hFV]; change cutProj D (g y) ∈ G.V; rw [hpg y (Q₁.V_subset_U hy)]; exact hQ₁G.1 hy
  have hxe : x ∈ closure e := (show x ∈ closure e ∩ Q₁.V from hcap.symm ▸ mem_insert x _).1
  have hye : y ∈ closure e := (show y ∈ closure e ∩ Q₁.V from hcap.symm ▸ mem_insert_of_mem x rfl).1
  have hlink := isLink_of_distinct_vertices_in_closure heF hgx hgy
    (fun h => hxy (hginj (Q₁.V_subset_U hx) (Q₁.V_subset_U hy) h))
    (hcl (mem_image_of_mem g hxe)) (hcl (mem_image_of_mem g hye))
  exact ⟨hy, heF, hlink.2.2.2, hcl⟩

/-- The inverse of an embedding is continuous on its range. -/
theorem continuousOn_invFun_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] {f : X → Y} (hf : IsEmbedding f) :
    ContinuousOn (Function.invFun f) (range f) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (range f).domRestrict (Function.invFun f) = hf.toHomeomorph.symm := by
    funext y
    apply hf.injective
    change f (Function.invFun f y.1) = _
    rw [Function.invFun_eq y.2]
    exact (congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply y)).symm
  rw [this]
  exact Homeomorph.continuous _

/-- The curve `q` run on `[0, t]`. -/
@[expose] def scaleCurve {X : Type*} [TopologicalSpace X] (q : C(𝕀, X)) (t : 𝕀) : C(𝕀, X) :=
  ⟨fun s => q (s * t), q.continuous.comp (continuous_id.mul continuous_const)⟩

theorem range_scaleCurve {X : Type*} [TopologicalSpace X] (q : C(𝕀, X)) (t : 𝕀) :
    range (scaleCurve q t) = q '' Icc 0 t := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s * t, ⟨unitInterval.nonneg', unitInterval.mul_le_right⟩, rfl⟩
  · rintro ⟨r, ⟨-, hr⟩, rfl⟩
    by_cases ht : (t : ℝ) = 0
    · have hr0 : r = 0 := by
        apply Subtype.ext
        exact le_antisymm (le_trans hr (le_of_eq ht)) r.2.1
      have ht0 : t = 0 := Subtype.ext ht
      refine ⟨0, ?_⟩
      change q (0 * t) = q r
      rw [zero_mul, hr0]
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
      have hle : (r : ℝ) / t ≤ 1 := (div_le_one htpos).mpr hr
      refine ⟨⟨(r : ℝ) / t, div_nonneg r.2.1 t.2.1, hle⟩, ?_⟩
      change q (_ * t) = q r
      congr 1
      apply Subtype.ext
      change (r : ℝ) / t * t = r
      field_simp

theorem scaleCurve_injective {X : Type*} [TopologicalSpace X] {q : C(𝕀, X)}
    (hq : Function.Injective q) {t : 𝕀} (ht : t ≠ 0) : Function.Injective (scaleCurve q t) := by
  intro a b hab
  have h := hq hab
  have ht' : (t : ℝ) ≠ 0 := fun h0 => ht (Subtype.ext h0)
  apply Subtype.ext
  have := congrArg Subtype.val h
  change (a : ℝ) * t = (b : ℝ) * t at this
  exact mul_right_cancel₀ ht' this

/-- The aligned lift of `q` run on `[0, t]` is the lift of `q` run on `[0, t]`. -/
theorem cylinderCurveLiftAt_scaleCurve (q : Curve ClosedCylinder) (a : ℝ)
    (ha : Circle.exp a = (q 0).1.2) (t : 𝕀) (s : 𝕀) :
    cylinderCurveLiftAt (scaleCurve q t) a s = cylinderCurveLiftAt q a (s * t) := by
  let qc : C(𝕀, CylinderCover) := scaleCurve (cylinderCurveLiftAt q a) t
  have hproj : ∀ r, cylinderCoverProjection (qc r) = scaleCurve q t r := fun r =>
    cylinderCoverProjection_curveLiftAt q a ha (r * t)
  have h := cylinderCurveLiftAt_eq_of_cover_lift (scaleCurve q t) qc hproj
  have h0 : (qc 0).2 = a := by
    change (cylinderCurveLiftAt q a (0 * t)).2 = a
    rw [zero_mul, cylinderCurveLiftAt_zero]
  rw [h0] at h
  rw [h]
  rfl

/-- A point of the cut disc over the linkage path lies on one of the two lifts. -/
theorem mem_lifts_of_cutProj_mem_path (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) {p : D}
    (hp : cutProj D p ∈ (L.pathDrawing 0).U) :
    p.1 ∈ range (liftedLinkageCurve hG.1 L 1) ∨ p.1 ∈ range (liftedLinkageCurve hG.1 L 2) := by
  obtain ⟨τ, hτ⟩ := (L.curve_parametrizes 0).2.1.symm ▸ hp
  have hΓD : liftedLinkageCurve hG.1 L 1 τ ∈ D := by
    apply Surface.discBd_subset D
    rw [hBd]
    exact Or.inl (Or.inl (Or.inl (mem_range_self τ)))
  have heq : radialCylinderProjection p.1 = radialCylinderProjection (liftedLinkageCurve hG.1 L 1 τ) := by
    rw [radialCylinderProjection_lift_one]
    exact hτ.symm
  rcases radialCylinderProjection_single_strip_fibers L hG hθ 1 hD hBd hstrip p.2 hΓD heq with
    h | ⟨t, ⟨h, -⟩ | ⟨-, h⟩⟩
  · exact Or.inl ⟨τ, h.symm⟩
  · exact Or.inr ⟨t, h.symm⟩
  · exact Or.inl ⟨t, h.symm⟩

/-- A vertex of the cut drawing on the boundary of the cut disc lies over the linkage path. -/
theorem cutProj_mem_path_of_mem_bd (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) {p : D} (hpV : cutProj D p ∈ G.V)
    (hpbd : p ∈ bd D) : cutProj D p ∈ (L.pathDrawing 0).U := by
  rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip] at hpbd
  rcases hpbd with hcyl | hP
  · have hM : cutProj D p ∈ cylinderM1 1 ∪ cylinderM2 1 := by
      rw [← hG.2.2]
      exact ⟨hpV, hcyl⟩
    rcases hM with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hj0 : j = 0 := Subsingleton.elim _ _
      subst hj0
      rw [← hj]
      exact (L.pathDrawing 0).V_subset_U (isPathDrawing_end_vertices (L.isPath 0)).1
    · obtain ⟨j', hj'⟩ := L.curve_one_mem 0
      have hjj : j = j' := Subsingleton.elim _ _
      subst hjj
      rw [← hj, hj']
      exact (L.pathDrawing 0).V_subset_U (isPathDrawing_end_vertices (L.isPath 0)).2
  · exact hP

/-- A point of the cut disc is on its boundary exactly when it is in the intrinsic boundary. -/
theorem val_mem_discBd_iff (p : D) : p.1 ∈ discBd D ↔ p ∈ bd D := by
  constructor
  · rintro ⟨q, hq, heq⟩
    exact (Subtype.ext heq : q = p) ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

end GraphMinor.GM06
