module

public import GraphMinor.GM06.Alg57OnePathComplete
public import GraphMinor.GM06.Alg57OnePathPrefix
import GraphMinor.GM06.Section5CutRegion
import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CoverCurve
import GraphMinor.GM06.Section5IncidentPrefixValency
import GraphMinor.GM06.Section5LiftedPaths
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5SidedReduction4
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Alg57Reduction4Complete
import GraphMinor.GM11.Walks
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Rotation
import GraphMinor.GM11.CircuitRegions

/-!
# Lemma 12 and the completeness half of Lemma 13, for one path

Here we prove `exists_cut_path_of_reduction4Step_one`: when Reductions 1 and 2 do not apply and
`s₁` does not have valency one, every one-path Reduction 4 gives a path of the cut drawing `F`
of the kind `FIND_4` looks for. The plan is in the header of `Alg57OnePathComplete`.

Let `Q` be the new path of the reduction, and `q` its parametrization, whose aligned lift stays in
the closure of the lifted region. We lift `Q` into the cut disc `D` (`exists_cut_lift`) and cut
`Q` at its first vertex `w ≠ s₁` on the linkage path `P₁`. Call the first part `Q₁`.

* `Q₁` has no edge of `P₁` (`not_mem_path_edges_of_first_contact`). Such an edge would join `s₁`
  to `w`, so it would be a subpath of `P₁` from `s₁` whose lift stays in the closure of the
  region. Since Reductions 1 and 2 do not apply, this would force `s₁` to have valency one.
* So the lift of `Q₁` is a path of `F` (`isCarry_cut_lift`) that meets the boundary of `D` only at
  its two ends. Its end over `w` lies on one of the two lifts `Γ₁`, `Γ₂` of `P₁`.
* It is not on `Γ₂`. Otherwise the lifted path is a crosscut of `D` from the start of `Γ₁` to
  `Γ₂`, and Lemma 2 (`le_of_mem_closure_of_crosscut`) says the closure of the lifted region meets
  `Γ₁` only at its start. But the contact of the reduction is a later point of `Γ₁` in that
  closure. This is Lemma 12.
* So it is a point `Γ₁ u'` with `u' > 0`, and the lifted prefix up to `u'` is not in the closure of
  the region (`single_path_initial_lift_prefix_not_subset_coverRegion_of_no_reductions12`).
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- **The first part of the new path has no edge of `P₁`.** Let `Q` be a path of `G` from `s₁`
whose aligned lift stays in the closure of the lifted region, and let `W₁` be a simple walk of `Q`
from `s₁` to `w ≠ s₁` that meets `P₁` only at its two ends. If Reductions 1 and 2 do not apply
and `s₁` does not have valency one, then no edge of `W₁` is an edge of `P₁`. Such an edge would
join `s₁` to `w`, so it would be a subpath of `P₁` from `s₁` in the closure of the region, and
`valency_initial_eq_one_of_incident_prefix_of_no_reductions12` would give valency one. -/
theorem not_mem_path_edges_of_first_contact (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction1Step 1 G L H M)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction2Step 1 G L H M)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    {Q : Drawing ClosedCylinder} (hQG : Q.IsSubdrawing G) {v : ClosedCylinder}
    {q : Curve ClosedCylinder} (hq : ParametrizesSet q Q.U (cylinderM1Point 1 0) v)
    (hqR : range (cylinderCurveLiftAt q (cylinderInitialLift 1 0).2) ⊆
      closure (cylinderCoverRegion 1 G 0))
    {w : ClosedCylinder} (W₁ : GraphWalk Q.toGraph (cylinderM1Point 1 0) w)
    (hW₁ : W₁.IsSimple) (hsw : cylinderM1Point 1 0 ≠ w)
    (hfirst : ∀ y ∈ W₁.support, y ∈ (L.pathDrawing 0).U → y = cylinderM1Point 1 0 ∨ y = w)
    {e : Set ClosedCylinder} (he : e ∈ W₁.edges) : e ∉ (L.pathDrawing 0).E := by
  intro heP
  obtain ⟨y, y', hy, hy', hl⟩ := walk_exists_isLink_of_mem_edges W₁ he
  have hyy : y ≠ y' := by
    rintro rfl
    exact walk_not_isLink_self_of_nodup W₁ hW₁ he hl
  have hyP : y ∈ (L.pathDrawing 0).U := by
    have : y ∈ closure e ∩ Q.V := by rw [hl.2.2.2]; exact mem_insert _ _
    exact (L.pathDrawing 0).closure_subset_U heP this.1
  have hy'P : y' ∈ (L.pathDrawing 0).U := by
    have : y' ∈ closure e ∩ Q.V := by rw [hl.2.2.2]; exact mem_insert_of_mem _ rfl
    exact (L.pathDrawing 0).closure_subset_U heP this.1
  have hlG : G.toGraph.IsLink e y y' := (hQG.isLink_iff hl.1).mp hl
  have hlink : G.toGraph.IsLink e (cylinderM1Point 1 0) w := by
    rcases hfirst y hy hyP with rfl | rfl <;> rcases hfirst y' hy' hy'P with rfl | rfl
    · exact absurd rfl hyy
    · exact hlG
    · exact hlG.symm
    · exact absurd rfl hyy
  -- the one-edge path along `e`
  let W' : GraphWalk G.toGraph (cylinderM1Point 1 0) w := .cons hlink (.nil hlink.right_mem)
  have hW' : W'.IsSimple := by
    change [(cylinderM1Point 1 0), w].Nodup
    simp [hsw]
  have hQ' : IsPathDrawing (walkDrawing G W') (cylinderM1Point 1 0) w := isPathDrawing_walkDrawing_of_isSimple G hW' hsw
  have hcl : (walkDrawing G W').U ⊆ closure e := by
    intro x hx
    rw [mem_walkDrawing_U] at hx
    have hsw' : (cylinderM1Point 1 0) ∈ closure e ∩ G.V ∧ w ∈ closure e ∩ G.V := by
      rw [hlink.2.2.2]
      exact ⟨mem_insert _ _, mem_insert_of_mem _ rfl⟩
    rcases hx with hx | ⟨e', he', hxe⟩
    · change x ∈ [(cylinderM1Point 1 0), w] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hsw'.1.1
      · exact hsw'.2.1
    · change e' ∈ [e] at he'
      rw [List.mem_singleton] at he'
      exact he' ▸ hxe
  have heQ : e ∈ Q.E := hl.1
  have hQ'Q : (walkDrawing G W').U ⊆ Q.U := hcl.trans (Q.closure_subset_U heQ)
  have hQ'P : (walkDrawing G W').U ⊆ (L.pathDrawing 0).U := hcl.trans ((L.pathDrawing 0).closure_subset_U heP)
  have hsub : IsSubpathOf G (walkDrawing G W') (cylinderM1Point 1 0) w :=
    ⟨walkDrawing_isSubdrawing G W', (walkDrawing_isSubdrawing G W').U_subset, hQ'⟩
  -- its parametrization is an initial part of `q`
  obtain ⟨g', hg'i, hg'r, hg'0, hg'1⟩ := hQ'.2
  have hwQ : w ∈ range q := by
    rw [hq.2.1]
    exact hQ'Q ((walkDrawing G W').V_subset_U (isPathDrawing_end_vertices hQ').2)
  obtain ⟨b, hb⟩ := hwQ
  have hrange : range g' = q '' uIcc 0 b :=
    range_eq_image_uIcc_of_subarc hq.1 hg'i (by rw [hg'r, hq.2.1]; exact hQ'Q)
      (by rw [hg'0, hq.2.2.1]) (by rw [hg'1, hb])
  have hb0 : b ≠ 0 := by
    intro h
    apply hsw
    rw [← hb, h]
    exact hq.2.2.1.symm
  have hparam : ParametrizesSet (scaleCurve q b) (walkDrawing G W').U (cylinderM1Point 1 0) w := by
    refine ⟨scaleCurve_injective hq.1 hb0, ?_, ?_, ?_⟩
    · rw [range_scaleCurve, ← uIcc_of_le unitInterval.nonneg', ← hrange, hg'r]
    · change q (0 * b) = (cylinderM1Point 1 0)
      rw [zero_mul]
      exact hq.2.2.1
    · change q (1 * b) = w
      rw [one_mul]
      exact hb
  have ha : Circle.exp (cylinderInitialLift 1 0).2 = (q 0).1.2 := by
    rw [hq.2.2.1]
    rfl
  have hlift : range (cylinderCurveLiftAt (scaleCurve q b) (cylinderInitialLift 1 0).2) ⊆
      closure (cylinderCoverRegion 1 G 0) := by
    rintro _ ⟨r, rfl⟩
    rw [cylinderCurveLiftAt_scaleCurve q _ ha b r]
    exact hqR (mem_range_self _)
  exact hval (valency_initial_eq_one_of_incident_prefix_of_no_reductions12 L hG hθ hno1 hno2
    hsub hQ'P (scaleCurve q b) hparam hlift)

/-- The lift `Γ₂` does not pass through the start `(1, 2π)` of `Γ₁`. -/
theorem start_not_mem_range_liftedLinkageCurve_two (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) :
    ((1 : ℝ), 2 * π) ∉ range (liftedLinkageCurve hG.1 L 2) := by
  rintro ⟨t, ht⟩
  have hraw := liftedLinkageCurve_props_raw hG.1 L 2
  by_cases h0 : t = 0
  · subst h0
    have h2 := hraw.2.2.2.1
    rw [ht] at h2
    simp only at h2
    push_cast at h2
    nlinarith [Real.pi_pos]
  by_cases h1 : t = 1
  · subst h1
    have h2 := hraw.2.2.1
    rw [ht] at h2
    simp only at h2
    norm_num at h2
  · have hr := (liftedLinkageCurve_interior_radius L hG 2
      ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr h1⟩).1
    rw [ht] at hr
    simp at hr

/-- **Lemma 12 and the completeness half of Lemma 13, for `k = 1`.** Assume Reductions 1 and 2 do
not apply and `s₁` does not have valency one. If a one-path Reduction 4 applies, then some vertex
`Γ₁ u` of the lift of `P₁` with `u > 0` has a lifted prefix not in the closure of the lifted
region, and the cut drawing `F` has a path from the start of `Γ₁` to `Γ₁ u` that misses `Γ₂`,
meets `Γ₁` only at its ends, has edges over edges of `G`, and lies over the closure of the
lifted region. -/
theorem exists_cut_path_of_reduction4Step_one (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction1Step 1 G L H M)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction2Step 1 G L H M)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {L' : CylinderLinkage 1 G} (h : Section5Reduction4Step 1 G L G L') :
    ∃ u : 𝕀, 0 < u ∧ L.curve 0 u ∈ (L.pathDrawing 0).V ∧
      ¬ (cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 '' Icc 0 u ⊆
        closure (cylinderCoverRegion 1 G 0)) ∧
      ∃ (s w : D) (Q : Drawing D), IsSubpathOf F Q s w ∧ s.1 = (1, 2 * π) ∧
        w.1 = liftedLinkageCurve hG.1 L 1 u ∧
        (∀ p ∈ Q.U, p.1 ∉ range (liftedLinkageCurve hG.1 L 2)) ∧
        (∀ p ∈ Q.U, p.1 ∈ range (liftedLinkageCurve hG.1 L 1) → p = s ∨ p = w) ∧
        (∀ ec ∈ Q.E, cutProj D '' ec ∈ G.E) ∧
        cutCov D '' Q.U ⊆ closure (cylinderCoverRegion 1 G 0) := by
  classical
  obtain ⟨-, i, u, T, Q, q, huV, -, -, -, hQG, -, hQ, hq, hqR, hq1, -, -⟩ :=
    section5Reduction4Step_iff_of_one.mp h
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hPG : (L.pathDrawing 0).IsSubdrawing G := (L.isSubdrawing 0).1
  have hemb := isClosedEmbedding_single_strip_coverMap hD hstrip
  have h12 : liftedLinkageCurve hG.1 L (1 + 1) = liftedLinkageCurve hG.1 L 2 := rfl
  have hΓbd (t : 𝕀) : liftedLinkageCurve hG.1 L 1 t ∈ discBd D := by
    rw [hBd]
    exact Or.inl (Or.inl (Or.inl (mem_range_self t)))
  have hΓ'bd (t : 𝕀) : liftedLinkageCurve hG.1 L 2 t ∈ discBd D := by
    rw [hBd, liftedStripBoundary, h12]
    exact Or.inl (Or.inl (Or.inr (mem_range_self t)))
  have hΓD (t : 𝕀) : liftedLinkageCurve hG.1 L 1 t ∈ D := Surface.discBd_subset D (hΓbd t)
  have hΓcov (t : 𝕀) : cutCov D ⟨_, hΓD t⟩ =
      cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 t :=
    (cylinderCurveLiftAt_linkage_one L hG.1 t).symm
  have hΓ0 : liftedLinkageCurve hG.1 L 1 0 = (1, 2 * π) := by
    apply Prod.ext
    · exact (liftedLinkageCurve_props_raw hG.1 L 1).2.1
    · simpa using (liftedLinkageCurve_props_raw hG.1 L 1).2.2.2.1
  have hsv : cylinderM1Point 1 0 ≠ L.curve 0 u := isPathDrawing_start_ne_end hQ
  have hu0 : 0 < u := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun h0 => hsv ?_
    rw [← h0]
    exact (L.curve_parametrizes 0).2.2.1.symm
  -- the lift of `q` into the cut disc
  have ha : Circle.exp (cylinderInitialLift 1 0).2 = (q 0).1.2 := by
    rw [hq.2.2.1]
    rfl
  obtain ⟨c, hc⟩ := exists_cut_lift L hG hθ hD hBd hstrip q _ hqR
  have hcP (t : 𝕀) : cutProj D (c t) = q t := by
    rw [cutProj_eq_cover, hc]
    exact cylinderCoverProjection_curveLiftAt q _ ha t
  have hc0 : c 0 = ⟨_, hΓD 0⟩ := by
    apply hemb.injective
    change cutCov D (c 0) = cutCov D ⟨_, hΓD 0⟩
    rw [hc, hΓcov, cylinderCurveLiftAt_zero, cylinderCurveLiftAt_zero, hq.2.2.1,
      (L.curve_parametrizes 0).2.2.1]
  have hc1 : c 1 = ⟨_, hΓD u⟩ := by
    apply hemb.injective
    change cutCov D (c 1) = cutCov D ⟨_, hΓD u⟩
    rw [hc, hΓcov]
    exact hq1
  let g : ClosedCylinder → D := fun y => c (Function.invFun q y)
  have hgq (t : 𝕀) : g (q t) = c t := by
    change c (Function.invFun q (q t)) = c t
    rw [Function.leftInverse_invFun hq.1 t]
  have hpg : ∀ y ∈ Q.U, cutProj D (g y) = y := by
    intro y hy
    rw [← hq.2.1] at hy
    obtain ⟨t, rfl⟩ := hy
    rw [hgq, hcP]
  have hgcov : ∀ y ∈ Q.U, cutCov D (g y) ∈ closure (cylinderCoverRegion 1 G 0) := by
    intro y hy
    rw [← hq.2.1] at hy
    obtain ⟨t, rfl⟩ := hy
    rw [hgq, hc]
    exact hqR (mem_range_self t)
  have hgcont : ContinuousOn g Q.U := by
    rw [← hq.2.1]
    exact c.continuous.comp_continuousOn
      (continuousOn_invFun_range (q.continuous.isClosedEmbedding hq.1).isEmbedding)
  have hginj : InjOn g Q.U := fun y hy y' hy' hyy => by
    rw [← hpg y hy, ← hpg y' hy', hyy]
  have hgs : g (cylinderM1Point 1 0) = c 0 := by
    rw [← hq.2.2.1, hgq]
  -- cut the walk of `Q` at its first vertex on `P₁` after `s₁`
  obtain ⟨W, hW, hVQ, -⟩ := hQ.1
  obtain ⟨w, hwX, W₁, W₂, hsplit, hfirst⟩ := walk_exists_append_first_mem W
    {x | x ∈ (L.pathDrawing 0).U ∧ x ≠ cylinderM1Point 1 0}
    ⟨(L.pathDrawing 0).V_subset_U huV, hsv.symm⟩
  have hW₁ : W₁.IsSimple := by
    have hn := hW
    change W.support.Nodup at hn
    rw [hsplit, GraphWalk.support_append] at hn
    exact hn.of_append_left
  have hsuppQ : ∀ y ∈ W₁.support, y ∈ Q.V := by
    intro y hy
    rw [hVQ]
    change y ∈ W.support
    rw [hsplit, GraphWalk.support_append]
    exact List.mem_append_left _ hy
  have hsw : cylinderM1Point 1 0 ≠ w := fun h => hwX.2 h.symm
  have hfirst' : ∀ y ∈ W₁.support, y ∈ (L.pathDrawing 0).U →
      y = cylinderM1Point 1 0 ∨ y = w := by
    intro y hy hyP
    by_cases hys : y = cylinderM1Point 1 0
    · exact Or.inl hys
    · exact Or.inr (hfirst y hy ⟨hyP, hys⟩)
  have hnoP : ∀ e ∈ W₁.edges, e ∉ (L.pathDrawing 0).E := fun e he =>
    not_mem_path_edges_of_first_contact L hG hθ hno1 hno2 hval hQG hq hqR W₁ hW₁ hsw hfirst' he
  have hsQ : cylinderM1Point 1 0 ∈ Q.U := Q.V_subset_U (hsuppQ _ W₁.start_mem_support)
  have hwQ : w ∈ Q.U := Q.V_subset_U (hsuppQ _ W₁.end_mem_support)
  -- the first part as a drawing, carried into the cut drawing
  have hQ₁Q : (walkDrawing Q W₁).IsSubdrawing Q := walkDrawing_isSubdrawing Q W₁
  have hQ₁G := hQ₁Q.trans hQG
  have hQ₁U : (walkDrawing Q W₁).U ⊆ Q.U := hQ₁Q.U_subset
  have hnoloop : ∀ e ∈ (walkDrawing Q W₁).E, ∀ x, ¬ (walkDrawing Q W₁).toGraph.IsLink e x x := by
    intro e he x hx
    have he' : e ∈ W₁.edges := by rw [walkDrawing_E] at he; exact he
    exact walk_not_isLink_self_of_nodup W₁ hW₁ he' ((hQ₁Q.isLink_iff he).mp hx)
  have hcarry := isCarry_cut_lift L hG hθ hD hBd hstrip F hFU hFV hEdges hQ₁G
    (hgcont.mono hQ₁U) (hginj.mono hQ₁U) (fun y hy => hpg y (hQ₁U hy))
    (fun e he => hnoP e (by rw [walkDrawing_E] at he; exact he)) hnoloop
  obtain ⟨W₁', hW₁'s, hW₁'e⟩ := hQ₁Q.exists_walk_down W₁
    (fun x hx => by rw [walkDrawing_V]; exact hx) (fun e he => by rw [walkDrawing_E]; exact he)
  obtain ⟨Wt, hWts, hWte, -, -⟩ := hcarry.walk W₁'
    (by rw [walkDrawing_V]; exact W₁.start_mem_support) _ (g w) rfl rfl
  have hWt : Wt.IsSimple := by
    change Wt.support.Nodup
    rw [hWts, hW₁'s]
    exact hW₁.map_on fun x hx y hy hxy =>
      hginj (Q.V_subset_U (hsuppQ x hx)) (Q.V_subset_U (hsuppQ y hy)) hxy
  have hgsw : g (cylinderM1Point 1 0) ≠ g w := fun h => hsw (hginj hsQ hwQ h)
  have hQt : IsPathDrawing (walkDrawing F Wt) (g (cylinderM1Point 1 0)) (g w) :=
    isPathDrawing_walkDrawing_of_isSimple F hWt hgsw
  -- every point of the lifted path is the lift of a point of the first part
  have hQtU : ∀ p ∈ (walkDrawing F Wt).U, ∃ y ∈ (walkDrawing Q W₁).U, p = g y := by
    intro p hp
    rw [mem_walkDrawing_U] at hp
    rcases hp with hp | ⟨ec, hec, hpe⟩
    · rw [hWts, hW₁'s, List.mem_map] at hp
      obtain ⟨y, hy, rfl⟩ := hp
      exact ⟨y, (walkDrawing Q W₁).V_subset_U (by rw [walkDrawing_V]; exact hy), rfl⟩
    · rw [hWte, hW₁'e, List.mem_map] at hec
      obtain ⟨e, he, rfl⟩ := hec
      have heQ₁ : e ∈ (walkDrawing Q W₁).E := by rw [walkDrawing_E]; exact he
      have hcl : closure e ⊆ (walkDrawing Q W₁).U := (walkDrawing Q W₁).closure_subset_U heQ₁
      have hcomp : IsCompact (g '' closure e) :=
        isClosed_closure.isCompact.image_of_continuousOn (hgcont.mono (hcl.trans hQ₁U))
      obtain ⟨y, hy, rfl⟩ := closure_minimal (image_mono subset_closure) hcomp.isClosed hpe
      exact ⟨y, hcl hy, rfl⟩
  -- the lifted path meets the boundary of the cut disc only at its ends
  have hbd : ∀ y ∈ (walkDrawing Q W₁).U, g y ∈ bd D → y = cylinderM1Point 1 0 ∨ y = w := by
    intro y hy hyb
    have hy' := hpg y (hQ₁U hy)
    by_cases hyV : y ∈ (walkDrawing Q W₁).V
    · have hyP := cutProj_mem_path_of_mem_bd L hG hθ hD hBd hstrip
        (by rw [hy']; exact hQ₁G.1 hyV) hyb
      rw [hy'] at hyP
      rw [walkDrawing_V] at hyV
      exact hfirst' y hyV hyP
    · exfalso
      obtain ⟨e, he, hye⟩ := (walkDrawing Q W₁).exists_edge_of_mem hy hyV
      have heG := hQ₁G.2 he
      rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip] at hyb
      change cutProj D (g y) ∈ bd ClosedCylinder ∪ (L.pathDrawing 0).U at hyb
      rw [hy'] at hyb
      rcases hyb with hb | hb
      · exact edge_notMem_V heG hye (hG.2.1 ⟨hb, G.closure_subset_U heG (subset_closure hye)⟩)
      · exact disjoint_left.mp (GM11.edge_disjoint_U hPG heG
          (hnoP e (by rw [walkDrawing_E] at he; exact he))) hye hb
  have hwlift := mem_lifts_of_cutProj_mem_path L hG hθ hD hBd hstrip (p := g w)
    (by rw [hpg w hwQ]; exact hwX.1)
  -- Lemma 12: the lifted path does not end on `Γ₂`
  have hnotΓ' : (g w).1 ∉ range (liftedLinkageCurve hG.1 L 2) := by
    rintro ⟨β, hβ⟩
    obtain ⟨φ, hφi, hφr, hφ0, hφ1⟩ := hQt.2
    obtain ⟨hZR, hZcl⟩ := preimage_coverRegion_sdiff_boundary_mem_regions L hG hθ hD hBd hstrip F hFU
    set Z := (cutCov D ⁻¹' cylinderCoverRegion 1 G 0) \ bd D with hZ
    have hZR' : Z ∈ F.R := hZR
    have hZcl' : cutCov D '' closure Z = closure (cylinderCoverRegion 1 G 0) := hZcl
    have hφU (t : 𝕀) : ∃ y ∈ (walkDrawing Q W₁).U, φ t = g y :=
      hQtU (φ t) (hφr ▸ mem_range_self t)
    have hcin : ∀ t, t ≠ 0 → t ≠ 1 → (φ t).1 ∈ D \ discBd D := by
      intro t ht0 ht1
      refine ⟨(φ t).2, fun hb => ?_⟩
      obtain ⟨y, hy, hyeq⟩ := hφU t
      rcases hbd y hy (hyeq ▸ (val_mem_discBd_iff _).mp hb) with rfl | rfl
      · exact ht0 (hφi (by rw [hφ0, hyeq]))
      · exact ht1 (hφi (by rw [hφ1, hyeq]))
    have hCpre : IsPreconnected (Subtype.val '' Z) :=
      (GM11.region_isPreconnected hZR').image _ continuous_subtype_val.continuousOn
    have hCD : Subtype.val '' Z ⊆ D \ discBd D := by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨p.2, fun hb => hp.2 ((val_mem_discBd_iff p).mp hb)⟩
    have hCc : Disjoint (Subtype.val '' Z) (range fun t => (φ t).1) := by
      rw [disjoint_left]
      rintro _ ⟨p, hp, rfl⟩ ⟨t, ht⟩
      have hpt : φ t = p := Subtype.ext ht
      obtain ⟨y, hy, hyeq⟩ := hφU t
      have hoff := (connectedComponentIn_subset _ _
        (show cutCov D p ∈ connectedComponentIn _ _ from hp.1)).2
      apply hoff
      change cutProj D p ∈ G.U
      rw [← hpt, hyeq, hpg y (hQ₁U hy)]
      exact hQG.U_subset (hQ₁U hy)
    have hy : (liftedLinkageCurve hG.1 L 1 0).2 < 3 * π ∧
        3 * π < (liftedLinkageCurve hG.1 L (1 + 1) 0).2 := by
      rw [(liftedLinkageCurve_props_raw hG.1 L 1).2.2.2.1,
        (liftedLinkageCurve_props_raw hG.1 L (1 + 1)).2.2.2.1]
      push_cast
      constructor <;> nlinarith [Real.pi_pos]
    have hyC : ((1 : ℝ), 3 * π) ∈ closure (Subtype.val '' Z) := by
      let b : CylinderCover := (⟨1, by norm_num⟩,
        (2 * (((0 : Fin 1).val + 1 : ℕ) : ℝ) + 1) * π / (1 : ℕ))
      have hb : b ∈ cylinderCoverRegion 1 G 0 := by
        unfold cylinderCoverRegion
        apply mem_connectedComponentIn
        exact ⟨mem_univ _, cylinderN1Point_not_mem_U hG 0⟩
      have hb' : b ∈ cutCov D '' closure Z := by
        rw [hZcl']
        exact subset_closure hb
      obtain ⟨p, hpZ, hpb⟩ := hb'
      have h1 : max 1 (min 2 p.1.1) = 1 := congrArg (fun z : CylinderCover => z.1.1) hpb
      have h2 : p.1.2 = (2 * (((0 : Fin 1).val + 1 : ℕ) : ℝ) + 1) * π / (1 : ℕ) :=
        congrArg Prod.snd hpb
      have hs := hstrip p.2
      have hp1 : p.1.1 = 1 := by
        rw [min_eq_right hs.2, max_eq_right hs.1] at h1
        exact h1
      have hpeq : p.1 = ((1 : ℝ), 3 * π) := by
        apply Prod.ext hp1
        rw [h2]
        norm_num
      rw [← hpeq]
      exact image_closure_subset_closure_image continuous_subtype_val ⟨p, hpZ, rfl⟩
    have ht : liftedLinkageCurve hG.1 L 1 u ∈ closure (Subtype.val '' Z) := by
      have hmem : cutCov D (c 1) ∈ closure (cylinderCoverRegion 1 G 0) := by
        rw [hc]
        exact hqR (mem_range_self 1)
      rw [← hZcl'] at hmem
      obtain ⟨p, hpZ, hpc⟩ := hmem
      have hp : p = c 1 := hemb.injective hpc
      have : liftedLinkageCurve hG.1 L 1 u = p.1 := by rw [hp, hc1]
      rw [this]
      exact image_closure_subset_closure_image continuous_subtype_val ⟨p, hpZ, rfl⟩
    have hle := le_of_mem_closure_of_crosscut L hG 1 hD hBd (c := fun t => (φ t).1)
      ⟨continuous_subtype_val.comp φ.continuous, fun a b hab => hφi (Subtype.ext hab)⟩
      (α := 0) (β := β) (by rw [hφ0, hgs, hc0])
      (by rw [hφ1, h12, hβ]) hcin hCpre hCD hCc hy hyC ht
    exact absurd hle (not_le.mpr hu0)
  -- so the lifted path ends on `Γ₁`, at a later point
  obtain ⟨u', hu'⟩ := hwlift.resolve_right hnotΓ'
  have hgs1 : (g (cylinderM1Point 1 0)).1 = (1, 2 * π) := by
    rw [hgs, hc0]
    exact hΓ0
  have hu'0 : 0 < u' := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun h0 => hgsw (Subtype.ext ?_)
    rw [hgs1, ← hu', ← h0, hΓ0]
  have hcurve : L.curve 0 u' = w := by
    have hw' := hpg w hwQ
    change radialCylinderProjection (g w).1 = w at hw'
    rw [← hu', radialCylinderProjection_lift_one] at hw'
    exact hw'
  have hu'V : L.curve 0 u' ∈ (L.pathDrawing 0).V := by
    rw [hcurve]
    exact mem_V_of_mem_U_of_isSubdrawing hPG hwX.1 (hQG.1 (hsuppQ _ W₁.end_mem_support))
  refine ⟨u', hu'0, hu'V,
    single_path_initial_lift_prefix_not_subset_coverRegion_of_no_reductions12 L hG hθ hno1 hno2
      hval hD hBd hstrip u' hu'0 hu'V,
    g (cylinderM1Point 1 0), g w, walkDrawing F Wt,
    ⟨walkDrawing_isSubdrawing F Wt, (walkDrawing_isSubdrawing F Wt).U_subset, hQt⟩,
    hgs1, hu'.symm, ?_, ?_, ?_, ?_⟩
  · intro p hp hpΓ
    obtain ⟨y, hy, rfl⟩ := hQtU p hp
    obtain ⟨t, ht⟩ := hpΓ
    have hb : g y ∈ bd D := (val_mem_discBd_iff _).mp (ht ▸ hΓ'bd t)
    rcases hbd y hy hb with rfl | rfl
    · exact start_not_mem_range_liftedLinkageCurve_two L hG (hgs1 ▸ ⟨t, ht⟩)
    · exact hnotΓ' ⟨t, ht⟩
  · intro p hp hpΓ
    obtain ⟨y, hy, rfl⟩ := hQtU p hp
    obtain ⟨t, ht⟩ := hpΓ
    have hb : g y ∈ bd D := (val_mem_discBd_iff _).mp (ht ▸ hΓbd t)
    rcases hbd y hy hb with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro ec hec
    rw [walkDrawing_E] at hec
    change ec ∈ Wt.edges at hec
    rw [hWte, hW₁'e, List.mem_map] at hec
    obtain ⟨e, he, rfl⟩ := hec
    have heQ : e ∈ Q.E := hQ₁Q.2 (by rw [walkDrawing_E]; exact he)
    have heU : e ⊆ Q.U := subset_closure.trans (Q.closure_subset_U heQ)
    have himg : cutProj D '' (g '' e) = e := by
      rw [image_image]
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        change cutProj D (g z) ∈ e
        rw [hpg z (heU hz)]
        exact hz
      · intro hy
        exact ⟨y, hy, hpg y (heU hy)⟩
    rw [himg]
    exact hQG.2 heQ
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hQtU p hp
    exact hgcov y (hQ₁U hy)

end GraphMinor.GM06
