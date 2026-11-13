module

public import GraphMinor.GM06.Alg57OnePathInnerSides
public import GraphMinor.GM06.Alg57OnePathEnd
import GraphMinor.GM06.Section5CutRegionCoordinates
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CappedBarrierNice
import GraphMinor.GM06.Section5CoverRegion

/-!
# The sides of the rays at the end of the one path

At the end `x = P₁(1)` the outer cuff is one loop edge with darts `c⁺` (`false`) and `c⁻`
(`true`). Let `a` be the dart of the last edge of `P₁` at `x`. The proof of `lifted_incidence_end`
splits a small star at `x` into the wedge from `c⁺` to `a`, on side one, the wedge from `a` to
`c⁻`, not on side one, and the corner after `c⁻`, outside the cylinder. We repeat that part of
the proof and read off the sides of the rays (`raySides_end`): the rays of the darts of the block
`c⁺, R.rot c⁺, …` before `a` are on side one, the others are not.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology Metric Real GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
  {U₁ U₂ : Set CylinderCover} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : Disjoint U₁ U₂)
  (h₁ : ∀ t, coverLift L hG 1 t ∈ U₁) (h₂ : ∀ t, coverLift L hG 2 t ∈ U₂)
  {H : Drawing ClosedCylinder} (hGH : G.IsSubdrawing H) (hFU : H.U = G.U ∪ bd ClosedCylinder)
  (hFV : H.V = G.V)
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing H))}
  (hγ : EdgePar (cylinderSphereDrawing H) γ) (hR : IsDrawingRotation (cylinderSphereDrawing H) γ R)
  (hccw : IsCcwRotation (cylinderSphereDrawing H) γ R)
  (heI : ∀ j : Fin 1, cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1) ∈
    (cylinderSphereDrawing H).E)
  (hγI : ∀ j : Fin 1, ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1)) t =
    cylinderToSphere (initialCuffGapCurve 1 j t))
  (heO : ∀ j : Fin 1, cylinderToSphere '' (alg511OuterCuffGapCurve 1 j '' Ioo 0 1) ∈
    (cylinderSphereDrawing H).E)
  (hγO : ∀ j : Fin 1, ∀ t, γ (cylinderToSphere '' (alg511OuterCuffGapCurve 1 j '' Ioo 0 1)) t =
    cylinderToSphere (alg511OuterCuffGapCurve 1 j t))
  (hV : ∀ v ∈ (cylinderSphereDrawing H).V, ∃ a : DrawingDart (cylinderSphereDrawing H),
    dartVertex γ a = v)

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI hγI hγO hV in
/-- **The sides of the rays at the end of `P₁`.** With `a` the dart of the last edge of `P₁` at
`P₁(1)`, the rays there are on side one exactly for the darts of the block `c⁺, R.rot c⁺, …`
before `a`, where `c⁺` is the `false` dart of the outer cuff loop. -/
theorem raySides_end {a : DrawingDart (cylinderSphereDrawing H)}
    (ha : dartVertex γ a = spherePath L 1) (haX : a.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₂ : ℝ} (ht₂ : t₂ ∈ Icc (0 : ℝ) 1) (htt₂ : t₂ < 1)
    (ha1 : dartVertex γ (dartFlip _ a) = spherePath L t₂) :
    RaySides L D U₁ γ R 1 (fun d => ∃ i, (∀ j ≤ i, R.rot^[j]
      ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), false), heO 0⟩ ≠ a) ∧
      R.rot^[i] ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), false), heO 0⟩ =
        d) := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  have hinf := infty_notMem_cylinderSphereDrawing_U H
  have hX := isGammaNice_spherePath L hGH
  have hf := continuous_spherePath L
  have hinj := injOn_spherePath L
  set eO := cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1) with heO_def
  set ct : DrawingDart (cylinderSphereDrawing H) := ⟨(eO, true), heO 0⟩ with hct_def
  set cf : DrawingDart (cylinderSphereDrawing H) := ⟨(eO, false), heO 0⟩ with hcf_def
  set R₁ := cylinderToSphere '' (cylinderRegion 1 G 0 \ bd ClosedCylinder)
  set X := cylinderToSphere '' (L.pathDrawing 0).U
  set Z := cylinderToSphere '' ((L.pathDrawing 0).U ∪ bd ClosedCylinder)
  have h01 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- the end of `P₁` and the darts of the outer cuff
  have hx1 : L.curve 0 1 = cylinderM2Point 1 0 := by
    obtain ⟨j, hj⟩ := L.curve_one_mem 0
    rw [← hj, Subsingleton.elim j 0]
  have hxc : spherePath L 1 = cylinderToSphere (L.curve 0 1) := spherePath_of_mem L h01
  have hxM : spherePath L 1 = cylinderToSphere (cylinderM2Point 1 0) := by rw [hxc, hx1]
  have hs1 : cylinderM2Point 1 (finSuccCycle 0) = cylinderM2Point 1 0 := by
    congr 1
  have hvct : dartVertex γ ct = spherePath L 1 := by
    rw [hxM, ← hs1, ← (alg511_outer_gap_ends hG 0).2]
    exact hγO 0 1
  have hvcf : dartVertex γ cf = spherePath L 1 := by
    rw [hxM, ← (alg511_outer_gap_ends hG 0).1]
    exact hγO 0 0
  have hrot : R.rot ct = cf := by
    have h := outer_cuff_rotation hG hGH hFU hFV hγ hR hccw heO hγO 0
    exact Subtype.ext h
  have hflipct : dartFlip _ ct = cf := rfl
  have hflipcf : dartFlip _ cf = ct := rfl
  have hact : a ≠ ct := by
    rintro rfl
    have := hinj ht₂ h01 (ha1.symm.trans (by rw [hflipct]; exact hvcf))
    linarith
  have hcfa : cf ≠ a := by
    rintro rfl
    have := hinj ht₂ h01 (ha1.symm.trans (by rw [hflipcf]; exact hvct))
    linarith
  have hctcf : ct ≠ cf := by
    intro h
    have := congrArg (fun d : DrawingDart (cylinderSphereDrawing H) => d.1.2) h
    simp [ct, cf] at this
  -- the sets where the side does not change
  obtain ⟨N₁, hN₁, hxN₁, hdich⟩ := sphere_sideDich_cuffs L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ 1
  rw [← hxc] at hxN₁
  obtain ⟨Nc, hNc, hxNc, hNcd⟩ := side_dichotomy L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ 1
  obtain ⟨Vc, hVc, hVcNc⟩ := isClosedEmbedding_cylinderToSphere.isInducing.isOpen_iff.mp hNc
  have hxVc : spherePath L 1 ∈ Vc := by
    rw [hxc]
    change L.curve 0 1 ∈ cylinderToSphere ⁻¹' Vc
    rw [hVcNc]
    exact hxNc
  have honetwo : ∀ r : ClosedCylinder, cylinderToSphere r ∈ Vc → r ∉ (L.pathDrawing 0).U →
      OnSide D U₁ r ∨ OnSide D U₂ r := by
    intro r hr hrP
    have hrN : r ∈ Nc := by rw [← hVcNc]; exact hr
    rcases hNcd {r} (singleton_subset_iff.mpr hrN) isPreconnected_singleton
      (disjoint_singleton_left.mpr hrP) with h | h
    exacts [Or.inl (h r rfl), Or.inr (h r rfl)]
  -- a closed set to stay away from: the inner cuff and the first half of `P₁`
  set K := cylinderToSphere '' cylinderCuff1 ∪ spherePath L '' Icc 0 (1 / 2)
  have hK : IsClosed K :=
    (isClosedEmbedding_cylinderToSphere.isClosedMap _
      (isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const)).union
      (isCompact_Icc.image hf).isClosed
  have hxK : spherePath L 1 ∉ K := by
    rintro (⟨r, hr, hre⟩ | ⟨s, hs, hse⟩)
    · rw [hxM] at hre
      have h2 := congrArg (fun q : ClosedCylinder => q.1.1) (injective_cylinderToSphere hre)
      have h1 : r.1.1 = 1 := hr
      simp [cylinderM2Point, cylinderPoint, h1] at h2
    · have := hinj ⟨hs.1, by linarith [hs.2]⟩ h01 hse
      linarith [hs.2]
  -- a small star at the end
  obtain ⟨Φ₀, z, hst₀⟩ := hccw (spherePath L 1) ⟨a, ha⟩
  obtain ⟨Φ, hst, hsub⟩ := hst₀.exists_small hS ((hN₁.inter hVc).inter hK.isOpen_compl)
    ⟨⟨hxN₁, hxVc⟩, hxK⟩
  obtain ⟨Ψ, hΨ, hw⟩ := hst.pos
  have hpos : 0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) := by
    rw [wind_chartC]; exact hw
  have hfin := hst.rimDirs_finite hγ
  have hp := hst.polar
  have hsubN : range Φ ⊆ N₁ := fun y hy => (hsub hy).1.1
  have hsubV : range Φ ⊆ Vc := fun y hy => (hsub hy).1.2
  have hsubK : range Φ ⊆ Kᶜ := fun y hy => (hsub hy).2
  -- the path near its end in the chart
  have hloc : range Φ ∩ X ⊆ spherePath L '' Icc (1 / 2) 1 := by
    rintro y ⟨hyΦ, hyX⟩
    have hyX' : y ∈ spherePath L '' Icc 0 1 := by rw [image_spherePath L]; exact hyX
    obtain ⟨s, hs, rfl⟩ := hyX'
    refine ⟨s, ⟨?_, hs.2⟩, rfl⟩
    by_contra hlt
    exact hsubK hyΦ (Or.inr ⟨s, ⟨hs.1, (not_le.mp hlt).le⟩, rfl⟩)
  obtain ⟨B, hBX, ⟨δ, hrunB⟩, hBu⟩ := exists_path_dirs_end hp hΨ hX hf (a := 1 / 2)
    (by norm_num) (hinj.mono (Icc_subset_Icc (by norm_num) le_rfl))
    ((image_mono (Icc_subset_Icc (by norm_num) le_rfl)).trans (image_spherePath L).subset) hloc
  have hza : z a = B := hBu _ (haX (hst.rim_mem_edge hγ hΨ ha))
  -- the barrier `Z` and its directions
  have hbdH : bd ClosedCylinder ⊆ H.U := by rw [hFU]; exact subset_union_right
  have hZ : IsGammaNice (cylinderSphereDrawing H) Z := by
    have h := isGammaNice_capped_linkage_and_cuffs L hGH hbdH
    have he : (⋃ j : Fin 1, (L.pathDrawing j).U) = (L.pathDrawing 0).U := by
      ext y; simp [Fin.exists_fin_one]
    rwa [he] at h
  have hZU : Z ⊆ (cylinderSphereDrawing H).U := by
    rw [cylinderSphereDrawing_U]
    exact image_mono (union_subset ((L.isSubdrawing 0).2.trans hGH.U_subset) hbdH)
  have heOZ : eO ⊆ Z := by
    rintro _ ⟨_, ⟨u, -, rfl⟩, rfl⟩
    refine ⟨_, Or.inr ?_, rfl⟩
    rw [bd_closedCylinder]
    right
    change (3 : ℝ) - 1 = 2
    norm_num
  have hdirsZ : ∀ w, polarRimMap Φ w ∈ Z → w = z a ∨ w = z ct ∨ w = z cf := by
    rintro w ⟨r, hr, hry⟩
    have hyΦ : polarRimMap Φ w ∈ range Φ := mem_range_self _
    rcases hr with hrP | hrb
    · left
      rw [hza]
      exact hBu w ⟨r, hrP, hry⟩
    · rw [bd_closedCylinder] at hrb
      rcases hrb with hr1 | hr2
      · exact absurd (Or.inl ⟨r, hr1, hry⟩) (hsubK hyΦ)
      · have hrM : r ≠ cylinderM2Point 1 0 := by
          rintro rfl
          apply IsCcwStar.rim_notMem_V hp w
          rw [← hry, ← hxM, ← ha]
          exact dartVertex_mem hγ a
        have hye : polarRimMap Φ w ∈ eO := hry ▸ mem_image_of_mem _ (cuff2_mem_outerGap hr2 hrM)
        obtain ⟨d, hd, hzd⟩ := hst.dirs w eO (heO 0) hye
        have hde : d.1.1 = eO :=
          (cylinderSphereDrawing H).edge_eq_of_mem d.2 (heO 0) (hzd ▸ hst.rim_mem_edge hγ hΨ hd) hye
        right
        rcases d with ⟨⟨e, bb⟩, he⟩
        simp only at hde
        subst hde
        cases bb
        · right; exact hzd.symm
        · left; exact hzd.symm
  subst hza
  -- the three directions of the barrier and their order
  have hFD := hst.mem_rimDirs hγ hvcf
  have hBD := hst.mem_rimDirs hγ ha
  have hCD := hst.mem_rimDirs hγ hvct
  have hFB : z cf ≠ z a := fun h => hcfa (hst.inj _ _ hvcf ha h)
  have hCB : z ct ≠ z a := fun h => hact (hst.inj _ _ ha hvct h.symm)
  have hFC : z cf ≠ z ct := fun h => hctcf (hst.inj _ _ hvct hvcf h.symm)
  have hnext : z ct * Circle.exp (gap (rimDirs (cylinderSphereDrawing H) Φ) (z ct)) = z cf := by
    rw [← hrot]; exact hst.next_eq hγ hR hvct
  have hgC := gap_pos hfin (z ct)
  have hBF : angleTo (z a) (z cf) = angleTo (z a) (z ct) + gap (rimDirs (cylinderSphereDrawing H) Φ) (z ct) := by
    have h := angleTo_step hCB hgC (gap_le_angleTo hfin _ hBD) (by rw [hnext]; exact hFB)
    rwa [hnext] at h
  have hlast : angleTo (z cf) (z a) ≤ angleTo (z cf) (z ct) := by
    have h := angleTo_le_of_next hfin hBD (by rw [hnext]; exact hFB.symm) (by rw [hnext]; exact hFC)
    rwa [hnext] at h
  -- the two wedges miss the barrier
  set W1 := wedgeSet Ψ (z cf) (angleTo (z cf) (z a))
  set W2 := wedgeSet Ψ (z a) (angleTo (z a) (z ct))
  have hW1Z : Disjoint W1 Z := by
    apply disjoint_wedgeSet hp hΨ hZ
    intro θ' hθ' hmem
    have hθ2 : θ' ∈ Ioc 0 (2 * Real.pi) := ⟨hθ'.1, hθ'.2.le.trans (angleTo_le _ _)⟩
    rcases hdirsZ _ hmem with h | h | h
    · have := angleTo_eq hθ2 h.symm
      linarith [hθ'.2]
    · have := angleTo_eq hθ2 h.symm
      linarith [hθ'.2]
    · have := angleTo_eq hθ2 h.symm
      rw [angleTo_self] at this
      linarith [hθ'.2, angleTo_le (z cf) (z a)]
  have hW2Z : Disjoint W2 Z := by
    apply disjoint_wedgeSet hp hΨ hZ
    intro θ' hθ' hmem
    have hθ2 : θ' ∈ Ioc 0 (2 * Real.pi) := ⟨hθ'.1, hθ'.2.le.trans (angleTo_le _ _)⟩
    rcases hdirsZ _ hmem with h | h | h
    · have := angleTo_eq hθ2 h.symm
      rw [angleTo_self] at this
      linarith [hθ'.2, angleTo_le (z a) (z ct)]
    · have := angleTo_eq hθ2 h.symm
      linarith [hθ'.2]
    · have := angleTo_eq hθ2 h.symm
      linarith [hθ'.2]
  have hdW1 := hdich W1 ((wedgeSet_subset_range hΨ _ _).trans hsubN) (isPreconnected_wedgeSet _ _)
    hW1Z
  have hdW2 := hdich W2 ((wedgeSet_subset_range hΨ _ _).trans hsubN) (isPreconnected_wedgeSet _ _)
    hW2Z
  -- the first wedge is on side one, by the corner just before `a`
  have hva : dartVertex γ (R.rot.symm a) = spherePath L 1 := by
    rw [← ha, ← hR.vertex_rot (R.rot.symm a), Equiv.apply_symm_apply]
  have hprev := hst.prev_eq hγ hR ha
  have hleftA : z (R.rot.symm a) = z cf ∨
      angleTo (z cf) (z (R.rot.symm a)) < angleTo (z cf) (z a) := by
    by_cases h : z (R.rot.symm a) = z cf
    · exact Or.inl h
    · right
      have h2 := angleTo_step h (gap_pos hfin _) (gap_le_angleTo hfin _ hFD)
        (by rw [hprev]; exact hFB.symm)
      rw [hprev] at h2
      linarith [gap_pos hfin (z (R.rot.symm a))]
  have hCa := cornerSet_subset_wedgeSet_of_left (Ψ := Ψ) hfin hBD hleftA
  have hQa := (left_side_one L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI hγI
    hV).2 hp hΨ hpos hfin hBD hprev hrunB
    (hdich _ ((cornerSet_subset_range hΨ _).trans hsubN) (isPreconnected_cornerSet _)
      ((disjoint_cornerSet hp hΨ hfin _).mono_right hZU))
  have hW1one : ∀ y ∈ W1, sphereSide D U₁ y := by
    rcases hdW1 with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy⟩ := cornerSet_nonempty (Γ := cylinderSphereDrawing H) (Φ := Φ) (Ψ := Ψ) hfin
        (z (R.rot.symm a))
      exact h y (hCa hy) (hQa y hy)
  -- the corner after `c⁻` lies outside the cylinder
  have hcap : ∀ y ∈ cornerSet (cylinderSphereDrawing H) Φ Ψ (z ct), y ∉ toSph '' ball (0 : ℂ) 1 := by
    obtain ⟨ρ₀, hρ₀, hform₀⟩ := exists_cornerLabel hinf hγ hR hccw
    have hcl := outer_reverse_corner_subset_closed_cap (k := 1) (i := 0) hG hFU hγ hρ₀ hform₀
      (heO 0) (hγO 0)
    have hρct := cornerLabel_eq_star hinf hγ hform₀ ct (by rw [hvct]; exact hst)
    intro y hy
    exact hcl (subset_closure (hρct ▸ image_cone_subset_cornerRegion hp hΨ hfin _ hy))
  -- each direction off the barrier lies in one of the three parts
  have htri : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ u : Circle, u ≠ z cf → u ≠ z a → u ≠ z ct →
      toSph (chartC Ψ ((r : ℂ) * u)) ∈ W1 ∨ toSph (chartC Ψ ((r : ℂ) * u)) ∈ W2 ∨
        toSph (chartC Ψ ((r : ℂ) * u)) ∈ cornerSet (cylinderSphereDrawing H) Φ Ψ (z ct) := by
    intro r hr hr1 u huF huB huC
    by_cases h1 : angleTo (z cf) u < angleTo (z cf) (z a)
    · exact Or.inl (mem_wedgeSet_of_lt hr hr1 h1)
    have h1' : angleTo (z cf) (z a) < angleTo (z cf) u := lt_of_le_of_ne (not_lt.mp h1)
      fun h => huB (by rw [← mul_exp_angleTo (z cf) u, ← h, mul_exp_angleTo])
    have hs1 := angleTo_sub h1'
    by_cases h2 : angleTo (z a) u < angleTo (z a) (z ct)
    · exact Or.inr (Or.inl (mem_wedgeSet_of_lt hr hr1 h2))
    have h2' : angleTo (z a) (z ct) < angleTo (z a) u := lt_of_le_of_ne (not_lt.mp h2)
      fun h => huC (by rw [← mul_exp_angleTo (z a) u, ← h, mul_exp_angleTo])
    have hs2 := angleTo_sub h2'
    have hsw := angleTo_swap hFB
    have hFu : angleTo (z cf) u < 2 * Real.pi := lt_of_le_of_ne (angleTo_le _ _)
      fun h => huF (by rw [← mul_exp_angleTo (z cf) u, h, Circle.exp_two_pi, mul_one])
    have h3 : angleTo (z ct) u < gap (rimDirs (cylinderSphereDrawing H) Φ) (z ct) := by linarith
    exact Or.inr (Or.inr (mem_wedgeSet_of_lt hr hr1 h3))
  -- the darts outside the first block, other than `c⁻`, are in the second block
  have hright2 : ∀ d, dartVertex γ d = spherePath L 1 →
      ¬ (z d = z cf ∨ angleTo (z cf) (z d) < angleTo (z cf) (z a)) → z d ≠ z ct →
      z d = z a ∨ angleTo (z a) (z d) < angleTo (z a) (z ct) := by
    intro d hd hl hdC
    rcases right_of_not_left hFB hl with h | h
    · exact Or.inl h
    · right
      by_contra hge
      have hlt : angleTo (z a) (z ct) < angleTo (z a) (z d) := lt_of_le_of_ne (not_lt.mp hge)
        fun h' => hdC (by rw [← mul_exp_angleTo (z a) (z d), ← h', mul_exp_angleTo])
      have hs := angleTo_sub hlt
      have hg := gap_le_angleTo hfin (z ct) (hst.mem_rimDirs hγ hd)
      linarith
  have hWo : ∀ U : Set CylinderCover, IsOpen U → IsOpen (U ∩
      (fun q => cylinderToSphere (cylinderCoverProjection q)) ⁻¹' interior (range Φ)) :=
    fun U hU' => hU'.inter (isOpen_interior.preimage
      (continuous_cylinderToSphere.comp continuous_cylinderCoverProjection))
  have hΓW : ∀ m : ℤ, ∀ U : Set CylinderCover, coverLift L hG m 1 ∈ U → coverLift L hG m 1 ∈ U ∩
      (fun q => cylinderToSphere (cylinderCoverProjection q)) ⁻¹' interior (range Φ) := by
    intro m U hmU
    refine ⟨hmU, ?_⟩
    simp only [mem_preimage]
    rw [proj_coverLift, ← hxc]
    exact hp.nhd
  have hopen : ∀ M : Set ClosedCylinder, IsOpen M → L.curve 0 1 ∈ M →
      ∃ V : Set (OnePoint EuclideanPlane), IsOpen V ∧ spherePath L 1 ∈ V ∧
        cylinderToSphere ⁻¹' V = M := by
    intro M hM hxM'
    obtain ⟨V, hV', hVM⟩ := isClosedEmbedding_cylinderToSphere.isInducing.isOpen_iff.mp hM
    refine ⟨V, hV', ?_, hVM⟩
    rw [hxc]
    change L.curve 0 1 ∈ cylinderToSphere ⁻¹' V
    rw [hVM]; exact hxM'
  have hrimZ : ∀ d, dartVertex γ d = spherePath L 1 → d.1.1 ⊆ Z →
      polarRimMap Φ (z d) ∈ Z := fun d hd hdZ => hdZ (hst.rim_mem_edge hγ hΨ hd)
  have hFZ := hrimZ cf hvcf heOZ
  have hCZ := hrimZ ct hvct heOZ
  have hBZ := hrimZ a ha (haX.trans (image_mono subset_union_left))
  -- the second wedge is off side one, by a point on side two near `Γ₂(1)`
  have hW2not : ∀ y ∈ W2, ¬ sphereSide D U₁ y := by
    rcases hdW2 with h | h
    swap
    · exact h
    exfalso
    obtain ⟨p, hpD, hpW, hpb, hpP⟩ := exists_inner_point_near_lift L hG hθ hD hBd hstrip
      (Or.inr rfl) 1 (hWo U₂ hU₂) (hΓW 2 U₂ (h₂ 1))
    have hr2 : OnSide D U₂ (radialCylinderProjection p) :=
      ⟨planeToCylinderCover p, ⟨p, hpD, rfl⟩, rfl, hpW.1⟩
    have hyΦ : cylinderToSphere (radialCylinderProjection p) ∈ range Φ := interior_subset hpW.2
    have hyZ : cylinderToSphere (radialCylinderProjection p) ∉ Z := by
      rintro ⟨r', hr', he⟩
      rw [injective_cylinderToSphere he] at hr'
      rcases hr' with h' | h'
      exacts [hpP h', hpb h']
    have hyx : cylinderToSphere (radialCylinderProjection p) ≠ spherePath L 1 := by
      intro h'
      rw [hxM] at h'
      exact hpb (injective_cylinderToSphere h' ▸ by
        rw [bd_closedCylinder]; right; simp [cylinderM2Point, cylinderPoint, cylinderCuff2])
    obtain ⟨t', ht', ht1', u, hu⟩ := exists_chart_polar hp hΨ hyΦ hyx
    have hne : ∀ w, polarRimMap Φ w ∈ Z → u ≠ w := by
      rintro w hwZ rfl
      exact hyZ (by rw [hu]; exact (chart_ray_mem_iff hp hΨ hZ u ht' ht1').mpr hwZ)
    have hside1 : ∀ y, y = cylinderToSphere (radialCylinderProjection p) →
        ¬ sphereSide D U₁ y := by
      rintro y rfl ⟨r', he, hr'1⟩
      rw [injective_cylinderToSphere he] at hr'1
      exact not_onSide_two_of_onSide_one L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hpP hr'1 hr2
    rcases htri t' ht' ht1' u (hne _ hFZ) (hne _ hBZ) (hne _ hCZ) with h' | h' | h'
    · exact hside1 _ rfl (hu ▸ hW1one _ h')
    · exact hside1 _ rfl (hu ▸ h _ h')
    · exact hcap _ h' (hu ▸ cylinderToSphere_mem_ball hpb)

  -- the rays of the darts along edges off `P₁`
  have hx1' : spherePath L 1 = cylinderToSphere (L.curve 0 1) := hxc
  refine ⟨Φ, Ψ, z, hx1' ▸ hst, hΨ, fun d hd f hf hfP hdf r hr hr1 => ?_⟩
  rw [← hx1'] at hd
  have hfZ : ∀ c : DrawingDart (cylinderSphereDrawing H), c.1.1 ⊆ Z → d ≠ c := by
    rintro c hcZ rfl
    obtain ⟨y, hy⟩ := hf.2.2.1.nonempty
    have hdisj := deleted_edge_disjoint_subdrawing (L.isSubdrawing 0).1 hf hfP
    obtain ⟨y', hy', he⟩ := hcZ (hdf ▸ mem_image_of_mem cylinderToSphere hy)
    rw [injective_cylinderToSphere he] at hy'
    rcases hy' with hyP | hyb
    · exact disjoint_left.mp hdisj hy hyP
    · exact (hf.2.1 hy).2 (hG.2.1 ⟨hyb, (hf.2.1 hy).1⟩)
  have hdF : z d ≠ z cf := fun h => hfZ cf heOZ (hst.inj _ _ hd hvcf h)
  have hdC : z d ≠ z ct := fun h => hfZ ct heOZ (hst.inj _ _ hd hvct h)
  have hdB : z d ≠ z a := fun h =>
    hfZ a (haX.trans (image_mono subset_union_left)) (hst.inj _ _ hd ha h)
  have hiff := hst.arc_iff_block hγ hR ha hvcf hd hcfa
  constructor
  · intro hs
    rcases hiff.mpr hs with h | h
    · exact absurd h hdF
    · exact hW1one _ (mem_wedgeSet_of_lt hr hr1 h)
  · intro hs
    rcases hright2 d hd (fun h => hs (hiff.mp h)) hdC with h | h
    · exact absurd h hdB
    · exact hW2not _ (mem_wedgeSet_of_lt hr hr1 h)

end GraphMinor.GM06
