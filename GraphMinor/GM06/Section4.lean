module

public import GraphMinor.GM06.Section3Main
public import GraphMinor.Surface.Jordan
import GraphMinor.Surface.Crossing
import GraphMinor.Surface.Cylinder
import GraphMinor.Surface.InvarianceOfDomain
import Mathlib.Data.Set.Card

/-!
# Graph Minors VI, Section 4: Cuff Arcs on the Cylinder and Proof of (4.3)

This file proves the topological structure of the boundary cuffs of `ClosedCylinder`, establishes
the cuff crossing theorem on `ClosedCylinder` by embedding `ClosedCylinder` as an annulus into
`ClosedUnitDisc`, characterizes `cuffSubArc` via angular coordinates on `Circle`, and proves
`GM06.theorem_4_3 : Statement43` of Robertson and Seymour, *Graph Minors. VI. Disjoint paths
across a disc*, J. Combin. Theory Ser. B **41** (1986), 115–138 (page 125) with zero unproved
hypotheses.
-/

public section

namespace GraphMinor.GM06

open Set Function Complex Real Topology Metric Graph GraphMinor.Surface

/-! ## 1. Boundary and Cuffs of `ClosedCylinder` -/

/-- The radial map embedding `ClosedCylinder` into `EuclideanPlane` as the closed annulus
$\{v \in \mathbb{R}^2 : 1/2 \le \|v\| \le 1\}$, sending `cylinderCuff2` to `UnitCircle`. -/
noncomputable def cylToPlane (p : ClosedCylinder) : EuclideanPlane :=
  (p.1.1 / 2) • complexPlane (p.1.2 : ℂ)

theorem cylToPlane_apply (p : ClosedCylinder) :
    cylToPlane p = (p.1.1 / 2) • complexPlane (p.1.2 : ℂ) := by
  rw [cylToPlane]

theorem continuous_cylToPlane : Continuous cylToPlane := by
  unfold cylToPlane
  fun_prop

theorem norm_cylToPlane (p : ClosedCylinder) :
    ‖cylToPlane p‖ = p.1.1 / 2 := by
  have hr : 0 ≤ p.1.1 := by linarith [p.2.1.1]
  simp [cylToPlane, norm_smul, abs_of_nonneg hr]

theorem injective_cylToPlane : Injective cylToPlane := by
  intro p q hpq
  have hnorm : ‖cylToPlane p‖ = ‖cylToPlane q‖ := congrArg norm hpq
  rw [norm_cylToPlane, norm_cylToPlane] at hnorm
  have hr_eq : p.1.1 = q.1.1 := by linarith
  have hpos : p.1.1 / 2 ≠ 0 := by
    have := p.2.1.1
    linarith
  have hsmul : (p.1.1 / 2) • complexPlane (p.1.2 : ℂ) =
      (p.1.1 / 2) • complexPlane (q.1.2 : ℂ) := by
    simpa [cylToPlane, hr_eq] using hpq
  have hcp := smul_right_injective EuclideanPlane hpos hsmul
  have hcircle : p.1.2 = q.1.2 := Subtype.ext (complexPlane.injective hcp)
  exact Subtype.ext (Prod.ext hr_eq hcircle)

instance compactSpace_closedCylinder : CompactSpace ClosedCylinder :=
  isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_univ)

theorem isClosedEmbedding_cylToPlane : IsClosedEmbedding cylToPlane :=
  continuous_cylToPlane.isClosedEmbedding injective_cylToPlane

theorem range_cylToPlane :
    range cylToPlane = {v : EuclideanPlane | 1 / 2 ≤ ‖v‖ ∧ ‖v‖ ≤ 1} := by
  ext v
  simp only [mem_range, mem_ofPred_eq]
  constructor
  · rintro ⟨p, rfl⟩
    rw [norm_cylToPlane]
    have h1 := p.2.1.1
    have h2 := p.2.1.2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have hv_pos : 0 < ‖v‖ := by linarith
    have hv_ne : ‖v‖ ≠ 0 := ne_of_gt hv_pos
    let r : ℝ := 2 * ‖v‖
    have hr : r ∈ Icc (1 : ℝ) 2 := ⟨by dsimp [r]; linarith, by dsimp [r]; linarith⟩
    let z : ℂ := complexPlane.symm v / (‖v‖ : ℂ)
    have hz_norm : ‖z‖ = 1 := by
      simp [z, div_self hv_ne]
    let u : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz_norm⟩
    refine ⟨⟨(r, u), hr, trivial⟩, ?_⟩
    dsimp [cylToPlane, r, u, z]
    have hmul : (2 * ‖v‖ / 2 : ℝ) = ‖v‖ := by ring
    rw [hmul]
    apply complexPlane.symm.injective
    rw [map_smul, LinearIsometryEquiv.symm_apply_apply, Complex.real_smul]
    exact mul_div_cancel₀ _ ( Complex.ofReal_ne_zero.mpr hv_ne )

/-- Every point $p \in \text{ClosedCylinder}$ with $1 < p.1.1 < 2$ is an interior point of
`ClosedCylinder`. -/
private theorem isInteriorPoint_of_r_mem_Ioo {p : ClosedCylinder}
    (hp1 : 1 < p.1.1) (hp2 : p.1.1 < 2) :
    IsInteriorPoint p := by
  let e := isClosedEmbedding_cylToPlane.toIsEmbedding.toHomeomorph
  rw [← isInteriorPoint_homeomorph_iff e p]
  let y₀ : EuclideanPlane := cylToPlane p
  have hy₀_norm : ‖y₀‖ = p.1.1 / 2 := norm_cylToPlane p
  let δ : ℝ := min (‖y₀‖ - 1 / 2) (1 - ‖y₀‖)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    rw [lt_min_iff, hy₀_norm]
    constructor <;> linarith
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  have hball_sub : Metric.ball y₀ δ ⊆ range cylToPlane := by
    intro w hw
    rw [range_cylToPlane]
    have hdist : ‖w - y₀‖ < δ := by simpa [dist_eq_norm] using hw
    have hlt1 : ‖w - y₀‖ < ‖y₀‖ - 1 / 2 := lt_of_lt_of_le hdist (min_le_left _ _)
    have hlt2 : ‖w - y₀‖ < 1 - ‖y₀‖ := lt_of_lt_of_le hdist (min_le_right _ _)
    have htri1 : ‖y₀‖ - ‖w - y₀‖ ≤ ‖w‖ := by
      have := norm_sub_norm_le y₀ (y₀ - w)
      simpa [norm_sub_rev] using this
    have htri2 : ‖w‖ ≤ ‖y₀‖ + ‖w - y₀‖ := by
      have := norm_add_le y₀ (w - y₀)
      simpa using this
    constructor <;> linarith
  let U : Set (range cylToPlane) := Subtype.val ⁻¹' Metric.ball y₀ δ
  have hU_open : IsOpen U := isOpen_ball.preimage continuous_subtype_val
  have hep_mem : e p ∈ U := by
    change cylToPlane p ∈ Metric.ball y₀ δ
    exact mem_ball_self hδ_pos
  have hto : ∀ u : U, δ⁻¹ • (u.1.1 - y₀) ∈ OpenUnitDisc := by
    intro u
    rw [OpenUnitDisc, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hδ_pos)]
    have hu : ‖u.1.1 - y₀‖ < δ := dist_eq_norm u.1.1 y₀ ▸ mem_ball.mp u.2
    exact (inv_mul_lt_iff₀ hδ_pos).mpr (by linarith)
  have hinv : ∀ z : OpenUnitDisc, y₀ + δ • z.1 ∈ Metric.ball y₀ δ := by
    intro z
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hδ_pos]
    have hz : ‖z.1‖ < 1 := mem_ball_zero_iff.mp z.2
    nlinarith
  refine ⟨U, hU_open, hep_mem, ⟨?_⟩⟩
  refine
    { toFun := fun u => ⟨δ⁻¹ • (u.1.1 - y₀), hto u⟩
      invFun := fun z => ⟨⟨y₀ + δ • z.1, hball_sub (hinv z)⟩, hinv z⟩
      left_inv := fun u => by
        ext1; ext1
        simp [smul_smul, mul_inv_cancel₀ hδ_ne]
      right_inv := fun z => by
        ext1
        simp [smul_smul, inv_mul_cancel₀ hδ_ne]
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ hto
        fun_prop
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ (fun z => hball_sub (hinv z))) hinv
        fun_prop }

/-- No point on `cylinderCuff1` or `cylinderCuff2` is an interior point of `ClosedCylinder`.
Route: invariance of domain (`isOpen_image_of_injOn`) applied to `complexPlane.symm ∘ cylToPlane`. -/
private theorem not_isInteriorPoint_of_cuff {p : ClosedCylinder}
    (hp : p.1.1 = 1 ∨ p.1.1 = 2) :
    ¬ IsInteriorPoint p := by
  intro ⟨U, hU, hpU, ⟨f⟩⟩
  have hmem : ∀ z : ℂ, ‖z‖ < 1 → complexPlane z ∈ OpenUnitDisc := fun z hz => by
    refine mem_ball_zero_iff.mpr ?_
    rwa [LinearIsometryEquiv.norm_map]
  let ψ : ClosedCylinder → ℂ := fun q => complexPlane.symm (cylToPlane q)
  have hψ_cont : Continuous ψ := complexPlane.symm.continuous.comp continuous_cylToPlane
  have hψ_inj : Injective ψ := complexPlane.symm.injective.comp injective_cylToPlane
  have hψ_norm : ∀ q : ClosedCylinder, ‖ψ q‖ = q.1.1 / 2 := fun q => by
    simp [ψ, norm_cylToPlane]
  let g : ℂ → ℂ := fun z =>
    if h : ‖z‖ < 1 then ψ (f.symm ⟨complexPlane z, hmem z h⟩).1 else 0
  have hgb : ∀ z (h : z ∈ ball (0 : ℂ) 1), g z =
      ψ (f.symm ⟨complexPlane z, hmem z (by simpa using h)⟩).1 := by
    intro z h
    have h' : ‖z‖ < 1 := by simpa using h
    simp only [g, h', dite_true]
  have hgc : ContinuousOn g (ball (0 : ℂ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (ball (0 : ℂ) 1).domRestrict g = fun z : ball (0 : ℂ) 1 =>
        ψ (f.symm ⟨complexPlane z.1, hmem z.1 (mem_ball_zero_iff.mp z.2)⟩).1 := by
      ext z
      exact hgb z.1 z.2
    rw [this]
    have h2 : Continuous fun z : ball (0 : ℂ) 1 =>
        (⟨complexPlane z.1, hmem z.1 (mem_ball_zero_iff.mp z.2)⟩ : OpenUnitDisc) := by
      refine Continuous.subtype_mk ?_ _
      exact complexPlane.continuous.comp continuous_subtype_val
    exact hψ_cont.comp (continuous_subtype_val.comp (f.symm.continuous.comp h2))
  have hgi : InjOn g (ball (0 : ℂ) 1) := by
    intro a ha b hb hab
    rw [hgb a ha, hgb b hb] at hab
    have h1 := hψ_inj hab
    have h2 := f.symm.injective (Subtype.ext h1)
    exact complexPlane.injective (congrArg Subtype.val h2)
  have hopen := isOpen_image_of_injOn isOpen_ball hgc hgi
  have hy : ψ p ∈ g '' ball (0 : ℂ) 1 := by
    have hn : ‖complexPlane.symm (f ⟨p, hpU⟩).1‖ < 1 := by
      rw [LinearIsometryEquiv.norm_map]
      exact mem_ball_zero_iff.mp (f ⟨p, hpU⟩).2
    refine ⟨complexPlane.symm (f ⟨p, hpU⟩).1, by simpa using hn, ?_⟩
    rw [hgb _ (by simpa using hn)]
    simp
  have hbounds : ∀ w ∈ g '' ball (0 : ℂ) 1, 1 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 1 := by
    rintro _ ⟨z, hz, rfl⟩
    let q := (f.symm ⟨complexPlane z, hmem z (by simpa using hz)⟩).1
    rw [hgb z hz, hψ_norm q]
    have hq1 := q.2.1.1
    have hq2 := q.2.1.2
    constructor <;> linarith
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hy
  set y := ψ p with hydef
  rcases hp with hp1 | hp2
  · have hyn : ‖y‖ = 1 / 2 := by rw [hydef, hψ_norm, hp1]
    let δ : ℝ := min (ε / 2) (1 / 4)
    have hδ_pos : 0 < δ := lt_min (by positivity) (by norm_num)
    have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    have hδ_le : δ ≤ 1 / 4 := min_le_right _ _
    have h1 : ((1 - δ : ℝ) : ℂ) * y ∈ ball y ε := by
      have hsub : ((1 - δ : ℝ) : ℂ) * y - y = -((δ : ℂ) * y) := by push_cast; ring
      rw [mem_ball, dist_eq_norm, hsub, norm_neg, norm_mul, hyn, norm_real, Real.norm_eq_abs,
        abs_of_pos hδ_pos]
      linarith
    have h2 := (hbounds _ (hball h1)).1
    rw [norm_mul, hyn, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h2
    linarith
  · have hyn : ‖y‖ = 1 := by rw [hydef, hψ_norm, hp2]; norm_num
    have h1 : ((1 + ε / 2 : ℝ) : ℂ) * y ∈ ball y ε := by
      have hsub : ((1 + ε / 2 : ℝ) : ℂ) * y - y = ((ε / 2 : ℝ) : ℂ) * y := by push_cast; ring
      rw [mem_ball, dist_eq_norm, hsub, norm_mul, hyn, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have h2 := (hbounds _ (hball h1)).2
    rw [norm_mul, hyn, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h2
    linarith

/-- The manifold boundary of `ClosedCylinder` is `cylinderCuff1 ∪ cylinderCuff2`. -/
theorem bd_closedCylinder : bd ClosedCylinder = cylinderCuff1 ∪ cylinderCuff2 := by
  ext p
  simp only [bd, mem_ofPred_eq, mem_union, cylinderCuff1, cylinderCuff2]
  constructor
  · intro hp
    by_contra! hnot
    rcases hnot with ⟨hne1, hne2⟩
    have h1 : 1 < p.1.1 := lt_of_le_of_ne p.2.1.1 (Ne.symm hne1)
    have h2 : p.1.1 < 2 := lt_of_le_of_ne p.2.1.2 hne2
    exact hp (isInteriorPoint_of_r_mem_Ioo h1 h2)
  · intro hp
    exact not_isInteriorPoint_of_cuff hp

/-- The homeomorphism `Circle ≃ₜ cylinderCuff1`. -/
noncomputable def circleHomeomorphCylinderCuff1 : Circle ≃ₜ cylinderCuff1 where
  toFun u := ⟨⟨(1, u), ⟨le_refl 1, by norm_num⟩, trivial⟩, rfl⟩
  invFun p := p.1.1.2
  left_inv _ := rfl
  right_inv p := by
    ext1; ext1
    exact Prod.ext p.2.symm rfl
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_const.prodMk continuous_id
  continuous_invFun :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)

/-- The homeomorphism `Circle ≃ₜ cylinderCuff2`. -/
noncomputable def circleHomeomorphCylinderCuff2 : Circle ≃ₜ cylinderCuff2 where
  toFun u := ⟨⟨(2, u), ⟨by norm_num, le_refl 2⟩, trivial⟩, rfl⟩
  invFun p := p.1.1.2
  left_inv _ := rfl
  right_inv p := by
    ext1; ext1
    exact Prod.ext p.2.symm rfl
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_const.prodMk continuous_id
  continuous_invFun :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem isOArc_cylinderCuff1 : IsOArc cylinderCuff1 :=
  ⟨circleHomeomorphCylinderCuff1⟩

theorem isOArc_cylinderCuff2 : IsOArc cylinderCuff2 :=
  ⟨circleHomeomorphCylinderCuff2⟩

private theorem isPreconnected_cylinderCuff1 : IsPreconnected cylinderCuff1 := by
  have : ConnectedSpace cylinderCuff1 :=
    circleHomeomorphCylinderCuff1.surjective.connectedSpace circleHomeomorphCylinderCuff1.continuous
  exact isConnected_iff_connectedSpace.mpr this |>.isPreconnected

private theorem isPreconnected_cylinderCuff2 : IsPreconnected cylinderCuff2 := by
  have : ConnectedSpace cylinderCuff2 :=
    circleHomeomorphCylinderCuff2.surjective.connectedSpace circleHomeomorphCylinderCuff2.continuous
  exact isConnected_iff_connectedSpace.mpr this |>.isPreconnected

private theorem isOpen_cylinderCuff1_or_2 :
    ∃ U₁ U₂ : Set ClosedCylinder,
      IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
      cylinderCuff1 ⊆ U₁ ∧ cylinderCuff2 ⊆ U₂ ∧
      cylinderCuff1 ∪ cylinderCuff2 ⊆ U₁ ∪ U₂ := by
  let rProj : ClosedCylinder → ℝ := fun p => p.1.1
  have hr_cont : Continuous rProj := continuous_fst.comp continuous_subtype_val
  refine ⟨rProj ⁻¹' Iio (3 / 2 : ℝ), rProj ⁻¹' Ioi (3 / 2 : ℝ),
    isOpen_Iio.preimage hr_cont, isOpen_Ioi.preimage hr_cont, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro p hp1 hp2
    change p.1.1 < 3 / 2 at hp1
    change 3 / 2 < p.1.1 at hp2
    linarith
  · intro p hp
    change p.1.1 = 1 at hp
    change p.1.1 < 3 / 2
    linarith
  · intro p hp
    change p.1.1 = 2 at hp
    change 3 / 2 < p.1.1
    linarith
  · rintro p (hp1 | hp2)
    · left; change p.1.1 = 1 at hp1; change p.1.1 < 3 / 2; linarith
    · right; change p.1.1 = 2 at hp2; change 3 / 2 < p.1.1; linarith

/-- The cuffs of `ClosedCylinder` are `cylinderCuff1` and `cylinderCuff2`. -/
theorem cuffs_closedCylinder :
    cuffs ClosedCylinder = {cylinderCuff1, cylinderCuff2} := by
  unfold cuffs componentsIn
  rw [bd_closedCylinder]
  obtain ⟨U₁, U₂, hU₁_open, hU₂_open, hU_disj, hsub1, hsub2, _⟩ := isOpen_cylinderCuff1_or_2
  have hcc1 : ∀ p ∈ cylinderCuff1,
      connectedComponentIn (cylinderCuff1 ∪ cylinderCuff2) p = cylinderCuff1 := by
    intro p hp
    apply Subset.antisymm
    · intro q hq
      have hq_mem : q ∈ cylinderCuff1 ∪ cylinderCuff2 :=
        connectedComponentIn_subset _ p hq
      rcases hq_mem with hq1 | hq2
      · exact hq1
      · exfalso
        have hconn : IsPreconnected (connectedComponentIn (cylinderCuff1 ∪ cylinderCuff2) p) :=
          isPreconnected_connectedComponentIn
        have hp_cc : p ∈ connectedComponentIn (cylinderCuff1 ∪ cylinderCuff2) p :=
          mem_connectedComponentIn (Or.inl hp)
        have hsubU : connectedComponentIn (cylinderCuff1 ∪ cylinderCuff2) p ⊆ U₁ ∪ U₂ := by
          intro z hz
          rcases connectedComponentIn_subset _ p hz with hz1 | hz2
          · exact Or.inl (hsub1 hz1)
          · exact Or.inr (hsub2 hz2)
        rcases hconn U₁ U₂ hU₁_open hU₂_open hsubU ⟨p, hp_cc, hsub1 hp⟩ ⟨q, hq, hsub2 hq2⟩ with
          ⟨w, _, hw1, hw2⟩
        exact hU_disj.ne_of_mem hw1 hw2 rfl
    · exact isPreconnected_cylinderCuff1.subset_connectedComponentIn hp subset_union_left
  have hcc2 : ∀ p ∈ cylinderCuff2,
      connectedComponentIn (cylinderCuff1 ∪ cylinderCuff2) p = cylinderCuff2 := by
    intro p hp
    apply Subset.antisymm
    · intro q hq
      have hq_mem : q ∈ cylinderCuff1 ∪ cylinderCuff2 :=
        connectedComponentIn_subset _ p hq
      rcases hq_mem with hq1 | hq2
      · exfalso
        have hconn : IsPreconnected (connectedComponentIn (cylinderCuff1 ∪ cylinderCuff2) p) :=
          isPreconnected_connectedComponentIn
        have hp_cc : p ∈ connectedComponentIn (cylinderCuff1 ∪ cylinderCuff2) p :=
          mem_connectedComponentIn (Or.inr hp)
        have hsubU : connectedComponentIn (cylinderCuff1 ∪ cylinderCuff2) p ⊆ U₁ ∪ U₂ := by
          intro z hz
          rcases connectedComponentIn_subset _ p hz with hz1 | hz2
          · exact Or.inl (hsub1 hz1)
          · exact Or.inr (hsub2 hz2)
        rcases hconn U₁ U₂ hU₁_open hU₂_open hsubU ⟨q, hq, hsub1 hq1⟩ ⟨p, hp_cc, hsub2 hp⟩ with
          ⟨w, _, hw1, hw2⟩
        exact hU_disj.ne_of_mem hw1 hw2 rfl
      · exact hq2
    · exact isPreconnected_cylinderCuff2.subset_connectedComponentIn hp subset_union_right
  ext C
  simp only [mem_image, mem_union, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨p, hp1 | hp2, rfl⟩
    · exact Or.inl (hcc1 p hp1)
    · exact Or.inr (hcc2 p hp2)
  · rintro (rfl | rfl)
    · let p₁ : ClosedCylinder := ⟨(1, 1), ⟨le_refl 1, by norm_num⟩, trivial⟩
      exact ⟨p₁, Or.inl rfl, hcc1 p₁ rfl⟩
    · let p₂ : ClosedCylinder := ⟨(2, 1), ⟨by norm_num, le_refl 2⟩, trivial⟩
      exact ⟨p₂, Or.inr rfl, hcc2 p₂ rfl⟩

/-! ## 2. Cuff Crossing on `ClosedCylinder` -/

/-- The radial embedding of `ClosedCylinder` into `ClosedUnitDisc` sending `cylinderCuff2` onto
`bd ClosedUnitDisc`. -/
noncomputable def cylToDisc2 (p : ClosedCylinder) : ClosedUnitDisc :=
  ⟨cylToPlane p, by
    rw [ClosedUnitDisc, mem_closedBall_zero_iff, norm_cylToPlane]
    have := p.2.1.2
    linarith⟩

theorem continuous_cylToDisc2 : Continuous cylToDisc2 :=
  continuous_cylToPlane.subtype_mk _

theorem injective_cylToDisc2 : Injective cylToDisc2 :=
  fun _ _ h => injective_cylToPlane (congrArg Subtype.val h)

theorem isClosedEmbedding_cylToDisc2 : IsClosedEmbedding cylToDisc2 :=
  continuous_cylToDisc2.isClosedEmbedding injective_cylToDisc2

theorem image_cylinderCuff2_cylToDisc2 :
    cylToDisc2 '' cylinderCuff2 = bd ClosedUnitDisc := by
  rw [bd_closedUnitDisc]
  ext x
  simp only [mem_image, cylinderCuff2, mem_ofPred_eq, UnitCircle, mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨p, hp, rfl⟩
    change ‖cylToPlane p‖ = 1
    rw [norm_cylToPlane, hp]
    norm_num
  · intro hx
    have hx_pos : (0 : ℝ) < 1 := zero_lt_one
    let z : ℂ := complexPlane.symm x.1
    have hz : ‖z‖ = 1 := by rw [LinearIsometryEquiv.norm_map, hx]
    let u : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
    let p : ClosedCylinder := ⟨(2, u), ⟨by norm_num, le_refl 2⟩, trivial⟩
    refine ⟨p, rfl, Subtype.ext ?_⟩
    dsimp [cylToDisc2, cylToPlane, p, u, z]
    have h2 : (2 / 2 : ℝ) = 1 := by norm_num
    rw [h2, one_smul, LinearIsometryEquiv.apply_symm_apply]

/-- The reflection involution `(r, u) ↦ (3 - r, u)` on `ClosedCylinder` swapping `cylinderCuff1`
and `cylinderCuff2`. -/
def swapCylinder : ClosedCylinder ≃ₜ ClosedCylinder where
  toFun p := ⟨(3 - p.1.1, p.1.2), ⟨by linarith [p.2.1.2], by linarith [p.2.1.1]⟩, trivial⟩
  invFun p := ⟨(3 - p.1.1, p.1.2), ⟨by linarith [p.2.1.2], by linarith [p.2.1.1]⟩, trivial⟩
  left_inv p := by
    ext1; ext1
    · change 3 - (3 - p.1.1) = p.1.1; ring
    · rfl
  right_inv p := by
    ext1; ext1
    · change 3 - (3 - p.1.1) = p.1.1; ring
    · rfl
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact continuous_const.sub (continuous_fst.comp continuous_subtype_val)
    · exact continuous_snd.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact continuous_const.sub (continuous_fst.comp continuous_subtype_val)
    · exact continuous_snd.comp continuous_subtype_val

theorem image_cylinderCuff1_swapCylinder :
    swapCylinder '' cylinderCuff1 = cylinderCuff2 := by
  ext p
  simp only [mem_image, cylinderCuff1, cylinderCuff2, mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩
    change 3 - q.1.1 = 2
    linarith
  · intro hp
    refine ⟨swapCylinder p, ?_, swapCylinder.right_inv p⟩
    change 3 - p.1.1 = 1
    linarith

/-- Transfer of `CrossesOn` along a topological embedding onto a set $C'$. -/
private theorem crossesOn_image_of_isEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) {C : Set X} {a c b d : X}
    (hcross : CrossesOn C a c b d) :
    CrossesOn (f '' C) (f a) (f c) (f b) (f d) := by
  have hinj := hf.injective
  rcases hcross with ⟨ha, hb, hc, hd, hac, hbd, hab, had, hcb, hcd, hcc⟩
  refine ⟨mem_image_of_mem f ha, mem_image_of_mem f hb, mem_image_of_mem f hc,
    mem_image_of_mem f hd, hinj.ne hac, hinj.ne hbd, hinj.ne hab, hinj.ne had,
    hinj.ne hcb, hinj.ne hcd, ?_⟩
  have hdiff : (f '' C) \ {f a, f c} = f '' (C \ {a, c}) := by
    have : ({f a, f c} : Set Y) = f '' {a, c} := by simp
    rw [this, ← image_sdiff hinj]
  have hb_mem : b ∈ C \ {a, c} := ⟨hb, by simp [hab.symm, hcb.symm]⟩
  have hd_mem : d ∈ C \ {a, c} := ⟨hd, by simp [had.symm, hcd.symm]⟩
  rw [hdiff, ← isEmbedding_image_connectedComponentIn hf hb_mem,
    ← isEmbedding_image_connectedComponentIn hf hd_mem, ne_eq, image_eq_image hinj]
  exact hcc

/-- Cuff crossing on `ClosedCylinder`: if $C \in \operatorname{cuffs}(\text{ClosedCylinder})$ and
$A, B \subseteq \text{ClosedCylinder}$ are compact connected sets whose endpoints $a, c \in A$ and
$b, d \in B$ cross on $C$, then $A \cap B \ne \emptyset$. -/
theorem cuffCrossing_closedCylinder {C A B : Set ClosedCylinder} {a c b d : ClosedCylinder}
    (hC : C ∈ cuffs ClosedCylinder)
    (hA_comp : IsCompact A) (hB_comp : IsCompact B)
    (hA_conn : IsConnected A) (hB_conn : IsConnected B)
    (ha : a ∈ A) (hc : c ∈ A) (hb : b ∈ B) (hd : d ∈ B)
    (hcross : CrossesOn C a c b d) :
    (A ∩ B).Nonempty := by
  have hDisc : IsClosedDiscSpace ClosedUnitDisc := ⟨Homeomorph.refl ClosedUnitDisc⟩
  have h_case2 : C = cylinderCuff2 → (A ∩ B).Nonempty := by
    rintro rfl
    have hemb := isClosedEmbedding_cylToDisc2.toIsEmbedding
    have hcross' := crossesOn_image_of_isEmbedding hemb hcross
    rw [image_cylinderCuff2_cylToDisc2] at hcross'
    have hmeet := disc_crossing (univ : Set ClosedUnitDisc) (cylToDisc2 '' A) (cylToDisc2 '' B)
      (cylToDisc2 a) (cylToDisc2 c) (cylToDisc2 b) (cylToDisc2 d)
      ⟨Homeomorph.Set.univ ClosedUnitDisc |>.symm⟩
      (subset_univ _) (subset_univ _)
      (hA_comp.image continuous_cylToDisc2) (hB_comp.image continuous_cylToDisc2)
      (hA_conn.image _ continuous_cylToDisc2.continuousOn)
      (hB_conn.image _ continuous_cylToDisc2.continuousOn)
      (mem_image_of_mem _ ha) (mem_image_of_mem _ hc)
      (mem_image_of_mem _ hb) (mem_image_of_mem _ hd)
      (by
        have hbd : discBd (univ : Set ClosedUnitDisc) = bd ClosedUnitDisc := by
          simpa [discBd, Homeomorph.Set.univ] using
            image_bd_homeomorph (Homeomorph.Set.univ ClosedUnitDisc)
        rw [hbd]; exact hcross')
    rcases hmeet with ⟨w, ⟨x, hxA, rfl⟩, ⟨y, hyB, hyx⟩⟩
    have hyx' : y = x := injective_cylToDisc2 hyx
    subst hyx'
    exact ⟨y, hxA, hyB⟩
  rw [cuffs_closedCylinder] at hC
  rcases hC with rfl | hC2
  · let f := cylToDisc2 ∘ swapCylinder
    have hf_emb : IsEmbedding f :=
      isClosedEmbedding_cylToDisc2.toIsEmbedding.comp swapCylinder.isEmbedding
    have hcross' := crossesOn_image_of_isEmbedding hf_emb hcross
    have himg : f '' cylinderCuff1 = bd ClosedUnitDisc := by
      rw [image_comp, image_cylinderCuff1_swapCylinder, image_cylinderCuff2_cylToDisc2]
    rw [himg] at hcross'
    have hmeet := disc_crossing (univ : Set ClosedUnitDisc) (f '' A) (f '' B)
      (f a) (f c) (f b) (f d)
      ⟨Homeomorph.Set.univ ClosedUnitDisc |>.symm⟩
      (subset_univ _) (subset_univ _)
      (hA_comp.image hf_emb.continuous) (hB_comp.image hf_emb.continuous)
      (hA_conn.image _ hf_emb.continuous.continuousOn)
      (hB_conn.image _ hf_emb.continuous.continuousOn)
      (mem_image_of_mem _ ha) (mem_image_of_mem _ hc)
      (mem_image_of_mem _ hb) (mem_image_of_mem _ hd)
      (by
        have hbd : discBd (univ : Set ClosedUnitDisc) = bd ClosedUnitDisc := by
          simpa [discBd, Homeomorph.Set.univ] using
            image_bd_homeomorph (Homeomorph.Set.univ ClosedUnitDisc)
        rw [hbd]; exact hcross')
    rcases hmeet with ⟨w, ⟨x, hxA, rfl⟩, ⟨y, hyB, hyx⟩⟩
    have hyx' : y = x := hf_emb.injective hyx
    subst hyx'
    exact ⟨y, hxA, hyB⟩
  · exact h_case2 (mem_singleton_iff.mp hC2)

/-! ## 3. Characterization of `cuffSubArc` on `Circle` and on Cuffs -/

/-- On `Circle`, the connected components of `univ \ {x, y}` for $x \ne y$ are `circleOpenArc x y`
and `circleOpenArc y x`. -/
theorem mem_componentsIn_univ_sdiff_pair_iff {x y : Circle} (hxy : x ≠ y)
    {K : Set Circle} :
    K ∈ componentsIn ((univ : Set Circle) \ {x, y}) ↔
      K = circleOpenArc x y ∨ K = circleOpenArc y x := by
  rw [← compl_eq_univ_sdiff]
  unfold componentsIn
  simp only [mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [compl_pair_eq_union_circleOpenArc hxy] at hz
    rcases hz with hz1 | hz2
    · exact Or.inl (connectedComponentIn_compl_pair_eq_left hxy hz1)
    · exact Or.inr (connectedComponentIn_compl_pair_eq_right hxy hz2)
  · rintro (rfl | rfl)
    · obtain ⟨z, hz⟩ := nonempty_circleOpenArc hxy
      have hz_compl : z ∈ ({x, y} : Set Circle)ᶜ := by
        rw [compl_pair_eq_union_circleOpenArc hxy]; exact Or.inl hz
      exact ⟨z, hz_compl, connectedComponentIn_compl_pair_eq_left hxy hz⟩
    · obtain ⟨z, hz⟩ := nonempty_circleOpenArc hxy.symm
      have hz_compl : z ∈ ({x, y} : Set Circle)ᶜ := by
        rw [compl_pair_eq_union_circleOpenArc hxy]; exact Or.inr hz
      exact ⟨z, hz_compl, connectedComponentIn_compl_pair_eq_right hxy hz⟩

/-- For $x \ne y$ on `Circle` and $a, b \in \operatorname{circleOpenArc} x y$ with $a \ne b$ and
$x.\operatorname{angleDiff}(a) < x.\operatorname{angleDiff}(b)$, `circleOpenArc a b` is the unique
component of `univ \ {a, b}` contained in `circleOpenArc x y`, and it equals
$\{z : x.\operatorname{angleDiff}(a) < x.\operatorname{angleDiff}(z) < x.\operatorname{angleDiff}(b)\}$. -/
theorem circleOpenArc_eq_of_angleDiff_lt {x y a b : Circle} (hxy : x ≠ y)
    (ha : a ∈ circleOpenArc x y) (hb : b ∈ circleOpenArc x y)
    (hab_lt : x.angleDiff a < x.angleDiff b) :
    circleOpenArc a b = {z : Circle | x.angleDiff a < x.angleDiff z ∧ x.angleDiff z < x.angleDiff b} ∧
    circleOpenArc a b ⊆ circleOpenArc x y ∧
    ¬ (circleOpenArc b a ⊆ circleOpenArc x y) := by
  have hab : a ≠ b := fun heq => (ne_of_lt hab_lt) (congrArg (x.angleDiff) heq)
  rw [mem_circleOpenArc_iff_angleDiff hxy] at ha hb
  have h1 : circleOpenArc a b =
      {z : Circle | x.angleDiff a < x.angleDiff z ∧ x.angleDiff z < x.angleDiff b} := by
    ext z
    rw [mem_circleOpenArc_iff_angleDiff hab, mem_ofPred_eq]
    have haz := angleDiff_eq_of_angleDiff (x := x) (a := a) (b := z)
    have hab' := angleDiff_eq_of_angleDiff (x := x) (a := a) (b := b)
    have hxz_ge := Circle.angleDiff_nonneg x z
    have hxz_lt := Circle.angleDiff_lt_two_pi x z
    have hxy_lt := Circle.angleDiff_lt_two_pi x y
    grind [-Circle.angleDiff]
  refine ⟨h1, ?_, ?_⟩
  · intro z hz
    rw [h1] at hz
    rw [mem_circleOpenArc_iff_angleDiff hxy]
    exact ⟨ha.1.trans hz.1, hz.2.trans hb.2⟩
  · intro hsub
    have hx_in : x ∈ circleOpenArc b a := by
      rw [mem_circleOpenArc_iff_angleDiff hab.symm]
      have hbx := angleDiff_eq_of_angleDiff (x := x) (a := b) (b := x)
      have hba := angleDiff_eq_of_angleDiff (x := x) (a := b) (b := a)
      have hxx : x.angleDiff x = 0 := by simp [Circle.angleDiff]
      have hxy_lt := Circle.angleDiff_lt_two_pi x y
      grind [-Circle.angleDiff]
    have hx_xy := (mem_circleOpenArc_iff_angleDiff hxy).mp (hsub hx_in)
    have hxx : x.angleDiff x = 0 := by simp [Circle.angleDiff]
    linarith [hx_xy.1]

/-- On `Circle`, for $x \ne y$ and distinct $a, b \in \operatorname{circleOpenArc} x y$,
`cuffSubArc univ (circleOpenArc x y) a b` equals `{z | onOpenArc (circleCoordFrom x) a b z}`. -/
theorem cuffSubArc_univ_circleOpenArc_eq {x y a b : Circle} (hxy : x ≠ y)
    (ha : a ∈ circleOpenArc x y) (hb : b ∈ circleOpenArc x y) (hab : a ≠ b) :
    cuffSubArc (univ : Set Circle) (circleOpenArc x y) a b =
      {z : Circle | onOpenArc (circleCoordFrom x) a b z} := by
  have hab_ne : x.angleDiff a ≠ x.angleDiff b := (circleCoordFrom x).injective.ne hab
  rcases lt_or_gt_of_ne hab_ne with hlt | hgt
  · obtain ⟨h_eq, h_sub, h_nsub⟩ := circleOpenArc_eq_of_angleDiff_lt hxy ha hb hlt
    have hset : {K ∈ componentsIn ((univ : Set Circle) \ {a, b}) | K ⊆ circleOpenArc x y} =
        {circleOpenArc a b} := by
      ext K
      simp only [mem_ofPred_eq, mem_componentsIn_univ_sdiff_pair_iff hab, mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl, hK⟩
        · rfl
        · exact False.elim (h_nsub hK)
      · rintro rfl
        exact ⟨Or.inl rfl, h_sub⟩
    unfold cuffSubArc
    rw [hset, sUnion_singleton, h_eq]
    ext z
    simp only [mem_ofPred_eq, onOpenArc, circleCoordFrom]
    rw [min_eq_left hlt.le, max_eq_right hlt.le]
  · obtain ⟨h_eq, h_sub, h_nsub⟩ := circleOpenArc_eq_of_angleDiff_lt hxy hb ha hgt
    have hset : {K ∈ componentsIn ((univ : Set Circle) \ {a, b}) | K ⊆ circleOpenArc x y} =
        {circleOpenArc b a} := by
      ext K
      simp only [mem_ofPred_eq, mem_componentsIn_univ_sdiff_pair_iff hab, mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl, hK⟩
        · exact False.elim (h_nsub hK)
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, h_sub⟩
    unfold cuffSubArc
    rw [hset, sUnion_singleton, h_eq]
    ext z
    simp only [mem_ofPred_eq, onOpenArc, circleCoordFrom]
    rw [min_eq_right hgt.le, max_eq_left hgt.le]

/-- Transfer of `cuffSubArc` along `oArcMap φ`. -/
theorem cuffSubArc_oArcMap {S : Type*} [TopologicalSpace S] {C : Set S}
    (φ : Circle ≃ₜ C) (S' : Set Circle) (a b : Circle) :
    cuffSubArc C (oArcMap φ '' S') (oArcMap φ a) (oArcMap φ b) =
      oArcMap φ '' cuffSubArc (univ : Set Circle) S' a b := by
  have hinj := injective_oArcMap φ
  have hemb := isEmbedding_oArcMap φ
  have hdiff : C \ {oArcMap φ a, oArcMap φ b} = oArcMap φ '' ((univ : Set Circle) \ {a, b}) := by
    rw [← compl_eq_univ_sdiff, ← diff_image_oArcMap φ]
    simp
  unfold cuffSubArc
  ext w
  simp only [mem_sUnion, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨K, ⟨⟨p, hp, rfl⟩, hK_sub⟩, hwK⟩
    rw [hdiff] at hp hwK hK_sub
    rcases hp with ⟨z, hz, rfl⟩
    rw [← isEmbedding_image_connectedComponentIn hemb hz] at hwK hK_sub
    rcases hwK with ⟨u, hu, rfl⟩
    refine ⟨u, ⟨connectedComponentIn ((univ : Set Circle) \ {a, b}) z, ⟨⟨z, hz, rfl⟩, ?_⟩, hu⟩, rfl⟩
    intro v hv
    exact (image_subset_image_iff hinj).mp hK_sub hv
  · rintro ⟨u, ⟨K₀, ⟨⟨z, hz, rfl⟩, hK₀_sub⟩, huK₀⟩, rfl⟩
    refine ⟨oArcMap φ '' connectedComponentIn ((univ : Set Circle) \ {a, b}) z, ⟨?_, ?_⟩,
      mem_image_of_mem _ huK₀⟩
    · rw [isEmbedding_image_connectedComponentIn hemb hz, ← hdiff]
      exact ⟨oArcMap φ z, by rw [hdiff]; exact mem_image_of_mem _ hz, rfl⟩
    · exact image_mono hK₀_sub

/-- Key Dichotomy for `(4.3)` on any $O$-arc $C$: if $s \ne t$ in $C$, $S_{\text{arc}}$ is a
component of $C \setminus \{s, t\}$, $a, b \in S_{\text{arc}}$ are distinct,
$c \in \operatorname{cuffSubArc} C S_{\text{arc}} a b$, and $d \in S_{\text{arc}}$ with $d \ne c$,
then either $\{a, b\}$ crosses $\{c, d\}$ on $C$, or
$\operatorname{cuffSubArc} C S_{\text{arc}} c d \subseteq \operatorname{cuffSubArc} C S_{\text{arc}} a b \setminus \{c\}$. -/
theorem crossesOn_or_cuffSubArc_ssubset_of_mem {S : Type*} [TopologicalSpace S]
    {C S_arc : Set S} {s t a b c d : S}
    (hC : IsOArc C) (hs : s ∈ C) (ht : t ∈ C) (hst : s ≠ t)
    (hS_arc : S_arc ∈ componentsIn (C \ {s, t}))
    (ha : a ∈ S_arc) (hb : b ∈ S_arc) (hab : a ≠ b)
    (hc : c ∈ cuffSubArc C S_arc a b) (hd : d ∈ S_arc) (hcd : c ≠ d) :
    CrossesOn C a b c d ∨
      (cuffSubArc C S_arc c d ⊆ cuffSubArc C S_arc a b ∧ c ∉ cuffSubArc C S_arc c d) := by
  obtain ⟨φ⟩ := hC
  have hinj := injective_oArcMap φ
  have hemb := isEmbedding_oArcMap φ
  let s' : Circle := φ.symm ⟨s, hs⟩
  let t' : Circle := φ.symm ⟨t, ht⟩
  have hs' : oArcMap φ s' = s := by simp [oArcMap, s']
  have ht' : oArcMap φ t' = t := by simp [oArcMap, t']
  have hst' : s' ≠ t' := fun heq => hst (hs' ▸ ht' ▸ congrArg (oArcMap φ) heq)
  have hdiff_st : C \ {s, t} = oArcMap φ '' ((univ : Set Circle) \ {s', t'}) := by
    rw [← hs', ← ht', ← compl_eq_univ_sdiff, ← diff_image_oArcMap φ]
    simp
  have hS_arc_form : ∃ x y : Circle, x ≠ y ∧ S_arc = oArcMap φ '' circleOpenArc x y := by
    rcases hS_arc with ⟨p, hp, rfl⟩
    rw [hdiff_st] at hp ⊢
    rcases hp with ⟨z, hz, rfl⟩
    rw [← isEmbedding_image_connectedComponentIn hemb hz]
    have hmem : connectedComponentIn ((univ : Set Circle) \ {s', t'}) z ∈
        componentsIn ((univ : Set Circle) \ {s', t'}) := ⟨z, hz, rfl⟩
    rw [mem_componentsIn_univ_sdiff_pair_iff hst'] at hmem
    rcases hmem with h1 | h2
    · exact ⟨s', t', hst', by rw [h1]⟩
    · exact ⟨t', s', hst'.symm, by rw [h2]⟩
  obtain ⟨x, y, hxy, rfl⟩ := hS_arc_form
  rcases ha with ⟨a', ha', rfl⟩
  rcases hb with ⟨b', hb', rfl⟩
  rcases hd with ⟨d', hd', rfl⟩
  have hab' : a' ≠ b' := fun heq => hab (congrArg (oArcMap φ) heq)
  rw [cuffSubArc_oArcMap φ (circleOpenArc x y) a' b',
    cuffSubArc_univ_circleOpenArc_eq hxy ha' hb' hab'] at hc
  rcases hc with ⟨c', hc', rfl⟩
  have hcd' : c' ≠ d' := fun heq => hcd (congrArg (oArcMap φ) heq)
  have hca' : c' ≠ a' := fun heq => not_onOpenArc_left (circleCoordFrom x) a' b' (heq ▸ hc')
  have hcb' : c' ≠ b' := fun heq => not_onOpenArc_right (circleCoordFrom x) a' b' (heq ▸ hc')
  by_cases hd_in : d' ∈ {z : Circle | onOpenArc (circleCoordFrom x) a' b' z} ∪ {a', b'}
  · right
    rw [cuffSubArc_oArcMap φ (circleOpenArc x y) a' b',
      cuffSubArc_oArcMap φ (circleOpenArc x y) c' d',
      cuffSubArc_univ_circleOpenArc_eq hxy ha' hb' hab',
      cuffSubArc_univ_circleOpenArc_eq hxy (by
        have hsub : cuffSubArc (univ : Set Circle) (circleOpenArc x y) a' b' ⊆ circleOpenArc x y := by
          unfold cuffSubArc
          intro z hz
          rcases mem_sUnion.mp hz with ⟨K, hK, hzK⟩
          exact hK.2 hzK
        rw [cuffSubArc_univ_circleOpenArc_eq hxy ha' hb' hab'] at hsub
        exact hsub hc') hd' hcd']
    refine ⟨image_mono ?_, ?_⟩
    · intro z hz
      simp only [mem_ofPred_eq, onOpenArc] at hc' hd_in hz ⊢
      rcases hd_in with hd_arc | (rfl | rfl)
      · constructor
        · exact lt_of_le_of_lt (le_min hc'.1.le hd_arc.1.le) hz.1
        · exact lt_of_lt_of_le hz.2 (max_le hc'.2.le hd_arc.2.le)
      · constructor
        · exact lt_of_le_of_lt (le_min hc'.1.le (min_le_left _ _)) hz.1
        · exact lt_of_lt_of_le hz.2 (max_le hc'.2.le (le_max_left _ _))
      · constructor
        · exact lt_of_le_of_lt (le_min hc'.1.le (min_le_right _ _)) hz.1
        · exact lt_of_lt_of_le hz.2 (max_le hc'.2.le (le_max_right _ _))
    · rintro ⟨z, hz, hzc⟩
      have hzc' : z = c' := hinj hzc
      subst hzc'
      exact not_onOpenArc_left (circleCoordFrom x) z d' hz
  · left
    rw [crossesOn_oArcMap_iff φ, crossesOn_univ_iff_circleCoordFrom x]
    have hda' : d' ≠ a' := fun heq => hd_in (Or.inr (Or.inl heq))
    have hdb' : d' ≠ b' := fun heq => hd_in (Or.inr (Or.inr heq))
    have hd_not_arc : ¬ onOpenArc (circleCoordFrom x) a' b' d' :=
      fun h => hd_in (Or.inl h)
    exact ⟨hab', hcd', hca'.symm, hda'.symm, hcb'.symm, hdb'.symm,
      iff_of_true hc' hd_not_arc⟩

/-! ## 4. Proof of Graph Minors VI, (4.3) -/

/-- In a connected graph $G$ with $|V(G)| \ge 2$, every vertex $c \in V(G)$ has a neighbour
$d \ne c$ in $G$. -/
private theorem exists_adj_ne_of_connected_ncard_ge_two {α β : Type*} {G : Graph α β}
    (hConn : IsGraphConnected G) (hCard : 2 ≤ V(G).ncard) {c : α} (hc : c ∈ V(G)) :
    ∃ e ∈ E(G), ∃ d ∈ V(G), d ≠ c ∧ G.IsLink e c d := by
  have hex_w : ∃ w ∈ V(G), w ≠ c := by
    by_contra! hall
    have hsub : V(G) ⊆ {c} := fun w hw => mem_singleton_iff.mpr (hall w hw)
    have hle : V(G).ncard ≤ ({c} : Set α).ncard := ncard_le_ncard hsub (finite_singleton c)
    rw [ncard_singleton] at hle
    omega
  obtain ⟨w, hw, hwc⟩ := hex_w
  obtain ⟨W⟩ := hConn.2 c hc w hw
  have hwalk : ∀ {u v : α} (W' : GraphWalk G u v), u = c → v ≠ c →
      ∃ e ∈ E(G), ∃ d ∈ V(G), d ≠ c ∧ G.IsLink e c d := by
    intro u v W'
    induction W' with
    | nil =>
      intro rfl hvc
      exact False.elim (hvc rfl)
    | @cons u v₁ v₂ e hlink _ ih =>
      intro rfl hvc
      rcases eq_or_ne v₁ u with rfl | hne
      · exact ih rfl hvc
      · exact ⟨e, hlink.edge_mem, v₁, hlink.right_mem, hne, hlink⟩
  exact hwalk W rfl hwc

/-- **Graph Minors VI, (4.3)** (page 125):
"Let $\Sigma$ be a cylinder, and let $C$ be a cuff of $\Sigma$. Let $s, t \in C$ be distinct, and
let $S$ be a component of $C - \{s, t\}$. Let $K$ be a connected graph with $|V(K)| \ge 2$,
properly drawn on $\Sigma$ with $V(K) \subseteq S$. Then there is an edge of $K$ with distinct ends
$a, b$ say, such that $S(a, b) \cap V(K) = \emptyset$." -/
theorem theorem_4_3_proof : Statement43 := by
  intro C s t S_arc K hC hs ht hst hS_arc _hK_prop hK_conn hK_card hK_sub
  have hOArc : IsOArc C := by
    have hC' := hC
    rw [cuffs_closedCylinder] at hC'
    rcases hC' with rfl | hC2
    · exact isOArc_cylinderCuff1
    · rw [mem_singleton_iff.mp hC2]
      exact isOArc_cylinderCuff2
  have hv₀ : K.V.Nonempty := hK_conn.1
  obtain ⟨a₀, ha₀⟩ := hv₀
  obtain ⟨e₀, he₀, b₀, hb₀, hba₀, hlink₀⟩ :=
    exists_adj_ne_of_connected_ncard_ge_two hK_conn hK_card ha₀
  have hab₀ : a₀ ≠ b₀ := hba₀.symm
  -- No two edges of K with distinct endpoints can cross on C.
  have h_not_cross : ∀ {e₁ e₂ : Set ClosedCylinder} {a b c d : ClosedCylinder},
      K.toGraph.IsLink e₁ a b → a ≠ b → K.toGraph.IsLink e₂ c d → c ≠ d →
      ¬ CrossesOn C a b c d := by
    intro e₁ e₂ a b c d hlink₁ hab hlink₂ hcd hcross
    have he₁ : e₁ ∈ K.E := hlink₁.1
    have he₂ : e₂ ∈ K.E := hlink₂.1
    have hcl₁ : closure e₁ = e₁ ∪ {a, b} := by
      rcases K.edge_cond e₁ he₁ with ⟨u, v, _, hcap, f, hf0, hf1⟩ | ⟨u, hcap, _⟩
      · have h_ioo_pc : IsPathConnected {t : unitInterval | (t : ℝ) ∈ Ioo (0 : ℝ) 1} := by
          have hconv : Convex ℝ (Ioo (0 : ℝ) 1) := convex_Ioo 0 1
          have hpc0 : IsPathConnected (Ioo (0 : ℝ) 1) :=
            hconv.isPathConnected ⟨1 / 2, by constructor <;> linarith⟩
          let clamp : ℝ → unitInterval := fun x =>
            ⟨max 0 (min 1 x), le_max_left 0 _, max_le zero_le_one (min_le_left 1 x)⟩
          have hclamp_cont : Continuous clamp :=
            (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _
          have himg : clamp '' Ioo (0 : ℝ) 1 = {t : unitInterval | (t : ℝ) ∈ Ioo (0 : ℝ) 1} := by
            ext τ
            constructor
            · rintro ⟨x, hx, rfl⟩
              simp only [clamp, mem_ofPred_eq]
              have hmin : min 1 x = x := min_eq_right (le_of_lt hx.2)
              have hmax : max 0 (min 1 x) = x := by rw [hmin]; exact max_eq_right (le_of_lt hx.1)
              rw [hmax]; exact hx
            · intro hτ
              refine ⟨(τ : ℝ), hτ, Subtype.ext ?_⟩
              simp only [clamp]
              have hmin : min 1 (τ : ℝ) = (τ : ℝ) := min_eq_right (le_of_lt hτ.2)
              rw [hmin]; exact max_eq_right (le_of_lt hτ.1)
          rw [← himg]
          exact hpc0.image hclamp_cont
        let phi : unitInterval → ClosedCylinder := fun τ => (f τ).1
        have hphi_cont : Continuous phi := continuous_subtype_val.comp f.continuous
        have himg_eq : phi '' {τ : unitInterval | (τ : ℝ) ∈ Ioo (0 : ℝ) 1} = closure e₁ \ K.V := by
          ext z
          constructor
          · rintro ⟨τ, hτ, rfl⟩
            refine ⟨(f τ).2, fun hzV => ?_⟩
            have hz_mem : phi τ ∈ closure e₁ ∩ K.V := ⟨(f τ).2, hzV⟩
            rw [hcap] at hz_mem
            rcases hz_mem with hzu | hzv
            · have hτ0 : τ = 0 := f.injective (Subtype.ext (hzu.trans hf0.symm))
              subst hτ0; exact lt_irrefl (0 : ℝ) hτ.1
            · have hτ1 : τ = 1 := f.injective (Subtype.ext (hzv.trans hf1.symm))
              subst hτ1; exact lt_irrefl (1 : ℝ) hτ.2
          · rintro ⟨hz_cl, hz_notV⟩
            let τ : unitInterval := f.symm ⟨z, hz_cl⟩
            have hfτ : phi τ = z := congrArg Subtype.val (f.apply_symm_apply ⟨z, hz_cl⟩)
            refine ⟨τ, ?_, hfτ⟩
            have hτ0 : (τ : ℝ) ≠ 0 := by
              intro h0
              have hτ_eq : τ = 0 := Subtype.ext h0
              have hz_eq : z = u := by rw [← hfτ, hτ_eq]; exact hf0
              have huV : u ∈ K.V := by
                have : u ∈ closure e₁ ∩ K.V := by rw [hcap]; exact mem_insert u {v}
                exact this.2
              exact hz_notV (hz_eq ▸ huV)
            have hτ1 : (τ : ℝ) ≠ 1 := by
              intro h1
              have hτ_eq : τ = 1 := Subtype.ext h1
              have hz_eq : z = v := by rw [← hfτ, hτ_eq]; exact hf1
              have hvV : v ∈ K.V := by
                have : v ∈ closure e₁ ∩ K.V := by rw [hcap]; exact mem_insert_of_mem u rfl
                exact this.2
              exact hz_notV (hz_eq ▸ hvV)
            exact ⟨lt_of_le_of_ne τ.2.1 (Ne.symm hτ0), lt_of_le_of_ne τ.2.2 hτ1⟩
        have hpc_diff : IsPathConnected (closure e₁ \ K.V) := by
          rw [← himg_eq]; exact h_ioo_pc.image hphi_cont
        have hsub_diff : closure e₁ \ K.V ⊆ K.U \ K.V :=
          sdiff_subset_sdiff_left (K.isClosed_U.closure_subset_iff.mpr (he₁.2.1.trans sdiff_subset))
        have he_sub_diff : e₁ ⊆ closure e₁ \ K.V :=
          subset_sdiff.mpr ⟨subset_closure, disjoint_left.mpr fun _ hxe hxV => (he₁.2.1 hxe).2 hxV⟩
        have hdiff_eq : closure e₁ \ K.V = e₁ :=
          he₁.2.2.2 (closure e₁ \ K.V) hsub_diff hpc_diff he_sub_diff
        calc closure e₁
          _ = (closure e₁ \ K.V) ∪ (closure e₁ ∩ K.V) := (sdiff_union_inter (closure e₁) K.V).symm
          _ = e₁ ∪ {a, b} := by rw [hdiff_eq, hlink₁.2.2.2]
      · exfalso
        have hpair : ({a, b} : Set ClosedCylinder) = {u} := hlink₁.2.2.2.symm.trans hcap
        have ha_eq : a = u := mem_singleton_iff.mp (hpair ▸ mem_insert a {b})
        have hb_eq : b = u := mem_singleton_iff.mp (hpair ▸ mem_insert_of_mem a rfl)
        exact hab (ha_eq.trans hb_eq.symm)
    -- Using `exists_compact_connected_of_walk` on single-edge walks gives compact connected sets!
    let W₁ : GraphWalk K.toGraph a b := GraphWalk.cons hlink₁ (GraphWalk.nil hlink₁.right_mem)
    let W₂ : GraphWalk K.toGraph c d := GraphWalk.cons hlink₂ (GraphWalk.nil hlink₂.right_mem)
    have hcl₂_comp : IsCompact (closure e₂) := by
      rcases K.edge_cond e₂ he₂ with ⟨_, _, _, _, f, _, _⟩ | ⟨_, _, ⟨f⟩⟩
      · have : CompactSpace (closure e₂) := f.compactSpace
        exact isCompact_iff_compactSpace.mpr this
      · have : CompactSpace (closure e₂) := f.compactSpace
        exact isCompact_iff_compactSpace.mpr this
    have hcl₁_comp : IsCompact (closure e₁) := by
      rcases K.edge_cond e₁ he₁ with ⟨_, _, _, _, f, _, _⟩ | ⟨_, _, ⟨f⟩⟩
      · have : CompactSpace (closure e₁) := f.compactSpace
        exact isCompact_iff_compactSpace.mpr this
      · have : CompactSpace (closure e₁) := f.compactSpace
        exact isCompact_iff_compactSpace.mpr this
    have hcl₁_conn : IsConnected (closure e₁) := by
      rcases K.edge_cond e₁ he₁ with ⟨_, _, _, _, f, _, _⟩ | ⟨_, _, ⟨f⟩⟩
      · have : ConnectedSpace (closure e₁) := f.surjective.connectedSpace f.continuous
        exact isConnected_iff_connectedSpace.mpr this
      · have : ConnectedSpace (closure e₁) := f.surjective.connectedSpace f.continuous
        exact isConnected_iff_connectedSpace.mpr this
    have hcl₂_conn : IsConnected (closure e₂) := by
      rcases K.edge_cond e₂ he₂ with ⟨_, _, _, _, f, _, _⟩ | ⟨_, _, ⟨f⟩⟩
      · have : ConnectedSpace (closure e₂) := f.surjective.connectedSpace f.continuous
        exact isConnected_iff_connectedSpace.mpr this
      · have : ConnectedSpace (closure e₂) := f.surjective.connectedSpace f.continuous
        exact isConnected_iff_connectedSpace.mpr this
    have ha_cl₁ : a ∈ closure e₁ := by
      have : a ∈ closure e₁ ∩ K.V := by rw [hlink₁.2.2.2]; exact mem_insert a {b}
      exact this.1
    have hb_cl₁ : b ∈ closure e₁ := by
      have : b ∈ closure e₁ ∩ K.V := by rw [hlink₁.2.2.2]; exact mem_insert_of_mem a rfl
      exact this.1
    have hc_cl₂ : c ∈ closure e₂ := by
      have : c ∈ closure e₂ ∩ K.V := by rw [hlink₂.2.2.2]; exact mem_insert c {d}
      exact this.1
    have hd_cl₂ : d ∈ closure e₂ := by
      have : d ∈ closure e₂ ∩ K.V := by rw [hlink₂.2.2.2]; exact mem_insert_of_mem c rfl
      exact this.1
    have hmeet := cuffCrossing_closedCylinder hC hcl₁_comp hcl₂_comp hcl₁_conn hcl₂_conn
      ha_cl₁ hb_cl₁ hc_cl₂ hd_cl₂ hcross
    rcases hmeet with ⟨z, hz1, hz2⟩
    by_cases hzV : z ∈ K.V
    · have hz_ab : z ∈ ({a, b} : Set ClosedCylinder) := by
        rw [← hlink₁.2.2.2]; exact ⟨hz1, hzV⟩
      have hz_cd : z ∈ ({c, d} : Set ClosedCylinder) := by
        rw [← hlink₂.2.2.2]; exact ⟨hz2, hzV⟩
      rcases hz_ab with rfl | rfl <;> rcases hz_cd with rfl | rfl
      · exact hcross.2.2.2.2.2.2.1 rfl
      · exact hcross.2.2.2.2.2.2.2.1 rfl
      · exact hcross.2.2.2.2.2.2.2.2.1 rfl
      · exact hcross.2.2.2.2.2.2.2.2.2.1 rfl
    · rw [hcl₁] at hz1
      rcases hz1 with hze₁ | (rfl | rfl)
      · have he_ne : e₁ ≠ e₂ := by
          rintro rfl
          have hpair : ({a, b} : Set ClosedCylinder) = {c, d} := hlink₁.2.2.2.symm.trans hlink₂.2.2.2
          have ha_cd : a ∈ ({c, d} : Set ClosedCylinder) := hpair ▸ mem_insert a {b}
          rcases ha_cd with rfl | rfl
          · exact hcross.2.2.2.2.2.2.1 rfl
          · exact hcross.2.2.2.2.2.2.2.1 rfl
        have hdisj : Disjoint e₁ e₂ := by
          rw [Set.disjoint_iff_inter_eq_empty]
          by_contra hnon
          have hnon_empty : (e₁ ∩ e₂).Nonempty := nonempty_iff_ne_empty.mpr hnon
          have hpc : IsPathConnected (e₁ ∪ e₂) := he₁.2.2.1.union he₂.2.2.1 hnon_empty
          have hsub : e₁ ∪ e₂ ⊆ K.U \ K.V := union_subset he₁.2.1 he₂.2.1
          have heq₁ : e₁ ∪ e₂ = e₁ := he₁.2.2.2 (e₁ ∪ e₂) hsub hpc subset_union_left
          have heq₂ : e₁ ∪ e₂ = e₂ := he₂.2.2.2 (e₁ ∪ e₂) hsub hpc subset_union_right
          exact he_ne (heq₁.symm.trans heq₂)
        -- Similarly z ∈ closure e₂ \ K.V ⊆ e₂:
        have hz_not_e₂ : z ∉ closure e₂ := by
          intro hz_cl₂
          -- Since e₁ is open in K.U \ K.V or rather e₁ ∪ e₂ is not connected:
          -- Even simpler: closure e₂ = e₂ ∪ {c, d} by symmetry!
          rcases K.edge_cond e₂ he₂ with ⟨u', v', _, hcap', f, hf0, hf1⟩ | ⟨u', hcap', _⟩
          · let τ : unitInterval := f.symm ⟨z, hz_cl₂⟩
            have hfτ : (f τ).1 = z := congrArg Subtype.val (f.apply_symm_apply ⟨z, hz_cl₂⟩)
            have hτ_ioo : (τ : ℝ) ∈ Ioo (0 : ℝ) 1 := by
              have h0 : (τ : ℝ) ≠ 0 := by
                intro h0
                have hτ_eq : τ = 0 := Subtype.ext h0
                have hz_u' : z = u' := by rw [← hfτ, hτ_eq]; exact hf0
                have hu'V : u' ∈ K.V := by
                  have : u' ∈ closure e₂ ∩ K.V := by rw [hcap']; exact mem_insert u' {v'}
                  exact this.2
                exact hzV (hz_u' ▸ hu'V)
              have h1 : (τ : ℝ) ≠ 1 := by
                intro h1
                have hτ_eq : τ = 1 := Subtype.ext h1
                have hz_v' : z = v' := by rw [← hfτ, hτ_eq]; exact hf1
                have hv'V : v' ∈ K.V := by
                  have : v' ∈ closure e₂ ∩ K.V := by rw [hcap']; exact mem_insert_of_mem u' rfl
                  exact this.2
                exact hzV (hz_v' ▸ hv'V)
              exact ⟨lt_of_le_of_ne τ.2.1 (Ne.symm h0), lt_of_le_of_ne τ.2.2 h1⟩
            have h_ioo_pc : IsPathConnected {t : unitInterval | (t : ℝ) ∈ Ioo (0 : ℝ) 1} := by
              have hconv : Convex ℝ (Ioo (0 : ℝ) 1) := convex_Ioo 0 1
              have hpc0 : IsPathConnected (Ioo (0 : ℝ) 1) :=
                hconv.isPathConnected ⟨1 / 2, by constructor <;> linarith⟩
              let clamp : ℝ → unitInterval := fun x =>
                ⟨max 0 (min 1 x), le_max_left 0 _, max_le zero_le_one (min_le_left 1 x)⟩
              have hclamp_cont : Continuous clamp :=
                (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _
              have himg : clamp '' Ioo (0 : ℝ) 1 = {t : unitInterval | (t : ℝ) ∈ Ioo (0 : ℝ) 1} := by
                ext s₀
                constructor
                · rintro ⟨x, hx, rfl⟩
                  simp only [clamp, mem_ofPred_eq]
                  have hmin : min 1 x = x := min_eq_right (le_of_lt hx.2)
                  have hmax : max 0 (min 1 x) = x := by rw [hmin]; exact max_eq_right (le_of_lt hx.1)
                  rw [hmax]; exact hx
                · intro hs₀
                  refine ⟨(s₀ : ℝ), hs₀, Subtype.ext ?_⟩
                  simp only [clamp]
                  have hmin : min 1 (s₀ : ℝ) = (s₀ : ℝ) := min_eq_right (le_of_lt hs₀.2)
                  rw [hmin]; exact max_eq_right (le_of_lt hs₀.1)
              rw [← himg]
              exact hpc0.image hclamp_cont
            let phi2 : unitInterval → ClosedCylinder := fun s₀ => (f s₀).1
            have hphi2_cont : Continuous phi2 := continuous_subtype_val.comp f.continuous
            let D2 := phi2 '' {s₀ : unitInterval | (s₀ : ℝ) ∈ Ioo (0 : ℝ) 1}
            have hD2_pc : IsPathConnected D2 := h_ioo_pc.image hphi2_cont
            have hD2_sub : D2 ⊆ K.U \ K.V := by
              rintro w ⟨s₀, hs₀, rfl⟩
              refine ⟨K.isClosed_U.closure_subset_iff.mpr (he₂.2.1.trans sdiff_subset) (f s₀).2,
                fun hwV => ?_⟩
              have hw_mem : phi2 s₀ ∈ closure e₂ ∩ K.V := ⟨(f s₀).2, hwV⟩
              rw [hcap'] at hw_mem
              rcases hw_mem with hwu | hwv
              · have hs0 : s₀ = 0 := f.injective (Subtype.ext (hwu.trans hf0.symm))
                subst hs0; exact lt_irrefl (0 : ℝ) hs₀.1
              · have hs1 : s₀ = 1 := f.injective (Subtype.ext (hwv.trans hf1.symm))
                subst hs1; exact lt_irrefl (1 : ℝ) hs₀.2
            have hz_D2 : z ∈ D2 := ⟨τ, hτ_ioo, hfτ⟩
            obtain ⟨w₀, hw₀⟩ := he₂.1
            have hw₀_D2 : w₀ ∈ D2 := by
              let s₀ := f.symm ⟨w₀, subset_closure hw₀⟩
              have hfs₀ : phi2 s₀ = w₀ := congrArg Subtype.val (f.apply_symm_apply ⟨w₀, subset_closure hw₀⟩)
              have hs0 : (s₀ : ℝ) ≠ 0 := by
                intro h0
                have hs₀_eq : s₀ = 0 := Subtype.ext h0
                have hw_u : w₀ = u' := by rw [← hfs₀, hs₀_eq]; exact hf0
                have hu'V : u' ∈ K.V := by
                  have : u' ∈ closure e₂ ∩ K.V := by rw [hcap']; exact mem_insert u' {v'}
                  exact this.2
                exact (he₂.2.1 hw₀).2 (hw_u ▸ hu'V)
              have hs1 : (s₀ : ℝ) ≠ 1 := by
                intro h1
                have hs₀_eq : s₀ = 1 := Subtype.ext h1
                have hw_v : w₀ = v' := by rw [← hfs₀, hs₀_eq]; exact hf1
                have hv'V : v' ∈ K.V := by
                  have : v' ∈ closure e₂ ∩ K.V := by rw [hcap']; exact mem_insert_of_mem u' rfl
                  exact this.2
                exact (he₂.2.1 hw₀).2 (hw_v ▸ hv'V)
              exact ⟨s₀, ⟨lt_of_le_of_ne s₀.2.1 (Ne.symm hs0), lt_of_le_of_ne s₀.2.2 hs1⟩, hfs₀⟩
            have hD2_e2 : D2 ∪ e₂ = e₂ :=
              he₂.2.2.2 (D2 ∪ e₂) (union_subset hD2_sub he₂.2.1)
                (hD2_pc.union he₂.2.2.1 ⟨w₀, hw₀_D2, hw₀⟩) subset_union_right
            have hze₂ : z ∈ e₂ := hD2_e2 ▸ Or.inl hz_D2
            exact disjoint_left.mp hdisj hze₁ hze₂
          · have hpair : ({c, d} : Set ClosedCylinder) = {u'} := hlink₂.2.2.2.symm.trans hcap'
            have hc_eq : c = u' := mem_singleton_iff.mp (hpair ▸ mem_insert c {d})
            have hd_eq : d = u' := mem_singleton_iff.mp (hpair ▸ mem_insert_of_mem c rfl)
            exact hcd (hc_eq.trans hd_eq.symm)
        exact hz_not_e₂ hz2
      · exact hzV hlink₁.left_mem
      · exact hzV hlink₁.right_mem
  -- Now finish by strong induction on `(cuffSubArc C S_arc a b ∩ K.V).ncard`.
  have h_min : ∀ (n : ℕ) (e : Set ClosedCylinder) (a b : ClosedCylinder),
      e ∈ K.E → a ∈ K.V → b ∈ K.V → a ≠ b → K.toGraph.IsLink e a b →
      (cuffSubArc C S_arc a b ∩ K.V).ncard = n →
      ∃ e' ∈ K.E, ∃ a' ∈ K.V, ∃ b' ∈ K.V,
        a' ≠ b' ∧ K.toGraph.IsLink e' a' b' ∧ Disjoint (cuffSubArc C S_arc a' b') K.V := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro e a b he ha hb hab hlink hcard
      by_cases hdisj : Disjoint (cuffSubArc C S_arc a b) K.V
      · exact ⟨e, he, a, ha, b, hb, hab, hlink, hdisj⟩
      · obtain ⟨c, hc_arc, hcV⟩ := not_disjoint_iff_nonempty_inter.mp hdisj
        obtain ⟨e', he', d, hdV, hdc, hlink'⟩ :=
          exists_adj_ne_of_connected_ncard_ge_two hK_conn hK_card hcV
        have hcd : c ≠ d := hdc.symm
        rcases crossesOn_or_cuffSubArc_ssubset_of_mem hOArc hs ht hst hS_arc
          (hK_sub ha) (hK_sub hb) hab hc_arc (hK_sub hdV) hcd with hcross | ⟨hsub_cd, hc_not_cd⟩
        · exact False.elim (h_not_cross hlink hab hlink' hcd hcross)
        · have hssub : cuffSubArc C S_arc c d ∩ K.V ⊂ cuffSubArc C S_arc a b ∩ K.V := by
            refine ssubset_iff_subset_ne.mpr ⟨inter_subset_inter_left K.V hsub_cd, ?_⟩
            intro heq
            have hc_mem : c ∈ cuffSubArc C S_arc a b ∩ K.V := ⟨hc_arc, hcV⟩
            rw [← heq] at hc_mem
            exact hc_not_cd hc_mem.1
          have hfin : (cuffSubArc C S_arc a b ∩ K.V).Finite :=
            K.finite_V.inter_of_right _
          have hlt : (cuffSubArc C S_arc c d ∩ K.V).ncard < n := by
            rw [← hcard]
            exact ncard_lt_ncard hssub hfin
          exact ih (cuffSubArc C S_arc c d ∩ K.V).ncard hlt e' c d he' hcV hdV hcd hlink' rfl
  exact h_min (cuffSubArc C S_arc a₀ b₀ ∩ K.V).ncard e₀ a₀ b₀ he₀ ha₀ hb₀ hab₀ hlink₀ rfl

end GraphMinor.GM06
