module

public import GraphMinor.Surface.DiscTwist
public import GraphMinor.Surface.CutCyl
public import GraphMinor.GM07.StarDisc
public import GraphMinor.GHR18.ManifoldCocycle

/-!
# Closed disc boundary homeomorphism extension and disjoint strip boxes

This file provides two foundational geometric tools used in the surgery proof of Geelen–Huynh–Richter
(2018), Theorem 2.6, and in the disc matching bound of LPPS (2022):

1. **Radial extension of boundary homeomorphisms on closed discs**:
   - `exists_closedBall_homeo_of_circle`: any homeomorphism `Circle ≃ₜ Circle` extends radially to
     `closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1`.
   - `exists_disc_homeo_of_bd`: any homeomorphism `discBd D₁ ≃ₜ discBd D₂` between the boundaries of
     two closed discs extends to `D₁ ≃ₜ D₂`.
   - `exists_chord_homeo`: any two chords `F, F'` of a closed disc `D` sharing the same endpoints
     `s ≠ t ∈ discBd D` are carried to each other by a homeomorphism `α : S ≃ₜ S` fixing `(discInt D)ᶜ`.

2. **Disjoint strip boxes around a matching** (`StripBox`, `exists_stripBox`):
   - Given a finite family `Q : Fin m → Set S` of pairwise disjoint proper `I`-arcs and a closed set
     `Z` disjoint from their boundary endpoints, constructs pairwise disjoint interior strip rectangles
     `f i '' (Icc (a i) (b i) ×ℂ Icc (-δ) δ) ⊆ (bd S)ᶜ` in which `Q i` is the real axis `im = 0` and
     whose omitted collar tips `Q i \ f i '' (Ioo (a i) (b i) ×ℂ {0})` are closed and disjoint from `Z`.
   - Also `isClosedDisc_rect`: any closed sub-rectangle `[x₁, x₂] × [y₁, y₂]` (`x₁ < x₂, y₁ < y₂`)
     inside a strip box maps to an interior closed disc `⊆ (bd S)ᶜ`.
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Topology Metric Complex Function GraphMinor.Surface GraphMinor.GM07

/-! ### Section 1: Gluing homeomorphisms on closed covers and radial disc extension -/

section DiscHomeo

/-- Glue two homeomorphisms defined on closed sets covering `X` and `Y` that agree on the overlaps. -/
noncomputable def homeo_glue_closed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} {A' B' : Set Y}
    (hAc : IsClosed A) (hBc : IsClosed B) (hcov : A ∪ B = univ)
    (hA'c : IsClosed A') (hB'c : IsClosed B') (hcov' : A' ∪ B' = univ)
    (eA : A ≃ₜ A') (eB : B ≃ₜ B')
    (hagree : ∀ x (hA : x ∈ A) (hB : x ∈ B), (eA ⟨x, hA⟩).1 = (eB ⟨x, hB⟩).1)
    (hagree_inv : ∀ y (hA' : y ∈ A') (hB' : y ∈ B'), (eA.symm ⟨y, hA'⟩).1 = (eB.symm ⟨y, hB'⟩).1) :
    X ≃ₜ Y := by
  classical
  have hBof : ∀ x : X, x ∉ A → x ∈ B := fun x hx => (hcov ▸ mem_univ x).resolve_left hx
  have hB'of : ∀ y : Y, y ∉ A' → y ∈ B' := fun y hy => (hcov' ▸ mem_univ y).resolve_left hy
  let f : X → Y := fun x => if hx : x ∈ A then (eA ⟨x, hx⟩).1 else (eB ⟨x, hBof x hx⟩).1
  let g : Y → X := fun y => if hy : y ∈ A' then (eA.symm ⟨y, hy⟩).1 else (eB.symm ⟨y, hB'of y hy⟩).1
  have hfA : ∀ x (hx : x ∈ A), f x = (eA ⟨x, hx⟩).1 := fun x hx => dite_eq_left hx
  have hfB : ∀ x (hx : x ∈ B), f x = (eB ⟨x, hx⟩).1 := fun x hx => by
    dsimp only [f]
    by_cases hA : x ∈ A
    · rw [dite_eq_left hA]; exact hagree x hA hx
    · exact dite_eq_right hA
  have hgA : ∀ y (hy : y ∈ A'), g y = (eA.symm ⟨y, hy⟩).1 := fun y hy => dite_eq_left hy
  have hgB : ∀ y (hy : y ∈ B'), g y = (eB.symm ⟨y, hy⟩).1 := fun y hy => by
    dsimp only [g]
    by_cases hA' : y ∈ A'
    · rw [dite_eq_left hA']; exact hagree_inv y hA' hy
    · exact dite_eq_right hA'
  have hfc : Continuous f := by
    rw [← continuousOn_univ, ← hcov]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hAc hBc
    · rw [continuousOn_iff_continuous_domRestrict]
      have heq : A.domRestrict f = fun x : A => (eA x).1 := funext fun x => hfA x.1 x.2
      rw [heq]; exact continuous_subtype_val.comp eA.continuous
    · rw [continuousOn_iff_continuous_domRestrict]
      have heq : B.domRestrict f = fun x : B => (eB x).1 := funext fun x => hfB x.1 x.2
      rw [heq]; exact continuous_subtype_val.comp eB.continuous
  have hgc : Continuous g := by
    rw [← continuousOn_univ, ← hcov']
    refine ContinuousOn.union_of_isClosed ?_ ?_ hA'c hB'c
    · rw [continuousOn_iff_continuous_domRestrict]
      have heq : A'.domRestrict g = fun y : A' => (eA.symm y).1 := funext fun y => hgA y.1 y.2
      rw [heq]; exact continuous_subtype_val.comp eA.symm.continuous
    · rw [continuousOn_iff_continuous_domRestrict]
      have heq : B'.domRestrict g = fun y : B' => (eB.symm y).1 := funext fun y => hgB y.1 y.2
      rw [heq]; exact continuous_subtype_val.comp eB.symm.continuous
  exact
    { toFun := f
      invFun := g
      left_inv := fun x => by
        by_cases hx : x ∈ A
        · rw [hfA x hx, hgA _ (eA ⟨x, hx⟩).2]; exact congrArg Subtype.val (eA.symm_apply_apply ⟨x, hx⟩)
        · have hxB := hBof x hx
          rw [hfB x hxB, hgB _ (eB ⟨x, hxB⟩).2]; exact congrArg Subtype.val (eB.symm_apply_apply ⟨x, hxB⟩)
      right_inv := fun y => by
        by_cases hy : y ∈ A'
        · rw [hgA y hy, hfA _ (eA.symm ⟨y, hy⟩).2]; exact congrArg Subtype.val (eA.apply_symm_apply ⟨y, hy⟩)
        · have hyB' := hB'of y hy
          rw [hgB y hyB', hfB _ (eB.symm ⟨y, hyB'⟩).2]; exact congrArg Subtype.val (eB.apply_symm_apply ⟨y, hyB'⟩)
      continuous_toFun := hfc
      continuous_invFun := hgc }

theorem homeo_glue_closed_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} {A' B' : Set Y}
    (hAc : IsClosed A) (hBc : IsClosed B) (hcov : A ∪ B = univ)
    (hA'c : IsClosed A') (hB'c : IsClosed B') (hcov' : A' ∪ B' = univ)
    (eA : A ≃ₜ A') (eB : B ≃ₜ B')
    (hagree : ∀ x (hA : x ∈ A) (hB : x ∈ B), (eA ⟨x, hA⟩).1 = (eB ⟨x, hB⟩).1)
    (hagree_inv : ∀ y (hA' : y ∈ A') (hB' : y ∈ B'), (eA.symm ⟨y, hA'⟩).1 = (eB.symm ⟨y, hB'⟩).1)
    {x : X} (hx : x ∈ A) :
    homeo_glue_closed hAc hBc hcov hA'c hB'c hcov' eA eB hagree hagree_inv x = (eA ⟨x, hx⟩).1 := by
  classical
  unfold homeo_glue_closed; dsimp only
  exact dite_eq_left hx

theorem homeo_glue_closed_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} {A' B' : Set Y}
    (hAc : IsClosed A) (hBc : IsClosed B) (hcov : A ∪ B = univ)
    (hA'c : IsClosed A') (hB'c : IsClosed B') (hcov' : A' ∪ B' = univ)
    (eA : A ≃ₜ A') (eB : B ≃ₜ B')
    (hagree : ∀ x (hA : x ∈ A) (hB : x ∈ B), (eA ⟨x, hA⟩).1 = (eB ⟨x, hB⟩).1)
    (hagree_inv : ∀ y (hA' : y ∈ A') (hB' : y ∈ B'), (eA.symm ⟨y, hA'⟩).1 = (eB.symm ⟨y, hB'⟩).1)
    {x : X} (hx : x ∈ B) :
    homeo_glue_closed hAc hBc hcov hA'c hB'c hcov' eA eB hagree hagree_inv x = (eB ⟨x, hx⟩).1 := by
  classical
  change (if h : x ∈ A then (eA ⟨x, h⟩).1 else (eB ⟨x, _⟩).1) = (eB ⟨x, hx⟩).1
  by_cases hA : x ∈ A
  · rw [dite_eq_left hA]; exact hagree x hA hx
  · exact dite_eq_right hA

/-- Radial extension of a circle homeomorphism `e : Circle ≃ₜ Circle` to the closed unit disc
`closedBall (0 : ℂ) 1`. -/
theorem exists_closedBall_homeo_of_circle (e : Circle ≃ₜ Circle) :
    ∃ Φ : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1,
      ∀ w : Circle, (Φ ⟨(w : ℂ), by rw [mem_closedBall_zero_iff, Circle.norm_coe]⟩).1 = (e w : ℂ) := by
  classical
  let rad : (Circle → Circle) → ℂ → ℂ := fun φ z =>
    if hz : z = 0 then 0 else ((‖z‖ : ℝ) : ℂ) * (φ (unitOf z hz) : ℂ)
  have hnorm : ∀ (φ : Circle → Circle) (z : ℂ), ‖rad φ z‖ = ‖z‖ := fun φ z => by
    dsimp only [rad]; split_ifs with hz
    · simp [hz]
    · rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, norm_norm]
  have hcont : ∀ (φ : Circle → Circle), Continuous φ → Continuous (rad φ) := fun φ hφ => by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      have h0 : rad φ 0 = 0 := by simp [rad]
      rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
      simp only [hnorm]
      simpa using (continuous_norm (E := ℂ)).tendsto 0
    · refine ContinuousOn.continuousAt ?_ (isOpen_ne.mem_nhds hz)
      rw [continuousOn_iff_continuous_domRestrict]
      have heq : ({w : ℂ | w ≠ 0}).domRestrict (rad φ) =
          fun x : {w : ℂ // w ≠ 0} => ((‖x.1‖ : ℝ) : ℂ) * (φ (unitOf x.1 x.2) : ℂ) := by
        funext x; exact dite_eq_right x.2
      rw [heq]
      exact (Complex.continuous_ofReal.comp (continuous_norm.comp continuous_subtype_val)).mul
        (continuous_subtype_val.comp (hφ.comp continuous_unitOf))
  have hinv : ∀ (e' : Circle ≃ₜ Circle) (z : ℂ), rad e'.symm (rad e' z) = z := fun e' z => by
    by_cases hz : z = 0
    · simp [rad, hz]
    · have hz1 : rad e' z ≠ 0 := by
        rw [← norm_ne_zero_iff, hnorm]; exact norm_ne_zero_iff.mpr hz
      have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hu : unitOf (rad e' z) hz1 = e' (unitOf z hz) := by
        have heq : rad e' z = ((‖z‖ : ℝ) : ℂ) * (e' (unitOf z hz) : ℂ) := dite_eq_right hz
        simpa only [heq] using unitOf_mul ‖z‖ hpos (e' (unitOf z hz)) (heq ▸ hz1)
      calc rad e'.symm (rad e' z)
          = ((‖rad e' z‖ : ℝ) : ℂ) * (e'.symm (unitOf (rad e' z) hz1) : ℂ) := dite_eq_right hz1
        _ = ((‖z‖ : ℝ) : ℂ) * (e'.symm (e' (unitOf z hz)) : ℂ) := by rw [hnorm, hu]
        _ = ((‖z‖ : ℝ) : ℂ) * (unitOf z hz : ℂ) := by rw [e'.symm_apply_apply]
        _ = z := norm_mul_unitOf z hz
  have hmem : ∀ (φ : Circle → Circle) (z : closedBall (0 : ℂ) 1), rad φ z.1 ∈ closedBall (0 : ℂ) 1 :=
    fun φ z => by rw [mem_closedBall_zero_iff, hnorm]; exact mem_closedBall_zero_iff.mp z.2
  refine ⟨{
    toFun := fun z => ⟨rad e z.1, hmem e z⟩
    invFun := fun z => ⟨rad e.symm z.1, hmem e.symm z⟩
    left_inv := fun z => Subtype.ext (hinv e z.1)
    right_inv := fun z => Subtype.ext (hinv e.symm z.1)
    continuous_toFun := Continuous.subtype_mk ((hcont e e.continuous).comp continuous_subtype_val) _
    continuous_invFun := Continuous.subtype_mk ((hcont e.symm e.symm.continuous).comp continuous_subtype_val) _
  }, fun w => ?_⟩
  have hne : (w : ℂ) ≠ 0 := Circle.coe_ne_zero w
  have hu : unitOf (w : ℂ) hne = w := by
    apply Circle.ext; rw [coe_unitOf, Circle.norm_coe]; simp
  change rad e (w : ℂ) = (e w : ℂ)
  rw [show rad e (w : ℂ) = ((‖(w : ℂ)‖ : ℝ) : ℂ) * (e (unitOf (w : ℂ) hne) : ℂ) from dite_eq_right hne,
      Circle.norm_coe, hu]
  simp

/-- Any homeomorphism `hbd : discBd D₁ ≃ₜ discBd D₂` between the boundaries of two closed discs
extends to a homeomorphism `D₁ ≃ₜ D₂`. -/
theorem exists_disc_homeo_of_bd {S : Type*} [TopologicalSpace S] {D₁ D₂ : Set S}
    (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂) (hbd : discBd D₁ ≃ₜ discBd D₂) :
    ∃ Φ : D₁ ≃ₜ D₂, ∀ x : discBd D₁, (Φ ⟨x.1, discBd_subset _ x.2⟩).1 = (hbd x).1 := by
  obtain ⟨h₁, g₁, c₁⟩ := hD₁.exists_isChart
  obtain ⟨h₂, g₂, c₂⟩ := hD₂.exists_isChart
  let eD₁ : closedBall (0 : ℂ) 1 ≃ₜ D₁ :=
    { toFun := fun z => ⟨g₁ z.1, c₁.gm z.2⟩
      invFun := fun x => ⟨h₁ x.1, c₁.hm x.2⟩
      left_inv := fun z => Subtype.ext (c₁.hg z.2)
      right_inv := fun x => Subtype.ext (c₁.gh x.2)
      continuous_toFun := Continuous.subtype_mk (c₁.gc.comp_continuous continuous_subtype_val fun z => z.2) _
      continuous_invFun := Continuous.subtype_mk (c₁.hc.comp_continuous continuous_subtype_val fun x => x.2) _ }
  let eD₂ : closedBall (0 : ℂ) 1 ≃ₜ D₂ :=
    { toFun := fun z => ⟨g₂ z.1, c₂.gm z.2⟩
      invFun := fun x => ⟨h₂ x.1, c₂.hm x.2⟩
      left_inv := fun z => Subtype.ext (c₂.hg z.2)
      right_inv := fun x => Subtype.ext (c₂.gh x.2)
      continuous_toFun := Continuous.subtype_mk (c₂.gc.comp_continuous continuous_subtype_val fun z => z.2) _
      continuous_invFun := Continuous.subtype_mk (c₂.hc.comp_continuous continuous_subtype_val fun x => x.2) _ }
  have hg₁_bd : ∀ w : Circle, g₁ (w : ℂ) ∈ discBd D₁ := fun w => by
    have hmem : (w : ℂ) ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)
    rw [← c₁.bd] at hmem
    obtain ⟨x, hx, hxe⟩ := hmem
    rw [← hxe, c₁.gh (discBd_subset _ hx)]; exact hx
  have hg₂_bd : ∀ w : Circle, g₂ (w : ℂ) ∈ discBd D₂ := fun w => by
    have hmem : (w : ℂ) ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)
    rw [← c₂.bd] at hmem
    obtain ⟨x, hx, hxe⟩ := hmem
    rw [← hxe, c₂.gh (discBd_subset _ hx)]; exact hx
  have hh₁_bd : ∀ x : discBd D₁, h₁ x.1 ∈ sphere (0 : ℂ) 1 := fun x => c₁.bd ▸ ⟨x.1, x.2, rfl⟩
  have hh₂_bd : ∀ x : discBd D₂, h₂ x.1 ∈ sphere (0 : ℂ) 1 := fun x => c₂.bd ▸ ⟨x.1, x.2, rfl⟩
  let eS₁ : Circle ≃ₜ discBd D₁ :=
    { toFun := fun w => ⟨g₁ (w : ℂ), hg₁_bd w⟩
      invFun := fun x => ⟨h₁ x.1, hh₁_bd x⟩
      left_inv := fun w => Circle.ext (c₁.hg (mem_closedBall_zero_iff.mpr (Circle.norm_coe w).le))
      right_inv := fun x => Subtype.ext (c₁.gh (discBd_subset _ x.2))
      continuous_toFun := Continuous.subtype_mk (c₁.gc.comp_continuous continuous_subtype_val
        fun w => mem_closedBall_zero_iff.mpr (Circle.norm_coe w).le) _
      continuous_invFun := Continuous.subtype_mk (c₁.hc.comp_continuous continuous_subtype_val
        fun x => discBd_subset _ x.2) _ }
  let eS₂ : Circle ≃ₜ discBd D₂ :=
    { toFun := fun w => ⟨g₂ (w : ℂ), hg₂_bd w⟩
      invFun := fun x => ⟨h₂ x.1, hh₂_bd x⟩
      left_inv := fun w => Circle.ext (c₂.hg (mem_closedBall_zero_iff.mpr (Circle.norm_coe w).le))
      right_inv := fun x => Subtype.ext (c₂.gh (discBd_subset _ x.2))
      continuous_toFun := Continuous.subtype_mk (c₂.gc.comp_continuous continuous_subtype_val
        fun w => mem_closedBall_zero_iff.mpr (Circle.norm_coe w).le) _
      continuous_invFun := Continuous.subtype_mk (c₂.hc.comp_continuous continuous_subtype_val
        fun x => discBd_subset _ x.2) _ }
  obtain ⟨Φ₀, hΦ₀⟩ := exists_closedBall_homeo_of_circle ((eS₁.trans hbd).trans eS₂.symm)
  refine ⟨(eD₁.symm.trans Φ₀).trans eD₂, fun x => ?_⟩
  let w : Circle := ⟨h₁ x.1, hh₁_bd x⟩
  have he1 : eD₁.symm ⟨x.1, discBd_subset _ x.2⟩ = ⟨(w : ℂ), by rw [mem_closedBall_zero_iff, Circle.norm_coe]⟩ := rfl
  have hΦw := hΦ₀ w
  have heS1 : eS₁ w = x := Subtype.ext (c₁.gh (discBd_subset _ x.2))
  show g₂ (Φ₀ (eD₁.symm ⟨x.1, discBd_subset _ x.2⟩)).1 = (hbd x).1
  rw [he1, hΦw]
  show g₂ (eS₂.symm (hbd (eS₁ w)) : ℂ) = (hbd x).1
  rw [heS1]
  exact c₂.gh (discBd_subset _ (hbd x).2)

/-- Any two chords `F, F'` of a closed disc `D` with the same boundary endpoints `s ≠ t ∈ discBd D`
are carried to each other by a homeomorphism `α : S ≃ₜ S` fixing `(discInt D)ᶜ`. -/
theorem exists_chord_homeo {S : Type} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x)
    {D F F' : Set S} {s t : S} (hD : IsClosedDisc D)
    (hFD : F ⊆ D) (hF'D : F' ⊆ D) (hst : s ≠ t)
    (hF : IsLineWithEnds F s t) (hF' : IsLineWithEnds F' s t)
    (hb : F ∩ discBd D = {s, t}) (hb' : F' ∩ discBd D = {s, t}) :
    ∃ α : S ≃ₜ S, α '' F = F' ∧ ∀ x ∈ (discInt D)ᶜ, α x = x := by
  classical
  obtain ⟨Δ₁, Δ₂, A₁, A₂, hA₁, hA₂, hAu, hAi, hΔ₁, hΔ₂, hΔu, hΔi, hbΔ₁, hbΔ₂, -, -⟩ :=
    disc_split hD hFD hst hF hb
  obtain ⟨Δ₁', Δ₂', A₁', A₂', hA₁', hA₂', hAu', hAi', hΔ₁', hΔ₂', hΔu', hΔi', hbΔ₁', hbΔ₂', -, -⟩ :=
    disc_split hD hF'D hst hF' hb'
  have hleft_mem : ∀ {L : Set S}, IsLineWithEnds L s t → s ∈ L := fun ⟨f, h0, _⟩ => h0 ▸ (f 0).2
  have hright_mem : ∀ {L : Set S}, IsLineWithEnds L s t → t ∈ L := fun ⟨f, _, h1⟩ => h1 ▸ (f 1).2
  -- Match the boundary arcs `A₁', A₂'` with `A₁, A₂` (swapping `Δ₁', Δ₂'` if needed):
  have hne_diff : ∀ {L : Set S}, IsLineWithEnds L s t → (L \ {s, t}).Nonempty := fun {L} hL => by
    obtain ⟨f, h0, h1⟩ := hL
    refine ⟨(f ⟨1 / 2, by norm_num, by norm_num⟩).1, (f _).2, ?_⟩
    rintro (h | h)
    · have := congrArg Subtype.val (f.injective (Subtype.ext (h.trans h0.symm))); norm_num at this
    · have := congrArg Subtype.val (f.injective (Subtype.ext (h.trans h1.symm))); norm_num at this
  have hmatch_or : (A₁' = A₁ ∧ A₂' = A₂) ∨ (A₁' = A₂ ∧ A₂' = A₁) := by
    have hdisjA : Disjoint (A₁ \ {s, t}) (A₂ \ {s, t}) := by
      rw [Set.disjoint_left]; rintro x ⟨h1, hne⟩ ⟨h2, -⟩
      exact hne (hAi ▸ ⟨h1, h2⟩)
    have hsub_u : (A₁ \ {s, t}) ∪ (A₂ \ {s, t}) = (A₁' \ {s, t}) ∪ (A₂' \ {s, t}) := by
      rw [← union_sdiff_distrib, ← union_sdiff_distrib, hAu, hAu']
    have hA1'_sub : (A₁' \ {s, t} ⊆ A₁ \ {s, t}) ∨ (A₁' \ {s, t} ⊆ A₂ \ {s, t}) := by
      have hpc := hA₁'.isPreconnected_diff
      have hcov1 : A₁' \ {s, t} ⊆ A₂ᶜ ∪ A₁ᶜ := fun x hx => by
        by_contra h
        rw [mem_union, not_or, mem_compl_iff, mem_compl_iff, not_not, not_not] at h
        exact hx.2 (hAi ▸ ⟨h.2, h.1⟩)
      have h1 : A₁' \ {s, t} ⊆ (A₁ \ {s, t}) ∪ (A₂ \ {s, t}) := hsub_u ▸ subset_union_left
      by_cases hm1 : ((A₁' \ {s, t}) ∩ (A₁ \ {s, t})).Nonempty
      · by_cases hm2 : ((A₁' \ {s, t}) ∩ (A₂ \ {s, t})).Nonempty
        · exfalso
          obtain ⟨x, hx, hx1, hx2⟩ := hpc A₂ᶜ A₁ᶜ hA₂.isCompact.isClosed.isOpen_compl
            hA₁.isCompact.isClosed.isOpen_compl hcov1
            (hm1.mono (show (A₁' \ {s, t}) ∩ (A₁ \ {s, t}) ⊆ (A₁' \ {s, t}) ∩ A₂ᶜ from
              fun y ⟨hy1, hy2⟩ => ⟨hy1, fun h => Set.disjoint_left.mp hdisjA hy2 ⟨h, hy1.2⟩⟩))
            (hm2.mono (show (A₁' \ {s, t}) ∩ (A₂ \ {s, t}) ⊆ (A₁' \ {s, t}) ∩ A₁ᶜ from
              fun y ⟨hy1, hy2⟩ => ⟨hy1, fun h => Set.disjoint_left.mp hdisjA ⟨h, hy1.2⟩ hy2⟩))
          rcases h1 hx with h | h
          · exact hx2 h.1
          · exact hx1 h.1
        · left; intro x hx
          rcases h1 hx with h | h
          · exact h
          · exact absurd ⟨x, hx, h⟩ hm2
      · right; intro x hx
        rcases h1 hx with h | h
        · exact absurd ⟨x, hx, h⟩ hm1
        · exact h
    have hadd_st : ∀ {L : Set S}, IsLineWithEnds L s t → (L \ {s, t}) ∪ {s, t} = L := fun {L} hL => by
      ext x; constructor
      · rintro (⟨hx, -⟩ | hx)
        · exact hx
        · rcases hx with rfl | h
          · exact hleft_mem hL
          · rw [mem_singleton_iff.mp h]; exact hright_mem hL
      · intro hx
        by_cases h : x ∈ ({s, t} : Set S)
        · exact Or.inr h
        · exact Or.inl ⟨hx, h⟩
    have hA2'_sub : (A₂' \ {s, t} ⊆ A₁ \ {s, t}) ∨ (A₂' \ {s, t} ⊆ A₂ \ {s, t}) := by
      have hpc := hA₂'.isPreconnected_diff
      have hcov1 : A₂' \ {s, t} ⊆ A₂ᶜ ∪ A₁ᶜ := fun x hx => by
        by_contra h
        rw [mem_union, not_or, mem_compl_iff, mem_compl_iff, not_not, not_not] at h
        exact hx.2 (hAi ▸ ⟨h.2, h.1⟩)
      have h1 : A₂' \ {s, t} ⊆ (A₁ \ {s, t}) ∪ (A₂ \ {s, t}) := hsub_u ▸ subset_union_right
      by_cases hm1 : ((A₂' \ {s, t}) ∩ (A₁ \ {s, t})).Nonempty
      · by_cases hm2 : ((A₂' \ {s, t}) ∩ (A₂ \ {s, t})).Nonempty
        · exfalso
          obtain ⟨x, hx, hx1, hx2⟩ := hpc A₂ᶜ A₁ᶜ hA₂.isCompact.isClosed.isOpen_compl
            hA₁.isCompact.isClosed.isOpen_compl hcov1
            (hm1.mono (show (A₂' \ {s, t}) ∩ (A₁ \ {s, t}) ⊆ (A₂' \ {s, t}) ∩ A₂ᶜ from
              fun y ⟨hy1, hy2⟩ => ⟨hy1, fun h => Set.disjoint_left.mp hdisjA hy2 ⟨h, hy1.2⟩⟩))
            (hm2.mono (show (A₂' \ {s, t}) ∩ (A₂ \ {s, t}) ⊆ (A₂' \ {s, t}) ∩ A₁ᶜ from
              fun y ⟨hy1, hy2⟩ => ⟨hy1, fun h => Set.disjoint_left.mp hdisjA ⟨h, hy1.2⟩ hy2⟩))
          rcases h1 hx with h | h
          · exact hx2 h.1
          · exact hx1 h.1
        · left; intro x hx
          rcases h1 hx with h | h
          · exact h
          · exact absurd ⟨x, hx, h⟩ hm2
      · right; intro x hx
        rcases h1 hx with h | h
        · exact absurd ⟨x, hx, h⟩ hm1
        · exact h
    rcases hA1'_sub with h11 | h12 <;> rcases hA2'_sub with h21 | h22
    · exfalso; obtain ⟨x, hx⟩ := hne_diff hA₂
      have hx' : x ∈ (A₁' \ {s, t}) ∪ (A₂' \ {s, t}) := hsub_u ▸ Or.inr hx
      rcases hx' with h | h
      · exact Set.disjoint_left.mp hdisjA (h11 h) hx
      · exact Set.disjoint_left.mp hdisjA (h21 h) hx
    · left
      have e1 : A₁' \ {s, t} = A₁ \ {s, t} := subset_antisymm h11 fun x hx => by
        rcases (hsub_u ▸ Or.inl hx : x ∈ (A₁' \ {s, t}) ∪ (A₂' \ {s, t})) with h | h
        · exact h
        · exact absurd (h22 h) (Set.disjoint_left.mp hdisjA hx)
      have e2 : A₂' \ {s, t} = A₂ \ {s, t} := subset_antisymm h22 fun x hx => by
        rcases (hsub_u ▸ Or.inr hx : x ∈ (A₁' \ {s, t}) ∪ (A₂' \ {s, t})) with h | h
        · exact absurd (h11 h) (Set.disjoint_right.mp hdisjA hx)
        · exact h
      exact ⟨by rw [← hadd_st hA₁', e1, hadd_st hA₁], by rw [← hadd_st hA₂', e2, hadd_st hA₂]⟩
    · right
      have e1 : A₁' \ {s, t} = A₂ \ {s, t} := subset_antisymm h12 fun x hx => by
        rcases (hsub_u ▸ Or.inr hx : x ∈ (A₁' \ {s, t}) ∪ (A₂' \ {s, t})) with h | h
        · exact h
        · exact absurd (h21 h) (Set.disjoint_right.mp hdisjA hx)
      have e2 : A₂' \ {s, t} = A₁ \ {s, t} := subset_antisymm h21 fun x hx => by
        rcases (hsub_u ▸ Or.inl hx : x ∈ (A₁' \ {s, t}) ∪ (A₂' \ {s, t})) with h | h
        · exact absurd (h12 h) (Set.disjoint_left.mp hdisjA hx)
        · exact h
      exact ⟨by rw [← hadd_st hA₁', e1, hadd_st hA₂], by rw [← hadd_st hA₂', e2, hadd_st hA₁]⟩
    · exfalso; obtain ⟨x, hx⟩ := hne_diff hA₁
      have hx' : x ∈ (A₁' \ {s, t}) ∪ (A₂' \ {s, t}) := hsub_u ▸ Or.inl hx
      rcases hx' with h | h
      · exact Set.disjoint_left.mp hdisjA hx (h12 h)
      · exact Set.disjoint_left.mp hdisjA hx (h22 h)
  -- Helper to build the glued homeomorphism once `A₁' = A₁` and `A₂' = A₂`:
  have hbuild : ∀ (E₁ E₂ : Set S), IsClosedDisc E₁ → IsClosedDisc E₂ → E₁ ∪ E₂ = D → E₁ ∩ E₂ = F' →
      discBd E₁ = A₁ ∪ F' → discBd E₂ = A₂ ∪ F' →
      ∃ α : S ≃ₜ S, α '' F = F' ∧ ∀ x ∈ (discInt D)ᶜ, α x = x := by
    intro E₁ E₂ hE₁ hE₂ hEu hEi hbE₁ hbE₂
    have hFl : s ∈ F := hleft_mem hF
    have hFr : t ∈ F := hright_mem hF
    have hF'l : s ∈ F' := hleft_mem hF'
    have hF'r : t ∈ F' := hright_mem hF'
    have hFc : IsClosed F := hF.isCompact.isClosed
    have hF'c : IsClosed F' := hF'.isCompact.isClosed
    obtain ⟨f, hf0, hf1⟩ := hF
    obtain ⟨f', hf'0, hf'1⟩ := hF'
    let φF : F ≃ₜ F' := f.symm.trans f'
    have hφFs : (φF ⟨s, hFl⟩).1 = s := by
      have h0 : f.symm ⟨s, hFl⟩ = 0 := f.injective (by rw [f.apply_symm_apply]; exact Subtype.ext hf0.symm)
      show (f' (f.symm ⟨s, hFl⟩)).1 = s; rw [h0, hf'0]
    have hφFt : (φF ⟨t, hFr⟩).1 = t := by
      have h1 : f.symm ⟨t, hFr⟩ = 1 := f.injective (by rw [f.apply_symm_apply]; exact Subtype.ext hf1.symm)
      show (f' (f.symm ⟨t, hFr⟩)).1 = t; rw [h1, hf'1]
    have hφF_inv_s : (φF.symm ⟨s, hF'l⟩).1 = s := by
      have : φF ⟨s, hFl⟩ = ⟨s, hF'l⟩ := Subtype.ext hφFs
      rw [← this, φF.symm_apply_apply]
    have hφF_inv_t : (φF.symm ⟨t, hF'r⟩).1 = t := by
      have : φF ⟨t, hFr⟩ = ⟨t, hF'r⟩ := Subtype.ext hφFt
      rw [← this, φF.symm_apply_apply]
    -- Build boundary homeomorphism `discBd Δᵢ ≃ₜ discBd Eᵢ` fixing `Aᵢ` and acting as `φF` on `F`:
    have hmkHalf : ∀ (B Δ E : Set S), IsClosed B → B ⊆ discBd D →
        IsClosedDisc Δ → IsClosedDisc E → ∀ (hbΔ : discBd Δ = B ∪ F) (hbE : discBd E = B ∪ F'),
        ∃ Φ : Δ ≃ₜ E,
          (∀ x (hx : x ∈ B), (Φ ⟨x, discBd_subset _ (hbΔ.symm ▸ Or.inl hx)⟩).1 = x) ∧
          (∀ x (hx : x ∈ F), (Φ ⟨x, discBd_subset _ (hbΔ.symm ▸ Or.inr hx)⟩).1 = (φF ⟨x, hx⟩).1) ∧
          (∀ y (hy : y ∈ B), (Φ.symm ⟨y, discBd_subset _ (hbE.symm ▸ Or.inl hy)⟩).1 = y) ∧
          (∀ y (hy : y ∈ F'), (Φ.symm ⟨y, discBd_subset _ (hbE.symm ▸ Or.inr hy)⟩).1 = (φF.symm ⟨y, hy⟩).1) := by
      intro B Δ E hBc hBsub hΔ' hE' hbΔ hbE
      let B₁ : Set (discBd Δ) := Subtype.val ⁻¹' B
      let F₁ : Set (discBd Δ) := Subtype.val ⁻¹' F
      let B₂ : Set (discBd E) := Subtype.val ⁻¹' B
      let F₂ : Set (discBd E) := Subtype.val ⁻¹' F'
      have hB₁c : IsClosed B₁ := hBc.preimage continuous_subtype_val
      have hF₁c : IsClosed F₁ := hFc.preimage continuous_subtype_val
      have hB₂c : IsClosed B₂ := hBc.preimage continuous_subtype_val
      have hF₂c : IsClosed F₂ := hF'c.preimage continuous_subtype_val
      have hcov1 : B₁ ∪ F₁ = univ := by
        ext x; simp only [B₁, F₁, mem_union, mem_preimage, mem_univ, iff_true]
        exact (Set.ext_iff.mp hbΔ x.1).mp x.2
      have hcov2 : B₂ ∪ F₂ = univ := by
        ext x; simp only [B₂, F₂, mem_union, mem_preimage, mem_univ, iff_true]
        exact (Set.ext_iff.mp hbE x.1).mp x.2
      let eB : B₁ ≃ₜ B₂ :=
        { toFun := fun x => ⟨⟨x.1.1, by rw [hbE]; exact Or.inl x.2⟩, x.2⟩
          invFun := fun y => ⟨⟨y.1.1, by rw [hbΔ]; exact Or.inl y.2⟩, y.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          continuous_toFun := by
            refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
            exact continuous_subtype_val.comp continuous_subtype_val
          continuous_invFun := by
            refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
            exact continuous_subtype_val.comp continuous_subtype_val }
      let eF : F₁ ≃ₜ F₂ :=
        { toFun := fun x => ⟨⟨(φF ⟨x.1.1, x.2⟩).1, by rw [hbE]; exact Or.inr (φF ⟨x.1.1, x.2⟩).2⟩, (φF ⟨x.1.1, x.2⟩).2⟩
          invFun := fun y => ⟨⟨(φF.symm ⟨y.1.1, y.2⟩).1, by rw [hbΔ]; exact Or.inr (φF.symm ⟨y.1.1, y.2⟩).2⟩, (φF.symm ⟨y.1.1, y.2⟩).2⟩
          left_inv := fun x => Subtype.ext (Subtype.ext (by
            change (φF.symm (φF ⟨x.1.1, x.2⟩)).1 = x.1.1; rw [φF.symm_apply_apply]))
          right_inv := fun y => Subtype.ext (Subtype.ext (by
            change (φF (φF.symm ⟨y.1.1, y.2⟩)).1 = y.1.1; rw [φF.apply_symm_apply]))
          continuous_toFun := by
            refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
            exact continuous_subtype_val.comp (φF.continuous.comp
              (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)))
          continuous_invFun := by
            refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
            exact continuous_subtype_val.comp (φF.symm.continuous.comp
              (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2))) }
      have hag : ∀ x (h1 : x ∈ B₁) (h2 : x ∈ F₁), (eB ⟨x, h1⟩).1 = (eF ⟨x, h2⟩).1 := fun x h1 h2 => by
        apply Subtype.ext
        have hst' : x.1 ∈ ({s, t} : Set S) := hb ▸ ⟨h2, hBsub h1⟩
        rcases hst' with he | he
        · change x.1 = (φF ⟨x.1, h2⟩).1
          have hsub : (⟨x.1, h2⟩ : F) = ⟨s, hFl⟩ := Subtype.ext he
          rw [hsub, he, hφFs]
        · change x.1 = (φF ⟨x.1, h2⟩).1
          have hsub : (⟨x.1, h2⟩ : F) = ⟨t, hFr⟩ := Subtype.ext (mem_singleton_iff.mp he)
          rw [hsub, mem_singleton_iff.mp he, hφFt]
      have hagi : ∀ y (h1 : y ∈ B₂) (h2 : y ∈ F₂), (eB.symm ⟨y, h1⟩).1 = (eF.symm ⟨y, h2⟩).1 := fun y h1 h2 => by
        apply Subtype.ext
        have hst' : y.1 ∈ ({s, t} : Set S) := hb' ▸ ⟨h2, hBsub h1⟩
        rcases hst' with he | he
        · change y.1 = (φF.symm ⟨y.1, h2⟩).1
          have hsub : (⟨y.1, h2⟩ : F') = ⟨s, hF'l⟩ := Subtype.ext he
          rw [hsub, he, hφF_inv_s]
        · change y.1 = (φF.symm ⟨y.1, h2⟩).1
          have hsub : (⟨y.1, h2⟩ : F') = ⟨t, hF'r⟩ := Subtype.ext (mem_singleton_iff.mp he)
          rw [hsub, mem_singleton_iff.mp he, hφF_inv_t]
      let hbd := homeo_glue_closed hB₁c hF₁c hcov1 hB₂c hF₂c hcov2 eB eF hag hagi
      obtain ⟨Φ, hΦ⟩ := exists_disc_homeo_of_bd hΔ' hE' hbd
      have hΦB : ∀ x (hx : x ∈ B), (Φ ⟨x, discBd_subset _ (hbΔ.symm ▸ Or.inl hx)⟩).1 = x := fun x hx => by
        rw [hΦ ⟨x, hbΔ.symm ▸ Or.inl hx⟩]
        exact congrArg Subtype.val (homeo_glue_closed_left hB₁c hF₁c hcov1 hB₂c hF₂c hcov2 eB eF hag hagi hx)
      have hΦF : ∀ x (hx : x ∈ F), (Φ ⟨x, discBd_subset _ (hbΔ.symm ▸ Or.inr hx)⟩).1 = (φF ⟨x, hx⟩).1 := fun x hx => by
        rw [hΦ ⟨x, hbΔ.symm ▸ Or.inr hx⟩]
        exact congrArg Subtype.val (homeo_glue_closed_right hB₁c hF₁c hcov1 hB₂c hF₂c hcov2 eB eF hag hagi hx)
      refine ⟨Φ, hΦB, hΦF, fun y hy => ?_, fun y hy => ?_⟩
      · have e1 : Φ ⟨y, discBd_subset _ (hbΔ.symm ▸ Or.inl hy)⟩ = ⟨y, discBd_subset _ (hbE.symm ▸ Or.inl hy)⟩ :=
          Subtype.ext (hΦB y hy)
        rw [← e1, Φ.symm_apply_apply]
      · have e1 : Φ ⟨(φF.symm ⟨y, hy⟩).1, discBd_subset _ (hbΔ.symm ▸ Or.inr (φF.symm ⟨y, hy⟩).2)⟩ =
            ⟨y, discBd_subset _ (hbE.symm ▸ Or.inr hy)⟩ := by
          apply Subtype.ext; rw [hΦF _ (φF.symm ⟨y, hy⟩).2]; exact congrArg Subtype.val (φF.apply_symm_apply ⟨y, hy⟩)
        rw [← e1, Φ.symm_apply_apply]
    obtain ⟨Φ₁, hΦ₁A, hΦ₁F, hΦ₁Ai, hΦ₁Fi⟩ := hmkHalf A₁ Δ₁ E₁ hA₁.isCompact.isClosed (hAu ▸ subset_union_left) hΔ₁ hE₁ hbΔ₁ hbE₁
    obtain ⟨Φ₂, hΦ₂A, hΦ₂F, hΦ₂Ai, hΦ₂Fi⟩ := hmkHalf A₂ Δ₂ E₂ hA₂.isCompact.isClosed (hAu ▸ subset_union_right) hΔ₂ hE₂ hbΔ₂ hbE₂
    -- Glue `Φ₁` and `Φ₂` into `ΦD : D ≃ₜ D`:
    let D₁ : Set D := Subtype.val ⁻¹' Δ₁
    let D₂ : Set D := Subtype.val ⁻¹' Δ₂
    let D₁' : Set D := Subtype.val ⁻¹' E₁
    let D₂' : Set D := Subtype.val ⁻¹' E₂
    have hD₁c : IsClosed D₁ := hΔ₁.isClosed.preimage continuous_subtype_val
    have hD₂c : IsClosed D₂ := hΔ₂.isClosed.preimage continuous_subtype_val
    have hD₁'c : IsClosed D₁' := hE₁.isClosed.preimage continuous_subtype_val
    have hD₂'c : IsClosed D₂' := hE₂.isClosed.preimage continuous_subtype_val
    have hcovD : D₁ ∪ D₂ = univ := by
      ext x; simp only [D₁, D₂, mem_union, mem_preimage, mem_univ, iff_true]
      exact (Set.ext_iff.mp hΔu x.1).mpr x.2
    have hcovD' : D₁' ∪ D₂' = univ := by
      ext x; simp only [D₁', D₂', mem_union, mem_preimage, mem_univ, iff_true]
      exact (Set.ext_iff.mp hEu x.1).mpr x.2
    let eD₁ : D₁ ≃ₜ D₁' :=
      { toFun := fun x => ⟨⟨(Φ₁ ⟨x.1.1, x.2⟩).1, (Set.ext_iff.mp hEu _).mp (Or.inl (Φ₁ ⟨x.1.1, x.2⟩).2)⟩, (Φ₁ ⟨x.1.1, x.2⟩).2⟩
        invFun := fun y => ⟨⟨(Φ₁.symm ⟨y.1.1, y.2⟩).1, (Set.ext_iff.mp hΔu _).mp (Or.inl (Φ₁.symm ⟨y.1.1, y.2⟩).2)⟩, (Φ₁.symm ⟨y.1.1, y.2⟩).2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext (by
          change (Φ₁.symm (Φ₁ ⟨x.1.1, x.2⟩)).1 = x.1.1; rw [Φ₁.symm_apply_apply]))
        right_inv := fun y => Subtype.ext (Subtype.ext (by
          change (Φ₁ (Φ₁.symm ⟨y.1.1, y.2⟩)).1 = y.1.1; rw [Φ₁.apply_symm_apply]))
        continuous_toFun := by
          refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
          exact continuous_subtype_val.comp (Φ₁.continuous.comp
            (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)))
        continuous_invFun := by
          refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
          exact continuous_subtype_val.comp (Φ₁.symm.continuous.comp
            (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2))) }
    let eD₂ : D₂ ≃ₜ D₂' :=
      { toFun := fun x => ⟨⟨(Φ₂ ⟨x.1.1, x.2⟩).1, (Set.ext_iff.mp hEu _).mp (Or.inr (Φ₂ ⟨x.1.1, x.2⟩).2)⟩, (Φ₂ ⟨x.1.1, x.2⟩).2⟩
        invFun := fun y => ⟨⟨(Φ₂.symm ⟨y.1.1, y.2⟩).1, (Set.ext_iff.mp hΔu _).mp (Or.inr (Φ₂.symm ⟨y.1.1, y.2⟩).2)⟩, (Φ₂.symm ⟨y.1.1, y.2⟩).2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext (by
          change (Φ₂.symm (Φ₂ ⟨x.1.1, x.2⟩)).1 = x.1.1; rw [Φ₂.symm_apply_apply]))
        right_inv := fun y => Subtype.ext (Subtype.ext (by
          change (Φ₂ (Φ₂.symm ⟨y.1.1, y.2⟩)).1 = y.1.1; rw [Φ₂.apply_symm_apply]))
        continuous_toFun := by
          refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
          exact continuous_subtype_val.comp (Φ₂.continuous.comp
            (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)))
        continuous_invFun := by
          refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
          exact continuous_subtype_val.comp (Φ₂.symm.continuous.comp
            (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2))) }
    have hagD : ∀ x (h1 : x ∈ D₁) (h2 : x ∈ D₂), (eD₁ ⟨x, h1⟩).1 = (eD₂ ⟨x, h2⟩).1 := fun x h1 h2 => by
      apply Subtype.ext
      have hxF : x.1 ∈ F := hΔi ▸ ⟨h1, h2⟩
      exact (hΦ₁F x.1 hxF).trans (hΦ₂F x.1 hxF).symm
    have hagDi : ∀ y (h1 : y ∈ D₁') (h2 : y ∈ D₂'), (eD₁.symm ⟨y, h1⟩).1 = (eD₂.symm ⟨y, h2⟩).1 := fun y h1 h2 => by
      apply Subtype.ext
      have hyF' : y.1 ∈ F' := hEi ▸ ⟨h1, h2⟩
      exact (hΦ₁Fi y.1 hyF').trans (hΦ₂Fi y.1 hyF').symm
    let ΦD : D ≃ₜ D := homeo_glue_closed hD₁c hD₂c hcovD hD₁'c hD₂'c hcovD' eD₁ eD₂ hagD hagDi
    have hΦD_bd : ∀ x (hx : x ∈ discBd D), (ΦD ⟨x, discBd_subset _ hx⟩).1 = x := fun x hx => by
      rcases (hAu ▸ hx : x ∈ A₁ ∪ A₂) with h1 | h2
      · have hx1 : (⟨x, discBd_subset _ hx⟩ : D) ∈ D₁ := discBd_subset Δ₁ (by rw [hbΔ₁]; exact Or.inl h1)
        exact (congrArg Subtype.val (homeo_glue_closed_left hD₁c hD₂c hcovD hD₁'c hD₂'c hcovD' eD₁ eD₂ hagD hagDi hx1)).trans (hΦ₁A x h1)
      · have hx2 : (⟨x, discBd_subset _ hx⟩ : D) ∈ D₂ := discBd_subset Δ₂ (by rw [hbΔ₂]; exact Or.inl h2)
        exact (congrArg Subtype.val (homeo_glue_closed_right hD₁c hD₂c hcovD hD₁'c hD₂'c hcovD' eD₁ eD₂ hagD hagDi hx2)).trans (hΦ₂A x h2)
    have hΦD_bdi : ∀ x (hx : x ∈ discBd D), (ΦD.symm ⟨x, discBd_subset _ hx⟩).1 = x := fun x hx => by
      have e1 : ΦD ⟨x, discBd_subset _ hx⟩ = ⟨x, discBd_subset _ hx⟩ := Subtype.ext (hΦD_bd x hx)
      rw [← e1, ΦD.symm_apply_apply]
    -- Glue `ΦD` on `D` and `id` on `(discInt D)ᶜ`:
    have hopenI : IsOpen (discInt D) := hD.isOpen_discInt hman
    have hcovS : D ∪ (discInt D)ᶜ = univ := by
      ext x; simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
      exact (em (x ∈ D)).imp_right fun h hx => h hx.1
    have hagS : ∀ x (h1 : x ∈ D) (h2 : x ∈ (discInt D)ᶜ),
        (ΦD ⟨x, h1⟩).1 = ((Homeomorph.refl ((discInt D)ᶜ : Set S)) ⟨x, h2⟩).1 := fun x h1 h2 =>
      hΦD_bd x (show x ∈ discBd D by by_contra hnb; exact h2 (show x ∈ discInt D from ⟨h1, hnb⟩))
    have hagSi : ∀ y (h1 : y ∈ D) (h2 : y ∈ (discInt D)ᶜ),
        (ΦD.symm ⟨y, h1⟩).1 = ((Homeomorph.refl ((discInt D)ᶜ : Set S)).symm ⟨y, h2⟩).1 := fun y h1 h2 =>
      hΦD_bdi y (show y ∈ discBd D by by_contra hnb; exact h2 (show y ∈ discInt D from ⟨h1, hnb⟩))
    let α : S ≃ₜ S := homeo_glue_closed hD.isClosed hopenI.isClosed_compl hcovS hD.isClosed hopenI.isClosed_compl hcovS
      ΦD (Homeomorph.refl _) hagS hagSi
    refine ⟨α, ?_, fun x hx => homeo_glue_closed_right hD.isClosed hopenI.isClosed_compl hcovS hD.isClosed hopenI.isClosed_compl hcovS
      ΦD (Homeomorph.refl _) hagS hagSi hx⟩
    ext y; constructor
    · rintro ⟨x, hxF, rfl⟩
      have hx1 : (⟨x, hFD hxF⟩ : D) ∈ D₁ := discBd_subset Δ₁ (by rw [hbΔ₁]; exact Or.inr hxF)
      have he1 : α x = (ΦD ⟨x, hFD hxF⟩).1 :=
        homeo_glue_closed_left hD.isClosed hopenI.isClosed_compl hcovS hD.isClosed hopenI.isClosed_compl hcovS
          ΦD (Homeomorph.refl _) hagS hagSi (hFD hxF)
      have he2 : (ΦD ⟨x, hFD hxF⟩).1 = (φF ⟨x, hxF⟩).1 :=
        (congrArg Subtype.val (homeo_glue_closed_left hD₁c hD₂c hcovD hD₁'c hD₂'c hcovD' eD₁ eD₂ hagD hagDi hx1)).trans (hΦ₁F x hxF)
      rw [he1, he2]; exact (φF ⟨x, hxF⟩).2
    · intro hyF'
      let x := (φF.symm ⟨y, hyF'⟩).1
      have hxF : x ∈ F := (φF.symm ⟨y, hyF'⟩).2
      have hx1 : (⟨x, hFD hxF⟩ : D) ∈ D₁ := discBd_subset Δ₁ (by rw [hbΔ₁]; exact Or.inr hxF)
      refine ⟨x, hxF, ?_⟩
      have he1 : α x = (ΦD ⟨x, hFD hxF⟩).1 :=
        homeo_glue_closed_left hD.isClosed hopenI.isClosed_compl hcovS hD.isClosed hopenI.isClosed_compl hcovS
          ΦD (Homeomorph.refl _) hagS hagSi (hFD hxF)
      have he2 : (ΦD ⟨x, hFD hxF⟩).1 = (φF ⟨x, hxF⟩).1 :=
        (congrArg Subtype.val (homeo_glue_closed_left hD₁c hD₂c hcovD hD₁'c hD₂'c hcovD' eD₁ eD₂ hagD hagDi hx1)).trans (hΦ₁F x hxF)
      rw [he1, he2]; exact congrArg Subtype.val (φF.apply_symm_apply ⟨y, hyF'⟩)
  rcases hmatch_or with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hbuild Δ₁' Δ₂' hΔ₁' hΔ₂' hΔu' hΔi' hbΔ₁' hbΔ₂'
  · exact hbuild Δ₂' Δ₁' hΔ₂' hΔ₁' (union_comm _ _ ▸ hΔu') (inter_comm _ _ ▸ hΔi') hbΔ₂' hbΔ₁'

end DiscHomeo

/-! ### Section 2: Closed discs from complex rectangles -/

section RectDisc

/-- Any closed rectangle `Icc x₁ x₂ ×ℂ Icc y₁ y₂` (`x₁ < x₂`, `y₁ < y₂`) is a closed disc in `ℂ`,
with boundary the perimeter of the rectangle. -/
theorem isClosedDisc_reProdIm_Icc {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ < x₂) (hy : y₁ < y₂) :
    IsClosedDisc (Icc x₁ x₂ ×ℂ Icc y₁ y₂) ∧
    discBd (Icc x₁ x₂ ×ℂ Icc y₁ y₂) =
      (Icc x₁ x₂ ×ℂ Icc y₁ y₂) \ (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂) := by
  let cx : ℝ := (x₁ + x₂) / 2
  let cy : ℝ := (y₁ + y₂) / 2
  let rx : ℝ := (x₂ - x₁) / 2
  let ry : ℝ := (y₂ - y₁) / 2
  have hrx : 0 < rx := by simp only [rx]; linarith
  have hry : 0 < ry := by simp only [ry]; linarith
  -- Affine homeomorphism from the `ℓ¹` diamond `{|u| + |v| ≤ 1}` to `Icc x₁ x₂ ×ℂ Icc y₁ y₂`:
  let A : ℂ → ℂ := fun z =>
    ((cx + rx * (z.re + z.im) : ℝ) : ℂ) + ((cy + ry * (z.re - z.im) : ℝ) : ℂ) * I
  let Ainv : ℂ → ℂ := fun w =>
    let u := (w.re - cx) / rx
    let v := (w.im - cy) / ry
    (((u + v) / 2 : ℝ) : ℂ) + (((u - v) / 2 : ℝ) : ℂ) * I
  have hAc : Continuous A := by
    unfold A; fun_prop
  have hAAinv : ∀ w, A (Ainv w) = w := fun w => by
    apply Complex.ext
    · simp only [A, Ainv, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_zero, add_im, mul_im]
      field_simp [hrx.ne']; ring
    · simp only [A, Ainv, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_zero, add_im, mul_im]
      field_simp [hry.ne']; ring
  have hAinvA : ∀ z, Ainv (A z) = z := fun z => by
    apply Complex.ext
    · simp only [A, Ainv, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_zero, add_im, mul_im]
      field_simp [hrx.ne', hry.ne']; ring
    · simp only [A, Ainv, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_zero, add_im, mul_im]
      field_simp [hrx.ne', hry.ne']; ring
  -- Compose with `nu : closedBall 0 1 → diamond` and `mu : diamond → closedBall 0 1`:
  let g : ℂ → ℂ := fun z => A (nu z)
  let h : ℂ → ℂ := fun w => mu (Ainv w)
  have hAre : ∀ z : ℂ, (A z).re = cx + rx * (z.re + z.im) := fun z => by simp [A]
  have hAim : ∀ z : ℂ, (A z).im = cy + ry * (z.re - z.im) := fun z => by simp [A]
  have habs_iff : ∀ u v r : ℝ, (|u + v| ≤ r ∧ |u - v| ≤ r) ↔ |u| + |v| ≤ r := fun u v r => by
    rw [abs_le, abs_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      cases le_total 0 u <;> cases le_total 0 v <;>
        simp [abs_of_nonneg, abs_of_nonpos, *] <;> linarith
    · intro h
      have hu : -|u| ≤ u ∧ u ≤ |u| := ⟨neg_abs_le u, le_abs_self u⟩
      have hv : -|v| ≤ v ∧ v ≤ |v| := ⟨neg_abs_le v, le_abs_self v⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have habs_lt_iff : ∀ u v r : ℝ, (|u + v| < r ∧ |u - v| < r) ↔ |u| + |v| < r := fun u v r => by
    rw [abs_lt, abs_lt]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      cases le_total 0 u <;> cases le_total 0 v <;>
        simp [abs_of_nonneg, abs_of_nonpos, *] <;> linarith
    · intro h
      have hu := neg_abs_le u; have hu' := le_abs_self u
      have hv := neg_abs_le v; have hv' := le_abs_self v
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hsq : ∀ z : ℂ, z ∈ closedBall (0 : ℂ) 1 ↔ g z ∈ Icc x₁ x₂ ×ℂ Icc y₁ y₂ := fun z => by
    rw [mem_closedBall_zero_iff, Complex.mem_reProdIm, ← nn_nu z]
    simp only [g, hAre, hAim, mem_Icc, nn]
    rw [← habs_iff (nu z).re (nu z).im 1, abs_le, abs_le]
    simp only [cx, cy, rx, ry]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  have hoo_iff : ∀ z : ℂ, ‖z‖ < 1 ↔ g z ∈ Ioo x₁ x₂ ×ℂ Ioo y₁ y₂ := fun z => by
    rw [Complex.mem_reProdIm, ← nn_nu z]
    simp only [g, hAre, hAim, mem_Ioo, nn]
    rw [← habs_lt_iff (nu z).re (nu z).im 1, abs_lt, abs_lt]
    simp only [cx, cy, rx, ry]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  have hbd_eq : ∀ z : ℂ, z ∈ sphere (0 : ℂ) 1 ↔
      g z ∈ (Icc x₁ x₂ ×ℂ Icc y₁ y₂) \ (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂) := fun z => by
    rw [mem_sphere_zero_iff_norm, mem_sdiff, ← hsq z, ← hoo_iff z, mem_closedBall_zero_iff]
    constructor
    · intro h; exact ⟨h.le, by linarith⟩
    · rintro ⟨h1, h2⟩; linarith
  have hgi : ∀ z, h (g z) = z := fun z => by simp only [h, g, hAinvA, mu_nu]
  have hgh : ∀ w, g (h w) = w := fun w => by simp only [h, g, nu_mu, hAAinv]
  have hgc : Continuous g := hAc.comp continuous_nu
  have hginj : Function.Injective g := fun z₁ z₂ he => by rw [← hgi z₁, he, hgi z₂]
  obtain ⟨hD0, hDb0⟩ := GM11.closedBall_disc
  obtain ⟨h', hh'c, hh'l⟩ := exists_inv_of_compactOn (isCompact_closedBall (0 : ℂ) 1) hgc.continuousOn hginj.injOn
  have hres := hD0.image hgc.continuousOn hh'c hh'l
  have him_rect : g '' closedBall (0 : ℂ) 1 = Icc x₁ x₂ ×ℂ Icc y₁ y₂ := by
    ext w; constructor
    · rintro ⟨z, hz, rfl⟩; exact (hsq z).mp hz
    · intro hw; exact ⟨h w, (hsq (h w)).mpr (by rw [hgh w]; exact hw), hgh w⟩
  have him_bd : g '' sphere (0 : ℂ) 1 = (Icc x₁ x₂ ×ℂ Icc y₁ y₂) \ (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂) := by
    ext w; constructor
    · rintro ⟨z, hz, rfl⟩; exact (hbd_eq z).mp hz
    · intro hw; exact ⟨h w, (hbd_eq (h w)).mpr (by rw [hgh w]; exact hw), hgh w⟩
  rw [him_rect, hDb0, him_bd] at hres
  exact hres

end RectDisc

/-! ### Section 3: Disjoint strip boxes around a matching -/

section StripBoxSec

variable {S : Type} [TopologicalSpace S]

/-- A family of pairwise disjoint interior strip rectangles around a finite family `Q : Fin m → Set S`
of proper `I`-arcs in `S`. Inside each rectangle `R i = [a i, b i] × [-δ, δ]`, `f i` embeds `R i`
into `(bd S)ᶜ` sending the real axis `im = 0` onto the middle segment of `Q i`, and avoiding all
other arcs `Q i'`. -/
structure StripBox (S : Type) [TopologicalSpace S] {m : ℕ} (Q : Fin m → Set S) where
  a : Fin m → ℝ
  b : Fin m → ℝ
  hab : ∀ i, a i < b i
  δ : ℝ
  hδ : 0 < δ
  f : Fin m → ℂ → S
  hfc : ∀ i, ContinuousOn (f i) (Icc (a i) (b i) ×ℂ Icc (-δ) δ)
  hfi : ∀ i, InjOn (f i) (Icc (a i) (b i) ×ℂ Icc (-δ) δ)
  hfo : ∀ i (U : Set ℂ), IsOpen U → U ⊆ Ioo (a i) (b i) ×ℂ Ioo (-δ) δ → IsOpen (f i '' U)
  hint : ∀ i, f i '' (Icc (a i) (b i) ×ℂ Icc (-δ) δ) ⊆ (bd S)ᶜ
  hdisj : Pairwise fun i i' =>
    Disjoint (f i '' (Icc (a i) (b i) ×ℂ Icc (-δ) δ)) (f i' '' (Icc (a i') (b i') ×ℂ Icc (-δ) δ))
  hQ_eq : ∀ i, ∀ z ∈ Icc (a i) (b i) ×ℂ Icc (-δ) δ, f i z ∈ Q i ↔ z.im = 0
  hQ_other : ∀ i i', i ≠ i' → Disjoint (f i '' (Icc (a i) (b i) ×ℂ Icc (-δ) δ)) (Q i')
  htip_closed : ∀ i, IsClosed (Q i \ f i '' (Ioo (a i) (b i) ×ℂ {0}))

namespace StripBox

variable {m : ℕ} {Q : Fin m → Set S}

/-- The closed complex rectangle `[a i, b i] × [-δ, δ]`. -/
def rect (sb : StripBox S Q) (i : Fin m) : Set ℂ :=
  Icc (sb.a i) (sb.b i) ×ℂ Icc (-sb.δ) sb.δ

/-- The open complex rectangle `(a i, b i) × (-δ, δ)`. -/
def openRect (sb : StripBox S Q) (i : Fin m) : Set ℂ :=
  Ioo (sb.a i) (sb.b i) ×ℂ Ioo (-sb.δ) sb.δ

/-- The image of `rect i` in `S`. -/
def box (sb : StripBox S Q) (i : Fin m) : Set S :=
  sb.f i '' sb.rect i

/-- The image of `openRect i` in `S`. -/
def openBox (sb : StripBox S Q) (i : Fin m) : Set S :=
  sb.f i '' sb.openRect i

/-- The middle open segment of `Q i` inside `openBox i`. -/
def mid (sb : StripBox S Q) (i : Fin m) : Set S :=
  sb.f i '' (Ioo (sb.a i) (sb.b i) ×ℂ {0})

/-- The closed collar tips of `Q i` outside `mid i`. -/
def tip (sb : StripBox S Q) (i : Fin m) : Set S :=
  Q i \ sb.mid i

/-- Shrink the half-width `δ` of a `StripBox` to any `0 < δ' ≤ δ`. -/
def shrink (sb : StripBox S Q) (δ' : ℝ) (hδ' : 0 < δ') (hle : δ' ≤ sb.δ) : StripBox S Q where
  a := sb.a
  b := sb.b
  hab := sb.hab
  δ := δ'
  hδ := hδ'
  f := sb.f
  hfc := fun i => (sb.hfc i).mono fun z hz => by
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨hz.1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  hfi := fun i => (sb.hfi i).mono fun z hz => by
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨hz.1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  hfo := fun i U hUo hU => sb.hfo i U hUo (hU.trans fun z hz => by
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨hz.1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩)
  hint := fun i => (image_mono (fun z hz => by
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨hz.1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩)).trans (sb.hint i)
  hdisj := fun i j hij => (sb.hdisj hij).mono
    (image_mono fun z hz => by rw [Complex.mem_reProdIm] at hz ⊢; exact ⟨hz.1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩)
    (image_mono fun z hz => by rw [Complex.mem_reProdIm] at hz ⊢; exact ⟨hz.1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩)
  hQ_eq := fun i z hz => sb.hQ_eq i z (by
    rw [Complex.mem_reProdIm] at hz ⊢; exact ⟨hz.1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩)
  hQ_other := fun i j hij => (sb.hQ_other i j hij).mono_left
    (image_mono fun z hz => by rw [Complex.mem_reProdIm] at hz ⊢; exact ⟨hz.1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩)
  htip_closed := sb.htip_closed

/-- Any closed sub-rectangle `[x₁, x₂] × [y₁, y₂] ⊆ sb.rect i` (`x₁ < x₂`, `y₁ < y₂`) maps under
`sb.f i` to an interior closed disc in `S`. -/
theorem isClosedDisc_subrect [T2Space S] (sb : StripBox S Q) (i : Fin m)
    {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ < x₂) (hy : y₁ < y₂)
    (hsub : Icc x₁ x₂ ×ℂ Icc y₁ y₂ ⊆ sb.rect i) :
    IsClosedDisc (sb.f i '' (Icc x₁ x₂ ×ℂ Icc y₁ y₂)) ∧
    sb.f i '' (Icc x₁ x₂ ×ℂ Icc y₁ y₂) ⊆ (bd S)ᶜ := by
  obtain ⟨hD, -⟩ := isClosedDisc_reProdIm_Icc hx hy
  have hcomp : IsCompact (Icc x₁ x₂ ×ℂ Icc y₁ y₂) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨inv, hinvc, hinvl⟩ := exists_inv_of_compactOn hcomp ((sb.hfc i).mono hsub) ((sb.hfi i).mono hsub)
  exact ⟨(hD.image ((sb.hfc i).mono hsub) hinvc hinvl).1, (image_mono hsub).trans (sb.hint i)⟩

/-- Any closed ball `closedBall c r ⊆ sb.rect i` (`0 < r`) maps under `sb.f i` to an interior
closed disc in `S`. -/
theorem isClosedDisc_subball [T2Space S] (sb : StripBox S Q) (i : Fin m)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hsub : closedBall c r ⊆ sb.rect i) :
    IsClosedDisc (sb.f i '' closedBall c r) ∧ sb.f i '' closedBall c r ⊆ (bd S)ᶜ := by
  obtain ⟨hD0, -⟩ := GM11.closedBall_disc
  have htrans : (fun z : ℂ => (r : ℂ) * z + c) '' closedBall 0 1 = closedBall c r := by
    ext w; constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
      nlinarith
    · intro hw
      refine ⟨(w - c) / (r : ℂ), ?_, by field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne']; ring⟩
      rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_le_one hr]
      simpa [dist_eq_norm] using mem_closedBall.mp hw
  have hD : IsClosedDisc (closedBall c r) := by
    rw [← htrans]
    refine (hD0.image (f := fun z : ℂ => (r : ℂ) * z + c) (f' := fun w : ℂ => (w - c) / (r : ℂ))
      (by fun_prop) (by fun_prop) (fun z _ => ?_)).1
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simp [hrc]
  obtain ⟨inv, hinvc, hinvl⟩ := exists_inv_of_compactOn (isCompact_closedBall c r)
    ((sb.hfc i).mono hsub) ((sb.hfi i).mono hsub)
  exact ⟨(hD.image ((sb.hfc i).mono hsub) hinvc hinvl).1, (image_mono hsub).trans (sb.hint i)⟩

end StripBox

/-- Construct a `StripBox S Q` for any finite family `Q : Fin m → Set S` of pairwise disjoint
proper `I`-arcs, with collar tips disjoint from a given closed set `Z` that avoids all boundary
endpoints of `Q`. -/
theorem exists_stripBox (hS : IsSurface S) {m : ℕ} (Q : Fin m → Set S)
    (hQ : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (Q i) u v ∧ Q i ∩ bd S = {u, v})
    (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    {Z : Set S} (hZc : IsClosed Z) (hZbd : ∀ i, Disjoint Z (Q i ∩ bd S)) :
    ∃ sb : StripBox S Q, ∀ i, Disjoint Z (sb.tip i) := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨T, _, j, K, hT, hj, hK, hcov, hinter, -⟩ := exists_capAll S hS
  have : T2Space T := hT.2.1
  have hji := hj.injective
  -- For each `i`, parameterize `Q i` by `a_i : I → S` and get a strip chart `(O_i, K_i, θ_i)` in `T`:
  have hparam : ∀ i : Fin m, ∃ (a : unitInterval → S),
      IsArcMap a ∧ range a = Q i ∧ a 0 ∈ bd S ∧ a 1 ∈ bd S ∧
      ∀ t : unitInterval, t ≠ 0 → t ≠ 1 → a t ∉ bd S := by
    intro i
    obtain ⟨u, v, huv, hl, hb⟩ := hQ i
    obtain ⟨a, ha, hr, h0, h1⟩ := hl.exists_arc
    refine ⟨a, ha, hr, h0 ▸ (hb ▸ Or.inl rfl : u ∈ Q i ∩ bd S).2,
      h1 ▸ (hb ▸ Or.inr rfl : v ∈ Q i ∩ bd S).2, fun t ht0 ht1 hbd => ?_⟩
    have hmem : a t ∈ ({u, v} : Set S) := hb ▸ ⟨hr ▸ mem_range_self t, hbd⟩
    rcases hmem with h | h
    · exact ht0 (ha.2 (h.trans h0.symm))
    · exact ht1 (ha.2 (h.trans h1.symm))
  choose p hp_arc hp_rng hp0 hp1 hp_int using hparam
  have hstrip : ∀ i : Fin m, ∃ (Os : Set ℂ) (Ks : ℂ → T) (θ : unitInterval → ℝ),
      StripChart Os Ks ∧ Continuous θ ∧ StrictMono θ ∧
      ∀ t : unitInterval, (θ t : ℂ) ∈ Os ∧ Ks (θ t) = j (p i t) := fun i =>
    exists_stripChart_of_arc hT ⟨hj.continuous.comp (hp_arc i).1, hji.comp (hp_arc i).2⟩
  choose Os Ks θ hKs hθc hθm hθ using hstrip
  -- Choose `η_i ∈ (0, 1/4)` so the tips `p i '' (Icc 0 η_i ∪ Icc (1 - η_i) 1)` miss `Z`:
  have heta : ∀ i : Fin m, ∃ η : ℝ, 0 < η ∧ η < 1 / 4 ∧
      Disjoint Z (p i '' {t : unitInterval | t.1 ≤ η ∨ 1 - η ≤ t.1}) := by
    intro i
    have h0Z : p i 0 ∉ Z := fun h =>
      Set.disjoint_left.mp (hZbd i) h ⟨hp_rng i ▸ mem_range_self 0, hp0 i⟩
    have h1Z : p i 1 ∉ Z := fun h =>
      Set.disjoint_left.mp (hZbd i) h ⟨hp_rng i ▸ mem_range_self 1, hp1 i⟩
    have hpre_o : IsOpen (p i ⁻¹' Zᶜ) := hZc.isOpen_compl.preimage (hp_arc i).1
    obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.isOpen_iff.mp hpre_o 0 h0Z
    obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp hpre_o 1 h1Z
    let η := min (1 / 8) (min (r₀ / 2) (r₁ / 2))
    have hη0 : 0 < η := lt_min (by norm_num) (lt_min (half_pos hr₀) (half_pos hr₁))
    have hη4 : η < 1 / 4 := (min_le_left _ _).trans_lt (by norm_num)
    refine ⟨η, hη0, hη4, ?_⟩
    rw [Set.disjoint_left]; rintro _ hxZ ⟨t, ht, rfl⟩
    rcases ht with hle | hge
    · have hd : dist t (0 : unitInterval) < r₀ := by
        rw [Subtype.dist_eq, Set.Icc.coe_zero, Real.dist_eq, sub_zero, abs_of_nonneg t.2.1]
        exact hle.trans_lt (((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hr₀))
      exact hr₀sub hd hxZ
    · have hd : dist t (1 : unitInterval) < r₁ := by
        rw [Subtype.dist_eq, Set.Icc.coe_one, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr t.2.2)]
        have : 1 - t.1 ≤ η := by linarith
        exact this.trans_lt (((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hr₁))
      exact hr₁sub hd hxZ
  choose η hη0 hη4 hηZ using heta
  let tL : Fin m → unitInterval := fun i => ⟨η i, (hη0 i).le, by linarith [hη4 i]⟩
  let tR : Fin m → unitInterval := fun i => ⟨1 - η i, by linarith [hη4 i], by linarith [hη0 i]⟩
  have htLR : ∀ i, tL i < tR i := fun i => show η i < 1 - η i by linarith [hη4 i]
  let a : Fin m → ℝ := fun i => θ i (tL i)
  let b : Fin m → ℝ := fun i => θ i (tR i)
  have hab : ∀ i, a i < b i := fun i => hθm i (htLR i)
  -- For each `i`, the compact middle segment `M_i := j '' (p i '' Icc (tL i) (tR i))` is disjoint from
  -- the closed set `Bad_i := K ∪ (⋃ i' ≠ i, j '' Q i') ∪ (j '' (Q i \ p i '' Ioo (tL i) (tR i)))`!
  -- Wait: `M_i` contains the two endpoints `p i (tL i)` and `p i (tR i)` which are NOT in `Ioo (tL i) (tR i)`,
  -- so use `K ∪ (⋃ i' ≠ i, j '' Q i') ∪ (j '' (p i '' (Iic (tL i / 2) ∪ Ici (1 - η i / 2))))`!
  -- Even simpler: pick `U_i` open in `T` separating the compact sets `M_i` pairwise AND avoiding `K`!
  have hQ_closed : ∀ i, IsClosed (Q i) := fun i => by
    rw [← hp_rng i]; exact (isCompact_range (hp_arc i).1).isClosed
  -- Wait: build pairwise disjoint open sets `U_i` in `T` with `M_i ⊆ U_i`, `U_i ⊆ Kᶜ`, `Disjoint U_i (j '' Q i')` (`i' ≠ i`)!
  let M : Fin m → Set T := fun i => (fun t => j (p i t)) '' Icc (tL i) (tR i)
  have hMcpt : ∀ i, IsCompact (M i) := fun i =>
    isCompact_Icc.image (hj.continuous.comp (hp_arc i).1)
  have hMsubQ : ∀ i, M i ⊆ j '' Q i := by
    intro i; rintro _ ⟨t, _, rfl⟩; exact ⟨p i t, hp_rng i ▸ mem_range_self t, rfl⟩
  have hMnotK : ∀ i, Disjoint (M i) K := fun i => by
    rw [Set.disjoint_left]; rintro _ ⟨t, ht, rfl⟩ hK'
    have hbd : p i t ∈ bd S := by
      have : j (p i t) ∈ range j ∩ K := ⟨mem_range_self _, hK'⟩
      rw [hinter] at this
      obtain ⟨y, hy, he⟩ := this; exact hji he ▸ hy
    have ht0 : t ≠ 0 := fun h => by
      have h1 : η i ≤ t.1 := ht.1; rw [h] at h1; change η i ≤ (0 : ℝ) at h1; linarith [hη0 i]
    have ht1 : t ≠ 1 := fun h => by
      have h1 : t.1 ≤ 1 - η i := ht.2; rw [h] at h1; change (1 : ℝ) ≤ 1 - η i at h1; linarith [hη0 i]
    exact hp_int i t ht0 ht1 hbd
  have : CompactSpace T := hT.1
  have hsep : ∀ i i' : Fin m, i ≠ i' → ∃ U V : Set T, IsOpen U ∧ IsOpen V ∧ M i ⊆ U ∧ M i' ⊆ V ∧ Disjoint U V := by
    intro i i' hne
    have hdisjM : Disjoint (M i) (M i') :=
      (Set.disjoint_image_of_injective hji (hQdisj hne)).mono (hMsubQ i) (hMsubQ i')
    obtain ⟨U, V, hUo, hVo, hMU, hMV, hcl⟩ :=
      exists_disjoint_closure_nhds (hMcpt i).isClosed (hMcpt i').isClosed hdisjM
    exact ⟨U, V, hUo, hVo, hMU, hMV, hcl.mono subset_closure subset_closure⟩
  choose U_sep V_sep hUsep_o hVsep_o hUsep_m hVsep_m hUV_disj using hsep
  let W_i : Fin m → Set T := fun i =>
    Kᶜ ∩ (⋂ (i' : Fin m) (h : i ≠ i'), (j '' Q i')ᶜ ∩
      if hlt : i.1 < i'.1 then U_sep i i' h else V_sep i' i h.symm)
  have hWi_o : ∀ i, IsOpen (W_i i) := fun i => by
    refine hK.isOpen_compl.inter (isOpen_iInter_of_finite fun i' => isOpen_iInter_of_finite fun h => ?_)
    refine (hj.isClosedMap _ (hQ_closed i')).isOpen_compl.inter ?_
    split_ifs <;> [exact hUsep_o i i' h; exact hVsep_o i' i h.symm]
  have hM_in_W : ∀ i, M i ⊆ W_i i := fun i y hy => by
    refine ⟨Set.disjoint_left.mp (hMnotK i) hy, mem_iInter.mpr fun i' => mem_iInter.mpr fun h => ⟨?_, ?_⟩⟩
    · exact Set.disjoint_left.mp (Set.disjoint_image_of_injective hji (hQdisj h)) (hMsubQ i hy)
    · split_ifs
      · exact hUsep_m i i' h hy
      · exact hVsep_m i' i h.symm hy
  have hW_disj : Pairwise fun i i' => Disjoint (W_i i) (W_i i') := by
    intro i i' hne
    rw [Set.disjoint_left]; intro y hy1 hy2
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · have h1 := (mem_iInter.mp (mem_iInter.mp hy1.2 i') hne).2
      rw [dite_eq_left hlt] at h1
      have h2 := (mem_iInter.mp (mem_iInter.mp hy2.2 i) hne.symm).2
      rw [dite_eq_right (not_lt.mpr hlt.le)] at h2
      exact Set.disjoint_left.mp (hUV_disj i i' hne) h1 h2
    · have h1 := (mem_iInter.mp (mem_iInter.mp hy1.2 i') hne).2
      rw [dite_eq_right (not_lt.mpr hgt.le)] at h1
      have h2 := (mem_iInter.mp (mem_iInter.mp hy2.2 i) hne.symm).2
      rw [dite_eq_left hgt] at h2
      exact Set.disjoint_left.mp (hUV_disj i' i hne.symm) h2 h1
  -- For each `i`, find `δ_i > 0` so `[a i, b i] × [-δ_i, δ_i] ⊆ Os i`, maps into `W_i i`, and misses the closed tips of `Q i`:
  have hδi : ∀ i : Fin m, ∃ d : ℝ, 0 < d ∧
      Icc (a i) (b i) ×ℂ Icc (-d) d ⊆ Os i ∧
      Ks i '' (Icc (a i) (b i) ×ℂ Icc (-d) d) ⊆ W_i i ∧
      ∀ z ∈ Icc (a i) (b i) ×ℂ Icc (-d) d, Ks i z ∈ j '' Q i ↔ z.im = 0 := by
    intro i
    let tips_i : Set T := (fun t => j (p i t)) '' {t : unitInterval | t.1 ≤ η i / 2 ∨ 1 - η i / 2 ≤ t.1}
    have htips_c : IsClosed tips_i := by
      have hcpt : IsCompact {t : unitInterval | t.1 ≤ η i / 2 ∨ 1 - η i / 2 ≤ t.1} := by
        have h1 : IsClosed {t : unitInterval | t.1 ≤ η i / 2} := isClosed_le continuous_subtype_val continuous_const
        have h2 : IsClosed {t : unitInterval | 1 - η i / 2 ≤ t.1} := isClosed_le continuous_const continuous_subtype_val
        exact (h1.union h2).isCompact
      exact (hcpt.image (hj.continuous.comp (hp_arc i).1)).isClosed
    have hopenG : IsOpen (Os i ∩ Ks i ⁻¹' (W_i i ∩ tips_iᶜ)) :=
      (hKs i).hc.isOpen_inter_preimage (hKs i).isOpen ((hWi_o i).inter htips_c.isOpen_compl)
    have hseg_sub : (fun x : ℝ => (x : ℂ)) '' Icc (a i) (b i) ⊆ Os i ∩ Ks i ⁻¹' (W_i i ∩ tips_iᶜ) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨t, ht_in, htx⟩ := intermediate_value_Icc (htLR i).le (hθc i).continuousOn hx
      rw [← htx]
      refine ⟨(hθ i t).1, by
        rw [mem_preimage, (hθ i t).2]
        refine ⟨hM_in_W i ⟨t, ht_in, rfl⟩, fun ⟨t', ht', he⟩ => ?_⟩
        have htt' : t' = t := (hp_arc i).2 (hji he)
        rw [htt'] at ht'
        rcases ht' with hle | hge
        · have : η i ≤ t.1 := ht_in.1; linarith [hη0 i]
        · have : t.1 ≤ 1 - η i := ht_in.2; linarith [hη0 i]⟩
    have hseg_cpt : IsCompact ((fun x : ℝ => (x : ℂ)) '' Icc (a i) (b i)) :=
      isCompact_Icc.image Complex.continuous_ofReal
    obtain ⟨r, hr, hrsub⟩ := hseg_cpt.exists_thickening_subset_open hopenG hseg_sub
    let d := r / 2
    have hd : 0 < d := half_pos hr
    have hrect_in : Icc (a i) (b i) ×ℂ Icc (-d) d ⊆ Os i ∩ Ks i ⁻¹' (W_i i ∩ tips_iᶜ) := fun z hz => by
      rw [Complex.mem_reProdIm] at hz
      apply hrsub
      rw [Metric.mem_thickening_iff]
      refine ⟨(z.re : ℂ), ⟨z.re, hz.1, rfl⟩, ?_⟩
      rw [dist_eq_norm, show z - (z.re : ℂ) = (z.im : ℂ) * I by apply Complex.ext <;> simp,
          norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have : |z.im| ≤ d := abs_le.mpr hz.2
      linarith [show d = r / 2 from rfl, hr]
    refine ⟨d, hd, fun z hz => (hrect_in hz).1, by rintro _ ⟨z, hz, rfl⟩; exact (hrect_in hz).2.1, fun z hz => ?_⟩
    constructor
    · intro hzQ
      obtain ⟨x, hxQ, hxe⟩ := hzQ
      obtain ⟨t, rfl⟩ := hp_rng i ▸ hxQ
      have hzeq : z = (θ i t : ℂ) := (hKs i).hi (hrect_in hz).1 (hθ i t).1 (hxe.symm.trans (hθ i t).2.symm)
      rw [hzeq]; simp
    · intro him0
      rw [Complex.mem_reProdIm] at hz
      obtain ⟨t, _, htx⟩ := intermediate_value_Icc (htLR i).le (hθc i).continuousOn hz.1
      have hzeq : z = (θ i t : ℂ) := Complex.ext (by simp [htx]) (by simp [him0])
      rw [hzeq, (hθ i t).2]
      exact ⟨p i t, hp_rng i ▸ mem_range_self t, rfl⟩
  choose δi hδi_pos hδi_Os hδi_W hδi_Q using hδi
  -- Take a uniform `δ > 0` (if `m = 0`, pick `1`; otherwise min over `Fin m`):
  obtain ⟨δ, hδ_pos, hδ_le⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i : Fin m, δ ≤ δi i := by
    by_cases hm : m = 0
    · subst hm; exact ⟨1, one_pos, fun i => Fin.elim0 i⟩
    · have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, Nat.pos_of_ne_zero hm⟩, Finset.mem_univ _⟩
      refine ⟨(Finset.univ : Finset (Fin m)).inf' hne δi, ?_, fun i => Finset.inf'_le δi (Finset.mem_univ i)⟩
      rw [Finset.lt_inf'_iff]; exact fun i _ => hδi_pos i
  -- Lift `Ks i` along `j` to `f i : ℂ → S` on `Icc (a i) (b i) ×ℂ Icc (-δ) δ`:
  have hsub_rect : ∀ i, Icc (a i) (b i) ×ℂ Icc (-δ) δ ⊆ Icc (a i) (b i) ×ℂ Icc (-δi i) (δi i) := fun i z hz => by
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨hz.1, ⟨by linarith [hz.2.1, hδ_le i], by linarith [hz.2.2, hδ_le i]⟩⟩
  have hK_in_rng : ∀ i z, z ∈ Icc (a i) (b i) ×ℂ Icc (-δ) δ → Ks i z ∈ range j := fun i z hz => by
    have hW := hδi_W i ⟨z, hsub_rect i hz, rfl⟩
    exact (hcov ▸ mem_univ (Ks i z)).resolve_right hW.1
  let f : Fin m → ℂ → S := fun i z =>
    if h : Ks i z ∈ range j then h.choose else p i 0
  have hjf : ∀ i z, z ∈ Icc (a i) (b i) ×ℂ Icc (-δ) δ → j (f i z) = Ks i z := fun i z hz => by
    have hr := hK_in_rng i z hz
    simp only [f, dite_eq_left hr]
    exact hr.choose_spec
  refine ⟨{
    a := a
    b := b
    hab := hab
    δ := δ
    hδ := hδ_pos
    f := f
    hfc := fun i => by
      rw [hj.isEmbedding.continuousOn_iff]
      exact ((hKs i).hc.mono ((hsub_rect i).trans (hδi_Os i))).congr fun z hz => hjf i z hz
    hfi := fun i z hz w hw hfe => (hKs i).hi (hδi_Os i (hsub_rect i hz)) (hδi_Os i (hsub_rect i hw))
      (by rw [← hjf i z hz, ← hjf i w hw, hfe])
    hfo := fun i U hUo hU => by
      have hUsub : U ⊆ Icc (a i) (b i) ×ℂ Icc (-δ) δ := hU.trans fun z hz => by
        rw [Complex.mem_reProdIm] at hz ⊢; exact ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩
      have hpre : j ⁻¹' (Ks i '' U) = f i '' U := by
        ext x; constructor
        · rintro ⟨z, hz, hze⟩
          exact ⟨z, hz, hji ((hjf i z (hUsub hz)).trans hze)⟩
        · rintro ⟨z, hz, rfl⟩
          exact ⟨z, hz, (hjf i z (hUsub hz)).symm⟩
      rw [← hpre]
      exact ((hKs i).ho U hUo (hUsub.trans ((hsub_rect i).trans (hδi_Os i)))).preimage hj.continuous
    hint := fun i => by
      rintro _ ⟨z, hz, rfl⟩ hbd
      have hK' : j (f i z) ∈ K := (hinter ▸ mem_image_of_mem j hbd : j (f i z) ∈ range j ∩ K).2
      rw [hjf i z hz] at hK'
      exact (hδi_W i ⟨z, hsub_rect i hz, rfl⟩).1 hK'
    hdisj := fun i i' hne => by
      dsimp only; rw [Set.disjoint_left]; rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, he⟩
      have h1 : Ks i z ∈ W_i i := hδi_W i ⟨z, hsub_rect i hz, rfl⟩
      have h2 : Ks i z ∈ W_i i' := by
        have : Ks i z = Ks i' w := by rw [← hjf i z hz, ← hjf i' w hw, he]
        rw [this]; exact hδi_W i' ⟨w, hsub_rect i' hw, rfl⟩
      exact Set.disjoint_left.mp (hW_disj hne) h1 h2
    hQ_eq := fun i z hz => by
      have := hδi_Q i z (hsub_rect i hz)
      rw [← hjf i z hz] at this
      exact ⟨fun h => this.mp ⟨f i z, h, rfl⟩, fun h => by
        obtain ⟨y, hy, hye⟩ := this.mpr h; exact hji hye ▸ hy⟩
    hQ_other := fun i i' hne => by
      rw [Set.disjoint_left]; rintro _ ⟨z, hz, rfl⟩ hxQ
      have hW := hδi_W i ⟨z, hsub_rect i hz, rfl⟩
      have hnot := (mem_iInter.mp (mem_iInter.mp hW.2 i') hne).1
      exact hnot ⟨f i z, hxQ, hjf i z hz⟩
    htip_closed := fun i => by
      have hmid_eq : f i '' (Ioo (a i) (b i) ×ℂ {0}) = p i '' Ioo (tL i) (tR i) := by
        ext x; constructor
        · rintro ⟨z, hz, rfl⟩
          rw [Complex.mem_reProdIm] at hz
          have hz_in : z ∈ Icc (a i) (b i) ×ℂ Icc (-δ) δ := Complex.mem_reProdIm.mpr
            ⟨Ioo_subset_Icc_self hz.1, by rw [mem_singleton_iff.mp hz.2]; exact ⟨by linarith, by linarith⟩⟩
          obtain ⟨t, ht_in, htx⟩ := intermediate_value_Icc (htLR i).le (hθc i).continuousOn (Ioo_subset_Icc_self hz.1)
          have hzeq : z = (θ i t : ℂ) := Complex.ext (by simp [htx]) (by simp [mem_singleton_iff.mp hz.2])
          have ht_oo : t ∈ Ioo (tL i) (tR i) := ⟨lt_of_le_of_ne ht_in.1 fun h => by rw [← h] at htx; exact hz.1.1.ne htx,
            lt_of_le_of_ne ht_in.2 fun h => by rw [h] at htx; exact hz.1.2.ne htx.symm⟩
          refine ⟨t, ht_oo, hji ?_⟩
          rw [hjf i z hz_in, hzeq, (hθ i t).2]
        · rintro ⟨t, ht, rfl⟩
          have hz_in : (θ i t : ℂ) ∈ Icc (a i) (b i) ×ℂ Icc (-δ) δ := Complex.mem_reProdIm.mpr
            ⟨⟨(hθm i ht.1).le, (hθm i ht.2).le⟩, by simp [hδ_pos.le]⟩
          refine ⟨(θ i t : ℂ), Complex.mem_reProdIm.mpr ⟨⟨hθm i ht.1, hθm i ht.2⟩, by simp⟩, hji ?_⟩
          rw [hjf i _ hz_in, (hθ i t).2]
      rw [hmid_eq]
      have hcomp_eq : Q i \ p i '' Ioo (tL i) (tR i) = p i '' {t : unitInterval | t.1 ≤ η i ∨ 1 - η i ≤ t.1} := by
        ext x; constructor
        · rintro ⟨hxQ, hxno⟩
          obtain ⟨t, rfl⟩ := hp_rng i ▸ hxQ
          refine ⟨t, ?_, rfl⟩
          by_contra h; change ¬ (t.1 ≤ η i ∨ 1 - η i ≤ t.1) at h; push Not at h
          exact hxno ⟨t, ⟨h.1, h.2⟩, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          refine ⟨hp_rng i ▸ mem_range_self t, ?_⟩
          rintro ⟨t', ht', he⟩
          have := (hp_arc i).2 he; subst this
          rcases ht with hle | hge
          · exact not_le_of_gt (show η i < t'.1 from ht'.1) hle
          · exact not_le_of_gt (show t'.1 < 1 - η i from ht'.2) hge
      rw [hcomp_eq]
      have hcpt : IsCompact {t : unitInterval | t.1 ≤ η i ∨ 1 - η i ≤ t.1} :=
        ((isClosed_le continuous_subtype_val continuous_const).union
          (isClosed_le continuous_const continuous_subtype_val)).isCompact
      exact (hcpt.image (hp_arc i).1).isClosed
  }, fun i => ?_⟩
  -- Show `Disjoint Z (tip i)`:
  have hmid_sub : p i '' Ioo (tL i) (tR i) ⊆ f i '' (Ioo (a i) (b i) ×ℂ {0}) := by
    rintro _ ⟨t, ht, rfl⟩
    have hz_in : (θ i t : ℂ) ∈ Icc (a i) (b i) ×ℂ Icc (-δ) δ := Complex.mem_reProdIm.mpr
      ⟨⟨(hθm i ht.1).le, (hθm i ht.2).le⟩, by simp [hδ_pos.le]⟩
    exact ⟨(θ i t : ℂ), Complex.mem_reProdIm.mpr ⟨⟨hθm i ht.1, hθm i ht.2⟩, by simp⟩, hji ((hjf i _ hz_in).trans (hθ i t).2)⟩
  refine (hηZ i).mono_right fun x hx => ?_
  obtain ⟨t, rfl⟩ := hp_rng i ▸ hx.1
  refine ⟨t, ?_, rfl⟩
  by_contra h; change ¬ (t.1 ≤ η i ∨ 1 - η i ≤ t.1) at h; push Not at h
  exact hx.2 (hmid_sub ⟨t, ⟨h.1, h.2⟩, rfl⟩)

end StripBoxSec

end GraphMinor.GHR18
