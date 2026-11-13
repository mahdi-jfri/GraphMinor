module

public import GraphMinor.GM22.Section8To13a
public import GraphMinor.GM22.Section8To13b
public import GraphMinor.GM22.Section8To13c2
public import GraphMinor.GM19.PlaneOrientation
public import GraphMinor.GM19.FragmentOrient
public import GraphMinor.GM16.CyclicOrderTransport

/-!
# Sphere Orientation, Corner Cyclic Order, and Rural Division Disc Drawing (`hyp_x`)

This file establishes the topological orientation and rural division disc-drawing ingredients for
deriving Graph Minors XIII, Theorem (10.2) from Graph Minors XXII, Theorem (8.3) (page 563):
- Construction of a surface orientation on `OnePoint EuclideanPlane` (`nonempty_sphereOrientation`).
- Equality `Set.univ \ r₀ = E₀` for the outer region `r₀ = interior (closure E₀ᶜ)` of the enclosed
  wall disc `E₀ = fig1Sph φ '' fig1EnclosedSet W.height`.
- Separation of the four wall corners on `C₀.U = discBd E₀` via the diagonal linear function
  `fig1DiagLine`, yielding a boundary circle homeomorphism `φ_C : Circle ≃ₜ C₀.U` under which the
  four corners `W.corner 0, W.corner 1, W.corner 2, W.corner 3` appear at strictly increasing angles
  `0 = a₀ < a₁ < a₂ < a₃ < 2π`.
- Selection of a sphere orientation `orient : GM19.SurfaceOrientation (OnePoint EuclideanPlane)`
  agreeing with `wallCornerCyclicPerm W` on `(Set.univ \ r₀, PiSet)`.
- Isomorphism between `divisionIncidenceGraph Z 𝒜_83` and `divisionBipartiteGraph S_H 𝒜`, and proof
  of Hypothesis (x) (`HasDiscDrawingWithBoundaryOrderInGraph`) from `hc.isRuralDivision`.
-/

@[expose] public section

namespace GraphMinor
namespace GM22

open Set Function Topology Graph Hypergraph
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM11
open GraphMinor.GM13
open GraphMinor.GM16

universe u v

/-! ## 1. Surface Orientation on `OnePoint EuclideanPlane` -/

/-- `OnePoint EuclideanPlane` admits a `GM19.SurfaceOrientation`. -/
theorem nonempty_sphereOrientation :
    Nonempty (GM19.SurfaceOrientation (OnePoint EuclideanPlane)) := by
  classical
  let c : EuclideanPlane → OnePoint EuclideanPlane := OnePoint.some
  have hc : Topology.IsOpenEmbedding c := OnePoint.isOpenEmbedding_coe
  let r : OnePoint EuclideanPlane → EuclideanPlane := Function.invFun c
  have hrc : ∀ x : EuclideanPlane, r (c x) = x := Function.leftInverse_invFun hc.injective
  have hrange : Set.range c = ({(OnePoint.infty : OnePoint EuclideanPlane)} : Set _)ᶜ := by
    ext p
    simp only [mem_range, mem_compl_iff, mem_singleton_iff]
    induction p using OnePoint.rec with
    | infty =>
      simp only [not_true_eq_false, iff_false, not_exists]
      intro x hx
      exact OnePoint.coe_ne_infty x hx
    | coe x =>
      exact ⟨fun _ => OnePoint.coe_ne_infty x, fun _ => ⟨x, rfl⟩⟩
  have hcr : ∀ p ∈ Set.range c, c (r p) = p := by
    rintro _ ⟨x, rfl⟩
    rw [hrc]
  have hrcont : ContinuousOn r (Set.range c) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous fun y : Set.range c => r y.1
    have heq : (fun y : Set.range c => r y.1) = hc.isEmbedding.toHomeomorph.symm := by
      funext y
      obtain ⟨_, x, rfl⟩ := y
      apply hc.isEmbedding.toHomeomorph.injective
      rw [Homeomorph.apply_symm_apply]
      exact Subtype.ext (hcr _ ⟨x, rfl⟩)
    rw [heq]
    exact Homeomorph.continuous _
  have hrinj : InjOn r (Set.range c) := by
    intro p₁ hp₁ p₂ hp₂ heq
    rw [← hcr p₁ hp₁, ← hcr p₂ hp₂, heq]
  let j : OnePoint EuclideanPlane → ℂ := fun p => complexPlane.symm (r p)
  have hj_pull : GM19.IsPartialOrientation
      {Δ : Set (OnePoint EuclideanPlane) | Δ ⊆ ({(OnePoint.infty : OnePoint EuclideanPlane)} : Set _)ᶜ}
      (GM19.pullPos j GM19.planeOrientation.pos) := by
    refine (GM19.planeOrientation.isPartial Set.univ).pull fun Δ hΔ => ?_
    have hΔ' : Δ ⊆ Set.range c := hrange.symm ▸ hΔ
    refine ⟨complexPlane.symm.continuous.comp_continuousOn (hrcont.mono hΔ'),
      complexPlane.symm.injective.comp_injOn (hrinj.mono hΔ'), mem_univ _⟩
  obtain ⟨ω, _⟩ := GM19.extend_orientation GM09.isClosedSurface_sphere
    (Set.finite_singleton (OnePoint.infty : OnePoint EuclideanPlane)) hj_pull
  exact ⟨ω⟩

/-! ## 2. `wallCornerCyclicPerm` as `cyclicPermOnSet` -/

/-- The equivalence `Fin 4 ≃ Set.range W.corner` given by `W.corner`. -/
noncomputable def wallCornerEquiv {α : Type u} {β : Type v} (W : Wall α β) :
    Fin 4 ≃ Set.range W.corner :=
  Equiv.ofInjective W.corner W.corner_injective

@[simp]
theorem wallCornerEquiv_apply_val {α : Type u} {β : Type v} (W : Wall α β) (i : Fin 4) :
    (wallCornerEquiv W i).1 = W.corner i :=
  rfl

/-- `wallCornerCyclicPerm W` coincides with `GM16.cyclicPermOnSet` for `wallCornerEquiv W`. -/
theorem wallCornerCyclicPerm_eq_cyclicPermOnSet {α : Type u} {β : Type v} (W : Wall α β) :
    wallCornerCyclicPerm W =
      GM16.cyclicPermOnSet (Set.finite_range W.corner) (wallCornerEquiv W) := by
  have h01 : W.corner 0 ≠ W.corner 1 := W.corner_injective.ne (by decide)
  have h02 : W.corner 0 ≠ W.corner 2 := W.corner_injective.ne (by decide)
  have h03 : W.corner 0 ≠ W.corner 3 := W.corner_injective.ne (by decide)
  have h12 : W.corner 1 ≠ W.corner 2 := W.corner_injective.ne (by decide)
  have h13 : W.corner 1 ≠ W.corner 3 := W.corner_injective.ne (by decide)
  have h23 : W.corner 2 ≠ W.corner 3 := W.corner_injective.ne (by decide)
  cases h1 : wallCornerCyclicPerm W with
  | mk bar₁ toFun₁ fin₁ bij₁ orb₁ =>
    cases h2 : GM16.cyclicPermOnSet (Set.finite_range W.corner) (wallCornerEquiv W) with
    | mk bar₂ toFun₂ fin₂ bij₂ orb₂ =>
      have hbar : bar₁ = bar₂ := by
        have hb1 : bar₁ = W.corners := congrArg CyclicPerm.bar h1.symm
        have hb2 : bar₂ = W.corners := congrArg CyclicPerm.bar h2.symm
        exact hb1.trans hb2.symm
      subst hbar
      congr 1
      funext x
      have hf1 : toFun₁ x = (wallCornerCyclicPerm W).toFun x :=
        congrFun (congrArg CyclicPerm.toFun h1.symm) x
      have hf2 : toFun₂ x =
          (GM16.cyclicPermOnSet (Set.finite_range W.corner) (wallCornerEquiv W)).toFun x :=
        congrFun (congrArg CyclicPerm.toFun h2.symm) x
      rw [hf1, hf2]
      by_cases hx : x ∈ Set.range W.corner
      · obtain ⟨i, rfl⟩ := hx
        have hstep :
            (GM16.cyclicPermOnSet (Set.finite_range W.corner) (wallCornerEquiv W)).toFun
              (wallCornerEquiv W i).1 =
              (wallCornerEquiv W (finRotate 4 i)).1 := by
          simp only [GM16.cyclicPermOnSet, Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta,
            Equiv.symm_apply_apply]
        rw [wallCornerEquiv_apply_val] at hstep
        rw [hstep, wallCornerEquiv_apply_val]
        fin_cases i <;>
          simp [wallCornerCyclicPerm,
            Ne.symm h01, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13, Ne.symm h23]
      · have hx0 : x ≠ W.corner 0 := fun h => hx ⟨0, h.symm⟩
        have hx1 : x ≠ W.corner 1 := fun h => hx ⟨1, h.symm⟩
        have hx2 : x ≠ W.corner 2 := fun h => hx ⟨2, h.symm⟩
        have hx3 : x ≠ W.corner 3 := fun h => hx ⟨3, h.symm⟩
        simp [wallCornerCyclicPerm, GM16.cyclicPermOnSet, Wall.corners, hx, hx0, hx1, hx2, hx3]

/-- Clockwise triples for `wallCornerCyclicPerm W` are characterized by `Fin 4` cyclic order. -/
theorem wallCornerCyclicPerm_isClockwise3_iff {α : Type u} {β : Type v} (W : Wall α β)
    (i j k : Fin 4) :
    (wallCornerCyclicPerm W).IsClockwise3 (W.corner i) (W.corner j) (W.corner k) ↔
      (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j) := by
  rw [wallCornerCyclicPerm_eq_cyclicPermOnSet W,
    ← wallCornerEquiv_apply_val W i, ← wallCornerEquiv_apply_val W j,
    ← wallCornerEquiv_apply_val W k,
    GM16.cyclicPermOnSet_clockwise3_iff (Set.finite_range W.corner) (wallCornerEquiv W) i j k,
    GM16.finCyclicPerm_clockwise3_iff]

/-- Lifting `IsClockwise3` along `liftCyclicPermInr`. -/
theorem liftCyclicPermInr_isClockwise3 {α : Type u} {γ : Type*} (Ω : CyclicPerm α)
    {a b c : α} (h : Ω.IsClockwise3 a b c) :
    (liftCyclicPermInr (γ := γ) Ω).IsClockwise3 (Sum.inr a) (Sum.inr b) (Sum.inr c) := by
  have hiter : ∀ (n : ℕ) (x : α),
      ((liftCyclicPermInr (γ := γ) Ω).toFun^[n]) (Sum.inr x) = Sum.inr ((Ω.toFun^[n]) x) := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rfl
  have hhit : ∀ (X : Set α) (x y : α),
      Ω.FirstHitIn X x y →
        (liftCyclicPermInr (γ := γ) Ω).FirstHitIn (Sum.inr '' X) (Sum.inr x) (Sum.inr y) := by
    rintro X x y ⟨n, hn, hyn, hyX, hmin⟩
    refine ⟨n, hn, by rw [hiter, hyn], ⟨y, hyX, rfl⟩, fun m hm1 hm2 => ?_⟩
    rw [hiter]
    rintro ⟨z, hzX, hzeq⟩
    exact hmin m hm1 hm2 (Sum.inr.inj hzeq ▸ hzX)
  have hset : ({(Sum.inr a : γ ⊕ α), Sum.inr b, Sum.inr c} : Set (γ ⊕ α)) =
      Sum.inr '' ({a, b, c} : Set α) := by
    rw [image_insert_eq, image_insert_eq, image_singleton]
  rw [CyclicPerm.isClockwise3_iff] at h ⊢
  rcases h with ⟨hab, hac, hbc, ha, hb, hc, h1, h2, h3⟩
  rw [hset]
  exact ⟨fun h => hab (Sum.inr.inj h), fun h => hac (Sum.inr.inj h), fun h => hbc (Sum.inr.inj h),
    ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ⟨c, hc, rfl⟩,
    hhit _ a b h1, hhit _ b c h2, hhit _ c a h3⟩

/-! ## 3. Complement of `r₀`, Diagonal Separator `fig1DiagLine`, and Corner Order on `C₀.U` -/

/-- For a closed disc `E₀` in `OnePoint EuclideanPlane` and `r₀ = interior (closure E₀ᶜ)`,
we have `Set.univ \ r₀ = E₀` and `discBd E₀ = subBd r₀`. -/
theorem univ_sdiff_interior_closure_compl_eq {E₀ : Set (OnePoint EuclideanPlane)}
    (hC : IsClosedDisc E₀) :
    Set.univ \ interior (closure E₀ᶜ) = E₀ := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hSph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  obtain ⟨hD, hBd, hCup, hMeet⟩ := GM16.isClosedDisc_closure_compl_of_isSphere hSph hC
  have hfr : frontier (closure E₀ᶜ) = discBd E₀ :=
    (GM11.IsClosedDisc.frontier_eq_discBd hS hD).trans hBd
  have hcl : closure (closure E₀ᶜ) = closure E₀ᶜ := closure_closure
  ext x
  simp only [mem_sdiff, mem_univ, true_and]
  constructor
  · intro hx_not_int
    rcases (hCup.ge (mem_univ x)) with hxE | hxD
    · exact hxE
    · have hx_fr : x ∈ frontier (closure E₀ᶜ) := ⟨hcl.symm ▸ hxD, hx_not_int⟩
      rw [hfr] at hx_fr
      exact Surface.discBd_subset E₀ hx_fr
  · intro hxE hx_int
    have hxD : x ∈ closure E₀ᶜ := interior_subset hx_int
    have hx_bd : x ∈ discBd E₀ := hMeet ▸ ⟨hxE, hxD⟩
    rw [← hfr] at hx_bd
    exact hx_bd.2 hx_int

/-- `fig1EnclosedSet h` is closed in `ℝ × ℝ`. -/
theorem isClosed_fig1EnclosedSet (h : ℕ) : IsClosed (fig1EnclosedSet h) := by
  unfold fig1EnclosedSet GM16.rectangleStack
  exact (Set.finite_lt_nat h).isClosed_biUnion fun k _ => isClosed_Icc.prod isClosed_Icc

/-- The diagonal line function `(2h - 1) y - h (x - 1)` through corners `0 = (1, 0)` and
`2 = (2h, h)`, separating corner `1 = (0, h)` from corner `3 = (2h + 1, 0)` along the perimeter of
`fig1EnclosedSet h`. -/
noncomputable def fig1DiagLine (h : ℕ) (z : ℝ × ℝ) : ℝ :=
  (2 * (h : ℝ) - 1) * z.2 - (h : ℝ) * (z.1 - 1)

theorem fig1DiagLine_corner0 (h : ℕ) :
    fig1DiagLine h (GM16.latticePoint (elementaryWallCorner h 0)) = 0 := by
  simp [fig1DiagLine, elementaryWallCorner, GM16.latticePoint]

theorem fig1DiagLine_corner2 (h : ℕ) :
    fig1DiagLine h (GM16.latticePoint (elementaryWallCorner h 2)) = 0 := by
  simp [fig1DiagLine, elementaryWallCorner, GM16.latticePoint]
  ring

theorem fig1DiagLine_corner1_pos {h : ℕ} (hh : 2 ≤ h) :
    0 < fig1DiagLine h (GM16.latticePoint (elementaryWallCorner h 1)) := by
  have hh' : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have heq : fig1DiagLine h (GM16.latticePoint (elementaryWallCorner h 1)) = 2 * (h : ℝ) ^ 2 := by
    simp [fig1DiagLine, elementaryWallCorner, GM16.latticePoint]
    ring
  rw [heq]
  nlinarith

theorem fig1DiagLine_corner3_neg {h : ℕ} (hh : 2 ≤ h) :
    fig1DiagLine h (GM16.latticePoint (elementaryWallCorner h 3)) < 0 := by
  have hh' : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have heq : fig1DiagLine h (GM16.latticePoint (elementaryWallCorner h 3)) = - (2 * (h : ℝ) ^ 2) := by
    simp [fig1DiagLine, elementaryWallCorner, GM16.latticePoint]
    ring
  rw [heq]
  nlinarith

/-- At every point `z ∈ frontier (fig1EnclosedSet h)` different from `(1, 0)` and `(2h, h)`,
`fig1DiagLine h z ≠ 0`. -/
theorem fig1DiagLine_ne_zero_of_mem_frontier {h : ℕ} (hh : 2 ≤ h) (he : Even h)
    {z : ℝ × ℝ} (hz : z ∈ frontier (fig1EnclosedSet h))
    (hne0 : z ≠ GM16.latticePoint (elementaryWallCorner h 0))
    (hne2 : z ≠ GM16.latticePoint (elementaryWallCorner h 2)) :
    fig1DiagLine h z ≠ 0 := by
  have hh1 : 1 ≤ h := by omega
  have hh' : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hcl : closure (fig1EnclosedSet h) = fig1EnclosedSet h :=
    (isClosed_fig1EnclosedSet h).closure_eq
  have hz_enc : z ∈ fig1EnclosedSet h := hcl ▸ hz.1
  have hz_not_int : z ∉ interior (fig1EnclosedSet h) := hz.2
  obtain ⟨hzx1, hzx2, hzy1, hzy2⟩ := mem_fig1EnclosedSet_bounds hz_enc
  rcases eq_or_lt_of_le hzy1 with hy0 | hy_pos
  · -- Case `z.2 = 0`
    have hzy0 : z.2 = 0 := hy0.symm
    obtain ⟨k, hk_lt, hkx, hk1, hk2⟩ := mem_iUnion₂.mp hz_enc
    have hk0 : k = 0 := by
      have hle0 : (k : ℝ) ≤ 0 := hzy0 ▸ hk1
      have hle0' : k ≤ 0 := by exact_mod_cast hle0
      omega
    subst hk0
    have hL0 : fig1RowLeft 0 = 1 := ite_eq_left (by decide)
    have hzx_ge1 : (1 : ℝ) ≤ z.1 := hL0 ▸ hkx.1
    have hzx_ne1 : z.1 ≠ 1 := by
      intro h1
      apply hne0
      ext <;> simp [elementaryWallCorner, GM16.latticePoint, h1, hzy0]
    have hzx_gt1 : (1 : ℝ) < z.1 := lt_of_le_of_ne hzx_ge1 (Ne.symm hzx_ne1)
    have hneg : fig1DiagLine h z < 0 := by
      unfold fig1DiagLine
      rw [hzy0]
      nlinarith
    exact ne_of_lt hneg
  · rcases eq_or_lt_of_le hzy2 with hyh | hy_lt
    · -- Case `z.2 = h`
      obtain ⟨k, hk_lt, hkx, hk1, hk2⟩ := mem_iUnion₂.mp hz_enc
      have hkh : k = h - 1 := by
        have hle : (h : ℝ) ≤ (k : ℝ) + 1 := hyh ▸ hk2
        have hle' : h ≤ k + 1 := by exact_mod_cast hle
        omega
      subst hkh
      have hodd : ¬ Even (h - 1) := by
        obtain ⟨m, rfl⟩ := he
        intro ⟨n, hn⟩
        omega
      have hR : fig1RowRight h (h - 1) = 2 * (h : ℝ) := by
        unfold fig1RowRight fig1RowLeft
        rw [ite_eq_right hodd]
        ring
      have hzx_le : z.1 ≤ 2 * (h : ℝ) := hR ▸ hkx.2
      have hzx_ne : z.1 ≠ 2 * (h : ℝ) := by
        intro h2
        apply hne2
        ext <;> simp [elementaryWallCorner, GM16.latticePoint, h2, hyh]
      have hzx_lt : z.1 < 2 * (h : ℝ) := lt_of_le_of_ne hzx_le hzx_ne
      have hpos : 0 < fig1DiagLine h z := by
        unfold fig1DiagLine
        rw [hyh]
        nlinarith
      exact ne_of_gt hpos
    · -- Case `0 < z.2 < h`
      have hnot_open : z.1 ∉ Ioo (1 : ℝ) (2 * (h : ℝ)) := by
        intro hzx_in
        exact hz_not_int (openInnerRect_subset_interior_fig1EnclosedSet hh1 ⟨hzx_in, hy_pos, hy_lt⟩)
      rcases le_or_gt z.1 1 with hzx_le1 | hzx_gt1
      · have hpos : 0 < fig1DiagLine h z := by
          unfold fig1DiagLine
          nlinarith
        exact ne_of_gt hpos
      · have hzx_ge2h : 2 * (h : ℝ) ≤ z.1 := by
          by_contra hlt
          exact hnot_open ⟨hzx_gt1, not_le.mp hlt⟩
        have hneg : fig1DiagLine h z < 0 := by
          unfold fig1DiagLine
          nlinarith
        exact ne_of_lt hneg

/-- For a Fig. 1 sphere drawing `Γ` of a wall `W` with perimeter circuit `C₀` (`C₀.U = discBd E₀`),
there exists a circle homeomorphism `φ_C : Circle ≃ₜ C₀.U` and strictly increasing angles
`a : Fin 4 → ℝ` (`0 = a 0 < a 1 < a 2 < a 3 < 2π`) such that
`(φ_C (Circle.exp (a k))).1 = fig1Sph φ (pos (W.toWall.corner k))` for all `k : Fin 4`. -/
theorem exists_corner_ordered_circleHomeo {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {C₀ : Drawing (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hC₀_U : C₀.U = discBd (fig1Sph φ '' fig1EnclosedSet W.height))
    (hp_C₀ : ∀ k : Fin 4, fig1Sph φ (pos (W.toWall.corner k)) ∈ C₀.U) :
    ∃ (φ_C : Circle ≃ₜ C₀.U) (a : Fin 4 → ℝ),
      a 0 = 0 ∧ a 0 < a 1 ∧ a 1 < a 2 ∧ a 2 < a 3 ∧ a 3 < 2 * Real.pi ∧
      ∀ k : Fin 4, (φ_C (Circle.exp (a k))).1 = fig1Sph φ (pos (W.toWall.corner k)) := by
  let E₀ := fig1Sph φ '' fig1EnclosedSet W.height
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hf_open : Topology.IsOpenEmbedding (fig1Sph φ) := isOpenEmbedding_fig1Sph φ
  have hf_emb : Topology.IsEmbedding (fig1Sph φ) := hf_open.isEmbedding
  have hh2 : 2 ≤ W.height := W.toWall.two_le_height
  have he : Even W.height := W.toWall.even_height
  have hC : IsClosedDisc E₀ := isClosedDisc_image_fig1EnclosedSet hS hf_emb (by omega)
  have hpos_corner : ∀ k : Fin 4,
      pos (W.toWall.corner k) = GM16.latticePoint (elementaryWallCorner W.height k) := by
    intro k
    exact hpos_branch (elementaryWallCorner W.height k) _
  let p : Fin 4 → OnePoint EuclideanPlane := fun k => fig1Sph φ (pos (W.toWall.corner k))
  have hp_inj : Function.Injective p := by
    intro i j hij
    have hcorner_W : ∀ k : Fin 4, W.toWall.corner k ∈ V(W.graph) :=
      fun k => W.toWall.perimeter_le.vertexSet_mono (corner_mem_perimeter W.toWall k)
    exact W.toWall.corner_injective (hinj (hcorner_W i) (hcorner_W j) (hf_open.injective hij))
  have hcl_enc : closure (fig1EnclosedSet W.height) = fig1EnclosedSet W.height :=
    (isClosed_fig1EnclosedSet W.height).closure_eq
  have hcl_E₀ : closure E₀ = E₀ := hC.isCompact.isClosed.closure_eq
  have hint_E₀ : interior E₀ = fig1Sph φ '' interior (fig1EnclosedSet W.height) :=
    interior_image_eq_of_isOpenEmbedding hf_open (fig1EnclosedSet W.height)
  have hdiscBd_E₀ : discBd E₀ = fig1Sph φ '' frontier (fig1EnclosedSet W.height) := by
    rw [← GM11.IsClosedDisc.frontier_eq_discBd hS hC, frontier, hcl_E₀, hint_E₀,
      frontier, hcl_enc]
    ext y
    simp only [E₀, mem_sdiff, mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hnot⟩
      exact ⟨x, ⟨hx, fun hx_int => hnot ⟨x, hx_int, rfl⟩⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hx_not_int⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro ⟨x', hx'_int, hx'_eq⟩
      exact hx_not_int (hf_open.injective hx'_eq ▸ hx'_int)
  obtain ⟨ψ₀₀⟩ := hC.isOArc_discBd
  let ψ₀ : Circle ≃ₜ C₀.U := ψ₀₀.trans (Homeomorph.setCongr hC₀_U.symm)
  let z₀ : Circle := ψ₀.symm ⟨p 0, hp_C₀ 0⟩
  let ψ₁ : Circle ≃ₜ C₀.U := (Homeomorph.mulLeft z₀).trans ψ₀
  have hψ₁_zero : (ψ₁ (Circle.exp 0)).1 = p 0 := by
    change (ψ₀ (z₀ * Circle.exp 0)).1 = p 0
    rw [Circle.exp_zero, mul_one, Homeomorph.apply_symm_apply]
  let w : Fin 4 → Circle := fun k => ψ₁.symm ⟨p k, hp_C₀ k⟩
  have hw_inj : Function.Injective w := fun i j hij =>
    hp_inj (congrArg Subtype.val (ψ₁.symm.injective hij))
  have hw0 : w 0 = 1 := by
    apply ψ₁.injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext (by simpa [Circle.exp_zero] using hψ₁_zero.symm)
  let θ : Fin 4 → ℝ := fun k => Circle.angleDiff 1 (w k)
  have hθ0 : θ 0 = 0 := by simp [θ, hw0, Circle.angleDiff]
  have hθ_bounds : ∀ k : Fin 4, k ≠ 0 → 0 < θ k ∧ θ k < 2 * Real.pi := by
    intro k hk
    have hne : (1 : Circle) ≠ w k := hw0 ▸ hw_inj.ne (Ne.symm hk)
    exact ⟨Circle.angleDiff_pos hne, Circle.angleDiff_lt_two_pi 1 (w k)⟩
  have hexp_θ : ∀ k : Fin 4, Circle.exp (θ k) = w k := by
    intro k
    simpa [θ] using Circle.exp_angleDiff_mul (x := 1) (y := w k)
  have hψ₁_θ : ∀ k : Fin 4, (ψ₁ (Circle.exp (θ k))).1 = p k := by
    intro k
    rw [hexp_θ k, Homeomorph.apply_symm_apply]
  have hθ_inj : Function.Injective θ := by
    intro i j hij
    exact hw_inj (by rw [← hexp_θ i, ← hexp_θ j, hij])
  -- Continuous pullback of `fig1DiagLine W.height` to `C₀.U`
  let f_fr : frontier (fig1EnclosedSet W.height) ≃ₜ discBd E₀ :=
    (hf_emb.homeomorphImage (frontier (fig1EnclosedSet W.height))).trans
      (Homeomorph.setCongr hdiscBd_E₀.symm)
  let g : ℝ → ℝ := fun t =>
    fig1DiagLine W.height (f_fr.symm ⟨(ψ₁ (Circle.exp t)).1, hC₀_U ▸ (ψ₁ (Circle.exp t)).2⟩).1
  have hg_cont : Continuous g := by
    have hdiag_cont : Continuous (fig1DiagLine W.height) := by
      unfold fig1DiagLine; fun_prop
    refine hdiag_cont.comp ?_
    exact continuous_subtype_val.comp (f_fr.symm.continuous.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp (ψ₁.continuous.comp Circle.exp.continuous)) _))
  have hf_fr_symm : ∀ (z : ℝ × ℝ) (hz : z ∈ frontier (fig1EnclosedSet W.height)),
      (f_fr.symm ⟨fig1Sph φ z, hdiscBd_E₀ ▸ ⟨z, hz, rfl⟩⟩).1 = z := by
    intro z hz
    have h1 : f_fr ⟨z, hz⟩ = ⟨fig1Sph φ z, hdiscBd_E₀ ▸ ⟨z, hz, rfl⟩⟩ := rfl
    rw [← h1, Homeomorph.symm_apply_apply]
  have hg_val : ∀ k : Fin 4,
      g (θ k) = fig1DiagLine W.height (GM16.latticePoint (elementaryWallCorner W.height k)) := by
    intro k
    dsimp [g]
    have hpk : p k ∈ discBd E₀ := hC₀_U ▸ hp_C₀ k
    have hmem_fr : pos (W.toWall.corner k) ∈ frontier (fig1EnclosedSet W.height) := by
      rw [hdiscBd_E₀] at hpk
      obtain ⟨z, hz, hzeq⟩ := hpk
      exact hf_open.injective hzeq ▸ hz
    have hsub : (⟨(ψ₁ (Circle.exp (θ k))).1, hC₀_U ▸ (ψ₁ (Circle.exp (θ k))).2⟩ : discBd E₀) =
        ⟨fig1Sph φ (pos (W.toWall.corner k)), hdiscBd_E₀ ▸ ⟨pos (W.toWall.corner k), hmem_fr, rfl⟩⟩ :=
      Subtype.ext (hψ₁_θ k)
    rw [hsub, hf_fr_symm (pos (W.toWall.corner k)) hmem_fr, hpos_corner k]
  have hg1_pos : 0 < g (θ 1) := by rw [hg_val 1]; exact fig1DiagLine_corner1_pos hh2
  have hg3_neg : g (θ 3) < 0 := by rw [hg_val 3]; exact fig1DiagLine_corner3_neg hh2
  have hg_ne_zero : ∀ t : ℝ, 0 < t → t < 2 * Real.pi → t ≠ θ 2 → g t ≠ 0 := by
    intro t ht_pos ht_lt hne_θ2
    let y : discBd E₀ := ⟨(ψ₁ (Circle.exp t)).1, hC₀_U ▸ (ψ₁ (Circle.exp t)).2⟩
    let z := (f_fr.symm y).1
    have hz_fr : z ∈ frontier (fig1EnclosedSet W.height) := (f_fr.symm y).2
    have hy_eq : fig1Sph φ z = (ψ₁ (Circle.exp t)).1 := by
      have : (f_fr (f_fr.symm y)).1 = y.1 := by rw [Homeomorph.apply_symm_apply]
      exact this
    have hne0 : z ≠ GM16.latticePoint (elementaryWallCorner W.height 0) := by
      intro hz0
      have hpt : (ψ₁ (Circle.exp t)).1 = (ψ₁ (Circle.exp 0)).1 := by
        rw [← hy_eq, hz0, ← hpos_corner 0, hψ₁_zero]
      have hexp : Circle.exp t = Circle.exp 0 := ψ₁.injective (Subtype.ext hpt)
      exact circle_exp_ne (ne_of_gt ht_pos)
        (by rw [sub_zero, abs_of_pos ht_pos]; exact ht_lt) hexp
    have hne2 : z ≠ GM16.latticePoint (elementaryWallCorner W.height 2) := by
      intro hz2
      have hpt : (ψ₁ (Circle.exp t)).1 = (ψ₁ (Circle.exp (θ 2))).1 := by
        rw [← hy_eq, hz2, ← hpos_corner 2, hψ₁_θ 2]
      have hexp : Circle.exp t = Circle.exp (θ 2) := ψ₁.injective (Subtype.ext hpt)
      have hb2 := hθ_bounds 2 (by decide)
      exact circle_exp_ne hne_θ2 (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩) hexp
    exact fig1DiagLine_ne_zero_of_mem_frontier hh2 he hz_fr hne0 hne2
  have hb1 := hθ_bounds 1 (by decide)
  have hb2 := hθ_bounds 2 (by decide)
  have hb3 := hθ_bounds 3 (by decide)
  have h12 : θ 1 ≠ θ 2 := hθ_inj.ne (by decide)
  have h23 : θ 2 ≠ θ 3 := hθ_inj.ne (by decide)
  have h13 : θ 1 ≠ θ 3 := hθ_inj.ne (by decide)
  -- Show `θ 2` lies strictly between `θ 1` and `θ 3`
  have h_between : (θ 1 < θ 2 ∧ θ 2 < θ 3) ∨ (θ 3 < θ 2 ∧ θ 2 < θ 1) := by
    by_contra hnot
    have h_same_side : (max (θ 1) (θ 3) < θ 2) ∨ (θ 2 < min (θ 1) (θ 3)) := by
      rcases lt_or_gt_of_ne h12 with h12_lt | h12_gt <;>
        rcases lt_or_gt_of_ne h23 with h23_lt | h23_gt
      · exact (hnot (Or.inl ⟨h12_lt, h23_lt⟩)).elim
      · exact Or.inl (max_lt h12_lt h23_gt)
      · exact Or.inr (lt_min h12_gt h23_lt)
      · exact (hnot (Or.inr ⟨h23_gt, h12_gt⟩)).elim
    have hmin_le_max : min (θ 1) (θ 3) ≤ max (θ 1) (θ 3) := min_le_max
    have h0_mem : (0 : ℝ) ∈ Icc (g (θ 3)) (g (θ 1)) := ⟨ le_of_lt hg3_neg, le_of_lt hg1_pos⟩
    obtain ⟨t, ht_Icc, hgt0⟩ : ∃ t ∈ Icc (min (θ 1) (θ 3)) (max (θ 1) (θ 3)), g t = 0 := by
      rcases lt_or_gt_of_ne h13 with h13_lt | h13_gt
      · rw [min_eq_left h13_lt.le, max_eq_right h13_lt.le]
        exact intermediate_value_Icc' h13_lt.le hg_cont.continuousOn h0_mem
      · rw [min_eq_right h13_gt.le, max_eq_left h13_gt.le]
        exact intermediate_value_Icc h13_gt.le hg_cont.continuousOn h0_mem
    have ht_pos : 0 < t := lt_of_lt_of_le (lt_min hb1.1 hb3.1) ht_Icc.1
    have ht_lt : t < 2 * Real.pi := lt_of_le_of_lt ht_Icc.2 (max_lt hb1.2 hb3.2)
    have ht_ne2 : t ≠ θ 2 := by
      rcases h_same_side with hgt | hlt
      · exact ne_of_lt (lt_of_le_of_lt ht_Icc.2 hgt)
      · exact ne_of_gt (lt_of_lt_of_le hlt ht_Icc.1)
    exact hg_ne_zero t ht_pos ht_lt ht_ne2 hgt0
  rcases h_between with ⟨h12_lt, h23_lt⟩ | ⟨h32_lt, h21_lt⟩
  · refine ⟨ψ₁, θ, hθ0, hθ0 ▸ hb1.1, h12_lt, h23_lt, hb3.2, hψ₁_θ⟩
  · let ψ₂ : Circle ≃ₜ C₀.U := (Homeomorph.inv Circle).trans ψ₁
    let a : Fin 4 → ℝ := fun k => if k = 0 then 0 else 2 * Real.pi - θ k
    refine ⟨ψ₂, a, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [a]; linarith [hb1.2]
    · dsimp [a]; linarith
    · dsimp [a]; linarith
    · dsimp [a]; linarith [hb3.1]
    · intro k
      fin_cases k
      · change (ψ₁ (Circle.exp 0)⁻¹).1 = p 0
        rw [Circle.exp_zero, inv_one, ← Circle.exp_zero]
        exact hψ₁_zero
      · change (ψ₁ (Circle.exp (2 * Real.pi - θ 1))⁻¹).1 = p 1
        rw [Circle.exp_sub, Circle.exp_two_pi, one_div, inv_inv]
        exact hψ₁_θ 1
      · change (ψ₁ (Circle.exp (2 * Real.pi - θ 2))⁻¹).1 = p 2
        rw [Circle.exp_sub, Circle.exp_two_pi, one_div, inv_inv]
        exact hψ₁_θ 2
      · change (ψ₁ (Circle.exp (2 * Real.pi - θ 3))⁻¹).1 = p 3
        rw [Circle.exp_sub, Circle.exp_two_pi, one_div, inv_inv]
        exact hψ₁_θ 3

/-- Increasing angles `0 ≤ t₁ < t₂ < t₃ < 2π` give `CircleCyclic (Circle.exp t₁) (Circle.exp t₂) (Circle.exp t₃)`
as well as all cyclic rotations. -/
theorem circleCyclic_of_increasing_angles {t₁ t₂ t₃ : ℝ}
    (ht0 : 0 ≤ t₁) (h12 : t₁ < t₂) (h23 : t₂ < t₃) (ht3 : t₃ < 2 * Real.pi) :
    CircleCyclic (Circle.exp t₁) (Circle.exp t₂) (Circle.exp t₃) ∧
    CircleCyclic (Circle.exp t₂) (Circle.exp t₃) (Circle.exp t₁) ∧
    CircleCyclic (Circle.exp t₃) (Circle.exp t₁) (Circle.exp t₂) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨t₂ - t₁, t₃ - t₁, by linarith, by linarith, by linarith, ?_, ?_⟩
    · rw [← Circle.exp_add, add_sub_cancel]
    · rw [← Circle.exp_add, add_sub_cancel]
  · refine ⟨t₃ - t₂, 2 * Real.pi + t₁ - t₂, by linarith, by linarith, by linarith, ?_, ?_⟩
    · rw [← Circle.exp_add, add_sub_cancel]
    · rw [← Circle.exp_add, show t₂ + (2 * Real.pi + t₁ - t₂) = 2 * Real.pi + t₁ by ring,
        Circle.exp_add, Circle.exp_two_pi, one_mul]
  · refine ⟨2 * Real.pi + t₁ - t₃, 2 * Real.pi + t₂ - t₃, by linarith, by linarith, by linarith, ?_, ?_⟩
    · rw [← Circle.exp_add, show t₃ + (2 * Real.pi + t₁ - t₃) = 2 * Real.pi + t₁ by ring,
        Circle.exp_add, Circle.exp_two_pi, one_mul]
    · rw [← Circle.exp_add, show t₃ + (2 * Real.pi + t₂ - t₃) = 2 * Real.pi + t₂ by ring,
        Circle.exp_add, Circle.exp_two_pi, one_mul]

/-- There exists a sphere orientation `orient : GM19.SurfaceOrientation (OnePoint EuclideanPlane)`
whose boundary direction on `Set.univ \ r₀ = E₀` agrees with `wallCornerCyclicPerm W.toWall` on the
four drawn corners `fig1Sph φ (pos (W.toWall.corner k))`. -/
theorem exists_sphere_orientation_for_wall {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {C₀ : Drawing (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hC₀_U : C₀.U = discBd (fig1Sph φ '' fig1EnclosedSet W.height))
    (hp_C₀ : ∀ k : Fin 4, fig1Sph φ (pos (W.toWall.corner k)) ∈ C₀.U) :
    let E₀ := fig1Sph φ '' fig1EnclosedSet W.height
    let r₀ := interior (closure E₀ᶜ)
    ∃ orient : GM19.SurfaceOrientation (OnePoint EuclideanPlane),
      ∀ i j k : Fin 4,
        (wallCornerCyclicPerm W.toWall).IsClockwise3
          (W.toWall.corner i) (W.toWall.corner j) (W.toWall.corner k) →
        orient.pos (Set.univ \ r₀)
          (fig1Sph φ (pos (W.toWall.corner i)))
          (fig1Sph φ (pos (W.toWall.corner j)))
          (fig1Sph φ (pos (W.toWall.corner k))) := by
  intro E₀ r₀
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hf_emb : Topology.IsEmbedding (fig1Sph φ) := (isOpenEmbedding_fig1Sph φ).isEmbedding
  have hh2 : 2 ≤ W.height := W.toWall.two_le_height
  have hC : IsClosedDisc E₀ := isClosedDisc_image_fig1EnclosedSet hS hf_emb (by omega)
  have huniv_sdiff : Set.univ \ r₀ = E₀ := univ_sdiff_interior_closure_compl_eq hC
  obtain ⟨φ_C, a, ha0, ha01, ha12, ha23, ha3, hφ_C_a⟩ :=
    exists_corner_ordered_circleHomeo hinj hpos_branch hC₀_U hp_C₀
  let φ_bd : Circle → OnePoint EuclideanPlane := fun z => (φ_C z).1
  have hφ_bd_cont : Continuous φ_bd := continuous_subtype_val.comp φ_C.continuous
  have hφ_bd_inj : Function.Injective φ_bd := Subtype.val_injective.comp φ_C.injective
  have hφ_bd_range : Set.range φ_bd = discBd E₀ := by
    rw [← hC₀_U]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (φ_C z).2
    · intro hx
      exact ⟨φ_C.symm ⟨x, hx⟩, by simp [φ_bd]⟩
  let r_C : OnePoint EuclideanPlane → OnePoint EuclideanPlane → OnePoint EuclideanPlane → Prop :=
    fun x y z => ∃ u v w : Circle, φ_bd u = x ∧ φ_bd v = y ∧ φ_bd w = z ∧ CircleCyclic u v w
  have hr_C_dir : GM19.IsDirectionOf (discBd E₀) r_C := by
    refine ⟨φ_bd, hφ_bd_cont, hφ_bd_inj, hφ_bd_range, fun u v w _ _ _ => ⟨?_, ?_⟩⟩
    · rintro ⟨u', v', w', hu, hv, hw, hcy⟩
      rwa [hφ_bd_inj hu, hφ_bd_inj hv, hφ_bd_inj hw] at hcy
    · intro hcy
      exact ⟨u, v, w, rfl, rfl, rfl, hcy⟩
  have hr_C_corners : ∀ i j k : Fin 4,
      (wallCornerCyclicPerm W.toWall).IsClockwise3
        (W.toWall.corner i) (W.toWall.corner j) (W.toWall.corner k) →
      r_C (fig1Sph φ (pos (W.toWall.corner i)))
        (fig1Sph φ (pos (W.toWall.corner j)))
        (fig1Sph φ (pos (W.toWall.corner k))) := by
    intro i j k hcw
    rw [wallCornerCyclicPerm_isClockwise3_iff] at hcw
    refine ⟨Circle.exp (a i), Circle.exp (a j), Circle.exp (a k),
      hφ_C_a i, hφ_C_a j, hφ_C_a k, ?_⟩
    have ha_nonneg : ∀ m : Fin 4, 0 ≤ a m := by
      intro m; fin_cases m <;> dsimp <;> linarith
    have ha_lt_two_pi : ∀ m : Fin 4, a m < 2 * Real.pi := by
      intro m; fin_cases m <;> dsimp <;> linarith
    have ha_mono : StrictMono a := by
      intro m₁ m₂ hm
      fin_cases m₁ <;> fin_cases m₂ <;> dsimp at hm ⊢ <;> first | omega | linarith
    rcases hcw with ⟨hij, hjk⟩ | ⟨hjk, hki⟩ | ⟨hki, hij⟩
    · exact (circleCyclic_of_increasing_angles (ha_nonneg i) (ha_mono hij) (ha_mono hjk)
        (ha_lt_two_pi k)).1
    · exact (circleCyclic_of_increasing_angles (ha_nonneg j) (ha_mono hjk) (ha_mono hki)
        (ha_lt_two_pi i)).2.2
    · exact (circleCyclic_of_increasing_angles (ha_nonneg k) (ha_mono hki) (ha_mono hij)
        (ha_lt_two_pi j)).2.1
  obtain ⟨ω₀⟩ := nonempty_sphereOrientation
  have hω₀_dir : GM19.IsDirectionOf (discBd E₀) (ω₀.pos E₀) := ω₀.isDirection E₀ hC
  have hp_bd : ∀ m : Fin 4, fig1Sph φ (pos (W.toWall.corner m)) ∈ discBd E₀ := by
    intro m
    rw [← hφ_bd_range]
    exact ⟨Circle.exp (a m), hφ_C_a m⟩
  have hp_inj : Function.Injective (fun m : Fin 4 => fig1Sph φ (pos (W.toWall.corner m))) := by
    intro m₁ m₂ hm
    have hcorner_W : ∀ k : Fin 4, W.toWall.corner k ∈ V(W.graph) :=
      fun k => W.toWall.perimeter_le.vertexSet_mono (corner_mem_perimeter W.toWall k)
    exact W.toWall.corner_injective (hinj (hcorner_W m₁) (hcorner_W m₂)
      ((isOpenEmbedding_fig1Sph φ).injective hm))
  rcases hr_C_dir.same_or_reverse hω₀_dir with hsame | hrev
  · refine ⟨ω₀, fun i j k hcw => ?_⟩
    rw [huniv_sdiff]
    have hne := (CyclicPerm.isClockwise3_iff.mp hcw)
    have hij : i ≠ j := fun h => hne.1 (congrArg W.toWall.corner h)
    have hik : i ≠ k := fun h => hne.2.1 (congrArg W.toWall.corner h)
    have hjk : j ≠ k := fun h => hne.2.2.1 (congrArg W.toWall.corner h)
    exact (hsame _ _ _ (hp_bd i) (hp_bd j) (hp_bd k)
      (hp_inj.ne hij) (hp_inj.ne hjk) (hp_inj.ne hik)).mp (hr_C_corners i j k hcw)
  · refine ⟨GM19.orientationOfPartial (ω₀.isPartial Set.univ).rev, fun i j k hcw => ?_⟩
    rw [huniv_sdiff]
    have hne := (CyclicPerm.isClockwise3_iff.mp hcw)
    have hij : i ≠ j := fun h => hne.1 (congrArg W.toWall.corner h)
    have hik : i ≠ k := fun h => hne.2.1 (congrArg W.toWall.corner h)
    have hjk : j ≠ k := fun h => hne.2.2.1 (congrArg W.toWall.corner h)
    change ω₀.pos E₀ (fig1Sph φ (pos (W.toWall.corner i)))
      (fig1Sph φ (pos (W.toWall.corner k))) (fig1Sph φ (pos (W.toWall.corner j)))
    exact (hrev _ _ _ (hp_bd i) (hp_bd j) (hp_bd k)
      (hp_inj.ne hij) (hp_inj.ne hjk) (hp_inj.ne hik)).mp (hr_C_corners i j k hcw)

/-! ## 4. Rural Division and `HasDiscDrawingWithBoundaryOrderInGraph` (`hyp_x`) -/

/-- Under `HypothesisC G q X H S_H 𝒜` and `vis : Vision G X H S_H 𝒜`, the GM22 incidence graph
`divisionIncidenceGraph Z 𝒜_83` (where `Z = divTotalBoundary S_H 𝒜` and
`𝒜_83 = (fun A => (vis.tildeA A).toGraph) '' 𝒜`) is isomorphic to the GM13 bipartite graph
`divisionBipartiteGraph S_H 𝒜`. -/
noncomputable def divisionIncidenceBipartiteIso {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜) :
    let Z := divTotalBoundary S_H 𝒜
    let 𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜
    Iso (divisionIncidenceGraph Z 𝒜_83) (divisionBipartiteGraph S_H 𝒜) := by
  intro Z 𝒜_83
  let G₁ := divisionIncidenceGraph Z 𝒜_83
  let G₂ := divisionBipartiteGraph S_H 𝒜
  have hbar_sub_Z : S_H.Ω.bar ⊆ Z := by
    rw [hc.isWallSociety.2]
    exact corners_subset_divTotalBoundary hc
  have hZ_union : divTotalBoundary S_H 𝒜 ∪ S_H.Ω.bar = Z :=
    union_eq_self_of_subset_right hbar_sub_Z
  let fV : α ⊕ Graph α β → Graph α β ⊕ α := fun x =>
    match x with
    | Sum.inl z => Sum.inr z
    | Sum.inr tA => Sum.inl (tA.deleteVerts X)
  have hfV_mem : ∀ x ∈ V(G₁), fV x ∈ V(G₂) := by
    rintro (z | tA) (⟨z₀, hz₀, h⟩ | ⟨_, ⟨A, hA, rfl⟩, h⟩)
    · obtain rfl := Sum.inl.inj h
      exact Or.inr ⟨z₀, Or.inl hz₀, rfl⟩
    · cases h
    · cases h
    · obtain rfl := Sum.inr.inj h
      dsimp [fV]
      rw [(tildeA_properties hc vis hA).2.1]
      exact Or.inl ⟨A, hA, rfl⟩
  have hfV_inj : InjOn fV V(G₁) := by
    rintro (z₁ | tA₁) h₁ (z₂ | tA₂) h₂ heq
    ·exact congrArg Sum.inl (Sum.inr.inj heq)
    · cases heq
    · cases heq
    · obtain (⟨_, _, h⟩ | ⟨_, ⟨A₁, hA₁, rfl⟩, h⟩) := h₁
      · cases h
      obtain rfl := Sum.inr.inj h
      obtain (⟨_, _, h'⟩ | ⟨_, ⟨A₂, hA₂, rfl⟩, h'⟩) := h₂
      · cases h'
      obtain rfl := Sum.inr.inj h'
      dsimp [fV] at heq
      have hA_eq : A₁ = A₂ := by
        have hdel := Sum.inl.inj heq
        rwa [(tildeA_properties hc vis hA₁).2.1, (tildeA_properties hc vis hA₂).2.1] at hdel
      subst hA_eq
      rfl
  have hfV_surj : ∀ y ∈ V(G₂), ∃ x ∈ V(G₁), fV x = y := by
    rintro _ (⟨A, hA, rfl⟩ | ⟨z, hz, rfl⟩)
    · refine ⟨Sum.inr (vis.tildeA A).toGraph, Or.inr ⟨_, ⟨A, hA, rfl⟩, rfl⟩, ?_⟩
      dsimp [fV]
      rw [(tildeA_properties hc vis hA).2.1]
    · have hzZ : z ∈ Z := hZ_union ▸ hz
      exact ⟨Sum.inl z, Or.inl ⟨z, hzZ, rfl⟩, rfl⟩
  let eV : V(G₁) ≃ V(G₂) :=
    Equiv.ofBijective (fun x => ⟨fV x.1, hfV_mem x.1 x.2⟩)
      ⟨fun x₁ x₂ h => Subtype.ext (hfV_inj x₁.2 x₂.2 (congrArg Subtype.val h)),
       fun y => by
         obtain ⟨x, hx, heq⟩ := hfV_surj y.1 y.2
         exact ⟨⟨x, hx⟩, Subtype.ext heq⟩⟩
  let fE : α × Graph α β → Graph α β × α := fun p => (p.2.deleteVerts X, p.1)
  have hfE_mem : ∀ p ∈ E(G₁), fE p ∈ E(G₂) := by
    rintro ⟨z, tA⟩ ⟨hz, ⟨A, hA, htA_eq⟩, hztA⟩
    dsimp only at hz htA_eq hztA
    subst htA_eq
    obtain ⟨_, hdel_eq, _, hZA⟩ := tildeA_properties hc vis hA
    have hz_bd : z ∈ divBoundary S_H A := hZA ▸ ⟨hz, hztA⟩
    dsimp [fE, G₂, divisionBipartiteGraph]
    rw [hdel_eq]
    exact ⟨hA, hz_bd⟩
  have hfE_inj : InjOn fE E(G₁) := by
    rintro ⟨z₁, tA₁⟩ ⟨_, ⟨A₁, hA₁, htA₁_eq⟩, _⟩ ⟨z₂, tA₂⟩ ⟨_, ⟨A₂, hA₂, htA₂_eq⟩, _⟩ heq
    dsimp only at htA₁_eq htA₂_eq
    subst htA₁_eq htA₂_eq
    have hz : z₁ = z₂ := congrArg Prod.snd heq
    have hA : A₁ = A₂ := by
      have hdel := congrArg Prod.fst heq
      dsimp [fE] at hdel
      rwa [(tildeA_properties hc vis hA₁).2.1, (tildeA_properties hc vis hA₂).2.1] at hdel
    subst hz hA
    rfl
  have hfE_surj : ∀ q ∈ E(G₂), ∃ p ∈ E(G₁), fE p = q := by
    rintro ⟨A, z⟩ ⟨hA, hz_bd⟩
    obtain ⟨_, hdel_eq, _, hZA⟩ := tildeA_properties hc vis hA
    have hz_inter : z ∈ Z ∩ V((vis.tildeA A).toGraph) := hZA.symm ▸ hz_bd
    refine ⟨(z, (vis.tildeA A).toGraph), ⟨hz_inter.1, ⟨A, hA, rfl⟩, hz_inter.2⟩, ?_⟩
    dsimp [fE]
    rw [hdel_eq]
  let eE : E(G₁) ≃ E(G₂) :=
    Equiv.ofBijective (fun p => ⟨fE p.1, hfE_mem p.1 p.2⟩)
      ⟨fun p₁ p₂ h => Subtype.ext (hfE_inj p₁.2 p₂.2 (congrArg Subtype.val h)),
       fun q => by
         obtain ⟨p, hp, heq⟩ := hfE_surj q.1 q.2
         exact ⟨⟨p, hp⟩, Subtype.ext heq⟩⟩
  refine
    { vertexEquiv := eV
      edgeEquiv := eE
      isLink_iff := fun p x y => ?_ }
  rcases p with ⟨⟨z, tA⟩, hp_mem⟩
  rcases hp_mem with ⟨hz, ⟨A, hA, htA_eq⟩, hztA⟩
  dsimp only at hz htA_eq hztA
  subst htA_eq
  obtain ⟨_, hdel_eq, _, hZA⟩ := tildeA_properties hc vis hA
  have hz_bd : z ∈ divBoundary S_H A := hZA ▸ ⟨hz, hztA⟩
  change G₁.IsLink (z, (vis.tildeA A).toGraph) x.1 y.1 ↔
    G₂.IsLink ((vis.tildeA A).toGraph.deleteVerts X, z) (fV x.1) (fV y.1)
  rw [hdel_eq]
  dsimp [G₁, G₂, divisionIncidenceGraph, divisionBipartiteGraph]
  have hx_inl : fV x.1 = Sum.inr z ↔ x.1 = Sum.inl z := by
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    have hx_mem : Sum.inl z ∈ V(G₁) := Or.inl ⟨z, hz, rfl⟩
    exact hfV_inj x.2 hx_mem h
  have hy_inl : fV y.1 = Sum.inr z ↔ y.1 = Sum.inl z := by
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    have hy_mem : Sum.inl z ∈ V(G₁) := Or.inl ⟨z, hz, rfl⟩
    exact hfV_inj y.2 hy_mem h
  have hx_inr : fV x.1 = Sum.inl A ↔ x.1 = Sum.inr (vis.tildeA A).toGraph := by
    refine ⟨fun h => ?_, fun h => by rw [h]; dsimp [fV]; rw [hdel_eq]⟩
    have hx_mem : Sum.inr (vis.tildeA A).toGraph ∈ V(G₁) := Or.inr ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    refine hfV_inj x.2 hx_mem ?_
    rw [h]
    dsimp [fV]
    rw [hdel_eq]
  have hy_inr : fV y.1 = Sum.inl A ↔ y.1 = Sum.inr (vis.tildeA A).toGraph := by
    refine ⟨fun h => ?_, fun h => by rw [h]; dsimp [fV]; rw [hdel_eq]⟩
    have hy_mem : Sum.inr (vis.tildeA A).toGraph ∈ V(G₁) := Or.inr ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    refine hfV_inj y.2 hy_mem ?_
    rw [h]
    dsimp [fV]
    rw [hdel_eq]
  rw [hx_inl, hy_inl, hx_inr, hy_inr]
  have htA_mem : (vis.tildeA A).toGraph ∈ 𝒜_83 := ⟨A, hA, rfl⟩
  tauto

/-- Two strictly increasing 4-tuples of real numbers with the same underlying 4-element set are
pointwise equal. -/
theorem eq_of_strictMono_four_of_set_eq {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℝ}
    (ha12 : a₁ < a₂) (ha23 : a₂ < a₃) (ha34 : a₃ < a₄)
    (hb12 : b₁ < b₂) (hb23 : b₂ < b₃) (hb34 : b₃ < b₄)
    (hset : ({a₁, a₂, a₃, a₄} : Set ℝ) = {b₁, b₂, b₃, b₄}) :
    a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ ∧ a₄ = b₄ := by
  have ha_mem : ∀ x ∈ ({a₁, a₂, a₃, a₄} : Set ℝ), x = b₁ ∨ x = b₂ ∨ x = b₃ ∨ x = b₄ := by
    intro x hx; rw [hset] at hx; simpa using hx
  have hb_mem : ∀ x ∈ ({b₁, b₂, b₃, b₄} : Set ℝ), x = a₁ ∨ x = a₂ ∨ x = a₃ ∨ x = a₄ := by
    intro x hx; rw [← hset] at hx; simpa using hx
  have h1 : a₁ = b₁ := by
    have ha1 := ha_mem a₁ (by simp)
    have hb1 := hb_mem b₁ (by simp)
    rcases ha1 with rfl | rfl | rfl | rfl <;> rcases hb1 with h | h | h | h <;> linarith
  have h4 : a₄ = b₄ := by
    have ha4 := ha_mem a₄ (by simp)
    have hb4 := hb_mem b₄ (by simp)
    rcases ha4 with rfl | rfl | rfl | rfl <;> rcases hb4 with h | h | h | h <;> linarith
  have h2 : a₂ = b₂ := by
    have ha2 := ha_mem a₂ (by simp)
    have hb2 := hb_mem b₂ (by simp)
    rcases ha2 with h | rfl | rfl | h <;> rcases hb2 with h' | h' | h' | h' <;> linarith
  have h3 : a₃ = b₃ := by
    have ha3 := ha_mem a₃ (by simp)
    have hb3 := hb_mem b₃ (by simp)
    rcases ha3 with h | h | rfl | h <;> rcases hb3 with h' | h' | h' | h' <;> linarith
  exact ⟨h1, h2, h3, h4⟩

/-- Under `HypothesisC G q X H S_H 𝒜` and `vis : Vision G X H S_H 𝒜`, Hypothesis (x) of
Theorem (8.3) (`HasDiscDrawingWithBoundaryOrderInGraph`) holds for `Z := divTotalBoundary S_H 𝒜`
and `𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜`. -/
theorem tildeA_hyp_x {α : Type u} {β : Type v} [Nonempty α]
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜)
    {W : DrawnWall α β} (hW_toWall : W.toWall = H)
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    {C₀ : Drawing (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hC₀_U : C₀.U = discBd (fig1Sph φ '' fig1EnclosedSet W.height))
    (hmem_V : ∀ v ∈ V(W.graph), fig1Sph φ (pos v) ∈ C₀.V ↔ v ∈ V(W.perimeter)) :
    HasDiscDrawingWithBoundaryOrderInGraph (drawingVertToGraph Γ) C₀
      (wallPiSet H φ pos) (divTotalBoundary S_H 𝒜)
      ((fun A => (vis.tildeA A).toGraph) '' 𝒜) := by
  subst hW_toWall
  let Z := divTotalBoundary S_H 𝒜
  let 𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜
  obtain ⟨hPi_sub, _, hdraw_corner, _⟩ := wallPiSet_props hinj hΓv hmem_V
  obtain ⟨φ_C, a, ha0, ha01, ha12, ha23, ha3, hφ_C_a⟩ :=
    exists_corner_ordered_circleHomeo hinj hpos_branch hC₀_U
      (fun k => C₀.V_subset_U (hPi_sub ⟨k, rfl⟩))
  obtain ⟨hV_bip, hE_bip, hbar_bip, hrural_bip⟩ := hc.isRuralDivision.isRuralBipartite
  let S_bip : Society (Graph α β ⊕ α) (Graph α β × α) :=
    Society.mk (divisionBipartiteGraph S_H 𝒜) (liftCyclicPermInr S_H.Ω) hV_bip hE_bip hbar_bip
  obtain ⟨Γ_bip, Δ, φ_D₀, hΔ, _, hU_Δ, _, hbd_bip, hagrees⟩ :=
    GM13.exists_clean_disc_drawing_of_isRuralSociety S_bip hrural_bip
  let iso₀ := divisionIncidenceBipartiteIso hc vis
  let gd : GraphDrawing (divisionIncidenceGraph Z 𝒜_83) EuclideanPlane :=
    { drawing := Γ_bip.drawing
      iso :=
        { vertexEquiv := iso₀.vertexEquiv.trans Γ_bip.iso.vertexEquiv
          edgeEquiv := iso₀.edgeEquiv.trans Γ_bip.iso.edgeEquiv
          isLink_iff := fun e x y =>
            (iso₀.isLink_iff e x y).trans
              (Γ_bip.iso.isLink_iff (iso₀.edgeEquiv e) (iso₀.vertexEquiv x) (iso₀.vertexEquiv y)) } }
  have hbar_eq : S_H.Ω.bar = W.toWall.corners := by
    rw [hc.isWallSociety.2]; rfl
  have hcorner_Z : ∀ k : Fin 4, W.toWall.corner k ∈ Z :=
    fun k => corners_subset_divTotalBoundary hc ⟨k, rfl⟩
  have hcorner_G1 : ∀ k : Fin 4,
      Sum.inl (W.toWall.corner k) ∈ V(divisionIncidenceGraph Z 𝒜_83) :=
    fun k => Or.inl ⟨W.toWall.corner k, hcorner_Z k, rfl⟩
  have hcorner_G2 : ∀ k : Fin 4,
      Sum.inr (W.toWall.corner k) ∈ V(divisionBipartiteGraph S_H 𝒜) :=
    fun k => Or.inr ⟨W.toWall.corner k, Or.inl (hcorner_Z k), rfl⟩
  let d : Fin 4 → EuclideanPlane := fun k =>
    (gd.iso.vertexEquiv ⟨Sum.inl (W.toWall.corner k), hcorner_G1 k⟩).1
  have hd_eq_bip : ∀ k : Fin 4,
      d k = (Γ_bip.iso.vertexEquiv ⟨Sum.inr (W.toWall.corner k), hcorner_G2 k⟩).1 :=
    fun _ => rfl
  have hd_mem_vset : ∀ k : Fin 4,
      d k ∈ graphDrawingVertexSet Γ_bip (Sum.inr (W.toWall.corner k)) := by
    intro k
    rw [GM13.graphDrawingVertexSet_eq_singleton Γ_bip (hcorner_G2 k), hd_eq_bip k]
    rfl
  have hd_bd : ∀ k : Fin 4, d k ∈ subBd Δ := by
    intro k
    have hbar_k : (Sum.inr (W.toWall.corner k) : Graph α β ⊕ α) ∈ (liftCyclicPermInr S_H.Ω).bar :=
      ⟨W.toWall.corner k, hbar_eq ▸ ⟨k, rfl⟩, rfl⟩
    exact (hbd_bip _ (hcorner_G2 k)).mpr hbar_k (hd_mem_vset k)
  let zd₀ : Circle := φ_D₀.symm ⟨d 0, hd_bd 0⟩
  let φ_D : Circle ≃ₜ subBd Δ := (Homeomorph.mulLeft zd₀).trans φ_D₀
  let wd : Fin 4 → Circle := fun k => φ_D.symm ⟨d k, hd_bd k⟩
  have hwd0 : wd 0 = 1 := by
    apply φ_D.injective
    rw [Homeomorph.apply_symm_apply]
    exact (Homeomorph.apply_symm_apply φ_D₀ ⟨d 0, hd_bd 0⟩).symm.trans (by
      change φ_D₀ zd₀ = φ_D₀ (zd₀ * 1); rw [mul_one])
  have hφ_D₀_wd : ∀ k : Fin 4, (φ_D₀ (zd₀ * wd k)).1 = d k := by
    intro k
    change (φ_D (wd k)).1 = d k
    rw [Homeomorph.apply_symm_apply]
  let b : Fin 4 → ℝ := fun k => Circle.angleDiff 1 (wd k)
  have hb0 : b 0 = 0 := by simp [b, hwd0, Circle.angleDiff]
  have hexp_b : ∀ k : Fin 4, Circle.exp (b k) = wd k := by
    intro k
    simpa [b] using Circle.exp_angleDiff_mul (x := 1) (y := wd k)
  have hφ_D_b : ∀ k : Fin 4, (φ_D (Circle.exp (b k))).1 = d k := by
    intro k
    rw [hexp_b k, Homeomorph.apply_symm_apply]
  have hangleDiff_mulLeft : ∀ x y : Circle, (zd₀ * x).angleDiff (zd₀ * y) = x.angleDiff y := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp [Circle.angleDiff]
    · have hpos : 0 < x.angleDiff y := Circle.angleDiff_pos hxy
      have hlt : x.angleDiff y < 2 * Real.pi := Circle.angleDiff_lt_two_pi x y
      have hmul : Circle.exp (x.angleDiff y) * (zd₀ * x) = zd₀ * y := by
        rw [← mul_left_comm zd₀, Circle.exp_angleDiff_mul]
      rw [← hmul, angleDiff_exp_mul hpos hlt]
  have hb_cw : ∀ j k : Fin 4, 0 < j → j < k → b j < b k := by
    intro j k hj hjk
    have hcw_W : (wallCornerCyclicPerm W.toWall).IsClockwise3
        (W.toWall.corner 0) (W.toWall.corner j) (W.toWall.corner k) :=
      (wallCornerCyclicPerm_isClockwise3_iff W.toWall 0 j k).mpr (Or.inl ⟨hj, hjk⟩)
    have hcw_S : S_H.Ω.IsClockwise3
        (W.toWall.corner 0) (W.toWall.corner j) (W.toWall.corner k) := by
      rwa [hc.isWallSociety.2]
    have hcw_lift : (liftCyclicPermInr (γ := Graph α β) S_H.Ω).IsClockwise3
        (Sum.inr (W.toWall.corner 0)) (Sum.inr (W.toWall.corner j)) (Sum.inr (W.toWall.corner k)) :=
      liftCyclicPermInr_isClockwise3 S_H.Ω hcw_S
    have hlt := GM09.angleDiff_lt_of_isClockwise3 hagrees hcw_lift
      (by rw [hφ_D₀_wd 0]; exact hd_mem_vset 0)
      (by rw [hφ_D₀_wd j]; exact hd_mem_vset j)
      (by rw [hφ_D₀_wd k]; exact hd_mem_vset k)
    rwa [hangleDiff_mulLeft, hangleDiff_mulLeft, hwd0] at hlt
  have hb01 : b 0 < b 1 := by
    rw [hb0]
    have hd_ne : d 0 ≠ d 1 := by
      intro h
      have hsub := Γ_bip.iso.vertexEquiv.injective (Subtype.ext (hd_eq_bip 0 ▸ hd_eq_bip 1 ▸ h))
      have h01 : (0 : Fin 4) = 1 :=
        W.toWall.corner_injective (Sum.inr.inj (congrArg Subtype.val hsub))
      exact absurd h01 (by decide)
    have hwd_ne : wd 1 ≠ 1 := fun h => hd_ne (by rw [← hφ_D_b 0, ← hφ_D_b 1, hb0, Circle.exp_zero, ← h, hexp_b 1])
    exact Circle.angleDiff_pos (Ne.symm hwd_ne)
  have hb12 : b 1 < b 2 := hb_cw 1 2 (by decide) (by decide)
  have hb23 : b 2 < b 3 := hb_cw 2 3 (by decide) (by decide)
  have hb3_lt : b 3 < 2 * Real.pi := Circle.angleDiff_lt_two_pi 1 (wd 3)
  refine ⟨Δ, gd, φ_C, φ_D, hΔ, hU_Δ, ?_, ?_, ?_⟩
  · rintro _ ⟨k, rfl⟩
    rw [hdraw_corner k]
    exact ⟨hcorner_G1 k, hd_bd k⟩
  · intro v
    have hv_bip : (iso₀.vertexEquiv v).1 ∈ V(divisionBipartiteGraph S_H 𝒜) := (iso₀.vertexEquiv v).2
    have hbd_iff := hbd_bip (iso₀.vertexEquiv v).1 hv_bip
    rw [GM13.graphDrawingVertexSet_eq_singleton Γ_bip hv_bip, singleton_subset_iff] at hbd_iff
    change (Γ_bip.iso.vertexEquiv (iso₀.vertexEquiv v)).1 ∈ subBd Δ ↔ _
    rw [hbd_iff]
    constructor
    · rintro ⟨c, hc_bar, hceq⟩
      rw [hbar_eq] at hc_bar
      obtain ⟨k, rfl⟩ := hc_bar
      refine ⟨fig1Sph φ (pos (W.toWall.corner k)), ⟨k, rfl⟩, ?_⟩
      rw [hdraw_corner k]
      rcases v with ⟨z | tA, hv_mem⟩
      · exact congrArg Sum.inl (Sum.inr.inj hceq.symm)
      · cases hceq
    · rintro ⟨_, ⟨k, rfl⟩, hveq⟩
      rw [hdraw_corner k] at hveq
      have hveq' : (iso₀.vertexEquiv v).1 = Sum.inr (W.toWall.corner k) := by
        rcases v with ⟨x, hv_mem⟩
        subst hveq
        rfl
      rw [hveq']
      exact ⟨W.toWall.corner k, hbar_eq.symm ▸ ⟨k, rfl⟩, rfl⟩
  · intro t₁ t₂ t₃ t₄ p₁ p₂ p₃ p₄ ht₁ ht₂ ht₃ ht₄ ht₅ hPi_eq hc₁ hc₂ hc₃ hc₄
    -- Show `{t₁, t₂, t₃, t₄} = {a 0, a 1, a 2, a 3}`
    have hexp_inj_Ico : InjOn Circle.exp (Ico 0 (2 * Real.pi)) := by
      intro x hx y hy hxy
      by_contra hne
      exact circle_exp_ne hne
        (abs_sub_lt_iff.mpr ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1]⟩) hxy
    have hset_t_a : ({t₁, t₂, t₃, t₄} : Set ℝ) = {a 0, a 1, a 2, a 3} := by
      have hsub_t : ({t₁, t₂, t₃, t₄} : Set ℝ) ⊆ Ico 0 (2 * Real.pi) := by
        rintro x (rfl | rfl | rfl | rfl) <;> exact ⟨by linarith, by linarith⟩
      have hsub_a : ({a 0, a 1, a 2, a 3} : Set ℝ) ⊆ Ico 0 (2 * Real.pi) := by
        rintro x (rfl | rfl | rfl | rfl) <;> exact ⟨by linarith, by linarith⟩
      have himg_eq : (fun t => (φ_C (Circle.exp t)).1) '' {t₁, t₂, t₃, t₄} =
          (fun t => (φ_C (Circle.exp t)).1) '' {a 0, a 1, a 2, a 3} := by
        simp only [image_insert_eq, image_singleton, hc₁, hc₂, hc₃, hc₄,
          hφ_C_a 0, hφ_C_a 1, hφ_C_a 2, hφ_C_a 3, ← hPi_eq]
        ext x
        simp only [wallPiSet, mem_range, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨k, rfl⟩
          fin_cases k <;> tauto
        · rintro (rfl | rfl | rfl | rfl)
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨3, rfl⟩
      have hinj_comp : InjOn (fun t => (φ_C (Circle.exp t)).1) (Ico 0 (2 * Real.pi)) :=
        (Subtype.val_injective.comp φ_C.injective).comp_injOn hexp_inj_Ico
      ext x
      constructor
      · intro hx
        have hfx : (φ_C (Circle.exp x)).1 ∈
            (fun t => (φ_C (Circle.exp t)).1) '' {a 0, a 1, a 2, a 3} :=
          himg_eq ▸ ⟨x, hx, rfl⟩
        obtain ⟨y, hy, hyx⟩ := hfx
        exact hinj_comp (hsub_a hy) (hsub_t hx) hyx ▸ hy
      · intro hx
        have hfx : (φ_C (Circle.exp x)).1 ∈
            (fun t => (φ_C (Circle.exp t)).1) '' {t₁, t₂, t₃, t₄} :=
          himg_eq.symm ▸ ⟨x, hx, rfl⟩
        obtain ⟨y, hy, hyx⟩ := hfx
        exact hinj_comp (hsub_t hy) (hsub_a hx) hyx ▸ hy
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      eq_of_strictMono_four_of_set_eq ht₂ ht₃ ht₄ ha01 ha12 ha23 hset_t_a
    have hp₁_eq : p₁ = fig1Sph φ (pos (W.toWall.corner 0)) := hc₁.symm.trans (hφ_C_a 0)
    have hp₂_eq : p₂ = fig1Sph φ (pos (W.toWall.corner 1)) := hc₂.symm.trans (hφ_C_a 1)
    have hp₃_eq : p₃ = fig1Sph φ (pos (W.toWall.corner 2)) := hc₃.symm.trans (hφ_C_a 2)
    have hp₄_eq : p₄ = fig1Sph φ (pos (W.toWall.corner 3)) := hc₄.symm.trans (hφ_C_a 3)
    subst hp₁_eq hp₂_eq hp₃_eq hp₄_eq
    rw [hdraw_corner 0, hdraw_corner 1, hdraw_corner 2, hdraw_corner 3]
    exact ⟨b 0, b 1, b 2, b 3, hcorner_G1 0, hcorner_G1 1, hcorner_G1 2, hcorner_G1 3,
      le_of_eq hb0.symm, hb01, hb12, hb23, hb3_lt,
      hφ_D_b 0, hφ_D_b 1, hφ_D_b 2, hφ_D_b 3⟩

end GM22
end GraphMinor
