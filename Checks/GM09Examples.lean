module

import GraphMinor.GM09.Basic
import GraphMinor.GM11.DrawingOps

/-!
# Sanity checks and examples for `Neighborhood.IsRural` and `Society.IsRuralSociety` (GM IX)

This file verifies that the definition of a rural neighborhood (`Neighborhood.IsRural`) in
`GraphMinor/GM09/Defs.lean`, which ties the orientations of both boundary circles `bd(Δ)` and
`bd(Δ₀)` to the clockwise orientation of `EuclideanPlane` (`IsClockwiseDiscHomeo`), satisfies four
essential properties:

1. **Counterexample (`not_isRural_counterexample`):** The edgeless neighborhood on three vertices
   `{0, 1, 2}` with opposite cyclic orders `Ω = (0, 1, 2)` and `Ω₀ = (0, 2, 1)` is **not** rural.
2. **Simultaneous reversal (`isRural_reverse`):** If `(G, Ω, Ω₀)` is rural, then so is
   `(G, Ω⁻¹, Ω₀⁻¹)`, reversing both cyclic permutations simultaneously (by reflecting the plane
   via `conjPlane`).
3. **Society reversal (`isRuralSociety_reverse_iff`):** A society `(G, Ω)` is rural
   (`IsRuralSociety`) if and only if `(G, Ω⁻¹)` is.
4. **Non-vacuity (`isRural_roundDiscExample`):** A round-disc example with `Ω̄₀` non-empty is rural.
-/

namespace GraphMinor.GM09Examples

open Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
  GraphMinor.GM09 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. Properties of `CyclicPerm` reversal (`Ω⁻¹`) -/

@[simp]
theorem reverse_bar (Ω : CyclicPerm α) : Ω⁻¹.bar = Ω.bar := rfl

theorem reverse_toFun (Ω : CyclicPerm α) : Ω⁻¹.toFun = Ω.invFunBar := rfl

theorem iterate_invFunBar_toFun (Ω : CyclicPerm α) (n : ℕ) {z : α} (hz : z ∈ Ω.bar) :
    (Ω.invFunBar^[n]) ((Ω.toFun^[n]) z) = z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply',
      Ω.invFunBar_toFun (Ω.iterate_mem n hz)]
    exact ih

theorem iterate_toFun_invFunBar (Ω : CyclicPerm α) (n : ℕ) {z : α} (hz : z ∈ Ω.bar) :
    (Ω.toFun^[n]) ((Ω.invFunBar^[n]) z) = z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hmem : (Ω.invFunBar^[n]) z ∈ Ω.bar := by
      change (Ω⁻¹.toFun^[n]) z ∈ Ω⁻¹.bar
      exact Ω⁻¹.iterate_mem n hz
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', Ω.toFun_invFunBar hmem]
    exact ih

theorem iterate_invFunBar_sub (Ω : CyclicPerm α) {k j : ℕ} (hj : j ≤ k) {x : α}
    (hx : x ∈ Ω.bar) :
    (Ω.invFunBar^[j]) ((Ω.toFun^[k]) x) = (Ω.toFun^[k - j]) x := by
  have hk : k = j + (k - j) := (Nat.add_sub_of_le hj).symm
  conv_lhs => rw [hk, Function.iterate_add_apply]
  exact iterate_invFunBar_toFun Ω j (Ω.iterate_mem (k - j) hx)

theorem firstHitIn_reverse_of_firstHitIn {Ω : CyclicPerm α} {X : Set α} {x y : α}
    (hx : x ∈ Ω.bar) (hxX : x ∈ X) (h : Ω.FirstHitIn X x y) :
    Ω⁻¹.FirstHitIn X y x := by
  rcases h with ⟨k, hk1, rfl, hyX, hmin⟩
  refine ⟨k, hk1, ?_, hxX, ?_⟩
  · change (Ω.invFunBar^[k]) ((Ω.toFun^[k]) x) = x
    exact iterate_invFunBar_toFun Ω k hx
  · intro j hj1 hjlt
    change (Ω.invFunBar^[j]) ((Ω.toFun^[k]) x) ∉ X
    rw [iterate_invFunBar_sub Ω (le_of_lt hjlt) hx]
    exact hmin (k - j) (Nat.le_sub_of_add_le (by omega)) (Nat.sub_lt (by omega) (by omega))

theorem firstHitIn_of_firstHitIn_reverse {Ω : CyclicPerm α} {X : Set α} {x y : α}
    (hy : y ∈ Ω.bar) (hyX : y ∈ X) (h : Ω⁻¹.FirstHitIn X y x) :
    Ω.FirstHitIn X x y := by
  rcases h with ⟨k, hk1, hky, hxX, hmin⟩
  change (Ω.invFunBar^[k]) y = x at hky
  subst hky
  have hsub : ∀ {j : ℕ}, j ≤ k → (Ω.toFun^[j]) ((Ω.invFunBar^[k]) y) = (Ω.invFunBar^[k - j]) y := by
    intro j hj
    have hk : k = j + (k - j) := (Nat.add_sub_of_le hj).symm
    have hmem : (Ω.invFunBar^[k - j]) y ∈ Ω.bar := Ω⁻¹.iterate_mem (k - j) hy
    conv_lhs => rw [hk, Function.iterate_add_apply]
    exact iterate_toFun_invFunBar Ω j hmem
  refine ⟨k, hk1, ?_, hyX, ?_⟩
  · rw [hsub (le_refl k), Nat.sub_self, Function.iterate_zero_apply]
  · intro j hj1 hjlt
    rw [hsub (le_of_lt hjlt)]
    exact hmin (k - j) (Nat.le_sub_of_add_le (by omega)) (Nat.sub_lt (by omega) (by omega))

theorem isClockwise3_reverse_iff {Ω : CyclicPerm α} {v₁ v₂ v₃ : α} :
    Ω⁻¹.IsClockwise3 v₁ v₂ v₃ ↔ Ω.IsClockwise3 v₁ v₃ v₂ := by
  rw [CyclicPerm.isClockwise3_iff, CyclicPerm.isClockwise3_iff]
  have hset : ({v₁, v₃, v₂} : Set α) = {v₁, v₂, v₃} := by
    ext x; simp [or_comm]
  rw [hset]
  simp only [reverse_bar]
  refine ⟨fun ⟨h12, h13, h23, hv1, hv2, hv3, hhit12, hhit23, hhit31⟩ =>
    ⟨h13, h12, h23.symm, hv1, hv3, hv2,
      firstHitIn_of_firstHitIn_reverse hv3 (by simp) hhit31,
      firstHitIn_of_firstHitIn_reverse hv2 (by simp) hhit23,
      firstHitIn_of_firstHitIn_reverse hv1 (by simp) hhit12⟩,
    fun ⟨h13, h12, h32, hv1, hv3, hv2, hhit13, hhit32, hhit21⟩ =>
    ⟨h12, h13, h32.symm, hv1, hv2, hv3,
      firstHitIn_reverse_of_firstHitIn hv2 (by simp) hhit21,
      firstHitIn_reverse_of_firstHitIn hv3 (by simp) hhit32,
      firstHitIn_reverse_of_firstHitIn hv1 (by simp) hhit13⟩⟩

/-! ## 2. Disjointness of `IsRural` when `Ω` and `Ω₀` have opposite orientations on 3 vertices -/

theorem circleCyclic_of_lt {t₁ t₂ t₃ : ℝ} (h12 : t₁ < t₂) (h23 : t₂ < t₃)
    (h31 : t₃ < t₁ + 2 * Real.pi) :
    CircleCyclic (Circle.exp t₁) (Circle.exp t₂) (Circle.exp t₃) :=
  ⟨t₂ - t₁, t₃ - t₁, by linarith, by linarith, by linarith,
    by rw [← Circle.exp_add, add_sub_cancel],
    by rw [← Circle.exp_add, add_sub_cancel]⟩

/-- If `(G, Ω, Ω₀)` is a rural neighborhood and `v₁, v₂, v₃` are vertices of `G`, then `(v₁, v₂, v₃)`
cannot be `Ω`-clockwise while `(v₁, v₃, v₂)` is `Ω₀`-clockwise. -/
theorem not_isClockwise3_swap_of_isRural {N : Neighborhood α β} (hrural : N.IsRural)
    {v₁ v₂ v₃ : α} (hcw : N.Ω.IsClockwise3 v₁ v₂ v₃) (hcw₀ : N.Ω₀.IsClockwise3 v₁ v₃ v₂) :
    False := by
  obtain ⟨Γ, Δ, Δ₀, hΔ, hΔ₀_sub, _, _, _, ⟨φ, hφ_cw, hagrees⟩, hinner⟩ := hrural
  have hv₁_bar₀ : v₁ ∈ N.Ω₀.bar := (CyclicPerm.isClockwise3_iff.mp hcw₀).2.2.2.1
  rcases hinner with ⟨_, hbar₀_emp⟩ | ⟨hΔ₀, φ₀, hφ₀_cw, hagrees₀⟩
  · rw [hbar₀_emp] at hv₁_bar₀
    exact hv₁_bar₀
  · obtain ⟨t₁, t₂, t₃, ht12, ht23, ht31, hφ1, hφ2, hφ3⟩ := hagrees.2 v₁ v₂ v₃ hcw
    obtain ⟨s₁, s₃, s₂, hs13, hs32, hs21, hφ₀1, hφ₀3, hφ₀2⟩ := hagrees₀.2 v₁ v₃ v₂ hcw₀
    obtain ⟨_, h1⟩ := hφ1
    obtain ⟨_, h01⟩ := hφ₀1
    obtain ⟨_, h2⟩ := hφ2
    obtain ⟨_, h02⟩ := hφ₀2
    obtain ⟨_, h3⟩ := hφ3
    obtain ⟨_, h03⟩ := hφ₀3
    have heq1 : (φ₀ (Circle.exp s₁)).1 = (φ (Circle.exp t₁)).1 := h01.symm.trans h1
    have heq2 : (φ₀ (Circle.exp s₂)).1 = (φ (Circle.exp t₂)).1 := h02.symm.trans h2
    have heq3 : (φ₀ (Circle.exp s₃)).1 = (φ (Circle.exp t₃)).1 := h03.symm.trans h3
    have hcy_outer : CircleCyclic (Circle.exp t₁) (Circle.exp t₂) (Circle.exp t₃) :=
      circleCyclic_of_lt ht12 ht23 ht31
    have hcy_inner : CircleCyclic (Circle.exp s₁) (Circle.exp s₃) (Circle.exp s₂) :=
      circleCyclic_of_lt hs13 hs32 hs21
    have hcy_outer' : CircleCyclic (Circle.exp t₁) (Circle.exp t₃) (Circle.exp t₂) :=
      order_of_nested_euclideanPlane hΔ₀ hΔ hΔ₀_sub rfl rfl hφ₀_cw hφ_cw hcy_inner heq1 heq3 heq2
    exact not_circleCyclic_both hcy_outer hcy_outer'

/-! ## 3. The 3-vertex counterexample is not rural -/

/-- The edgeless graph on `Fin 3 = {0, 1, 2}`. -/
def counterexampleGraph : Graph (Fin 3) Empty where
  vertexSet := univ
  edgeSet := ∅
  IsLink e _ _ := e.elim
  isLink_symm e _ := e.elim
  eq_or_eq_of_isLink_of_isLink e _ _ _ _ := e.elim
  edge_mem_iff_exists_isLink e := e.elim
  left_mem_of_isLink e _ _ := e.elim

/-- The cyclic permutation `(0, 1, 2)` on `Fin 3`. -/
def cyclicPerm012 : CyclicPerm (Fin 3) where
  bar := univ
  toFun i := i + 1
  finite_bar := finite_univ
  bijOn :=
    ⟨fun _ _ => trivial,
     fun _ _ _ _ h => add_right_cancel h,
     fun x _ => ⟨x - 1, trivial, sub_add_cancel x 1⟩⟩
  single_orbit x _ y _ := by
    refine ⟨(y - x).val, ?_⟩
    revert x y
    decide

/-- The reverse cyclic permutation `(0, 2, 1)` on `Fin 3`. -/
def cyclicPerm021 : CyclicPerm (Fin 3) where
  bar := univ
  toFun i := i + 2
  finite_bar := finite_univ
  bijOn :=
    ⟨fun _ _ => trivial,
     fun _ _ _ _ h => add_right_cancel h,
     fun x _ => ⟨x + 1, trivial, by fin_cases x <;> rfl⟩⟩
  single_orbit x _ y _ := by
    refine ⟨(x - y).val, ?_⟩
    revert x y
    decide

/-- The counterexample neighborhood `G = ({0, 1, 2}, ∅)`, `Ω = (0, 1, 2)`, `Ω₀ = (0, 2, 1)`. -/
def counterexampleNeighborhood : Neighborhood (Fin 3) Empty where
  G := counterexampleGraph
  Ω := cyclicPerm012
  Ω₀ := cyclicPerm021
  finite_V := finite_univ
  finite_E := finite_empty
  bar_subset _ _ := trivial
  bar₀_subset _ _ := trivial

theorem isClockwise3_cyclicPerm012 : cyclicPerm012.IsClockwise3 0 1 2 := by
  rw [CyclicPerm.isClockwise3_iff]
  refine ⟨by decide, by decide, by decide, trivial, trivial, trivial, ?_, ?_, ?_⟩
  · refine ⟨1, le_rfl, rfl, by simp, fun j hj1 hjlt => by omega⟩
  · refine ⟨1, le_rfl, rfl, by simp, fun j hj1 hjlt => by omega⟩
  · refine ⟨1, le_rfl, rfl, by simp, fun j hj1 hjlt => by omega⟩

theorem isClockwise3_cyclicPerm021 : cyclicPerm021.IsClockwise3 0 2 1 := by
  rw [CyclicPerm.isClockwise3_iff]
  refine ⟨by decide, by decide, by decide, trivial, trivial, trivial, ?_, ?_, ?_⟩
  · refine ⟨1, le_rfl, rfl, by simp, fun j hj1 hjlt => by omega⟩
  · refine ⟨1, le_rfl, rfl, by simp, fun j hj1 hjlt => by omega⟩
  · refine ⟨1, le_rfl, rfl, by simp, fun j hj1 hjlt => by omega⟩

/-- **Check 1:** The counterexample neighborhood `(G, (0, 1, 2), (0, 2, 1))` on three edgeless
vertices is not rural. -/
theorem not_isRural_counterexample : ¬ counterexampleNeighborhood.IsRural := fun hrural =>
  not_isClockwise3_swap_of_isRural hrural isClockwise3_cyclicPerm012 isClockwise3_cyclicPerm021

/-! ## 4. Reversing both `Ω` and `Ω₀` preserves `IsRural` -/

/-- Transport a `Drawing EuclideanPlane` along `conjPlane`. -/
theorem exists_conjPlane_drawing (D : Drawing EuclideanPlane) :
    ∃ D' : Drawing EuclideanPlane,
      D'.U = conjPlane '' D.U ∧ D'.V = conjPlane '' D.V ∧ D'.E = image conjPlane '' D.E ∧
      ∀ e ∈ D.E, closure (conjPlane '' e) = conjPlane '' closure e := by
  have harc := GM11.arcComponentsIn_image (F := D.U \ D.V)
    conjPlane.continuous.continuousOn conjPlane.symm.continuous.continuousOn
    (fun x _ => conjPlane.symm_apply_apply x)
  have hdiff : conjPlane '' D.U \ conjPlane '' D.V = conjPlane '' (D.U \ D.V) :=
    (Set.image_sdiff conjPlane.injective D.U D.V).symm
  have hcl : ∀ e ∈ D.E, closure (conjPlane '' e) = conjPlane '' closure e :=
    fun e _ => (conjPlane.toHomeomorph.image_closure e).symm
  have hcap : ∀ e ∈ D.E, closure (conjPlane '' e) ∩ conjPlane '' D.V =
      conjPlane '' (closure e ∩ D.V) := by
    intro e he
    rw [hcl e he, Set.image_inter conjPlane.injective]
  refine ⟨⟨conjPlane '' D.U, conjPlane '' D.V, image_mono D.V_subset_U,
    conjPlane.toHomeomorph.isClosed_image.mpr D.isClosed_U,
    D.finite_V.image conjPlane, ?_, ?_⟩, rfl, rfl, ?_, hcl⟩
  rotate_left 2
  · change arcComponentsIn (conjPlane '' D.U \ conjPlane '' D.V) = _
    rw [hdiff, harc]
    rfl
  · rw [hdiff, harc]
    exact D.finite_edges.image _
  · rw [hdiff, harc]
    rintro _ ⟨e, he, rfl⟩
    rw [hcap e he]
    rcases D.edge_cond e he with ⟨u, v, huv, hc, hL⟩ | ⟨u, hc, hF⟩
    · left
      refine ⟨conjPlane u, conjPlane v, fun h => huv (conjPlane.injective h), ?_, ?_⟩
      · rw [hc, image_pair]
      · obtain ⟨φ₁, h0, h1⟩ := hL
        exact ⟨(φ₁.trans (conjPlane.toHomeomorph.image (closure e))).trans
          (Homeomorph.setCongr (hcl e he).symm),
          congrArg conjPlane h0, congrArg conjPlane h1⟩
    · right
      refine ⟨conjPlane u, ?_, ?_⟩
      · rw [hc, image_singleton]
      · obtain ⟨φ₂⟩ := hF
        exact ⟨(φ₂.trans (conjPlane.toHomeomorph.image (closure e))).trans
          (Homeomorph.setCongr (hcl e he).symm)⟩

/-- Transport a `GraphDrawing G EuclideanPlane` along `conjPlane`. -/
theorem exists_conjPlane_graphDrawing {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) :
    ∃ Γ' : GraphDrawing G EuclideanPlane,
      Γ'.drawing.U = conjPlane '' Γ.drawing.U ∧
      (∀ v, graphDrawingVertexSet Γ' v = conjPlane '' graphDrawingVertexSet Γ v) := by
  obtain ⟨D', hU', hV', hE', hcl⟩ := exists_conjPlane_drawing Γ.drawing
  have hinjE : InjOn (image conjPlane) Γ.drawing.E :=
    fun _ _ _ _ heq => Set.image_injective.mpr conjPlane.injective heq
  let vFun : Γ.drawing.V → D'.V := fun x => ⟨conjPlane x.1, hV' ▸ ⟨x.1, x.2, rfl⟩⟩
  have hvFun_bij : Function.Bijective vFun :=
    ⟨fun x y h => Subtype.ext (conjPlane.injective (congrArg Subtype.val h)),
     fun z => by
       have hz : z.1 ∈ conjPlane '' Γ.drawing.V := hV' ▸ z.2
       obtain ⟨x, hx, hfx⟩ := hz
       exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩⟩
  let eFun : Γ.drawing.E → D'.E := fun e => ⟨conjPlane '' e.1, hE' ▸ ⟨e.1, e.2, rfl⟩⟩
  have heFun_bij : Function.Bijective eFun :=
    ⟨fun e₁ e₂ h => Subtype.ext (hinjE e₁.2 e₂.2 (congrArg Subtype.val h)),
     fun a => by
       have ha : a.1 ∈ image conjPlane '' Γ.drawing.E := hE' ▸ a.2
       obtain ⟨e, he, hfe⟩ := ha
       exact ⟨⟨e, he⟩, Subtype.ext hfe⟩⟩
  let vEquiv : Γ.drawing.V ≃ D'.V := Equiv.ofBijective vFun hvFun_bij
  let eEquiv : Γ.drawing.E ≃ D'.E := Equiv.ofBijective eFun heFun_bij
  let iso' : Iso G D'.toGraph :=
    { vertexEquiv := Γ.iso.vertexEquiv.trans vEquiv
      edgeEquiv := Γ.iso.edgeEquiv.trans eEquiv
      isLink_iff := fun {e x y} => by
        rw [Γ.iso.isLink_iff]
        let e₀ := Γ.iso.edgeEquiv e
        let x₀ := Γ.iso.vertexEquiv x
        let y₀ := Γ.iso.vertexEquiv y
        change Γ.drawing.toGraph.IsLink e₀.1 x₀.1 y₀.1 ↔
          D'.toGraph.IsLink (conjPlane '' e₀.1) (conjPlane x₀.1) (conjPlane y₀.1)
        have he' : conjPlane '' e₀.1 ∈ D'.E := hE' ▸ ⟨e₀.1, e₀.2, rfl⟩
        have hx' : conjPlane x₀.1 ∈ D'.V := hV' ▸ ⟨x₀.1, x₀.2, rfl⟩
        have hy' : conjPlane y₀.1 ∈ D'.V := hV' ▸ ⟨y₀.1, y₀.2, rfl⟩
        have hcap : closure (conjPlane '' e₀.1) ∩ D'.V =
            conjPlane '' (closure e₀.1 ∩ Γ.drawing.V) := by
          rw [hcl e₀.1 e₀.2, hV', Set.image_inter conjPlane.injective]
        constructor
        · rintro ⟨_, _, _, hlink⟩
          refine ⟨he', hx', hy', ?_⟩
          rw [hcap, hlink, image_pair]
        · rintro ⟨_, _, _, hlink⟩
          refine ⟨e₀.2, x₀.2, y₀.2, ?_⟩
          rw [hcap, ← image_pair] at hlink
          exact Set.image_injective.mpr conjPlane.injective hlink }
  let Γ' : GraphDrawing G EuclideanPlane := ⟨D', iso'⟩
  refine ⟨Γ', hU', fun v => ?_⟩
  ext y
  simp only [graphDrawingVertexSet, mem_ofPred_eq, mem_image]
  exact ⟨fun ⟨hv, hy⟩ => ⟨(Γ.iso.vertexEquiv ⟨v, hv⟩).1, ⟨hv, rfl⟩, hy⟩,
    fun ⟨x, ⟨hv, hx⟩, hxy⟩ => ⟨hv, (congrArg conjPlane hx).trans hxy⟩⟩

theorem drawingAgreesWithOArcHomeo_conjPlane_inv {G : Graph α β}
    {Γ Γ' : GraphDrawing G EuclideanPlane} {Ω : CyclicPerm α} {C C' : Set EuclideanPlane}
    (φ : Circle ≃ₜ C) (hC' : C' = conjPlane '' C)
    (hvert : ∀ v, graphDrawingVertexSet Γ' v = conjPlane '' graphDrawingVertexSet Γ v)
    (hagrees : DrawingAgreesWithOArcHomeo Γ Ω C φ) :
    DrawingAgreesWithOArcHomeo Γ' Ω⁻¹ C'
      ((Homeomorph.inv Circle).trans
        ((φ.trans (conjPlane.toHomeomorph.image C)).trans (Homeomorph.setCongr hC'.symm))) := by
  let φ' : Circle ≃ₜ C' :=
    (Homeomorph.inv Circle).trans
      ((φ.trans (conjPlane.toHomeomorph.image C)).trans (Homeomorph.setCongr hC'.symm))
  have hφ'_val : ∀ w : Circle, (φ' w).1 = conjPlane (φ w⁻¹).1 := fun _ => rfl
  refine ⟨fun v hv => ?_, fun v₁ v₂ v₃ hcw => ?_⟩
  · rw [reverse_bar] at hv
    rw [hvert v, hC']
    exact image_mono (hagrees.1 v hv)
  · rw [isClockwise3_reverse_iff] at hcw
    obtain ⟨t₁, t₃, t₂, ht13, ht32, ht21, h1, h3, h2⟩ := hagrees.2 v₁ v₃ v₂ hcw
    refine ⟨-t₁, -t₂ + 2 * Real.pi, -t₃ + 2 * Real.pi,
      by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
    · rw [hφ'_val, ← Circle.exp_neg, neg_neg, hvert v₁]
      exact mem_image_of_mem _ h1
    · have hexp : (Circle.exp (-t₂ + 2 * Real.pi))⁻¹ = Circle.exp t₂ := by
        rw [← Circle.exp_neg, show -(-t₂ + 2 * Real.pi) = t₂ - 2 * Real.pi by ring,
          ← GM19.exp_add_two_pi (t₂ - 2 * Real.pi), sub_add_cancel]
      rw [hφ'_val, hexp, hvert v₂]
      exact mem_image_of_mem _ h2
    · have hexp : (Circle.exp (-t₃ + 2 * Real.pi))⁻¹ = Circle.exp t₃ := by
        rw [← Circle.exp_neg, show -(-t₃ + 2 * Real.pi) = t₃ - 2 * Real.pi by ring,
          ← GM19.exp_add_two_pi (t₃ - 2 * Real.pi), sub_add_cancel]
      rw [hφ'_val, hexp, hvert v₃]
      exact mem_image_of_mem _ h3

/-- The neighborhood `(G, Ω⁻¹, Ω₀⁻¹)` obtained by reversing both boundary cyclic permutations of `N`. -/
noncomputable def reverseNeighborhood (N : Neighborhood α β) : Neighborhood α β where
  G := N.G
  Ω := N.Ω⁻¹
  Ω₀ := N.Ω₀⁻¹
  finite_V := N.finite_V
  finite_E := N.finite_E
  bar_subset := N.bar_subset
  bar₀_subset := N.bar₀_subset

/-- **Check 2:** If `(G, Ω, Ω₀)` is rural, then so is `(G, Ω⁻¹, Ω₀⁻¹)`. -/
theorem isRural_reverse {N : Neighborhood α β} (hrural : N.IsRural) :
    (reverseNeighborhood N).IsRural := by
  obtain ⟨Γ, Δ, Δ₀, hΔ, hΔ₀_sub, hU_sub, hbd, hbd₀, ⟨φ, hφ_cw, hagrees⟩, hinner⟩ := hrural
  obtain ⟨Γ', hU'_eq, hvert'⟩ := exists_conjPlane_graphDrawing Γ
  let Δ' : Set EuclideanPlane := conjPlane '' Δ
  let Δ₀' : Set EuclideanPlane := conjPlane '' Δ₀
  have hΔ' : IsClosedDisc Δ' := isClosedDisc_image_conjPlane hΔ
  have hΔ₀'_sub : Δ₀' ⊆ Δ' := image_mono hΔ₀_sub
  have hU'_sub : Γ'.drawing.U ⊆ Δ' \ interior Δ₀' := by
    rw [hU'_eq, interior_image_conjPlane, ← Set.image_sdiff conjPlane.injective]
    exact image_mono hU_sub
  have hbd' : ∀ v ∈ V(N.G), (graphDrawingVertexSet Γ' v ⊆ subBd Δ' ↔ v ∈ N.Ω⁻¹.bar) := by
    intro v hv
    rw [hvert' v, subBd_image_conjPlane, Set.image_subset_image_iff conjPlane.injective,
      reverse_bar]
    exact hbd v hv
  have hbd₀' : ∀ v ∈ V(N.G), (graphDrawingVertexSet Γ' v ⊆ subBd Δ₀' ↔ v ∈ N.Ω₀⁻¹.bar) := by
    intro v hv
    rw [hvert' v, subBd_image_conjPlane, Set.image_subset_image_iff conjPlane.injective,
      reverse_bar]
    exact hbd₀ v hv
  have hdisj_Δ : ∀ w, (φ w).1 ∉ interior Δ := by
    intro w hw
    have hmem : (φ w).1 ∈ frontier Δ := Surface.subBd_eq_frontier Δ ▸ (φ w).2
    exact hmem.2 hw
  have hφ'_cw_base : IsClockwiseDiscHomeo Δ'
      ((Homeomorph.inv Circle).trans (φ.trans (conjPlane.toHomeomorph.image (subBd Δ)))) :=
    isClockwiseDiscHomeo_conjPlane_inv hdisj_Δ hφ_cw
  let φ' : Circle ≃ₜ subBd Δ' :=
    (Homeomorph.inv Circle).trans
      ((φ.trans (conjPlane.toHomeomorph.image (subBd Δ))).trans
        (Homeomorph.setCongr (subBd_image_conjPlane Δ).symm))
  have hφ'_cw : IsClockwiseDiscHomeo Δ' φ' := hφ'_cw_base
  have hagrees' : DrawingAgreesWithOArcHomeo Γ' N.Ω⁻¹ (subBd Δ') φ' :=
    drawingAgreesWithOArcHomeo_conjPlane_inv φ (subBd_image_conjPlane Δ) hvert' hagrees
  refine ⟨Γ', Δ', Δ₀', hΔ', hΔ₀'_sub, hU'_sub, hbd', hbd₀', ⟨φ', hφ'_cw, hagrees'⟩, ?_⟩
  rcases hinner with ⟨rfl, hbar₀⟩ | ⟨hΔ₀, φ₀, hφ₀_cw, hagrees₀⟩
  · exact Or.inl ⟨by simp [Δ₀'], hbar₀⟩
  · right
    have hdisj_Δ₀ : ∀ w, (φ₀ w).1 ∉ interior Δ₀ := by
      intro w hw
      have hmem : (φ₀ w).1 ∈ frontier Δ₀ := Surface.subBd_eq_frontier Δ₀ ▸ (φ₀ w).2
      exact hmem.2 hw
    have hφ₀'_cw : IsClockwiseDiscHomeo Δ₀'
        ((Homeomorph.inv Circle).trans
          ((φ₀.trans (conjPlane.toHomeomorph.image (subBd Δ₀))).trans
            (Homeomorph.setCongr (subBd_image_conjPlane Δ₀).symm))) :=
      isClockwiseDiscHomeo_conjPlane_inv hdisj_Δ₀ hφ₀_cw
    refine ⟨isClosedDisc_image_conjPlane hΔ₀,
      (Homeomorph.inv Circle).trans
        ((φ₀.trans (conjPlane.toHomeomorph.image (subBd Δ₀))).trans
          (Homeomorph.setCongr (subBd_image_conjPlane Δ₀).symm)),
      hφ₀'_cw,
      drawingAgreesWithOArcHomeo_conjPlane_inv φ₀ (subBd_image_conjPlane Δ₀) hvert' hagrees₀⟩

theorem drawingAgreesWithOArcHomeo_congr_perm {S : Type*} [TopologicalSpace S]
    {G : Graph α β} {Γ : GraphDrawing G S} {Ω₁ Ω₂ : CyclicPerm α} {C : Set S} (φ : Circle ≃ₜ C)
    (hbar : Ω₁.bar = Ω₂.bar)
    (hcw : ∀ v₁ v₂ v₃, Ω₁.IsClockwise3 v₁ v₂ v₃ ↔ Ω₂.IsClockwise3 v₁ v₂ v₃) :
    DrawingAgreesWithOArcHomeo Γ Ω₁ C φ ↔ DrawingAgreesWithOArcHomeo Γ Ω₂ C φ := by
  unfold DrawingAgreesWithOArcHomeo
  rw [hbar]
  exact and_congr_right fun _ => forall₃_congr fun v₁ v₂ v₃ => imp_congr_left (hcw v₁ v₂ v₃)

theorem isRural_congr_perm {N₁ N₂ : Neighborhood α β} (h₁ : N₁.IsRural) (hG : N₁.G = N₂.G)
    (hbar : N₁.Ω.bar = N₂.Ω.bar) (hbar₀ : N₁.Ω₀.bar = N₂.Ω₀.bar)
    (hcw : ∀ v₁ v₂ v₃, N₁.Ω.IsClockwise3 v₁ v₂ v₃ ↔ N₂.Ω.IsClockwise3 v₁ v₂ v₃)
    (hcw₀ : ∀ v₁ v₂ v₃, N₁.Ω₀.IsClockwise3 v₁ v₂ v₃ ↔ N₂.Ω₀.IsClockwise3 v₁ v₂ v₃) :
    N₂.IsRural := by
  rcases N₁ with ⟨G, Ω₁, Ω₀₁, fV₁, fE₁, b₁, b₀₁⟩
  rcases N₂ with ⟨G₂, Ω₂, Ω₀₂, fV₂, fE₂, b₂, b₀₂⟩
  dsimp at hG hbar hbar₀ hcw hcw₀
  subst hG
  obtain ⟨Γ, Δ, Δ₀, hΔ, hΔ₀_sub, hU_sub, hbd, hbd₀, ⟨φ, hφ_cw, hagrees⟩, hinner⟩ := h₁
  refine ⟨Γ, Δ, Δ₀, hΔ, hΔ₀_sub, hU_sub,
    fun v hv => (hbd v hv).trans (by rw [hbar]),
    fun v hv => (hbd₀ v hv).trans (by rw [hbar₀]),
    ⟨φ, hφ_cw, (drawingAgreesWithOArcHomeo_congr_perm φ hbar hcw).mp hagrees⟩, ?_⟩
  rcases hinner with ⟨hΔ₀_emp, hbar₀_emp⟩ | ⟨hΔ₀, φ₀, hφ₀_cw, hagrees₀⟩
  · exact Or.inl ⟨hΔ₀_emp, hbar₀ ▸ hbar₀_emp⟩
  · exact Or.inr ⟨hΔ₀, φ₀, hφ₀_cw,
      (drawingAgreesWithOArcHomeo_congr_perm φ₀ hbar₀ hcw₀).mp hagrees₀⟩

theorem isRural_reverse_iff (N : Neighborhood α β) :
    (reverseNeighborhood N).IsRural ↔ N.IsRural := by
  refine ⟨fun h => ?_, isRural_reverse⟩
  refine isRural_congr_perm (isRural_reverse h) rfl rfl rfl
    (fun v₁ v₂ v₃ => ?_) (fun v₁ v₂ v₃ => ?_)
  · change N.Ω⁻¹⁻¹.IsClockwise3 v₁ v₂ v₃ ↔ N.Ω.IsClockwise3 v₁ v₂ v₃
    rw [isClockwise3_reverse_iff, isClockwise3_reverse_iff]
  · change N.Ω₀⁻¹⁻¹.IsClockwise3 v₁ v₂ v₃ ↔ N.Ω₀.IsClockwise3 v₁ v₂ v₃
    rw [isClockwise3_reverse_iff, isClockwise3_reverse_iff]

/-! ## 5. Society rurality (`IsRuralSociety`) is invariant under reversing `Ω` -/

/-- The society `(G, Ω⁻¹)` obtained by reversing the cyclic permutation `Ω` of `S`. -/
noncomputable def reverseSociety (S : Society α β) : Society α β where
  G := S.G
  Ω := S.Ω⁻¹
  finite_V := S.finite_V
  finite_E := S.finite_E
  bar_subset := S.bar_subset

/-- **Check 3:** A society `(G, Ω)` is rural (`IsRuralSociety`) if and only if `(G, Ω⁻¹)` is. -/
theorem isRuralSociety_reverse_iff (S : Society α β) :
    (reverseSociety S).IsRuralSociety ↔ S.IsRuralSociety := by
  unfold Society.IsRuralSociety
  refine ⟨fun ⟨Ω₀, h₀, hbar₀, h⟩ => ?_, fun ⟨Ω₀, h₀, hbar₀, h⟩ => ?_⟩
  · refine ⟨Ω₀⁻¹, h₀, hbar₀, ?_⟩
    refine isRural_congr_perm (isRural_reverse h) rfl rfl rfl (fun v₁ v₂ v₃ => ?_) (fun _ _ _ => Iff.rfl)
    change S.Ω⁻¹⁻¹.IsClockwise3 v₁ v₂ v₃ ↔ S.Ω.IsClockwise3 v₁ v₂ v₃
    rw [isClockwise3_reverse_iff, isClockwise3_reverse_iff]
  · exact ⟨Ω₀⁻¹, h₀, hbar₀, isRural_reverse h⟩

/-! ## 6. A round-disc example with `Ω̄₀` non-empty is rural -/

/-- The one-vertex edgeless graph on `Unit`. -/
def oneVertexGraph : Graph Unit Empty where
  vertexSet := {()}
  edgeSet := ∅
  IsLink e _ _ := e.elim
  isLink_symm e _ := e.elim
  eq_or_eq_of_isLink_of_isLink e _ _ _ _ := e.elim
  edge_mem_iff_exists_isLink e := e.elim
  left_mem_of_isLink e _ _ := e.elim

/-- The cyclic permutation on `{()}`. -/
def oneVertexCyclicPerm : CyclicPerm Unit where
  bar := {()}
  toFun := id
  finite_bar := finite_singleton ()
  bijOn := bijOn_id {()}
  single_orbit _ _ _ _ := ⟨0, rfl⟩

/-- The round-disc example neighborhood on `{()}` with `Ω̄ = Ω̄₀ = {()}`. -/
def roundDiscNeighborhood : Neighborhood Unit Empty where
  G := oneVertexGraph
  Ω := oneVertexCyclicPerm
  Ω₀ := oneVertexCyclicPerm
  finite_V := finite_singleton ()
  finite_E := finite_empty
  bar_subset := Subset.rfl
  bar₀_subset := Subset.rfl

theorem roundDiscNeighborhood_bar₀_nonempty : roundDiscNeighborhood.Ω₀.bar.Nonempty :=
  ⟨(), rfl⟩

/-- **Check 4:** The round-disc example with `Ω̄₀` non-empty is rural. -/
theorem isRural_roundDiscExample : roundDiscNeighborhood.IsRural := by
  have hD : IsClosedDisc ClosedUnitDisc := ⟨Homeomorph.refl ClosedUnitDisc⟩
  obtain ⟨φ, hφ_cw⟩ := exists_isClockwiseDiscHomeo hD
  let p₀ : EuclideanPlane := (φ 1).1
  have hp₀_bd : p₀ ∈ subBd ClosedUnitDisc := (φ 1).2
  have hp₀_D : p₀ ∈ ClosedUnitDisc := by
    have hcl : IsClosed ClosedUnitDisc := isClosed_closedBall
    rw [Surface.subBd_eq_frontier] at hp₀_bd
    exact hcl.frontier_subset hp₀_bd
  have hp₀_not_int : p₀ ∉ interior ClosedUnitDisc := by
    have h := hp₀_bd
    rw [Surface.subBd_eq_frontier] at h
    exact h.2
  let D_draw : Drawing EuclideanPlane := GM11.pointsDrawing (finite_singleton p₀)
  have hD_V : D_draw.V = {p₀} := rfl
  have hD_E : D_draw.E = ∅ := by
    ext C
    exact ⟨fun ⟨⟨x, hx⟩, hsub, _⟩ => by simpa [D_draw, GM11.pointsDrawing] using hsub hx,
      False.elim⟩
  let vEquiv : V(roundDiscNeighborhood.G) ≃ D_draw.V :=
    { toFun := fun _ => ⟨p₀, rfl⟩
      invFun := fun _ => ⟨(), rfl⟩
      left_inv := fun ⟨(), _⟩ => rfl
      right_inv := fun ⟨_, hx⟩ => Subtype.ext hx.symm }
  let eEquiv : E(roundDiscNeighborhood.G) ≃ D_draw.E :=
    { toFun := fun e => e.1.elim
      invFun := fun e => False.elim (by rw [hD_E] at e; exact e.2)
      left_inv := fun e => e.1.elim
      right_inv := fun e => False.elim (by rw [hD_E] at e; exact e.2) }
  let Γ : GraphDrawing roundDiscNeighborhood.G EuclideanPlane :=
    { drawing := D_draw
      iso :=
        { vertexEquiv := vEquiv
          edgeEquiv := eEquiv
          isLink_iff := fun {e _ _} => e.1.elim } }
  have hvert : ∀ v : Unit, graphDrawingVertexSet Γ v = {p₀} := by
    intro v
    ext x
    constructor
    · rintro ⟨_, rfl⟩
      rfl
    · intro hx
      rw [mem_singleton_iff.mp hx]
      exact ⟨rfl, rfl⟩
  have hagrees :
      DrawingAgreesWithOArcHomeo Γ roundDiscNeighborhood.Ω (subBd ClosedUnitDisc) φ := by
    refine ⟨fun v _ => ?_, fun v₁ v₂ _ hcw => ?_⟩
    · rw [hvert v, singleton_subset_iff]
      exact hp₀_bd
    · exact False.elim ((CyclicPerm.isClockwise3_iff.mp hcw).1 (Subsingleton.elim v₁ v₂))
  refine ⟨Γ, ClosedUnitDisc, ClosedUnitDisc, hD, Subset.rfl, ?_, ?_, ?_,
    ⟨φ, hφ_cw, hagrees⟩, Or.inr ⟨hD, φ, hφ_cw, hagrees⟩⟩
  · change {p₀} ⊆ ClosedUnitDisc \ interior ClosedUnitDisc
    rw [singleton_subset_iff]
    exact ⟨hp₀_D, hp₀_not_int⟩
  · intro v _
    rw [hvert v, singleton_subset_iff]
    exact ⟨fun _ => rfl, fun _ => hp₀_bd⟩
  · intro v _
    rw [hvert v, singleton_subset_iff]
    exact ⟨fun _ => rfl, fun _ => hp₀_bd⟩

end GraphMinor.GM09Examples
