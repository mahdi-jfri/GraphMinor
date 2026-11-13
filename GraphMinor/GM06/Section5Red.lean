module

public import GraphMinor.GM06.Section5

/-!
# Graph Minors VI, Section 5: Proofs of Reductions Lemmas (5.4) and (5.5)

This file proves:
- Path parameterization and homotopy helpers (`curvesHomotopicIn_of_range_subset_parametrizesSet`,
  `parametrizesSet_pathTrans`, `isPathDrawing_walkDrawing_of_isSimple`, `curvesHomotopic_comp_pi_map`).
- `GM06.theorem_5_4 : Statement54` (Graph Minors VI, page 130).
- The contraction case used in (5.4).
-/

public section

namespace GraphMinor.GM06

universe u

open Set Function Complex Real Topology Metric Graph unitInterval
open GraphMinor.Surface GraphMinor.GM11

/-! ## 1. Path Parameterization and Homotopy Helpers -/

/-- Any curve `γ` whose range lies in `U` and shares endpoints `s, t` with an injective
parameterization `f₀` of `U` (`ParametrizesSet f₀ U s t`) is homotopic to `f₀` in `U`. -/
theorem curvesHomotopicIn_of_range_subset_parametrizesSet
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {U : Set S} {s t : S} {f₀ γ : Curve S}
    (hf₀ : ParametrizesSet f₀ U s t)
    (hγU : range γ ⊆ U) (hγ0 : γ 0 = s) (hγ1 : γ 1 = t) :
    CurvesHomotopicIn U γ f₀ := by
  rcases hf₀ with ⟨hf₀_inj, hf₀_range, hf₀0, hf₀1⟩
  let φ : unitInterval ≃ₜ range f₀ :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofInjective f₀ hf₀_inj)
      f₀.continuous.rangeFactorization
  have hγ_mem : ∀ x : unitInterval, γ x ∈ range f₀ := fun x => by
    rw [hf₀_range]
    exact hγU ⟨x, rfl⟩
  let σ_fn : C(unitInterval, unitInterval) :=
    ⟨fun x => φ.symm ⟨γ x, hγ_mem x⟩,
      φ.symm.continuous.comp (γ.continuous.subtype_mk hγ_mem)⟩
  have hf₀_σ : ∀ x : unitInterval, f₀ (σ_fn x) = γ x := fun x =>
    congrArg Subtype.val (φ.apply_symm_apply ⟨γ x, hγ_mem x⟩)
  have hσ0 : σ_fn 0 = 0 := hf₀_inj (by rw [hf₀_σ 0, hγ0, hf₀0])
  have hσ1 : σ_fn 1 = 1 := hf₀_inj (by rw [hf₀_σ 1, hγ1, hf₀1])
  have h_mem : ∀ p : unitInterval × unitInterval,
      (1 - (p.2 : ℝ)) * (σ_fn p.1 : ℝ) + (p.2 : ℝ) * (p.1 : ℝ) ∈ Icc (0 : ℝ) 1 := fun p =>
    convex_Icc (0 : ℝ) 1 (σ_fn p.1).2 p.1.2
      (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
  let τ : C(unitInterval × unitInterval, unitInterval) :=
    ⟨fun p => ⟨(1 - (p.2 : ℝ)) * (σ_fn p.1 : ℝ) + (p.2 : ℝ) * (p.1 : ℝ), h_mem p⟩,
      (Continuous.add
        (Continuous.mul (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
          (continuous_subtype_val.comp (σ_fn.continuous.comp continuous_fst)))
        (Continuous.mul (continuous_subtype_val.comp continuous_snd)
          (continuous_subtype_val.comp continuous_fst))).subtype_mk h_mem⟩
  let ψ : C(unitInterval × unitInterval, S) := f₀.comp τ
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [← hf₀_range]
    exact ⟨τ p, rfl⟩
  · intro x
    have hτ0 : τ (x, 0) = σ_fn x := Subtype.ext (by change (1 - 0) * (σ_fn x : ℝ) + 0 * (x : ℝ) = σ_fn x; ring)
    change f₀ (τ (x, 0)) = γ x
    rw [hτ0, hf₀_σ]
  · intro x
    have hτ1 : τ (x, 1) = x := Subtype.ext (by change (1 - 1) * (σ_fn x : ℝ) + 1 * (x : ℝ) = x; ring)
    change f₀ (τ (x, 1)) = f₀ x
    rw [hτ1]
  · intro y
    have hτy0 : τ (0, y) = 0 := Subtype.ext (by
      change (1 - (y : ℝ)) * (σ_fn 0 : ℝ) + (y : ℝ) * (0 : ℝ) = 0
      rw [hσ0]; simp)
    change f₀ (τ (0, y)) = γ 0
    rw [hτy0, hf₀0, hγ0]
  · intro y
    have hτy0 : τ (0, y) = 0 := Subtype.ext (by
      change (1 - (y : ℝ)) * (σ_fn 0 : ℝ) + (y : ℝ) * (0 : ℝ) = 0
      rw [hσ0]; simp)
    change f₀ (τ (0, y)) = f₀ 0
    rw [hτy0]
  · intro y
    have hτy1 : τ (1, y) = 1 := Subtype.ext (by
      change (1 - (y : ℝ)) * (σ_fn 1 : ℝ) + (y : ℝ) * (1 : ℝ) = 1
      rw [hσ1]; simp)
    change f₀ (τ (1, y)) = γ 1
    rw [hτy1, hf₀1, hγ1]
  · intro y
    have hτy1 : τ (1, y) = 1 := Subtype.ext (by
      change (1 - (y : ℝ)) * (σ_fn 1 : ℝ) + (y : ℝ) * (1 : ℝ) = 1
      rw [hσ1]; simp)
    change f₀ (τ (1, y)) = f₀ 1
    rw [hτy1]

/-- Concatenation of two injective parameterizations `ParametrizesSet f₁ U₁ u w` and
`ParametrizesSet f₂ U₂ w v` meeting only at `w` (`U₁ ∩ U₂ ⊆ {w}`) gives an injective
parameterization of `U₁ ∪ U₂` from `u` to `v`. -/
theorem parametrizesSet_pathTrans {S : Type u} [TopologicalSpace S]
    {U₁ U₂ : Set S} {u w v : S} {f₁ f₂ : Curve S}
    (hf₁ : ParametrizesSet f₁ U₁ u w) (hf₂ : ParametrizesSet f₂ U₂ w v)
    (hinter : U₁ ∩ U₂ ⊆ {w}) :
    let P₁ : Path u w := ⟨f₁, hf₁.2.2.1, hf₁.2.2.2⟩
    let P₂ : Path w v := ⟨f₂, hf₂.2.2.1, hf₂.2.2.2⟩
    ParametrizesSet (P₁.trans P₂).toContinuousMap (U₁ ∪ U₂) u v := by
  intro P₁ P₂
  rcases hf₁ with ⟨hinj₁, hrange₁, hf₁0, hf₁1⟩
  rcases hf₂ with ⟨hinj₂, hrange₂, hf₂0, hf₂1⟩
  refine ⟨?_, ?_, P₁.trans P₂ |>.source, P₁.trans P₂ |>.target⟩
  · intro t₁ t₂ heq
    change (P₁.trans P₂) t₁ = (P₁.trans P₂) t₂ at heq
    rw [Path.trans_apply, Path.trans_apply] at heq
    split_ifs at heq with h1 h2 h2
    · have h_arg := congrArg Subtype.val (hinj₁ heq)
      change 2 * (t₁ : ℝ) = 2 * (t₂ : ℝ) at h_arg
      exact Subtype.ext (by linarith)
    · let s₁ : unitInterval := ⟨2 * (t₁ : ℝ), ⟨by linarith [t₁.2.1], by linarith⟩⟩
      let s₂ : unitInterval := ⟨2 * (t₂ : ℝ) - 1, ⟨by linarith, by linarith [t₂.2.2]⟩⟩
      change f₁ s₁ = f₂ s₂ at heq
      have hmem : f₁ s₁ ∈ U₁ ∩ U₂ := by
        rw [← hrange₁, ← hrange₂]
        exact ⟨⟨s₁, rfl⟩, ⟨s₂, heq.symm⟩⟩
      have h_eq_w : f₁ s₁ = w := mem_singleton_iff.mp (hinter hmem)
      have h_eq_w2 : f₂ s₂ = w := heq.symm.trans h_eq_w
      have ht₂_arg := congrArg Subtype.val (hinj₂ (h_eq_w2.trans hf₂0.symm))
      change 2 * (t₂ : ℝ) - 1 = 0 at ht₂_arg
      linarith
    · let s₂ : unitInterval := ⟨2 * (t₂ : ℝ), ⟨by linarith [t₂.2.1], by linarith⟩⟩
      let s₁ : unitInterval := ⟨2 * (t₁ : ℝ) - 1, ⟨by linarith, by linarith [t₁.2.2]⟩⟩
      change f₂ s₁ = f₁ s₂ at heq
      have hmem : f₁ s₂ ∈ U₁ ∩ U₂ := by
        rw [← hrange₁, ← hrange₂]
        exact ⟨⟨s₂, rfl⟩, ⟨s₁, heq⟩⟩
      have h_eq_w : f₁ s₂ = w := mem_singleton_iff.mp (hinter hmem)
      have h_eq_w1 : f₂ s₁ = w := heq.trans h_eq_w
      have ht₁_arg := congrArg Subtype.val (hinj₂ (h_eq_w1.trans hf₂0.symm))
      change 2 * (t₁ : ℝ) - 1 = 0 at ht₁_arg
      linarith
    · have h_arg := congrArg Subtype.val (hinj₂ heq)
      change 2 * (t₁ : ℝ) - 1 = 2 * (t₂ : ℝ) - 1 at h_arg
      exact Subtype.ext (by linarith)
  · change range (P₁.trans P₂) = U₁ ∪ U₂
    rw [Path.trans_range]
    exact congrArg₂ (· ∪ ·) hrange₁ hrange₂

/-- Every non-loop edge `e` of a drawing `Γ` with `Γ.toGraph.IsLink e u v` (`u ≠ v`) has a
curve `f` satisfying `ParametrizesSet f (closure e) u v`. -/
theorem exists_parametrizesSet_closure_edge {S : Type u} [TopologicalSpace S]
    (Γ : Drawing S) {e : Set S} {u v : S}
    (hlink : Γ.toGraph.IsLink e u v) (hne : u ≠ v) :
    ∃ f : Curve S, ParametrizesSet f (closure e) u v := by
  rcases hlink with ⟨he, _, _, hcap⟩
  rcases Γ.edge_cond e he with ⟨u', v', hu'v', hcap', φ, hφ0, hφ1⟩ | ⟨u', hcap', _⟩
  · have hpair : ({u', v'} : Set S) = {u, v} := hcap'.symm.trans hcap
    have hu'_mem : u' ∈ ({u, v} : Set S) := hpair ▸ mem_insert u' {v'}
    have hv'_mem : v' ∈ ({u, v} : Set S) := hpair ▸ mem_insert_of_mem u' rfl
    let γ : Curve S := ⟨fun t => (φ t).1, continuous_subtype_val.comp φ.continuous⟩
    have hγ_inj : Function.Injective γ := fun t₁ t₂ h => φ.injective (Subtype.ext h)
    have hγ_range : range γ = closure e := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩; exact (φ t).2
      · intro hx
        exact ⟨φ.symm ⟨x, hx⟩, congrArg Subtype.val (φ.apply_symm_apply ⟨x, hx⟩)⟩
    rcases hu'_mem with hu'_u | hu'_v
    · rcases hv'_mem with hv'_u | hv'_v
      · exact False.elim (hu'v' (hu'_u.trans hv'_u.symm))
      · have hv_eq : v' = v := mem_singleton_iff.mp hv'_v
        exact ⟨γ, hγ_inj, hγ_range, hφ0.trans hu'_u, hφ1.trans hv_eq⟩
    · have hu'_eq : u' = v := mem_singleton_iff.mp hu'_v
      have hv'_eq : v' = u := by
        rcases hv'_mem with hv'_u | hv'_v
        · exact hv'_u
        · exact False.elim (hu'v' (hu'_eq.trans (mem_singleton_iff.mp hv'_v).symm))
      let γ_rev : Curve S := ⟨fun t => γ (σ t), γ.continuous.comp continuous_symm⟩
      have hσ_inj : Function.Injective σ := fun t₁ t₂ h => by simpa using congrArg σ h
      refine ⟨γ_rev, hγ_inj.comp hσ_inj, ?_, ?_, ?_⟩
      · rw [← hγ_range]
        ext x
        constructor
        · rintro ⟨t, rfl⟩; exact ⟨σ t, rfl⟩
        · rintro ⟨t, rfl⟩; exact ⟨σ t, by simp [γ_rev]⟩
      · change (φ (σ 0)).1 = u; simpa [hv'_eq] using hφ1
      · change (φ (σ 1)).1 = v; simpa [hu'_eq] using hφ0
  · exfalso
    have hpair : ({u, v} : Set S) = {u'} := hcap.symm.trans hcap'
    have hu : u = u' := mem_singleton_iff.mp (hpair ▸ mem_insert u {v})
    have hv : v = u' := mem_singleton_iff.mp (hpair ▸ mem_insert_of_mem u rfl)
    exact hne (hu.trans hv.symm)

/-- For any simple walk `W : GraphWalk Γ.toGraph u v` with `u ≠ v`, `walkDrawing Γ W` has a curve
`f` satisfying `ParametrizesSet f (walkDrawing Γ W).U u v`, and hence satisfies
`IsPathDrawing (walkDrawing Γ W) u v`. -/
theorem exists_parametrizesSet_walkDrawing_of_isSimple {S : Type u} [TopologicalSpace S] [T1Space S]
    (Γ : Drawing S) {u v : S} {W : GraphWalk Γ.toGraph u v}
    (hW : W.IsSimple) (hne : u ≠ v) :
    ∃ f : Curve S, ParametrizesSet f (walkDrawing Γ W).U u v := by
  induction W with
  | nil _ => exact False.elim (hne rfl)
  | @cons u w v e hlink r ih =>
    have hnd : (u :: r.support).Nodup := by
      simpa [GraphWalk.IsSimple] using hW
    have hu_not_r : u ∉ r.support := (List.nodup_cons.mp hnd).1
    have hr_simple : r.IsSimple := (List.nodup_cons.mp hnd).2
    have huw : u ≠ w := fun h => hu_not_r (h ▸ r.start_mem_support)
    obtain ⟨f_e, hf_e⟩ := exists_parametrizesSet_closure_edge Γ hlink huw
    rcases eq_or_ne w v with rfl | hwv
    · have hr_nil : r = GraphWalk.nil hlink.right_mem := by
        cases r with
        | nil _ => rfl
        | @cons w w' w _ hlink' r' =>
          exfalso
          have hnd' : (w :: r'.support).Nodup := hr_simple
          exact (List.nodup_cons.mp hnd').1 r'.end_mem_support
      have hU_eq : (walkDrawing Γ (GraphWalk.cons hlink r)).U = closure e := by
        rw [hr_nil]
        ext x
        rw [mem_walkDrawing_U]
        simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false, GraphWalk.edges_cons, GraphWalk.edges_nil,
          exists_eq_left]
        constructor
        · rintro ((rfl | rfl) | hx)
          · have : x ∈ closure e ∩ Γ.V := by rw [hlink.2.2.2]; exact mem_insert x {w}
            exact this.1
          · have : x ∈ closure e ∩ Γ.V := by rw [hlink.2.2.2]; exact mem_insert_of_mem u rfl
            exact this.1
          · exact hx
        · intro hx; exact Or.inr hx
      rw [hU_eq]
      exact ⟨f_e, hf_e⟩
    · obtain ⟨f_r, hf_r⟩ := ih hr_simple hwv
      have hU_eq : (walkDrawing Γ (GraphWalk.cons hlink r)).U =
          closure e ∪ (walkDrawing Γ r).U := by
        ext x
        rw [mem_walkDrawing_U, mem_union, mem_walkDrawing_U]
        simp only [GraphWalk.support_cons, List.mem_cons, GraphWalk.edges_cons]
        constructor
        · rintro ((rfl | hxr) | ⟨e', rfl | he', hxe'⟩)
          · left
            have : x ∈ closure e ∩ Γ.V := by rw [hlink.2.2.2]; exact mem_insert x {w}
            exact this.1
          · exact Or.inr (Or.inl hxr)
          · exact Or.inl hxe'
          · exact Or.inr (Or.inr ⟨e', he', hxe'⟩)
        · rintro (hxe | (hxr | ⟨e', he', hxe'⟩))
          · exact Or.inr ⟨e, Or.inl rfl, hxe⟩
          · exact Or.inl (Or.inr hxr)
          · exact Or.inr ⟨e', Or.inr he', hxe'⟩
      have hinter : closure e ∩ (walkDrawing Γ r).U ⊆ {w} := by
        rintro x ⟨hxe, hxr⟩
        rw [mem_singleton_iff]
        rw [closure_edge_eq_union_ends Γ hlink huw] at hxe
        rcases hxe with hxe_in | (rfl | rfl)
        · exfalso
          have hx_not_V : x ∉ Γ.V := (hlink.1.2.1 hxe_in).2
          rw [mem_walkDrawing_U] at hxr
          rcases hxr with hxr_sup | ⟨e', he', hxe'⟩
          · exact hx_not_V (r.mem_vertexSet_of_mem_support hxr_sup)
          · have hxe'_in : x ∈ e' := by
              have he'_mem : e' ∈ Γ.E := by
                have : e' ∈ (walkDrawing Γ r).E := by rw [walkDrawing_E]; exact he'
                exact (walkDrawing_isSubdrawing Γ r).2 this
              rw [← Γ.closure_diff_V he'_mem]
              exact ⟨hxe', hx_not_V⟩
            have he'_mem : e' ∈ Γ.E := by
              have : e' ∈ (walkDrawing Γ r).E := by rw [walkDrawing_E]; exact he'
              exact (walkDrawing_isSubdrawing Γ r).2 this
            have he'_eq : e' = e := Γ.edge_eq_of_mem he'_mem hlink.1 hxe'_in hxe_in
            subst he'_eq
            exact hu_not_r (r.left_mem_support_of_mem_edges he' hlink)
        · exfalso
          have hx_V : x ∈ (walkDrawing Γ r).V := by
            rw [mem_walkDrawing_U] at hxr
            rcases hxr with hxr_sup | ⟨e', he', hxe'⟩
            · rw [walkDrawing_V]; exact hxr_sup
            · have he'_sub : e' ∈ (walkDrawing Γ r).E := by rw [walkDrawing_E]; exact he'
              have hcap := (walkDrawing_isSubdrawing Γ r).closure_inter_V he'_sub
              have : x ∈ closure e' ∩ Γ.V := ⟨hxe', hlink.2.1⟩
              rw [← hcap] at this
              exact this.2
          rw [walkDrawing_V] at hx_V
          exact hu_not_r hx_V
        · rfl
      rw [hU_eq]
      exact ⟨_, parametrizesSet_pathTrans hf_e hf_r hinter⟩

theorem isPathDrawing_walkDrawing_of_isSimple {S : Type u} [TopologicalSpace S] [T1Space S]
    (Γ : Drawing S) {u v : S} {W : GraphWalk Γ.toGraph u v}
    (hW : W.IsSimple) (hne : u ≠ v) :
    IsPathDrawing (walkDrawing Γ W) u v :=
  ⟨walkDrawing_isPathBetween Γ hW, exists_parametrizesSet_walkDrawing_of_isSimple Γ hW hne⟩

/-! ## 2. Proof of Graph Minors VI, (5.4) -/

theorem cylinderM1Point_mem_cylinderCuff1 (k : ℕ) (j : Fin k) :
    cylinderM1Point k j ∈ cylinderCuff1 :=
  rfl

theorem cylinderM2Point_mem_cylinderCuff2 (k : ℕ) (j : Fin k) :
    cylinderM2Point k j ∈ cylinderCuff2 :=
  rfl

theorem cylinderM1Point_mem_bd (k : ℕ) (j : Fin k) :
    cylinderM1Point k j ∈ bd ClosedCylinder := by
  rw [bd_closedCylinder]
  exact Or.inl (cylinderM1Point_mem_cylinderCuff1 k j)

theorem cylinderM2Point_mem_bd (k : ℕ) (j : Fin k) :
    cylinderM2Point k j ∈ bd ClosedCylinder := by
  rw [bd_closedCylinder]
  exact Or.inr (cylinderM2Point_mem_cylinderCuff2 k j)

theorem cylinderM1Point_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective (cylinderM1Point k) := by
  intro i j hij
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have hexp : Circle.exp (2 * ((i.1 + 1 : ℕ) : ℝ) * π / k) =
      Circle.exp (2 * ((j.1 + 1 : ℕ) : ℝ) * π / k) :=
    congrArg (fun p : ClosedCylinder => p.1.2) hij
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
  have hm_int : ((i.1 + 1 : ℕ) : ℝ) = ((j.1 + 1 : ℕ) : ℝ) + (m : ℝ) * (k : ℝ) := by
    have hmul : (2 * ((i.1 + 1 : ℕ) : ℝ) * π / k) * (k / (2 * π)) =
        (2 * ((j.1 + 1 : ℕ) : ℝ) * π / k + m * (2 * π)) * (k / (2 * π)) := by rw [hm]
    have h2pi_ne : (2 * π : ℝ) ≠ 0 := by positivity
    field_simp [hk_ne, h2pi_ne] at hmul
    linarith
  have hm_z : (i.1 : ℤ) + 1 = (j.1 : ℤ) + 1 + m * (k : ℤ) := by
    exact_mod_cast hm_int
  have hi_lt : (i.1 : ℤ) < (k : ℤ) := Int.ofNat_lt.mpr i.2
  have hj_lt : (j.1 : ℤ) < (k : ℤ) := Int.ofNat_lt.mpr j.2
  have hi_ge : (0 : ℤ) ≤ (i.1 : ℤ) := Int.natCast_nonneg i.1
  have hj_ge : (0 : ℤ) ≤ (j.1 : ℤ) := Int.natCast_nonneg j.1
  have hm0 : m = 0 := by nlinarith
  subst hm0
  ext
  omega

/-- If `H_id` is a homotopy from `id` to `π_map` fixing `bd ClosedCylinder` pointwise, then any
curve `γ` with endpoints in `bd ClosedCylinder` is homotopic to `π_map.comp γ`. -/
theorem curvesHomotopic_comp_pi_map
    {π_map : C(ClosedCylinder, ClosedCylinder)}
    {H_id : C(unitInterval × ClosedCylinder, ClosedCylinder)}
    (hH0 : ∀ p, H_id (0, p) = p)
    (hH1 : ∀ p, H_id (1, p) = π_map p)
    (hHbd : ∀ p ∈ bd ClosedCylinder, ∀ t, H_id (t, p) = p)
    {γ : Curve ClosedCylinder}
    (hγ0 : γ 0 ∈ bd ClosedCylinder) (hγ1 : γ 1 ∈ bd ClosedCylinder) :
    CurvesHomotopic γ (π_map.comp γ) := by
  let ψ : C(unitInterval × unitInterval, ClosedCylinder) :=
    ⟨fun p => H_id (p.2, γ p.1),
      H_id.continuous.comp (continuous_snd.prodMk (γ.continuous.comp continuous_fst))⟩
  refine ⟨ψ, fun _ => trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact hH0 (γ x)
  · intro x; exact hH1 (γ x)
  · intro y; exact hHbd (γ 0) hγ0 y
  · intro y; exact (hHbd (γ 0) hγ0 y).trans ((hHbd (γ 0) hγ0 1).symm.trans (hH1 (γ 0)))
  · intro y; exact hHbd (γ 1) hγ1 y
  · intro y; exact (hHbd (γ 1) hγ1 y).trans ((hHbd (γ 1) hγ1 1).symm.trans (hH1 (γ 1)))

/-- At an initial vertex of valency one, every edge other than its
non-loop incident edge has closure missing that vertex. -/
theorem not_mem_closure_edge_of_ne_red3 {k : ℕ} {G : Drawing ClosedCylinder}
    {i : Fin k} {e e₀ : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hlink : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv_ne : v ≠ cylinderM1Point k i)
    (he₀ : e₀ ∈ G.E) (he₀_ne : e₀ ≠ e) :
    cylinderM1Point k i ∉ closure e₀ := by
  let s_i := cylinderM1Point k i
  intro hs_cl
  have hs_V : s_i ∈ G.V := hlink.2.1
  have hs_cap : s_i ∈ closure e₀ ∩ G.V := ⟨hs_cl, hs_V⟩
  let S₁ : Set (Set ClosedCylinder) :=
    {e' ∈ E(G.toGraph) | ∃ w ≠ s_i, G.toGraph.IsLink e' s_i w}
  let S₂ : Set (Set ClosedCylinder) :=
    {e' ∈ E(G.toGraph) | G.toGraph.IsLink e' s_i s_i}
  have hS₁_fin : S₁.Finite := G.finite_edges.subset (fun _ h => h.1)
  have hS₂_fin : S₂.Finite := G.finite_edges.subset (fun _ h => h.1)
  have hval_eq : S₁.ncard + 2 * S₂.ncard = 1 := hval
  rcases G.edge_cond e₀ he₀ with ⟨u₁, u₂, hu₁₂, hcap₀, _⟩ | ⟨u₁, hcap₀, _⟩
  · rw [hcap₀] at hs_cap
    have hex_w : ∃ w ≠ s_i, G.toGraph.IsLink e₀ s_i w := by
      rcases hs_cap with rfl | hs_u₂
      · refine ⟨u₂, hu₁₂.symm, he₀, hs_V, ?_, hcap₀⟩
        have : u₂ ∈ closure e₀ ∩ G.V := by rw [hcap₀]; exact mem_insert_of_mem s_i rfl
        exact this.2
      · have hs_eq : s_i = u₂ := mem_singleton_iff.mp hs_u₂
        subst hs_eq
        refine ⟨u₁, hu₁₂, he₀, hs_V, ?_, ?_⟩
        · have : u₁ ∈ closure e₀ ∩ G.V := by rw [hcap₀]; exact mem_insert u₁ {s_i}
          exact this.2
        · rw [hcap₀, Set.pair_comm]
    have he_mem : e ∈ S₁ := ⟨hlink.1, v, hv_ne, hlink⟩
    have he₀_mem : e₀ ∈ S₁ := ⟨he₀, hex_w⟩
    have hpair_sub : ({e₀, e} : Set (Set ClosedCylinder)) ⊆ S₁ := by
      rintro x (rfl | rfl)
      · exact he₀_mem
      · exact he_mem
    have h2 : 2 ≤ S₁.ncard := by
      have hcard := ncard_le_ncard hpair_sub hS₁_fin
      rw [ncard_pair he₀_ne] at hcard
      exact hcard
    omega
  · rw [hcap₀] at hs_cap
    have hs_eq : s_i = u₁ := mem_singleton_iff.mp hs_cap
    subst hs_eq
    have he₀_mem : e₀ ∈ S₂ := ⟨he₀, he₀, hs_V, hs_V, by simpa using hcap₀⟩
    have h1 : 1 ≤ S₂.ncard := (Set.ncard_pos hS₂_fin).mpr ⟨e₀, he₀_mem⟩
    omega

/-- **Graph Minors VI, (5.4)** (page 130):
"If $(G', \mathcal{L}')$ is produced from $(G, \mathcal{L})$ by one of the reductions 1,..., 4, and
$\theta(\mathcal{L}') + 1/k$ is feasible in $G'$, then $\theta(\mathcal{L}) + 1/k$ is feasible in
$G$." -/
theorem theorem_5_4_proof : Statement54 := by
  intro k G G' L L' θ θ' hG hG' hL hL' hRed hFeas'
  rcases hRed with h1 | h2 | h3 | h4
  · exact theorem_5_4_red124 k G G' L L' θ θ' hG hL hL' (Or.inl h1) hFeas'
  · exact theorem_5_4_red124 k G G' L L' θ θ' hG hL hL' (Or.inr (Or.inl h2)) hFeas'
  · rcases h3 with ⟨i, e, v, π_map, H_id, hval, he, hv, hv_ne, hv_cuff2, hlink,
      hH0, hH1, hHbd, hpre, _, hInj, hSurj, _, hG'U, hG'V, hG'E, hL'U, _⟩
    have hk : 0 < k := hG.1
    let s_i := cylinderM1Point k i
    have hpi_bd : ∀ p ∈ bd ClosedCylinder, π_map p = p := fun p hp =>
      (hH1 p).symm.trans (hHbd p hp 1)
    have hθ_eq : θ' = θ := by
      let i₀ : Fin k := ⟨0, hk⟩
      have hg0 : L.curve i₀ 0 ∈ bd ClosedCylinder := by
        rw [(L.curve_parametrizes i₀).2.2.1]
        exact cylinderM1Point_mem_bd k i₀
      have hg1 : L.curve i₀ 1 ∈ bd ClosedCylinder := by
        rcases L.curve_one_mem i₀ with ⟨j₁, hj₁⟩
        rw [← hj₁]
        exact cylinderM2Point_mem_bd k j₁
      have hhom₁ : CurvesHomotopic (L'.curve i₀) (π_map.comp (L.curve i₀)) := (hL'U i₀).2
      have hhom₂ : CurvesHomotopic (L.curve i₀) (π_map.comp (L.curve i₀)) :=
        curvesHomotopic_comp_pi_map hH0 hH1 hHbd hg0 hg1
      rw [← hL' i₀, ← hL i₀, windingNumber_eq_of_homotopic hhom₁,
        ← windingNumber_eq_of_homotopic hhom₂]
    rw [hθ_eq] at hFeas'
    have hcl_e : closure e = e ∪ {s_i, v} :=
      closure_edge_eq_union_ends G hlink hv_ne.symm
    have hpi_v : π_map v = s_i := by
      have hv_cl : v ∈ closure e := by rw [hcl_e]; exact Or.inr (mem_insert_of_mem s_i rfl)
      rw [← hpre] at hv_cl
      exact mem_singleton_iff.mp hv_cl
    have hpi_si : π_map s_i = s_i := hpi_bd s_i (cylinderM1Point_mem_bd k i)
    have hv_mem_diff : v ∈ G.V \ {s_i} := ⟨hv, hv_ne⟩
    have hinj_V : InjOn π_map (G.V \ {s_i}) := by
      rintro x ⟨hxV, hx_ne⟩ y ⟨hyV, hy_ne⟩ hxy
      by_cases hpi_x : π_map x = s_i
      · have hx_cl : x ∈ closure e := by rw [← hpre]; exact hpi_x
        have hy_cl : y ∈ closure e := by rw [← hpre]; exact hxy.symm.trans hpi_x
        have hx_pair : x ∈ ({s_i, v} : Set ClosedCylinder) := by
          rw [← hlink.2.2.2]; exact ⟨hx_cl, hxV⟩
        have hy_pair : y ∈ ({s_i, v} : Set ClosedCylinder) := by
          rw [← hlink.2.2.2]; exact ⟨hy_cl, hyV⟩
        have hxv : x = v := by
          rcases hx_pair with rfl | hxv
          · exact False.elim (hx_ne rfl)
          · exact mem_singleton_iff.mp hxv
        have hyv : y = v := by
          rcases hy_pair with rfl | hyv
          · exact False.elim (hy_ne rfl)
          · exact mem_singleton_iff.mp hyv
        exact hxv.trans hyv.symm
      · have hx_not_cl : x ∉ closure e := fun h => hpi_x (by rw [← hpre] at h; exact h)
        have hy_not_cl : y ∉ closure e := fun h => hpi_x (hxy.trans (by rw [← hpre] at h; exact h))
        exact hInj x hx_not_cl y hy_not_cl hxy
    have hsurj_V : ∀ z ∈ G'.V, ∃ x ∈ G.V \ {s_i}, π_map x = z := by
      intro z hz
      rw [hG'V] at hz
      rcases hz with ⟨x, hxV, rfl⟩
      rcases eq_or_ne x s_i with rfl | hx_ne
      · exact ⟨v, hv_mem_diff, hpi_v.trans hpi_si.symm⟩
      · exact ⟨x, ⟨hxV, hx_ne⟩, rfl⟩
    have hdisj_e₀ : ∀ e₀ ∈ G.E \ {e}, Disjoint e₀ (closure e) := by
      rintro e₀ ⟨he₀, he₀_ne⟩
      rw [hcl_e]
      refine Disjoint.union_right (disjoint_edges_of_ne G he₀ he he₀_ne) ?_
      rw [disjoint_left]
      intro x hxe₀ hx_pair
      have hx_not_V : x ∉ G.V := (he₀.2.1 hxe₀).2
      rcases hx_pair with rfl | hxv
      · exact hx_not_V hlink.2.1
      · exact hx_not_V (mem_singleton_iff.mp hxv ▸ hv)
    have hcl_img : ∀ e₀ ∈ G.E \ {e}, closure (π_map '' e₀) = π_map '' closure e₀ := by
      rintro e₀ ⟨he₀, _⟩
      apply Subset.antisymm
      · exact closure_minimal (image_mono subset_closure)
          ((isCompact_closure_edge G he₀).image π_map.continuous).isClosed
      · exact image_closure_subset_closure_image π_map.continuous
    have hisLink_fwd : ∀ e₀ ∈ G.E \ {e}, ∀ x y : ClosedCylinder,
        G.toGraph.IsLink e₀ x y → G'.toGraph.IsLink (π_map '' e₀) (π_map x) (π_map y) := by
      rintro e₀ he₀ x y ⟨he₀_E, hxV, hyV, hcap₀⟩
      have he₀' : π_map '' e₀ ∈ G'.E := by
        rw [hG'E]
        exact ⟨e₀, he₀, rfl⟩
      have hx' : π_map x ∈ G'.V := by rw [hG'V]; exact ⟨x, hxV, rfl⟩
      have hy' : π_map y ∈ G'.V := by rw [hG'V]; exact ⟨y, hyV, rfl⟩
      refine ⟨he₀', hx', hy', ?_⟩
      rw [hcl_img e₀ he₀]
      ext z
      simp only [mem_inter_iff, mem_image, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨⟨w, hw_cl, rfl⟩, hzV'⟩
        by_cases hpi_w : π_map w = s_i
        · have hw_cl_e : w ∈ closure e := by rw [← hpre]; exact hpi_w
          have hw_not_e₀ : w ∉ e₀ := disjoint_right.mp (hdisj_e₀ e₀ he₀) hw_cl_e
          have hw_V : w ∈ G.V := by
            by_contra hw_notV
            have : w ∈ closure e₀ \ G.V := ⟨hw_cl, hw_notV⟩
            rw [G.closure_diff_V he₀_E] at this
            exact hw_not_e₀ this
          have hw_xy : w ∈ ({x, y} : Set ClosedCylinder) := by
            rw [← hcap₀]; exact ⟨hw_cl, hw_V⟩
          rcases hw_xy with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rw [hG'V] at hzV'
          rcases hzV' with ⟨u, huV, hpi_u⟩
          have hw_not_cl : w ∉ closure e := fun h => hpi_w (by rw [← hpre] at h; exact h)
          have hu_not_cl : u ∉ closure e := fun h =>
            hpi_w (hpi_u.symm.trans (by rw [← hpre] at h; exact h))
          have hwu : w = u := hInj w hw_not_cl u hu_not_cl hpi_u.symm
          have hw_V : w ∈ G.V := hwu ▸ huV
          have hw_xy : w ∈ ({x, y} : Set ClosedCylinder) := by
            rw [← hcap₀]; exact ⟨hw_cl, hw_V⟩
          rcases hw_xy with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
      · rintro (rfl | rfl)
        · have hx_cl : x ∈ closure e₀ := by
            have : x ∈ closure e₀ ∩ G.V := by rw [hcap₀]; exact mem_insert x {y}
            exact this.1
          exact ⟨⟨x, hx_cl, rfl⟩, hx'⟩
        · have hy_cl : y ∈ closure e₀ := by
            have : y ∈ closure e₀ ∩ G.V := by rw [hcap₀]; exact mem_insert_of_mem x rfl
            exact this.1
          exact ⟨⟨y, hy_cl, rfl⟩, hy'⟩
    have hisLink_rev : ∀ e' z₁ z₂, G'.toGraph.IsLink e' z₁ z₂ →
        ∃ e₀ ∈ G.E \ {e}, ∃ x₁ ∈ G.V \ {s_i}, ∃ x₂ ∈ G.V \ {s_i},
          e' = π_map '' e₀ ∧ π_map x₁ = z₁ ∧ π_map x₂ = z₂ ∧ G.toGraph.IsLink e₀ x₁ x₂ := by
      intro e' z₁ z₂ hlink'
      have he' : e' ∈ G'.E := hlink'.1
      rw [hG'E] at he'
      rcases he' with ⟨e₀, he₀, rfl⟩
      obtain ⟨x₁, hx₁, rfl⟩ := hsurj_V z₁ hlink'.2.1
      obtain ⟨x₂, hx₂, rfl⟩ := hsurj_V z₂ hlink'.2.2.1
      refine ⟨e₀, he₀, x₁, hx₁, x₂, hx₂, rfl, rfl, rfl, ?_⟩
      have hs_not_cl₀ : s_i ∉ closure e₀ :=
        not_mem_closure_edge_of_ne_red3 hval hlink hv_ne he₀.1 he₀.2
      obtain ⟨u₁, u₂, hlink₀⟩ : ∃ u₁ u₂, G.toGraph.IsLink e₀ u₁ u₂ := by
        rcases G.edge_cond e₀ he₀.1 with ⟨u₁, u₂, _, hcap₀, _⟩ | ⟨u₁, hcap₀, _⟩
        · have hu₁_cap : u₁ ∈ closure e₀ ∩ G.V := by rw [hcap₀]; exact mem_insert u₁ {u₂}
          have hu₂_cap : u₂ ∈ closure e₀ ∩ G.V := by rw [hcap₀]; exact mem_insert_of_mem u₁ rfl
          exact ⟨u₁, u₂, he₀.1, hu₁_cap.2, hu₂_cap.2, hcap₀⟩
        · have hu₁_cap : u₁ ∈ closure e₀ ∩ G.V := by rw [hcap₀]; exact mem_singleton u₁
          exact ⟨u₁, u₁, he₀.1, hu₁_cap.2, hu₁_cap.2, by simpa using hcap₀⟩
      have hu₁_cl : u₁ ∈ closure e₀ := by
        have : u₁ ∈ closure e₀ ∩ G.V := by rw [hlink₀.2.2.2]; exact mem_insert u₁ {u₂}
        exact this.1
      have hu₂_cl : u₂ ∈ closure e₀ := by
        have : u₂ ∈ closure e₀ ∩ G.V := by rw [hlink₀.2.2.2]; exact mem_insert_of_mem u₁ rfl
        exact this.1
      have hu₁_diff : u₁ ∈ G.V \ {s_i} := ⟨hlink₀.2.1, fun h => hs_not_cl₀ (h ▸ hu₁_cl)⟩
      have hu₂_diff : u₂ ∈ G.V \ {s_i} := ⟨hlink₀.2.2.1, fun h => hs_not_cl₀ (h ▸ hu₂_cl)⟩
      have hlink₀' := hisLink_fwd e₀ he₀ u₁ u₂ hlink₀
      have hpair_img : ({π_map x₁, π_map x₂} : Set ClosedCylinder) = {π_map u₁, π_map u₂} :=
        hlink'.2.2.2.symm.trans hlink₀'.2.2.2
      have hpair_eq : ({x₁, x₂} : Set ClosedCylinder) = {u₁, u₂} := by
        ext w
        simp only [mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro (rfl | rfl)
          · have hmem : π_map w ∈ ({π_map u₁, π_map u₂} : Set ClosedCylinder) :=
              hpair_img ▸ mem_insert (π_map w) {π_map x₂}
            rcases hmem with h1 | h2
            · exact Or.inl (hinj_V hx₁ hu₁_diff h1)
            · exact Or.inr (hinj_V hx₁ hu₂_diff (mem_singleton_iff.mp h2))
          · have hmem : π_map w ∈ ({π_map u₁, π_map u₂} : Set ClosedCylinder) :=
              hpair_img ▸ mem_insert_of_mem (π_map x₁) rfl
            rcases hmem with h1 | h2
            · exact Or.inl (hinj_V hx₂ hu₁_diff h1)
            · exact Or.inr (hinj_V hx₂ hu₂_diff (mem_singleton_iff.mp h2))
        · rintro (rfl | rfl)
          · have hmem : π_map w ∈ ({π_map x₁, π_map x₂} : Set ClosedCylinder) :=
              hpair_img.symm ▸ mem_insert (π_map w) {π_map u₂}
            rcases hmem with h1 | h2
            · exact Or.inl (hinj_V hu₁_diff hx₁ h1)
            · exact Or.inr (hinj_V hu₁_diff hx₂ (mem_singleton_iff.mp h2))
          · have hmem : π_map w ∈ ({π_map x₁, π_map x₂} : Set ClosedCylinder) :=
              hpair_img.symm ▸ mem_insert_of_mem (π_map u₁) rfl
            rcases hmem with h1 | h2
            · exact Or.inl (hinj_V hu₂_diff hx₁ h1)
            · exact Or.inr (hinj_V hu₂_diff hx₂ (mem_singleton_iff.mp h2))
      exact ⟨he₀.1, hx₁.1, hx₂.1, hlink₀.2.2.2.trans hpair_eq.symm⟩
    have hlift_walk : ∀ {z₁ z₂ : ClosedCylinder} (W' : GraphWalk G'.toGraph z₁ z₂),
        ∃ x₁ ∈ G.V \ {s_i}, ∃ x₂ ∈ G.V \ {s_i}, ∃ W : GraphWalk G.toGraph x₁ x₂,
          π_map x₁ = z₁ ∧ π_map x₂ = z₂ ∧
          W.support.map π_map = W'.support ∧
          (∀ u ∈ W.support, u ∈ G.V \ {s_i}) ∧
          (walkDrawing G W).U ⊆ π_map ⁻¹' (walkDrawing G' W').U := by
      intro z₁ z₂ W'
      induction W' with
      | @nil z hz =>
        obtain ⟨x, hx, rfl⟩ := hsurj_V z hz
        have hxV : x ∈ V(G.toGraph) := hx.1
        refine ⟨x, hx, x, hx, GraphWalk.nil hxV, rfl, rfl, rfl, ?_, ?_⟩
        · intro u hu
          rw [GraphWalk.support_nil, List.mem_singleton] at hu
          exact hu ▸ hx
        · intro p hp
          rw [mem_walkDrawing_U, GraphWalk.support_nil, GraphWalk.edges_nil] at hp
          simp only [List.mem_singleton, List.not_mem_nil, false_and, exists_false, or_false] at hp
          rw [hp, mem_preimage, mem_walkDrawing_U, GraphWalk.support_nil]
          exact Or.inl (List.mem_singleton_self _)
      | @cons z₁ z_mid z₂ e' hlink' r' ih =>
        obtain ⟨x_mid', hx_mid', x₂, hx₂, W_r, hpi_mid', hpi_2, hsup_r, hV_r, hU_r⟩ := ih
        obtain ⟨e₀, he₀, x₁, hx₁, x_mid, hx_mid, rfl, hpi_1, hpi_mid, hlink₀⟩ :=
          hisLink_rev e' z₁ z_mid hlink'
        have hx_mid_eq : x_mid = x_mid' := hinj_V hx_mid hx_mid' (hpi_mid.trans hpi_mid'.symm)
        subst hx_mid_eq
        let W := GraphWalk.cons hlink₀ W_r
        refine ⟨x₁, hx₁, x₂, hx₂, W, hpi_1, hpi_2, ?_, ?_, ?_⟩
        · simp [W, hpi_1, hsup_r]
        · intro u hu
          rw [GraphWalk.support_cons, List.mem_cons] at hu
          rcases hu with rfl | hu
          · exact hx₁
          · exact hV_r u hu
        · intro p hp
          rw [mem_walkDrawing_U, GraphWalk.support_cons, GraphWalk.edges_cons] at hp
          simp only [List.mem_cons] at hp
          rw [mem_preimage, mem_walkDrawing_U, GraphWalk.support_cons, GraphWalk.edges_cons]
          rcases hp with (rfl | hp_r) | ⟨e₁, he₁_eq | he₁, hpe₁⟩
          · exact Or.inl (List.mem_cons.mpr (Or.inl hpi_1))
          · have hp' := hU_r (by rw [mem_walkDrawing_U]; exact Or.inl hp_r)
            rw [mem_preimage, mem_walkDrawing_U] at hp'
            rcases hp' with hp'_sup | ⟨e₂, he₂, hpe₂⟩
            · exact Or.inl (List.mem_cons_of_mem _ hp'_sup)
            · exact Or.inr ⟨e₂, List.mem_cons_of_mem _ he₂, hpe₂⟩
          · rw [he₁_eq] at hpe₁
            refine Or.inr ⟨π_map '' e₀, List.mem_cons_self, ?_⟩
            rw [hcl_img e₀ he₀]
            exact ⟨p, hpe₁, rfl⟩
          · have hp' := hU_r (by rw [mem_walkDrawing_U]; exact Or.inr ⟨e₁, he₁, hpe₁⟩)
            rw [mem_preimage, mem_walkDrawing_U] at hp'
            rcases hp' with hp'_sup | ⟨e₂, he₂, hpe₂⟩
            · exact Or.inl (List.mem_cons_of_mem _ hp'_sup)
            · exact Or.inr ⟨e₂, List.mem_cons_of_mem _ he₂, hpe₂⟩
    rcases hFeas' with ⟨M', hM'⟩
    have hex_P : ∀ j : Fin k, ∃ (P_j : Drawing ClosedCylinder) (f_j : Curve ClosedCylinder),
        P_j.IsSubdrawing G ∧ P_j.U ⊆ G.U ∧
        IsPathDrawing P_j (cylinderM1Point k j) (M'.curve j 1) ∧
        ParametrizesSet f_j P_j.U (cylinderM1Point k j) (M'.curve j 1) ∧
        P_j.U ⊆ π_map ⁻¹' (M'.pathDrawing j).U ∧
        windingNumber f_j = θ + 1 / (k : ℝ) := by
      intro j
      let s_j := cylinderM1Point k j
      let t_j := M'.curve j 1
      have hs_j_cuff1 : s_j ∈ cylinderCuff1 := cylinderM1Point_mem_cylinderCuff1 k j
      have ht_j_cuff2 : t_j ∈ cylinderCuff2 := by
        rcases M'.curve_one_mem j with ⟨m₂, hm₂⟩
        change M'.curve j 1 ∈ cylinderCuff2
        rw [← hm₂]
        exact cylinderM2Point_mem_cylinderCuff2 k m₂
      have hst_ne : s_j ≠ t_j :=
        disjoint_cylinderCuffs.ne_of_mem hs_j_cuff1 ht_j_cuff2
      have hti_ne : t_j ≠ s_i :=
        disjoint_cylinderCuffs.symm.ne_of_mem ht_j_cuff2 (cylinderM1Point_mem_cylinderCuff1 k i)
      have ht_j_G : t_j ∈ G.V := by
        have ht_bd : t_j ∈ cylinderM1 k ∪ cylinderM2 k := Or.inr (M'.curve_one_mem j)
        rw [← hG.2.2] at ht_bd
        exact ht_bd.1
      have ht_j_diff : t_j ∈ G.V \ {s_i} := ⟨ht_j_G, hti_ne⟩
      have hpi_tj : π_map t_j = t_j := hpi_bd t_j (by rw [bd_closedCylinder]; exact Or.inr ht_j_cuff2)
      rcases (M'.isPath j).1 with ⟨W'_P, hW'_P_simple, hPV, hPE⟩
      obtain ⟨W', hW'_sup, hW'_edg⟩ := (M'.isSubdrawing j).1.exists_walk_up W'_P
      have hW'_simple : W'.IsSimple := by
        unfold GraphWalk.IsSimple; rw [hW'_sup]; exact hW'_P_simple
      have hW'_U : (walkDrawing G' W').U = (M'.pathDrawing j).U := by
        have h_eq : walkDrawing G' W' = M'.pathDrawing j := by
          apply Drawing.ext_of_V_E
          · rw [walkDrawing_V, hW'_sup, hPV]
          · rw [walkDrawing_E, hW'_edg, hPE]
        rw [h_eq]
      obtain ⟨x₁, hx₁, x₂, hx₂, W_raw, hpi_1, hpi_2, hsup_map, hV_raw, hU_raw⟩ := hlift_walk W'
      rw [hW'_U] at hU_raw
      have hx₂_eq : x₂ = t_j := hinj_V hx₂ ht_j_diff (hpi_2.trans hpi_tj.symm)
      subst hx₂_eq
      have hW_raw_simple : W_raw.IsSimple := by
        have hnd : (W_raw.support.map π_map).Nodup := by
          rw [hsup_map]; exact hW'_simple
        exact List.Nodup.of_map π_map hnd
      have hwalk_exists : ∃ W_j : GraphWalk G.toGraph s_j t_j,
          W_j.IsSimple ∧ (walkDrawing G W_j).U ⊆ π_map ⁻¹' (M'.pathDrawing j).U := by
        rcases eq_or_ne j i with rfl | hj_ne
        · have hx₁_eq : x₁ = v := hinj_V hx₁ hv_mem_diff (hpi_1.trans hpi_v.symm)
          subst hx₁_eq
          let W_i : GraphWalk G.toGraph s_i t_j := GraphWalk.cons hlink W_raw
          have hsi_not_sup : s_i ∉ W_raw.support := fun h => (hV_raw s_i h).2 rfl
          have hWi_simple : W_i.IsSimple := by
            unfold GraphWalk.IsSimple
            rw [GraphWalk.support_cons]
            exact List.nodup_cons.mpr ⟨hsi_not_sup, hW_raw_simple⟩
          refine ⟨W_i, hWi_simple, ?_⟩
          intro p hp
          rw [mem_walkDrawing_U, GraphWalk.support_cons, GraphWalk.edges_cons] at hp
          simp only [List.mem_cons] at hp
          have hsi_mem_P' : s_i ∈ (M'.pathDrawing j).U := by
            rw [← (M'.curve_parametrizes j).2.1]
            exact ⟨0, (M'.curve_parametrizes j).2.2.1⟩
          rcases hp with (rfl | hp_sup) | ⟨e₁, rfl | he₁, hpe₁⟩
          · rw [mem_preimage, hpi_si]; exact hsi_mem_P'
          · exact hU_raw (by rw [mem_walkDrawing_U]; exact Or.inl hp_sup)
          · rw [mem_preimage]
            have : π_map p = s_i := by rw [← hpre] at hpe₁; exact hpe₁
            rw [this]; exact hsi_mem_P'
          · exact hU_raw (by rw [mem_walkDrawing_U]; exact Or.inr ⟨e₁, he₁, hpe₁⟩)
        · have hsj_ne_si : s_j ≠ s_i := (cylinderM1Point_injective hk).ne hj_ne
          have hsj_G : s_j ∈ G.V := by
            have hs_bd : s_j ∈ cylinderM1 k ∪ cylinderM2 k := Or.inl ⟨j, rfl⟩
            rw [← hG.2.2] at hs_bd
            exact hs_bd.1
          have hsj_diff : s_j ∈ G.V \ {s_i} := ⟨hsj_G, hsj_ne_si⟩
          have hpi_sj : π_map s_j = s_j := hpi_bd s_j (cylinderM1Point_mem_bd k j)
          have hx₁_eq : x₁ = s_j := hinj_V hx₁ hsj_diff (hpi_1.trans hpi_sj.symm)
          subst hx₁_eq
          exact ⟨W_raw, hW_raw_simple, hU_raw⟩
      obtain ⟨W_j, hWj_simple, hWj_U⟩ := hwalk_exists
      let P_j := walkDrawing G W_j
      have hPj_sub : P_j.IsSubdrawing G := walkDrawing_isSubdrawing G W_j
      have hPj_path : IsPathDrawing P_j s_j t_j :=
        isPathDrawing_walkDrawing_of_isSimple G hWj_simple hst_ne
      obtain ⟨f_j, hfj_param⟩ := hPj_path.2
      have hfj0_bd : f_j 0 ∈ bd ClosedCylinder := by
        rw [hfj_param.2.2.1]; exact cylinderM1Point_mem_bd k j
      have hfj1_bd : f_j 1 ∈ bd ClosedCylinder := by
        rw [hfj_param.2.2.2, bd_closedCylinder]; exact Or.inr ht_j_cuff2
      have hhom₁ : CurvesHomotopic f_j (π_map.comp f_j) :=
        curvesHomotopic_comp_pi_map hH0 hH1 hHbd hfj0_bd hfj1_bd
      have hcomp_range : range (π_map.comp f_j) ⊆ (M'.pathDrawing j).U := by
        rintro _ ⟨t, rfl⟩
        apply hWj_U
        rw [← hfj_param.2.1]
        exact ⟨t, rfl⟩
      have hcomp0 : (π_map.comp f_j) 0 = s_j := by
        change π_map (f_j 0) = s_j
        rw [hfj_param.2.2.1, hpi_bd s_j (cylinderM1Point_mem_bd k j)]
      have hcomp1 : (π_map.comp f_j) 1 = t_j := by
        change π_map (f_j 1) = t_j
        rw [hfj_param.2.2.2, hpi_tj]
      have hhom₂ : CurvesHomotopicIn (M'.pathDrawing j).U (π_map.comp f_j) (M'.curve j) :=
        curvesHomotopicIn_of_range_subset_parametrizesSet
          (M'.curve_parametrizes j) hcomp_range hcomp0 hcomp1
      have hhom₂_univ : CurvesHomotopic (π_map.comp f_j) (M'.curve j) := by
        rcases hhom₂ with ⟨ψ, _, hψ0, hψ1, hψy0, hψy0', hψy1, hψy1'⟩
        exact ⟨ψ, fun _ => trivial, hψ0, hψ1, hψy0, hψy0', hψy1, hψy1'⟩
      have hwf : windingNumber f_j = θ + 1 / (k : ℝ) := by
        rw [windingNumber_eq_of_homotopic hhom₁, windingNumber_eq_of_homotopic hhom₂_univ, hM' j]
      exact ⟨P_j, f_j, hPj_sub, hPj_sub.U_subset, hPj_path, hfj_param, hWj_U, hwf⟩
    choose P_fam f_fam hP_sub hP_U hP_path hP_param hP_pre hP_wind using hex_P
    refine ⟨{
      pathDrawing := P_fam
      curve := f_fam
      isSubdrawing := fun j => ⟨hP_sub j, hP_U j⟩
      isPath := fun j => by
        rw [(hP_param j).2.2.2]
        exact hP_path j
      curve_parametrizes := fun j => by
        have h := hP_param j
        rwa [← h.2.2.2] at h
      curve_one_mem := fun j => by
        rw [(hP_param j).2.2.2]
        exact M'.curve_one_mem j
      pairwise_disjoint := fun j₁ j₂ hj₁₂ => by
        dsimp only
        rw [Set.disjoint_left]
        intro x hx₁ hx₂
        exact Set.disjoint_left.mp (M'.pairwise_disjoint hj₁₂)
          (hP_pre j₁ hx₁) (hP_pre j₂ hx₂)
    }, hP_wind⟩
  · exact theorem_5_4_red124 k G G' L L' θ θ' hG hL hL' (Or.inr (Or.inr h4)) hFeas'

end GraphMinor.GM06
