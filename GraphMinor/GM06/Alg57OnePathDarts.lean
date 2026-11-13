module

public import GraphMinor.GM06.Alg57OnePathIncidence
public import GraphMinor.GM06.Alg57CornerAtVertex

/-!
# The two sides of the one path, read on darts

`lifted_incidence_chart` reads the lifted incidence at an inner point of `P₁` in a path chart:
the left arc of directions `[F, B)` belongs to `Γ₁`, the right arc `[B, F)` to `Γ₂`. To read it on
the darts of the capped drawing, we must know which darts point along `F` and `B`.

The tool is a simple fact about arcs (`side_of_isPreconnected`). Remove a point `f s` from the arc
`f '' [0, 1]`. A connected set in what is left lies before `f s` or after it. In a path chart the
ray of `F` lies after the centre and the ray of `B` before it (`IsPathChart.ray_F_side`). So a
direction whose ray meets the part after the centre is `F` (`IsPathChart.eq_F`), and one whose
ray meets the part before it is `B`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

section Arc

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f : ℝ → Y}

/-- **A connected set off a point of an arc lies on one side of it.** -/
theorem side_of_isPreconnected (hf : Continuous f) (hinj : InjOn f (Icc 0 1)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {C : Set Y} (hC : IsPreconnected C) (hCX : C ⊆ f '' Icc 0 1)
    (hsC : f s ∉ C) : C ⊆ f '' Ico 0 s ∨ C ⊆ f '' Ioc s 1 := by
  have hA : IsClosed (f '' Icc 0 s) := (isCompact_Icc.image hf).isClosed
  have hB : IsClosed (f '' Icc s 1) := (isCompact_Icc.image hf).isClosed
  have hcov : C ⊆ f '' Icc 0 s ∪ f '' Icc s 1 := by
    rw [← image_union, Icc_union_Icc_eq_Icc hs.1 hs.2]
    exact hCX
  have hdisj : C ∩ (f '' Icc 0 s ∩ f '' Icc s 1) = ∅ := by
    ext y
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨hyC, ⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
    have huv : v = u := hinj ⟨by linarith [hs.1, hv.1], hv.2⟩ ⟨hu.1, by linarith [hu.2, hs.2]⟩ hvu
    subst huv
    have hvs : v = s := le_antisymm hu.2 hv.1
    subst hvs
    exact hsC hyC
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hC) _ _ hA hB hcov hdisj with h | h
  · left
    intro y hy
    obtain ⟨u, hu, rfl⟩ := h hy
    refine ⟨u, ⟨hu.1, lt_of_le_of_ne hu.2 ?_⟩, rfl⟩
    rintro rfl
    exact hsC hy
  · right
    intro y hy
    obtain ⟨u, hu, rfl⟩ := h hy
    refine ⟨u, ⟨lt_of_le_of_ne hu.1 ?_, hu.2⟩, rfl⟩
    rintro rfl
    exact hsC hy

/-- A connected set off `f s` whose closure contains a later point of the arc lies after `f s`. -/
theorem subset_Ioc_side (hf : Continuous f) (hinj : InjOn f (Icc 0 1)) {s t₁ : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (hst : s < t₁) {C : Set Y}
    (hC : IsPreconnected C) (hCX : C ⊆ f '' Icc 0 1) (hsC : f s ∉ C) (hcl : f t₁ ∈ closure C) :
    C ⊆ f '' Ioc s 1 := by
  rcases side_of_isPreconnected hf hinj hs hC hCX hsC with h | h
  · exfalso
    obtain ⟨u, hu, hu'⟩ := closure_minimal (h.trans (image_mono Ico_subset_Icc_self))
      (isCompact_Icc.image hf).isClosed hcl
    have := hinj ⟨hu.1, hu.2.trans hs.2⟩ ht₁ hu'
    linarith [hu.2]
  · exact h

/-- A connected set off `f s` whose closure contains an earlier point of the arc lies before
`f s`. -/
theorem subset_Ico_side (hf : Continuous f) (hinj : InjOn f (Icc 0 1)) {s t₁ : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (hst : t₁ < s) {C : Set Y}
    (hC : IsPreconnected C) (hCX : C ⊆ f '' Icc 0 1) (hsC : f s ∉ C) (hcl : f t₁ ∈ closure C) :
    C ⊆ f '' Ico 0 s := by
  rcases side_of_isPreconnected hf hinj hs hC hCX hsC with h | h
  · exact h
  · exfalso
    obtain ⟨u, hu, hu'⟩ := closure_minimal (h.trans (image_mono Ioc_subset_Icc_self))
      (isCompact_Icc.image hf).isClosed hcl
    have := hinj ⟨hs.1.trans hu.1, hu.2⟩ ht₁ hu'
    linarith [hu.1]

/-- The two sides of a point of an arc are disjoint. -/
theorem disjoint_sides (hinj : InjOn f (Icc 0 1)) (s : ℝ) :
    Disjoint (f '' Ico 0 s) (f '' Ioc s 1) := by
  rw [disjoint_left]
  rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
  have := hinj ⟨hu.1.trans (le_of_lt (hu.2.trans hv.1)), hv.2⟩
    ⟨hu.1, (hu.2.trans hv.1).le.trans hv.2⟩ hvu
  linarith [hu.2, hv.1]

end Arc

section Chart

variable {Γ : Drawing (OnePoint EuclideanPlane)} {X : Set (OnePoint EuclideanPlane)}
  {f : ℝ → OnePoint EuclideanPlane} {t : ℝ} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
  {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {F B : Circle}

theorem continuous_ray (Ψ : C(ClosedUnitDisc, EuclideanPlane)) (W : Circle) :
    Continuous fun r : ℝ => toSph (chartC Ψ ((r : ℂ) * W)) :=
  continuous_toSph.comp (continuous_chartC.comp (by fun_prop))

/-- A point of a ray of a polar chart is not its centre. -/
theorem ray_ne_centre {c : OnePoint EuclideanPlane} (hp : IsPolar Γ c Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (W : Circle) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) : toSph (chartC Ψ ((r : ℂ) * W)) ≠ c := by
  rw [← toSph_chartC_zero hp hΨ]
  intro h
  have hn : ‖(r : ℂ) * W‖ = r := by
    rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le]
  have h0 := chartC_injOn hΨ hp.inj (mem_closedBall_zero_iff.mpr (by rw [hn]; exact hr1))
    (mem_closedBall_zero_iff.mpr (by simp)) (toSph_injective h)
  have := congrArg norm h0
  rw [hn, norm_zero] at this
  linarith

namespace IsPathChart

variable (hc : IsPathChart Γ X f t Φ Ψ F B) (ht : t ∈ Ioo (0 : ℝ) 1) (hX : IsGammaNice Γ X)
  (hf : Continuous f) (hinj : InjOn f (Icc 0 1)) (hXf : X = f '' Icc 0 1)
include hc ht hX hf hinj hXf

/-- **The ray of `F` lies after the centre.** -/
theorem ray_F_side {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    toSph (chartC Ψ ((r : ℂ) * F)) ∈ f '' Ioc t 1 := by
  have hfX : ∀ s ∈ Icc (0 : ℝ) 1, f s ∈ X := fun s hs => hXf ▸ ⟨s, hs, rfl⟩
  have hFX := (hc.rim_mem ht hX hfX).1
  obtain ⟨δ, hδ, ρ, -, hρ0, hmono, hρG⟩ := hc.out
  set ε := min δ ((1 - t) / 2)
  have hε : 0 < ε := lt_min hδ (by linarith [ht.2])
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ (1 - t) / 2 := min_le_right _ _
  have hpos : 0 < ρ (t + ε) := by
    rw [← hρ0]
    exact hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  obtain ⟨hρ1, hG⟩ := hρG (t + ε) ⟨by linarith, by linarith⟩
  set C := (fun r : ℝ => toSph (chartC Ψ ((r : ℂ) * F))) '' Ioc 0 1
  have hCX : C ⊆ f '' Icc 0 1 := by
    rintro _ ⟨r', hr', rfl⟩
    rw [← hXf]
    exact (chart_ray_mem_iff hc.polar hc.hΨ hX F hr'.1 hr'.2).mpr hFX
  have hsC : f t ∉ C := by
    rintro ⟨r', hr', he⟩
    exact ray_ne_centre hc.polar hc.hΨ F hr'.1 hr'.2 he
  have hpC : f (t + ε) ∈ C := ⟨_, ⟨hpos, hρ1.le⟩, hG.symm⟩
  rcases side_of_isPreconnected hf hinj ⟨ht.1.le, ht.2.le⟩
      (isPreconnected_Ioc.image _ (continuous_ray Ψ F).continuousOn) hCX hsC with h | h
  · exfalso
    exact disjoint_left.mp (disjoint_sides hinj t) (h hpC)
      ⟨t + ε, ⟨by linarith, by linarith⟩, rfl⟩
  · exact h ⟨r, ⟨hr, hr1⟩, rfl⟩

/-- **The ray of `B` lies before the centre.** -/
theorem ray_B_side {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    toSph (chartC Ψ ((r : ℂ) * B)) ∈ f '' Ico 0 t := by
  have hfX : ∀ s ∈ Icc (0 : ℝ) 1, f s ∈ X := fun s hs => hXf ▸ ⟨s, hs, rfl⟩
  have hBX := (hc.rim_mem ht hX hfX).2
  obtain ⟨δ, hδ, ρ, -, hρ0, hanti, hρG⟩ := hc.inn
  set ε := min δ (t / 2)
  have hε : 0 < ε := lt_min hδ (by linarith [ht.1])
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ t / 2 := min_le_right _ _
  have hpos : 0 < ρ (t - ε) := by
    rw [← hρ0]
    exact hanti ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  obtain ⟨hρ1, hG⟩ := hρG (t - ε) ⟨by linarith, by linarith⟩
  set C := (fun r : ℝ => toSph (chartC Ψ ((r : ℂ) * B))) '' Ioc 0 1
  have hCX : C ⊆ f '' Icc 0 1 := by
    rintro _ ⟨r', hr', rfl⟩
    rw [← hXf]
    exact (chart_ray_mem_iff hc.polar hc.hΨ hX B hr'.1 hr'.2).mpr hBX
  have hsC : f t ∉ C := by
    rintro ⟨r', hr', he⟩
    exact ray_ne_centre hc.polar hc.hΨ B hr'.1 hr'.2 he
  have hpC : f (t - ε) ∈ C := ⟨_, ⟨hpos, hρ1.le⟩, hG.symm⟩
  rcases side_of_isPreconnected hf hinj ⟨ht.1.le, ht.2.le⟩
      (isPreconnected_Ioc.image _ (continuous_ray Ψ B).continuousOn) hCX hsC with h | h
  · exact h ⟨r, ⟨hr, hr1⟩, rfl⟩
  · exfalso
    exact disjoint_left.mp (disjoint_sides hinj t) ⟨t - ε, ⟨by linarith, by linarith⟩, rfl⟩
      (h hpC)

/-- **A direction of the path whose ray meets the part after the centre is `F`.** -/
theorem eq_F {W : Circle} (hW : polarRimMap Φ W ∈ X) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hmem : toSph (chartC Ψ ((r : ℂ) * W)) ∈ f '' Ioc t 1) : W = F := by
  rcases hc.dirs W hW with h | h
  · exact h
  · subst h
    exact absurd hmem (disjoint_left.mp (disjoint_sides hinj t)
      (hc.ray_B_side ht hX hf hinj hXf hr hr1))

/-- **A direction of the path whose ray meets the part before the centre is `B`.** -/
theorem eq_B {W : Circle} (hW : polarRimMap Φ W ∈ X) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hmem : toSph (chartC Ψ ((r : ℂ) * W)) ∈ f '' Ico 0 t) : W = B := by
  rcases hc.dirs W hW with h | h
  · subst h
    exact absurd (hc.ray_F_side ht hX hf hinj hXf hr hr1)
      (disjoint_left.mp (disjoint_sides hinj t) hmem)
  · exact h

end IsPathChart

end Chart

section Block

/-- Turning on from `w` by `g`, not past `F`, adds `g` to the angle from `F`. -/
theorem angleTo_step {F w : Circle} (hwF : w ≠ F) {g : ℝ} (hg : 0 < g) (hle : g ≤ angleTo w F)
    (hne : w * Circle.exp g ≠ F) : angleTo F (w * Circle.exp g) = angleTo F w + g := by
  have hsw := angleTo_swap hwF.symm
  have hpos := angleTo_pos F w
  have heq : w * Circle.exp g = F * Circle.exp (angleTo F w + g) := by
    rw [Circle.exp_add, ← mul_assoc, mul_exp_angleTo]
  have hlt : angleTo F w + g < 2 * Real.pi := by
    refine lt_of_le_of_ne (by linarith) fun h2 => hne ?_
    rw [heq, h2, Circle.exp_two_pi, mul_one]
  exact angleTo_eq ⟨by linarith, hlt.le⟩ heq

/-- The angle from `w` to `u` is the difference of their angles from `F`, when `w` comes first. -/
theorem angleTo_sub {F w u : Circle} (hlt : angleTo F w < angleTo F u) :
    angleTo w u = angleTo F u - angleTo F w := by
  have h1 := angleTo_pos F w
  have h2 := angleTo_le F u
  refine angleTo_eq ⟨by linarith, by linarith⟩ ?_
  have hw : F * Circle.exp (angleTo F w) = w := mul_exp_angleTo F w
  calc u = F * Circle.exp (angleTo F u) := (mul_exp_angleTo F u).symm
    _ = F * Circle.exp (angleTo F w) * Circle.exp (angleTo F u - angleTo F w) := by
        rw [mul_assoc, ← Circle.exp_add, add_sub_cancel]
    _ = w * Circle.exp (angleTo F u - angleTo F w) := by rw [hw]

variable {Γ : Drawing (OnePoint EuclideanPlane)}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart Γ)} {v : OnePoint EuclideanPlane}
  {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {z : DrawingDart Γ → Circle}

theorem dartVertex_rot_iterate (hR : IsDrawingRotation Γ γ R) (b : DrawingDart Γ) (i : ℕ) :
    dartVertex γ (R.rot^[i] b) = dartVertex γ b := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', hR.vertex_rot, ih]

/-- **The arc from `z b` to `z a` is the block from `b` to `a`.** At a vertex with a
counterclockwise star, the darts whose directions lie in the arc `[z b, z a)` are the darts
`b, R.rot b, R.rot² b, …` met before `a`. -/
theorem IsCcwStar.arc_iff_block (h : IsCcwStar Γ γ R v Φ z) (hγ : EdgePar Γ γ)
    (hR : IsDrawingRotation Γ γ R) {a b d : DrawingDart Γ} (ha : dartVertex γ a = v)
    (hb : dartVertex γ b = v) (hd : dartVertex γ d = v) (hab : b ≠ a) :
    (z d = z b ∨ angleTo (z b) (z d) < angleTo (z b) (z a)) ↔
      ∃ i, (∀ j ≤ i, R.rot^[j] b ≠ a) ∧ R.rot^[i] b = d := by
  classical
  have hD := h.rimDirs_finite hγ
  have hzab : z a ≠ z b := fun e => hab (h.inj _ _ hb ha e.symm)
  have haD : z a ∈ rimDirs Γ Φ := h.mem_rimDirs hγ ha
  have hbD : z b ∈ rimDirs Γ Φ := h.mem_rimDirs hγ hb
  have hαa : angleTo (z b) (z a) < 2 * Real.pi := by
    refine lt_of_le_of_ne (angleTo_le _ _) fun h2 => hzab ?_
    rw [← mul_exp_angleTo (z b) (z a), h2, Circle.exp_two_pi, mul_one]
  have hiv := dartVertex_rot_iterate hR b
  constructor
  · intro hleft
    let β : Circle → ℝ := fun w => if w = z b then 0 else angleTo (z b) w
    suffices key : ∀ n : ℕ, ∀ d, dartVertex γ d = v →
        (z d = z b ∨ angleTo (z b) (z d) < angleTo (z b) (z a)) →
        {u ∈ rimDirs Γ Φ | β u < β (z d)}.ncard = n →
        ∃ i, (∀ j ≤ i, R.rot^[j] b ≠ a) ∧ R.rot^[i] b = d from key _ d hd hleft rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
    intro d hd hl hn
    by_cases hdb : d = b
    · refine ⟨0, fun j hj => ?_, hdb.symm⟩
      rw [Nat.le_zero.mp hj]
      exact hab
    have hp : dartVertex γ (R.rot.symm d) = v := by
      rw [← hd, ← hR.vertex_rot (R.rot.symm d), Equiv.apply_symm_apply]
    have hprev := h.prev_eq hγ hR hd
    have hzd : z d ≠ z b := fun e => hdb (h.inj _ _ hd hb e)
    have hαd : angleTo (z b) (z d) < angleTo (z b) (z a) := hl.resolve_left hzd
    have hβd : β (z d) = angleTo (z b) (z d) := (if_neg hzd)
    have hg := gap_pos hD (z (R.rot.symm d))
    obtain ⟨hlp, hβ⟩ : (z (R.rot.symm d) = z b ∨
        angleTo (z b) (z (R.rot.symm d)) < angleTo (z b) (z a)) ∧
        β (z (R.rot.symm d)) < β (z d) := by
      by_cases hpb : z (R.rot.symm d) = z b
      · refine ⟨Or.inl hpb, ?_⟩
        have : β (z (R.rot.symm d)) = 0 := if_pos hpb
        rw [this, hβd]
        exact angleTo_pos _ _
      · have hstep := angleTo_step hpb hg (gap_le_angleTo hD _ hbD) (by rw [hprev]; exact hzd)
        rw [hprev] at hstep
        refine ⟨Or.inr (by linarith), ?_⟩
        have : β (z (R.rot.symm d)) = angleTo (z b) (z (R.rot.symm d)) := if_neg hpb
        rw [this, hβd]
        linarith
    have hfin : {u ∈ rimDirs Γ Φ | β u < β (z d)}.Finite := hD.subset (sep_subset _ _)
    have hlt : {u ∈ rimDirs Γ Φ | β u < β (z (R.rot.symm d))}.ncard <
        {u ∈ rimDirs Γ Φ | β u < β (z d)}.ncard := by
      apply Set.ncard_lt_ncard _ hfin
      have hsub : {u ∈ rimDirs Γ Φ | β u < β (z (R.rot.symm d))} ⊆
          {u ∈ rimDirs Γ Φ | β u < β (z d)} := fun u hu => ⟨hu.1, hu.2.trans hβ⟩
      rw [Set.ssubset_iff_of_subset hsub]
      exact ⟨z (R.rot.symm d), (⟨h.mem_rimDirs hγ hp, hβ⟩ :
        z (R.rot.symm d) ∈ {u ∈ rimDirs Γ Φ | β u < β (z d)}), fun hu => lt_irrefl _ hu.2⟩
    obtain ⟨i, hi, hip⟩ := IH _ (hn ▸ hlt) _ hp hlp rfl
    have hsucc : R.rot^[i + 1] b = d := by
      rw [Function.iterate_succ_apply', hip, Equiv.apply_symm_apply]
    refine ⟨i + 1, fun j hj => ?_, hsucc⟩
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact hi j (by omega)
    · rw [hsucc]
      rintro rfl
      exact lt_irrefl _ hαd
  · rintro ⟨i, hi, rfl⟩
    induction i with
    | zero => exact Or.inl rfl
    | succ i ih =>
      have IH := ih (fun j hj => hi j (by omega)) ((hiv i).trans hb)
      set w := z (R.rot^[i] b)
      have hnext : w * Circle.exp (gap (rimDirs Γ Φ) w) = z (R.rot^[i + 1] b) := by
        rw [Function.iterate_succ_apply']
        exact h.next_eq hγ hR ((hiv i).trans hb)
      have hne : z (R.rot^[i + 1] b) ≠ z a := fun e =>
        hi (i + 1) le_rfl (h.inj _ _ ((hiv (i + 1)).trans hb) ha e)
      have hg := gap_pos hD w
      by_cases hnb : z (R.rot^[i + 1] b) = z b
      · exact Or.inl hnb
      right
      have hle := gap_le_angleTo hD w haD
      by_cases hwb : w = z b
      · have hgle : gap (rimDirs Γ Φ) w ≤ angleTo (z b) (z a) := hwb ▸ hle
        have hα : angleTo (z b) (z (R.rot^[i + 1] b)) = gap (rimDirs Γ Φ) w := by
          rw [← hnext]
          exact angleTo_eq ⟨hg, by linarith⟩ (by rw [hwb])
        rw [hα]
        refine lt_of_le_of_ne hgle fun h2 => hne ?_
        rw [← hnext, h2, hwb, mul_exp_angleTo]
      · have hαw := IH.resolve_left hwb
        have hsub := angleTo_sub hαw
        have hstep := angleTo_step hwb hg (gap_le_angleTo hD w hbD) (by rw [hnext]; exact hnb)
        rw [hnext] at hstep
        rw [hstep]
        refine lt_of_le_of_ne (by linarith) fun h2 => hne ?_
        rw [← mul_exp_angleTo (z b) (z (R.rot^[i + 1] b)), hstep, h2, mul_exp_angleTo]

end Block

section DartSide

variable {Γ : Drawing (OnePoint EuclideanPlane)}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {f : ℝ → OnePoint EuclideanPlane} {X : Set (OnePoint EuclideanPlane)}

theorem dartFlip_dartFlip (d : DrawingDart Γ) : dartFlip Γ (dartFlip Γ d) = d := by
  apply Subtype.ext
  simp [dartFlip]

/-- The head of a dart lies in the closure of its edge. -/
theorem dartCurve_one_mem_closure (hγ : EdgePar Γ γ) (d : DrawingDart Γ) {a : ℝ} (ha : a < 1) :
    dartCurve γ d 1 ∈ closure (dartCurve γ d '' Ioo a 1) :=
  (isEdgeCurve_dartCurve hγ d).cont.continuousWithinAt.mem_closure_image
    (by rw [closure_Ioo ha.ne]; exact right_mem_Icc.mpr ha.le)

theorem dartCurve_one (d : DrawingDart Γ) : dartCurve γ d 1 = dartVertex γ (dartFlip Γ d) := by
  rw [← dartCurve_zero, dartCurve_flip, sub_zero]

/-- **An edge along an arc lies on the side of its head.** -/
theorem dart_subset_side (hγ : EdgePar Γ γ) (hf : Continuous f) (hinj : InjOn f (Icc 0 1))
    (d : DrawingDart Γ) {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1)
    (hdX : d.1.1 ⊆ f '' Icc 0 1) (h0 : dartVertex γ d = f t₀)
    (h1 : dartVertex γ (dartFlip Γ d) = f t₁) :
    (t₀ < t₁ → d.1.1 ⊆ f '' Ioc t₀ 1) ∧ (t₁ < t₀ → d.1.1 ⊆ f '' Ico 0 t₀) := by
  have hE := isEdgeCurve_dartCurve hγ d
  have hC : IsPreconnected d.1.1 := hE.image ▸ isPreconnected_Ioo.image _ hE.cont.continuousOn
  have hsC : f t₀ ∉ d.1.1 := fun hm => (d.2.2.1 hm).2 (h0 ▸ dartVertex_mem hγ d)
  have hcl : f t₁ ∈ closure d.1.1 := by
    rw [← h1, ← dartCurve_one, ← hE.image]
    exact dartCurve_one_mem_closure hγ d zero_lt_one
  exact ⟨fun h => subset_Ioc_side hf hinj ht₀ ht₁ h hC hdX hsC hcl,
    fun h => subset_Ico_side hf hinj ht₀ ht₁ h hC hdX hsC hcl⟩

variable {R : DartRotation (DrawingDart Γ)} {t : ℝ} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
  {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {F B : Circle} {z : DrawingDart Γ → Circle}

/-- **In a star that is a path chart, the dart along the path forward points along `F`, the dart
along it backward along `B`.** -/
theorem IsCcwStar.dir_eq (hst : IsCcwStar Γ γ R (f t) Φ z) (hγ : EdgePar Γ γ)
    (hc : IsPathChart Γ X f t Φ Ψ F B) (ht : t ∈ Ioo (0 : ℝ) 1) (hX : IsGammaNice Γ X)
    (hf : Continuous f) (hinj : InjOn f (Icc 0 1)) (hXf : X = f '' Icc 0 1)
    {b : DrawingDart Γ} (hb : dartVertex γ b = f t) (hbX : b.1.1 ⊆ X) {t₁ : ℝ}
    (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (h1 : dartVertex γ (dartFlip Γ b) = f t₁) :
    (t < t₁ → z b = F) ∧ (t₁ < t → z b = B) := by
  have hray := hst.ray_mem_edge hγ hc.hΨ hb one_pos le_rfl
  have hrim : polarRimMap Φ (z b) ∈ X :=
    (chart_ray_mem_iff hc.polar hc.hΨ hX _ one_pos le_rfl).mp (hbX hray)
  have hside := dart_subset_side hγ hf hinj b ⟨ht.1.le, ht.2.le⟩ ht₁ (hXf ▸ hbX) hb h1
  exact ⟨fun h => hc.eq_F ht hX hf hinj hXf hrim one_pos le_rfl (hside.1 h hray),
    fun h => hc.eq_B ht hX hf hinj hXf hrim one_pos le_rfl (hside.2 h hray)⟩

/-- **A dart along the path, read in a path chart at an inner point of its edge.** If the edge of
`d` runs out along `W` there, then `W` is `F` when the head of `d` comes later on the path, and
`B` when it comes earlier. -/
theorem IsPathChart.runsOut_dart_eq (hc : IsPathChart Γ X f t Φ Ψ F B) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hX : IsGammaNice Γ X) (hf : Continuous f) (hinj : InjOn f (Icc 0 1))
    (hXf : X = f '' Icc 0 1) (hγ : EdgePar Γ γ) {d : DrawingDart Γ} (hdX : d.1.1 ⊆ X) {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hda : dartCurve γ d a = f t) {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1)
    (h1 : dartVertex γ (dartFlip Γ d) = f t₁) {W : Circle} {δ : ℝ}
    (hrun : RunsOut Ψ W (dartCurve γ d) a δ) : (t < t₁ → W = F) ∧ (t₁ < t → W = B) := by
  have hE := isEdgeCurve_dartCurve hγ d
  set C := dartCurve γ d '' Ioo a 1
  have hCd : C ⊆ d.1.1 := hE.image ▸ image_mono (Ioo_subset_Ioo_left ha.1.le)
  have hC : IsPreconnected C := isPreconnected_Ioo.image _ hE.cont.continuousOn
  have hCX : C ⊆ f '' Icc 0 1 := hXf ▸ hCd.trans hdX
  have hsC : f t ∉ C := by
    rintro ⟨u, hu, he⟩
    have := hE.inj ⟨ha.1.trans hu.1, hu.2⟩ ha (he.trans hda.symm)
    linarith [hu.1]
  have hcl : f t₁ ∈ closure C := by
    rw [← h1, ← dartCurve_one]
    exact dartCurve_one_mem_closure hγ d ha.2
  obtain ⟨hδ, ρ, -, hρ0, hmono, hρG⟩ := hrun
  set ε := min δ ((1 - a) / 2)
  have hε : 0 < ε := lt_min hδ (by linarith [ha.2])
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ (1 - a) / 2 := min_le_right _ _
  have hpos : 0 < ρ (a + ε) := by
    rw [← hρ0]
    exact hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  obtain ⟨hρ1, hG⟩ := hρG (a + ε) ⟨by linarith, by linarith⟩
  have hpC : dartCurve γ d (a + ε) ∈ C := ⟨a + ε, ⟨by linarith, by linarith [ha.2]⟩, rfl⟩
  have hrim : polarRimMap Φ W ∈ X :=
    (chart_ray_mem_iff hc.polar hc.hΨ hX W hpos hρ1.le).mp (hG ▸ hdX (hCd hpC))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hside := subset_Ioc_side hf hinj ⟨ht.1.le, ht.2.le⟩ ht₁ h hC hCX hsC hcl
    exact hc.eq_F ht hX hf hinj hXf hrim hpos hρ1.le (hG ▸ hside hpC)
  · have hside := subset_Ico_side hf hinj ⟨ht.1.le, ht.2.le⟩ ht₁ h hC hCX hsC hcl
    exact hc.eq_B ht hX hf hinj hXf hrim hpos hρ1.le (hG ▸ hside hpC)

end DartSide

section Incidence

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}
  (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
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
  (hV : ∀ v ∈ (cylinderSphereDrawing H).V, ∃ a : DrawingDart (cylinderSphereDrawing H),
    dartVertex γ a = v)
  {ρ : DrawingDart (cylinderSphereDrawing H) → Set (OnePoint EuclideanPlane)}
  (hform : ∀ d, ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
    (z : DrawingDart (cylinderSphereDrawing H) → Circle),
    IsCcwStar (cylinderSphereDrawing H) γ R (dartVertex γ d) Φ z ∧
      ρ d = cornerRegion (cylinderSphereDrawing H) Φ (z d))

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI hγI hV hform in
/-- **The lifted incidence at an inner vertex of `P₁`** (Lemma 11 for `k = 1`). Let `x = P₁(t)` be
a vertex of `P₁` other than its ends. Let `b` be the dart at `x` along `P₁` forward and `a` the
dart at `x` along `P₁` backward. Then `Γ₁(t)` is in the closure of `R̃₁` exactly when the corner
after some dart of the block `b, R.rot b, …` before `a` is `R₁`. Likewise `Γ₂(t)` and the block
from `a` to `b`. -/
theorem lifted_incidence_vertex {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {a b : DrawingDart (cylinderSphereDrawing H)}
    (hb : dartVertex γ b = spherePath L t) (hbX : b.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (htt₁ : t < t₁)
    (hb1 : dartVertex γ (dartFlip _ b) = spherePath L t₁)
    (ha : dartVertex γ a = spherePath L t) (haX : a.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₂ : ℝ} (ht₂ : t₂ ∈ Icc (0 : ℝ) 1) (htt₂ : t₂ < t)
    (ha1 : dartVertex γ (dartFlip _ a) = spherePath L t₂) :
    (coverLift L hG 1 ⟨t, Ioo_subset_Icc_self ht⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ i, (∀ j ≤ i, R.rot^[j] b ≠ a) ∧
        ρ (R.rot^[i] b) = cylinderToSphere '' (cylinderRegion 1 G 0 \ bd ClosedCylinder)) ∧
    (coverLift L hG 2 ⟨t, Ioo_subset_Icc_self ht⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ i, (∀ j ≤ i, R.rot^[j] a ≠ b) ∧
        ρ (R.rot^[i] a) = cylinderToSphere '' (cylinderRegion 1 G 0 \ bd ClosedCylinder)) := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  have hinf := infty_notMem_cylinderSphereDrawing_U H
  have hX := isGammaNice_spherePath L hGH
  have hXf := (image_spherePath L).symm
  have hf := continuous_spherePath L
  have hinj := injOn_spherePath L
  obtain ⟨O, hO, hxO, hO'⟩ := lifted_incidence_chart L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH
    hFU hFV hγ hR hccw heI hγI hV ht
  obtain ⟨O₂, hO₂, hxO₂, hsmall⟩ := exists_isPathChart_of_small hX (spherePath_subset_U L hGH) hf
    hinj (image_spherePath L).subset (image_spherePath L).symm.subset ht
  obtain ⟨Φ₀, z, hst₀⟩ := hccw (spherePath L t) ⟨b, hb⟩
  obtain ⟨Φ, hst, hsub⟩ := hst₀.exists_small hS (hO.inter hO₂) ⟨hxO, hxO₂⟩
  obtain ⟨Ψ, hΨ, hw⟩ := hst.pos
  have hpos : 0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) := by
    rw [wind_chartC]; exact hw
  obtain ⟨F, B, hc⟩ := hsmall hst.polar hΨ hpos (hst.rimDirs_finite hγ)
    (hsub.trans inter_subset_right)
  have hzb : z b = F := (hst.dir_eq hγ hc ht hX hf hinj hXf hb hbX ht₁ hb1).1 htt₁
  have hza : z a = B := (hst.dir_eq hγ hc ht hX hf hinj hXf ha haX ht₂ ha1).2 htt₂
  have hab : b ≠ a := by
    rintro rfl
    exact hc.ne (hzb.symm.trans hza)
  obtain ⟨h1, h2⟩ := hO' hc (hsub.trans inter_subset_left)
  have hρ : ∀ d, dartVertex γ d = spherePath L t →
      ρ d = cornerRegion (cylinderSphereDrawing H) Φ (z d) := fun d hd =>
    cornerLabel_eq_star hinf hγ hform d (by rw [hd]; exact hst)
  have hdirs := hst.rimDirs_eq hγ
  have hiv : ∀ c, dartVertex γ c = spherePath L t → ∀ i,
      dartVertex γ (R.rot^[i] c) = spherePath L t := fun c hc' i =>
    (dartVertex_rot_iterate hR c i).trans hc'
  constructor
  · rw [h1]
    constructor
    · rintro ⟨w, hw, hl, hcr⟩
      rw [hdirs] at hw
      obtain ⟨d, hd, rfl⟩ := hw
      rw [← hzb, ← hza] at hl
      obtain ⟨i, hi, hid⟩ := (hst.arc_iff_block hγ hR ha hb hd hab).mp hl
      exact ⟨i, hi, by rw [hid, hρ d hd, hcr]⟩
    · rintro ⟨i, hi, hρi⟩
      have hd := hiv b hb i
      refine ⟨z (R.rot^[i] b), hst.mem_rimDirs hγ hd, ?_, by rw [← hρ _ hd]; exact hρi⟩
      rw [← hzb, ← hza]
      exact (hst.arc_iff_block hγ hR ha hb hd hab).mpr ⟨i, hi, rfl⟩
  · rw [h2]
    constructor
    · rintro ⟨w, hw, hl, hcr⟩
      rw [hdirs] at hw
      obtain ⟨d, hd, rfl⟩ := hw
      rw [← hzb, ← hza] at hl
      obtain ⟨i, hi, hid⟩ := (hst.arc_iff_block hγ hR hb ha hd hab.symm).mp hl
      exact ⟨i, hi, by rw [hid, hρ d hd, hcr]⟩
    · rintro ⟨i, hi, hρi⟩
      have hd := hiv a ha i
      refine ⟨z (R.rot^[i] a), hst.mem_rimDirs hγ hd, ?_, by rw [← hρ _ hd]; exact hρi⟩
      rw [← hzb, ← hza]
      exact (hst.arc_iff_block hγ hR hb ha hd hab.symm).mpr ⟨i, hi, rfl⟩

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI hγI hV hform in
/-- **The lifted incidence inside an edge of `P₁`.** Let `d` be a dart of an edge of `P₁` whose
head comes later on `P₁` than its tail, and let `P₁(s)` be a point of its edge. Then `Γ₁(s)` is
in the closure of `R̃₁` exactly when the corner after `d` is `R₁`, and `Γ₂(s)` is in it exactly
when the corner after the reverse of `d` is `R₁`. -/
theorem lifted_incidence_edge {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {d : DrawingDart (cylinderSphereDrawing H)}
    (hdX : d.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (htt : t₀ < t₁)
    (hd0 : dartVertex γ d = spherePath L t₀) (hd1 : dartVertex γ (dartFlip _ d) = spherePath L t₁)
    (hsd : spherePath L s ∈ d.1.1) :
    (coverLift L hG 1 ⟨s, Ioo_subset_Icc_self hs⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ρ d = cylinderToSphere '' (cylinderRegion 1 G 0 \ bd ClosedCylinder)) ∧
    (coverLift L hG 2 ⟨s, Ioo_subset_Icc_self hs⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ρ (dartFlip _ d) = cylinderToSphere '' (cylinderRegion 1 G 0 \ bd ClosedCylinder)) := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  have hinf := infty_notMem_cylinderSphereDrawing_U H
  have hX := isGammaNice_spherePath L hGH
  have hXf := (image_spherePath L).symm
  have hf := continuous_spherePath L
  have hinj := injOn_spherePath L
  have hs' : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
  -- `s` lies strictly between the two ends of the edge
  have hside := dart_subset_side hγ hf hinj d ht₀ ht₁ (hXf ▸ hdX) hd0 hd1
  have hflip0 : dartVertex γ (dartFlip _ (dartFlip _ d)) = spherePath L t₀ := by
    rw [dartFlip_dartFlip]; exact hd0
  have hside' := dart_subset_side hγ hf hinj (dartFlip _ d) ht₁ ht₀ (hXf ▸ hdX) hd1 hflip0
  have hts : t₀ < s := by
    obtain ⟨u, hu, he⟩ := hside.1 htt hsd
    have := hinj ⟨hu.1.le.trans' ht₀.1, hu.2⟩ hs' he
    linarith [hu.1]
  have hst : s < t₁ := by
    obtain ⟨u, hu, he⟩ := hside'.2 htt hsd
    have := hinj ⟨hu.1, hu.2.le.trans ht₁.2⟩ hs' he
    linarith [hu.2]
  have hE := isEdgeCurve_dartCurve hγ d
  obtain ⟨a, ha, hda⟩ : spherePath L s ∈ dartCurve γ d '' Ioo 0 1 := by rw [hE.image]; exact hsd
  obtain ⟨O, hO, hxO, hO'⟩ := lifted_incidence_chart L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH
    hFU hFV hγ hR hccw heI hγI hV hs
  obtain ⟨O₂, hO₂, hxO₂, hsmall⟩ := exists_isPathChart_of_small hX (spherePath_subset_U L hGH) hf
    hinj (image_spherePath L).subset (image_spherePath L).symm.subset hs
  obtain ⟨Φ, Ψ, F', B', δ₁, δ₂, hp, hsub, hΨ, hpos, hdirs, -, hout, hin⟩ :=
    exists_edge_chart_in hS hinf d.2 hE ha (hO.inter hO₂) (by rw [hda]; exact ⟨hxO, hxO₂⟩)
  have hp' : IsPolar (cylinderSphereDrawing H) (spherePath L s) Φ := hda ▸ hp
  have hfin : (rimDirs (cylinderSphereDrawing H) Φ).Finite := by
    rw [hdirs]; exact (finite_singleton _).insert _
  obtain ⟨F, B, hc⟩ := hsmall hp' hΨ hpos hfin (hsub.trans inter_subset_right)
  have hF : F' = F := (hc.runsOut_dart_eq hs hX hf hinj hXf hγ hdX ha hda ht₁ hd1 hout).1 hst
  have hrin : RunsOut Ψ B' (dartCurve γ (dartFlip _ d)) (1 - a) δ₂ := by
    have := hin.runsOut_one_sub
    convert this using 2
    exact dartCurve_flip γ d _
  have ha' : 1 - a ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ha.2], by linarith [ha.1]⟩
  have hda' : dartCurve γ (dartFlip _ d) (1 - a) = spherePath L s := by
    rw [dartCurve_flip, sub_sub_cancel, hda]
  have hB : B' = B := (hc.runsOut_dart_eq hs hX hf hinj hXf hγ (d := dartFlip _ d) (by exact hdX)
    ha' hda' ht₀ hflip0 hrin).2 hts
  subst hF hB
  have hFD : F' ∈ rimDirs (cylinderSphereDrawing H) Φ := by rw [hdirs]; exact mem_insert _ _
  have hBD : B' ∈ rimDirs (cylinderSphereDrawing H) Φ := by
    rw [hdirs]; exact mem_insert_of_mem _ rfl
  have hρd := cornerLabel_eq_mid hinf hγ hform d a ha Φ Ψ hp hΨ hpos hfin F' hFD δ₁ hout
  have hρd' := cornerLabel_eq_mid hinf hγ hform (dartFlip _ d) (1 - a) ha' Φ Ψ (hda'.symm ▸ hp')
    hΨ hpos hfin B' hBD δ₂ hrin
  obtain ⟨h1, h2⟩ := hO' hc (hsub.trans inter_subset_left)
  rw [h1, h2, hρd, hρd', hdirs]
  constructor
  · constructor
    · rintro ⟨w, hw, hl, hcr⟩
      rcases hw with rfl | rfl
      · exact hcr
      · rcases hl with h | h
        · exact absurd h.symm hc.ne
        · exact absurd h (lt_irrefl _)
    · intro hcr
      exact ⟨F', mem_insert _ _, Or.inl rfl, hcr⟩
  · constructor
    · rintro ⟨w, hw, hl, hcr⟩
      rcases hw with rfl | rfl
      · rcases hl with h | h
        · exact absurd h hc.ne
        · exact absurd h (lt_irrefl _)
      · exact hcr
    · intro hcr
      exact ⟨B', mem_insert_of_mem _ rfl, Or.inl rfl, hcr⟩

end Incidence

end GraphMinor.GM06
