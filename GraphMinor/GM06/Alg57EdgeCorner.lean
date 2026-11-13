module

public import GraphMinor.GM06.Alg57EdgeChain

/-!
# The left of an edge seen from an inner point

`cornerRegion_start_eq_end` says that the corner on the left of an edge is the same at its two
ends. Here we add the same fact for a chart centred at an inner point of the edge, in which the
edge runs out along a ray: the corner after that ray is the corner after the edge at its start
(`cornerRegion_start_eq_mid`). This lets us compute the region on the left of an edge in any
convenient chart along the edge, such as an explicit chart on a cuff of the cylinder.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {Γ : Drawing (OnePoint EuclideanPlane)} {e : Set (OnePoint EuclideanPlane)}
  {G : ℝ → OnePoint EuclideanPlane}

/-- **The left of an edge, seen from an inner point.** Let a positive chart at the start of an
edge have a ray `Wu` along which the edge runs out, and let a positive chart at an inner point
`G a` have a ray `Wm` along which the edge runs out. Then the corners after `Wu` and after `Wm`
are the same region. The proof is the one of `cornerRegion_start_eq_end`: the corner after the
forward ray of the edge charts is locally constant along the edge. -/
theorem cornerRegion_start_eq_mid (hS : IsClosedSurface (OnePoint EuclideanPlane))
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U) (he : e ∈ Γ.E)
    (hG : IsEdgeCurve Γ e G)
    {Φu Φm : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψu Ψm : C(ClosedUnitDisc, EuclideanPlane)}
    (hpu : IsPolar Γ (G 0) Φu) (hΨu : ∀ x, Φu x = (Ψu x : OnePoint EuclideanPlane))
    (hposu : 0 < wind (fun w : Circle => chartC Ψu w) (chartC Ψu 0))
    (hDu : (rimDirs Γ Φu).Finite) {Wu : Circle} (hWu : Wu ∈ rimDirs Γ Φu) {δu : ℝ}
    (hrunu : RunsOut Ψu Wu G 0 δu) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hpm : IsPolar Γ (G a) Φm) (hΨm : ∀ x, Φm x = (Ψm x : OnePoint EuclideanPlane))
    (hposm : 0 < wind (fun w : Circle => chartC Ψm w) (chartC Ψm 0))
    (hDm : (rimDirs Γ Φm).Finite) {Wm : Circle} (hWm : Wm ∈ rimDirs Γ Φm) {δm : ℝ}
    (hrunm : RunsOut Ψm Wm G a δm) :
    cornerRegion Γ Φu Wu = cornerRegion Γ Φm Wm := by
  have hchart := fun t (ht : t ∈ Ioo (0 : ℝ) 1) => exists_edge_chart hS hinf he hG ht
  choose Φ Ψ F B δ₁ δ₂ hp hΨ hpos hD hFB hout hin using hchart
  let L : Ioo (0 : ℝ) 1 → Set (OnePoint EuclideanPlane) := fun t =>
    cornerRegion Γ (Φ t.1 t.2) (F t.1 t.2)
  have hfin : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), (rimDirs Γ (Φ t ht)).Finite := fun t ht => by
    rw [hD t ht]; exact (finite_singleton _).insert _
  have hFD : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), F t ht ∈ rimDirs Γ (Φ t ht) := fun t ht => by
    rw [hD t ht]; exact mem_insert _ _
  have hBD : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), B t ht ∈ rimDirs Γ (Φ t ht) := fun t ht => by
    rw [hD t ht]; exact mem_insert_of_mem _ (mem_singleton _)
  have hFBprev : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1),
      F t ht * Circle.exp (gap (rimDirs Γ (Φ t ht)) (F t ht)) = B t ht := fun t ht => by
    rw [hD t ht]; exact mul_exp_gap_pair (hFB t ht)
  -- nearby charts on the edge give the same corner
  have hnear : ∀ t₀ (h₀ : t₀ ∈ Ioo (0 : ℝ) 1) t₁ (h₁ : t₁ ∈ Ioo (0 : ℝ) 1),
      t₁ ∈ Ioo (t₀ - δ₂ t₀ h₀) (t₀ + δ₁ t₀ h₀) → L ⟨t₁, h₁⟩ = L ⟨t₀, h₀⟩ := by
    intro t₀ h₀ t₁ h₁ ht
    rcases lt_trichotomy t₁ t₀ with hlt | heq | hgt
    · obtain ⟨ρ, hanti, hray⟩ := (hin t₀ h₀).ray_before ⟨ht.1, hlt⟩
      exact cornerRegion_eq_of_in (hp t₀ h₀) (hΨ t₀ h₀) (hpos t₀ h₀) (hfin t₀ h₀) (hp t₁ h₁)
        (hΨ t₁ h₁) (hpos t₁ h₁) (hfin t₁ h₁) (hBD t₀ h₀) (hFBprev t₀ h₀)
        (by linarith : 0 < (t₀ - t₁) / 2) (hout t₁ h₁) rfl hray hanti
    · subst heq; rfl
    · obtain ⟨ρ, hmono, hray⟩ := (hout t₀ h₀).ray_after ⟨hgt, ht.2⟩
      exact cornerRegion_eq_of_out (hp t₀ h₀) (hΨ t₀ h₀) (hpos t₀ h₀) (hfin t₀ h₀) (hp t₁ h₁)
        (hΨ t₁ h₁) (hpos t₁ h₁) (hfin t₁ h₁) (hFD t₀ h₀) (by linarith [ht.2])
        (hout t₁ h₁) rfl hray hmono
  have hlc : IsLocallyConstant L := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨t₀, h₀⟩
    have hδ₁ := (hout t₀ h₀).1
    have hδ₂ := (hin t₀ h₀).1
    have hmem : (⟨t₀, h₀⟩ : Ioo (0 : ℝ) 1) ∈
        Subtype.val ⁻¹' Ioo (t₀ - δ₂ t₀ h₀) (t₀ + δ₁ t₀ h₀) :=
      ⟨by linarith, by linarith⟩
    filter_upwards [(isOpen_Ioo.preimage continuous_subtype_val).mem_nhds hmem]
    rintro ⟨t₁, h₁⟩ ht
    exact hnear t₀ h₀ t₁ h₁ ht
  have : PreconnectedSpace (Ioo (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  -- a chart running out at time `b` gives the corner of an edge chart just after `b`
  have hafter : ∀ {b : ℝ} (hb : b ∈ Ico (0 : ℝ) 1)
      {Φb : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψb : C(ClosedUnitDisc, EuclideanPlane)},
      IsPolar Γ (G b) Φb → (∀ x, Φb x = (Ψb x : OnePoint EuclideanPlane)) →
      0 < wind (fun w : Circle => chartC Ψb w) (chartC Ψb 0) → (rimDirs Γ Φb).Finite →
      ∀ {Wb : Circle}, Wb ∈ rimDirs Γ Φb → ∀ {δb : ℝ}, RunsOut Ψb Wb G b δb →
      ∃ ts : Ioo (0 : ℝ) 1, L ts = cornerRegion Γ Φb Wb := by
    intro b hb Φb Ψb hpb hΨb hposb hDb Wb hWb δb hrunb
    have hδb : 0 < δb := hrunb.1
    have hm : 0 < min δb (1 - b) := lt_min hδb (by linarith [hb.2])
    have hm1 := min_le_left δb (1 - b)
    have hm2 := min_le_right δb (1 - b)
    obtain ⟨ts, hts0, htsu, hts1⟩ : ∃ ts : ℝ, b < ts ∧ ts < b + δb ∧ ts < 1 :=
      ⟨b + min δb (1 - b) / 2, by linarith, by linarith, by linarith⟩
    have hts : ts ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hts1⟩
    refine ⟨⟨ts, hts⟩, ?_⟩
    obtain ⟨ρ, hmono, hray⟩ := hrunb.ray_after (t₁ := ts) ⟨hts0, htsu⟩
    exact cornerRegion_eq_of_out hpb hΨb hposb hDb (hp ts hts) (hΨ ts hts) (hpos ts hts)
      (hfin ts hts) hWb (by linarith) (hout ts hts) rfl hray hmono
  obtain ⟨tu, hu⟩ := hafter ⟨le_rfl, one_pos⟩ hpu hΨu hposu hDu hWu hrunu
  obtain ⟨tm, hm⟩ := hafter ⟨ha.1.le, ha.2⟩ hpm hΨm hposm hDm hWm hrunm
  rw [← hu, ← hm]
  exact hlc.apply_eq_of_preconnectedSpace _ _

end GraphMinor.GM06
