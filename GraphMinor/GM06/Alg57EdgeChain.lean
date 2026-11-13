module

public import GraphMinor.GM06.Alg57EdgeCharts

/-!
# The region on the left of an edge

This is the half-band argument of Step 1 and Step 4 of the proof of Lemma 3 of our proof of VI (5.7)
(outlined in `Alg57Algorithm.lean`): the face label on the left of an edge stays constant along the
edge. Here the left of the edge at a point is the corner after the forward ray of a positive chart
there (`exists_edge_chart`). Nearby charts give the same corner (`cornerRegion_eq_of_out`,
`cornerRegion_eq_of_in`), so the corner is the same all along the edge. At the two ends it is the
corner after the edge at its start, and the corner before the edge at its end
(`cornerRegion_start_eq_end`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- In a star of two directions, the corner after one ends at the other. -/
theorem gap_pair {F B : Circle} (hFB : F ≠ B) : gap {F, B} F = angleTo F B := by
  have hD : ({F, B} : Set Circle).Finite := (finite_singleton B).insert F
  have hle := gap_le_angleTo hD F (mem_insert_of_mem _ (mem_singleton B))
  rcases gap_mem hD F with h | ⟨w, hw, h⟩
  · rw [h] at hle ⊢
    exact le_antisymm hle (angleTo_le F B)
  · rcases hw with rfl | hw
    · rw [← h, angleTo_self] at hle ⊢
      exact le_antisymm hle (angleTo_le w B)
    · rw [mem_singleton_iff] at hw
      rw [← h, hw]

theorem mul_exp_gap_pair {F B : Circle} (hFB : F ≠ B) : F * Circle.exp (gap {F, B} F) = B := by
  rw [gap_pair hFB, mul_exp_angleTo]

section Runs

variable {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {W : Circle} {G : ℝ → OnePoint EuclideanPlane}

/-- After its start, a curve running out along a ray stays on the ray at a positive radius. -/
theorem RunsOut.ray_after {a δ : ℝ} (h : RunsOut Ψ W G a δ) {t₁ : ℝ} (ht₁ : t₁ ∈ Ioo a (a + δ)) :
    ∃ ρ : ℝ → ℝ, StrictMonoOn ρ (Icc t₁ (t₁ + (a + δ - t₁))) ∧
      ∀ t ∈ Icc t₁ (t₁ + (a + δ - t₁)), 0 < ρ t ∧ ρ t < 1 ∧
        G t = toSph (chartC Ψ ((ρ t : ℂ) * W)) := by
  obtain ⟨hδ, ρ, -, hρ0, hmono, hρG⟩ := h
  have hsub : Icc t₁ (t₁ + (a + δ - t₁)) ⊆ Icc a (a + δ) :=
    Icc_subset_Icc ht₁.1.le (by linarith)
  refine ⟨ρ, hmono.mono hsub, fun t ht => ⟨?_, (hρG t (hsub ht)).1, (hρG t (hsub ht)).2⟩⟩
  rw [← hρ0]
  exact hmono ⟨le_rfl, by linarith⟩ (hsub ht) (by linarith [ht.1, ht₁.1])

/-- Before its end, a curve running in along a ray stays on the ray at a positive radius. -/
theorem RunsIn.ray_before {b δ : ℝ} (h : RunsIn Ψ W G b δ) {t₁ : ℝ} (ht₁ : t₁ ∈ Ioo (b - δ) b) :
    ∃ ρ : ℝ → ℝ, StrictAntiOn ρ (Icc t₁ (t₁ + (b - t₁) / 2)) ∧
      ∀ t ∈ Icc t₁ (t₁ + (b - t₁) / 2), 0 < ρ t ∧ ρ t < 1 ∧
        G t = toSph (chartC Ψ ((ρ t : ℂ) * W)) := by
  obtain ⟨hδ, ρ, -, hρ0, hanti, hρG⟩ := h
  have hsub : Icc t₁ (t₁ + (b - t₁) / 2) ⊆ Icc (b - δ) b :=
    Icc_subset_Icc ht₁.1.le (by linarith [ht₁.2])
  refine ⟨ρ, hanti.mono hsub, fun t ht => ⟨?_, (hρG t (hsub ht)).1, (hρG t (hsub ht)).2⟩⟩
  rw [← hρ0]
  exact hanti (hsub ht) ⟨by linarith [ht₁.1], le_rfl⟩ (by linarith [ht.2, ht₁.2])

end Runs

section Chain

variable {Γ : Drawing (OnePoint EuclideanPlane)} {e : Set (OnePoint EuclideanPlane)}
  {G : ℝ → OnePoint EuclideanPlane}

/-- **The left of an edge is the same at both ends.** Let a positive chart at the start of an
edge have a ray `Wu` along which the edge runs out, and let a positive chart at the end have a
ray `Wv` along which the edge runs in, with `Wv'` the ray before `Wv`. Then the corner after `Wu`
at the start is the corner after `Wv'` at the end. -/
theorem cornerRegion_start_eq_end (hS : IsClosedSurface (OnePoint EuclideanPlane))
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U) (he : e ∈ Γ.E)
    (hG : IsEdgeCurve Γ e G)
    {Φu Φv : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψu Ψv : C(ClosedUnitDisc, EuclideanPlane)}
    (hpu : IsPolar Γ (G 0) Φu) (hΨu : ∀ x, Φu x = (Ψu x : OnePoint EuclideanPlane))
    (hposu : 0 < wind (fun w : Circle => chartC Ψu w) (chartC Ψu 0))
    (hDu : (rimDirs Γ Φu).Finite) {Wu : Circle} (hWu : Wu ∈ rimDirs Γ Φu) {δu : ℝ}
    (hrunu : RunsOut Ψu Wu G 0 δu)
    (hpv : IsPolar Γ (G 1) Φv) (hΨv : ∀ x, Φv x = (Ψv x : OnePoint EuclideanPlane))
    (hposv : 0 < wind (fun w : Circle => chartC Ψv w) (chartC Ψv 0))
    (hDv : (rimDirs Γ Φv).Finite) {Wv Wv' : Circle} (hWv : Wv ∈ rimDirs Γ Φv)
    (hprev : Wv' * Circle.exp (gap (rimDirs Γ Φv) Wv') = Wv) {δv : ℝ}
    (hrunv : RunsIn Ψv Wv G 1 δv) :
    cornerRegion Γ Φu Wu = cornerRegion Γ Φv Wv' := by
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
  -- so the corner is the same all along the edge
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
  -- the start
  have hδu : 0 < δu := hrunu.1
  obtain ⟨ts, hts0, htsu, hts1⟩ : ∃ ts : ℝ, 0 < ts ∧ ts < δu ∧ ts < 1 :=
    ⟨min δu (1 / 2) / 2, by positivity, by linarith [min_le_left δu (1 / 2)],
      by linarith [min_le_right δu (1 / 2)]⟩
  have hts : ts ∈ Ioo (0 : ℝ) 1 := ⟨hts0, hts1⟩
  have hstart : L ⟨ts, hts⟩ = cornerRegion Γ Φu Wu := by
    obtain ⟨ρ, hmono, hray⟩ := hrunu.ray_after (t₁ := ts) ⟨hts0, by linarith⟩
    exact cornerRegion_eq_of_out hpu hΨu hposu hDu (hp ts hts) (hΨ ts hts) (hpos ts hts)
      (hfin ts hts) hWu (by linarith) (hout ts hts) rfl hray hmono
  -- the end
  have hδv : 0 < δv := hrunv.1
  obtain ⟨te, hte0, htev, hte1⟩ : ∃ te : ℝ, 0 < te ∧ 1 - δv < te ∧ te < 1 :=
    ⟨1 - min δv (1 / 2) / 2, by linarith [min_le_right δv (1 / 2)],
      by linarith [min_le_left δv (1 / 2), half_lt_self (lt_min hδv (by norm_num : (0:ℝ) < 1 / 2))],
      by linarith [half_pos (lt_min hδv (by norm_num : (0:ℝ) < 1 / 2))]⟩
  have hte : te ∈ Ioo (0 : ℝ) 1 := ⟨hte0, hte1⟩
  have hend : L ⟨te, hte⟩ = cornerRegion Γ Φv Wv' := by
    obtain ⟨ρ, hanti, hray⟩ := hrunv.ray_before (t₁ := te) ⟨htev, hte1⟩
    exact cornerRegion_eq_of_in hpv hΨv hposv hDv (hp te hte) (hΨ te hte) (hpos te hte)
      (hfin te hte) hWv hprev (by linarith [hte.2]) (hout te hte) rfl hray hanti
  rw [← hstart, ← hend]
  exact hlc.apply_eq_of_preconnectedSpace _ _

end Chain

end GraphMinor.GM06
