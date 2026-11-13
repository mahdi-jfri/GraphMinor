module

public import GraphMinor.GM06.Alg57PathSide
public import GraphMinor.GM06.Alg57StarShrink
public import GraphMinor.GM06.Alg57CornerLabelExists

/-!
# Path charts exist

Let `f` be an arc in the sphere, injective on `[0, 1]`, whose image is a nice set `X` inside
`U(Γ)`. At an inner point `f t` the arc is the only part of `X` near `f t`, because the rest of
the arc, `f '' ([0, t/2] ∪ [(t+1)/2, 1])`, is compact and misses `f t`. So every positive polar
chart at `f t` inside a small open set is a path chart (`exists_isPathChart_of_small`): it has
exactly two directions in `X`, one along which `f` runs out and one along which it runs in
(`exists_path_dirs`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

section PathChartExists

variable {Γ : Drawing (OnePoint EuclideanPlane)} {X : Set (OnePoint EuclideanPlane)}
  {f : ℝ → OnePoint EuclideanPlane}

/-- **Small charts along an arc are path charts.** At an inner point `f t` of an arc with point
set `X`, every positive polar chart with finitely many directions inside a suitable open set is
a path chart. -/
theorem exists_isPathChart_of_small (hX : IsGammaNice Γ X) (hXU : X ⊆ Γ.U) (hf : Continuous f)
    (hinj : InjOn f (Icc 0 1)) (hfX : f '' Icc 0 1 ⊆ X) (hXf : X ⊆ f '' Icc 0 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ O : Set (OnePoint EuclideanPlane), IsOpen O ∧ f t ∈ O ∧
      ∀ {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)},
        IsPolar Γ (f t) Φ → (∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) →
        0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) → (rimDirs Γ Φ).Finite →
        range Φ ⊆ O → ∃ F B : Circle, IsPathChart Γ X f t Φ Ψ F B := by
  obtain ⟨h0, h1⟩ := ht
  have ha : t / 2 < t := by linarith
  have hb : t < (t + 1) / 2 := by linarith
  set K := f '' (Icc 0 (t / 2) ∪ Icc ((t + 1) / 2) 1)
  have hK : IsClosed K := ((isCompact_Icc.union isCompact_Icc).image hf).isClosed
  have htK : f t ∉ K := by
    rintro ⟨s, hs, hst⟩
    have hs01 : s ∈ Icc (0 : ℝ) 1 := by
      rcases hs with h | h
      · exact ⟨h.1, by linarith [h.2]⟩
      · exact ⟨by linarith [h.1], h.2⟩
    have := hinj hs01 ⟨h0.le, h1.le⟩ hst
    rcases hs with h | h <;> linarith [h.1, h.2]
  refine ⟨Kᶜ, hK.isOpen_compl, htK, fun {Φ Ψ} hp hΨ hpos hfin hsub => ?_⟩
  have hloc : range Φ ∩ X ⊆ f '' Icc (t / 2) ((t + 1) / 2) := by
    rintro x ⟨hxΦ, hxX⟩
    obtain ⟨s, hs, rfl⟩ := hXf hxX
    have hK' := hsub hxΦ
    refine ⟨s, ⟨?_, ?_⟩, rfl⟩
    · by_contra h
      exact hK' ⟨s, Or.inl ⟨hs.1, (not_le.mp h).le⟩, rfl⟩
    · by_contra h
      exact hK' ⟨s, Or.inr ⟨(not_le.mp h).le, hs.2⟩, rfl⟩
  have hab : Icc (t / 2) ((t + 1) / 2) ⊆ Icc 0 1 :=
    Icc_subset_Icc (by linarith) (by linarith)
  obtain ⟨F, B, hne, hFX, hBX, hout, hin, hdirs⟩ := exists_path_dirs hp hΨ hX hf ha hb
    (hinj.mono hab) ((image_mono hab).trans hfX) hloc
  exact ⟨F, B, ⟨hp, hΨ, hpos, hfin, hXU hFX, hXU hBX, hne, hout, hin, hdirs⟩⟩

/-- **Path charts inside any open set.** For a drawing with a counterclockwise rotation, at an
inner point of the arc there is a path chart inside any given open set around it: at a vertex we
shrink a counterclockwise star (`IsCcwStar.exists_small`), and inside an edge we take an edge
chart (`exists_edge_chart_in`). -/
theorem exists_isPathChart_in (hS : IsClosedSurface (OnePoint EuclideanPlane))
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {R : DartRotation (DrawingDart Γ)} (hγ : EdgePar Γ γ) (hccw : IsCcwRotation Γ γ R)
    (hV : ∀ v ∈ Γ.V, ∃ a : DrawingDart Γ, dartVertex γ a = v)
    (hX : IsGammaNice Γ X) (hXU : X ⊆ Γ.U) (hf : Continuous f)
    (hinj : InjOn f (Icc 0 1)) (hfX : f '' Icc 0 1 ⊆ X) (hXf : X ⊆ f '' Icc 0 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {N : Set (OnePoint EuclideanPlane)} (hN : IsOpen N)
    (htN : f t ∈ N) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψ : C(ClosedUnitDisc, EuclideanPlane))
      (F B : Circle), IsPathChart Γ X f t Φ Ψ F B ∧ range Φ ⊆ N := by
  obtain ⟨O, hO, htO, hsmall⟩ := exists_isPathChart_of_small hX hXU hf hinj hfX hXf ht
  have htU : f t ∈ Γ.U := hXU (hfX ⟨t, Ioo_subset_Icc_self ht, rfl⟩)
  by_cases htV : f t ∈ Γ.V
  · obtain ⟨a, ha⟩ := hV _ htV
    obtain ⟨Φ, z, hst⟩ := hccw (f t) ⟨a, ha⟩
    obtain ⟨Φ', hst', hsub⟩ := hst.exists_small hS (hO.inter hN) ⟨htO, htN⟩
    obtain ⟨Ψ, hΨ, hw⟩ := hst'.pos
    have hpos : 0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) := by
      rw [wind_chartC]; exact hw
    obtain ⟨F, B, hc⟩ := hsmall hst'.polar hΨ hpos (hst'.rimDirs_finite hγ)
      (hsub.trans inter_subset_left)
    exact ⟨Φ', Ψ, F, B, hc, hsub.trans inter_subset_right⟩
  · obtain ⟨e, he, hte⟩ := Γ.exists_edge_of_mem htU htV
    have hG := isEdgeCurve_edgeCurve hγ he
    obtain ⟨t₀, ht₀, ht₀e⟩ : f t ∈ edgeCurve γ e '' Ioo 0 1 := by rw [hG.image]; exact hte
    obtain ⟨Φ, Ψ, F', B', δ₁, δ₂, hp, hsub, hΨ, hpos, hdirs, -⟩ :=
      exists_edge_chart_in hS hinf he hG ht₀ (hO.inter hN) (by rw [ht₀e]; exact ⟨htO, htN⟩)
    rw [ht₀e] at hp
    have hfin : (rimDirs Γ Φ).Finite := by rw [hdirs]; exact toFinite _
    obtain ⟨F, B, hc⟩ := hsmall hp hΨ hpos hfin (hsub.trans inter_subset_left)
    exact ⟨Φ, Ψ, F, B, hc, hsub.trans inter_subset_right⟩

end PathChartExists

end GraphMinor.GM06
