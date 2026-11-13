module

public import GraphMinor.GM06.Alg57EdgeRuns
public import GraphMinor.GM06.Alg57PositiveRotations
public import GraphMinor.GM06.Alg511PolarReflection
public import GraphMinor.GM06.Section5SmallPolar
public import GraphMinor.GM06.Section5InitialSubarcsMeet
public import GraphMinor.GM06.Section5PolarRay
public import GraphMinor.GM11.EdgeSides

/-!
# Positive charts at the points of an edge

Lemma 1 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) gives a band along the middle
of each edge. We use instead a positive polar chart at each point `G t₀` of the edge, where `G`
parametrizes the edge (`IsEdgeCurve`). In such a chart the edge is two rays: the edge runs out along
one ray `F` after time `t₀` and runs in along the other ray `B` up to time `t₀`, and the drawing has
no other rays (`exists_edge_chart`).

The proof shrinks a polar chart into a neighbourhood that meets `U(Γ)` only in a short piece
`G (t₀ - η, t₀ + η)` of the edge. Each ray of the chart in `U(Γ)` is connected, so it lies in
the piece before `t₀` or in the piece after `t₀`. Two rays in the same piece meet, since both are
initial pieces of the same arc (`exists_positive_meeting_of_initial_subarcs`), so they are
equal.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A parametrization of an edge by the reals, injective on `(0, 1)`, with its ends at vertices. -/
structure IsEdgeCurve (Γ : Drawing (OnePoint EuclideanPlane)) (e : Set (OnePoint EuclideanPlane))
    (G : ℝ → OnePoint EuclideanPlane) : Prop where
  cont : Continuous G
  inj : InjOn G (Ioo 0 1)
  image : G '' Ioo 0 1 = e
  zero : G 0 ∈ Γ.V
  one : G 1 ∈ Γ.V

namespace IsEdgeCurve

variable {Γ : Drawing (OnePoint EuclideanPlane)} {e : Set (OnePoint EuclideanPlane)}
  {G : ℝ → OnePoint EuclideanPlane}

theorem mem_edge (h : IsEdgeCurve Γ e G) {t : ℝ} (ht : t ∈ Ioo 0 1) : G t ∈ e :=
  h.image ▸ mem_image_of_mem G ht

/-- The edge read backwards. -/
theorem rev (h : IsEdgeCurve Γ e G) : IsEdgeCurve Γ e (fun t => G (1 - t)) where
  cont := h.cont.comp (continuous_const.sub continuous_id)
  inj := fun s hs t ht hst => by
    have := h.inj (show 1 - s ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      (show 1 - t ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [ht.2], by linarith [ht.1]⟩) hst
    linarith
  image := by
    rw [← h.image]
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by simp⟩
  zero := by simpa using h.one
  one := by simpa using h.zero

theorem injOn_Icc (h : IsEdgeCurve Γ e G) {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    InjOn G (Icc a b) :=
  h.inj.mono fun _ hs => show _ ∈ Ioo (0 : ℝ) 1 from ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩

/-- Near the start, the edge curve is injective including its start, since the start is a
vertex and the edge misses the vertices. -/
theorem injOn_Icc_zero (h : IsEdgeCurve Γ e G) (he : e ∈ Γ.E) {b : ℝ} (hb : b < 1) :
    InjOn G (Icc 0 b) := by
  intro s hs s' hs' hss'
  rcases eq_or_lt_of_le hs.1 with h0 | h0 <;> rcases eq_or_lt_of_le hs'.1 with h0' | h0'
  · rw [← h0, ← h0']
  · exfalso
    rw [← h0] at hss'
    exact edge_notMem_V he (h.mem_edge ⟨h0', hs'.2.trans_lt hb⟩) (hss' ▸ h.zero)
  · exfalso
    rw [← h0'] at hss'
    exact edge_notMem_V he (h.mem_edge ⟨h0, hs.2.trans_lt hb⟩) (hss'.symm ▸ h.zero)
  · exact h.inj ⟨h0, hs.2.trans_lt hb⟩ ⟨h0', hs'.2.trans_lt hb⟩ hss'

end IsEdgeCurve

section EdgeChart

variable {Γ : Drawing (OnePoint EuclideanPlane)} {e : Set (OnePoint EuclideanPlane)}
  {G : ℝ → OnePoint EuclideanPlane}

/-- A positive polar chart of the sphere. -/
theorem exists_positive_chart {c : OnePoint EuclideanPlane}
    {Φ₁ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hp₁ : IsPolar Γ c Φ₁)
    (hfin : (OnePoint.infty : OnePoint EuclideanPlane) ∉ range Φ₁) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψ : C(ClosedUnitDisc, EuclideanPlane)),
      IsPolar Γ c Φ ∧ range Φ ⊆ range Φ₁ ∧ (∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) ∧
      0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) := by
  have hrange : range Φ₁ ⊆ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane) := by
    rintro y hy
    exact OnePoint.ne_infty_iff_exists.mp (fun h => hfin (h ▸ hy))
  rcases positive_polar_or_mirror Φ₁ hp₁.inj hrange with ⟨Ψ, hΨ, hw⟩ | ⟨Ψ, hΨ, hw⟩
  · exact ⟨Φ₁, Ψ, hp₁, subset_rfl, hΨ, by rw [wind_chartC]; exact hw⟩
  · refine ⟨_, Ψ, alg511_isPolar_comp_discMirror hp₁ 0, ?_, hΨ, by rw [wind_chartC]; exact hw⟩
    rintro _ ⟨x, rfl⟩
    exact mem_range_self _

/-- **Positive charts at a point of an edge, inside a given open set.** At each point `G t₀` of
an edge, and inside each open set `N` containing it, there is a positive polar chart whose only
rays in `U(Γ)` are two distinct rays `F` and `B`; the edge runs out along `F` after `t₀` and runs
in along `B` up to `t₀`. -/
theorem exists_edge_chart_in (hS : IsClosedSurface (OnePoint EuclideanPlane))
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U) (he : e ∈ Γ.E)
    (hG : IsEdgeCurve Γ e G) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) {N : Set (OnePoint EuclideanPlane)}
    (hN : IsOpen N) (hGN : G t₀ ∈ N) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψ : C(ClosedUnitDisc, EuclideanPlane))
      (F B : Circle) (δ₁ δ₂ : ℝ),
      IsPolar Γ (G t₀) Φ ∧ range Φ ⊆ N ∧ (∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) ∧
      0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) ∧
      rimDirs Γ Φ = {F, B} ∧ F ≠ B ∧ RunsOut Ψ F G t₀ δ₁ ∧ RunsIn Ψ B G t₀ δ₂ := by
  obtain ⟨h0, h1⟩ := ht₀
  set η : ℝ := min t₀ (1 - t₀) / 2
  have hηdef : η = min t₀ (1 - t₀) / 2 := rfl
  have hη : 0 < η := half_pos (lt_min h0 (by linarith))
  have hηt : η < t₀ := by have := min_le_left t₀ (1 - t₀); linarith
  have hηt' : t₀ + η < 1 := by have := min_le_right t₀ (1 - t₀); linarith
  have hGt₀ : G t₀ ∈ e := hG.mem_edge ⟨h0, h1⟩
  -- the two pieces of the edge next to `G t₀`
  set u := G '' Icc (t₀ - η) t₀
  set v := G '' Icc t₀ (t₀ + η)
  have hu : IsClosed u := ((isCompact_Icc).image hG.cont).isClosed
  have hv : IsClosed v := ((isCompact_Icc).image hG.cont).isClosed
  have hinjJ : InjOn G (Icc (t₀ - η) (t₀ + η)) := hG.injOn_Icc (by linarith) hηt'
  have huv : u ∩ v ⊆ {G t₀} := by
    rintro _ ⟨⟨s, hs, rfl⟩, ⟨s', hs', hss'⟩⟩
    have hJs : s ∈ Icc (t₀ - η) (t₀ + η) := ⟨hs.1, by linarith [hs.2]⟩
    have hJs' : s' ∈ Icc (t₀ - η) (t₀ + η) := ⟨by linarith [hs'.1], hs'.2⟩
    have h := hinjJ hJs' hJs hss'
    have : s = t₀ := le_antisymm hs.2 (h ▸ hs'.1)
    rw [mem_singleton_iff, this]
  -- a neighbourhood meeting `U(Γ)` only near `G t₀`
  set K : Set ℝ := Icc 0 1 \ Ioo (t₀ - η) (t₀ + η)
  have hK : IsCompact K := isCompact_Icc.diff isOpen_Ioo
  have hGK : G t₀ ∉ G '' K := by
    rintro ⟨s, ⟨hs, hsJ⟩, hss⟩
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · rw [← hs0] at hss
      exact edge_notMem_V he hGt₀ (hss ▸ hG.zero)
    rcases eq_or_lt_of_le hs.2 with hs1 | hs1
    · rw [hs1] at hss
      exact edge_notMem_V he hGt₀ (hss ▸ hG.one)
    have := hG.inj ⟨hs0, hs1⟩ ⟨h0, h1⟩ hss
    exact hsJ ⟨by linarith, by linarith⟩
  set O : Set (OnePoint EuclideanPlane) :=
    (G '' K)ᶜ ∩ (Γ.U \ e)ᶜ ∩ {OnePoint.infty}ᶜ ∩ N
  have hO : IsOpen O :=
    ((((hK.image hG.cont).isClosed.isOpen_compl).inter
      (isClosed_U_sdiff_edge Γ he).isOpen_compl).inter isClosed_singleton.isOpen_compl).inter hN
  have hGO : G t₀ ∈ O :=
    ⟨⟨⟨hGK, fun h => h.2 hGt₀⟩, fun h => hinf (h ▸ (he.2.1 hGt₀).1)⟩, hGN⟩
  have hOU : ∀ y ∈ O, y ∈ Γ.U → y ∈ u ∪ v := by
    rintro y ⟨⟨⟨hyK, hye⟩, -⟩, -⟩ hyU
    have hye' : y ∈ e := by by_contra h; exact hye ⟨hyU, h⟩
    rw [← hG.image] at hye'
    obtain ⟨s, hs, rfl⟩ := hye'
    have hsJ : s ∈ Ioo (t₀ - η) (t₀ + η) := by
      by_contra h
      exact hyK ⟨s, ⟨⟨hs.1.le, hs.2.le⟩, h⟩, rfl⟩
    rcases le_total s t₀ with hst | hst
    · exact Or.inl ⟨s, ⟨hsJ.1.le, hst⟩, rfl⟩
    · exact Or.inr ⟨s, ⟨hst, hsJ.2.le⟩, rfl⟩
  -- a positive polar chart inside `O`
  obtain ⟨Φ₀, hp₀⟩ := exists_isPolar_of_edge hS Γ he hGt₀
  obtain ⟨Φ₁, hp₁, hΦ₁O⟩ := exists_small_polar_chart hS hp₀ hO hGO
  obtain ⟨Φ, Ψ, hp, hΦΦ₁, hΨ, hpos⟩ := exists_positive_chart hp₁ (fun h => (hΦ₁O h).1.2 rfl)
  have hΦO : range Φ ⊆ O := hΦΦ₁.trans hΦ₁O
  have hc0 : toSph (chartC Ψ 0) = G t₀ := toSph_chartC_zero hp hΨ
  have hray_ne : ∀ w : Circle, ∀ r : ℝ, 0 < r → r ≤ 1 →
      toSph (chartC Ψ ((r : ℂ) * w)) ≠ G t₀ := by
    intro w r hr hr1 h
    rw [← hc0] at h
    have := chartC_injOn hΨ hp.inj (by
      rw [mem_closedBall_zero_iff, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hr.le]; exact hr1) (mem_closedBall_self zero_le_one)
      (toSph_injective h)
    simp [hr.ne'] at this
  have hray_range : ∀ w : Circle, ∀ r : ℝ, 0 < r → r ≤ 1 →
      toSph (chartC Ψ ((r : ℂ) * w)) ∈ range Φ := fun w r _ _ => by
    rw [toSph_chartC hΨ]; exact mem_range_self _
  -- each ray in `U(Γ)` lies in one piece
  have hside : ∀ w ∈ rimDirs Γ Φ, (∀ r : ℝ, 0 < r → r ≤ 1 → toSph (chartC Ψ ((r : ℂ) * w)) ∈ u) ∨
      (∀ r : ℝ, 0 < r → r ≤ 1 → toSph (chartC Ψ ((r : ℂ) * w)) ∈ v) := by
    intro w hw
    set Rw := (fun r : ℝ => toSph (chartC Ψ ((r : ℂ) * w))) '' Ioc 0 1
    have hRw : IsPreconnected Rw := isPreconnected_Ioc.image _
      ((continuous_toSph.comp (continuous_chartC.comp (by fun_prop))).continuousOn)
    have hcov : Rw ⊆ u ∪ v := by
      rintro _ ⟨r, hr, rfl⟩
      exact hOU _ (hΦO (hray_range w r hr.1 hr.2))
        ((chart_ray_mem_iff hp hΨ (isGammaNice_U Γ) w hr.1 hr.2).mpr hw)
    have hdis : Rw ∩ (u ∩ v) = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨r, hr, rfl⟩ hu' hv'
      exact hray_ne w r hr.1 hr.2 (huv ⟨hu', hv'⟩)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hRw u v hu hv hcov hdis with h | h
    · exact Or.inl fun r hr hr1 => h ⟨r, ⟨hr, hr1⟩, rfl⟩
    · exact Or.inr fun r hr hr1 => h ⟨r, ⟨hr, hr1⟩, rfl⟩
  -- two rays in the same piece are equal
  have hpiece : ∀ (f : C(I, OnePoint EuclideanPlane)), IsArcMap f → f 0 = G t₀ →
      ∀ w w' : Circle, (∀ r : ℝ, 0 < r → r ≤ 1 → toSph (chartC Ψ ((r : ℂ) * w)) ∈ range f) →
      (∀ r : ℝ, 0 < r → r ≤ 1 → toSph (chartC Ψ ((r : ℂ) * w')) ∈ range f) → w = w' := by
    intro f hf hf0 w w' hw hw'
    have hsub : ∀ z : Circle, (∀ r : ℝ, 0 < r → r ≤ 1 →
        toSph (chartC Ψ ((r : ℂ) * z)) ∈ range f) → range (polarRayMap Φ z) ⊆ range f := by
      rintro z hz _ ⟨r, rfl⟩
      rcases eq_or_lt_of_le r.2.1 with hr | hr
      · have : r = 0 := Subtype.ext hr.symm
        rw [this, polarRayMap_zero, hp.centre, ← hf0]
        exact mem_range_self _
      · have := hz r hr r.2.2
        rwa [toSph_chartC hΨ, discPt_mul] at this
    have hstart : ∀ z : Circle, polarRayMap Φ z 0 = f 0 := fun z => by
      rw [polarRayMap_zero, hp.centre, hf0]
    obtain ⟨r, s, hr, -, hrs⟩ := exists_positive_meeting_of_initial_subarcs f
      (polarRayMap Φ w) (polarRayMap Φ w') hf (isArcMap_polarRayMap hp.inj w)
      (isArcMap_polarRayMap hp.inj w') (hsub w hw) (hsub w' hw') (hstart w) (hstart w')
    exact polarDiscPoint_direction_eq hr (hp.inj hrs)
  -- the arcs of the two pieces
  let fv : C(I, OnePoint EuclideanPlane) := ⟨fun s => G (t₀ + η * s), by
    have := hG.cont; fun_prop⟩
  let fu : C(I, OnePoint EuclideanPlane) := ⟨fun s => G (t₀ - η * s), by
    have := hG.cont; fun_prop⟩
  have hfv : IsArcMap fv := ⟨fv.continuous, fun s s' h => by
    have := hinjJ (x₁ := t₀ + η * s) ⟨by nlinarith [s.2.1], by nlinarith [s.2.2]⟩
      ⟨by nlinarith [s'.2.1], by nlinarith [s'.2.2]⟩ h
    exact Subtype.ext (by nlinarith)⟩
  have hfu : IsArcMap fu := ⟨fu.continuous, fun s s' h => by
    have := hinjJ (x₁ := t₀ - η * s) ⟨by nlinarith [s.2.2], by nlinarith [s.2.1]⟩
      ⟨by nlinarith [s'.2.2], by nlinarith [s'.2.1]⟩ h
    exact Subtype.ext (by nlinarith)⟩
  have hvf : v ⊆ range fv := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨(s - t₀) / η, div_nonneg (by linarith [hs.1]) hη.le,
      (div_le_one hη).mpr (by linarith [hs.2])⟩, ?_⟩
    change G (t₀ + η * ((s - t₀) / η)) = G s
    rw [mul_div_cancel₀ _ hη.ne']; ring_nf
  have huf : u ⊆ range fu := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨(t₀ - s) / η, div_nonneg (by linarith [hs.2]) hη.le,
      (div_le_one hη).mpr (by linarith [hs.1])⟩, ?_⟩
    change G (t₀ - η * ((t₀ - s) / η)) = G s
    rw [mul_div_cancel₀ _ hη.ne']; ring_nf
  have hfv0 : fv 0 = G t₀ := by simp [fv]
  have hfu0 : fu 0 = G t₀ := by simp [fu]
  -- times near `t₀` stay in the chart
  obtain ⟨δ₀, hδ₀, hδ₀G⟩ : ∃ δ₀, 0 < δ₀ ∧ δ₀ ≤ η ∧
      ∀ t ∈ Icc (t₀ - δ₀) (t₀ + δ₀), G t ∈ range Φ := by
    have hpre := (isOpen_interior.preimage hG.cont).mem_nhds (show t₀ ∈ G ⁻¹' interior (range Φ)
      from hp.nhd)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    refine ⟨min (ε / 2) η, lt_min (half_pos hε) hη, min_le_right _ _, fun t ht => ?_⟩
    apply interior_subset
    apply hball
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, min_le_left (ε / 2) η]
  obtain ⟨hδ₀η, hδ₀G⟩ := hδ₀G
  -- the direction of a point of the edge near `t₀`
  have hdir : ∀ t, t ≠ t₀ → t ∈ Icc (t₀ - δ₀) (t₀ + δ₀) → ∃ r : ℝ, ∃ w : Circle,
      0 < r ∧ r ≤ 1 ∧ G t = toSph (chartC Ψ ((r : ℂ) * w)) ∧ w ∈ rimDirs Γ Φ := by
    intro t htt ht
    have htJ : t ∈ Ioo 0 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hne : G t ≠ G t₀ := fun h => htt (hG.inj htJ ⟨h0, h1⟩ h)
    obtain ⟨r, w, hr, hr1, hGt⟩ := chart_point_polar hp hΨ (hδ₀G t ht) hne
    refine ⟨r, w, hr, hr1, hGt, ?_⟩
    show polarRimMap Φ w ∈ Γ.U
    rw [← chart_ray_mem_iff hp hΨ (isGammaNice_U Γ) w hr hr1, ← hGt]
    exact (he.2.1 (hG.mem_edge htJ)).1
  -- a direction is on the side of the edge points on its ray
  have hside_v : ∀ t ∈ Ioc t₀ (t₀ + δ₀), ∀ r : ℝ, ∀ w : Circle, 0 < r → r ≤ 1 →
      G t = toSph (chartC Ψ ((r : ℂ) * w)) → w ∈ rimDirs Γ Φ →
      ∀ r' : ℝ, 0 < r' → r' ≤ 1 → toSph (chartC Ψ ((r' : ℂ) * w)) ∈ v := by
    intro t ht r w hr hr1 hGt hw
    rcases hside w hw with hU | hV
    · exfalso
      have hGv : G t ∈ v := ⟨t, ⟨ht.1.le, by linarith [ht.2]⟩, rfl⟩
      have hGu : G t ∈ u := hGt ▸ hU r hr hr1
      have := huv ⟨hGu, hGv⟩
      have htJ : t ∈ Ioo 0 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact ht.1.ne' (hG.inj htJ ⟨h0, h1⟩ this)
    · exact hV
  have hside_u : ∀ t ∈ Ico (t₀ - δ₀) t₀, ∀ r : ℝ, ∀ w : Circle, 0 < r → r ≤ 1 →
      G t = toSph (chartC Ψ ((r : ℂ) * w)) → w ∈ rimDirs Γ Φ →
      ∀ r' : ℝ, 0 < r' → r' ≤ 1 → toSph (chartC Ψ ((r' : ℂ) * w)) ∈ u := by
    intro t ht r w hr hr1 hGt hw
    rcases hside w hw with hU | hV
    · exact hU
    · exfalso
      have hGu : G t ∈ u := ⟨t, ⟨by linarith [ht.1], ht.2.le⟩, rfl⟩
      have hGv : G t ∈ v := hGt ▸ hV r hr hr1
      have := huv ⟨hGu, hGv⟩
      have htJ : t ∈ Ioo 0 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact ht.2.ne (hG.inj htJ ⟨h0, h1⟩ this)
  -- the forward direction `F` and the backward direction `B`
  obtain ⟨rF, F, hrF, hrF1, hGF, hFD⟩ := hdir (t₀ + δ₀) (by linarith) ⟨by linarith, le_rfl⟩
  obtain ⟨rB, B, hrB, hrB1, hGB, hBD⟩ := hdir (t₀ - δ₀) (by linarith) ⟨le_rfl, by linarith⟩
  have hFv := hside_v (t₀ + δ₀) ⟨by linarith, le_rfl⟩ rF F hrF hrF1 hGF hFD
  have hBu := hside_u (t₀ - δ₀) ⟨le_rfl, by linarith⟩ rB B hrB hrB1 hGB hBD
  have hFB : F ≠ B := by
    intro h
    rw [h] at hFv
    have := huv ⟨hBu 1 one_pos le_rfl, hFv 1 one_pos le_rfl⟩
    exact hray_ne B 1 one_pos le_rfl this
  have hDv : ∀ w ∈ rimDirs Γ Φ, (∀ r : ℝ, 0 < r → r ≤ 1 →
      toSph (chartC Ψ ((r : ℂ) * w)) ∈ v) → w = F := fun w _ hw =>
    hpiece fv hfv hfv0 w F (fun r hr hr1 => hvf (hw r hr hr1))
      (fun r hr hr1 => hvf (hFv r hr hr1))
  have hDu : ∀ w ∈ rimDirs Γ Φ, (∀ r : ℝ, 0 < r → r ≤ 1 →
      toSph (chartC Ψ ((r : ℂ) * w)) ∈ u) → w = B := fun w _ hw =>
    hpiece fu hfu hfu0 w B (fun r hr hr1 => huf (hw r hr hr1))
      (fun r hr hr1 => huf (hBu r hr hr1))
  have hD : rimDirs Γ Φ = {F, B} := by
    ext w
    constructor
    · intro hw
      rcases hside w hw with h | h
      · exact Or.inr (hDu w hw h)
      · exact Or.inl (hDv w hw h)
    · rintro (rfl | rfl)
      · exact hFD
      · exact hBD
  -- the edge runs along `F` and `B`
  have hout : RunsOut Ψ F G t₀ (δ₀ / 2) := by
    apply runsOut_of_on_ray hΨ hG.cont hδ₀ hp (hinjJ.mono (Icc_subset_Icc (by linarith)
      (by linarith)))
    intro t ht
    obtain ⟨r, w, hr, hr1, hGt, hw⟩ := hdir t ht.1.ne' ⟨by linarith [ht.1], ht.2⟩
    have := hDv w hw (hside_v t ht r w hr hr1 hGt hw)
    exact ⟨r, hr, hr1, this ▸ hGt⟩
  have hin : RunsIn Ψ B G t₀ (δ₀ / 2) := by
    apply RunsOut.runsIn
    have hp' : IsPolar Γ ((fun t => G (-t)) (-t₀)) Φ := by simpa using hp
    apply runsOut_of_on_ray hΨ (hG.cont.comp continuous_neg) hδ₀ hp'
    · intro s hs s' hs' hss'
      have := hinjJ (x₁ := -s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
        ⟨by linarith [hs'.2], by linarith [hs'.1]⟩ hss'
      linarith
    · intro s hs
      have ht : -s ∈ Ico (t₀ - δ₀) t₀ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      obtain ⟨r, w, hr, hr1, hGt, hw⟩ := hdir (-s) ht.2.ne ⟨ht.1, by linarith [ht.2]⟩
      have := hDu w hw (hside_u (-s) ht r w hr hr1 hGt hw)
      exact ⟨r, hr, hr1, this ▸ hGt⟩
  exact ⟨Φ, Ψ, F, B, δ₀ / 2, δ₀ / 2, hp, fun y hy => (hΦO hy).2, hΨ, hpos, hD, hFB, hout, hin⟩

/-- **Positive charts at a point of an edge.** At each point `G t₀` of an edge there is a
positive polar chart whose only rays in `U(Γ)` are two distinct rays `F` and `B`; the edge runs
out along `F` after `t₀` and runs in along `B` up to `t₀`. -/
theorem exists_edge_chart (hS : IsClosedSurface (OnePoint EuclideanPlane))
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U) (he : e ∈ Γ.E)
    (hG : IsEdgeCurve Γ e G) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψ : C(ClosedUnitDisc, EuclideanPlane))
      (F B : Circle) (δ₁ δ₂ : ℝ),
      IsPolar Γ (G t₀) Φ ∧ (∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) ∧
      0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) ∧
      rimDirs Γ Φ = {F, B} ∧ F ≠ B ∧ RunsOut Ψ F G t₀ δ₁ ∧ RunsIn Ψ B G t₀ δ₂ := by
  obtain ⟨Φ, Ψ, F, B, δ₁, δ₂, hp, -, hrest⟩ :=
    exists_edge_chart_in hS hinf he hG ht₀ isOpen_univ (mem_univ (G t₀))
  exact ⟨Φ, Ψ, F, B, δ₁, δ₂, hp, hrest⟩

end EdgeChart

end GraphMinor.GM06
