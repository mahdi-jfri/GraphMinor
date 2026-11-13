module

public import GraphMinor.GM06.Alg57EdgeCorner

/-!
# The side of a corner along an edge

`cornerRegion_start_eq_end` follows the region on the left of an edge. For `k = 1` of (5.7) we
need a finer fact: the points just on the left of the linkage path are all on one side of it, as
seen from the cut disc. A region can touch the path from both sides, so knowing the region is not
enough. Instead we follow a property `Q` of points along the edge.

The *corner set* after a direction `w` of a positive chart is the image of the open cone of
angle `gap` after `w` (`cornerSet`). It is connected and it misses `U(Γ)`. The two transfer
steps of `cornerRegion_eq_of_out` and `cornerRegion_eq_of_in` give a common point of two corner
sets (`cornerSet_meet_of_out`, `cornerSet_meet_of_in`).

Let `X ⊆ U(Γ)`; for us `X` is the linkage path. Suppose that near every point of the edge each
connected set that misses `X` either has `Q` at all its points or at none (`SideDich`). Then whether `Q` holds on the corner set after the
forward ray is the same at the start of the edge, at its inner points and at its end
(`exists_cornerQ_edge`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

section CornerSet

variable {Γ : Drawing (OnePoint EuclideanPlane)} {c : OnePoint EuclideanPlane}
  {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}

/-- The open corner after a direction `w` of a chart, as a set of the sphere. -/
noncomputable def cornerSet (Γ : Drawing (OnePoint EuclideanPlane))
    (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψ : C(ClosedUnitDisc, EuclideanPlane))
    (w : Circle) : Set (OnePoint EuclideanPlane) :=
  toSph '' (chartC Ψ '' cone w (gap (rimDirs Γ Φ) w) 1)

theorem isPreconnected_cornerSet (w : Circle) : IsPreconnected (cornerSet Γ Φ Ψ w) :=
  ((isPreconnected_cone _ _ _).image _ continuous_chartC.continuousOn).image _
    continuous_toSph.continuousOn

theorem cornerSet_subset_range (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (w : Circle) :
    cornerSet Γ Φ Ψ w ⊆ range Φ := by
  rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
  rw [toSph_chartC hΨ]
  exact mem_range_self _

theorem cornerSet_nonempty (hD : (rimDirs Γ Φ).Finite) (w : Circle) :
    (cornerSet Γ Φ Ψ w).Nonempty := by
  have hg := gap_pos hD w
  exact ⟨_, ⟨_, ⟨_, ⟨1, one_pos, le_rfl, _, half_pos hg, half_lt_self hg, rfl⟩, rfl⟩, rfl⟩⟩

/-- The corner set misses `U(Γ)`, since it lies in the region of the corner. -/
theorem disjoint_cornerSet (hp : IsPolar Γ c Φ) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    (hD : (rimDirs Γ Φ).Finite) (w : Circle) : Disjoint (cornerSet Γ Φ Ψ w) Γ.U :=
  disjoint_left.mpr fun _ hy hyU =>
    region_subset (cornerRegion_mem hp hΨ hD w) (image_cone_subset_cornerRegion hp hΨ hD w hy) hyU

end CornerSet

section Transfer

variable {Γ : Drawing (OnePoint EuclideanPlane)} {c₁ c₂ : OnePoint EuclideanPlane}
  {Φ₁ Φ₂ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ₁ Ψ₂ : C(ClosedUnitDisc, EuclideanPlane)}
  {G : ℝ → OnePoint EuclideanPlane}

/-- **Corner sets meet, outward.** In the setting of `cornerRegion_eq_of_out`, the corner set
after `W₂` meets the corner set after `W₁`. The common point comes from
`RayOverlap.sector_transfer_out`. -/
theorem cornerSet_meet_of_out
    (hp₁ : IsPolar Γ c₁ Φ₁) (hΨ₁ : ∀ x, Φ₁ x = (Ψ₁ x : OnePoint EuclideanPlane))
    (hpos₁ : 0 < wind (fun w : Circle => chartC Ψ₁ w) (chartC Ψ₁ 0))
    (hD₁ : (rimDirs Γ Φ₁).Finite)
    (hp₂ : IsPolar Γ c₂ Φ₂) (hΨ₂ : ∀ x, Φ₂ x = (Ψ₂ x : OnePoint EuclideanPlane))
    (hpos₂ : 0 < wind (fun w : Circle => chartC Ψ₂ w) (chartC Ψ₂ 0))
    (hD₂ : (rimDirs Γ Φ₂).Finite)
    {W₁ W₂ : Circle} (hW₁ : W₁ ∈ rimDirs Γ Φ₁) {a δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hout : RunsOut Ψ₂ W₂ G a δ₂) (hc₂ : c₂ = G a) {ρ₁ : ℝ → ℝ}
    (hray : ∀ t ∈ Icc a (a + δ₁), 0 < ρ₁ t ∧ ρ₁ t < 1 ∧
      G t = toSph (chartC Ψ₁ ((ρ₁ t : ℂ) * W₁)))
    (hmono : StrictMonoOn ρ₁ (Icc a (a + δ₁))) :
    (cornerSet Γ Φ₂ Ψ₂ W₂ ∩ cornerSet Γ Φ₁ Ψ₁ W₁).Nonempty := by
  obtain ⟨ε₁, ε₂, R, s₁, s₂, s₃, t₁, t₂, t₃, hov, hε₁g, -, hε₂g, hs₁, hs₁₂, hs₂₃, hs₃, h1, h12,
    h23, h3, he₁, he₂, he₃⟩ :=
    cornerRegion_transfer_aux (W₁' := W₁) hp₁ hΨ₁ hpos₁ hD₁ hp₂ hΨ₂ hpos₂ hD₂ hW₁ hδ₁ hout hc₂
      hray
  have hm : ∀ t, a ≤ t → t ≤ t₃ → t ∈ Icc a (a + δ₁) := fun t h h' => ⟨h, by linarith⟩
  have hτ := hray t₁ (hm _ h1.le (by linarith))
  have hτ₃ := hray t₃ (hm _ (by linarith) le_rfl)
  have hsub := hov.sector_transfer_out hs₁ hs₁₂ hs₂₃ hs₃ hτ.1
    (hmono (hm _ h1.le (by linarith)) (hm _ (by linarith) (by linarith)) h12)
    (hmono (hm _ (by linarith) (by linarith)) (hm _ (by linarith) le_rfl) h23) hτ₃.2.1.le
    he₁ he₂ he₃
  have hR := hov.R₂_pos
  obtain ⟨y, hy⟩ : (osecP W₂ ε₂ R).Nonempty :=
    ⟨_, mem_osecP_coord hov.ε₂_pos hov.ε₂_lt hR⟩
  obtain ⟨y', hy', hyy⟩ := hsub ⟨y, hy, rfl⟩
  refine ⟨toSph (chartC Ψ₂ y), ⟨_, ⟨y, osecP_subset_cone hov.ε₂_pos hov.ε₂_lt hε₂g
    (openSector_mono hov.R₂_le hy), rfl⟩, rfl⟩, ⟨_, ⟨y', ?_, rfl⟩, by rw [hyy]⟩⟩
  exact osecP_subset_cone hov.ε₁_pos hov.ε₁_lt hε₁g hy'

/-- **Corner sets meet, inward.** In the setting of `cornerRegion_eq_of_in`, the corner set
after `W₂` meets the corner set after `W₁'`, the direction of the star before `W₁`. The common
point comes from `RayOverlap.sector_transfer_in`. -/
theorem cornerSet_meet_of_in
    (hp₁ : IsPolar Γ c₁ Φ₁) (hΨ₁ : ∀ x, Φ₁ x = (Ψ₁ x : OnePoint EuclideanPlane))
    (hpos₁ : 0 < wind (fun w : Circle => chartC Ψ₁ w) (chartC Ψ₁ 0))
    (hD₁ : (rimDirs Γ Φ₁).Finite)
    (hp₂ : IsPolar Γ c₂ Φ₂) (hΨ₂ : ∀ x, Φ₂ x = (Ψ₂ x : OnePoint EuclideanPlane))
    (hpos₂ : 0 < wind (fun w : Circle => chartC Ψ₂ w) (chartC Ψ₂ 0))
    (hD₂ : (rimDirs Γ Φ₂).Finite)
    {W₁ W₁' W₂ : Circle} (hW₁ : W₁ ∈ rimDirs Γ Φ₁)
    (hprev : W₁' * Circle.exp (gap (rimDirs Γ Φ₁) W₁') = W₁) {a δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hout : RunsOut Ψ₂ W₂ G a δ₂) (hc₂ : c₂ = G a) {ρ₁ : ℝ → ℝ}
    (hray : ∀ t ∈ Icc a (a + δ₁), 0 < ρ₁ t ∧ ρ₁ t < 1 ∧
      G t = toSph (chartC Ψ₁ ((ρ₁ t : ℂ) * W₁)))
    (hanti : StrictAntiOn ρ₁ (Icc a (a + δ₁))) :
    (cornerSet Γ Φ₂ Ψ₂ W₂ ∩ cornerSet Γ Φ₁ Ψ₁ W₁').Nonempty := by
  obtain ⟨ε₁, ε₂, R, s₁, s₂, s₃, t₁, t₂, t₃, hov, -, hε₁g', hε₂g, hs₁, hs₁₂, hs₂₃, hs₃, h1, h12,
    h23, h3, he₁, he₂, he₃⟩ :=
    cornerRegion_transfer_aux (W₁' := W₁') hp₁ hΨ₁ hpos₁ hD₁ hp₂ hΨ₂ hpos₂ hD₂ hW₁ hδ₁ hout hc₂
      hray
  have hm : ∀ t, a ≤ t → t ≤ t₃ → t ∈ Icc a (a + δ₁) := fun t h h' => ⟨h, by linarith⟩
  have hτ := hray t₁ (hm _ h1.le (by linarith))
  have hτ₃ := hray t₃ (hm _ (by linarith) le_rfl)
  have hsub := hov.sector_transfer_in hs₁ hs₁₂ hs₂₃ hs₃ hτ₃.1
    (hanti (hm _ (by linarith) (by linarith)) (hm _ (by linarith) le_rfl) h23)
    (hanti (hm _ h1.le (by linarith)) (hm _ (by linarith) (by linarith)) h12) hτ.2.1.le
    he₁ he₂ he₃
  have hR := hov.R₂_pos
  obtain ⟨y, hy⟩ : (osecP W₂ ε₂ R).Nonempty :=
    ⟨_, mem_osecP_coord hov.ε₂_pos hov.ε₂_lt hR⟩
  obtain ⟨y', hy', hyy⟩ := hsub ⟨y, hy, rfl⟩
  rw [← hprev] at hy'
  refine ⟨toSph (chartC Ψ₂ y), ⟨_, ⟨y, osecP_subset_cone hov.ε₂_pos hov.ε₂_lt hε₂g
    (openSector_mono hov.R₂_le hy), rfl⟩, rfl⟩, ⟨_, ⟨y', ?_, rfl⟩, by rw [hyy]⟩⟩
  exact osecM_subset_cone hov.ε₁_pos hov.ε₁_lt hε₁g' hy'

end Transfer

section Side

variable {Γ : Drawing (OnePoint EuclideanPlane)} {e : Set (OnePoint EuclideanPlane)}
  {G : ℝ → OnePoint EuclideanPlane} (Q : OnePoint EuclideanPlane → Prop)

/-- In `N`, a property `Q` does not change inside a connected set that misses `X`. -/
def SideDich (X : Set (OnePoint EuclideanPlane)) (Q : OnePoint EuclideanPlane → Prop)
    (N : Set (OnePoint EuclideanPlane)) : Prop :=
  ∀ S ⊆ N, IsPreconnected S → Disjoint S X → (∀ x ∈ S, Q x) ∨ (∀ x ∈ S, ¬ Q x)

/-- The property `Q` holds on the corner after `w`. -/
def CornerQ (Γ : Drawing (OnePoint EuclideanPlane)) (Q : OnePoint EuclideanPlane → Prop)
    (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψ : C(ClosedUnitDisc, EuclideanPlane))
    (w : Circle) : Prop :=
  ∀ x ∈ cornerSet Γ Φ Ψ w, Q x

theorem SideDich.mono {X : Set (OnePoint EuclideanPlane)} {Q : OnePoint EuclideanPlane → Prop}
    {N N' : Set (OnePoint EuclideanPlane)} (h : SideDich X Q N) (hN : N' ⊆ N) : SideDich X Q N' :=
  fun S hS => h S (hS.trans hN)

/-- **Meeting corners have the same side.** If two corner sets meet, and `Q` does not change on
either of them, then `Q` holds on one exactly when it holds on the other. -/
theorem cornerQ_iff_of_meet {X : Set (OnePoint EuclideanPlane)} (hX : X ⊆ Γ.U)
    {c₁ c₂ : OnePoint EuclideanPlane}
    {Φ₁ Φ₂ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ₁ Ψ₂ : C(ClosedUnitDisc, EuclideanPlane)}
    (hp₁ : IsPolar Γ c₁ Φ₁) (hΨ₁ : ∀ x, Φ₁ x = (Ψ₁ x : OnePoint EuclideanPlane))
    (hD₁ : (rimDirs Γ Φ₁).Finite) (hN₁ : SideDich X Q (range Φ₁))
    (hp₂ : IsPolar Γ c₂ Φ₂) (hΨ₂ : ∀ x, Φ₂ x = (Ψ₂ x : OnePoint EuclideanPlane))
    (hD₂ : (rimDirs Γ Φ₂).Finite) (hN₂ : SideDich X Q (range Φ₂)) {W₁ W₂ : Circle}
    (hmeet : (cornerSet Γ Φ₂ Ψ₂ W₂ ∩ cornerSet Γ Φ₁ Ψ₁ W₁).Nonempty) :
    CornerQ Γ Q Φ₂ Ψ₂ W₂ ↔ CornerQ Γ Q Φ₁ Ψ₁ W₁ := by
  obtain ⟨z, hz₂, hz₁⟩ := hmeet
  have h₁ := hN₁ _ (cornerSet_subset_range hΨ₁ W₁) (isPreconnected_cornerSet W₁)
    ((disjoint_cornerSet hp₁ hΨ₁ hD₁ W₁).mono_right hX)
  have h₂ := hN₂ _ (cornerSet_subset_range hΨ₂ W₂) (isPreconnected_cornerSet W₂)
    ((disjoint_cornerSet hp₂ hΨ₂ hD₂ W₂).mono_right hX)
  constructor
  · intro hQ
    rcases h₁ with h | h
    · exact h
    · exact absurd (hQ z hz₂) (h z hz₁)
  · intro hQ
    rcases h₂ with h | h
    · exact h
    · exact absurd (hQ z hz₁) (h z hz₂)

/-- **The side of the left corner is the same all along an edge.** Let `X ⊆ U(Γ)`, and suppose
that near every inner point of an edge `Q` does not change on connected sets that miss `X`. Then there is one
proposition `P` such that, at each chart at a point of the edge in which the edge runs out along
a ray, `Q` holds on the corner after that ray exactly when `P` holds. The same is true at the
end of the edge for the corner before the ray along which the edge runs in. The proof is the one
of `cornerRegion_start_eq_end`, with `cornerQ_iff_of_meet` in place of equal regions. -/
theorem exists_cornerQ_edge (hS : IsClosedSurface (OnePoint EuclideanPlane))
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U) (he : e ∈ Γ.E)
    (hG : IsEdgeCurve Γ e G) {X : Set (OnePoint EuclideanPlane)} (hX : X ⊆ Γ.U)
    (hN : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ N, IsOpen N ∧ G t ∈ N ∧ SideDich X Q N) :
    ∃ P : Prop,
      (∀ {b : ℝ}, b ∈ Ico (0 : ℝ) 1 →
        ∀ {Φb : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψb : C(ClosedUnitDisc, EuclideanPlane)},
        IsPolar Γ (G b) Φb → (∀ x, Φb x = (Ψb x : OnePoint EuclideanPlane)) →
        0 < wind (fun w : Circle => chartC Ψb w) (chartC Ψb 0) → (rimDirs Γ Φb).Finite →
        SideDich X Q (range Φb) → ∀ {Wb : Circle}, Wb ∈ rimDirs Γ Φb → ∀ {δb : ℝ},
        RunsOut Ψb Wb G b δb → (CornerQ Γ Q Φb Ψb Wb ↔ P)) ∧
      (∀ {Φv : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψv : C(ClosedUnitDisc, EuclideanPlane)},
        IsPolar Γ (G 1) Φv → (∀ x, Φv x = (Ψv x : OnePoint EuclideanPlane)) →
        0 < wind (fun w : Circle => chartC Ψv w) (chartC Ψv 0) → (rimDirs Γ Φv).Finite →
        SideDich X Q (range Φv) → ∀ {Wv Wv' : Circle}, Wv ∈ rimDirs Γ Φv →
        Wv' * Circle.exp (gap (rimDirs Γ Φv) Wv') = Wv → ∀ {δv : ℝ},
        RunsIn Ψv Wv G 1 δv → (CornerQ Γ Q Φv Ψv Wv' ↔ P)) := by
  choose N hNo hGN hND using hN
  have hchart := fun t (ht : t ∈ Ioo (0 : ℝ) 1) =>
    exists_edge_chart_in hS hinf he hG ht (hNo t ht) (hGN t ht)
  choose Φ Ψ F B δ₁ δ₂ hp hΦN hΨ hpos hD hFB hout hin using hchart
  let L : Ioo (0 : ℝ) 1 → Prop := fun t => CornerQ Γ Q (Φ t.1 t.2) (Ψ t.1 t.2) (F t.1 t.2)
  have hdich : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), SideDich X Q (range (Φ t ht)) := fun t ht =>
    (hND t ht).mono (hΦN t ht)
  have hfin : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), (rimDirs Γ (Φ t ht)).Finite := fun t ht => by
    rw [hD t ht]; exact (finite_singleton _).insert _
  have hFD : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), F t ht ∈ rimDirs Γ (Φ t ht) := fun t ht => by
    rw [hD t ht]; exact mem_insert _ _
  have hBD : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), B t ht ∈ rimDirs Γ (Φ t ht) := fun t ht => by
    rw [hD t ht]; exact mem_insert_of_mem _ (mem_singleton _)
  have hFBprev : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1),
      F t ht * Circle.exp (gap (rimDirs Γ (Φ t ht)) (F t ht)) = B t ht := fun t ht => by
    rw [hD t ht]; exact mul_exp_gap_pair (hFB t ht)
  -- nearby charts on the edge give the same side
  have hnear : ∀ t₀ (h₀ : t₀ ∈ Ioo (0 : ℝ) 1) t₁ (h₁ : t₁ ∈ Ioo (0 : ℝ) 1),
      t₁ ∈ Ioo (t₀ - δ₂ t₀ h₀) (t₀ + δ₁ t₀ h₀) → L ⟨t₁, h₁⟩ = L ⟨t₀, h₀⟩ := by
    intro t₀ h₀ t₁ h₁ ht
    apply propext
    rcases lt_trichotomy t₁ t₀ with hlt | heq | hgt
    · obtain ⟨ρ, hanti, hray⟩ := (hin t₀ h₀).ray_before ⟨ht.1, hlt⟩
      exact cornerQ_iff_of_meet Q hX (hp t₀ h₀) (hΨ t₀ h₀) (hfin t₀ h₀) (hdich t₀ h₀) (hp t₁ h₁)
        (hΨ t₁ h₁) (hfin t₁ h₁) (hdich t₁ h₁)
        (cornerSet_meet_of_in (hp t₀ h₀) (hΨ t₀ h₀) (hpos t₀ h₀) (hfin t₀ h₀) (hp t₁ h₁)
        (hΨ t₁ h₁) (hpos t₁ h₁) (hfin t₁ h₁) (hBD t₀ h₀) (hFBprev t₀ h₀)
        (by linarith : 0 < (t₀ - t₁) / 2) (hout t₁ h₁) rfl hray hanti)
    · subst heq; exact Iff.rfl
    · obtain ⟨ρ, hmono, hray⟩ := (hout t₀ h₀).ray_after ⟨hgt, ht.2⟩
      exact cornerQ_iff_of_meet Q hX (hp t₀ h₀) (hΨ t₀ h₀) (hfin t₀ h₀) (hdich t₀ h₀) (hp t₁ h₁)
        (hΨ t₁ h₁) (hfin t₁ h₁) (hdich t₁ h₁)
        (cornerSet_meet_of_out (hp t₀ h₀) (hΨ t₀ h₀) (hpos t₀ h₀) (hfin t₀ h₀) (hp t₁ h₁)
        (hΨ t₁ h₁) (hpos t₁ h₁) (hfin t₁ h₁) (hFD t₀ h₀) (by linarith [ht.2])
        (hout t₁ h₁) rfl hray hmono)
  -- so the side is the same all along the edge
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
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨L ⟨1 / 2, hhalf⟩, ?_, ?_⟩
  · -- a chart running out at time `b` has the side of an edge chart just after `b`
    intro b hb Φb Ψb hpb hΨb hposb hDb hNb Wb hWb δb hrunb
    have hδb : 0 < δb := hrunb.1
    have hm1 := min_le_left δb (1 - b)
    have hm2 := min_le_right δb (1 - b)
    have hm : 0 < min δb (1 - b) := lt_min hδb (by linarith [hb.2])
    obtain ⟨ts, hts0, htsu, hts1⟩ : ∃ ts : ℝ, b < ts ∧ ts < b + δb ∧ ts < 1 :=
      ⟨b + min δb (1 - b) / 2, by linarith, by linarith, by linarith⟩
    have hts : ts ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hts1⟩
    obtain ⟨ρ, hmono, hray⟩ := hrunb.ray_after (t₁ := ts) ⟨hts0, htsu⟩
    have h := cornerQ_iff_of_meet Q hX hpb hΨb hDb hNb (hp ts hts) (hΨ ts hts) (hfin ts hts)
      (hdich ts hts) (cornerSet_meet_of_out hpb hΨb hposb hDb (hp ts hts) (hΨ ts hts)
      (hpos ts hts) (hfin ts hts) hWb (by linarith) (hout ts hts) rfl hray hmono)
    rw [← h]
    exact Eq.to_iff (hlc.apply_eq_of_preconnectedSpace ⟨ts, hts⟩ _)
  · -- the end
    intro Φv Ψv hpv hΨv hposv hDv hNv Wv Wv' hWv hprev δv hrunv
    have hδv : 0 < δv := hrunv.1
    obtain ⟨te, hte0, htev, hte1⟩ : ∃ te : ℝ, 0 < te ∧ 1 - δv < te ∧ te < 1 :=
      ⟨1 - min δv (1 / 2) / 2, by linarith [min_le_right δv (1 / 2)],
        by linarith [min_le_left δv (1 / 2),
          half_lt_self (lt_min hδv (by norm_num : (0:ℝ) < 1 / 2))],
        by linarith [half_pos (lt_min hδv (by norm_num : (0:ℝ) < 1 / 2))]⟩
    have hte : te ∈ Ioo (0 : ℝ) 1 := ⟨hte0, hte1⟩
    obtain ⟨ρ, hanti, hray⟩ := hrunv.ray_before (t₁ := te) ⟨htev, hte1⟩
    have h := cornerQ_iff_of_meet Q hX hpv hΨv hDv hNv (hp te hte) (hΨ te hte) (hfin te hte)
      (hdich te hte) (cornerSet_meet_of_in hpv hΨv hposv hDv (hp te hte) (hΨ te hte)
      (hpos te hte) (hfin te hte) hWv hprev (by linarith [hte.2]) (hout te hte) rfl hray hanti)
    rw [← h]
    exact Eq.to_iff (hlc.apply_eq_of_preconnectedSpace ⟨te, hte⟩ _)

/-- **Passing a direction off `X`.** In a chart, if the ray of the direction `w'` after `w` misses
`X`, then `Q` holds on the corner after `w` exactly when it holds on the corner after `w'`. Both
corners and the ray between them lie in one connected cone that misses `X`. -/
theorem cornerQ_iff_next {X : Set (OnePoint EuclideanPlane)} (hX : X ⊆ Γ.U)
    {c : OnePoint EuclideanPlane} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    {Ψ : C(ClosedUnitDisc, EuclideanPlane)} (hp : IsPolar Γ c Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (hD : (rimDirs Γ Φ).Finite)
    (hN : SideDich X Q (range Φ)) (w : Circle)
    (hray : ∀ r : ℝ, 0 < r → r ≤ 1 →
      toSph (chartC Ψ ((r : ℂ) * (w * Circle.exp (gap (rimDirs Γ Φ) w) : Circle))) ∉ X) :
    CornerQ Γ Q Φ Ψ w ↔ CornerQ Γ Q Φ Ψ (w * Circle.exp (gap (rimDirs Γ Φ) w)) := by
  set g := gap (rimDirs Γ Φ) w with hg_def
  set w' := w * Circle.exp g with hw'
  set g' := gap (rimDirs Γ Φ) w'
  have hg := gap_pos hD w
  have hg' := gap_pos hD w'
  set S := toSph '' (chartC Ψ '' cone w (g + g') 1)
  have hSN : S ⊆ range Φ := by
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    rw [toSph_chartC hΨ]
    exact mem_range_self _
  have hSc : IsPreconnected S :=
    ((isPreconnected_cone _ _ _).image _ continuous_chartC.continuousOn).image _
      continuous_toSph.continuousOn
  have hSX : Disjoint S X := by
    rw [disjoint_left]
    rintro _ ⟨_, ⟨_, ⟨t, ht, ht1, θ, hθ, hθg, rfl⟩, rfl⟩, rfl⟩ hyX
    rcases lt_trichotomy θ g with hlt | heq | hgt
    · rw [← Circle.coe_mul] at hyX
      have := (chart_ray_mem_iff hp hΨ (isGammaNice_U Γ) _ ht ht1).mp (hX hyX)
      exact rim_notMem_U_of_lt_gap hp hΨ hD w hθ hlt this
    · subst heq
      exact hray t ht ht1 (by rwa [← Circle.coe_mul] at hyX)
    · have hdir : w * Circle.exp θ = w' * Circle.exp (θ - g) := by
        rw [hw', mul_assoc, ← Circle.exp_add]; ring_nf
      rw [← Circle.coe_mul, hdir] at hyX
      have := (chart_ray_mem_iff hp hΨ (isGammaNice_U Γ) _ ht ht1).mp (hX hyX)
      exact rim_notMem_U_of_lt_gap hp hΨ hD w' (by linarith) (by linarith) this
  have h₁ : cornerSet Γ Φ Ψ w ⊆ S := by
    rintro _ ⟨_, ⟨_, ⟨t, ht, ht1, θ, hθ, hθg, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨t, ht, ht1, θ, hθ, by linarith, rfl⟩, rfl⟩, rfl⟩
  have h₂ : cornerSet Γ Φ Ψ w' ⊆ S := by
    rintro _ ⟨_, ⟨_, ⟨t, ht, ht1, θ, hθ, hθg, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨t, ht, ht1, g + θ, by linarith, by linarith, ?_⟩, rfl⟩, rfl⟩
    rw [Circle.exp_add, hw']
    push_cast
    ring
  rcases hN S hSN hSc hSX with h | h
  · exact ⟨fun _ x hx => h x (h₂ hx), fun _ x hx => h x (h₁ hx)⟩
  · obtain ⟨z₁, hz₁⟩ := cornerSet_nonempty (Ψ := Ψ) hD w
    obtain ⟨z₂, hz₂⟩ := cornerSet_nonempty (Ψ := Ψ) hD w'
    exact ⟨fun hQ => absurd (hQ z₁ hz₁) (h z₁ (h₁ hz₁)),
      fun hQ => absurd (hQ z₂ hz₂) (h z₂ (h₂ hz₂))⟩

/-- **Passing several directions off `X`.** Going counterclockwise from `w` past `n` directions
whose rays miss `X` does not change the side of the corner. This is `cornerQ_iff_next` used `n`
times. -/
theorem cornerQ_iff_iterate_next {X : Set (OnePoint EuclideanPlane)} (hX : X ⊆ Γ.U)
    {c : OnePoint EuclideanPlane} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    {Ψ : C(ClosedUnitDisc, EuclideanPlane)} (hp : IsPolar Γ c Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (hD : (rimDirs Γ Φ).Finite)
    (hN : SideDich X Q (range Φ)) (w : Circle) (n : ℕ)
    (hray : ∀ i < n, ∀ r : ℝ, 0 < r → r ≤ 1 →
      toSph (chartC Ψ ((r : ℂ) *
        ((fun u => u * Circle.exp (gap (rimDirs Γ Φ) u))^[i + 1] w : Circle))) ∉ X) :
    CornerQ Γ Q Φ Ψ w ↔
      CornerQ Γ Q Φ Ψ ((fun u => u * Circle.exp (gap (rimDirs Γ Φ) u))^[n] w) := by
  induction n with
  | zero => exact Iff.rfl
  | succ n ih =>
    rw [ih fun i hi => hray i (Nat.lt_succ_of_lt hi), Function.iterate_succ_apply']
    apply cornerQ_iff_next Q hX hp hΨ hD hN
    intro r hr hr1
    have := hray n (Nat.lt_succ_self n) r hr hr1
    rwa [Function.iterate_succ_apply'] at this

end Side

end GraphMinor.GM06
