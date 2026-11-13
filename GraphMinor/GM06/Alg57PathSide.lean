module

public import GraphMinor.GM06.Alg57PathChart
public import GraphMinor.GM06.Alg57CornerSide

/-!
# The side of a path, followed through charts

Let `f` be a path in the sphere drawn on a drawing `Γ`, with point set `X`. At a point `f t` with
`0 < t < 1` a *path chart* (`IsPathChart`) is a positive polar chart in which the path runs out
along a direction `F` and in along a direction `B`, and these are its only directions in `X`. The
*left wedge* of such a chart is the open cone from `F` counterclockwise to `B`
(`wedgeSet`). It is connected and it misses `X` (`disjoint_wedgeSet`).

Let `Q` be a property of points that does not change on connected sets near the path and off `X`
(`SideDich`). Then whether `Q` holds on the left wedge does not depend on the point of the path
(`exists_wedgeQ_path`). The proof follows `exists_cornerQ_edge`: the transfer steps of
`cornerRegion_transfer_aux` give a common point of the left wedges of two charts at nearby points.
The statement also covers a chart at the start of the path (the corner after the direction along
which the path leaves) and a chart at its end (the corner before the direction along which the
path arrives).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The open cone of a chart from direction `F` counterclockwise through angle `α`, in the
sphere. -/
noncomputable def wedgeSet (Ψ : C(ClosedUnitDisc, EuclideanPlane)) (F : Circle) (α : ℝ) :
    Set (OnePoint EuclideanPlane) :=
  toSph '' (chartC Ψ '' cone F α 1)

/-- A property holds on a whole set. -/
theorem iff_of_meet_dich {Q : OnePoint EuclideanPlane → Prop} {A B : Set (OnePoint EuclideanPlane)}
    (hA : (∀ x ∈ A, Q x) ∨ (∀ x ∈ A, ¬ Q x)) (hB : (∀ x ∈ B, Q x) ∨ (∀ x ∈ B, ¬ Q x))
    (h : (A ∩ B).Nonempty) : (∀ x ∈ A, Q x) ↔ (∀ x ∈ B, Q x) := by
  obtain ⟨z, hzA, hzB⟩ := h
  constructor
  · intro hQ
    rcases hB with hB | hB
    · exact hB
    · exact absurd (hQ z hzA) (hB z hzB)
  · intro hQ
    rcases hA with hA | hA
    · exact hA
    · exact absurd (hQ z hzB) (hA z hzA)

section Wedge

variable {Γ : Drawing (OnePoint EuclideanPlane)} {X : Set (OnePoint EuclideanPlane)}
  {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}
  {c : OnePoint EuclideanPlane}

theorem isPreconnected_wedgeSet (F : Circle) (α : ℝ) : IsPreconnected (wedgeSet Ψ F α) :=
  ((isPreconnected_cone _ _ _).image _ continuous_chartC.continuousOn).image _
    continuous_toSph.continuousOn

theorem wedgeSet_subset_range (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (F : Circle)
    (α : ℝ) : wedgeSet Ψ F α ⊆ range Φ := by
  rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
  rw [toSph_chartC hΨ]
  exact mem_range_self _

theorem cone_mono {w : Circle} {g g' R : ℝ} (h : g ≤ g') : cone w g R ⊆ cone w g' R := by
  rintro _ ⟨t, ht, htR, θ, hθ, hθg, rfl⟩
  exact ⟨t, ht, htR, θ, hθ, hθg.trans_le h, rfl⟩

theorem cornerSet_subset_wedgeSet (hD : (rimDirs Γ Φ).Finite) {F B : Circle}
    (hB : B ∈ rimDirs Γ Φ) : cornerSet Γ Φ Ψ F ⊆ wedgeSet Ψ F (angleTo F B) :=
  image_mono (image_mono (cone_mono (gap_le_angleTo hD F hB)))

/-- **The left wedge misses `X`** when no direction of `X` lies strictly inside it. -/
theorem disjoint_wedgeSet (hp : IsPolar Γ c Φ) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    (hX : IsGammaNice Γ X) {F : Circle} {α : ℝ}
    (hdirs : ∀ θ ∈ Ioo 0 α, polarRimMap Φ (F * Circle.exp θ) ∉ X) :
    Disjoint (wedgeSet Ψ F α) X := by
  rw [disjoint_left]
  rintro _ ⟨_, ⟨_, ⟨t, ht, ht1, θ, hθ, hθα, rfl⟩, rfl⟩, rfl⟩ hyX
  rw [← Circle.coe_mul] at hyX
  exact hdirs θ ⟨hθ, hθα⟩ ((chart_ray_mem_iff hp hΨ hX _ ht ht1).mp hyX)

end Wedge

/-- A *path chart* at `f t`: a positive polar chart with finitely many directions in which `f`
runs out along `F` and in along `B`, and these are its only directions in `X`. -/
structure IsPathChart (Γ : Drawing (OnePoint EuclideanPlane)) (X : Set (OnePoint EuclideanPlane))
    (f : ℝ → OnePoint EuclideanPlane) (t : ℝ) (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
    (Ψ : C(ClosedUnitDisc, EuclideanPlane)) (F B : Circle) : Prop where
  polar : IsPolar Γ (f t) Φ
  hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)
  pos : 0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0)
  fin : (rimDirs Γ Φ).Finite
  F_mem : F ∈ rimDirs Γ Φ
  B_mem : B ∈ rimDirs Γ Φ
  ne : F ≠ B
  out : ∃ δ, RunsOut Ψ F f t δ
  inn : ∃ δ, RunsIn Ψ B f t δ
  dirs : ∀ w, polarRimMap Φ w ∈ X → w = F ∨ w = B

namespace IsPathChart

variable {Γ : Drawing (OnePoint EuclideanPlane)} {X : Set (OnePoint EuclideanPlane)}
  {f : ℝ → OnePoint EuclideanPlane} {t : ℝ} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
  {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {F B : Circle}

/-- The left wedge of a path chart misses the path. -/
theorem disjoint (h : IsPathChart Γ X f t Φ Ψ F B) (hX : IsGammaNice Γ X) :
    Disjoint (wedgeSet Ψ F (angleTo F B)) X := by
  apply disjoint_wedgeSet h.polar h.hΨ hX
  intro θ hθ hmem
  have hθ2 : θ ∈ Ioc 0 (2 * Real.pi) := ⟨hθ.1, hθ.2.le.trans (angleTo_le F B)⟩
  rcases h.dirs _ hmem with h1 | h1
  · have := angleTo_eq hθ2 h1.symm
    rw [angleTo_self] at this
    linarith [hθ.2, angleTo_le F B]
  · have := angleTo_eq hθ2 h1.symm
    linarith [hθ.2]

/-- `Q` is constant on the left wedge of a path chart inside a set where `Q` does not change. -/
theorem dich (h : IsPathChart Γ X f t Φ Ψ F B) (hX : IsGammaNice Γ X)
    {Q : OnePoint EuclideanPlane → Prop} (hN : SideDich X Q (range Φ)) :
    (∀ x ∈ wedgeSet Ψ F (angleTo F B), Q x) ∨ (∀ x ∈ wedgeSet Ψ F (angleTo F B), ¬ Q x) :=
  hN _ (wedgeSet_subset_range h.hΨ F _) (isPreconnected_wedgeSet F _) (h.disjoint hX)

end IsPathChart

section Transfer

variable {Γ : Drawing (OnePoint EuclideanPlane)} {c₁ c₂ : OnePoint EuclideanPlane}
  {Φ₁ Φ₂ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ₁ Ψ₂ : C(ClosedUnitDisc, EuclideanPlane)}
  {G : ℝ → OnePoint EuclideanPlane}

/-- **The corner after a ray meets the left wedge before it.** In the setting of
`cornerRegion_eq_of_in`, with the curve on the ray `B₁` of the first chart, the corner set after
`W₂` meets the cone from any direction `F₁` counterclockwise to `B₁`. -/
theorem wedge_meet_of_in
    (hp₁ : IsPolar Γ c₁ Φ₁) (hΨ₁ : ∀ x, Φ₁ x = (Ψ₁ x : OnePoint EuclideanPlane))
    (hpos₁ : 0 < wind (fun w : Circle => chartC Ψ₁ w) (chartC Ψ₁ 0))
    (hD₁ : (rimDirs Γ Φ₁).Finite)
    (hp₂ : IsPolar Γ c₂ Φ₂) (hΨ₂ : ∀ x, Φ₂ x = (Ψ₂ x : OnePoint EuclideanPlane))
    (hpos₂ : 0 < wind (fun w : Circle => chartC Ψ₂ w) (chartC Ψ₂ 0))
    (hD₂ : (rimDirs Γ Φ₂).Finite)
    {F₁ B₁ W₂ : Circle} (hB₁ : B₁ ∈ rimDirs Γ Φ₁) {a δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hout : RunsOut Ψ₂ W₂ G a δ₂) (hc₂ : c₂ = G a) {ρ₁ : ℝ → ℝ}
    (hray : ∀ t ∈ Icc a (a + δ₁), 0 < ρ₁ t ∧ ρ₁ t < 1 ∧
      G t = toSph (chartC Ψ₁ ((ρ₁ t : ℂ) * B₁)))
    (hanti : StrictAntiOn ρ₁ (Icc a (a + δ₁))) :
    (cornerSet Γ Φ₂ Ψ₂ W₂ ∩ wedgeSet Ψ₁ F₁ (angleTo F₁ B₁)).Nonempty := by
  obtain ⟨ε₁, ε₂, R, s₁, s₂, s₃, t₁, t₂, t₃, hov, -, hε₁g', hε₂g, hs₁, hs₁₂, hs₂₃, hs₃, h1, h12,
    h23, h3, he₁, he₂, he₃⟩ :=
    cornerRegion_transfer_aux (W₁' := F₁) hp₁ hΨ₁ hpos₁ hD₁ hp₂ hΨ₂ hpos₂ hD₂ hB₁ hδ₁ hout hc₂
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
  rw [← mul_exp_angleTo F₁ B₁] at hy'
  refine ⟨toSph (chartC Ψ₂ y), ⟨_, ⟨y, osecP_subset_cone hov.ε₂_pos hov.ε₂_lt hε₂g
    (openSector_mono hov.R₂_le hy), rfl⟩, rfl⟩, ⟨_, ⟨y', ?_, rfl⟩, by rw [hyy]⟩⟩
  exact osecM_subset_cone hov.ε₁_pos hov.ε₁_lt
    (hε₁g'.trans_le (gap_le_angleTo hD₁ F₁ hB₁)) hy'

end Transfer

namespace IsPathChart

variable {Γ : Drawing (OnePoint EuclideanPlane)} {X : Set (OnePoint EuclideanPlane)}
  {f : ℝ → OnePoint EuclideanPlane}

/-- **Left wedges of nearby path charts meet.** -/
theorem wedge_meet {t₁ t₂ : ℝ} {Φ₁ Φ₂ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    {Ψ₁ Ψ₂ : C(ClosedUnitDisc, EuclideanPlane)} {F₁ B₁ F₂ B₂ : Circle}
    (h₁ : IsPathChart Γ X f t₁ Φ₁ Ψ₁ F₁ B₁) (h₂ : IsPathChart Γ X f t₂ Φ₂ Ψ₂ F₂ B₂)
    {δo δi : ℝ} (ho : RunsOut Ψ₁ F₁ f t₁ δo) (hi : RunsIn Ψ₁ B₁ f t₁ δi)
    (ht : t₂ ∈ Ioo (t₁ - δi) (t₁ + δo)) (hne : t₂ ≠ t₁) :
    (wedgeSet Ψ₂ F₂ (angleTo F₂ B₂) ∩ wedgeSet Ψ₁ F₁ (angleTo F₁ B₁)).Nonempty := by
  obtain ⟨δ₂, hout₂⟩ := h₂.out
  rcases lt_trichotomy t₂ t₁ with hlt | heq | hgt
  · obtain ⟨ρ, hanti, hray⟩ := hi.ray_before ⟨ht.1, hlt⟩
    obtain ⟨z, hz₂, hz₁⟩ := wedge_meet_of_in h₁.polar h₁.hΨ h₁.pos h₁.fin h₂.polar h₂.hΨ
      h₂.pos h₂.fin (F₁ := F₁) h₁.B_mem (by linarith : 0 < (t₁ - t₂) / 2) hout₂ rfl hray hanti
    exact ⟨z, cornerSet_subset_wedgeSet h₂.fin h₂.B_mem hz₂, hz₁⟩
  · exact absurd heq hne
  · obtain ⟨ρ, hmono, hray⟩ := ho.ray_after ⟨hgt, ht.2⟩
    obtain ⟨z, hz₂, hz₁⟩ := cornerSet_meet_of_out h₁.polar h₁.hΨ h₁.pos h₁.fin h₂.polar h₂.hΨ
      h₂.pos h₂.fin h₁.F_mem (by linarith [ht.2]) hout₂ rfl hray hmono
    exact ⟨z, cornerSet_subset_wedgeSet h₂.fin h₂.B_mem hz₂,
      cornerSet_subset_wedgeSet h₁.fin h₁.B_mem hz₁⟩

end IsPathChart

section Propagate

variable {Γ : Drawing (OnePoint EuclideanPlane)} {X : Set (OnePoint EuclideanPlane)}
  {f : ℝ → OnePoint EuclideanPlane} (Q : OnePoint EuclideanPlane → Prop)

/-- **The side of the left wedge is the same all along the path.** Suppose that at each inner
point of the path there is a path chart inside a set where `Q` does not change off `X`. Then one
proposition `P` decides whether `Q` holds on the left wedge of every such path chart, on the corner
after the leaving direction of a chart at the start, and on the corner before the arriving
direction of a chart at the end. -/
theorem exists_wedgeQ_path (hX : IsGammaNice Γ X)
    (hchart : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (Ψ : C(ClosedUnitDisc, EuclideanPlane)) (F B : Circle),
      IsPathChart Γ X f t Φ Ψ F B ∧ SideDich X Q (range Φ)) :
    ∃ P : Prop,
      (∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) 1 → ∀ {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
        {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {F B : Circle},
        IsPathChart Γ X f t Φ Ψ F B → SideDich X Q (range Φ) →
        ((∀ x ∈ wedgeSet Ψ F (angleTo F B), Q x) ↔ P)) ∧
      (∀ {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}
        {F : Circle} {δ : ℝ}, IsPolar Γ (f 0) Φ → (∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) →
        0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) → (rimDirs Γ Φ).Finite →
        F ∈ rimDirs Γ Φ → RunsOut Ψ F f 0 δ →
        ((∀ x ∈ cornerSet Γ Φ Ψ F, Q x) ∨ (∀ x ∈ cornerSet Γ Φ Ψ F, ¬ Q x)) →
        (CornerQ Γ Q Φ Ψ F ↔ P)) ∧
      (∀ {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}
        {B B' : Circle} {δ : ℝ}, IsPolar Γ (f 1) Φ →
        (∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) →
        0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) → (rimDirs Γ Φ).Finite →
        B ∈ rimDirs Γ Φ → B' * Circle.exp (gap (rimDirs Γ Φ) B') = B → RunsIn Ψ B f 1 δ →
        ((∀ x ∈ cornerSet Γ Φ Ψ B', Q x) ∨ (∀ x ∈ cornerSet Γ Φ Ψ B', ¬ Q x)) →
        (CornerQ Γ Q Φ Ψ B' ↔ P)) := by
  choose Φc Ψc Fc Bc hc hcN using hchart
  have hout : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), ∃ δ, RunsOut (Ψc t ht) (Fc t ht) f t δ :=
    fun t ht => (hc t ht).out
  have hin : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), ∃ δ, RunsIn (Ψc t ht) (Bc t ht) f t δ :=
    fun t ht => (hc t ht).inn
  choose δo hδo using hout
  choose δi hδi using hin
  let L : Ioo (0 : ℝ) 1 → Prop := fun t =>
    ∀ x ∈ wedgeSet (Ψc t.1 t.2) (Fc t.1 t.2) (angleTo (Fc t.1 t.2) (Bc t.1 t.2)), Q x
  have hdich : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), (∀ x ∈ wedgeSet (Ψc t ht) (Fc t ht)
      (angleTo (Fc t ht) (Bc t ht)), Q x) ∨ (∀ x ∈ wedgeSet (Ψc t ht) (Fc t ht)
      (angleTo (Fc t ht) (Bc t ht)), ¬ Q x) := fun t ht => (hc t ht).dich hX (hcN t ht)
  have hnear : ∀ t₀ (h₀ : t₀ ∈ Ioo (0 : ℝ) 1) t₁ (h₁ : t₁ ∈ Ioo (0 : ℝ) 1),
      t₁ ∈ Ioo (t₀ - δi t₀ h₀) (t₀ + δo t₀ h₀) → L ⟨t₁, h₁⟩ = L ⟨t₀, h₀⟩ := by
    intro t₀ h₀ t₁ h₁ ht
    by_cases heq : t₁ = t₀
    · subst heq; rfl
    apply propext
    exact iff_of_meet_dich (hdich t₁ h₁) (hdich t₀ h₀)
      ((hc t₀ h₀).wedge_meet (hc t₁ h₁) (hδo t₀ h₀) (hδi t₀ h₀) ht heq)
  have hlc : IsLocallyConstant L := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨t₀, h₀⟩
    have h1 := (hδo t₀ h₀).1
    have h2 := (hδi t₀ h₀).1
    have hmem : (⟨t₀, h₀⟩ : Ioo (0 : ℝ) 1) ∈
        Subtype.val ⁻¹' Ioo (t₀ - δi t₀ h₀) (t₀ + δo t₀ h₀) :=
      ⟨by linarith, by linarith⟩
    filter_upwards [(isOpen_Ioo.preimage continuous_subtype_val).mem_nhds hmem]
    rintro ⟨t₁, h₁⟩ ht
    exact hnear t₀ h₀ t₁ h₁ ht
  have : PreconnectedSpace (Ioo (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hconst : ∀ t (ht : t ∈ Ioo (0 : ℝ) 1), L ⟨t, ht⟩ = L ⟨1 / 2, hhalf⟩ := fun t ht =>
    hlc.apply_eq_of_preconnectedSpace _ _
  refine ⟨L ⟨1 / 2, hhalf⟩, ?_, ?_, ?_⟩
  · -- any path chart at an inner point
    intro t ht Φ Ψ F B h hN
    obtain ⟨δ, hδ⟩ := h.out
    obtain ⟨δ', hδ'⟩ := h.inn
    have hδp := hδ.1
    have hm : 0 < min δ (1 - t) := lt_min hδp (by linarith [ht.2])
    have hm1 := min_le_left δ (1 - t)
    have hm2 := min_le_right δ (1 - t)
    obtain ⟨t', ht'0, ht'δ, ht'1⟩ : ∃ t' : ℝ, t < t' ∧ t' < t + δ ∧ t' < 1 :=
      ⟨t + min δ (1 - t) / 2, by linarith, by linarith, by linarith⟩
    have ht' : t' ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.1], ht'1⟩
    have hmeet := h.wedge_meet (hc t' ht') hδ hδ' ⟨by linarith [hδ'.1], ht'δ⟩ ht'0.ne'
    rw [iff_of_meet_dich (h.dich hX hN) (hdich t' ht') (by
      obtain ⟨z, hz₁, hz₂⟩ := hmeet; exact ⟨z, hz₂, hz₁⟩)]
    exact Eq.to_iff (hconst t' ht')
  · -- the start
    intro Φ Ψ F δ hp hΨ hpos hD hF hrun hd
    have hδ := hrun.1
    have hm : 0 < min δ (1 / 2) := lt_min hδ (by norm_num)
    have hm1 := min_le_left δ (1 / 2)
    have hm2 := min_le_right δ (1 / 2)
    obtain ⟨ts, hts0, htsu, hts1⟩ : ∃ ts : ℝ, 0 < ts ∧ ts < δ ∧ ts < 1 :=
      ⟨min δ (1 / 2) / 2, by linarith, by linarith, by linarith⟩
    have hts : ts ∈ Ioo (0 : ℝ) 1 := ⟨hts0, hts1⟩
    obtain ⟨ρ, hmono, hray⟩ := hrun.ray_after (t₁ := ts) ⟨hts0, by linarith⟩
    obtain ⟨z, hz₂, hz₁⟩ := cornerSet_meet_of_out hp hΨ hpos hD (hc ts hts).polar (hc ts hts).hΨ
      (hc ts hts).pos (hc ts hts).fin hF (by linarith) (hδo ts hts) rfl hray hmono
    have := iff_of_meet_dich hd (hdich ts hts)
      ⟨z, hz₁, cornerSet_subset_wedgeSet (hc ts hts).fin (hc ts hts).B_mem hz₂⟩
    exact this.trans (Eq.to_iff (hconst ts hts))
  · -- the end
    intro Φ Ψ B B' δ hp hΨ hpos hD hB hprev hrun hd
    have hδ := hrun.1
    have hm : 0 < min δ (1 / 2) := lt_min hδ (by norm_num)
    have hm1 := min_le_left δ (1 / 2)
    have hm2 := min_le_right δ (1 / 2)
    obtain ⟨te, hte0, htev, hte1⟩ : ∃ te : ℝ, 0 < te ∧ 1 - δ < te ∧ te < 1 :=
      ⟨1 - min δ (1 / 2) / 2, by linarith, by linarith, by linarith⟩
    have hte : te ∈ Ioo (0 : ℝ) 1 := ⟨hte0, hte1⟩
    obtain ⟨ρ, hanti, hray⟩ := hrun.ray_before (t₁ := te) ⟨htev, hte1⟩
    obtain ⟨z, hz₂, hz₁⟩ := cornerSet_meet_of_in hp hΨ hpos hD (hc te hte).polar (hc te hte).hΨ
      (hc te hte).pos (hc te hte).fin hB hprev (by linarith [hte.2]) (hδo te hte) rfl hray hanti
    have := iff_of_meet_dich hd (hdich te hte)
      ⟨z, hz₁, cornerSet_subset_wedgeSet (hc te hte).fin (hc te hte).B_mem hz₂⟩
    exact this.trans (Eq.to_iff (hconst te hte))

end Propagate

end GraphMinor.GM06
