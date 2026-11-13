module

public import GraphMinor.GM06.Alg57ModelSectors
import GraphMinor.GM19.CircleOrder
import GraphMinor.Surface.InvarianceOfDomain

/-!
# Moving a side of a ray from one chart to another

Step 1 of the proof of Lemma 3 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) follows
the half-band on the left of an edge. In Lean we follow it through a chain of positive charts.
Two charts `χ₁` and `χ₂` overlap near a point of the edge. In both charts the edge is a ray.
Here we show which thin sector beside the ray of `χ₂` lies in which thin sector beside the ray
of `χ₁`.

The thin sector of `χ₂` is connected and misses the edge, so its image lies on one side of the
ray of `χ₁` (`image_subset_osecP_or_osecM`). The orientation decides which side
(`sector_transfer_out`, `sector_transfer_in`). If the ray of `χ₂` runs outward along the ray of
`χ₁`, then the counterclockwise side goes to the counterclockwise side. If it runs inward, it
goes to the clockwise side. The proof reads three points of the ray in the two nested discs and
uses `order_of_nested`.

A chart here is a map `χ : ℂ → ℂ`, continuous and injective on the closed unit disc, whose
boundary circle winds positively around `χ 0`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface

/-- On common boundary points, the positive order of a smaller disc is that of a larger disc. -/
theorem planePos_mono {Δ₁ Δ₂ : Set ℂ} (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂)
    (hsub : Δ₁ ⊆ Δ₂) {a b c : ℂ} (ha : a ∈ discBd Δ₂) (hb : b ∈ discBd Δ₂)
    (hc : c ∈ discBd Δ₂) (h : planePos Δ₁ a b c) : planePos Δ₂ a b c := by
  obtain ⟨φ, u, v, w, hφ, rfl, rfl, rfl, hcy⟩ := h
  obtain ⟨ψ, hψ⟩ := exists_posParam h₂
  have hr : range ψ = discBd Δ₂ := hψ.2.2.1
  obtain ⟨u', hu'⟩ : φ u ∈ range ψ := hr ▸ ha
  obtain ⟨v', hv'⟩ : φ v ∈ range ψ := hr ▸ hb
  obtain ⟨w', hw'⟩ : φ w ∈ range ψ := hr ▸ hc
  exact ⟨ψ, u', v', w', hψ, hu', hv', hw',
    order_of_nested h₁ h₂ hsub hφ hψ hcy hu'.symm hv'.symm hw'.symm⟩

/-- A cyclic triple read backwards is not cyclic. -/
theorem not_circleCyclic_rev {a b c : Circle} (h : CircleCyclic a b c) (h' : CircleCyclic c b a) :
    False := by
  have h1 : CircleCyclic b a c := GM19.CircleCyclic.rotate h'
  have h2 : CircleCyclic a c b := GM19.CircleCyclic.rotate h1
  exact not_circleCyclic_both h h2

section Charts

variable {χ₁ χ₂ : ℂ → ℂ}

/-- **Nested convex pieces of two charts keep the order of common boundary points.** If a
convex piece of `χ₂` lies in a convex piece of `χ₁`, then three common boundary points cannot
be in counterclockwise order in the first and in clockwise order in the second. -/
theorem false_of_nested_reversed (h₁c : Continuous χ₁) (h₁i : InjOn χ₁ (closedBall 0 1))
    (h₁p : 0 < wind (fun w : Circle => χ₁ w) (χ₁ 0)) (h₂c : Continuous χ₂)
    (h₂i : InjOn χ₂ (closedBall 0 1)) (h₂p : 0 < wind (fun w : Circle => χ₂ w) (χ₂ 0))
    {K₁ K₂ : Set ℂ} (hK₁c : Convex ℝ K₁) (hK₁cl : IsClosed K₁) (hK₁ : K₁ ⊆ closedBall 0 1)
    (hK₂c : Convex ℝ K₂) (hK₂cl : IsClosed K₂) (hK₂ : K₂ ⊆ closedBall 0 1)
    {p₁ p₂ : ℂ} (hp₁ : p₁ ∈ interior K₁) (hp₂ : p₂ ∈ interior K₂)
    (hsub : χ₂ '' K₂ ⊆ χ₁ '' K₁) {a₁ a₂ a₃ b₁ b₂ b₃ : ℂ}
    (ha₁ : a₁ ∈ frontier K₂) (ha₂ : a₂ ∈ frontier K₂) (ha₃ : a₃ ∈ frontier K₂)
    (hb₁ : b₁ ∈ frontier K₁) (hb₂ : b₂ ∈ frontier K₁) (hb₃ : b₃ ∈ frontier K₁)
    (he₁ : χ₂ a₁ = χ₁ b₁) (he₂ : χ₂ a₂ = χ₁ b₂) (he₃ : χ₂ a₃ = χ₁ b₃)
    (na₁ : a₁ - p₂ ≠ 0) (na₂ : a₂ - p₂ ≠ 0) (na₃ : a₃ - p₂ ≠ 0)
    (nb₁ : b₁ - p₁ ≠ 0) (nb₂ : b₂ - p₁ ≠ 0) (nb₃ : b₃ - p₁ ≠ 0)
    (hcy₂ : CircleCyclic (unitOf _ na₁) (unitOf _ na₂) (unitOf _ na₃))
    (hcy₁ : CircleCyclic (unitOf _ nb₃) (unitOf _ nb₂) (unitOf _ nb₁)) : False := by
  obtain ⟨hD₁, hbd₁, hpos₁⟩ := planePos_chart_convex h₁c h₁i h₁p hK₁c hK₁cl hK₁ hp₁
  obtain ⟨hD₂, -, hpos₂⟩ := planePos_chart_convex h₂c h₂i h₂p hK₂c hK₂cl hK₂ hp₂
  have h2 : planePos (χ₂ '' K₂) (χ₂ a₁) (χ₂ a₂) (χ₂ a₃) :=
    (hpos₂ a₁ ha₁ a₂ ha₂ a₃ ha₃ na₁ na₂ na₃).mpr hcy₂
  rw [he₁, he₂, he₃] at h2
  have hm : ∀ b ∈ frontier K₁, χ₁ b ∈ discBd (χ₁ '' K₁) := fun b hb => by
    rw [hbd₁]; exact mem_image_of_mem _ hb
  have h1 := planePos_mono hD₂ hD₁ hsub (hm b₁ hb₁) (hm b₂ hb₂) (hm b₃ hb₃) h2
  exact not_circleCyclic_rev ((hpos₁ b₁ hb₁ b₂ hb₂ b₃ hb₃ nb₁ nb₂ nb₃).mp h1) hcy₁

/-- A preconnected set that a chart `χ₂` maps into the double sector of the ray of `χ₁`, off
that ray, lies on one side of the ray. -/
theorem image_subset_osecP_or_osecM (h₁c : Continuous χ₁) (h₁i : InjOn χ₁ (closedBall 0 1))
    {W : Circle} {ε : ℝ} (hε : 0 < ε) (hε' : ε < Real.pi / 2) {X : Set ℂ}
    (hray : ∀ t : ℝ, 0 < t → t < 1 → χ₁ ((t : ℂ) * W) ∈ X) {P : Set ℂ}
    (hP : IsPreconnected (χ₂ '' P)) (hPsub : χ₂ '' P ⊆ χ₁ '' dsec W ε 1)
    (hPX : Disjoint (χ₂ '' P) X) :
    χ₂ '' P ⊆ χ₁ '' osecP W ε 1 ∨ χ₂ '' P ⊆ χ₁ '' osecM W ε 1 := by
  have hball : ∀ {Q : Set ℂ}, Q ⊆ dsec W ε 1 → Q ⊆ ball 0 1 := fun hQ _ hz =>
    mem_ball_zero_iff.mpr (hQ hz).1
  have hopen : ∀ {Q : Set ℂ}, IsOpen Q → Q ⊆ dsec W ε 1 → IsOpen (χ₁ '' Q) := fun hQo hQ =>
    isOpen_image_of_injOn hQo (h₁c.continuousOn)
      (h₁i.mono ((hball hQ).trans ball_subset_closedBall))
  have hoP := hopen (isOpen_openSector _ _ _) (osecP_subset_dsec hε hε')
  have hoM := hopen (isOpen_openSector _ _ _) (osecM_subset_dsec hε hε')
  have hcover : χ₂ '' P ⊆ χ₁ '' osecP W ε 1 ∪ χ₁ '' osecM W ε 1 := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hPsub hy
    rcases dsec_cases hε hε' hz with h | h | ⟨hpos, hzeq⟩
    · exact Or.inl ⟨z, h, hzy⟩
    · exact Or.inr ⟨z, h, hzy⟩
    · exfalso
      have hlt : along W z < 1 := by
        have h1 := hz.1
        have h2 := norm_eq_along_across W z
        nlinarith [sq_nonneg (across W z), norm_nonneg z]
      have := hray _ hpos hlt
      rw [← hzeq, hzy] at this
      exact Set.disjoint_left.mp hPX hy this
  have hdisj : Disjoint (χ₁ '' osecP W ε 1) (χ₁ '' osecM W ε 1) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', he⟩
    have hzz : z' = z := h₁i
      (ball_subset_closedBall (hball (osecM_subset_dsec hε hε') hz'))
      (ball_subset_closedBall (hball (osecP_subset_dsec hε hε') hz)) he
    subst hzz
    exact Set.disjoint_left.mp disjoint_osecP_osecM hz hz'
  rcases isPreconnected_iff_subset_of_disjoint.mp hP _ _ hoP hoM hcover
      (by
        have := Set.disjoint_iff_inter_eq_empty.mp hdisj
        simp only [osecP, osecM] at this
        rw [this, inter_empty]) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The image of a closed sector under a chart is closed. -/
theorem isClosed_image_sector (hc : Continuous χ₁) (A B : Circle) (R : ℝ) :
    IsClosed (χ₁ '' sector A B R) :=
  ((isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_sector A B R)
    (sector_subset_closedBall A B R) |>.image hc).isClosed

/-- If a chart maps an open sector into the image of another open sector, it maps the closed
sector into the image of the other closed sector. -/
theorem image_sector_subset {A B A' B' : Circle} {R R' : ℝ} (h₁c : Continuous χ₁)
    (h₂c : Continuous χ₂) {p : ℂ} (hp : p ∈ openSector A B R)
    (h : χ₂ '' openSector A B R ⊆ χ₁ '' openSector A' B' R') :
    χ₂ '' sector A B R ⊆ χ₁ '' sector A' B' R' := by
  calc χ₂ '' sector A B R ⊆ χ₂ '' closure (openSector A B R) :=
        image_mono (sector_subset_closure_openSector hp)
    _ ⊆ closure (χ₂ '' openSector A B R) := image_closure_subset_closure_image h₂c
    _ ⊆ closure (χ₁ '' sector A' B' R') :=
        closure_mono (h.trans (image_mono (openSector_subset_sector _ _ _)))
    _ = χ₁ '' sector A' B' R' := (isClosed_image_sector h₁c A' B' R').closure_eq

/-- The ray of a sector does not meet a point strictly on the counterclockwise side. -/
theorem ray_sub_ne_of_across_pos {W : Circle} {q : ℂ} (hq : 0 < across W q) (t : ℝ) :
    (t : ℂ) * W - q ≠ 0 := by
  intro h
  have : across W ((t : ℂ) * W) = across W q := by rw [sub_eq_zero.mp h]
  rw [across_ray] at this
  linarith

/-- The ray of a sector does not meet a point strictly on the clockwise side. -/
theorem ray_sub_ne_of_across_neg {W : Circle} {q : ℂ} (hq : across W q < 0) (t : ℝ) :
    (t : ℂ) * W - q ≠ 0 := by
  intro h
  have : across W ((t : ℂ) * W) = across W q := by rw [sub_eq_zero.mp h]
  rw [across_ray] at this
  linarith

/-- The hypotheses on two charts and a ray shared by both, used by the transfer lemmas. -/
structure RayOverlap (χ₁ χ₂ : ℂ → ℂ) (W₁ W₂ : Circle) (ε₁ ε₂ R₂ : ℝ) (X : Set ℂ) : Prop where
  cont₁ : Continuous χ₁
  inj₁ : InjOn χ₁ (closedBall 0 1)
  pos₁ : 0 < wind (fun w : Circle => χ₁ w) (χ₁ 0)
  cont₂ : Continuous χ₂
  inj₂ : InjOn χ₂ (closedBall 0 1)
  pos₂ : 0 < wind (fun w : Circle => χ₂ w) (χ₂ 0)
  ε₁_pos : 0 < ε₁
  ε₁_lt : ε₁ < Real.pi / 2
  ε₂_pos : 0 < ε₂
  ε₂_lt : ε₂ < Real.pi / 2
  R₂_pos : 0 < R₂
  R₂_le : R₂ ≤ 1
  ball : χ₂ '' closedBall 0 R₂ ⊆ χ₁ '' dsec W₁ ε₁ 1
  ray : ∀ t : ℝ, 0 < t → t < 1 → χ₁ ((t : ℂ) * W₁) ∈ X
  off : Disjoint (χ₂ '' osecP W₂ ε₂ R₂) X

theorem RayOverlap.osecP_side {W₁ W₂ : Circle} {ε₁ ε₂ R₂ : ℝ} {X : Set ℂ}
    (h : RayOverlap χ₁ χ₂ W₁ W₂ ε₁ ε₂ R₂ X) :
    χ₂ '' osecP W₂ ε₂ R₂ ⊆ χ₁ '' osecP W₁ ε₁ 1 ∨ χ₂ '' osecP W₂ ε₂ R₂ ⊆ χ₁ '' osecM W₁ ε₁ 1 :=
  image_subset_osecP_or_osecM h.cont₁ h.inj₁ h.ε₁_pos h.ε₁_lt h.ray
    ((convex_openSector _ _ _).isPreconnected.image _ h.cont₂.continuousOn)
    ((image_mono fun _ hz => mem_closedBall_zero_iff.mpr (hz.1.le)).trans h.ball) h.off

/-- **Outward transfer.** If the ray of `χ₂` runs outward along the ray of `χ₁`, the thin
counterclockwise sector of `χ₂` lies in the thin counterclockwise sector of `χ₁`. Three points
`sᵢ` of the ray of `χ₂` with images `τᵢ` on the ray of `χ₁` witness the direction. -/
theorem RayOverlap.sector_transfer_out {W₁ W₂ : Circle} {ε₁ ε₂ R₂ : ℝ} {X : Set ℂ}
    (h : RayOverlap χ₁ χ₂ W₁ W₂ ε₁ ε₂ R₂ X) {s₁ s₂ s₃ τ₁ τ₂ τ₃ : ℝ}
    (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂) (hs₂₃ : s₂ < s₃) (hs₃ : s₃ ≤ R₂)
    (hτ₁ : 0 < τ₁) (hτ₁₂ : τ₁ < τ₂) (hτ₂₃ : τ₂ < τ₃) (hτ₃ : τ₃ ≤ 1)
    (he₁ : χ₂ ((s₁ : ℂ) * W₂) = χ₁ ((τ₁ : ℂ) * W₁))
    (he₂ : χ₂ ((s₂ : ℂ) * W₂) = χ₁ ((τ₂ : ℂ) * W₁))
    (he₃ : χ₂ ((s₃ : ℂ) * W₂) = χ₁ ((τ₃ : ℂ) * W₁)) :
    χ₂ '' osecP W₂ ε₂ R₂ ⊆ χ₁ '' osecP W₁ ε₁ 1 := by
  rcases h.osecP_side with hP | hM
  · exact hP
  exfalso
  have hε₁ := h.ε₁_pos; have hε₁' := h.ε₁_lt; have hε₂ := h.ε₂_pos; have hε₂' := h.ε₂_lt
  have hR₂ := h.R₂_pos
  set p₂ := coordPt W₂ (R₂ / 2) (Real.sin ε₂ * (R₂ / 2) / 2)
  set p₁ := coordPt W₁ (1 / 2) (-(Real.sin ε₁ * (1 / 2) / 2))
  have hp₂ : p₂ ∈ osecP W₂ ε₂ R₂ := mem_osecP_coord hε₂ hε₂' hR₂
  have hp₁ : p₁ ∈ osecM W₁ ε₁ 1 := mem_osecM_coord hε₁ hε₁' one_pos
  have hs := Real.sin_pos_of_pos_of_lt_pi hε₂ (by linarith [Real.pi_pos])
  have hs' := Real.sin_pos_of_pos_of_lt_pi hε₁ (by linarith [Real.pi_pos])
  have hq₂ : 0 < across W₂ p₂ := by rw [across_coordPt]; positivity
  have hq₁ : across W₁ p₁ < 0 := by rw [across_coordPt]; nlinarith
  have hsub : χ₂ '' secP W₂ ε₂ R₂ ⊆ χ₁ '' secM W₁ ε₁ 1 :=
    image_sector_subset h.cont₁ h.cont₂ hp₂ hM
  exact false_of_nested_reversed h.cont₁ h.inj₁ h.pos₁ h.cont₂ h.inj₂ h.pos₂
    (convex_sector _ _ _) (isClosed_sector _ _ _) (sector_subset_closedBall _ _ _)
    (convex_sector _ _ _) (isClosed_sector _ _ _)
    ((sector_subset_closedBall _ _ _).trans (closedBall_subset_closedBall h.R₂_le))
    (openSector_subset_interior _ _ _ hp₁) (openSector_subset_interior _ _ _ hp₂) hsub
    (ray_mem_frontier_secP hε₂ hε₂' hs₁.le (by linarith))
    (ray_mem_frontier_secP hε₂ hε₂' (by linarith) (by linarith))
    (ray_mem_frontier_secP hε₂ hε₂' (by linarith) hs₃)
    (ray_mem_frontier_secM hε₁ hε₁' hτ₁.le (by linarith))
    (ray_mem_frontier_secM hε₁ hε₁' (by linarith) (by linarith))
    (ray_mem_frontier_secM hε₁ hε₁' (by linarith) hτ₃) he₁ he₂ he₃
    (ray_sub_ne_of_across_pos hq₂ _) (ray_sub_ne_of_across_pos hq₂ _)
    (ray_sub_ne_of_across_pos hq₂ _) (ray_sub_ne_of_across_neg hq₁ _)
    (ray_sub_ne_of_across_neg hq₁ _) (ray_sub_ne_of_across_neg hq₁ _)
    (circleCyclic_ray W₂ hq₂ hs₁₂ hs₂₃ _ _ _)
    (circleCyclic_ray_rev W₁ hq₁ hτ₁₂ hτ₂₃ _ _ _)

/-- **Inward transfer.** If the ray of `χ₂` runs inward along the ray of `χ₁`, the thin
counterclockwise sector of `χ₂` lies in the thin clockwise sector of `χ₁`. -/
theorem RayOverlap.sector_transfer_in {W₁ W₂ : Circle} {ε₁ ε₂ R₂ : ℝ} {X : Set ℂ}
    (h : RayOverlap χ₁ χ₂ W₁ W₂ ε₁ ε₂ R₂ X) {s₁ s₂ s₃ τ₁ τ₂ τ₃ : ℝ}
    (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂) (hs₂₃ : s₂ < s₃) (hs₃ : s₃ ≤ R₂)
    (hτ₃ : 0 < τ₃) (hτ₃₂ : τ₃ < τ₂) (hτ₂₁ : τ₂ < τ₁) (hτ₁ : τ₁ ≤ 1)
    (he₁ : χ₂ ((s₁ : ℂ) * W₂) = χ₁ ((τ₁ : ℂ) * W₁))
    (he₂ : χ₂ ((s₂ : ℂ) * W₂) = χ₁ ((τ₂ : ℂ) * W₁))
    (he₃ : χ₂ ((s₃ : ℂ) * W₂) = χ₁ ((τ₃ : ℂ) * W₁)) :
    χ₂ '' osecP W₂ ε₂ R₂ ⊆ χ₁ '' osecM W₁ ε₁ 1 := by
  rcases h.osecP_side with hP | hM
  swap
  · exact hM
  exfalso
  have hε₁ := h.ε₁_pos; have hε₁' := h.ε₁_lt; have hε₂ := h.ε₂_pos; have hε₂' := h.ε₂_lt
  have hR₂ := h.R₂_pos
  set p₂ := coordPt W₂ (R₂ / 2) (Real.sin ε₂ * (R₂ / 2) / 2)
  set p₁ := coordPt W₁ (1 / 2) (Real.sin ε₁ * (1 / 2) / 2)
  have hp₂ : p₂ ∈ osecP W₂ ε₂ R₂ := mem_osecP_coord hε₂ hε₂' hR₂
  have hp₁ : p₁ ∈ osecP W₁ ε₁ 1 := mem_osecP_coord hε₁ hε₁' one_pos
  have hs := Real.sin_pos_of_pos_of_lt_pi hε₂ (by linarith [Real.pi_pos])
  have hs' := Real.sin_pos_of_pos_of_lt_pi hε₁ (by linarith [Real.pi_pos])
  have hq₂ : 0 < across W₂ p₂ := by rw [across_coordPt]; positivity
  have hq₁ : 0 < across W₁ p₁ := by rw [across_coordPt]; positivity
  have hsub : χ₂ '' secP W₂ ε₂ R₂ ⊆ χ₁ '' secP W₁ ε₁ 1 :=
    image_sector_subset h.cont₁ h.cont₂ hp₂ hP
  exact false_of_nested_reversed h.cont₁ h.inj₁ h.pos₁ h.cont₂ h.inj₂ h.pos₂
    (convex_sector _ _ _) (isClosed_sector _ _ _) (sector_subset_closedBall _ _ _)
    (convex_sector _ _ _) (isClosed_sector _ _ _)
    ((sector_subset_closedBall _ _ _).trans (closedBall_subset_closedBall h.R₂_le))
    (openSector_subset_interior _ _ _ hp₁) (openSector_subset_interior _ _ _ hp₂) hsub
    (ray_mem_frontier_secP hε₂ hε₂' hs₁.le (by linarith))
    (ray_mem_frontier_secP hε₂ hε₂' (by linarith) (by linarith))
    (ray_mem_frontier_secP hε₂ hε₂' (by linarith) hs₃)
    (ray_mem_frontier_secP hε₁ hε₁' (by linarith) hτ₁)
    (ray_mem_frontier_secP hε₁ hε₁' (by linarith) (by linarith))
    (ray_mem_frontier_secP hε₁ hε₁' hτ₃.le (by linarith)) he₁ he₂ he₃
    (ray_sub_ne_of_across_pos hq₂ _) (ray_sub_ne_of_across_pos hq₂ _)
    (ray_sub_ne_of_across_pos hq₂ _) (ray_sub_ne_of_across_pos hq₁ _)
    (ray_sub_ne_of_across_pos hq₁ _) (ray_sub_ne_of_across_pos hq₁ _)
    (circleCyclic_ray W₂ hq₂ hs₁₂ hs₂₃ _ _ _)
    (circleCyclic_ray W₁ hq₁ hτ₃₂ hτ₂₁ _ _ _)

end Charts

end GraphMinor.GM06
