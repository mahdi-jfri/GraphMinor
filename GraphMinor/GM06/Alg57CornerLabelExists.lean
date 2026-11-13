module

public import GraphMinor.GM06.Alg57VertexStar

/-!
# Lemma 3 for the counterclockwise rotation

This file proves Lemma 3 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) for the actual
counterclockwise rotation of a drawing in the sphere (`sphere_faceOrbits_ccw`).
`IsCornerLabel.sphere_faceOrbits` proves Lemma 3 for a rotation with a corner label: a region
for each dart, in the corner after the dart, such that both ends of an edge see the same region
on the same side. Here we build that corner label (`exists_cornerLabel`).

At each vertex we read the rotation in a positive polar chart (`IsCcwStar`), and the label of a dart
is the region of the corner after its ray (`cornerRegion`). The incidence conditions come from the
picture in one chart (`region_eq_corner_of_ray`, `exists_corner_of_closure_centre`). The two ends of
an edge agree by Step 1 of the proof of Lemma 3, the half-band on the left of the edge
(`cornerRegion_start_eq_end`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval Equiv

variable {Γ : Drawing (OnePoint EuclideanPlane)}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart Γ)}

/-- A curve that runs out along a ray from time `0`, read backwards from time `1`, runs in along
the ray up to time `1`. -/
theorem RunsOut.runsIn_one {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {W : Circle}
    {G : ℝ → OnePoint EuclideanPlane} {δ : ℝ} (h : RunsOut Ψ W (fun s => G (1 - s)) 0 δ) :
    RunsIn Ψ W G 1 δ := by
  obtain ⟨hδ, ρ, hρc, hρ0, hmono, hρG⟩ := h
  have hmaps : MapsTo (fun s : ℝ => 1 - s) (Icc (1 - δ) 1) (Icc 0 (0 + δ)) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨hδ, fun s => ρ (1 - s), hρc.comp (continuousOn_const.sub continuousOn_id) hmaps,
    by simpa using hρ0, ?_, ?_⟩
  · intro s hs s' hs' hss'
    exact hmono (hmaps hs') (hmaps hs) (by linarith)
  · intro s hs
    have := hρG (1 - s) (hmaps hs)
    simp only [sub_sub_cancel] at this
    exact this

/-- The rotation `R` is the counterclockwise rotation of the drawing: at each vertex with a dart
there is a positive polar chart in which `R` turns counterclockwise. -/
def IsCcwRotation (Γ : Drawing (OnePoint EuclideanPlane))
    (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane)
    (R : DartRotation (DrawingDart Γ)) : Prop :=
  ∀ v, (∃ a : DrawingDart Γ, dartVertex γ a = v) →
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (z : DrawingDart Γ → Circle),
      IsCcwStar Γ γ R v Φ z

namespace IsCcwStar

variable {v : OnePoint EuclideanPlane} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
  {z : DrawingDart Γ → Circle}

/-- The ray of a dart lies in its edge. -/
theorem ray_mem_edge (h : IsCcwStar Γ γ R v Φ z) (hγ : EdgePar Γ γ)
    {Ψ : C(ClosedUnitDisc, EuclideanPlane)} (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    {a : DrawingDart Γ} (ha : dartVertex γ a = v) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    toSph (chartC Ψ ((t : ℂ) * z a)) ∈ a.1.1 := by
  obtain ⟨s, hs⟩ := h.spoke a ha ⟨t, ht.le, ht1⟩ ht
  rw [toSph_chartC hΨ]
  have := discPt_mul ⟨t, ht.le, ht1⟩ (z a)
  simp only at this
  rw [this, ← hs]
  rcases eq_or_lt_of_le s.2.1 with h0 | h0
  · exfalso
    have hs0 : s = 0 := Subtype.ext h0.symm
    rw [hs0, spoke_zero] at hs
    have : Φ (polarDiscPoint ⟨t, ht.le, ht1⟩ (z a)) = Φ polarCentre := by
      rw [← hs, h.polar.centre]; exact ha
    have h2 := congrArg (fun x : ClosedUnitDisc => ‖x.1‖) (h.polar.inj this)
    simp only [norm_polarDiscPoint] at h2
    have : t = 0 := by simpa [polarCentre] using h2
    linarith
  · exact spoke_mem_edge hγ a.2 h0

end IsCcwStar

/-- **The corner label of the counterclockwise rotation.** -/
theorem exists_cornerLabel (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U)
    (hγ : EdgePar Γ γ) (hR : IsDrawingRotation Γ γ R) (hccw : IsCcwRotation Γ γ R) :
    ∃ ρ, IsCornerLabel Γ γ R ρ ∧ ∀ d, ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (z : DrawingDart Γ → Circle), IsCcwStar Γ γ R (dartVertex γ d) Φ z ∧
        ρ d = cornerRegion Γ Φ (z d) := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  choose! Φ z hst using hccw
  have hst' : ∀ a : DrawingDart Γ, IsCcwStar Γ γ R (dartVertex γ a) (Φ (dartVertex γ a))
      (z (dartVertex γ a)) := fun a => hst _ ⟨a, rfl⟩
  have hΨex : ∀ a : DrawingDart Γ, ∃ Ψ : C(ClosedUnitDisc, EuclideanPlane),
      (∀ x, Φ (dartVertex γ a) x = (Ψ x : OnePoint EuclideanPlane)) ∧
      0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) := by
    intro a
    obtain ⟨Ψ, hΨ, hw⟩ := (hst' a).pos
    exact ⟨Ψ, hΨ, by rw [wind_chartC]; exact hw⟩
  choose Ψ hΨ hpos using hΨex
  let ρ : DrawingDart Γ → Set (OnePoint EuclideanPlane) := fun a =>
    cornerRegion Γ (Φ (dartVertex γ a)) (z (dartVertex γ a) a)
  have hD : ∀ a : DrawingDart Γ, (rimDirs Γ (Φ (dartVertex γ a))).Finite := fun a =>
    (hst' a).rimDirs_finite hγ
  have hvrot : ∀ a, dartVertex γ (R.rot.symm a) = dartVertex γ a := fun a => by
    rw [← hR.vertex_rot (R.rot.symm a), Equiv.apply_symm_apply]
  have hρrot : ∀ a, ρ (R.rot.symm a) =
      cornerRegion Γ (Φ (dartVertex γ a)) (z (dartVertex γ a) (R.rot.symm a)) := fun a => by
    simp only [ρ, hvrot a]
  -- a point of the ray of a dart, in its edge and in the closure of its corner
  have hmid : ∀ a : DrawingDart Γ,
      toSph (chartC (Ψ a) (((1 / 2 : ℝ) : ℂ) * z (dartVertex γ a) a)) ∈ a.1.1 ∧
      toSph (chartC (Ψ a) (((1 / 2 : ℝ) : ℂ) * z (dartVertex γ a) a)) ∈ closure (ρ a) :=
    fun a => ⟨(hst' a).ray_mem_edge hγ (hΨ a) rfl (by norm_num) (by norm_num),
      ray_mem_closure_cornerRegion (hst' a).polar (hΨ a) (hD a) _ (by norm_num) (by norm_num)⟩
  refine ⟨ρ, ⟨fun a => cornerRegion_mem (hst' a).polar (hΨ a) (hD a) _,
    fun a => centre_mem_closure_cornerRegion (hst' a).polar (hΨ a) (hD a) _, ?_, ?_, ?_, ?_⟩,
    fun d => ⟨_, _, hst' d, rfl⟩⟩
  · -- the corners at a vertex are all regions there
    intro r hr d hd
    obtain ⟨w, hw, hrw⟩ := exists_corner_of_closure_centre (hst' d).polar (hΨ d) (hD d)
      (Γ.V_subset_U (dartVertex_mem hγ d)) ⟨_, (hst' d).mem_rimDirs hγ rfl⟩ hr hd
    rw [(hst' d).rimDirs_eq hγ] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    have ha' : dartVertex γ a = dartVertex γ d := ha
    refine ⟨a, ha', ?_⟩
    show r = cornerRegion Γ (Φ (dartVertex γ a)) (z (dartVertex γ a) a)
    rw [ha']
    exact hrw
  · -- the edge of a dart is in the closure of its corner
    intro d
    exact edge_subset_closure_of_incident hS d.2 (cornerRegion_mem (hst' d).polar (hΨ d) (hD d) _)
      ⟨_, (hmid d).1, (hmid d).2⟩
  · -- the regions along the edge of a dart are the corners next to it
    intro d r hr hdr
    rw [hρrot d]
    rcases region_eq_corner_of_ray (hst' d).polar (hΨ d) (hD d) ((hst' d).mem_rimDirs hγ rfl)
      ((hst' d).prev_eq hγ hR rfl) (by norm_num) (by norm_num) hr (hdr (hmid d).1) with h | h
    · exact Or.inr h
    · exact Or.inl h
  · -- both ends of an edge see the same region on the left
    intro d
    set a' := dartFlip Γ d
    have hrev : R.rev d = a' := hR.rev_eq d
    rw [DartRotation.face_apply, hrev, hρrot a']
    have hG := isEdgeCurve_dartCurve hγ d
    have hG0 : dartCurve γ d 0 = dartVertex γ d := dartCurve_zero γ d
    have hG1 : dartCurve γ d 1 = dartVertex γ a' := by
      rw [← dartCurve_zero γ a', dartCurve_flip, sub_zero]
    obtain ⟨δu, hrunu⟩ := (hst' d).runsOut hγ (hΨ d) rfl
    obtain ⟨δv, hrunv⟩ := (hst' a').runsOut hγ (hΨ a') rfl
    have hrunv' : RunsIn (Ψ a') (z (dartVertex γ a') a') (dartCurve γ d) 1 δv := by
      apply RunsOut.runsIn_one
      have : (fun s => dartCurve γ d (1 - s)) = dartCurve γ a' := by
        funext s; rw [dartCurve_flip]
      rw [this]
      exact hrunv
    have hpu : IsPolar Γ (dartCurve γ d 0) (Φ (dartVertex γ d)) := hG0 ▸ (hst' d).polar
    have hpv : IsPolar Γ (dartCurve γ d 1) (Φ (dartVertex γ a')) := hG1 ▸ (hst' a').polar
    exact (cornerRegion_start_eq_end hS hinf d.2 hG hpu (hΨ d) (hpos d) (hD d)
      ((hst' d).mem_rimDirs hγ rfl) hrunu hpv (hΨ a') (hpos a') (hD a')
      ((hst' a').mem_rimDirs hγ rfl) ((hst' a').prev_eq hγ hR rfl) hrunv').symm

/-- **Lemma 3 of the proof of VI (5.7), for the counterclockwise rotation.** Let `Γ` be a
drawing in the sphere that misses the point at infinity and has an edge, and let `R` be its
counterclockwise rotation, connected on the darts. Then the orbits of `φ = σ⁻¹ τ` correspond one
to one with the regions, and the incidence rules (3) and (4) hold. -/
theorem sphere_faceOrbits_ccw (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U)
    (hγ : EdgePar Γ γ) (hR : IsDrawingRotation Γ γ R) (hccw : IsCcwRotation Γ γ R)
    (hc : R.Connected) (hV : ∀ v ∈ Γ.V, ∃ d : DrawingDart Γ, dartVertex γ d = v)
    (hne : Γ.E.Nonempty) :
    ∃ L : R.Faces → Γ.R, Function.Bijective L ∧
      (∀ (O : R.Faces) (d : DrawingDart Γ),
        d.1.1 ⊆ closure (L O).1 ↔ R.faceOf d = O ∨ R.faceOf (R.rev d) = O) ∧
      (∀ (O : R.Faces), ∀ v ∈ Γ.V,
        v ∈ closure (L O).1 ↔ ∃ d : DrawingDart Γ, dartVertex γ d = v ∧ R.faceOf d = O) := by
  obtain ⟨ρ, hρ, -⟩ := exists_cornerLabel hinf hγ hR hccw
  exact ⟨hρ.label, hρ.sphere_faceOrbits hinf hγ hR hc hV hne⟩

end GraphMinor.GM06
