module

public import GraphMinor.GM06.Alg57InputRep
public import GraphMinor.GM06.Alg511PolarReflection
import GraphMinor.Surface.PlaneOrientation
import GraphMinor.GM19.Winding
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic

/-!
# Positive polar charts under the orientation step

VI (5.11), page 134, reflects the drawing and reverses each
rotation row. Use a rotated complex conjugation in the plane and
a mirror of the parameter disc. Each of these negates boundary
winding, so their composition keeps the positive polar orientation.
The calculation uses only multiplication by a fixed nonzero number,
complex conjugation and reparametrization of one circle. A rotation
of the circle parameter preserves its winding by an explicit
homotopy. No general classification of surface orientations is used.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM19 unitInterval

/-- Rotated complex conjugation as an actual plane homeomorphism. -/
@[expose] noncomputable def alg511PlaneReflection (phase : ℝ) : EuclideanPlane ≃ₜ EuclideanPlane :=
  (complexPlane.toHomeomorph.symm.trans
    (Complex.conjLIE.toHomeomorph.trans
      (Homeomorph.mulLeft₀ (Circle.exp phase : ℂ) (Circle.coe_ne_zero _)))).trans
    complexPlane.toHomeomorph

/-- Complex coordinates of the concrete plane reflection. -/
theorem alg511PlaneReflection_complex (phase : ℝ) (z : EuclideanPlane) :
    complexPlane.symm (alg511PlaneReflection phase z) =
      (Circle.exp phase : ℂ) * (starRingEnd ℂ) (complexPlane.symm z) := by
  change complexPlane.symm (complexPlane _) = _
  rw [complexPlane.symm_apply_apply]
  rfl

private theorem wind_mul_const (c : ℂ) (hc : c ≠ 0) {φ : Circle → ℂ}
    (hφ : Continuous φ) {z : ℂ} (hne : ∀ w, φ w ≠ z) :
    wind (fun w => c * φ w) (c * z) = wind φ z := by
  let g : ℝ → ℂ := fun t => φ (Circle.exp t) - z
  have hg : Continuous g := (hφ.comp Circle.exp.continuous).sub continuous_const
  have hg0 : ∀ t, g t ≠ 0 := fun t => sub_ne_zero.mpr (hne _)
  obtain ⟨L, hL⟩ := exists_isAngle hg hg0
  obtain ⟨a, ha⟩ := isAngle_const hc
  have hm : IsAngle (fun t => c * g t) (fun t => a + L t) := ha.mul hL
  have hm0 : ∀ t, c * g t ≠ 0 := fun t => mul_ne_zero hc (hg0 t)
  have he : (fun t => c * φ (Circle.exp t) - c * z) = fun t => c * g t := by
    funext t
    exact (mul_sub c _ _).symm
  change turn (fun t => c * φ (Circle.exp t) - c * z) 0 (2 * Real.pi) = turn g 0 (2 * Real.pi)
  rw [he, hm.turn_eq hm0, hL.turn_eq hg0]
  ring

/-- Rotating the parameter of a circle leaves its winding about
any avoided point unchanged. The proof rotates continuously. -/
theorem alg511_wind_rotate (phase : ℝ) {φ : Circle → ℂ}
    (hφ : Continuous φ) {z : ℂ} (hne : ∀ w, φ w ≠ z) :
    wind (fun w => φ (Circle.exp phase * w)) z = wind φ z := by
  let H : ℝ → ℝ → ℂ := fun u t => φ (Circle.exp (u * phase) * Circle.exp t) - z
  have hH : Continuous (fun q : ℝ × ℝ => H q.1 q.2) := by
    unfold H
    fun_prop
  have hH0 : ∀ u t, H u t ≠ 0 := fun u t => sub_ne_zero.mpr (hne _)
  have hper : ∀ u, Function.Periodic (H u) (2 * Real.pi) := fun u t => by
    simp only [H, Circle.exp_add_two_pi]
  have hv : ∀ t, ∃ t' ∈ Icc 0 (2 * Real.pi), ∀ u, H u t = H u t' := by
    intro t
    obtain ⟨t', ht', n, rfl⟩ := exists_mem_period t
    exact ⟨_, ht', fun u => ((hper u).sub_zsmul_eq n).symm⟩
  have hh := turn_eq_of_homotopy hH hH0 isCompact_Icc hv
    (s := 0) (t := 2 * Real.pi) (fun u => by
      have h := hper u 0
      rw [zero_add] at h
      exact h.symm) 0 1
  have h0 : H 0 = fun t => φ (Circle.exp t) - z := by
    funext t
    simp only [H, zero_mul, Circle.exp_zero, one_mul]
  have h1 : H 1 = fun t => φ (Circle.exp phase * Circle.exp t) - z := by
    funext t
    simp only [H, one_mul]
  rw [h0, h1] at hh
  exact hh.symm

/-- A circle mirror negates winding, including a nonzero phase
chosen to keep a finite row away from the argument cut. -/
theorem alg511_wind_angularMirror (phase : ℝ) {φ : Circle → ℂ}
    (hφ : Continuous φ) {z : ℂ} (hne : ∀ w, φ w ≠ z) :
    wind (fun w => φ (alg511AngularMirror phase w)) z = -wind φ z := by
  let ψ : Circle → ℂ := fun w => φ (Circle.exp phase * w)
  have hψ : Continuous ψ := hφ.comp (continuous_const.mul continuous_id)
  have hψ0 : ∀ w, ψ w ≠ z := fun w => hne _
  change wind (fun w => ψ w⁻¹) z = _
  rw [wind_inv hψ hψ0]
  rw [alg511_wind_rotate phase hφ hne]

/-- The concrete plane reflection negates the winding of any
avoiding circle curve in complex coordinates. -/
theorem alg511_wind_planeReflection (phase : ℝ) {φ : Circle → EuclideanPlane}
    (hφ : Continuous φ) {z : EuclideanPlane} (hne : ∀ w, φ w ≠ z) :
    wind (fun w => complexPlane.symm (alg511PlaneReflection phase (φ w)))
      (complexPlane.symm (alg511PlaneReflection phase z)) =
      -wind (fun w => complexPlane.symm (φ w)) (complexPlane.symm z) := by
  simp only [alg511PlaneReflection_complex]
  have hz : ∀ w, complexPlane.symm (φ w) ≠ complexPlane.symm z :=
    fun w => fun h => hne w (complexPlane.symm.injective h)
  have hconj : ∀ w, (starRingEnd ℂ) (complexPlane.symm (φ w)) ≠
      (starRingEnd ℂ) (complexPlane.symm z) :=
    fun w h => hz w (Complex.conjLIE.injective h)
  rw [wind_mul_const _ (Circle.coe_ne_zero _) (by fun_prop) hconj]
  exact wind_conj (φ := fun w => complexPlane.symm (φ w))
    (complexPlane.symm.continuous.comp hφ) hz

/-- Reflecting the plane and mirroring the polar parameter disc
keeps a positively oriented polar chart positive. This is the
orientation calculation needed by the reflected rotation rows. -/
theorem alg511_positivePolar_reflection
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hpos : GM06PositivePolar Φ)
    (hinj : Function.Injective Φ) (phase mirrorPhase : ℝ) :
    GM06PositivePolar
      ((⟨(alg511PlaneReflection phase).onePointCongr,
        (alg511PlaneReflection phase).onePointCongr.continuous⟩ :
          C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)).comp
        (Φ.comp ⟨alg511DiscMirror mirrorPhase, (alg511DiscMirror mirrorPhase).continuous⟩)) := by
  obtain ⟨Ψ, hΨ, hwind⟩ := hpos
  let Ψ' : C(ClosedUnitDisc, EuclideanPlane) :=
    ⟨fun t => alg511PlaneReflection phase (Ψ (alg511DiscMirror mirrorPhase t)), by fun_prop⟩
  refine ⟨Ψ', ?_, ?_⟩
  · intro t
    change (alg511PlaneReflection phase).onePointCongr (Φ (alg511DiscMirror mirrorPhase t)) =
      (alg511PlaneReflection phase (Ψ (alg511DiscMirror mirrorPhase t)) : OnePoint EuclideanPlane)
    rw [hΨ]
    exact OnePoint.map_some _ _
  · let φ : Circle → EuclideanPlane := fun w => Ψ (polarDiscPoint 1 w)
    have hφ : Continuous φ := Ψ.continuous.comp (polarRimMap (ContinuousMap.id ClosedUnitDisc)).continuous
    have hne : ∀ w, φ w ≠ Ψ polarCentre := by
      intro w heq
      have heq' : Φ (polarDiscPoint 1 w) = Φ polarCentre := by
        rw [hΨ, hΨ]
        exact congrArg (fun p : EuclideanPlane => (p : OnePoint EuclideanPlane)) heq
      exact polarDiscPoint_one_ne_centre w (hinj heq')
    have hcentre : Ψ' polarCentre = alg511PlaneReflection phase (Ψ polarCentre) := by
      change alg511PlaneReflection phase (Ψ (alg511DiscMirror mirrorPhase polarCentre)) = _
      rw [alg511DiscMirror_centre]
    have hrim : (fun w => Ψ' (polarDiscPoint 1 w)) =
        fun w => alg511PlaneReflection phase (φ (alg511AngularMirror mirrorPhase w)) := by
      funext w
      change alg511PlaneReflection phase (Ψ (alg511DiscMirror mirrorPhase (polarDiscPoint 1 w))) = _
      rw [alg511DiscMirror_polarDiscPoint]
    have hc : Continuous (fun w => φ (alg511AngularMirror mirrorPhase w)) :=
      hφ.comp (alg511AngularMirror mirrorPhase).continuous
    have hn : ∀ w, φ (alg511AngularMirror mirrorPhase w) ≠ Ψ polarCentre := fun w => hne _
    have heq : (fun w => complexPlane.symm (Ψ' (polarDiscPoint 1 w))) =
        fun w => complexPlane.symm (alg511PlaneReflection phase (φ (alg511AngularMirror mirrorPhase w))) := by
      funext w
      exact congrArg complexPlane.symm (congrFun hrim w)
    have hz : ∀ w, complexPlane.symm (φ w) ≠ complexPlane.symm (Ψ polarCentre) :=
      fun w h => hne w (complexPlane.symm.injective h)
    have hplane := alg511_wind_planeReflection phase
      (φ := fun w => φ (alg511AngularMirror mirrorPhase w)) (z := Ψ polarCentre) hc hn
    have hmirror := alg511_wind_angularMirror mirrorPhase
      (φ := fun w => complexPlane.symm (φ w)) (z := complexPlane.symm (Ψ polarCentre))
      (complexPlane.symm.continuous.comp hφ) hz
    have hnew : wind (fun w => complexPlane.symm (Ψ' (polarDiscPoint 1 w)))
        (complexPlane.symm (Ψ' polarCentre)) =
        wind (fun w => complexPlane.symm (φ w)) (complexPlane.symm (Ψ polarCentre)) := by
      rw [heq, hcentre]
      exact hplane.trans ((congrArg Neg.neg hmirror).trans (neg_neg _))
    exact hnew.symm ▸ hwind

end GraphMinor.GM06
