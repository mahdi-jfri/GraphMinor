module

public import GraphMinor.GM06.Alg511CuffRotations
public import GraphMinor.GM06.Section5PolarRimCoordinates
public import GraphMinor.GM11.LocalCone
public import GraphMinor.Surface.Circle
import Mathlib.Tactic

/-!
# Reversing a finite polar rotation

For the orientation step of VI (5.11), page 134, a reflected
rotation lists the old directed ends in reverse order. Mirror the
angular coordinate and extend that mirror linearly along every
ray of the polar disc. Its phase is chosen from the least and
greatest angles in the finite row. This keeps those reflected
angles on the same branch of the argument function, including an
end whose old angle is pi. The disc mirror preserves the centre
and radial scaling, so precomposing a polar chart preserves all
of its geometric properties.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A circle mirror with the given phase. -/
@[expose] noncomputable def alg511AngularMirror (a : ℝ) : Circle ≃ₜ Circle where
  toFun w := Circle.exp a * w⁻¹
  invFun w := Circle.exp a * w⁻¹
  left_inv w := by
    change Circle.exp a * (Circle.exp a * w⁻¹)⁻¹ = w
    rw [mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
  right_inv w := by
    change Circle.exp a * (Circle.exp a * w⁻¹)⁻¹ = w
    rw [mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private noncomputable def complexMirror (a : ℝ) (z : ℂ) : ℂ :=
  (Circle.exp a : ℂ) * (starRingEnd ℂ) z

private theorem complexMirror_norm (a : ℝ) (z : ℂ) : ‖complexMirror a z‖ = ‖z‖ := by
  simp only [complexMirror, norm_mul, Circle.norm_coe, one_mul, Complex.norm_conj]

private theorem complexMirror_twice (a : ℝ) (z : ℂ) :
    complexMirror a (complexMirror a z) = z := by
  simp only [complexMirror, map_mul, Complex.conj_conj]
  rw [← Circle.coe_inv_eq_conj]
  have he : (Circle.exp a : ℂ) * ((Circle.exp a)⁻¹ : Circle) = 1 := by
    rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  calc
    (Circle.exp a : ℂ) * (((Circle.exp a)⁻¹ : Circle) * z) =
        ((Circle.exp a : ℂ) * ((Circle.exp a)⁻¹ : Circle)) * z := (mul_assoc _ _ _).symm
    _ = z := by rw [he, one_mul]

private theorem complexMirror_real_smul (a r : ℝ) (z : ℂ) :
    complexMirror a (r • z) = r • complexMirror a z := by
  simp only [complexMirror, Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

private theorem continuous_complexMirror (a : ℝ) : Continuous (complexMirror a) := by
  unfold complexMirror
  fun_prop

/-- The angular mirror extended across the closed polar disc.
Its inverse is the same mirror. -/
noncomputable def alg511DiscMirror (a : ℝ) : ClosedUnitDisc ≃ₜ ClosedUnitDisc where
  toFun x := ⟨planeOf (complexMirror a (planeOf.symm x.val)), by
    change planeOf (complexMirror a (planeOf.symm x.val)) ∈ Metric.closedBall (0 : EuclideanPlane) 1
    rw [mem_closedBall_zero_iff, planeOf.norm_map, complexMirror_norm, planeOf.symm.norm_map]
    exact mem_closedBall_zero_iff.mp x.property⟩
  invFun x := ⟨planeOf (complexMirror a (planeOf.symm x.val)), by
    change planeOf (complexMirror a (planeOf.symm x.val)) ∈ Metric.closedBall (0 : EuclideanPlane) 1
    rw [mem_closedBall_zero_iff, planeOf.norm_map, complexMirror_norm, planeOf.symm.norm_map]
    exact mem_closedBall_zero_iff.mp x.property⟩
  left_inv x := by
    apply Subtype.ext
    simp only [planeOf.symm_apply_apply, complexMirror_twice, planeOf.apply_symm_apply]
  right_inv x := by
    apply Subtype.ext
    simp only [planeOf.symm_apply_apply, complexMirror_twice, planeOf.apply_symm_apply]
  continuous_toFun := Continuous.subtype_mk
    (planeOf.continuous.comp ((continuous_complexMirror a).comp
      (planeOf.symm.continuous.comp continuous_subtype_val))) _
  continuous_invFun := Continuous.subtype_mk
    (planeOf.continuous.comp ((continuous_complexMirror a).comp
      (planeOf.symm.continuous.comp continuous_subtype_val))) _

/-- The disc mirror fixes the polar centre. -/
theorem alg511DiscMirror_centre (a : ℝ) : alg511DiscMirror a polarCentre = polarCentre := by
  apply Subtype.ext
  simp [alg511DiscMirror, polarCentre, complexMirror]

/-- Mirroring and moving along a polar ray commute. -/
theorem alg511DiscMirror_scale (a : ℝ) (c : I) (x : ClosedUnitDisc) :
    alg511DiscMirror a (discScale c x) = discScale c (alg511DiscMirror a x) := by
  apply Subtype.ext
  change planeOf (complexMirror a (planeOf.symm ((c.val : ℝ) • x.val))) =
    (c.val : ℝ) • planeOf (complexMirror a (planeOf.symm x.val))
  rw [map_smul, complexMirror_real_smul, map_smul]

/-- The disc mirror has the prescribed angular action at every
radius, including zero and the rim. -/
theorem alg511DiscMirror_polarDiscPoint (a : ℝ) (c : I) (w : Circle) :
    alg511DiscMirror a (polarDiscPoint c w) =
      polarDiscPoint c (alg511AngularMirror a w) := by
  apply Subtype.ext
  change planeOf (complexMirror a (planeOf.symm (planeOf ((c : ℂ) * w)))) =
    planeOf ((c : ℂ) * (Circle.exp a * w⁻¹ : Circle))
  rw [planeOf.symm_apply_apply]
  congr 1
  simp only [complexMirror, map_mul, Complex.conj_ofReal, Circle.coe_mul,
    Circle.coe_inv_eq_conj]
  ring

/-- Precomposing a polar chart by the disc mirror preserves its
centre, neighborhood and drawing rays. -/
theorem alg511_isPolar_comp_discMirror
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {v : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ) (a : ℝ) :
    IsPolar Γ v (Φ.comp ⟨alg511DiscMirror a, (alg511DiscMirror a).continuous⟩) := by
  refine ⟨hp.inj.comp (alg511DiscMirror a).injective, ?_, ?_, ?_⟩
  · change Φ (alg511DiscMirror a polarCentre) = v
    rw [alg511DiscMirror_centre, hp.centre]
  · have hr : range (fun x => Φ (alg511DiscMirror a x)) = range Φ := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact mem_range_self _
      · rintro ⟨x, rfl⟩
        obtain ⟨u, rfl⟩ := (alg511DiscMirror a).surjective x
        exact mem_range_self _
    change v ∈ interior (range (fun x => Φ (alg511DiscMirror a x)))
    rw [hr]
    exact hp.nhd
  · intro x hx c hc
    have hmx : alg511DiscMirror a x ≠ polarCentre := by
      intro heq
      apply hx
      apply (alg511DiscMirror a).injective
      rw [heq, alg511DiscMirror_centre]
    obtain ⟨s, hs, hx', hc'⟩ := hp.ray (alg511DiscMirror a x) hmx c hc
    refine ⟨s, hs, hx', ?_⟩
    change Φ (alg511DiscMirror a (discScale c x)) ∈ s
    rw [alg511DiscMirror_scale]
    exact hc'

/-- A phase can be chosen so that the mirror of every angle in a
finite row is represented by subtraction on the usual argument
branch. The choice depends only on the finite row's extremes. -/
theorem alg511_exists_row_mirror_phase (xs : List ℕ) (z : ℕ → Circle) :
    ∃ a : ℝ, ∀ r ∈ xs,
      circleStdCoord.angle (alg511AngularMirror a (z r)) = a - circleStdCoord.angle (z r) := by
  classical
  cases xs with
  | nil => exact ⟨0, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons i xs =>
    let s : Finset ℝ := ((i :: xs).map (fun r => circleStdCoord.angle (z r))).toFinset
    have hs : s.Nonempty := ⟨circleStdCoord.angle (z i), by simp [s]⟩
    let lo := s.min' hs
    let hi := s.max' hs
    have hlo : -Real.pi < lo := by
      have hm := s.min'_mem hs
      obtain ⟨r, _, hr⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
      change -Real.pi < s.min' hs
      rw [← hr]
      exact Complex.neg_pi_lt_arg _
    have hhi : hi ≤ Real.pi := by
      have hm := s.max'_mem hs
      obtain ⟨r, _, hr⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
      change s.max' hs ≤ Real.pi
      rw [← hr]
      exact Complex.arg_le_pi _
    refine ⟨lo + hi, ?_⟩
    intro r hr
    have hm : circleStdCoord.angle (z r) ∈ s := List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩)
    have hlow : lo ≤ circleStdCoord.angle (z r) := s.min'_le _ hm
    have hhigh : circleStdCoord.angle (z r) ≤ hi := s.le_max' _ hm
    have heq : alg511AngularMirror (lo + hi) (z r) =
        Circle.exp (lo + hi - circleStdCoord.angle (z r)) := by
      change Circle.exp (lo + hi) * (z r)⁻¹ = _
      rw [Circle.exp_sub, div_eq_mul_inv]
      congr 1
      exact congrArg Inv.inv (Circle.exp_arg (z r)).symm
    rw [heq]
    exact Circle.arg_exp (by linarith) (by linarith)

/-- Mirrored angles in the reversed row are increasing. This
handles the argument cut by the phase supplied above. -/
theorem alg511_pairwise_reverse_angles (xs : List ℕ) (z : ℕ → Circle) (a : ℝ)
    (ha : ∀ r ∈ xs, circleStdCoord.angle (alg511AngularMirror a (z r)) =
      a - circleStdCoord.angle (z r))
    (hs : xs.Pairwise (fun r s => circleStdCoord.angle (z r) < circleStdCoord.angle (z s))) :
    xs.reverse.Pairwise (fun r s =>
      circleStdCoord.angle (alg511AngularMirror a (z r)) <
        circleStdCoord.angle (alg511AngularMirror a (z s))) := by
  apply List.pairwise_reverse.mpr
  apply List.Pairwise.imp_of_mem (p := hs)
  intro r s hr hs hrs
  rw [ha r hr, ha s hs]
  exact sub_lt_sub_left hrs a


/-- Reversing a rotation row is realized by an actual mirrored
polar chart. The directed ends themselves keep their labels. -/
theorem Alg511CuffRotationRowRep.reverse
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {m : ℕ}
    {edge : Fin m ≃ Γ.E} {γ : Set S → I → S} {v : S} {xs : List ℕ}
    (hrow : Alg511CuffRotationRowRep edge γ v xs) :
    Alg511CuffRotationRowRep edge γ v xs.reverse := by
  obtain ⟨hnd, hmem, horder⟩ := hrow
  refine ⟨List.nodup_reverse.mpr hnd, fun r => (List.mem_reverse).trans (hmem r), ?_⟩
  rcases horder with hshort | ⟨Φ, z, hp, hzi, hs, hspoke, hrim⟩
  · exact Or.inl (by simpa only [List.length_reverse] using hshort)
  · obtain ⟨a, ha⟩ := alg511_exists_row_mirror_phase xs z
    let M := alg511AngularMirror a
    have hMM (w : Circle) : M (M w) = w := (alg511AngularMirror a).left_inv w
    let Ψ : C(ClosedUnitDisc, S) := Φ.comp ⟨alg511DiscMirror a, (alg511DiscMirror a).continuous⟩
    refine Or.inr ⟨Ψ, fun r => M (z r), alg511_isPolar_comp_discMirror hp a, ?_,
      alg511_pairwise_reverse_angles xs z a ha hs, ?_, ?_⟩
    · intro r hr s hs heq
      exact hzi (List.mem_reverse.mp hr) (List.mem_reverse.mp hs) (M.injective heq)
    · intro e t ht
      change Φ (alg511DiscMirror a (polarDiscPoint t (M (z (halfEdgeLabel edge e))))) ∈ _
      rw [alg511DiscMirror_polarDiscPoint]
      change Φ (polarDiscPoint t (M (M (z (halfEdgeLabel edge e)))) ) ∈ _
      rw [hMM]
      exact hspoke e t ht
    · intro j w
      have heq : polarRimMap Ψ w = polarRimMap Φ (M w) := by
        change Φ (alg511DiscMirror a (polarDiscPoint 1 w)) = Φ (polarDiscPoint 1 (M w))
        rw [alg511DiscMirror_polarDiscPoint]
      rw [heq, hrim]
      constructor
      · rintro ⟨r, hr, hz, hend⟩
        refine ⟨r, List.mem_reverse.mpr hr, ?_, hend⟩
        change M (z r) = w
        rw [hz, hMM]
      · rintro ⟨r, hr, hz, hend⟩
        refine ⟨r, List.mem_reverse.mp hr, ?_, hend⟩
        have hh := congrArg M hz
        change M (M (z r)) = M w at hh
        rw [hMM] at hh
        exact hh

end GraphMinor.GM06
