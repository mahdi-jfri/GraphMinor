module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.Surface.DiscTwist

/-!
# Angular projection in a punctured polar disc

For the corner argument in VI (5.5), page 130, project points of
a punctured polar neighbourhood onto its rim. Invert the embedded
disc chart and normalize its nonzero plane coordinate. The resulting
map is continuous away from the attachment, fixes angular directions,
and expresses every point at a positive radial scale.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- Angular projection of an embedded polar disc is continuous off
its centre and records the radial representation of every point. -/
theorem exists_polar_angular_projection
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {s : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ) :
    ∃ q : S → Circle, ContinuousOn q (range Φ \ {s}) ∧
      (∀ (c : I), 0 < c → ∀ w : Circle, q (Φ (polarDiscPoint c w)) = w) ∧
      ∀ y ∈ range Φ \ {s}, ∃ c : I, 0 < c ∧ Φ (polarDiscPoint c (q y)) = y := by
  classical
  have hemb := (Φ.continuous.isClosedEmbedding hp.inj).isEmbedding
  let e : ClosedUnitDisc ≃ₜ range Φ := hemb.toHomeomorph
  let j : S → ClosedUnitDisc := fun y =>
    if hy : y ∈ range Φ then e.symm ⟨y, hy⟩ else polarCentre
  have hj (x : ClosedUnitDisc) : j (Φ x) = x := by
    change (if hy : Φ x ∈ range Φ then e.symm ⟨Φ x, hy⟩ else polarCentre) = x
    rw [dite_eq_left (mem_range_self x)]
    exact e.symm_apply_apply x
  have hjc : ContinuousOn j (range Φ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (range Φ).domRestrict j = e.symm := by
      funext y
      simp only [domRestrict, j, dite_eq_left y.2]
    rw [heq]
    exact e.symm.continuous
  let g : S → ℂ := fun y => planeOf.symm (j y).1
  have hgc : ContinuousOn g (range Φ) :=
    planeOf.symm.continuous.comp_continuousOn (continuous_subtype_val.comp_continuousOn hjc)
  have hg (x : ClosedUnitDisc) : g (Φ x) = planeOf.symm x.1 := by
    change planeOf.symm (j (Φ x)).1 = _
    rw [hj]
  have hg0 (y) (hy : y ∈ range Φ \ {s}) : g y ≠ 0 := by
    obtain ⟨x, rfl⟩ := hy.1
    intro he
    have hx : x = polarCentre := by
      apply Subtype.ext
      apply planeOf.symm.injective
      simpa only [polarCentre, map_zero] using (hg x).symm.trans he
    exact hy.2 (by rw [hx, hp.centre]; rfl)
  let q : S → Circle := fun y => if he : g y ≠ 0 then unitOf (g y) he else 1
  have hqc : ContinuousOn q (range Φ \ {s}) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let f : (range Φ \ {s} : Set S) → {z : ℂ // z ≠ 0} :=
      fun y => ⟨g y.1, hg0 y.1 y.2⟩
    have hfc : Continuous f :=
      (continuousOn_iff_continuous_domRestrict.mp (hgc.mono sdiff_subset)).subtype_mk _
    have heq : (range Φ \ {s}).domRestrict q =
        (fun z : {z : ℂ // z ≠ 0} => unitOf z.1 z.2) ∘ f := by
      funext y
      simp only [domRestrict, q, dite_eq_left (hg0 y.1 y.2), Function.comp_apply, f]
    rw [heq]
    exact continuous_unitOf.comp hfc
  have hqg (y) (hy : g y ≠ 0) : q y = unitOf (g y) hy := by simp only [q, dite_eq_left hy]
  have hgr (c : I) (w : Circle) : g (Φ (polarDiscPoint c w)) = (c : ℂ) * w := by
    rw [hg]
    exact planeOf.symm_apply_apply _
  refine ⟨q, hqc, ?_, ?_⟩
  · intro c hc w
    have hne : (c : ℂ) * w ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hc)) (Circle.coe_ne_zero w)
    have hgne : g (Φ (polarDiscPoint c w)) ≠ 0 := by rwa [hgr]
    rw [hqg _ hgne]
    apply Circle.ext
    simp only [coe_unitOf, hgr]
    exact congrArg (fun z : Circle => (z : ℂ)) (unitOf_mul (c : ℝ) hc w hne)
  · intro y hy
    let c : I := ⟨‖g y‖, norm_nonneg _, by
      change ‖planeOf.symm (j y).1‖ ≤ 1
      rw [LinearIsometryEquiv.norm_map]
      exact mem_closedBall_zero_iff.mp (j y).2⟩
    have hc : 0 < c := norm_pos_iff.mpr (hg0 y hy)
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, rfl⟩ := hy.1
    apply congrArg Φ
    apply Subtype.ext
    change planeOf ((c : ℂ) * q (Φ x)) = x.1
    rw [hqg _ (hg0 _ hy)]
    change planeOf ((‖g (Φ x)‖ : ℂ) * unitOf (g (Φ x)) _) = x.1
    rw [norm_mul_unitOf, hg, planeOf.apply_symm_apply]

end GraphMinor.GM06
