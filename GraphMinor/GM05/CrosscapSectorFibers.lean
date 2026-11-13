module

public import GraphMinor.GM05.CrosscapPolarBase
import GraphMinor.GM05.CrosscapFibers

/-!
# Fibers of the two small crosscap sectors

For the local reversing disc in GM V, (8.10), quotient equality within
one sector determines its polar offset. The two opposite sectors have
no common base point. Their quotient images can meet only on the
unit boundary circle, corresponding to the common source diameter.
-/

public section

namespace GraphMinor.GM05

open Set Topology Metric Surface

/-- Within either sector the quotient determines the polar offset. -/
theorem crosscap_sector_offset_eq {a b c k : ℕ} (σ : Bool)
    (z w : ↥(closedBall (0 : ℂ) 1))
    (he : Quot.mk (ModelGlue a b (2*a+b+c)) (crosscapPolarBase (2*a+k) (2*a+b+c) σ z)=
      Quot.mk _ (crosscapPolarBase (2*a+k) (2*a+b+c) σ w)) :
    crosscapPolarOffset z.1=crosscapPolarOffset w.1 := by
  have hz := mem_closedBall_zero_iff.mp z.2
  have hw := mem_closedBall_zero_iff.mp w.2
  have hbound := crosscapPolarOffset_bounds hz
  cases σ
  · have hp : (crosscapPolarBase (2*a+k) (2*a+b+c) false z).1=
        (↑(modelCentre (2*a+k)+ -crosscapPolarOffset z.1) : OnePoint EuclideanPlane) := by
      rw [crosscapPolarBase_val]
      rfl
    have hnear : ‖-crosscapPolarOffset z.1‖<2 := by rw [norm_neg]; linarith only [hbound.2]
    rcases model_quot_eq_near_crosscap hp hnear he with heq|⟨hn,hq⟩
    · have hh := congrArg Subtype.val heq
      rw [crosscapPolarBase_val,crosscapPolarBase_val] at hh
      change (↑(modelCentre (2*a+k)+ -crosscapPolarOffset z.1) : OnePoint EuclideanPlane)=
        ↑(modelCentre (2*a+k)+ -crosscapPolarOffset w.1) at hh
      exact neg_injective (add_left_cancel (OnePoint.coe_injective hh))
    · rw [crosscapPolarBase_val] at hq
      change (↑(modelCentre (2*a+k)+ -crosscapPolarOffset w.1) : OnePoint EuclideanPlane)=
        ↑(modelCentre (2*a+k)- -crosscapPolarOffset z.1) at hq
      rw [sub_neg_eq_add] at hq
      have hh := add_left_cancel (OnePoint.coe_injective hq)
      exact (crosscapPolarOffset_ne_neg hz hw hh.symm).elim
  · have hp : (crosscapPolarBase (2*a+k) (2*a+b+c) true z).1=
        (↑(modelCentre (2*a+k)+crosscapPolarOffset z.1) : OnePoint EuclideanPlane) := by
      rw [crosscapPolarBase_val]
      rfl
    have hnear : ‖crosscapPolarOffset z.1‖<2 := by linarith only [hbound.2]
    rcases model_quot_eq_near_crosscap hp hnear he with heq|⟨hn,hq⟩
    · have hh := congrArg Subtype.val heq
      rw [crosscapPolarBase_val,crosscapPolarBase_val] at hh
      change (↑(modelCentre (2*a+k)+crosscapPolarOffset z.1) : OnePoint EuclideanPlane)=
        ↑(modelCentre (2*a+k)+crosscapPolarOffset w.1) at hh
      exact add_left_cancel (OnePoint.coe_injective hh)
    · rw [crosscapPolarBase_val] at hq
      change (↑(modelCentre (2*a+k)+crosscapPolarOffset w.1) : OnePoint EuclideanPlane)=
        ↑(modelCentre (2*a+k)-crosscapPolarOffset z.1) at hq
      rw [sub_eq_add_neg] at hq
      have hh := add_left_cancel (OnePoint.coe_injective hq)
      exact (crosscapPolarOffset_ne_neg hw hz hh).elim

/-- The quotient images of opposite sectors meet only on the diameter
of the source disc. -/
theorem crosscap_sector_mixed_diameter {a b c k : ℕ}
    (z w : ↥(closedBall (0 : ℂ) 1))
    (he : Quot.mk (ModelGlue a b (2*a+b+c)) (crosscapPolarBase (2*a+k) (2*a+b+c) true z)=
      Quot.mk _ (crosscapPolarBase (2*a+k) (2*a+b+c) false w)) :
    z.1.im=0 ∧ w.1.im=0 := by
  have hz := mem_closedBall_zero_iff.mp z.2
  have hw := mem_closedBall_zero_iff.mp w.2
  have hp : (crosscapPolarBase (2*a+k) (2*a+b+c) true z).1=
      (↑(modelCentre (2*a+k)+crosscapPolarOffset z.1) : OnePoint EuclideanPlane) := by
    rw [crosscapPolarBase_val]
    rfl
  have hbound := crosscapPolarOffset_bounds hz
  have hnear : ‖crosscapPolarOffset z.1‖<2 := by linarith only [hbound.2]
  rcases model_quot_eq_near_crosscap hp hnear he with heq|⟨hn,hq⟩
  · have hh := congrArg Subtype.val heq
    rw [crosscapPolarBase_val,crosscapPolarBase_val] at hh
    change (↑(modelCentre (2*a+k)+crosscapPolarOffset z.1) : OnePoint EuclideanPlane)=
      ↑(modelCentre (2*a+k)+ -crosscapPolarOffset w.1) at hh
    exact (crosscapPolarOffset_ne_neg hz hw (add_left_cancel (OnePoint.coe_injective hh))).elim
  · rw [crosscapPolarBase_val] at hq
    change (↑(modelCentre (2*a+k)+ -crosscapPolarOffset w.1) : OnePoint EuclideanPlane)=
      ↑(modelCentre (2*a+k)-crosscapPolarOffset z.1) at hq
    rw [sub_eq_add_neg] at hq
    have hoff : crosscapPolarOffset w.1=crosscapPolarOffset z.1 :=
      neg_injective (add_left_cancel (OnePoint.coe_injective hq))
    have hnw : ‖crosscapPolarOffset w.1‖=1 := by rw [hoff,hn]
    rw [norm_crosscapPolarOffset] at hn hnw
    have hzim : |z.1.im|=0 := by linarith only [hn]
    have hwim : |w.1.im|=0 := by linarith only [hnw]
    exact ⟨abs_eq_zero.mp hzim,abs_eq_zero.mp hwim⟩

end GraphMinor.GM05
