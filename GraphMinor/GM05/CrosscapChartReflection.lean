module

public import GraphMinor.GM05.CrosscapPolarChart
public import GraphMinor.GM05.CrosscapModelMap
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The half turn reflects the local disc

For the crosscap obstruction in GM V, (8.10), the supported map is
exactly negation on both small polar sectors. It exchanges them.
Thus the descended model homeomorphism acts on their joined source
disc by complex conjugation: one boundary point is fixed and two
others are exchanged.
-/

public section

namespace GraphMinor.GM05

open Set Topology Metric Surface

/-- Reflection of the closed complex unit disc across its real diameter. -/
noncomputable def complexDiscConj : ↥(closedBall (0 : ℂ) 1) ≃ₜ ↥(closedBall (0 : ℂ) 1) :=
  Complex.conjLIE.toHomeomorph.subtype fun z ↦ by
    simp only [mem_closedBall_zero_iff,LinearIsometryEquiv.coe_toHomeomorph,Complex.conjLIE_apply,Complex.norm_conj]

/-- Reflection acts on the underlying complex coordinate by conjugation. -/
theorem complexDiscConj_val (z : ↥(closedBall (0 : ℂ) 1)) :
    (complexDiscConj z).1=starRingEnd ℂ z.1 := by rfl

/-- Reflection preserves each unsigned polar sector point. -/
theorem crosscapPolarBase_conj (i n : ℕ) (σ : Bool) (z : ↥(closedBall (0 : ℂ) 1)) :
    crosscapPolarBase i n σ (complexDiscConj z)=crosscapPolarBase i n σ z := by
  apply Subtype.ext
  rw [crosscapPolarBase_val,crosscapPolarBase_val,complexDiscConj_val,crosscapPolarOffset_conj]

/-- Exact negation in the narrow annulus exchanges the two sector
images under the model quotient. -/
theorem crosscapModelHalfTurn_sector {a b c k : ℕ} (hk : k<b)
    (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre (2*a+k))=dist x (modelCentre (2*a+k)))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre (2*a+k)) → Θ x=x)
    (hcircle : ∀ u : EuclideanPlane,‖u‖=1 → Θ (modelCentre (2*a+k)+u)=modelCentre (2*a+k)-u)
    (hcore : ∀ u : EuclideanPlane,‖u‖ ≤ 5/4 → Θ (modelCentre (2*a+k)+u)=modelCentre (2*a+k)-u)
    (σ : Bool) (z : ↥(closedBall (0 : ℂ) 1)) :
    crosscapModelHalfTurn hk Θ hnorm hfix hcircle
        (Quot.mk _ (crosscapPolarBase (2*a+k) (2*a+b+c) σ z))=
      Quot.mk _ (crosscapPolarBase (2*a+k) (2*a+b+c) (!σ) z) := by
  rw [crosscapModelHalfTurn_mk]
  apply congrArg (Quot.mk _)
  apply Subtype.ext
  rw [modelBaseHalfTurn_apply_val,crosscapPolarBase_val,crosscapPolarBase_val]
  have hb := (crosscapPolarOffset_bounds (mem_closedBall_zero_iff.mp z.2)).2
  cases σ
  · change (↑(Θ (modelCentre (2*a+k)+ -crosscapPolarOffset z.1)) : OnePoint EuclideanPlane)=
      ↑(modelCentre (2*a+k)+crosscapPolarOffset z.1)
    rw [hcore _ (by rw [norm_neg]; linarith only [hb]),sub_neg_eq_add]
  · change (↑(Θ (modelCentre (2*a+k)+crosscapPolarOffset z.1)) : OnePoint EuclideanPlane)=
      ↑(modelCentre (2*a+k)+ -crosscapPolarOffset z.1)
    rw [hcore _ (by linarith only [hb])]
    rfl

/-- The descended homeomorphism reflects the whole local disc across
its diameter. -/
theorem crosscapPolarChart_reflection {a b c k : ℕ} (hk : k<b)
    (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre (2*a+k))=dist x (modelCentre (2*a+k)))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre (2*a+k)) → Θ x=x)
    (hcircle : ∀ u : EuclideanPlane,‖u‖=1 → Θ (modelCentre (2*a+k)+u)=modelCentre (2*a+k)-u)
    (hcore : ∀ u : EuclideanPlane,‖u‖ ≤ 5/4 → Θ (modelCentre (2*a+k)+u)=modelCentre (2*a+k)-u)
    (z : ↥(closedBall (0 : ℂ) 1)) :
    crosscapModelHalfTurn hk Θ hnorm hfix hcircle (crosscapPolarChart a b c k z)=
      crosscapPolarChart a b c k (complexDiscConj z) := by
  by_cases hz : 0 ≤ z.1.im
  · have hzc : (complexDiscConj z).1.im ≤ 0 := by rw [complexDiscConj_val,Complex.conj_im]; linarith only [hz]
    rw [crosscapPolarChart_of_nonneg a b c k z hz,crosscapModelHalfTurn_sector hk Θ hnorm hfix hcircle hcore,
      crosscapPolarChart_of_nonpos hk _ hzc,crosscapPolarBase_conj]
    rfl
  · have hzc : 0 ≤ (complexDiscConj z).1.im := by rw [complexDiscConj_val,Complex.conj_im]; linarith only [hz]
    rw [crosscapPolarChart_of_nonpos hk z (le_of_lt (lt_of_not_ge hz)),crosscapModelHalfTurn_sector hk Θ hnorm hfix hcircle hcore,
      crosscapPolarChart_of_nonneg a b c k _ hzc,crosscapPolarBase_conj]
    rfl

end GraphMinor.GM05
