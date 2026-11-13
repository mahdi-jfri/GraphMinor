module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.CoreHalfTurn
import GraphMinor.Surface.Jordan

/-!
# A half turn supported around one crosscap

To rule out crosscaps on an oriented surface in GM V, (8.10), rotate
the boundary of one model hole through a half turn and undo the motion
before reaching any other hole. The library disc twist supplies the
plane homeomorphism. It preserves distance from the hole centre,
fixes points at distance at least three halves, and exchanges antipodal
points of the unit boundary circle.
-/

public section

namespace GraphMinor.GM05

open Set Topology Metric Surface

/-- A radial half turn around a model hole, supported in its radius
three-halves neighbourhood. -/
theorem exists_crosscap_half_turn_core (i : ℕ) :
    ∃ Θ : EuclideanPlane ≃ₜ EuclideanPlane,
      (∀ x,dist (Θ x) (modelCentre i)=dist x (modelCentre i)) ∧
      (∀ x,3/2 ≤ dist x (modelCentre i) → Θ x=x) ∧
      ∀ u : EuclideanPlane,‖u‖ ≤ 5/4 → Θ (modelCentre i+u)=modelCentre i-u := by
  obtain ⟨θ,hfix,hnorm,hcore⟩ := exists_complex_half_turn_core
  let θP : EuclideanPlane ≃ₜ EuclideanPlane :=
    complexPlane.symm.toHomeomorph.trans (θ.trans complexPlane.toHomeomorph)
  have hnormP (x : EuclideanPlane) : ‖θP x‖=‖x‖ := by
    change ‖complexPlane (θ (complexPlane.symm x))‖=‖x‖
    rw [complexPlane.norm_map,hnorm,complexPlane.symm.norm_map]
  have hfixP (x : EuclideanPlane) (hx : 3/2 ≤ ‖x‖) : θP x=x := by
    change complexPlane (θ (complexPlane.symm x))=x
    rw [hfix _ (by rwa [complexPlane.symm.norm_map])]
    exact complexPlane.apply_symm_apply x
  have hcoreP (u : EuclideanPlane) (hu : ‖u‖ ≤ 5/4) : θP u= -u := by
    change complexPlane (θ (complexPlane.symm u))= -u
    rw [hcore _ (by rwa [complexPlane.symm.norm_map]),map_neg,complexPlane.apply_symm_apply]
  let Θ : EuclideanPlane ≃ₜ EuclideanPlane :=
    (Homeomorph.addLeft (-modelCentre i)).trans (θP.trans (Homeomorph.addLeft (modelCentre i)))
  have hΘ (x : EuclideanPlane) : Θ x=modelCentre i+θP (x-modelCentre i) := by
    simp only [Θ,Homeomorph.trans_apply,Homeomorph.coe_addLeft]
    rw [neg_add_eq_sub]
  refine ⟨Θ,?_,?_,?_⟩
  · intro x
    rw [hΘ,dist_eq_norm,add_sub_cancel_left,hnormP,dist_eq_norm]
  · intro x hx
    rw [hΘ,hfixP _ (by simpa only [dist_eq_norm] using hx)]
    abel
  · intro u hu
    rw [hΘ,add_sub_cancel_left,hcoreP u hu]
    rfl

/-- The supported half turn exchanges antipodal points of the unit
circle while fixing all points at distance at least three halves. -/
theorem exists_crosscap_half_turn (i : ℕ) :
    ∃ Θ : EuclideanPlane ≃ₜ EuclideanPlane,
      (∀ x,dist (Θ x) (modelCentre i)=dist x (modelCentre i)) ∧
      (∀ x,3/2 ≤ dist x (modelCentre i) → Θ x=x) ∧
      ∀ u : EuclideanPlane,‖u‖=1 → Θ (modelCentre i+u)=modelCentre i-u := by
  obtain ⟨Θ,hn,hf,hc⟩ := exists_crosscap_half_turn_core i
  exact ⟨Θ,hn,hf,fun u hu ↦ hc u (by rw [hu]; norm_num)⟩

end GraphMinor.GM05
