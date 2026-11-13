module

public import GraphMinor.GM05.ModelBaseHalfTurn
import GraphMinor.GM05.CrosscapGlue
import Mathlib.Topology.Homeomorph.Quotient

/-!
# Descending the half turn to the model surface

For the orientable classification step of GM V, (8.10), the supported
half turn preserves the identifications on the model base. Its inverse
has the same distance, support, and antipodal-boundary properties.
Thus the base homeomorphism descends to a homeomorphism of the actual
library model surface, with its action on quotient points specified.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

/-- The supported half turn preserves the model gluing relation in
both directions, since its inverse satisfies the same boundary and
support conditions. -/
theorem crosscap_half_turn_glue_iff {a b c k : ℕ} (hk : k<b)
    (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre (2*a+k))=dist x (modelCentre (2*a+k)))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre (2*a+k)) → Θ x=x)
    (hcircle : ∀ u : EuclideanPlane,‖u‖=1 →
      Θ (modelCentre (2*a+k)+u)=modelCentre (2*a+k)-u)
    (p q : modelBase (2*a+b+c)) :
    ModelGlue a b (2*a+b+c) p q ↔ ModelGlue a b (2*a+b+c)
      (modelBaseHalfTurn (2*a+k) (2*a+b+c) Θ hnorm hfix p)
      (modelBaseHalfTurn (2*a+k) (2*a+b+c) Θ hnorm hfix q) := by
  have hnorm' (x : EuclideanPlane) :
      dist (Θ.symm x) (modelCentre (2*a+k))=dist x (modelCentre (2*a+k)) := by
    have h := hnorm (Θ.symm x)
    rw [Θ.apply_symm_apply] at h
    exact h.symm
  have hfix' (x : EuclideanPlane) (hx : 3/2 ≤ dist x (modelCentre (2*a+k))) : Θ.symm x=x := by
    apply Θ.injective
    rw [Θ.apply_symm_apply,hfix x hx]
  have hcircle' (u : EuclideanPlane) (hu : ‖u‖=1) :
      Θ.symm (modelCentre (2*a+k)+u)=modelCentre (2*a+k)-u := by
    apply Θ.injective
    rw [Θ.apply_symm_apply]
    have h := hcircle (-u) (by rw [norm_neg,hu])
    simpa only [sub_eq_add_neg,neg_neg] using h.symm
  have hcomp (p : modelBase (2*a+b+c)) :
      modelBaseHalfTurn (2*a+k) (2*a+b+c) Θ.symm hnorm' hfix'
        (modelBaseHalfTurn (2*a+k) (2*a+b+c) Θ hnorm hfix p)=p := by
    apply Subtype.ext
    rw [modelBaseHalfTurn_apply_val,modelBaseHalfTurn_apply_val]
    change Θ.onePointCongr.symm (Θ.onePointCongr p.1)=p.1
    exact Θ.onePointCongr.symm_apply_apply p.1
  constructor
  · exact crosscap_half_turn_preserves_glue hk Θ hnorm hfix hcircle
  · intro h
    have h' := crosscap_half_turn_preserves_glue hk Θ.symm hnorm' hfix' hcircle' h
    rwa [hcomp,hcomp] at h'

/-- The model-surface homeomorphism induced by the supported half turn
about crosscap `k`. -/
noncomputable def crosscapModelHalfTurn {a b c k : ℕ} (hk : k<b)
    (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre (2*a+k))=dist x (modelCentre (2*a+k)))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre (2*a+k)) → Θ x=x)
    (hcircle : ∀ u : EuclideanPlane,‖u‖=1 →
      Θ (modelCentre (2*a+k)+u)=modelCentre (2*a+k)-u) :
    SurfaceModel a b c ≃ₜ SurfaceModel a b c :=
  Homeomorph.Quot.congr (modelBaseHalfTurn (2*a+k) (2*a+b+c) Θ hnorm hfix)
    (crosscap_half_turn_glue_iff hk Θ hnorm hfix hcircle)

/-- On quotient points, the descended map is the half turn of the
model-base point. -/
theorem crosscapModelHalfTurn_mk {a b c k : ℕ} (hk : k<b)
    (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre (2*a+k))=dist x (modelCentre (2*a+k)))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre (2*a+k)) → Θ x=x)
    (hcircle : ∀ u : EuclideanPlane,‖u‖=1 →
      Θ (modelCentre (2*a+k)+u)=modelCentre (2*a+k)-u)
    (p : modelBase (2*a+b+c)) :
    crosscapModelHalfTurn hk Θ hnorm hfix hcircle (Quot.mk _ p)=
      Quot.mk _ (modelBaseHalfTurn (2*a+k) (2*a+b+c) Θ hnorm hfix p) := by rfl

end GraphMinor.GM05
