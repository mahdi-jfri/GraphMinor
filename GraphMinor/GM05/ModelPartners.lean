module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM19.CapModel
import GraphMinor.Surface.ModelSides

/-!
# Uniqueness of model gluing partners

For the local crosscap disc in GM V, (8.10), the quotient map must be
injective on each of two small sectors. Unit circles around distinct
model centres are disjoint, since their centres have distance at least
three. Each point on a glued circle therefore has just one partner:
the reflected point on the other handle circle, or its antipode on a
crosscap circle.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

/-- A point cannot lie on the unit circles of two distinct model holes. -/
theorem modelCentre_eq_of_unit_offset {i j : ℕ} {u v : EuclideanPlane}
    (hu : ‖u‖=1) (hv : ‖v‖=1) (he : modelCentre i+u=modelCentre j+v) : i=j := by
  by_contra hij
  have hc := GM19.three_le_dist_centre hij
  have htri := dist_triangle (modelCentre i) (modelCentre i+u) (modelCentre j)
  have h₁ : dist (modelCentre i) (modelCentre i+u)=1 := by
    rw [dist_comm,dist_eq_norm,add_sub_cancel_left,hu]
  have h₂ : dist (modelCentre i+u) (modelCentre j)=1 := by
    rw [he,dist_eq_norm,add_sub_cancel_left,hv]
  rw [h₁,h₂] at htri
  linarith only [hc,htri]

/-- A glued pair is a handle pair in either direction or an antipodal
pair on a crosscap circle. -/
theorem model_gluing_cases {a b n : ℕ} {p q : modelBase n}
    (h : ModelGlue a b n p q ∨ ModelGlue a b n q p) :
    (∃ i<a,∃ u : EuclideanPlane,‖u‖=1 ∧
      p.1=(↑(modelCentre (2*i)+u) : OnePoint EuclideanPlane) ∧
      q.1=↑(modelCentre (2*i+1)+modelMirror u)) ∨
    (∃ i<a,∃ u : EuclideanPlane,‖u‖=1 ∧
      p.1=(↑(modelCentre (2*i+1)+modelMirror u) : OnePoint EuclideanPlane) ∧
      q.1=↑(modelCentre (2*i)+u)) ∨
    (∃ i<b,∃ u : EuclideanPlane,‖u‖=1 ∧
      p.1=(↑(modelCentre (2*a+i)+u) : OnePoint EuclideanPlane) ∧
      q.1=↑(modelCentre (2*a+i)-u)) := by
  rcases h with h|h
  · cases h with
    | handle i hi u hu p q hp hq => exact .inl ⟨i,hi,u,hu,hp,hq⟩
    | crosscap i hi u hu p q hp hq => exact .inr (.inr ⟨i,hi,u,hu,hp,hq⟩)
  · cases h with
    | handle i hi u hu q p hq hp => exact .inr (.inl ⟨i,hi,u,hu,hp,hq⟩)
    | crosscap i hi u hu q p hq hp =>
      refine .inr (.inr ⟨i,hi,-u,by rw [norm_neg,hu],?_,?_⟩)
      · simpa only [sub_eq_add_neg] using hp
      · simpa only [sub_neg_eq_add] using hq

/-- A point has at most one distinct gluing partner in the model base.
The relation includes both directions of the handle identifications. -/
theorem model_gluing_partner_unique {a b n : ℕ} {p q r : modelBase n}
    (hq : ModelGlue a b n p q ∨ ModelGlue a b n q p)
    (hr : ModelGlue a b n p r ∨ ModelGlue a b n r p) : q=r := by
  rcases model_gluing_cases hq with hq|hq|hq <;> rcases model_gluing_cases hr with hr|hr|hr
  all_goals
    obtain ⟨i,hi,u,hu,hp,hq⟩ := hq
    obtain ⟨j,hj,v,hv,hp',hr⟩ := hr
  · have hij := modelCentre_eq_of_unit_offset hu hv (OnePoint.coe_injective (hp.symm.trans hp'))
    have heij : i=j := by omega
    subst j
    have huv : u=v := add_left_cancel (OnePoint.coe_injective (hp.symm.trans hp'))
    subst v
    exact Subtype.ext (hq.trans hr.symm)
  · have hij := modelCentre_eq_of_unit_offset hu
      (show ‖modelMirror v‖=1 by rw [GM19.norm_modelMirror,hv]) (OnePoint.coe_injective (hp.symm.trans hp'))
    omega
  · have hij := modelCentre_eq_of_unit_offset hu hv (OnePoint.coe_injective (hp.symm.trans hp'))
    omega
  · have hij := modelCentre_eq_of_unit_offset
      (show ‖modelMirror u‖=1 by rw [GM19.norm_modelMirror,hu]) hv (OnePoint.coe_injective (hp.symm.trans hp'))
    omega
  · have hij := modelCentre_eq_of_unit_offset
      (show ‖modelMirror u‖=1 by rw [GM19.norm_modelMirror,hu])
      (show ‖modelMirror v‖=1 by rw [GM19.norm_modelMirror,hv]) (OnePoint.coe_injective (hp.symm.trans hp'))
    have heij : i=j := by omega
    subst j
    have huv : u=v := mirH.injective (add_left_cancel (OnePoint.coe_injective (hp.symm.trans hp')))
    subst v
    exact Subtype.ext (hq.trans hr.symm)
  · have hij := modelCentre_eq_of_unit_offset
      (show ‖modelMirror u‖=1 by rw [GM19.norm_modelMirror,hu]) hv (OnePoint.coe_injective (hp.symm.trans hp'))
    omega
  · have hij := modelCentre_eq_of_unit_offset hu hv (OnePoint.coe_injective (hp.symm.trans hp'))
    omega
  · have hij := modelCentre_eq_of_unit_offset hu
      (show ‖modelMirror v‖=1 by rw [GM19.norm_modelMirror,hv]) (OnePoint.coe_injective (hp.symm.trans hp'))
    omega
  · have hij := modelCentre_eq_of_unit_offset hu hv (OnePoint.coe_injective (hp.symm.trans hp'))
    have heij : i=j := by omega
    subst j
    have huv : u=v := add_left_cancel (OnePoint.coe_injective (hp.symm.trans hp'))
    subst v
    exact Subtype.ext (hq.trans hr.symm)

end GraphMinor.GM05
