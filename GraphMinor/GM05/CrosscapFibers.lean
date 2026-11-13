module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.ModelPartners
import GraphMinor.GM05.ModelQuotientFibers
import GraphMinor.GM19.CapModel

/-!
# Quotient fibers near one crosscap

For the reversing disc in GM V, (8.10), points within distance two of
the selected model centre can meet no other unit hole. A nontrivial
identification there is therefore exactly the antipodal identification
on that crosscap's unit circle. Points strictly outside all glued
circles have singleton fibers.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

private theorem near_hole_index {i j : ℕ} {v u : EuclideanPlane}
    (hv : ‖v‖<2) (hu : ‖u‖=1) (he : modelCentre i+v=modelCentre j+u) : i=j := by
  by_contra hij
  have hc := GM19.three_le_dist_centre hij
  have ht := dist_triangle (modelCentre i) (modelCentre i+v) (modelCentre j)
  have h₁ : dist (modelCentre i) (modelCentre i+v)=‖v‖ := by
    rw [dist_comm,dist_eq_norm,add_sub_cancel_left]
  have h₂ : dist (modelCentre i+v) (modelCentre j)=1 := by
    rw [he,dist_eq_norm,add_sub_cancel_left,hu]
  rw [h₁,h₂] at ht
  linarith only [hc,ht,hv]

/-- A generating identification within distance two of a crosscap
centre is the antipodal pair of that crosscap's unit circle. -/
theorem model_gluing_near_crosscap {a b n k : ℕ} {p q : modelBase n}
    {v : EuclideanPlane} (hp : p.1=(↑(modelCentre (2*a+k)+v) : OnePoint EuclideanPlane))
    (hv : ‖v‖<2) (h : ModelGlue a b n p q ∨ ModelGlue a b n q p) :
    ‖v‖=1 ∧ q.1=(↑(modelCentre (2*a+k)-v) : OnePoint EuclideanPlane) := by
  rcases model_gluing_cases h with h|h|h
  · obtain ⟨j,hj,u,hu,hp',hq⟩ := h
    have he := near_hole_index hv hu (OnePoint.coe_injective (hp.symm.trans hp'))
    omega
  · obtain ⟨j,hj,u,hu,hp',hq⟩ := h
    have he := near_hole_index hv (show ‖modelMirror u‖=1 by rw [GM19.norm_modelMirror,hu])
      (OnePoint.coe_injective (hp.symm.trans hp'))
    omega
  · obtain ⟨j,hj,u,hu,hp',hq⟩ := h
    have he := near_hole_index hv hu (OnePoint.coe_injective (hp.symm.trans hp'))
    have hejk : j=k := by omega
    subst j
    have hvu : v=u := add_left_cancel (OnePoint.coe_injective (hp.symm.trans hp'))
    subst u
    exact ⟨hu,hq⟩

/-- Quotient equality near a crosscap is equality of the base points
or that crosscap's unit-circle antipodal identification. -/
theorem model_quot_eq_near_crosscap {a b n k : ℕ} {p q : modelBase n}
    {v : EuclideanPlane} (hp : p.1=(↑(modelCentre (2*a+k)+v) : OnePoint EuclideanPlane))
    (hv : ‖v‖<2) (he : Quot.mk (ModelGlue a b n) p=Quot.mk _ q) :
    p=q ∨ (‖v‖=1 ∧ q.1=(↑(modelCentre (2*a+k)-v) : OnePoint EuclideanPlane)) := by
  rcases model_quot_eq_iff.mp he with he|he
  · exact .inl he
  · exact .inr (model_gluing_near_crosscap hp hv he)

/-- A point strictly outside all glued boundary circles has a singleton
fiber under the model quotient. -/
theorem model_quot_eq_of_off_circles {a b n : ℕ} {p q : modelBase n} {x : EuclideanPlane}
    (hp : p.1=(↑x : OnePoint EuclideanPlane))
    (hx : ∀ i<2*a+b,1<dist x (modelCentre i))
    (he : Quot.mk (ModelGlue a b n) p=Quot.mk _ q) : p=q := by
  rcases model_quot_eq_iff.mp he with he|he
  · exact he
  rcases model_gluing_cases he with h|h|h
  · obtain ⟨i,hi,u,hu,hp',-⟩ := h
    have he' := OnePoint.coe_injective (hp.symm.trans hp')
    have hd := hx (2*i) (by omega)
    rw [he',dist_eq_norm,add_sub_cancel_left,hu] at hd
    exact (lt_irrefl 1 hd).elim
  · obtain ⟨i,hi,u,hu,hp',-⟩ := h
    have he' := OnePoint.coe_injective (hp.symm.trans hp')
    have hd := hx (2*i+1) (by omega)
    rw [he',dist_eq_norm,add_sub_cancel_left,GM19.norm_modelMirror,hu] at hd
    exact (lt_irrefl 1 hd).elim
  · obtain ⟨i,hi,u,hu,hp',-⟩ := h
    have he' := OnePoint.coe_injective (hp.symm.trans hp')
    have hd := hx (2*a+i) (by omega)
    rw [he',dist_eq_norm,add_sub_cancel_left,hu] at hd
    exact (lt_irrefl 1 hd).elim

end GraphMinor.GM05
