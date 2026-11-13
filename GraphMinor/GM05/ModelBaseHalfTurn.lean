module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM19.CapModel
import GraphMinor.Surface.ModelPresent
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# A supported half turn preserves the model base

In the crosscap obstruction for GM V, (8.10), the supported half turn
around one unit hole must keep the sphere with all hole interiors
removed. It preserves distance from its own centre. The other centres
are at least three apart, so a point moved within radius three halves
stays outside all other unit holes. The inverse has the same support
and distance properties, giving a homeomorphism of the model base.
-/

public section

namespace GraphMinor.GM05

open Set Topology Metric Surface

private theorem preserves_holes (i n : ℕ) (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre i)=dist x (modelCentre i))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre i) → Θ x=x)
    {x : EuclideanPlane} (hx : ∀ j<n,1 ≤ dist x (modelCentre j)) :
    ∀ j<n,1 ≤ dist (Θ x) (modelCentre j) := by
  intro j hj
  by_cases hfar : 3/2 ≤ dist x (modelCentre i)
  · rw [hfix x hfar]
    exact hx j hj
  by_cases hji : j=i
  · subst j
    rw [hnorm]
    exact hx i hj
  have hcentres := GM19.three_le_dist_centre (Ne.symm hji)
  have htri := dist_triangle (modelCentre i) (Θ x) (modelCentre j)
  rw [dist_comm (modelCentre i) (Θ x),hnorm] at htri
  have hnear : dist x (modelCentre i)<3/2 := lt_of_not_ge hfar
  linarith only [hcentres,htri,hnear]

/-- A homeomorphism supported within three halves of one model centre
fixes the unit circles around all other model centres. -/
theorem supported_half_turn_fixes_other_boundary (i k : ℕ)
    (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre i) → Θ x=x)
    (hki : k ≠ i) {u : EuclideanPlane} (hu : ‖u‖=1) :
    Θ (modelCentre k+u)=modelCentre k+u := by
  have hcentres := GM19.three_le_dist_centre (Ne.symm hki)
  have hdist : dist (modelCentre k+u) (modelCentre k)=1 := by
    rw [dist_eq_norm,add_sub_cancel_left,hu]
  have htri := dist_triangle (modelCentre i) (modelCentre k+u) (modelCentre k)
  rw [dist_comm (modelCentre i) (modelCentre k+u),hdist] at htri
  apply hfix
  linarith only [hcentres,htri]

/-- A half turn supported near one hole keeps the sphere with all hole
interiors removed. The inverse has the same distance and support
properties, so the implication is an equivalence. -/
theorem modelBase_half_turn_iff (i n : ℕ) (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre i)=dist x (modelCentre i))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre i) → Θ x=x)
    (p : OnePoint EuclideanPlane) :
    p ∈ modelBase n ↔ Θ.onePointCongr p ∈ modelBase n := by
  have hnorm' (x : EuclideanPlane) : dist (Θ.symm x) (modelCentre i)=dist x (modelCentre i) := by
    have h := hnorm (Θ.symm x)
    rw [Θ.apply_symm_apply] at h
    exact h.symm
  have hfix' (x : EuclideanPlane) (hx : 3/2 ≤ dist x (modelCentre i)) : Θ.symm x=x := by
    apply Θ.injective
    rw [Θ.apply_symm_apply,hfix x hx]
  have hf (p : OnePoint EuclideanPlane) (hp : p ∈ modelBase n) :
      Θ.onePointCongr p ∈ modelBase n := by
    cases p using OnePoint.rec with
    | infty => simpa only [Homeomorph.onePointCongr_apply,OnePoint.map_infty] using hp
    | coe x =>
      change (↑(Θ x) : OnePoint EuclideanPlane) ∈ modelBase n
      exact mem_modelBase_coe.mpr (preserves_holes i n Θ hnorm hfix (mem_modelBase_coe.mp hp))
  constructor
  · exact hf p
  · intro hp
    cases p using OnePoint.rec with
    | infty => exact hp
    | coe x =>
      change (↑(Θ x) : OnePoint EuclideanPlane) ∈ modelBase n at hp
      have hh := preserves_holes i n Θ.symm hnorm' hfix' (mem_modelBase_coe.mp hp)
      rw [Θ.symm_apply_apply] at hh
      exact mem_modelBase_coe.mpr hh

/-- The homeomorphism of the sphere with holes induced by the supported
half turn. It is the restriction of the one-point extension. -/
noncomputable def modelBaseHalfTurn (i n : ℕ) (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre i)=dist x (modelCentre i))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre i) → Θ x=x) :
    modelBase n ≃ₜ modelBase n :=
  Θ.onePointCongr.subtype (modelBase_half_turn_iff i n Θ hnorm hfix)

/-- The base restriction acts by the one-point extension on points. -/
theorem modelBaseHalfTurn_apply_val (i n : ℕ) (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre i)=dist x (modelCentre i))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre i) → Θ x=x) (p : modelBase n) :
    (modelBaseHalfTurn i n Θ hnorm hfix p).1=Θ.onePointCongr p.1 := by rfl

end GraphMinor.GM05
