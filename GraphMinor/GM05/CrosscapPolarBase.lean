module

public import GraphMinor.GM05.CrosscapPolarOffset
import GraphMinor.GM19.CapModel
import GraphMinor.Surface.ModelPresent

/-!
# The two polar sectors in the model base

For the local disc in GM V, (8.10), the two small sectors lie outside
the unit hole and inside radius nine eighths. Distinct model centres
are at least three apart, so the sectors miss all other removed holes.
Each sector therefore maps continuously into the model base. Along the
diameter their boundary points are antipodal and have the same model
quotient image.
-/

public section

namespace GraphMinor.GM05

open Set Topology Metric Surface

/-- A point with radius between one and three halves about one model
centre lies outside every removed unit hole. -/
theorem mem_modelBase_offset (i n : ℕ) {v : EuclideanPlane}
    (hlo : 1 ≤ ‖v‖) (hhi : ‖v‖ ≤ 3/2) :
    (↑(modelCentre i+v) : OnePoint EuclideanPlane) ∈ modelBase n := by
  apply mem_modelBase_coe.mpr
  intro j hj
  by_cases hji : j=i
  · subst j
    rw [dist_eq_norm,add_sub_cancel_left]
    exact hlo
  have hc := GM19.three_le_dist_centre (Ne.symm hji)
  have ht := dist_triangle (modelCentre i) (modelCentre i+v) (modelCentre j)
  have hd : dist (modelCentre i) (modelCentre i+v)=‖v‖ := by
    rw [dist_comm,dist_eq_norm,add_sub_cancel_left]
  rw [hd] at ht
  linarith only [hc,ht,hhi]

/-- One of the two polar sectors in the sphere with model holes.
The Boolean selects the offset or its antipode. -/
noncomputable def crosscapPolarBase (i n : ℕ) (σ : Bool)
    (z : ↥(closedBall (0 : ℂ) 1)) : modelBase n := by
  let v := if σ then crosscapPolarOffset z.1 else -crosscapPolarOffset z.1
  have hv : ‖v‖=‖crosscapPolarOffset z.1‖ := by cases σ <;> simp [v]
  have hb := crosscapPolarOffset_bounds (mem_closedBall_zero_iff.mp z.2)
  exact ⟨↑(modelCentre i+v),mem_modelBase_offset i n (hv ▸ hb.1) (by rw [hv]; linarith only [hb.2])⟩

/-- The base point has the prescribed signed polar offset. -/
theorem crosscapPolarBase_val (i n : ℕ) (σ : Bool) (z : ↥(closedBall (0 : ℂ) 1)) :
    (crosscapPolarBase i n σ z).1=(↑(modelCentre i+
      (if σ then crosscapPolarOffset z.1 else -crosscapPolarOffset z.1)) : OnePoint EuclideanPlane) := by rfl

/-- Each sector is continuous as a map into the model base. -/
theorem continuous_crosscapPolarBase (i n : ℕ) (σ : Bool) : Continuous (crosscapPolarBase i n σ) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun z : ↥(closedBall (0 : ℂ) 1) ↦
    (↑(modelCentre i+(if σ then crosscapPolarOffset z.1 else -crosscapPolarOffset z.1)) : OnePoint EuclideanPlane))
  apply OnePoint.continuous_coe.comp
  have ho : Continuous (fun z : ↥(closedBall (0 : ℂ) 1) ↦ crosscapPolarOffset z.1) :=
    continuous_crosscapPolarOffset.comp continuous_subtype_val
  cases σ
  · change Continuous (fun z : ↥(closedBall (0 : ℂ) 1) ↦ modelCentre i+ -crosscapPolarOffset z.1)
    exact continuous_const.add ho.neg
  · change Continuous (fun z : ↥(closedBall (0 : ℂ) 1) ↦ modelCentre i+crosscapPolarOffset z.1)
    exact continuous_const.add ho

/-- The two sectors agree in the model quotient along the diameter,
where their offsets lie on the crosscap's unit circle. -/
theorem crosscapPolarBase_seam {a b c k : ℕ} (hk : k<b)
    (z : ↥(closedBall (0 : ℂ) 1)) (hz : z.1.im=0) :
    Quot.mk (ModelGlue a b (2*a+b+c)) (crosscapPolarBase (2*a+k) (2*a+b+c) true z)=
      Quot.mk _ (crosscapPolarBase (2*a+k) (2*a+b+c) false z) := by
  have hn : ‖crosscapPolarOffset z.1‖=1 := by rw [norm_crosscapPolarOffset,hz,abs_zero,zero_div,add_zero]
  apply Quot.sound
  apply ModelGlue.crosscap k hk (crosscapPolarOffset z.1) hn
  · rw [crosscapPolarBase_val]
    rfl
  · rw [crosscapPolarBase_val]
    rfl

end GraphMinor.GM05
