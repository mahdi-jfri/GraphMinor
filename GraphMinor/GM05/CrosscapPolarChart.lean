module

public import GraphMinor.GM05.CrosscapPolarBase
import GraphMinor.GM05.CrosscapSectorFibers
import Mathlib.Topology.Piecewise

/-!
# The embedded local crosscap disc

For GM V, (8.10), use the positive polar sector on the upper half of
the source disc and the negative sector on the lower half. The sectors
agree in the quotient along the diameter, so the joined map is
continuous. Within a sector the polar coordinates determine the source
point, and opposite sectors can meet only along the diameter. Thus the
joined map is injective.
-/

public section

namespace GraphMinor.GM05

open Set Topology Metric Surface

/-- The two sectors joined in the actual model surface. -/
noncomputable def crosscapPolarChart (a b c k : ℕ) (z : ↥(closedBall (0 : ℂ) 1)) : Quot (ModelGlue a b (2*a+b+c)) :=
  if 0 ≤ z.1.im then Quot.mk _ (crosscapPolarBase (2*a+k) (2*a+b+c) true z)
  else Quot.mk _ (crosscapPolarBase (2*a+k) (2*a+b+c) false z)

/-- On the upper half-disc the chart is the positive sector. -/
theorem crosscapPolarChart_of_nonneg (a b c k : ℕ) (z : ↥(closedBall (0 : ℂ) 1)) (hz : 0 ≤ z.1.im) :
    crosscapPolarChart a b c k z=Quot.mk _ (crosscapPolarBase (2*a+k) (2*a+b+c) true z) := by
  unfold crosscapPolarChart
  rw [ite_eq_left hz]

/-- On the lower half-disc the chart is the negative sector. -/
theorem crosscapPolarChart_of_neg (a b c k : ℕ) (z : ↥(closedBall (0 : ℂ) 1)) (hz : z.1.im<0) :
    crosscapPolarChart a b c k z=Quot.mk _ (crosscapPolarBase (2*a+k) (2*a+b+c) false z) := by
  unfold crosscapPolarChart
  rw [ite_eq_right (not_le.mpr hz)]

/-- On the closed lower half-disc the negative-sector formula remains
valid on the diameter, since the two quotient images agree there. -/
theorem crosscapPolarChart_of_nonpos {a b c k : ℕ} (hk : k<b)
    (z : ↥(closedBall (0 : ℂ) 1)) (hz : z.1.im ≤ 0) :
    crosscapPolarChart a b c k z=Quot.mk _ (crosscapPolarBase (2*a+k) (2*a+b+c) false z) := by
  by_cases he : z.1.im=0
  · rw [crosscapPolarChart_of_nonneg a b c k z (by rw [he])]
    exact crosscapPolarBase_seam hk z he
  · exact crosscapPolarChart_of_neg a b c k z (lt_of_le_of_ne hz he)

/-- The two sectors agree on the diameter, so their joined quotient map
is continuous. -/
theorem continuous_crosscapPolarChart {a b c k : ℕ} (hk : k<b) :
    Continuous (crosscapPolarChart a b c k) := by
  classical
  unfold crosscapPolarChart
  apply Continuous.if
  · intro z hz
    have he : (0 : ℝ)=z.1.im :=
      frontier_le_subset_eq continuous_const (Complex.continuous_im.comp continuous_subtype_val) hz
    exact crosscapPolarBase_seam hk z he.symm
  · exact continuous_quot_mk.comp (continuous_crosscapPolarBase _ _ true)
  · exact continuous_quot_mk.comp (continuous_crosscapPolarBase _ _ false)

/-- The joined crosscap chart is injective on the closed source disc. -/
theorem injective_crosscapPolarChart (a b c k : ℕ) :
    Function.Injective (crosscapPolarChart a b c k) := by
  classical
  intro z w he
  have hz := mem_closedBall_zero_iff.mp z.2
  have hw := mem_closedBall_zero_iff.mp w.2
  unfold crosscapPolarChart at he
  by_cases hzp : 0 ≤ z.1.im <;> by_cases hwp : 0 ≤ w.1.im
  all_goals simp only [hzp,hwp,↓reduceIte] at he
  · have hoff := crosscap_sector_offset_eq true z w he
    obtain ⟨hre,him⟩ := (crosscapPolarOffset_eq_iff hz hw).mp hoff
    rw [abs_of_nonneg hzp,abs_of_nonneg hwp] at him
    exact Subtype.ext (Complex.ext hre him)
  · have hzero := (crosscap_sector_mixed_diameter z w he).2
    exact (hwp (by rw [hzero])).elim
  · have hzero := (crosscap_sector_mixed_diameter w z he.symm).2
    exact (hzp (by rw [hzero])).elim
  · have hoff := crosscap_sector_offset_eq false z w he
    obtain ⟨hre,him⟩ := (crosscapPolarOffset_eq_iff hz hw).mp hoff
    rw [abs_of_nonpos (le_of_lt (lt_of_not_ge hzp)),abs_of_nonpos (le_of_lt (lt_of_not_ge hwp))] at him
    exact Subtype.ext (Complex.ext hre (neg_injective him))

end GraphMinor.GM05
