module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverCuffInterval

/-!
# The preceding cover strip approaches its right initial vertex

For the local side argument of VI (5.7), page 133, the chosen
initial lift is approached from the preceding cuff gap. The open
angular interval describing that gap has the initial angle in its
closure. Mapping that interval to the cover gives the required
incidence, without identifying endpoint copies when there is one path.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The prescribed initial lift belongs to the closure of its
preceding cover strip for every positive linkage size. -/
theorem cylinderInitialLift_mem_closure_preceding_cover_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i : Fin k) :
    cylinderInitialLift k i ∈ closure (cylinderCoverStrip L (i.val : ℤ)) := by
  let a := 2 * ((i.val : ℤ) : ℝ) * π / k
  let b := 2 * (((i.val : ℤ) + 1 : ℤ) : ℝ) * π / k
  have hab : a < b := by
    dsimp [a, b]
    apply (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hG.1)).mpr
    push_cast
    nlinarith only [pi_pos]
  let f : ℝ → CylinderCover := fun x => (⟨1, by norm_num⟩, x)
  have hfc : Continuous f := by fun_prop
  have hfb : f b = cylinderInitialLift k i := by
    apply Prod.ext
    · rfl
    · change b = (cylinderInitialLift k i).2
      simp only [b, cylinderInitialLift, Int.cast_add, Int.cast_natCast, Int.cast_one,
        Nat.cast_add, Nat.cast_one]
  have hbcl : b ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  have hsub : f '' Ioo a b ⊆ cylinderCoverStrip L (i.val : ℤ) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_cover_strip_on_initial_cuff_iff L hG hθ (i.val : ℤ) (f x) rfl).mpr hx
  rw [← hfb]
  exact closure_mono hsub (mem_closure_image hfc.continuousAt hbcl)

end GraphMinor.GM06
