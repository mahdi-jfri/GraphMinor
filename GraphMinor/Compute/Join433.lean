module

public import GraphMinor.Compute.Algorithm33
public import GraphMinor.Compute.Algorithm33Multigraph
public import GraphMinor.Compute.Specs4

/-!
# Joining `Alg33Spec` with `algorithm_3_3_multigraph_cases` (`Algorithm33.lean`)

This file proves `Alg33Spec` (`GraphMinor/Compute/Specs4.lean`) unconditionally from
`algorithm_3_3_multigraph_cases` (`GraphMinor/Compute/Algorithm33Multigraph.lean`, re-exported by
`GraphMinor/Compute/Algorithm33.lean`).
-/

@[expose] public section

namespace GraphMinor.Compute

/-- For every fixed `ω ≥ 2` and distinct array indices `a_in, a_G_out, a_bd_out < a_base`,
`alg33MultiProg ω a_in a_G_out a_bd_out a_base r_base` satisfies `Alg33Spec`. -/
theorem alg33Spec_of_algorithm_3_3 (ω : ℕ) (hω : 2 ≤ ω)
    (a_in a_G_out a_bd_out a_base r_base : ℕ)
    (ha_in : a_in < a_base) (ha_G : a_G_out < a_base) (ha_bd : a_bd_out < a_base)
    (hne_in_G : a_in ≠ a_G_out) (hne_in_bd : a_in ≠ a_bd_out) (hne_G_bd : a_G_out ≠ a_bd_out) :
    Alg33Spec ω a_in a_G_out a_bd_out a_base r_base
      (alg33MultiProg ω a_in a_G_out a_bd_out a_base r_base) := by
  classical
  rcases algorithm_3_3_multigraph_cases ω hω a_in a_G_out a_bd_out a_base r_base
      ha_in ha_G ha_bd hne_in_G hne_in_bd hne_G_bd with
    ⟨C₃₃, c_w, hC, hcw, hexec⟩
  refine ⟨C₃₃, c_w, hC, hcw, fun n G w hw _ _ s hin => ?_⟩
  rcases hexec n G w hw s hin with
    ⟨s', t, G', bdCode, hex, ht, hle, hbd, hor, haG, habd, hr, hregs, harrs⟩
  refine ⟨s', t, G', bdCode, hex,
    le_trans ht (Nat.mul_le_mul_left C₃₃ (by omega)),
    hle, hbd, hor, haG, habd, hr, hregs, harrs⟩

end GraphMinor.Compute
