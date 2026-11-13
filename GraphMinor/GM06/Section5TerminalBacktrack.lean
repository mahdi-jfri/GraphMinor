module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section4Winding

/-!
# The outer-cuff part of the tight helix

The curve in VI (5.3) moves backwards through half a boundary gap.
Its endpoints, winding, and only vertex contact are computed directly.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface
/-- The outer-cuff curve in VI (5.3), page 133. Starting at the terminal
vertex indexed by j, it decreases the angle by π/k to the preceding dual point. -/
noncomputable def terminalCuffBacktrackCurve (k : ℕ) (j : Fin k) : Curve ClosedCylinder :=
  ⟨fun u => cylinderPoint 2 (by simp)
      ((2 * ((j.1 + 1 : ℕ) : ℝ) - (u : ℝ)) * π / k),
    by dsimp [cylinderPoint]; fun_prop⟩
/-- The backtrack starts at its prescribed outer-cuff vertex. -/
theorem terminalCuffBacktrackCurve_zero {k : ℕ} (j : Fin k) :
    terminalCuffBacktrackCurve k j 0 = cylinderM2Point k j := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp ((2 * ((j.1 + 1 : ℕ) : ℝ) - (0 : ℝ)) * π / k) =
      Circle.exp (2 * ((j.1 + 1 : ℕ) : ℝ) * π / k)
    rw [sub_zero]
/-- The backtrack stays on the outer cuff. -/
theorem terminalCuffBacktrackCurve_mem_cuff2 {k : ℕ} (j : Fin k) (t : unitInterval) :
    terminalCuffBacktrackCurve k j t ∈ cylinderCuff2 := by
  simp only [terminalCuffBacktrackCurve, cylinderPoint, cylinderCuff2, mem_ofPred_eq]
  rfl
/-- The outer-cuff part of the helix in VI (5.3), page 133, has winding −1/(2k). -/
theorem windingNumber_terminalCuffBacktrackCurve {k : ℕ} (hk : 0 < k) (j : Fin k) :
    windingNumber (terminalCuffBacktrackCurve k j) = -(2 * (k : ℝ))⁻¹ := by
  let a : C(unitInterval, ℝ) :=
    ⟨fun u => (2 * ((j.1 + 1 : ℕ) : ℝ) - (u : ℝ)) * π / k, by fun_prop⟩
  rw [windingNumber_eq_of_exp_lift a (fun _ => rfl)]
  change ((2 * ((j.1 + 1 : ℕ) : ℝ) - 1) * π / k -
    (2 * ((j.1 + 1 : ℕ) : ℝ) - 0) * π / k) / (2 * π) = _
  field_simp [Nat.cast_ne_zero.mpr hk.ne', pi_ne_zero]
  ring
/-- The backtrack meets a vertex of a Section 5 drawing only at its initial parameter. -/
theorem terminalCuffBacktrackCurve_mem_vertices_iff {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (j : Fin k) (t : unitInterval) :
    terminalCuffBacktrackCurve k j t ∈ G.V ↔ t = 0 := by
  constructor
  · intro ht
    have hbd : terminalCuffBacktrackCurve k j t ∈ bd ClosedCylinder := by
      rw [bd_closedCylinder]
      exact Or.inr rfl
    have hp : terminalCuffBacktrackCurve k j t ∈ cylinderM1 k ∪ cylinderM2 k :=
      hG.2.2 ▸ ⟨ht, hbd⟩
    rcases hp with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hh : (1 : ℝ) = 2 := congrArg (fun p : ClosedCylinder => p.1.1) hi
      norm_num at hh
    · have he := congrArg (fun p : ClosedCylinder => p.1.2) hi
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
      have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hG.1.ne'
      have hh := congrArg (fun z : ℝ => z * ((k : ℝ) / π)) hm
      have heq : (t : ℝ) = 2 * (((j.1 : ℤ) - (i.1 : ℤ) + m * (k : ℤ) : ℤ) : ℝ) := by
        field_simp [hkne, pi_ne_zero] at hh
        push_cast at hh ⊢
        nlinarith only [hh]
      have hint : (((j.1 : ℤ) - (i.1 : ℤ) + m * (k : ℤ) : ℤ) : ℝ) = 0 := by
        have h0 := t.2.1
        have h1 := t.2.2
        have hz0 : 0 ≤ (j.1 : ℤ) - (i.1 : ℤ) + m * (k : ℤ) := by
          exact_mod_cast (show (0 : ℝ) ≤ (((j.1 : ℤ) - (i.1 : ℤ) + m * (k : ℤ) : ℤ) : ℝ) by linarith only [h0, heq])
        have hz1 : (j.1 : ℤ) - (i.1 : ℤ) + m * (k : ℤ) ≤ 0 := by
          have hlt : (((j.1 : ℤ) - (i.1 : ℤ) + m * (k : ℤ) : ℤ) : ℝ) < 1 := by
            linarith only [h1, heq]
          have : (j.1 : ℤ) - (i.1 : ℤ) + m * (k : ℤ) < 1 := by exact_mod_cast hlt
          omega
        exact_mod_cast le_antisymm hz1 hz0
      apply Subtype.ext
      change (t : ℝ) = 0
      rw [heq, hint, mul_zero]
  · rintro rfl
    have h0 : terminalCuffBacktrackCurve k j 0 = cylinderM2Point k j := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      change Circle.exp ((2 * ((j.1 + 1 : ℕ) : ℝ) - (0 : ℝ)) * π / k) =
        Circle.exp (2 * ((j.1 + 1 : ℕ) : ℝ) * π / k)
      rw [sub_zero]
    rw [h0]
    have hmem : cylinderM2Point k j ∈ cylinderM1 k ∪ cylinderM2 k := Or.inr ⟨j, rfl⟩
    have hv : cylinderM2Point k j ∈ G.V ∩ bd ClosedCylinder := hG.2.2.symm ▸ hmem
    exact hv.1
/-- The backtrack ends at the preceding dual outer-cuff point. -/
theorem terminalCuffBacktrackCurve_one {k : ℕ} (hk : 0 < k) (j : Fin k) :
    terminalCuffBacktrackCurve k j 1 = cylinderN2Point k (finPredCycle j) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    by_cases hj : j.1 = 0
    · simp only [finPredCycle, hj, ↓reduceDIte]
      change Circle.exp ((2 * ((0 + 1 : ℕ) : ℝ) - (1 : ℝ)) * π / k) =
        Circle.exp ((2 * ((k - 1 + 1 : ℕ) : ℝ) + 1) * π / k)
      have hkm : k - 1 + 1 = k := Nat.sub_add_cancel hk
      rw [hkm]
      have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
      have he : (2 * (k : ℝ) + 1) * π / k = π / k + 2 * π := by
        field_simp [hkne]
        ring
      rw [he, Circle.exp_add_two_pi]
      congr 1
      norm_num
    · simp only [finPredCycle, hj, ↓reduceDIte]
      have hjm : j.1 - 1 + 1 = j.1 := Nat.sub_add_cancel (Nat.pos_of_ne_zero hj)
      change Circle.exp ((2 * ((j.1 + 1 : ℕ) : ℝ) - (1 : ℝ)) * π / k) =
        Circle.exp ((2 * ((j.1 - 1 + 1 : ℕ) : ℝ) + 1) * π / k)
      rw [hjm]
      congr 1
      push_cast
      ring
end GraphMinor.GM06
