module

public import GraphMinor.GM06.Section5CurveCount
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4Winding

/-!
# The cuff curve added in claim (1) of VI (5.5)

Move backwards through one full initial cuff gap. The curve joins
the following dual point to the preceding one and crosses the
initial vertex once. Its winding is −1/k and its vertex count is
one. Thus prepending it leaves the helix potential unchanged.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface
/-- The full-gap initial-cuff curve in claim (1) of VI (5.5), page 131:
it moves from the following dual point to the preceding dual point,
crossing the initial vertex once in the decreasing angular direction. -/
noncomputable def initialCuffBacktrackCurve (k : ℕ) (i : Fin k) : Curve ClosedCylinder :=
  ⟨fun t => cylinderPoint 1 (by simp)
    ((2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - 2 * (t : ℝ)) * π / k),
    by dsimp [cylinderPoint]; fun_prop⟩
/-- The full-gap cuff curve starts at the following dual point. -/
theorem initialCuffBacktrackCurve_zero {k : ℕ} (i : Fin k) :
    initialCuffBacktrackCurve k i 0 = cylinderN1Point k i := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    congr 1
    change (2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - 2 * (0 : ℝ)) * π / k =
      (2 * ((i.1 + 1 : ℕ) : ℝ) + 1) * π / k
    ring
/-- At its midpoint the full-gap cuff curve meets the initial vertex. -/
theorem initialCuffBacktrackCurve_mid {k : ℕ} (i : Fin k) :
    initialCuffBacktrackCurve k i (leftHalfTime 1) = cylinderM1Point k i := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    congr 1
    change (2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - 2 * (1 / 2 : ℝ)) * π / k = _
    ring
/-- The full-gap cuff curve ends at the preceding dual point. -/
theorem initialCuffBacktrackCurve_one {k : ℕ} (hk : 0 < k) (i : Fin k) :
    initialCuffBacktrackCurve k i 1 = cylinderN1Point k (finPredCycle i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    by_cases hi : i.1 = 0
    · simp only [finPredCycle, hi, ↓reduceDIte]
      change Circle.exp ((2 * ((0 + 1 : ℕ) : ℝ) + 1 - 2 * (1 : ℝ)) * π / k) =
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
    · simp only [finPredCycle, hi, ↓reduceDIte]
      have him : i.1 - 1 + 1 = i.1 := Nat.sub_add_cancel (Nat.pos_of_ne_zero hi)
      change Circle.exp ((2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - 2 * (1 : ℝ)) * π / k) =
        Circle.exp ((2 * ((i.1 - 1 + 1 : ℕ) : ℝ) + 1) * π / k)
      rw [him]
      congr 1
      push_cast
      ring
/-- The full-gap cuff curve in VI (5.5), claim (1), has winding −1/k. -/
theorem windingNumber_initialCuffBacktrackCurve {k : ℕ} (hk : 0 < k) (i : Fin k) :
    windingNumber (initialCuffBacktrackCurve k i) = -(k : ℝ)⁻¹ := by
  let a : C(unitInterval, ℝ) :=
    ⟨fun t => (2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - 2 * (t : ℝ)) * π / k, by fun_prop⟩
  rw [windingNumber_eq_of_exp_lift a (fun _ => rfl)]
  change ((2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - 2 * (1 : ℝ)) * π / k -
    (2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - 2 * (0 : ℝ)) * π / k) / (2 * π) = _
  field_simp [Nat.cast_ne_zero.mpr hk.ne', pi_ne_zero]
  ring
/-- The full-gap cuff curve meets a prescribed vertex exactly at its midpoint. -/
private theorem initialCuffBacktrackCurve_mem_vertices_iff {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) (t : unitInterval) :
    initialCuffBacktrackCurve k i t ∈ G.V ↔ t = leftHalfTime 1 := by
  constructor
  · intro ht
    have hbd : initialCuffBacktrackCurve k i t ∈ bd ClosedCylinder := by
      rw [bd_closedCylinder]
      exact Or.inl rfl
    have hp : initialCuffBacktrackCurve k i t ∈ cylinderM1 k ∪ cylinderM2 k := hG.2.2 ▸ ⟨ht, hbd⟩
    rcases hp with ⟨j, hj⟩ | ⟨j, hj⟩
    · have he := congrArg (fun p : ClosedCylinder => p.1.2) hj
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
      have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hG.1.ne'
      have hh := congrArg (fun z : ℝ => z * ((k : ℝ) / π)) hm
      field_simp [hkne, pi_ne_zero] at hh
      push_cast at hh
      let n : ℤ := (i.1 : ℤ) - (j.1 : ℤ) + m * (k : ℤ)
      have heq : (t : ℝ) = (n : ℝ) + 1 / 2 := by
        dsimp [n]
        push_cast
        nlinarith only [hh]
      have hlo : (-1 : ℝ) < (n : ℝ) := by linarith only [heq, t.2.1]
      have hhi : (n : ℝ) < 1 := by linarith only [heq, t.2.2]
      have hloZ : (-1 : ℤ) < n := by exact_mod_cast hlo
      have hhiZ : n < 1 := by exact_mod_cast hhi
      have hn : n = 0 := by omega
      apply Subtype.ext
      change (t : ℝ) = 1 / 2
      rw [heq, hn]
      norm_num
    · have hh : (2 : ℝ) = 1 := congrArg (fun p : ClosedCylinder => p.1.1) hj
      norm_num at hh
  · rintro rfl
    rw [initialCuffBacktrackCurve_mid]
    have hp : cylinderM1Point k i ∈ cylinderM1 k ∪ cylinderM2 k := Or.inl ⟨i, rfl⟩
    exact (show cylinderM1Point k i ∈ G.V ∩ bd ClosedCylinder from hG.2.2.symm ▸ hp).1
/-- The full-gap cuff curve is normal and has one vertex contact,
as used in claim (1) of VI (5.5), page 131. -/
theorem initialCuffBacktrackCurve_props {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    IsNormalCurve G (initialCuffBacktrackCurve k i) ∧
      (curveVertexHits G (initialCuffBacktrackCurve k i)).Finite ∧
        curveL G (initialCuffBacktrackCurve k i) = 1 := by
  have hset : curveVertexHits G (initialCuffBacktrackCurve k i) = {leftHalfTime 1} := by
    ext t
    exact initialCuffBacktrackCurve_mem_vertices_iff hG i t
  refine ⟨?_, hset ▸ finite_singleton _, ?_⟩
  · rintro x ⟨⟨t, rfl⟩, htG⟩
    apply hG.2.1
    refine ⟨?_, htG⟩
    rw [bd_closedCylinder]
    exact Or.inl rfl
  · rw [curveL, hset, ncard_singleton]
/-- The half-gap cuff prefix h in VI (5.5), page 131, moves from the
following dual point backwards to the initial vertex. -/
noncomputable def initialCuffHalfBacktrackCurve (k : ℕ) (i : Fin k) : Curve ClosedCylinder :=
  ⟨fun t => cylinderPoint 1 (by simp)
    ((2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - (t : ℝ)) * π / k),
    by dsimp [cylinderPoint]; fun_prop⟩

/-- The half-gap prefix starts at the following dual point. -/
theorem initialCuffHalfBacktrackCurve_zero {k : ℕ} (i : Fin k) :
    initialCuffHalfBacktrackCurve k i 0 = cylinderN1Point k i := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    congr 1
    norm_num

/-- The half-gap prefix ends at the chosen initial vertex. -/
theorem initialCuffHalfBacktrackCurve_one {k : ℕ} (i : Fin k) :
    initialCuffHalfBacktrackCurve k i 1 = cylinderM1Point k i := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    congr 1
    norm_num

/-- The half-gap prefix contributes winding −1/(2k), as in VI (5.5), page 131. -/
theorem windingNumber_initialCuffHalfBacktrackCurve {k : ℕ} (hk : 0 < k) (i : Fin k) :
    windingNumber (initialCuffHalfBacktrackCurve k i) = -(2 * (k : ℝ))⁻¹ := by
  let a : C(unitInterval, ℝ) :=
    ⟨fun t => (2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - (t : ℝ)) * π / k, by fun_prop⟩
  rw [windingNumber_eq_of_exp_lift a (fun _ => rfl)]
  change ((2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - (1 : ℝ)) * π / k -
    (2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - (0 : ℝ)) * π / k) / (2 * π) = _
  field_simp [Nat.cast_ne_zero.mpr hk.ne', pi_ne_zero]
  ring

/-- The half-gap prefix is normal and meets a drawing vertex only
at its last parameter, as used in VI (5.5), page 131. -/
theorem initialCuffHalfBacktrackCurve_props {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    IsNormalCurve G (initialCuffHalfBacktrackCurve k i) ∧
      curveVertexHits G (initialCuffHalfBacktrackCurve k i) = {1} := by
  have heq (t : unitInterval) : initialCuffHalfBacktrackCurve k i t =
      initialCuffBacktrackCurve k i (leftHalfTime t) := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Circle.exp _ = Circle.exp _
      congr 1
      dsimp [leftHalfTime]
      ring
  refine ⟨?_, ?_⟩
  · rintro x ⟨⟨t, rfl⟩, htG⟩
    exact (initialCuffBacktrackCurve_props hG i).1
      ⟨⟨leftHalfTime t, (heq t).symm⟩, htG⟩
  · ext t
    change initialCuffHalfBacktrackCurve k i t ∈ G.V ↔ t = 1
    rw [heq, initialCuffBacktrackCurve_mem_vertices_iff hG]
    exact leftHalfTime_injective.eq_iff

/-- The explicit half-gap formula from VI (5.5), page 131, exposed
as an equation for constructing its indexed cover lift. -/
theorem initialCuffHalfBacktrackCurve_apply (k : ℕ) (i : Fin k) (t : unitInterval) :
    initialCuffHalfBacktrackCurve k i t = cylinderPoint 1 (by simp)
      ((2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - (t : ℝ)) * π / k) := by
  rw [initialCuffHalfBacktrackCurve]
  rfl


/-- Every point of the half-gap prefix lies on the initial cuff. -/
theorem initialCuffHalfBacktrackCurve_mem_cuff1 {k : ℕ} (i : Fin k) (t : unitInterval) :
    initialCuffHalfBacktrackCurve k i t ∈ cylinderCuff1 := by
  rw [initialCuffHalfBacktrackCurve_apply]
  rfl

end GraphMinor.GM06
