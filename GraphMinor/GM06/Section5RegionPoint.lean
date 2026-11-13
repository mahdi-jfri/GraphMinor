module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The boundary point defining a linkage region

In VI Section 5, page 128, Rᵢ is the region containing the dual point
between sᵢ and sᵢ₊₁. Its angle is an odd multiple of π/k, whereas the
prescribed vertices have even multiples. Equality modulo 2π would
make an odd integer even. Properness then puts this point outside G,
so it belongs to the stated region and linkage strip.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

private theorem exp_odd_grid_ne_even {k : ℕ} (hk : 0 < k) (a b : ℤ) :
    Circle.exp ((2 * (a : ℝ) + 1) * π / k) ≠ Circle.exp (2 * (b : ℝ) * π / k) := by
  intro heq
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hh := congrArg (fun x : ℝ => x * ((k : ℝ) / π)) hm
  have hl : ((2 * (a : ℝ) + 1) * π / k) * ((k : ℝ) / π) = 2 * a + 1 := by
    field_simp [hkne, pi_ne_zero]
  have hr : (2 * (b : ℝ) * π / k + (m : ℝ) * (2 * π)) * ((k : ℝ) / π) =
      2 * ((b : ℝ) + (m : ℝ) * (k : ℝ)) := by
    field_simp [hkne, pi_ne_zero]
  rw [hl, hr] at hh
  have hz : 2 * a + 1 = 2 * (b + m * (k : ℤ)) := by exact_mod_cast hh
  omega

/-- A dual point on the first cuff is not one of the prescribed
boundary vertices of a Section 5 drawing. -/
theorem cylinderN1Point_not_mem_prescribed_vertices
    {k : ℕ} (hk : 0 < k) (i : Fin k) :
    cylinderN1Point k i ∉ cylinderM1 k ∪ cylinderM2 k := by
  rintro (⟨j, hj⟩ | ⟨j, hj⟩)
  · have he : Circle.exp ((2 * ((i.1 + 1 : ℕ) : ℝ) + 1) * π / k) =
        Circle.exp (2 * ((j.1 + 1 : ℕ) : ℝ) * π / k) :=
      congrArg (fun p : ClosedCylinder => p.1.2) hj.symm
    exact exp_odd_grid_ne_even hk (i.1 + 1) (j.1 + 1) (by exact_mod_cast he)
  · have hr : (2 : ℝ) = 1 := congrArg (fun p : ClosedCylinder => p.1.1) hj
    norm_num at hr

/-- The dual point defining Rᵢ lies outside the drawing, by properness
and the prescribed boundary vertices. -/
theorem cylinderN1Point_not_mem_U
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    cylinderN1Point k i ∉ G.U := by
  intro hx
  have hxbd : cylinderN1Point k i ∈ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    exact Or.inl rfl
  have hxV : cylinderN1Point k i ∈ G.V := hG.2.1 ⟨hxbd, hx⟩
  exact cylinderN1Point_not_mem_prescribed_vertices hG.1 i (hG.2.2 ▸ ⟨hxV, hxbd⟩)

/-- A dual point on the outer cuff is not a prescribed boundary vertex. -/
theorem cylinderN2Point_not_mem_prescribed_vertices
    {k : ℕ} (hk : 0 < k) (i : Fin k) :
    cylinderN2Point k i ∉ cylinderM1 k ∪ cylinderM2 k := by
  rintro (⟨j, hj⟩ | ⟨j, hj⟩)
  · have hr : (1 : ℝ) = 2 := congrArg (fun p : ClosedCylinder => p.1.1) hj
    norm_num at hr
  · have he : Circle.exp ((2 * ((i.1 + 1 : ℕ) : ℝ) + 1) * π / k) =
        Circle.exp (2 * ((j.1 + 1 : ℕ) : ℝ) * π / k) :=
      congrArg (fun p : ClosedCylinder => p.1.2) hj.symm
    exact exp_odd_grid_ne_even hk (i.1 + 1) (j.1 + 1) (by exact_mod_cast he)

/-- The outer endpoint of a helix lies outside the drawing, by
properness and the prescribed boundary vertices of VI Section 5. -/
theorem cylinderN2Point_not_mem_U
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    cylinderN2Point k i ∉ G.U := by
  intro hx
  have hxbd : cylinderN2Point k i ∈ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    exact Or.inr rfl
  have hxV : cylinderN2Point k i ∈ G.V := hG.2.1 ⟨hxbd, hx⟩
  exact cylinderN2Point_not_mem_prescribed_vertices hG.1 i (hG.2.2 ▸ ⟨hxV, hxbd⟩)

/-- The dual boundary point belongs to its region Rᵢ. -/
theorem cylinderN1Point_mem_region
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    cylinderN1Point k i ∈ cylinderRegion k G i :=
  mem_connectedComponentIn ⟨mem_univ _, cylinderN1Point_not_mem_U hG i⟩

/-- Rᵢ is a region of G in the sense of the drawing definition. -/
theorem cylinderRegion_mem_regions
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    cylinderRegion k G i ∈ G.R :=
  ⟨cylinderN1Point k i, ⟨mem_univ _, cylinderN1Point_not_mem_U hG i⟩, rfl⟩

/-- The region Rᵢ lies in the corresponding linkage strip Σᵢ. -/
theorem cylinderRegion_subset_strip
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k) :
    cylinderRegion k G i ⊆ cylinderStrip L i := by
  apply connectedComponentIn_mono
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro hxL
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hxL
  exact hx.2 ((L.isSubdrawing j).2 hxj)

/-- The dual boundary point belongs to its linkage strip Σᵢ. -/
theorem cylinderN1Point_mem_strip
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    cylinderN1Point k i ∈ cylinderStrip L i :=
  cylinderRegion_subset_strip L i (cylinderN1Point_mem_region hG i)

/-- Both the region Rᵢ and the linkage strip Σᵢ are nonempty. -/
theorem cylinderRegion_strip_nonempty
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    (cylinderRegion k G i).Nonempty ∧ (cylinderStrip L i).Nonempty :=
  ⟨⟨_, cylinderN1Point_mem_region hG i⟩, ⟨_, cylinderN1Point_mem_strip L hG i⟩⟩

end GraphMinor.GM06
