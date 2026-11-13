module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5StripCuffs
import GraphMinor.GM06.Section5RegionPoint

/-!
# Distinct linkage strips are disjoint

For VI (5.1), page 129, two strips are components of the same path
complement. If they met, their closures would agree. But the initial
cuff part of each closure is its own closed angular gap, and only the
corresponding dual point is in that gap. Thus distinct indices give
distinct components. This separates the interiors of the paths Qᵢ.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

/-- A dual initial point in a closed initial gap has that gap's index. -/
theorem index_eq_of_dual_point_mem_initial_gap
    {k : ℕ} (hk : 0 < k) {i j : Fin k}
    (hmem : cylinderN1Point k i ∈ range (initialCuffGapCurve k j)) : i = j := by
  obtain ⟨u, hu⟩ := hmem
  have he : Circle.exp (2 * (((j.val + 1 : ℕ) : ℝ) + (u : ℝ)) * π / k) =
      Circle.exp ((2 * ((i.val + 1 : ℕ) : ℝ) + 1) * π / k) :=
    congrArg (fun p : ClosedCylinder => p.1.2) hu
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hh := congrArg (fun a : ℝ => a * ((k : ℝ) / (2 * π))) hm
  have hl : (2 * (((j.val + 1 : ℕ) : ℝ) + (u : ℝ)) * π / k) *
      ((k : ℝ) / (2 * π)) = ((j.val + 1 : ℕ) : ℝ) + (u : ℝ) := by
    field_simp [hkne, pi_ne_zero]
  have hr : (((2 * ((i.val + 1 : ℕ) : ℝ) + 1) * π / k) + (m : ℝ) * (2 * π)) *
      ((k : ℝ) / (2 * π)) = ((i.val + 1 : ℕ) : ℝ) + 1 / 2 + (m : ℝ) * k := by
    field_simp [hkne, pi_ne_zero]
  rw [hl, hr] at hh
  let z : ℤ := (j.val : ℤ) - i.val - m * k
  have huz : (u : ℝ) = 1 / 2 - (z : ℝ) := by
    dsimp only [z]
    push_cast at hh ⊢
    linarith only [hh]
  have hzlo : (-1 : ℝ) < (z : ℝ) := by linarith only [huz, u.2.2]
  have hzhi : (z : ℝ) < 1 := by linarith only [huz, u.2.1]
  have hzloZ : (-1 : ℤ) < z := by exact_mod_cast hzlo
  have hzhiZ : z < (1 : ℤ) := by exact_mod_cast hzhi
  have hz : z = 0 := by omega
  have hidx : (j.val : ℤ) = (i.val : ℤ) + m * (k : ℤ) := by
    dsimp only [z] at hz
    omega
  have himod : (i.val : ℤ) % (k : ℤ) = i.val :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr i.isLt)
  have hjmod : (j.val : ℤ) % (k : ℤ) = j.val :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr j.isLt)
  have hmod := congrArg (fun a : ℤ => a % (k : ℤ)) hidx
  simp only [Int.add_emod, Int.mul_emod, Int.emod_self, Int.zero_emod,
    mul_zero, add_zero, himod, hjmod] at hmod
  apply Fin.ext
  exact_mod_cast hmod.symm

/-- The distinct components Σᵢ used in VI (5.1), page 129, are disjoint.
Their initial cuff gaps distinguish the component indices. -/
theorem disjoint_cylinderStrip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) {i j : Fin k} (hne : i ≠ j) :
    Disjoint (cylinderStrip L i) (cylinderStrip L j) := by
  apply disjoint_left.mpr
  intro x hxi hxj
  have hij : cylinderStrip L i = cylinderStrip L j :=
    (connectedComponentIn_eq hxi).trans (connectedComponentIn_eq hxj).symm
  have hNi : cylinderN1Point k i ∈ cylinderStrip L j :=
    hij ▸ cylinderN1Point_mem_strip L hG i
  have hgap := closure_strip_inter_initial_cuff_subset_gap L hG hθ j
    ⟨subset_closure hNi, rfl⟩
  exact hne (index_eq_of_dual_point_mem_initial_gap hG.1 hgap)

end GraphMinor.GM06
