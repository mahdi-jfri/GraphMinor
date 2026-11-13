module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5RegionPoint
import Mathlib.Topology.Order.Compact

/-!
# The boundary gap belongs to Rᵢ

The open boundary arc from sᵢ to sᵢ₊₁ contains the dual point defining
Rᵢ and no vertex of G. Properness makes the whole open arc disjoint
from G, so connectedness puts it in Rᵢ. Its two ends are consequently
incident with Rᵢ. This supplies the initial boundary incidences in the
proof of VI (5.1), page 129.
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface

/-- The inner-cuff curve from sᵢ to sᵢ₊₁, increasing the angle by
2π/k in the concrete cylinder model of VI Section 5, page 128. -/
@[expose] noncomputable def initialCuffGapCurve (k : ℕ) (i : Fin k) : Curve ClosedCylinder :=
  ⟨fun u => cylinderPoint 1 (by simp) (2 * (((i.1 + 1 : ℕ) : ℝ) + (u : ℝ)) * π / k),
    by dsimp [cylinderPoint]; fun_prop⟩

private theorem initialCuffGapCurve_zero {k : ℕ} (i : Fin k) :
    initialCuffGapCurve k i 0 = cylinderM1Point k i := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    congr 1
    simp

private theorem initialCuffGapCurve_one {k : ℕ} (hk : 0 < k) (i : Fin k) :
    initialCuffGapCurve k i 1 = cylinderM1Point k (finSuccCycle i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · by_cases hi : i.1 + 1 < k
    · change Circle.exp _ = Circle.exp _
      simp only [finSuccCycle, hi, ↓reduceDIte]
      congr 1
      push_cast
      ring
    · have hik : i.1 + 1 = k := Nat.le_antisymm (Nat.succ_le_of_lt i.2) (Nat.le_of_not_gt hi)
      have hiR : ((i.1 + 1 : ℕ) : ℝ) = k := by exact_mod_cast hik
      have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
      change Circle.exp _ = Circle.exp _
      simp only [finSuccCycle, hi, ↓reduceDIte]
      have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
      rw [hone]
      norm_num only [Nat.zero_add, Nat.cast_one]
      change Circle.exp (2 * (((i.1 + 1 : ℕ) : ℝ) + 1) * π / k) = Circle.exp (2 * π / k)
      rw [hiR, show 2 * ((k : ℝ) + 1) * π / k = 2 * π / k + 2 * π by
        field_simp [hkne]; ring, Circle.exp_add_two_pi]

/-- The open angular interval between consecutive initial vertices
contains none of the prescribed boundary vertices. -/
theorem initialCuffGapCurve_interior_not_prescribed
    {k : ℕ} (hk : 0 < k) (i : Fin k) {u : unitInterval} (hu : u ∈ Ioo 0 1) :
    initialCuffGapCurve k i u ∉ cylinderM1 k ∪ cylinderM2 k := by
  rintro (⟨j, hj⟩ | ⟨j, hj⟩)
  · have he : Circle.exp (2 * (((i.1 + 1 : ℕ) : ℝ) + (u : ℝ)) * π / k) =
        Circle.exp (2 * ((j.1 + 1 : ℕ) : ℝ) * π / k) :=
      congrArg (fun p : ClosedCylinder => p.1.2) hj.symm
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
    have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    have h2pi : (2 * π : ℝ) ≠ 0 := mul_ne_zero two_ne_zero pi_ne_zero
    have hh := congrArg (fun x : ℝ => x * ((k : ℝ) / (2 * π))) hm
    have hl : (2 * (((i.1 + 1 : ℕ) : ℝ) + (u : ℝ)) * π / k) *
        ((k : ℝ) / (2 * π)) = ((i.1 + 1 : ℕ) : ℝ) + (u : ℝ) := by
      field_simp [hkne, pi_ne_zero]
    have hr : (2 * ((j.1 + 1 : ℕ) : ℝ) * π / k + (m : ℝ) * (2 * π)) *
        ((k : ℝ) / (2 * π)) = ((j.1 + 1 : ℕ) : ℝ) + (m : ℝ) * k := by
      field_simp [hkne, pi_ne_zero]
    rw [hl, hr] at hh
    let z : ℤ := (j.1 : ℤ) - i.1 + m * k
    have huz : (u : ℝ) = (z : ℝ) := by
      dsimp [z]
      push_cast at hh ⊢
      linarith only [hh]
    have h0 : (0 : ℝ) < (u : ℝ) := hu.1
    have h1 : (u : ℝ) < 1 := hu.2
    rw [huz] at h0 h1
    have hz0 : (0 : ℤ) < z := by exact_mod_cast h0
    have hz1 : z < (1 : ℤ) := by exact_mod_cast h1
    omega
  · have hr : (2 : ℝ) = 1 := congrArg (fun p : ClosedCylinder => p.1.1) hj
    norm_num at hr

/-- The open boundary gap from sᵢ to sᵢ₊₁ lies in the region Rᵢ
specified on page 128 of Graph Minors VI. -/
theorem initialCuffGapCurve_props
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    let f := initialCuffGapCurve k i
    f 0 = cylinderM1Point k i ∧ f 1 = cylinderM1Point k (finSuccCycle i) ∧
      range f ⊆ cylinderCuff1 ∧ cylinderN1Point k i ∈ f '' Ioo 0 1 ∧
      f '' Ioo 0 1 ⊆ cylinderRegion k G i := by
  let f := initialCuffGapCurve k i
  let u : unitInterval := ⟨1 / 2, by norm_num⟩
  have hu : u ∈ Ioo (0 : unitInterval) 1 := by
    constructor
    · change (0 : ℝ) < 1 / 2
      norm_num
    · change (1 / 2 : ℝ) < 1
      norm_num
  have hmid : f u = cylinderN1Point k i := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Circle.exp _ = Circle.exp _
      congr 1
      dsimp [u]
      ring
  refine ⟨initialCuffGapCurve_zero i, initialCuffGapCurve_one hG.1 i, ?_, ⟨u, hu, hmid⟩, ?_⟩
  · rintro x ⟨t, rfl⟩
    rfl
  have hconn : IsPreconnected (f '' Ioo 0 1) :=
    isPreconnected_Ioo.image f f.continuous.continuousOn
  change f '' Ioo 0 1 ⊆ connectedComponentIn (univ \ G.U) (cylinderN1Point k i)
  apply hconn.subset_connectedComponentIn ⟨u, hu, hmid⟩
  rintro x ⟨v, hv, rfl⟩
  refine ⟨mem_univ _, ?_⟩
  intro hxG
  have hxbd : f v ∈ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    exact Or.inl rfl
  have hxV : f v ∈ G.V := hG.2.1 ⟨hxbd, hxG⟩
  exact initialCuffGapCurve_interior_not_prescribed hG.1 i hv (hG.2.2 ▸ ⟨hxV, hxbd⟩)

/-- The inner cuff gap has its two stated ends, contains the dual
point defining Rᵢ, and has its open part in Rᵢ. -/
theorem exists_boundary_gap_in_cuff
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    ∃ f : Curve ClosedCylinder, f 0 = cylinderM1Point k i ∧
      f 1 = cylinderM1Point k (finSuccCycle i) ∧
      range f ⊆ cylinderCuff1 ∧ cylinderN1Point k i ∈ f '' Ioo 0 1 ∧
      f '' Ioo 0 1 ⊆ cylinderRegion k G i :=
  ⟨initialCuffGapCurve k i, initialCuffGapCurve_props hG i⟩

/-- The open boundary gap from sᵢ to sᵢ₊₁ is contained in Rᵢ. -/
theorem exists_boundary_gap_in_cylinderRegion
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    ∃ f : Curve ClosedCylinder, f 0 = cylinderM1Point k i ∧
      f 1 = cylinderM1Point k (finSuccCycle i) ∧
      f '' Ioo 0 1 ⊆ cylinderRegion k G i := by
  obtain ⟨f, hf0, hf1, _, _, hf⟩ := exists_boundary_gap_in_cuff hG i
  exact ⟨f, hf0, hf1, hf⟩

/-- Both initial vertices bounding the gap are incident with Rᵢ,
as used at the start of VI (5.1), page 129. -/
theorem initial_vertices_mem_closure_cylinderRegion
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    cylinderM1Point k i ∈ closure (cylinderRegion k G i) ∧
      cylinderM1Point k (finSuccCycle i) ∈ closure (cylinderRegion k G i) := by
  obtain ⟨f, hf0, hf1, hf⟩ := exists_boundary_gap_in_cylinderRegion hG i
  have hcl : closure (Ioo (0 : unitInterval) 1) = univ := by
    rw [closure_Ioo (zero_ne_one : (0 : unitInterval) ≠ 1)]
    ext v
    exact iff_true_intro ⟨v.2.1, v.2.2⟩
  have him : range f ⊆ closure (cylinderRegion k G i) := by
    have h := image_closure_subset_closure_image (s := Ioo (0 : unitInterval) 1) f.continuous
    rw [hcl, image_univ] at h
    exact h.trans (closure_mono hf)
  exact ⟨hf0 ▸ him (mem_range_self 0), hf1 ▸ him (mem_range_self 1)⟩

end GraphMinor.GM06
