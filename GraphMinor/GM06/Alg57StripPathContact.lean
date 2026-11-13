module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5
import GraphMinor.GM06.Section5StripDisc
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5StripProjection
import GraphMinor.GM06.Section5StripCuffs
import GraphMinor.GM06.Section5StripEnds
import GraphMinor.GM06.Section5LiftedPaths
import GraphMinor.GM06.Section5StripBoundary
import GraphMinor.GM06.Section5RegionPoint

/-!
# Which linkage paths meet a closed strip

For `k ≥ 2` the candidate graph of Reduction 4 (Section 12 of our proof of VI (5.7), outlined in
`Alg57Algorithm.lean`) removes the opposite boundary `Pᵢ₊₁` only. Our drawing form
(`IsReduction4CandidateVertex`) removes all other linkage paths. The two agree because the closed
strip `closure Σᵢ` meets no linkage path other than `Pᵢ` and `Pᵢ₊₁`
(`mem_path_of_mem_closure_strip`).

The proof lifts a point of the closed strip to the strip disc `D` between consecutive lifts.
A point of the open disc projects into `Σᵢ`, which misses all paths. A point of a lifted path is on
`Pᵢ` or `Pᵢ₊₁`. A point on a cuff line lies in the angular interval between the two lifted ends;
if it is on `Pⱼ` it is the end of `Pⱼ` on that cuff, and the ends of the lifts of all paths on a
cuff are spaced `2π/k` apart. So it is the end of one of the two bounding lifts.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

/-- Ends spaced `2π/k` apart: an angle between two consecutive ends, and equal on the circle to
the end of index `n`, is the end of index `m` or `m + 1`, up to a multiple of `k`. -/
theorem exists_index_of_circle_exp_eq {k : ℕ} (hk : 0 < k) {c y : ℝ} {m n : ℤ}
    (hy : 2 * (m : ℝ) * π / k + c ≤ y ∧ y ≤ 2 * ((m + 1 : ℤ) : ℝ) * π / k + c)
    (hexp : Circle.exp y = Circle.exp (2 * (n : ℝ) * π / k + c)) :
    ∃ q : ℤ, n + (k : ℤ) * q = m ∨ n + (k : ℤ) * q = m + 1 := by
  obtain ⟨q, hq⟩ := Circle.exp_eq_exp.mp hexp
  refine ⟨q, ?_⟩
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hval : y - c = 2 * (((n + (k : ℤ) * q : ℤ) : ℝ)) * π / k := by
    rw [hq]; push_cast; field_simp; ring
  have h1 : (m : ℝ) ≤ ((n + (k : ℤ) * q : ℤ) : ℝ) := by
    have : 2 * (m : ℝ) * π / k ≤ 2 * (((n + (k : ℤ) * q : ℤ) : ℝ)) * π / k := by
      linarith [hy.1]
    rw [div_le_div_iff_of_pos_right hkpos] at this
    nlinarith [pi_pos]
  have h2 : (((n + (k : ℤ) * q : ℤ) : ℝ)) ≤ ((m + 1 : ℤ) : ℝ) := by
    have : 2 * (((n + (k : ℤ) * q : ℤ) : ℝ)) * π / k ≤ 2 * ((m + 1 : ℤ) : ℝ) * π / k := by
      linarith [hy.2]
    rw [div_le_div_iff_of_pos_right hkpos] at this
    nlinarith [pi_pos]
  have h1' : m ≤ n + (k : ℤ) * q := by exact_mod_cast h1
  have h2' : n + (k : ℤ) * q ≤ m + 1 := by exact_mod_cast h2
  omega

/-- The same, read through the path index `modIdx`. -/
theorem modIdx_eq_or_of_circle_exp_eq {k : ℕ} (hk : 0 < k) {c y : ℝ} {m n : ℤ}
    (hy : 2 * (m : ℝ) * π / k + c ≤ y ∧ y ≤ 2 * ((m + 1 : ℤ) : ℝ) * π / k + c)
    (hexp : Circle.exp y = Circle.exp (2 * (n : ℝ) * π / k + c)) :
    modIdx k hk n = modIdx k hk m ∨ modIdx k hk n = modIdx k hk (m + 1) := by
  obtain ⟨q, hq | hq⟩ := exists_index_of_circle_exp_eq hk hy hexp
  · left; rw [← modIdx_add_mul hk n q, hq]
  · right; rw [← modIdx_add_mul hk n q, hq]

/-- **Contacts of a closed strip with the linkage** (`k ≥ 2`). A point of `closure Σᵢ` on a
linkage path `Pⱼ` has `j = i` or `j = i + 1`. -/
theorem mem_path_of_mem_closure_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i j : Fin k)
    {x : ClosedCylinder} (hx : x ∈ closure (cylinderStrip L i))
    (hxj : x ∈ (L.pathDrawing j).U) : j = i ∨ j = finSuccCycle i := by
  have hk := hG.1
  let m : ℤ := (i.val : ℤ) + 1
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ m
  have him := image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip
  rw [← him] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have hp12 := hstrip hp
  have hfst := radialCylinderProjection_fst hp12
  have hmi : modIdx k hk m = i := modIdx_natCast_succ hk i
  have hmi1 : modIdx k hk (m + 1) = finSuccCycle i := modIdx_natCast_succ_add_one hk i
  -- the point as a point of the lifted path of `Pⱼ`
  obtain ⟨t, ht⟩ : radialCylinderProjection p ∈ range (L.curve j) :=
    (L.curve_parametrizes j).2.1 ▸ hxj
  have hj := modIdx_natCast_succ hk j
  have hΓ := radialCylinderProjection_liftedLinkageCurve hk L ((j.val : ℤ) + 1) t
  rw [hj, ht] at hΓ
  have hjp := liftedLinkageCurve_props_raw hk L ((j.val : ℤ) + 1)
  have hrad : (liftedLinkageCurve hk L ((j.val : ℤ) + 1) t).1 = p.1 := by
    rw [liftedLinkageCurve_fst, hj, ht, hfst]
  have hang : Circle.exp p.2 = Circle.exp (liftedLinkageCurve hk L ((j.val : ℤ) + 1) t).2 := by
    have h := hjp.2.2.2.2.2 t
    rw [hj, ht] at h
    exact h.symm
  have hmid := fun s (hs : s ∈ Ioo (0 : unitInterval) 1) =>
    liftedLinkageCurve_interior_radius L hG ((j.val : ℤ) + 1) hs
  by_cases hpint : p ∈ discBd D
  · rw [hBd] at hpint
    rcases hpint with ((hpb | hpb) | hpb) | hpb
    · obtain ⟨s, rfl⟩ := hpb
      left
      by_contra hne
      have hmem : radialCylinderProjection (liftedLinkageCurve hk L m s) ∈ (L.pathDrawing i).U := by
        rw [radialCylinderProjection_liftedLinkageCurve, hmi]
        exact (L.curve_parametrizes i).2.1 ▸ mem_range_self s
      exact disjoint_left.mp (L.pairwise_disjoint hne) hxj hmem
    · obtain ⟨s, rfl⟩ := hpb
      right
      by_contra hne
      have hmem : radialCylinderProjection (liftedLinkageCurve hk L (m + 1) s) ∈
          (L.pathDrawing (finSuccCycle i)).U := by
        rw [radialCylinderProjection_liftedLinkageCurve, hmi1]
        exact (L.curve_parametrizes _).2.1 ▸ mem_range_self s
      exact disjoint_left.mp (L.pairwise_disjoint hne) hxj hmem
    · have hp1 : p.1 = 1 := mem_singleton_iff.mp hpb.1
      have ht0 : t = 0 := eq_zero_of_strip_radius_one hjp.2.2.1 hmid (hrad.trans hp1)
      rw [ht0, hjp.2.2.2.1] at hang
      have hy := hpb.2
      rw [(liftedLinkageCurve_props_raw hk L m).2.2.2.1,
        (liftedLinkageCurve_props_raw hk L (m + 1)).2.2.2.1] at hy
      have hor := modIdx_eq_or_of_circle_exp_eq (c := 0) hk
        (by simpa only [add_zero, mem_Icc] using hy) (by simpa only [add_zero] using hang)
      rw [hj, hmi, hmi1] at hor
      exact hor
    · have hp2 : p.1 = 2 := mem_singleton_iff.mp hpb.1
      have ht1 : t = 1 := eq_one_of_strip_radius_two hjp.2.1 hmid (hrad.trans hp2)
      rw [ht1, hjp.2.2.2.2.1, hj, hθ j] at hang
      have hy := hpb.2
      rw [(liftedLinkageCurve_props_raw hk L m).2.2.2.2.1,
        (liftedLinkageCurve_props_raw hk L (m + 1)).2.2.2.2.1, hmi, hmi1, hθ i,
        hθ (finSuccCycle i)] at hy
      have hor := modIdx_eq_or_of_circle_exp_eq (c := 2 * π * θ) hk hy hang
      rw [hj, hmi, hmi1] at hor
      exact hor
  · exfalso
    have hin : radialCylinderProjection p ∈ cylinderStrip L i :=
      stripDiscInterior_projection_mem_strip L hG hθ i hD hBd hstrip ⟨hp, hpint⟩ hfst rfl
    have hsub := connectedComponentIn_subset _ _ hin
    exact hsub.2 (mem_iUnion.mpr ⟨j, hxj⟩)

/-- For `k ≥ 2`, a point of `closure Σᵢ` off `Pᵢ₊₁` lies on no linkage path other than `Pᵢ`. -/
theorem not_mem_other_paths_iff_of_mem_closure_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k)
    {x : ClosedCylinder} (hx : x ∈ closure (cylinderStrip L i)) :
    (∀ j, j ≠ i → x ∉ (L.pathDrawing j).U) ↔ x ∉ (L.pathDrawing (finSuccCycle i)).U := by
  have hne : finSuccCycle i ≠ i := by
    intro h
    have := congrArg Fin.val h
    by_cases hi : i.val + 1 < k
    · simp [finSuccCycle, hi] at this
    · simp [finSuccCycle, hi] at this; omega
  constructor
  · exact fun h => h _ hne
  · intro h j hj hxj
    rcases mem_path_of_mem_closure_strip L hG hθ i j hx hxj with rfl | rfl
    · exact hj rfl
    · exact h hxj

/-- The same for a point of `closure Rᵢ`. -/
theorem not_mem_other_paths_iff_of_mem_closure_region
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k)
    {x : ClosedCylinder} (hx : x ∈ closure (cylinderRegion k G i)) :
    (∀ j, j ≠ i → x ∉ (L.pathDrawing j).U) ↔ x ∉ (L.pathDrawing (finSuccCycle i)).U :=
  not_mem_other_paths_iff_of_mem_closure_strip L hk hG hθ i
    (closure_mono (cylinderRegion_subset_strip L i) hx)

end GraphMinor.GM06
