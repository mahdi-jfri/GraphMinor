module

public import GraphMinor.GM06.Section5SubpathCount
import GraphMinor.GM06.Section5CurveCount
import GraphMinor.GM06.Section4Winding
import GraphMinor.GM06.Section5HelixConcatenation

/-!
# Splitting the old helix at the two selected times

VI (5.5), page 131, cuts the helix at its last earlier vertex hit
and its last region visit. The three closed parameter intervals
cover all times. Their only overlaps are the two joining times.
Subtracting the joining vertex indicators from concatenation counts
therefore recovers the original finite count, including a constant
terminal piece whose endpoint is not a vertex.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

open Classical in
/-- Splitting a finite parameter set at one cut counts the joining
parameter twice exactly when it belongs to the set. -/
theorem ncard_split_at (A : Set unitInterval) (hA : A.Finite) (z : unitInterval) :
    (A ∩ Iic z).ncard + (A ∩ Ici z).ncard = A.ncard + (if z ∈ A then 1 else 0) := by
  have hUnion : (A ∩ Iic z) ∪ (A ∩ Ici z) = A := by
    ext t
    constructor
    · rintro (h | h) <;> exact h.1
    · intro ht
      rcases le_total t z with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩
  have hInter : (A ∩ Iic z) ∩ (A ∩ Ici z) = if z ∈ A then {z} else ∅ := by
    ext t
    by_cases hz : z ∈ A
    · rw [ite_eq_left hz]
      constructor
      · rintro ⟨⟨_, htz⟩, _, hzt⟩
        exact le_antisymm htz hzt
      · rintro rfl
        exact ⟨⟨hz, le_rfl⟩, hz, le_rfl⟩
    · rw [ite_eq_right hz]
      constructor
      · rintro ⟨⟨htA, htz⟩, _, hzt⟩
        have heq : t = z := le_antisymm htz hzt
        exact (hz (heq ▸ htA)).elim
      · exact False.elim
  have hc := ncard_union_add_ncard_inter (A ∩ Iic z) (A ∩ Ici z)
    (hA.inter_of_left _) (hA.inter_of_left _)
  rw [hUnion, hInter] at hc
  by_cases hz : z ∈ A <;> simp only [hz, ite_true, ite_false, ncard_singleton, ncard_empty] at hc ⊢
  · exact hc.symm
  · exact hc.symm

open Classical in
private theorem ncard_three_parts (A : Set unitInterval) (hA : A.Finite)
    {z₁ z₂ : unitInterval} (hz : z₁ ≤ z₂) :
    (A ∩ Iic z₁).ncard + (A ∩ Icc z₁ z₂).ncard + (A ∩ Ici z₂).ncard =
      A.ncard + (if z₁ ∈ A then 1 else 0) + (if z₂ ∈ A then 1 else 0) := by
  have h1 := ncard_split_at A hA z₁
  have h2 := ncard_split_at (A ∩ Ici z₁) (hA.inter_of_left _) z₂
  have hMid : (A ∩ Ici z₁) ∩ Iic z₂ = A ∩ Icc z₁ z₂ := by
    ext t
    exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  have hRight : (A ∩ Ici z₁) ∩ Ici z₂ = A ∩ Ici z₂ := by
    ext t
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hz.trans h.2⟩, h.2⟩⟩
  rw [hMid, hRight] at h2
  simp only [mem_inter_iff, mem_Ici, hz, and_true] at h2
  omega

/-- Cutting and concatenating a path at the two times of VI (5.5),
page 131, preserves its finite vertex count. A terminal constant
piece is allowed because the terminal point is not a vertex. -/
theorem curveL_three_subpaths
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {a b : S}
    (p : Path a b) (hp : (curveVertexHits G p.toContinuousMap).Finite)
    {z₁ z₂ : unitInterval} (hz₁ : 0 < z₁) (hz₂ : z₁ < z₂) (hb : b ∉ G.V) :
    let P := ((p.subpath 0 z₁).trans (p.subpath z₁ z₂)).trans (p.subpath z₂ 1)
    (curveVertexHits G P.toContinuousMap).Finite ∧ curveL G P.toContinuousMap = curveL G p.toContinuousMap := by
  classical
  dsimp only
  have h1 := curveL_subpath p hz₁.ne hp
  have h2 := curveL_subpath p hz₂.ne hp
  have hb' : p 1 ∉ G.V := by rw [Path.target]; exact hb
  have h3 := curveL_subpath_of_end_not_vertex p z₂ 1 hb' hp
  simp only [uIcc_of_le (show (0 : unitInterval) ≤ z₁ from bot_le)] at h1
  simp only [uIcc_of_le hz₂.le] at h2
  simp only [uIcc_of_le (show z₂ ≤ 1 from le_top)] at h3
  have hLeft : Icc (0 : unitInterval) z₁ = Iic z₁ := by
    ext t
    exact ⟨And.right, fun ht => ⟨bot_le, ht⟩⟩
  have hRight : Icc z₂ (1 : unitInterval) = Ici z₂ := by
    ext t
    exact ⟨And.left, fun ht => ⟨ht, le_top⟩⟩
  rw [hLeft] at h1
  rw [hRight] at h3
  have h12 := curveL_path_trans_add (p.subpath 0 z₁) (p.subpath z₁ z₂) h1.1 h2.1
  have hall := curveL_path_trans_add ((p.subpath 0 z₁).trans (p.subpath z₁ z₂))
    (p.subpath z₂ 1) h12.1 h3.1
  have h12L := h12.2
  have hallL := hall.2
  rw [h1.2, h2.2] at h12L
  rw [h3.2] at hallL
  have hcard := ncard_three_parts (curveVertexHits G p.toContinuousMap) hp hz₂.le
  change (curveVertexHits G p.toContinuousMap ∩ Iic z₁).ncard +
    (curveVertexHits G p.toContinuousMap ∩ Icc z₁ z₂).ncard +
    (curveVertexHits G p.toContinuousMap ∩ Ici z₂).ncard =
      (curveVertexHits G p.toContinuousMap).ncard + (if p z₁ ∈ G.V then 1 else 0) +
        (if p z₂ ∈ G.V then 1 else 0) at hcard
  have hfull : (curveVertexHits G p.toContinuousMap).ncard = curveL G p.toContinuousMap := rfl
  exact ⟨hall.1, by omega⟩

/-- The winding of a linearly parametrized subpath is the change
of any actual lifted angular coordinate between its two cut times. -/
theorem windingNumber_path_subpath
    {a b : ClosedCylinder} (p : Path a b) (s t : unitInterval) :
    windingNumber (p.subpath s t).toContinuousMap =
      (cylinderAngleLift p.toContinuousMap t - cylinderAngleLift p.toContinuousMap s) / (2 * Real.pi) := by
  let α := cylinderAngleLift p.toContinuousMap
  let β : C(unitInterval, ℝ) := ⟨fun u => α (Icc.convexComb s t u),
    α.continuous.comp (Icc.continuous_convexComb s t)⟩
  have hβ (u : unitInterval) : Circle.exp (β u) = ((p.subpath s t) u).1.2 :=
    exp_cylinderAngleLift p.toContinuousMap (Icc.convexComb s t u)
  rw [windingNumber_eq_of_exp_lift β hβ]
  change (α (Icc.convexComb s t 1) - α (Icc.convexComb s t 0)) / (2 * Real.pi) = _
  rw [Icc.convexComb_one, Icc.convexComb_zero]

/-- The two cuts in VI (5.5), page 131, preserve the old helix
potential as well as its vertex count. -/
theorem curvePhi_three_subpaths
    {k : ℕ} {G : Drawing ClosedCylinder} {a b : ClosedCylinder}
    (p : Path a b) (hp : (curveVertexHits G p.toContinuousMap).Finite)
    {z₁ z₂ : unitInterval} (hz₁ : 0 < z₁) (hz₂ : z₁ < z₂) (hb : b ∉ G.V) :
    let P := ((p.subpath 0 z₁).trans (p.subpath z₁ z₂)).trans (p.subpath z₂ 1)
    curvePhi k G P.toContinuousMap = curvePhi k G p.toContinuousMap := by
  dsimp only
  have hL := (curveL_three_subpaths p hp hz₁ hz₂ hb).2
  have hw : windingNumber (((p.subpath 0 z₁).trans (p.subpath z₁ z₂)).trans
      (p.subpath z₂ 1)).toContinuousMap = windingNumber p.toContinuousMap := by
    rw [windingNumber_path_trans, windingNumber_path_trans,
      windingNumber_path_subpath, windingNumber_path_subpath, windingNumber_path_subpath]
    unfold windingNumber
    ring
  rw [curvePhi, curvePhi, hL, hw]

end GraphMinor.GM06
