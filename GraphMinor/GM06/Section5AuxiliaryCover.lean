module

public import GraphMinor.GM06.Section5CoverCurvePoint
public import GraphMinor.GM06.Section5CoverDisc
public import GraphMinor.GM06.Section5CurveCount

/-!
# Assembling the actual auxiliary cover curve

VI (5.5), pages 131–132, follows the old prefix, then returns through
the lifted last region segment, reverses the replacement approach,
and reverses the initial half gap. Lift the old prefix through the
fixed initial contact of the last region segment. The four lifted
pieces now have matching endpoints. Their concatenation projects
to the auxiliary curve, and after the first prefix it stays in the
cut strip and the following half gap.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

private theorem cover_projection_path_trans
    {a b c : CylinderCover} {x y z : ClosedCylinder}
    (p : Path a b) (q : Path b c) (P : Path x y) (Q : Path y z)
    (hp : ∀ t, cylinderCoverProjection (p t) = P t)
    (hq : ∀ t, cylinderCoverProjection (q t) = Q t) :
    ∀ t, cylinderCoverProjection ((p.trans q) t) = (P.trans Q) t := by
  intro t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

/-- Assemble the auxiliary lift from its actual region and half-gap
lifts, preserving the shared contact and the return location required
by the crossing count in VI (5.5), page 132. -/
theorem exists_auxiliary_cover_from_region_lifts
    {a x s w y : ClosedCylinder}
    (p : Path a x) (q : Path x w) (g : Path s w) (h : Path y s)
    (Q A H : C(unitInterval, CylinderCover))
    (hQproj : ∀ t, cylinderCoverProjection (Q t) = q t)
    (hAproj : ∀ t, cylinderCoverProjection (A t) = g t)
    (hHproj : ∀ t, cylinderCoverProjection (H t) = h t)
    (hA0 : A 0 = H 1) (hA1 : A 1 = Q 1)
    {D U : Set (ℝ × ℝ)}
    (hQD : ∀ t, cylinderCoverCoordinates (Q t) ∈ D)
    (hAD : ∀ t, cylinderCoverCoordinates (A t) ∈ D)
    (hHU : ∀ t, cylinderCoverCoordinates (H t) ∈ U) :
    ∃ B : C(unitInterval, CylinderCover),
      (∀ t, cylinderCoverProjection (B t) = (p.trans ((q.trans g.symm).trans h.symm)) t) ∧
      B 1 = H 0 ∧
      ∀ t, leftHalfTime 1 ≤ t → cylinderCoverCoordinates (B t) ∈ D ∪ U := by
  have hpoint : cylinderCoverProjection (Q 0) = p 1 := by
    calc
      cylinderCoverProjection (Q 0) = q 0 := hQproj 0
      _ = x := Path.source q
      _ = p 1 := (Path.target p).symm
  obtain ⟨P, hP1, hPproj⟩ := exists_cover_curve_through_point p.toContinuousMap 1 (Q 0) hpoint
  let CP : Path (P 0) (Q 0) := ⟨P, rfl, hP1⟩
  let CQ : Path (Q 0) (Q 1) := ⟨Q, rfl, rfl⟩
  let CG : Path (H 1) (Q 1) := ⟨A, hA0, hA1⟩
  let CH : Path (H 0) (H 1) := ⟨H, rfl, rfl⟩
  let R := (CQ.trans CG.symm).trans CH.symm
  let B := (CP.trans R).toContinuousMap
  have hQG := cover_projection_path_trans CQ CG.symm q g.symm hQproj
    (fun t => hAproj (unitInterval.symm t))
  have hRproj := cover_projection_path_trans (CQ.trans CG.symm) CH.symm
    (q.trans g.symm) h.symm hQG (fun t => hHproj (unitInterval.symm t))
  have hBproj := cover_projection_path_trans CP R p ((q.trans g.symm).trans h.symm) hPproj hRproj
  have hRrange (t : unitInterval) : cylinderCoverCoordinates (R t) ∈ D ∪ U := by
    change cylinderCoverCoordinates (((CQ.trans CG.symm).trans CH.symm) t) ∈ D ∪ U
    rw [Path.trans_apply]
    split_ifs
    · rw [Path.trans_apply]
      split_ifs
      · exact Or.inl (hQD _)
      · exact Or.inl (hAD (unitInterval.symm _))
    · exact Or.inr (hHU (unitInterval.symm _))
  refine ⟨B, hBproj, Path.target _, ?_⟩
  intro t ht
  change (1 : ℝ) / 2 ≤ (t : ℝ) at ht
  let u : unitInterval := ⟨2 * (t : ℝ) - 1, by
    constructor <;> linarith only [ht, t.2.2]⟩
  have hut : rightHalfTime u = t := by
    apply Subtype.ext
    change (2 * (t : ℝ) - 1 + 1) / 2 = t
    ring
  change cylinderCoverCoordinates ((CP.trans R) t) ∈ D ∪ U
  rw [← hut, path_trans_rightHalfTime]
  exact hRrange u

end GraphMinor.GM06
