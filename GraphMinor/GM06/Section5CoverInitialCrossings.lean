module

public import GraphMinor.GM06.Section5
public import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section5ReturnStripAvoidance

/-!
# Crossings before the prescribed-side return

For VI (5.5), page 132, use an actual continuous cover lift of the
auxiliary curve. Every linkage lift starting between its initial
cuff ends meets it at a vertex time. When the curve has entered the
return strip, the lifts counted beyond the following dual point
cannot meet it. Their distinct vertex times therefore occur strictly
before that return portion, as required for the earlier-prefix count.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- The initial-cuff crossing argument works for an actual cover
lift and a normal curve in any drawing containing the linkage. -/
theorem exists_vertex_hit_of_cover_initial_between
    {k : ℕ} {G H : Drawing ClosedCylinder} {θ : ℝ}
    (hk : 0 < k) (L : CylinderLinkage k G) (hθ : L.HasTheta θ)
    (hPH : ∀ i, (L.pathDrawing i).U ⊆ H.U)
    (f : Curve ClosedCylinder) (hf : IsNormalCurve H f)
    (B : C(unitInterval, CylinderCover)) (hBproj : ∀ t, cylinderCoverProjection (B t) = f t)
    (hB0 : (B 0).1.1 = 1) (hB1 : (B 1).1.1 = 1) (m : ℤ)
    (hbetween : ((B 0).2 < 2 * (m : ℝ) * π / k ∧ 2 * (m : ℝ) * π / k < (B 1).2) ∨
      ((B 1).2 < 2 * (m : ℝ) * π / k ∧ 2 * (m : ℝ) * π / k < (B 0).2)) :
    ∃ t ∈ curveVertexHits H f, ∃ u : unitInterval,
      liftedLinkageCurve hk L m u = cylinderCoverCoordinates (B t) := by
  let F : C(unitInterval, ℝ × ℝ) := ⟨fun t => cylinderCoverCoordinates (B t), by
    dsimp [cylinderCoverCoordinates]
    fun_prop⟩
  obtain ⟨hΓr, hΓ0r, hΓ1r, hΓ0y, _, hΓexp⟩ := liftedLinkageCurve_props hk L hθ m
  have hbt : ((F 0).2 < (liftedLinkageCurve hk L m 0).2 ∧
      (liftedLinkageCurve hk L m 0).2 < (F 1).2) ∨
      ((F 1).2 < (liftedLinkageCurve hk L m 0).2 ∧
        (liftedLinkageCurve hk L m 0).2 < (F 0).2) := by
    rw [hΓ0y]
    exact hbetween
  obtain ⟨t, u, hmeet⟩ := strip_crossing_left F (liftedLinkageCurve hk L m)
    (fun t => (B t).1.2) hΓr hB0 hB1 hΓ0r hΓ1r hbt
  have hpoint : L.curve (modIdx k hk m) u = cylinderCoverProjection (B t) := by
    apply Subtype.ext
    apply Prod.ext
    · exact (liftedLinkageCurve_fst hk L m u).symm.trans (congrArg Prod.fst hmeet.symm)
    · exact (hΓexp u).symm.trans (congrArg Circle.exp (congrArg Prod.snd hmeet.symm))
  have hpoint' := hpoint.trans (hBproj t)
  have hmem : f t ∈ H.U := by
    apply hPH (modIdx k hk m)
    rw [← (L.curve_parametrizes (modIdx k hk m)).2.1]
    exact ⟨u, hpoint'⟩
  exact ⟨t, hf ⟨mem_range_self t, hmem⟩, u, hmeet.symm⟩

/-- Counted crossings occur before the return strip begins, giving
the earlier-prefix part of VI (5.5), page 132. The hypotheses specify
the actual lifted curve and its geometric return location. -/
theorem card_cover_initial_crossings_le_earlier_hits
    {G H : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hPH : ∀ i, (L.pathDrawing i).U ⊆ H.U)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (f : Curve ClosedCylinder) (hf : IsNormalCurve H f)
    (hfin : (curveVertexHits H f).Finite)
    (B : C(unitInterval, CylinderCover)) (hBproj : ∀ t, cylinderCoverProjection (B t) = f t)
    (hB0 : (B 0).1.1 = 1) (hB1 : (B 1).1.1 = 1)
    (τ : unitInterval)
    (hReturn : ∀ t, τ ≤ t → cylinderCoverCoordinates (B t) ∈
      D ∪ ({1} ×ˢ Icc (4 * π) (5 * π)))
    (T : Finset ℤ) (hT : ∀ m ∈ T, 3 ≤ m)
    (hbetween : ∀ m ∈ T,
      ((B 0).2 < 2 * (m : ℝ) * π / 1 ∧ 2 * (m : ℝ) * π / 1 < (B 1).2) ∨
      ((B 1).2 < 2 * (m : ℝ) * π / 1 ∧ 2 * (m : ℝ) * π / 1 < (B 0).2)) :
    T.card ≤ (curveVertexHits H f ∩ Iio τ).ncard := by
  classical
  have hhit (m : T) := exists_vertex_hit_of_cover_initial_between hG.1 L hθ hPH f hf
    B hBproj hB0 hB1 m.1 (by simpa only [Nat.cast_one] using hbetween m.1 m.2)
  let hit : T → unitInterval := fun m => Classical.choose (hhit m)
  have hfinite : (curveVertexHits H f ∩ Iio τ).Finite := hfin.inter_of_left _
  have hmem (m : T) : hit m ∈ hfinite.toFinset := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨(Classical.choose_spec (hhit m)).1, ?_⟩
    by_contra hnot
    obtain ⟨u, hu⟩ := (Classical.choose_spec (hhit m)).2
    have huRange : cylinderCoverCoordinates (B (hit m)) ∈ range (liftedLinkageCurve hG.1 L m.1) :=
      ⟨u, hu⟩
    exact disjoint_left.mp (disjoint_counted_lift_return_strip L hG hθ hD hBd hstrip
      (hT m.1 m.2)) huRange (hReturn (hit m) (le_of_not_gt hnot))
  have hinj : Function.Injective hit := by
    intro a b hab
    apply Subtype.ext
    obtain ⟨u, hu⟩ := (Classical.choose_spec (hhit a)).2
    obtain ⟨v, hv⟩ := (Classical.choose_spec (hhit b)).2
    change liftedLinkageCurve hG.1 L a.1 u = cylinderCoverCoordinates (B (hit a)) at hu
    change liftedLinkageCurve hG.1 L b.1 v = cylinderCoverCoordinates (B (hit b)) at hv
    rw [hab] at hu
    exact eq_of_liftedLinkageCurve_eq hG.1 L hθ (hu.trans hv.symm)
  let E : T → hfinite.toFinset := fun m => ⟨hit m, hmem m⟩
  have hE : Function.Injective E := fun a b hab => hinj (congrArg Subtype.val hab)
  have hcard : T.card ≤ hfinite.toFinset.card := by
    simpa [Fintype.card_coe] using Fintype.card_le_of_injective E hE
  exact hcard.trans_eq (Set.ncard_eq_toFinset_card _ hfinite).symm

/-- Count the crossings before an indexed return strip for any k,
as needed for both cases of VI (5.5), page 132. -/
theorem card_cover_initial_crossings_le_earlier_hits_general
    {k : ℕ} {G H : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hPH : ∀ i, (L.pathDrawing i).U ⊆ H.U) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (f : Curve ClosedCylinder) (hf : IsNormalCurve H f)
    (hfin : (curveVertexHits H f).Finite)
    (B : C(unitInterval, CylinderCover)) (hBproj : ∀ t, cylinderCoverProjection (B t) = f t)
    (hB0 : (B 0).1.1 = 1) (hB1 : (B 1).1.1 = 1)
    (τ : unitInterval)
    (hReturn : ∀ t, τ ≤ t → cylinderCoverCoordinates (B t) ∈
      D ∪ ({1} ×ˢ Icc (2 * ((m : ℝ) + 1) * π / k) ((2 * ((m : ℝ) + 1) + 1) * π / k)))
    (T : Finset ℤ) (hT : ∀ n ∈ T, m + 2 ≤ n)
    (hbetween : ∀ n ∈ T,
      ((B 0).2 < 2 * (n : ℝ) * π / k ∧ 2 * (n : ℝ) * π / k < (B 1).2) ∨
      ((B 1).2 < 2 * (n : ℝ) * π / k ∧ 2 * (n : ℝ) * π / k < (B 0).2)) :
    T.card ≤ (curveVertexHits H f ∩ Iio τ).ncard := by
  classical
  have hhit (n : T) := exists_vertex_hit_of_cover_initial_between hG.1 L hθ hPH f hf
    B hBproj hB0 hB1 n.1 (hbetween n.1 n.2)
  let hit : T → unitInterval := fun n => Classical.choose (hhit n)
  have hfinite : (curveVertexHits H f ∩ Iio τ).Finite := hfin.inter_of_left _
  have hmem (n : T) : hit n ∈ hfinite.toFinset := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨(Classical.choose_spec (hhit n)).1, ?_⟩
    by_contra hnot
    obtain ⟨u, hu⟩ := (Classical.choose_spec (hhit n)).2
    have huRange : cylinderCoverCoordinates (B (hit n)) ∈ range (liftedLinkageCurve hG.1 L n.1) :=
      ⟨u, hu⟩
    exact disjoint_left.mp (disjoint_counted_lift_return_strip_general L hG hθ m hD hBd hstrip
      (hT n.1 n.2)) huRange (hReturn (hit n) (le_of_not_gt hnot))
  have hinj : Function.Injective hit := by
    intro a b hab
    apply Subtype.ext
    obtain ⟨u, hu⟩ := (Classical.choose_spec (hhit a)).2
    obtain ⟨v, hv⟩ := (Classical.choose_spec (hhit b)).2
    change liftedLinkageCurve hG.1 L a.1 u = cylinderCoverCoordinates (B (hit a)) at hu
    change liftedLinkageCurve hG.1 L b.1 v = cylinderCoverCoordinates (B (hit b)) at hv
    rw [hab] at hu
    exact eq_of_liftedLinkageCurve_eq hG.1 L hθ (hu.trans hv.symm)
  let E : T → hfinite.toFinset := fun n => ⟨hit n, hmem n⟩
  have hE : Function.Injective E := fun a b hab => hinj (congrArg Subtype.val hab)
  have hcard : T.card ≤ hfinite.toFinset.card := by
    simpa [Fintype.card_coe] using Fintype.card_le_of_injective E hE
  exact hcard.trans_eq (Set.ncard_eq_toFinset_card _ hfinite).symm

end GraphMinor.GM06
