module

public import GraphMinor.GM06.Section5LinkageStripCircle
public import GraphMinor.GM06.Section5RadialProjection
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5SingleStrip
import GraphMinor.GM06.Section5SingleStripFibers
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5StripProjection

/-!
# Projection of the one-path cut disc

In the one-path case of VI Section 5, cutting along the linkage path
gives the disc between two consecutive lifts. Its projection covers
the cylinder. Off the path it is one to one, and over the path it
has only the two matching boundary points. These facts give finite
fibers for constructing the finite drawing on the cut disc.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

private theorem projected_single_path_lift_mem
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G) (hk : 0 < 1)
    (n : ℤ) (t : unitInterval) :
    radialCylinderProjection (liftedLinkageCurve hk L n t) ∈ (L.pathDrawing 0).U := by
  rw [radialCylinderProjection_liftedLinkageCurve]
  have hi : modIdx 1 hk n = 0 := Subsingleton.elim _ _
  rw [hi]
  exact (L.curve_parametrizes 0).2.1 ▸ mem_range_self t

/-- The disc between the canonical lift of a sole linkage path and
its next translate projects onto the whole cylinder. -/
theorem surjective_single_strip_projection
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    Function.Surjective (fun p : D => radialCylinderProjection p.1) := by
  have hcl : closure (cylinderStrip L 0) = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ (L.pathDrawing 0).U
    · exact L.U_subset_closure_strip hG hθ 0 hx
    · apply subset_closure
      rw [cylinderStrip_eq_compl_of_one_path L hG]
      exact hx
  have him : radialCylinderProjection '' D = univ := by
    rw [image_stripDisc_eq_closure_strip L hG hθ 0 hD hBd hstrip, hcl]
  intro x
  obtain ⟨p, hp, hpx⟩ := him.symm ▸ mem_univ x
  exact ⟨⟨p, hp⟩, hpx⟩

/-- A point off the cut path has at most one point above it in the
closed lifted strip disc. -/
theorem single_strip_projection_inj_off_path
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {p q : D} (hp : radialCylinderProjection p.1 ∉ (L.pathDrawing 0).U)
    (heq : radialCylinderProjection p.1 = radialCylinderProjection q.1) : p = q := by
  rcases radialCylinderProjection_single_strip_fibers L hG hθ 1 hD hBd hstrip p.2 q.2 heq with
    he | ⟨t, ⟨hp', _⟩ | ⟨_, hp'⟩⟩
  · exact Subtype.ext he
  · exact False.elim (hp (hp' ▸ projected_single_path_lift_mem L hG.1 2 t))
  · exact False.elim (hp (hp' ▸ projected_single_path_lift_mem L hG.1 1 t))

/-- Every point of the cylinder has finitely many preimages in the
cut disc. The preimage of a path point consists of its two boundary
copies, and the preimage of any other point is a subsingleton. -/
theorem finite_fiber_single_strip_projection
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (x : ClosedCylinder) :
    ((fun p : D => radialCylinderProjection p.1) ⁻¹' {x}).Finite := by
  classical
  by_cases hx : x ∈ (L.pathDrawing 0).U
  · obtain ⟨t, ht⟩ := (L.curve_parametrizes 0).2.1.symm ▸ hx
    let p := liftedLinkageCurve hG.1 L 1 t
    let q := liftedLinkageCurve hG.1 L 2 t
    have hpD : p ∈ D := by
      apply discBd_subset D
      rw [hBd]
      exact Or.inl (Or.inl (Or.inl (mem_range_self t)))
    have hqD : q ∈ D := by
      apply discBd_subset D
      rw [hBd]
      exact Or.inl (Or.inl (Or.inr (mem_range_self t)))
    have hpx : radialCylinderProjection p = x := by
      rw [radialCylinderProjection_liftedLinkageCurve]
      have hi : modIdx 1 hG.1 1 = 0 := Subsingleton.elim _ _
      rw [hi]
      exact ht
    apply ((finite_singleton (⟨q, hqD⟩ : D)).insert (⟨p, hpD⟩ : D)).subset
    intro y hy
    have hyx : radialCylinderProjection y.1 = x := mem_singleton_iff.mp hy
    rcases radialCylinderProjection_single_strip_fibers L hG hθ 1 hD hBd hstrip
        y.2 hpD (hyx.trans hpx.symm) with he | ⟨u, ⟨hy2, hp1⟩ | ⟨hp2, hy1⟩⟩
    · exact Or.inl (Subtype.ext he)
    · have htu : t = u := (isArcMap_liftedLinkageCurve hG.1 L 1).2 hp1
      rw [← htu] at hy2
      exact Or.inr (Subtype.ext hy2)
    · exact False.elim (disjoint_left.mp (disjoint_range_liftedLinkageCurve hG.1 L
        (by norm_num : (1 : ℤ) ≠ 2)) (mem_range_self t) ⟨u, hp2.symm⟩)
  · have hinj : Set.Subsingleton ((fun p : D => radialCylinderProjection p.1) ⁻¹' {x}) := by
      intro p hp q hq
      have hpx : radialCylinderProjection p.1 = x := mem_singleton_iff.mp hp
      have hqx : radialCylinderProjection q.1 = x := mem_singleton_iff.mp hq
      exact single_strip_projection_inj_off_path L hG hθ hD hBd hstrip
        (hpx.symm ▸ hx) (hpx.trans hqx.symm)
    exact hinj.finite

end GraphMinor.GM06
