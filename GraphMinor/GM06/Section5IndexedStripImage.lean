module

public import GraphMinor.GM06.Section5LinkageStripCircle
public import GraphMinor.GM06.Section5RadialProjection
import GraphMinor.GM06.Section5StripDisc
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5StripInjective
import GraphMinor.Surface.PlaneDisc

/-!
# Strip discs with arbitrary integer indices

For the local argument in VI (5.1), page 129, adjacent strips must
also be compared across the cyclic indexing seam. Translate a
canonical strip disc by an integer angular period. Its boundary
index changes by that linkage period while its cylinder image stays
the same. This gives indexed discs with the required strip images
without imposing a choice of representative index.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- Each integer-indexed lifted strip has a closed disc projecting
onto the corresponding cylinder strip closure, including indices
across a full angular period. -/
theorem exists_indexed_stripDisc_with_image
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ) :
    ∃ D : Set (ℝ × ℝ), IsClosedDisc D ∧ discBd D = liftedStripBoundary hG.1 L m ∧
      D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2} ∧
      radialCylinderProjection '' D = closure (cylinderStrip L (modIdx k hG.1 m)) := by
  let i := modIdx k hG.1 m
  let q : ℤ := (m - 1) / (k : ℤ)
  have hrem : (i.val : ℤ) = (m - 1) % (k : ℤ) := by
    change ((modIdx k hG.1 m).val : ℤ) = _
    rw [modIdx_val]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.natCast_ne_zero.mpr hG.1.ne'))
  have hm : m = ((i.val : ℤ) + 1) + (k : ℤ) * q := by
    have hdiv := Int.emod_add_mul_ediv (m - 1) (k : ℤ)
    dsimp only [q]
    omega
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ ((i.val : ℤ) + 1)
  have himage := image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip
  let τ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.addRight (0, (q : ℝ) * (2 * π))
  have hτ : (τ : (ℝ × ℝ) → (ℝ × ℝ)) =
      fun x => (x.1, x.2 + (q : ℝ) * (2 * π)) := by
    funext x
    exact Prod.ext (add_zero x.1) rfl
  have htrans := hD.image τ.continuous.continuousOn τ.symm.continuous.continuousOn
    (fun x _ => τ.symm_apply_apply x)
  refine ⟨τ '' D, htrans.1, ?_, ?_, ?_⟩
  · rw [htrans.2, hBd, hτ, hm]
    exact image_liftedStripBoundary_add_mul hG.1 L _ q
  · rintro p ⟨x, hx, rfl⟩
    change 1 ≤ x.1 + 0 ∧ x.1 + 0 ≤ 2
    simpa only [add_zero, mem_ofPred_eq] using hstrip hx
  · have hπ (p : ℝ × ℝ) : radialCylinderProjection (τ p) = radialCylinderProjection p := by
      rw [hτ]
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change Circle.exp (p.2 + (q : ℝ) * (2 * π)) = Circle.exp p.2
        exact Circle.exp_eq_exp.mpr ⟨q, rfl⟩
    calc
      radialCylinderProjection '' (τ '' D) = radialCylinderProjection '' D := by
        rw [image_image]
        congr 1
        funext p
        exact hπ p
      _ = closure (cylinderStrip L i) := himage

end GraphMinor.GM06
