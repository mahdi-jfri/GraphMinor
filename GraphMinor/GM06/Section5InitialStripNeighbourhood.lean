module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5
import GraphMinor.GM06.Section5IndexedStripImage
import GraphMinor.GM06.Section5AdjacentStripNeighbourhood
import GraphMinor.GM06.Section5StripImage

/-!
# The two strips near an initial vertex

For the local boundary-contact argument in VI (5.1), page 129, the
two strips on either side of Pᵢ cover a cylinder neighbourhood of sᵢ.
Choose adjacent lifted strip discs with integer indices, including
across the cyclic seam, and project their half-neighbourhood.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- An integer index immediately before the canonical lift of Pᵢ
represents the cyclic predecessor strip. -/
theorem modIdx_natCast_eq_finPredCycle {k : ℕ} (hk : 0 < k) (i : Fin k) :
    modIdx k hk (i.val : ℤ) = finPredCycle i := by
  by_cases hi : i.val = 0
  · have hidx : (i.val : ℤ) = ((finPredCycle i).val : ℤ) + 1 + (k : ℤ) * (-1) := by
      have hval : (finPredCycle i).val = k - 1 := by simp [finPredCycle, hi]
      rw [hval, hi]
      omega
    rw [hidx, modIdx_add_mul, modIdx_natCast_succ]
  · have hidx : (i.val : ℤ) = ((finPredCycle i).val : ℤ) + 1 := by
      have hval : (finPredCycle i).val = i.val - 1 := by simp [finPredCycle, hi]
      rw [hval]
      omega
    rw [hidx, modIdx_natCast_succ]

/-- The two adjacent strip closures cover a neighbourhood of sᵢ,
as needed to locate other initial edges in VI (5.1). -/
theorem exists_initial_nhds_subset_adjacent_strip_closures
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k) :
    ∃ W : Set ClosedCylinder, IsOpen W ∧ cylinderM1Point k i ∈ W ∧
      W ⊆ closure (cylinderStrip L (finPredCycle i)) ∪ closure (cylinderStrip L i) := by
  obtain ⟨D, hD, hBdD, hstripD, himD⟩ := exists_indexed_stripDisc_with_image L hG hθ (i.val : ℤ)
  obtain ⟨E, hE, hBdE, hstripE, himE⟩ := exists_indexed_stripDisc_with_image L hG hθ ((i.val : ℤ) + 1)
  obtain ⟨W, hW, hcW, hsub⟩ := exists_nhds_subset_adjacent_strip_images L hG hθ (i.val : ℤ)
    hD hE hBdD hBdE hstripD hstripE
  have hstart : radialCylinderProjection (liftedLinkageCurve hG.1 L ((i.val : ℤ) + 1) 0) =
      cylinderM1Point k i := by
    rw [radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ,
      (L.curve_parametrizes i).2.2.1]
  rw [hstart] at hcW
  rw [himD, himE, modIdx_natCast_eq_finPredCycle, modIdx_natCast_succ] at hsub
  exact ⟨W, hW, hcW, hsub⟩

end GraphMinor.GM06
