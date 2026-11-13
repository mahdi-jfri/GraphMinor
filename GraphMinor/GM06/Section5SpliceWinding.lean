module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5StripWinding
import GraphMinor.GM06.Section5SplicedLinkage
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5StripBoundary
import GraphMinor.GM06.Section5StripProjection
import GraphMinor.GM06.Section4PathTools

/-!
# The winding of the cyclically spliced linkage

In VI (5.1), page 129, the ith new path lies in the closure of Σᵢ.
Both old boundary paths of that strip lie in its closure as well.
The new endpoints lift to the first initial endpoint and the next
terminal endpoint of the strip disc. The disc winding calculation
therefore gives θ + 1/k for every new linkage path.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

private theorem succ_path_subset_closure_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i : Fin k) :
    (L.pathDrawing (finSuccCycle i)).U ⊆ closure (cylinderStrip L i) := by
  let m : ℤ := (i.val : ℤ) + 1
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ m
  have him := image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip
  intro x hx
  obtain ⟨u, rfl⟩ := (L.curve_parametrizes (finSuccCycle i)).2.1.symm ▸ hx
  have hp : liftedLinkageCurve hG.1 L (m + 1) u ∈ D := by
    apply discBd_subset D
    rw [hBd]
    exact Or.inl (Or.inl (Or.inr (mem_range_self u)))
  have hproj : radialCylinderProjection (liftedLinkageCurve hG.1 L (m + 1) u) =
      L.curve (finSuccCycle i) u := by
    dsimp only [m]
    rw [radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ_add_one]
  rw [← hproj, ← him]
  exact mem_image_of_mem radialCylinderProjection hp

/-- The strip confinement and terminal shift of the cyclic splicing
in VI (5.1), page 129, force every new path to have winding θ + 1/k. -/
theorem theta_next_of_spliced_linkage
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L L' : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hk : 1 < k) (hθ : L.HasTheta θ)
    (hend : ∀ i, L'.curve i 1 = L.curve (finSuccCycle i) 1)
    (hconf : ∀ i, (L'.pathDrawing i).U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i} ∪
      (L.pathDrawing (finSuccCycle i)).U) : L'.HasTheta (θ + 1 / (k : ℝ)) := by
  intro i
  let m : ℤ := (i.val : ℤ) + 1
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ m
  have him := image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip
  have hsCl : cylinderM1Point k i ∈ closure (cylinderStrip L i) :=
    L.U_subset_closure_strip hG hθ i
      ((L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1)
  have hsucc := succ_path_subset_closure_strip L hG hθ i
  have hNew : (L'.pathDrawing i).U ⊆ closure (cylinderStrip L i) := by
    intro x hx
    rcases hconf i hx with (hxS | hxS) | hxT
    · exact subset_closure hxS
    · rw [mem_singleton_iff.mp hxS]
      exact hsCl
    · exact hsucc hxT
  have hf : range (L'.curve i) ⊆ radialCylinderProjection '' D := by
    rw [him, (L'.curve_parametrizes i).2.1]
    exact hNew
  have hf0 : L'.curve i 0 = radialCylinderProjection (liftedLinkageCurve hG.1 L m 0) := by
    dsimp only [m]
    rw [radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ,
      (L'.curve_parametrizes i).2.2.1, (L.curve_parametrizes i).2.2.1]
  have hf1 : L'.curve i 1 = radialCylinderProjection (liftedLinkageCurve hG.1 L (m + 1) 1) := by
    dsimp only [m]
    rw [radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ_add_one, hend i]
  exact windingNumber_eq_next_of_range_subset_stripDisc L hG hk hθ m hD hBd hstrip
    (L'.curve i) hf hf0 hf1

/-- The construction following the region-contact claim in the proof
of VI (5.1), page 129: cyclic splicing gives a feasible winding θ + 1/k. -/
theorem isThetaFeasible_next_of_region_contacts
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hk : 1 < k) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hcontact : ∀ i, closure (cylinderRegion k G i) ∩ (L.pathDrawing i).U ⊆
      {cylinderM1Point k i}) : IsThetaFeasible k G (θ + 1 / (k : ℝ)) := by
  obtain ⟨L', hend, hconf, _⟩ := exists_spliced_linkage_of_region_contacts L hG hk hθ hno hcontact
  exact ⟨L', theta_next_of_spliced_linkage L L' hG hk hθ hend hconf⟩

end GraphMinor.GM06
