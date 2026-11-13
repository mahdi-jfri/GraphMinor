module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5ContractedPath
import GraphMinor.GM06.Section5ContractionOtherPaths
import GraphMinor.GM06.Section5Red
import GraphMinor.GM07.Section3

/-!
# The linkage after contracting its initial edge

For Reduction 3 of VI, page 129, use the shortened image path at the
chosen start and retain the other paths and their curves. The image
path parametrization is homotopic to the collapsed old curve because
both lie on the same path and have the same ends.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The initial-edge collapse produces a linkage with the exact
image point sets and homotopies required by Reduction 3, while
retaining every other path and curve. -/
theorem exists_linkage_of_initial_edge_collapse
    {k : ℕ} {G G' : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure a)
    (hi : InjOn π (closure a)ᶜ)
    (hbd : ∀ x ∈ bd ClosedCylinder, π x = x)
    (hfix : ∀ j, j ≠ i → ∀ x ∈ (L.pathDrawing j).U, π x = x)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {a})) :
    ∃ L' : CylinderLinkage k G',
      (∀ j, (L'.pathDrawing j).U = π '' (L.pathDrawing j).U ∧
        CurvesHomotopic (L'.curve j) (π.comp (L.curve j))) ∧
      (∀ j, j ≠ i → L'.pathDrawing j = L.pathDrawing j ∧ L'.curve j = L.curve j) := by
  classical
  obtain ⟨Q, hQG, hQ, hQU⟩ :=
    exists_contracted_initial_path L i hval hl hvs hvC π hfiber hi hbd hV hE
  have hothers := other_paths_of_initial_edge_collapse L i hval hl hvs hvC π
    hfiber hi hfix hV hE hQU
  obtain ⟨f, hf⟩ := hQ.2
  let R : Fin k → Drawing ClosedCylinder := fun j => if j = i then Q else L.pathDrawing j
  let g : Fin k → Curve ClosedCylinder := fun j => if j = i then f else L.curve j
  have hgend : ∀ j, g j 1 = L.curve j 1 := by
    intro j
    by_cases hj : j = i
    · subst j; simpa [g] using hf.2.2.2
    · simp [g, hj]
  let L' : CylinderLinkage k G' := {
    pathDrawing := R
    curve := g
    isSubdrawing j := by
      by_cases hj : j = i
      · subst j; simpa [R] using And.intro hQG hQG.U_subset
      · exact ⟨by simpa [R, hj] using (hothers j hj).1,
          by simpa [R, hj] using (hothers j hj).1.U_subset⟩
    isPath j := by
      rw [hgend]
      by_cases hj : j = i
      · subst j; simpa [R] using hQ
      · simpa [R, hj] using L.isPath j
    curve_parametrizes j := by
      rw [hgend]
      by_cases hj : j = i
      · subst j; simpa [R, g] using hf
      · simpa [R, g, hj] using L.curve_parametrizes j
    curve_one_mem j := by rw [hgend]; exact L.curve_one_mem j
    pairwise_disjoint := by
      intro j l hjl
      by_cases hj : j = i
      · subst j
        simpa [R, Ne.symm hjl] using (hothers l (Ne.symm hjl)).2
      · by_cases hl' : l = i
        · subst l
          simpa [R, hj] using (hothers j hj).2.symm
        · simpa [R, hj, hl'] using L.pairwise_disjoint hjl }
  refine ⟨L', ?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst j
      change (R i).U = _ ∧ CurvesHomotopic (g i) _
      simp only [R, g, ite_eq_left (rfl : i = i)]
      refine ⟨hQU, ?_⟩
      have hγU : range (π.comp (L.curve i)) ⊆ Q.U := by
        rw [hQU]
        rintro x ⟨t, rfl⟩
        exact mem_image_of_mem π ((L.curve_parametrizes i).2.1 ▸ mem_range_self t)
      have hγ0 : (π.comp (L.curve i)) 0 = cylinderM1Point k i := by
        change π (L.curve i 0) = _
        rw [(L.curve_parametrizes i).2.2.1, hbd _ (cylinderM1Point_mem_bd k i)]
      have hγ1 : (π.comp (L.curve i)) 1 = L.curve i 1 := by
        obtain ⟨j, hj⟩ := L.curve_one_mem i
        change π (L.curve i 1) = _
        rw [← hj, hbd _ (cylinderM2Point_mem_bd k j)]
      obtain ⟨H, _, hrest⟩ := curvesHomotopicIn_of_range_subset_parametrizesSet hf hγU hγ0 hγ1
      exact GM07.CurvesHomotopic.symm ⟨H, fun _ => mem_univ _, hrest⟩
    · have hcurve : π.comp (L.curve j) = L.curve j := by
        apply ContinuousMap.ext
        intro t
        exact hfix j hj _ ((L.curve_parametrizes j).2.1 ▸ mem_range_self t)
      constructor
      · change (R j).U = _
        simp only [R, ite_eq_right hj]
        symm
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩; rwa [hfix j hj y hy]
        · intro hx; exact ⟨x, hx, hfix j hj x hx⟩
      · simpa only [L', g, ite_eq_right hj, hcurve] using GM07.CurvesHomotopic.refl (L.curve j)
  · intro j hj
    exact ⟨by simp [L', R, hj], by simp [L', g, hj]⟩

end GraphMinor.GM06
