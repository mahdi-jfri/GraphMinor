module

public import GraphMinor.GM06.Section5SeamRectangle
import GraphMinor.GM06.Section5InitialEdgeCoordinates
import GraphMinor.GM06.Section5NarrowSeamRectangle
import GraphMinor.GM06.Section5SeamRectangleFrontier
import GraphMinor.Surface.InvarianceOfDomain
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

/-!
# A contraction chart for the actual initial edge

For Reduction 3 of VI, page 129, put the incident edge at the central
half-segment of a cylinder seam chart. A narrow rectangle avoids all
other linkage paths. Its frontier and its intersection with the
surface boundary lie on fixed rectangle sides. This constructs the
chart used to paste the contraction, directly from the valency-one
hypotheses of the reduction.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

/-- The actual hypotheses of Reduction 3 give a closed rectangular
chart whose distinguished segment is exactly the edge to contract,
whose origin is the initial vertex, and which misses all other
linkage paths. All frontier and surface boundary points lie on the
fixed rectangle sides. -/
theorem exists_chart_of_initial_valency_one_edge
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2) :
    ∃ (D : Set ClosedCylinder) (e : Section5CollapseRectangle ≃ₜ D),
      IsClosed D ∧
      (∀ z, (e z).1 ∈ frontier D →
        z.1.1 = -1 ∨ z.1.1 = 1 ∨ z.2.1 = 0 ∨ z.2.1 = 2) ∧
      (∀ z, (e z).1 ∈ bd ClosedCylinder →
        z.1.1 = -1 ∨ z.1.1 = 1 ∨ z.2.1 = 0 ∨ z.2.1 = 2) ∧
      (e section5RectangleOrigin).1 = cylinderM1Point k i ∧
      (fun z => (e z).1) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1} = closure a ∧
      ∀ j : Fin k, j ≠ i → Disjoint D (L.pathDrawing j).U := by
  let c : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  obtain ⟨K, hK0, _, hedge, hseam⟩ := exists_coordinates_of_initial_valency_one_edge
    L hG i hval hl hvs hvC c (by
      constructor
      · change (0 : ℝ) < 1 / 2; norm_num
      · change (1 / 2 : ℝ) < 1; norm_num)
  let A := ⋃ j : {j : Fin k // j ≠ i}, (L.pathDrawing j.1).U
  have hA : IsClosed A := isClosed_iUnion_of_finite (fun j => (L.pathDrawing j.1).isClosed_U)
  have hdis : Disjoint (range (fun u : unitInterval => K (section5CylinderProduct.symm (1, u)))) A := by
    rw [hseam]
    apply disjoint_left.mpr
    intro x hxi hxA
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxA
    exact disjoint_left.mp (L.pairwise_disjoint (Ne.symm j.2)) hxi hxj
  obtain ⟨ε, hε, hεπ, hAvoid⟩ := exists_narrow_seam_rectangle_avoiding K hA hdis
  let f : C(Section5CollapseRectangle, ClosedCylinder) :=
    ⟨fun z => K (section5SeamRectangle ε z), K.continuous.comp (section5SeamRectangle ε).continuous⟩
  have hfi : Function.Injective f := K.injective.comp (section5SeamRectangle_injective hε hεπ)
  let D := range f
  let e : Section5CollapseRectangle ≃ₜ D := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective f hfi) f.continuous.rangeFactorization
  have hDimage : D = K '' range (section5SeamRectangle ε) := by
    change range (K ∘ section5SeamRectangle ε) = _
    exact range_comp _ _
  have hclosed : IsClosed D := (isCompact_range f.continuous).isClosed
  refine ⟨D, e, hclosed, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hz' : section5SeamRectangle ε z ∈ frontier (range (section5SeamRectangle ε)) := by
      change K (section5SeamRectangle ε z) ∈ frontier D at hz
      rw [hDimage, ← K.image_frontier] at hz
      obtain ⟨x, hx, he⟩ := hz
      exact K.injective he ▸ hx
    rcases section5SeamRectangle_frontier_sides hε z hz' with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · intro z hz
    have hz' : section5SeamRectangle ε z ∈ bd ClosedCylinder := by
      rw [← image_bd_homeomorph K] at hz
      obtain ⟨x, hx, he⟩ := hz
      exact K.injective he ▸ hx
    rcases (section5SeamRectangle_mem_boundary_iff ε z).mp hz' with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · change K (section5SeamRectangle ε section5RectangleOrigin) = _
    rw [section5SeamRectangle_origin]
    exact hK0
  · change (fun z => K (section5SeamRectangle ε z)) '' _ = closure a
    rw [← image_image K (section5SeamRectangle ε), image_section5SeamRectangle_segment, image_image]
    exact hedge.symm
  · intro j hj
    apply disjoint_left.mpr
    intro x hxD hxj
    exact disjoint_left.mp hAvoid hxD (mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩)

end GraphMinor.GM06
