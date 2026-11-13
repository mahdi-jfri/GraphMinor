module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5InitialEdgeChart
public import GraphMinor.GM06.Section5CollapseInChart
import GraphMinor.GM06.Section5CollapseChartFibers
import Mathlib.Topology.Maps.Basic

/-!
# The topological contraction of the actual initial edge

For Reduction 3 of VI, page 129, paste the rectangular contraction
into the chart around the valency-one edge. Its only collapsed fiber
is exactly that closed edge, and it fixes the surface boundary and
the other linkage paths throughout its homotopy. Restricting the
closed map gives the homeomorphism off the edge. The quotient-map
criterion proves openness away from the collapsed fiber.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- The actual Reduction 3 collapse retains its rectangular chart and
the formula for every stage of its homotopy. In particular, the
fixed-frontier and positive-chart arguments use the same collapse
as the drawing and linkage update. -/
theorem exists_rectangular_collapse_of_initial_valency_one_edge
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2) :
    ∃ (π : C(ClosedCylinder, ClosedCylinder))
      (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
      (D : Set ClosedCylinder) (E : Section5CollapseRectangle ≃ₜ D),
      IsClosed D ∧
      (∀ t z, H (t, (E z).val) = (E (section5RectangleCollapseHomotopy (t, z))).val) ∧
      (∀ x ∉ D, ∀ t, H (t, x) = x) ∧
      (E section5RectangleOrigin).val = cylinderM1Point k i ∧
      (fun z => (E z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1} = closure a ∧
      (∀ x, H (0, x) = x) ∧ (∀ x, H (1, x) = π x) ∧
      (∀ x ∈ bd ClosedCylinder, ∀ t, H (t, x) = x) ∧
      π ⁻¹' {cylinderM1Point k i} = closure a ∧
      Nonempty ({x : ClosedCylinder // x ∉ closure a} ≃ₜ
        {y : ClosedCylinder // y ≠ cylinderM1Point k i}) ∧
      InjOn π (closure a)ᶜ ∧
      (∀ y, y ≠ cylinderM1Point k i → ∃ x ∉ closure a, π x = y) ∧
      (∀ U : Set ClosedCylinder, IsOpen U → Disjoint U (closure a) → IsOpen (π '' U)) ∧
      ∀ j : Fin k, j ≠ i → ∀ x ∈ (L.pathDrawing j).U, ∀ t, H (t, x) = x := by
  obtain ⟨D, e, hD, hfront, hbd, hzero, hseg, hmiss⟩ :=
    exists_chart_of_initial_valency_one_edge L hG i hval hl hvs hvC
  obtain ⟨π, H, hH0, hH1, hHbd, hπchart, hHout, hHchart⟩ :=
    exists_rectangle_contraction_in_chart hD e hfront hbd
  have hout (x : ClosedCylinder) (hx : x ∉ D) : π x = x :=
    (hH1 x).symm.trans (hHout x hx 1)
  have hpre : π ⁻¹' {cylinderM1Point k i} = closure a := by
    rw [← hzero, fiber_of_rectangle_collapse_in_chart e π hπchart hout, hseg]
  have hsurj : Function.Surjective π := surjective_of_rectangle_collapse_in_chart e π hπchart hout
  have hinj : InjOn π (closure a)ᶜ := by
    rw [← hseg]
    exact injOn_of_rectangle_collapse_in_chart e π hπchart hout
  have hhomeo : Nonempty ({x : ClosedCylinder // x ∉ closure a} ≃ₜ
      {y : ClosedCylinder // y ≠ cylinderM1Point k i}) := by
    rw [← hseg, ← hzero]
    exact homeomorph_off_segment_of_rectangle_collapse_in_chart e π hπchart hout
  refine ⟨π, H, D, e, hD, hHchart, hHout, hzero, hseg,
    hH0, hH1, hHbd, hpre, hhomeo, hinj, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨x, ?_, hx⟩
    intro hxa
    have hxpre : x ∈ π ⁻¹' {cylinderM1Point k i} := hpre.symm ▸ hxa
    exact hy (hx.symm.trans hxpre)
  · intro U hU hUa
    have hquot := π.continuous.isClosedMap.isQuotientMap π.continuous hsurj
    rw [← hquot.isCoinducing.isOpen_preimage]
    have hsat : π ⁻¹' (π '' U) = U := by
      ext x
      constructor
      · rintro ⟨u, hu, he⟩
        have huNot : u ∉ closure a := disjoint_left.mp hUa hu
        have hxNot : x ∉ closure a := by
          intro hxa
          have hxpre' : x ∈ π ⁻¹' {cylinderM1Point k i} := by rw [hpre]; exact hxa
          have hxpre : π x = cylinderM1Point k i := hxpre'
          have hupre : u ∈ π ⁻¹' {cylinderM1Point k i} := he.trans hxpre
          exact huNot (hpre ▸ hupre)
        have hxu : x = u := hinj hxNot huNot he.symm
        exact hxu.symm ▸ hu
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hsat]
    exact hU
  · intro j hj x hx t
    have hxD : x ∉ D := fun h => disjoint_left.mp (hmiss j hj) h hx
    exact hHout x hxD t

/-- The actual hypotheses of Reduction 3 give its continuous collapse
map and boundary-fixing homotopy, with the exact fiber, complement
homeomorphism, openness, and fixed other linkage paths. -/
theorem exists_collapse_of_initial_valency_one_edge
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2) :
    ∃ (π : C(ClosedCylinder, ClosedCylinder))
      (H : C(unitInterval × ClosedCylinder, ClosedCylinder)),
      (∀ x, H (0, x) = x) ∧ (∀ x, H (1, x) = π x) ∧
      (∀ x ∈ bd ClosedCylinder, ∀ t, H (t, x) = x) ∧
      π ⁻¹' {cylinderM1Point k i} = closure a ∧
      Nonempty ({x : ClosedCylinder // x ∉ closure a} ≃ₜ
        {y : ClosedCylinder // y ≠ cylinderM1Point k i}) ∧
      InjOn π (closure a)ᶜ ∧
      (∀ y, y ≠ cylinderM1Point k i → ∃ x ∉ closure a, π x = y) ∧
      (∀ U : Set ClosedCylinder, IsOpen U → Disjoint U (closure a) → IsOpen (π '' U)) ∧
      ∀ j : Fin k, j ≠ i → ∀ x ∈ (L.pathDrawing j).U, ∀ t, H (t, x) = x := by
  obtain ⟨π, H, D, E, _, _, _, _, _, hH0, hH1, hHbd, hfibre, hhomeo, hi,
      hsurj, hopen, hfix⟩ :=
    exists_rectangular_collapse_of_initial_valency_one_edge L hG i hval hl hvs hvC
  exact ⟨π, H, hH0, hH1, hHbd, hfibre, hhomeo, hi, hsurj, hopen, hfix⟩

end GraphMinor.GM06
