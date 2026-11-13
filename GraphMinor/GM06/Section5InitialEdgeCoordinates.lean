module

public import GraphMinor.GM06.Section5CylinderProduct
import GraphMinor.GM06.Section5InitialEdgeParameter
import GraphMinor.GM06.Section5IntervalReparam
import GraphMinor.GM06.Section5ProperPaths
import GraphMinor.GM06.Section5SpanningPathCoordinates
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Interval.Set.OrderIso

/-!
# Coordinates for the initial edge

For Reduction 3 of VI, page 129, the edge at a vertex of valency one
is exactly an initial interval of the linkage parameter. An order
isomorphism puts its neighbour at any chosen interior height. The
spanning-path homeomorphism then identifies the entire closed edge
with precisely the corresponding initial part of the radial seam.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Under the actual hypotheses of Reduction 3, cylinder coordinates
identify the initial edge with an exact radial seam prefix, ending
at any prescribed interior height. The entire seam is the old linkage
path, so a narrow rectangle about it can avoid the other paths. -/
theorem exists_coordinates_of_initial_valency_one_edge
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2)
    (c : unitInterval) (hc : c ∈ Ioo (0 : unitInterval) 1) :
    ∃ K : ClosedCylinder ≃ₜ ClosedCylinder,
      K (section5CylinderProduct.symm (1, 0)) = cylinderM1Point k i ∧
      K (section5CylinderProduct.symm (1, c)) = v ∧
      closure e = (fun u => K (section5CylinderProduct.symm (1, u))) '' Icc 0 c ∧
      range (fun u => K (section5CylinderProduct.symm (1, u))) = (L.pathDrawing i).U := by
  obtain ⟨τ, hτ, hτv, hedge⟩ := exists_parameter_of_initial_valency_one_edge L i hval hl hvs hvC
  obtain ⟨a, ha⟩ := exists_unitInterval_orderIso_map_point τ c hτ hc
  have ha0 : a.symm 0 = 0 := a.symm.map_bot
  have hac : a.symm c = τ := by rw [← ha, a.symm_apply_apply]
  have ht : L.curve i 1 ∈ cylinderCuff2 := by
    obtain ⟨j, hj⟩ := L.curve_one_mem i
    rw [← hj]
    rfl
  obtain ⟨H, hH⟩ := exists_cylinder_coordinates_of_spanning_path (L.isPath i)
    (show cylinderM1Point k i ∈ cylinderCuff1 from rfl) ht (L.U_inter_boundary hG i)
    (L.curve i) (L.curve_parametrizes i)
  let J : Circle × unitInterval ≃ₜ Circle × unitInterval :=
    (Homeomorph.refl Circle).prodCongr a.symm.toHomeomorph
  let K := section5CylinderProduct.trans (J.trans H)
  have hK (u : unitInterval) : K (section5CylinderProduct.symm (1, u)) = L.curve i (a.symm u) := by
    change H (J (section5CylinderProduct (section5CylinderProduct.symm (1, u)))) = _
    rw [section5CylinderProduct.apply_symm_apply]
    exact hH (a.symm u)
  have hfun : (fun u => K (section5CylinderProduct.symm (1, u))) = (L.curve i) ∘ a.symm :=
    funext hK
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · rw [hK, ha0]
    exact (L.curve_parametrizes i).2.2.1
  · rw [hK, hac]
    exact hτv
  · rw [hfun]
    calc
      closure e = (L.curve i) '' Icc 0 τ := hedge
      _ = (L.curve i) '' (a.symm '' Icc 0 c) := by rw [a.symm.image_Icc, ha0, hac]
      _ = ((L.curve i) ∘ a.symm) '' Icc 0 c := image_image _ _ _
  · rw [hfun, range_comp, a.symm.surjective.range_eq, image_univ]
    exact (L.curve_parametrizes i).2.1

end GraphMinor.GM06
