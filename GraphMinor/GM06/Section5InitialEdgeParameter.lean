module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section5InitialArcParameter
import Mathlib.Tactic

/-!
# The exact linkage prefix contracted by Reduction 3

In VI Reduction 3, page 129, the sole edge at the initial vertex is
the first edge of its linkage path. Valency one excludes every other
choice for that first edge. Its closure is therefore an initial
subarc of the linkage curve. If its neighbour is not on the outer
cuff, the endpoint of that subarc has an interior parameter.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

private theorem exists_initial_link_in_path
    {P : Drawing ClosedCylinder} {s t : ClosedCylinder} (hP : IsPathDrawing P s t) :
    ∃ f ∈ P.E, ∃ b, P.toGraph.IsLink f s b := by
  have hst := isPathDrawing_start_ne_end hP
  obtain ⟨W, _, _, _⟩ := hP.1
  cases W with
  | nil _ => exact False.elim (hst rfl)
  | @cons s b t f hl R => exact ⟨f, hl.1, b, hl⟩

/-- Under the hypotheses of Reduction 3, the closed incident edge is
exactly an initial parameter interval of the linkage curve, ending
at an interior parameter for its neighbour. -/
theorem exists_parameter_of_initial_valency_one_edge
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2) :
    ∃ τ ∈ Ioo (0 : unitInterval) 1,
      L.curve i τ = v ∧ closure e = (L.curve i) '' Icc 0 τ := by
  have heP : e ∈ (L.pathDrawing i).E := by
    obtain ⟨f, hf, b, hfl⟩ := exists_initial_link_in_path (L.isPath i)
    have hfG : G.toGraph.IsLink f (cylinderM1Point k i) b :=
      ((L.isSubdrawing i).1.isLink_iff hf).mp hfl
    have hscl : cylinderM1Point k i ∈ closure f ∩ G.V :=
      hfG.2.2.2 ▸ mem_insert _ _
    have hfe : f = e := by
      by_contra hn
      exact not_mem_closure_edge_of_ne_red3 hval hl hvs hfG.1 hn hscl.1
    exact hfe ▸ hf
  have hcl : closure e ⊆ (L.pathDrawing i).U := (L.pathDrawing i).closure_subset_U heP
  obtain ⟨g, hg⟩ := exists_parametrizesSet_closure_edge G hl hvs.symm
  have hterm : L.curve i 1 ∈ cylinderCuff2 := by
    obtain ⟨j, hj⟩ := L.curve_one_mem i
    rw [← hj]
    rfl
  have hsub : range g ⊆ range (L.curve i) := by
    rw [hg.2.1, (L.curve_parametrizes i).2.1]
    exact hcl
  have hstart : g 0 = L.curve i 0 := hg.2.2.1.trans (L.curve_parametrizes i).2.2.1.symm
  have hend : g 1 ≠ L.curve i 1 := by
    rw [hg.2.2.2]
    exact fun he => hvC (he.symm ▸ hterm)
  obtain ⟨τ, hτ, hτv, hr⟩ := exists_parameter_of_initial_subarc (L.curve i) g
    ⟨(L.curve i).continuous, (L.curve_parametrizes i).1⟩ ⟨g.continuous, hg.1⟩ hsub hstart hend
  rw [hg.2.2.2] at hτv
  rw [hg.2.1] at hr
  exact ⟨τ, hτ, hτv, hr⟩

end GraphMinor.GM06
