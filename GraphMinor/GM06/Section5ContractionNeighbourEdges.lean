module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5InitialEdgeSuffix
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section5InitialEdgeParameter
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5DeletedInitialEdge
import GraphMinor.GM11.Walks

/-!
# Two old edges at the contraction neighbour

In Reduction 3 of VI (5.5), page 130, the neighbour is not on the
terminal cuff. The linkage therefore continues through a second
edge after its initial edge. The suffix lies in the drawing with
the initial vertex deleted, so the second edge differs from the
contracted edge. These edges supply the neighbour's polar chart.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The neighbour in Reduction 3 has a second incident edge, given
by the nondegenerate linkage suffix after the contracted edge. -/
theorem exists_second_edge_at_contraction_neighbour
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2) :
    ∃ f ∈ G.E, f ≠ e ∧ v ∈ closure f := by
  obtain ⟨B, hB, hBJ, _⟩ := exists_suffix_of_initial_valency_one_edge L i hval hl hv hvC
  let J := induceDrawing G (G.V \ {cylinderM1Point k i})
  have hJE : J.E = G.E \ {e} := (deleted_initial_vertex_drawing hval hl hv).1
  have hfirst : ∃ f w, B.toGraph.IsLink f v w := by
    obtain ⟨W, _, _, _⟩ := hB.1
    cases W with
    | nil _ => exact False.elim ((isPathDrawing_start_ne_end hB) rfl)
    | @cons a b c f hlf R => exact ⟨f, b, hlf⟩
  obtain ⟨f, w, hlf⟩ := hfirst
  have hlfJ := (hBJ.isLink_iff hlf.1).1 hlf
  have hfJ : f ∈ J.E := hlfJ.1
  have hfGE : f ∈ G.E \ {e} := hJE ▸ hfJ
  have hvf : v ∈ closure f := by
    have hh : v ∈ closure f ∩ J.V := hlfJ.2.2.2 ▸ mem_insert v {w}
    exact hh.1
  exact ⟨f, hfGE.1, fun heq => hfGE.2 (mem_singleton_iff.mpr heq), hvf⟩

/-- The old neighbour in Reduction 3 lies off both cuffs: another
initial vertex would violate disjointness of the linkage paths. -/
theorem contraction_neighbour_not_mem_boundary
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2) :
    v ∉ bd ClosedCylinder := by
  intro hvbd
  have hvM : v ∈ cylinderM1 k ∪ cylinderM2 k := hG.2.2 ▸ ⟨hl.2.2.1, hvbd⟩
  rcases hvM with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨τ, _, hτv, _⟩ := exists_parameter_of_initial_valency_one_edge L i hval hl hv hvC
    have hvPi : v ∈ (L.pathDrawing i).U :=
      (L.curve_parametrizes i).2.1 ▸ ⟨τ, hτv⟩
    have hji : j ≠ i := by
      intro he
      exact hv (hj.symm.trans (congrArg (cylinderM1Point k) he))
    have hvPj : v ∈ (L.pathDrawing j).U :=
      (L.curve_parametrizes j).2.1 ▸ ⟨0, (L.curve_parametrizes j).2.2.1.trans hj⟩
    exact disjoint_left.mp (L.pairwise_disjoint hji.symm) hvPi hvPj
  · exact hvC (hj ▸ (show cylinderM2Point k j ∈ cylinderCuff2 from rfl))

end GraphMinor.GM06
