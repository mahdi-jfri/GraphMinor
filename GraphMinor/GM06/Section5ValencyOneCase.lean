module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Reduction3Apply
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM11.Walks

/-!
# The valency-one case of (5.1)

A nondegenerate simple path has a non-loop first edge. Apply this to
the linkage path at a valency-one initial vertex. If no reduction is
available, Reduction 3 forces the other end onto the outer cuff.
This proves the first alternative of VI (5.1), page 129, whenever
there is an initial vertex of valency one.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Every nondegenerate path has a non-loop first edge. -/
theorem exists_nonloop_first_link
    {P : Drawing ClosedCylinder} {s t : ClosedCylinder} (hP : IsPathDrawing P s t) :
    ∃ e ∈ P.E, ∃ v, v ≠ s ∧ P.toGraph.IsLink e s v := by
  obtain ⟨W, hW, _, _⟩ := hP.1
  cases W with
  | nil _ => exact False.elim ((isPathDrawing_start_ne_end hP) rfl)
  | @cons s v t e hl R =>
    refine ⟨e, hl.1, v, ?_, hl⟩
    intro hvs
    exact (List.nodup_cons.mp hW).1 (hvs ▸ R.start_mem_support)

/-- The valency-one alternative of Graph Minors VI (5.1), page 129,
follows from the constructed Reduction 3, without any extra assumption
about the existence of a contraction. -/
theorem exists_cuff2_neighbour_of_valency_one
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1) :
    ∃ e ∈ G.E, ∃ t ∈ G.V ∩ cylinderCuff2,
      G.toGraph.IsLink e (cylinderM1Point k i) t := by
  obtain ⟨e, he, v, hvs, hlP⟩ := exists_nonloop_first_link (L.isPath i)
  have hl := ((L.isSubdrawing i).1.isLink_iff he).mp hlP
  exact ⟨e, hl.1, v, ⟨hl.2.2.1,
    neighbour_mem_cuff2_of_no_section5_reduction L hG hno i hval hl hvs⟩, hl⟩

end GraphMinor.GM06
