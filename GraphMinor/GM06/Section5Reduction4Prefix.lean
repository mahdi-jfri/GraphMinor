module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5InitialPathEdgeNotIncident
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM11.Walks

/-!
# Every nontrivial old prefix misses part of the region boundary

For Reduction 4 in the proof of VI (5.1), page 129, a subpath from
sᵢ to any later vertex contains an initial edge of Pᵢ. At a start of
valency different from one that edge is not incident with Rᵢ. Thus
no such prefix can lie wholly in the region closure.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

private theorem exists_initial_edge_closure_of_path
    {P : Drawing ClosedCylinder} {s t : ClosedCylinder} (hP : IsPathDrawing P s t) :
    ∃ e ∈ P.E, s ∈ closure e := by
  obtain ⟨W, _, _, _⟩ := hP.1
  cases W with
  | nil _ => exact False.elim ((isPathDrawing_start_ne_end hP) rfl)
  | @cons s v t e hl R =>
    exact ⟨e, hl.1, (show s ∈ closure e ∩ P.V from hl.2.2.2.symm ▸ mem_insert s {v}).1⟩

/-- Every nondegenerate initial subpath has a point outside the
following region closure at a start of valency different from one.
This supplies the old-prefix condition of Reduction 4 in VI (5.1). -/
theorem initial_subpath_not_subset_region_closure
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {A : Drawing ClosedCylinder} {v : ClosedCylinder}
    (hA : IsSubpathOf (L.pathDrawing i) A (cylinderM1Point k i) v) :
    ¬ A.U ⊆ closure (cylinderRegion k G i) := by
  obtain ⟨e, he, hse⟩ := exists_initial_edge_closure_of_path hA.2.2
  intro hAU
  exact initial_path_edge_not_subset_region_closure L hk hG hθ hno i hval (hA.1.2 he) hse
    (fun x hx => hAU ((he.2.1 hx).1))

end GraphMinor.GM06
