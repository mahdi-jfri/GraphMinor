module

public import GraphMinor.GM02.Feasibility
public import Mathlib.Combinatorics.Graph.Delete

/-!
# Retaining paths after vertex deletion

A pair path avoiding a set of vertices remains a path after deleting
that set. Transfer each edge using its original link and the avoidance
of its two endpoints. The support does not change. This supplies the
paths in the corrected induced graphs of II (2.9).
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v
variable {α : Type u} {β : Type v} {G : Graph α β} {p : Sym2 α}

/-- Every edge of an avoiding path survives vertex deletion. -/
theorem PairPath.edges_deleteVerts (P : PairPath (pathGraph G) p) (X : Set α)
    (hX : Disjoint P.vertices X) {e : Sym2 α} (he : e ∈ P.walk.edges) :
    e ∈ (pathGraph (G.deleteVerts X)).edgeSet := by
  obtain ⟨⟨a, b⟩, rfl⟩ := e.exists_rep
  have hab := (SimpleGraph.mem_edgeSet _).1 (P.walk.edges_subset_edgeSet he)
  have ha : a ∉ X := fun hx => Set.disjoint_left.1 hX (P.walk.fst_mem_support_of_mem_edges he) hx
  have hb : b ∉ X := fun hx => Set.disjoint_left.1 hX (P.walk.snd_mem_support_of_mem_edges he) hx
  obtain ⟨f, hf⟩ := hab.1
  exact (SimpleGraph.mem_edgeSet _).2 ⟨⟨f, (G.deleteVerts_isLink X).2 ⟨hf, ha, hb⟩⟩, hab.2⟩

/-- Regard an avoiding pair path as a path after vertex deletion. -/
noncomputable def PairPath.deleteVerts (P : PairPath (pathGraph G) p) (X : Set α)
    (hX : Disjoint P.vertices X) : PairPath (pathGraph (G.deleteVerts X)) p where
  start := P.start
  finish := P.finish
  ends_eq := P.ends_eq
  walk := P.walk.transfer _ (fun _ he => P.edges_deleteVerts X hX he)
  isPath := P.isPath.transfer _

/-- Deleting avoided vertices preserves the path's support. -/
theorem PairPath.deleteVerts_vertices (P : PairPath (pathGraph G) p) (X : Set α)
    (hX : Disjoint P.vertices X) : (P.deleteVerts X hX).vertices = P.vertices := by
  exact congrArg (fun l => {a | a ∈ l}) (Walk.support_transfer _ _)

end GraphMinor.GM02
