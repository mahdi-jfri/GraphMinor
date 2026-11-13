module

public import GraphMinor.Compute.GM06Alg511FlowGraph
public import GraphMinor.GM11.Walks
public import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic

/-!
# Transferring the initial flow paths to the drawing graph

The maximum-flow search in VI (5.11), page 134, uses the finite graph
of endpoint labels. A walk returned by that search lifts to a walk in
the actual drawing graph. The vertex sequence is exactly the image
of the label sequence. Thus a simple output path stays simple. The
edge witnesses here occur only in a mathematical existence proof,
not in the supplied input or an executable encoder.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.GM11 GraphMinor.Surface

/-- Every walk in the finite flow graph has a walk in the actual graph
with exactly the same labelled vertex sequence. -/
theorem alg511_exists_graphWalk_of_flowWalk (x : GM06Alg511Input)
    {α : Type*} {β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G)
    {a b : Fin x.vertexCount} (p : x.flowGraph.Walk a b) :
    ∃ W : GraphWalk G (rep.vertex a).val (rep.vertex b).val,
      W.support = p.support.map (fun i => (rep.vertex i).val) := by
  induction p with
  | nil => exact ⟨.nil (rep.vertex _).property, rfl⟩
  | @cons a c b hac p ih =>
    obtain ⟨e, he⟩ := ((x.flowGraph_adj_iff rep a c).mp hac).2
    obtain ⟨W, hW⟩ := ih
    refine ⟨.cons he W, ?_⟩
    rw [GraphWalk.support_cons, hW]
    rfl

/-- A simple path returned by the initial flow search lifts to a simple
walk, preserving its full vertex sequence. -/
theorem alg511_exists_simple_graphWalk_of_flowPath (x : GM06Alg511Input)
    {α : Type*} {β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G)
    {a b : Fin x.vertexCount} (p : x.flowGraph.Walk a b) (hp : p.IsPath) :
    ∃ W : GraphWalk G (rep.vertex a).val (rep.vertex b).val,
      W.IsSimple ∧ W.support = p.support.map (fun i => (rep.vertex i).val) := by
  obtain ⟨W, hW⟩ := alg511_exists_graphWalk_of_flowWalk x rep p
  refine ⟨W, ?_, hW⟩
  change W.support.Nodup
  rw [hW]
  exact hp.support_nodup.map (Subtype.val_injective.comp rep.vertex.injective)

end GraphMinor.GM06
