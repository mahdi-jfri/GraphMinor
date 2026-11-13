module

public import GraphMinor.GM01.Defs
public import GraphMinor.GM09.Basic
import GraphMinor.GM01.SimplePathSeparators
import GraphMinor.GM01.Basic
import Mathlib.Combinatorics.Graph.Simple

/-!
# Lifting a simplified path to its original graph

The use of (2.9) on page 60 of Graph Minors I passes through the
underlying simple graph. Choose an original edge for each step of
its simple walk. The lifted walk has exactly the same vertices under
subtype inclusion, so it is still simple. Its walk subgraph is an
actual path of the original graph with the exact image vertex set.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09 GraphMinor.Surface

private noncomputable def liftSimpleWalk {α β : Type*} (G : Graph α β)
    {a b : V(G)} : G.toSimpleGraph.Walk a b → GraphWalk G a.val b.val
  | .nil => .nil a.property
  | .cons hadj rest => .cons (Classical.choose_spec hadj.2) (liftSimpleWalk G rest)

private theorem liftSimpleWalk_support {α β : Type*} (G : Graph α β)
    {a b : V(G)} (w : G.toSimpleGraph.Walk a b) :
    (liftSimpleWalk G w).support = w.support.map Subtype.val := by
  induction w with
  | nil => rfl
  | cons hadj rest ih =>
    simp only [liftSimpleWalk,GraphWalk.support_cons,Walk.support_cons,List.map_cons,ih]

/-- A Section 2 path of the underlying simple graph lifts to an actual
path with its exact image vertex set, as needed for GM01 (2.9), page 60. -/
theorem exists_graph_path_of_simple_path {α β : Type*} (G : Graph α β) (P : Path V(G))
    (hP : P.toSubgraph ≤ SimpleGraph.toSubgraph G.toSimpleGraph le_top) :
    ∃ Q : Graph α β, IsGraphPathWithEnds G Q P.first.val P.last.val ∧
      V(Q) = Subtype.val '' P.verts := by
  obtain ⟨w,hSupport,hw⟩ := lift_path_to_simpleGraph G.toSimpleGraph P hP
  let W := liftSimpleWalk G w
  have hW : W.IsSimple := by
    change (liftSimpleWalk G w).support.Nodup
    rw [liftSimpleWalk_support]
    exact hw.support_nodup.map Subtype.val_injective
  refine ⟨walkSubgraph W,isGraphPathWithEnds_walkSubgraph hW,?_⟩
  rw [vertexSet_walkSubgraph]
  ext x
  change x ∈ (liftSimpleWalk G w).support ↔ x ∈ Subtype.val '' P.verts
  rw [liftSimpleWalk_support,hSupport]
  simp only [List.mem_map,mem_image,Path.mem_verts_iff]

end GraphMinor.GM01
