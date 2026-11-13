module

public import GraphMinor.Compute.PlanarityRamComplete
public import GraphMinor.Compute.PlanarityRamShapeStep
public import GraphMinor.Compute.PlanarityRamBoundedDiscover
import Mathlib.Tactic.SplitIfs

/-!
# One functional frame step

This exposes one iteration of `searchFrames` without consuming its fuel.
The exhausted, tree-child, back-edge, and ignored-incidence branches are
unchanged. The step form lets the RAM while-loop proof use the same
remaining-work measure as the functional fuel proof.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- One nonempty-frame iteration, with the same malformed-neighbor check
as the functional search. -/
def frameStep (adj : Array (List ℕ)) (search : Search) (f : Frame) (stack : List Frame) :
    Option (Search × List Frame) :=
  if f.next ≥ adj[f.vertex]!.length then
    some (finishIncoming { search with postorder := f.vertex :: search.postorder } f.vertex, stack)
  else
    let u := adj[f.vertex]![f.next]!
    if u ≥ adj.size then none
    else
      let advanced : Frame := { f with next := f.next + 1 }
      if (search.depth[u]?.join).isNone then
        some (discoverChild (addEdge search f.vertex u true).1 f.vertex u search.edges.size,
          ⟨u, 0⟩ :: advanced :: stack)
      else if search.parent[f.vertex]?.join ≠ some u ∧
          (search.depth[u]?.join).getD 0 < (search.depth[f.vertex]?.join).getD 0 then
        some (finishEdge (addEdge search f.vertex u false).1 search.edges.size, advanced :: stack)
      else some (search, advanced :: stack)

/-- The step function is exactly the successor-fuel equation of `searchFrames`. -/
theorem searchFrames_step (adj : Array (List ℕ)) (fuel : ℕ) (search : Search)
    (f : Frame) (stack : List Frame) :
    searchFrames adj (fuel + 1) search (f :: stack) =
      (frameStep adj search f stack).bind fun next => searchFrames adj fuel next.1 next.2 := by
  rw [searchFrames]
  unfold frameStep finishIncoming discoverChild
  dsimp only [Id.run, LRPlanarity.addEdge]
  split_ifs <;> rfl

/-- Finishing an edge leaves the completion list fixed. -/
theorem finishEdge_postorder (search : Search) (i : ℕ) :
    (finishEdge search i).postorder = search.postorder := by
  cases hp : search.parentEdge[search.edges[i]!.source]?.join <;>
    simp [finishEdge_eq, setEdgeKey, setEdgePair, hp]

/-- The optional incoming-edge update leaves depths fixed. -/
theorem finishIncoming_depth (search : Search) (v : ℕ) :
    (finishIncoming search v).depth = search.depth := by
  unfold finishIncoming
  split
  · rfl
  · exact finishEdge_depth search _

/-- The optional incoming-edge update leaves completions fixed. -/
theorem finishIncoming_postorder (search : Search) (v : ℕ) :
    (finishIncoming search v).postorder = search.postorder := by
  unfold finishIncoming
  split
  · rfl
  · exact finishEdge_postorder search _

/-- The optional incoming-edge update allocates no edge record. -/
theorem finishIncoming_edges_size (search : Search) (v : ℕ) :
    (finishIncoming search v).edges.size = search.edges.size := by
  unfold finishIncoming
  split
  · rfl
  · exact finishEdge_edges_size search _

/-- An incoming-edge update preserves all bounded-data conditions at a valid vertex. -/
theorem SearchBounded.finishIncoming {N : ℕ} {search : Search} (h : SearchBounded N search)
    (v : Fin N) : SearchBounded N (finishIncoming search v.val) := by
  unfold PlanarityRam.finishIncoming
  split
  · exact h
  · rename_i p hp
    exact h.finishEdge p (h.2.2.2.2.2.1 v p hp)

/-- Finishing an edge preserves the frame ownership invariant. -/
theorem FrameInvariant.finishEdge {adj : Array (List ℕ)} {search : Search} {stack : List Frame}
    (h : FrameInvariant adj search stack) (i : ℕ) : FrameInvariant adj (finishEdge search i) stack :=
  h.of_fields (finishEdge_depth search i) (finishEdge_postorder search i)

/-- The optional incoming-edge update preserves frame ownership. -/
theorem FrameInvariant.finishIncoming {adj : Array (List ℕ)} {search : Search} {stack : List Frame}
    (h : FrameInvariant adj search stack) (v : ℕ) : FrameInvariant adj (finishIncoming search v) stack :=
  h.of_fields (finishIncoming_depth search v) (finishIncoming_postorder search v)

end GraphMinor.Compute.PlanarityRam
