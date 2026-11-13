module

public import GraphMinor.Compute.PlanarityRamStep

/-!
# Invariants and work for one frame iteration

On well-formed adjacency lists, a nonempty frame step succeeds. It keeps
bounded data and vertex ownership, consumes one scan/completion unit, and
charges any new record to a consumed scan. These are properties of the
actual functional step, not assumptions about the RAM program.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- A valid nonempty iteration preserves the search invariants and the
record budget and consumes exactly one unit of the frame-work budget. -/
theorem frameStep_invariant (adj : Array (List ℕ))
    (hadj : ∀ v : Fin adj.size, ∀ u ∈ adj[v.val]!, u < adj.size)
    (search : Search) (f : Frame) (stack : List Frame)
    (hb : SearchBounded adj.size search) (hs : FrameInvariant adj search (f :: stack)) :
    ∃ next nextStack, frameStep adj search f stack = some (next, nextStack) ∧
      SearchBounded adj.size next ∧ FrameInvariant adj next nextStack ∧
      searchWork adj 1 next nextStack + 1 = searchWork adj 1 search (f :: stack) ∧
      next.edges.size + searchWork adj 0 next nextStack ≤
        search.edges.size + searchWork adj 0 search (f :: stack) := by
  have hv : f.vertex < adj.size := hs.2.2.1 _ (by simp [ownedVertices])
  by_cases hdone : f.next ≥ adj[f.vertex]!.length
  · let completed : Search := { search with postorder := f.vertex :: search.postorder }
    let next := finishIncoming completed f.vertex
    have hb' : SearchBounded adj.size completed := hb
    have hs' : FrameInvariant adj next stack := hs.complete.finishIncoming f.vertex
    have hd : next.depth = search.depth := finishIncoming_depth completed f.vertex
    have he : next.edges.size = search.edges.size := finishIncoming_edges_size completed f.vertex
    have hwork (c : ℕ) : searchWork adj c next stack + c =
        searchWork adj c search (f :: stack) := by
      rw [searchWork_of_depth_eq adj c search next stack hd]
      exact searchWork_complete adj c search f stack hdone
    refine ⟨next, stack, ?_, hb'.finishIncoming ⟨f.vertex, hv⟩, hs', hwork 1, ?_⟩
    · simp only [frameStep, hdone, ↓reduceIte]
      rfl
    · have hh := hwork 0
      omega
  · have hscan : f.next < adj[f.vertex]!.length := by omega
    generalize huExpr : adj[f.vertex]![f.next]! = u
    have hu : u < adj.size := by
      rw [← huExpr]
      exact scannedNeighbor_valid adj hadj f hscan
    have hurange : ¬u ≥ adj.size := by omega
    let advanced : Frame := { f with next := f.next + 1 }
    cases hdepth : search.depth[u]?.join with
    | none =>
      let next := discoverChild (addEdge search f.vertex u true).1 f.vertex u search.edges.size
      let nextStack : List Frame := ⟨u, 0⟩ :: advanced :: stack
      have he : next.edges.size = search.edges.size + 1 := by simp [next, discoverChild, addEdge]
      have hadded := hb.addEdge f.vertex u hv hu true
      have hb' : SearchBounded adj.size next := hadded.discoverChild f.vertex u search.edges.size
        hv hu (by simp [addEdge]) (hs.child_depth_lt ⟨u, hu⟩ hdepth)
      have hs' : FrameInvariant adj next nextStack := hs.discoverChild ⟨u, hu⟩ hdepth hscan
      have hwork (c : ℕ) : searchWork adj c next nextStack + 1 =
          searchWork adj c search (f :: stack) := by
        have hh := searchWork_discover adj c search hs.1 f stack ⟨u, hu⟩
          ((search.depth[f.vertex]?.join).getD 0 + 1) hdepth hscan
        simpa [next, nextStack, advanced, discoverChild, addEdge, searchWork] using hh
      refine ⟨next, nextStack, ?_, hb', hs', hwork 1, ?_⟩
      · simp only [frameStep, hdone, huExpr, hurange, hdepth, Option.isNone_none, ↓reduceIte]
        rfl
      · have hh := hwork 0
        omega
    | some depth =>
      by_cases hback : search.parent[f.vertex]?.join ≠ some u ∧
          depth < (search.depth[f.vertex]?.join).getD 0
      · let next := finishEdge (addEdge search f.vertex u false).1 search.edges.size
        have hadded := hb.addEdge f.vertex u hv hu false
        have hi : search.edges.size < (addEdge search f.vertex u false).1.edges.size := by simp [addEdge]
        have hb' : SearchBounded adj.size next := hadded.finishEdge search.edges.size hi
        have hd : next.depth = search.depth := finishEdge_depth _ _
        have hp : next.postorder = search.postorder := finishEdge_postorder _ _
        have hs' : FrameInvariant adj next (advanced :: stack) := (hs.advance hscan).of_fields hd hp
        have he : next.edges.size = search.edges.size + 1 := by
          simpa [next, addEdge] using finishEdge_edges_size (addEdge search f.vertex u false).1 search.edges.size
        have hwork (c : ℕ) : searchWork adj c next (advanced :: stack) + 1 =
            searchWork adj c search (f :: stack) := by
          rw [searchWork_of_depth_eq adj c search next (advanced :: stack) hd]
          exact searchWork_advance adj c search f stack hscan
        refine ⟨next, advanced :: stack, ?_, hb', hs', hwork 1, ?_⟩
        · simp only [frameStep, hdone, huExpr, hurange, hdepth, Option.isNone_some,
            Bool.false_eq_true, Option.getD_some, hback.2, ↓reduceIte]
          split
          · rfl
          · rename_i hnback
            exact False.elim (hnback ⟨hback.1, True.intro⟩)
        · have hh := hwork 0
          omega
      · have hwork (c : ℕ) := searchWork_advance adj c search f stack hscan
        refine ⟨search, advanced :: stack, ?_, hb, hs.advance hscan, hwork 1, ?_⟩
        · simp only [frameStep, hdone, huExpr, hurange, hdepth, Option.isNone_some,
            Bool.false_eq_true, Option.getD_some, hback, ↓reduceIte]
          rfl
        · have hh := hwork 0
          change search.edges.size + searchWork adj 0 search ({ f with next := f.next + 1 } :: stack) ≤ _
          omega

end GraphMinor.Compute.PlanarityRam
