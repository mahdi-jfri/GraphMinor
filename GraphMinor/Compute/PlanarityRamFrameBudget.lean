module

public import GraphMinor.Compute.PlanarityRamWork

/-!
# Fuel for the functional frame search

Each nonempty-frame step consumes one unit of the remaining-work measure.
Discovery transfers rather than duplicates a child's unscanned incidences.
Consequently sufficient fuel gives a successful functional search on lists
whose neighbors are in range. This is the fuel argument used in comparing
the RAM component loop with `searchFrames`.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- A frame with an unscanned entry names a valid vertex and a valid neighbor. -/
theorem scannedNeighbor_valid (adj : Array (List ℕ))
    (hadj : ∀ v : Fin adj.size, ∀ u ∈ adj[v.val]!, u < adj.size)
    (f : Frame) (hscan : f.next < adj[f.vertex]!.length) :
    adj[f.vertex]![f.next]! < adj.size := by
  have hv : f.vertex < adj.size := by
    by_contra hn
    have he : adj[f.vertex]! = [] := getElem!_neg adj f.vertex hn
    simp only [he, List.length_nil] at hscan
    omega
  have hm : adj[f.vertex]![f.next]! ∈ adj[f.vertex]! := by
    rw [getElem!_pos (adj[f.vertex]!) f.next hscan]
    exact List.getElem_mem hscan
  exact hadj ⟨f.vertex, hv⟩ _ hm

/-- With more fuel than remaining work, the frame search returns a search,
keeps the depth-array size, and leaves no more work than it started with.
Each newly created record is charged to a consumed adjacency-scan unit. -/
theorem searchFrames_budget (adj : Array (List ℕ))
    (hadj : ∀ v : Fin adj.size, ∀ u ∈ adj[v.val]!, u < adj.size)
    (fuel : ℕ) (search : Search) (stack : List Frame)
    (hsize : search.depth.size = adj.size)
    (hfuel : searchWork adj 1 search stack < fuel) :
    ∃ result, searchFrames adj fuel search stack = some result ∧
      result.depth.size = adj.size ∧ searchWork adj 1 result [] ≤ searchWork adj 1 search stack ∧
      result.edges.size + searchWork adj 0 result [] ≤ search.edges.size + searchWork adj 0 search stack := by
  induction fuel generalizing search stack with
  | zero => omega
  | succ fuel ih =>
    cases stack with
    | nil => exact ⟨search, rfl, hsize, le_rfl, le_rfl⟩
    | cons f stack =>
      by_cases hdone : adj[f.vertex]!.length ≤ f.next
      · let completed : Search := { search with postorder := f.vertex :: search.postorder }
        let next : Search := match search.parentEdge[f.vertex]?.join with
          | none => completed
          | some p => finishEdge completed p
        have hd : next.depth = search.depth := by
          dsimp only [next]
          split
          · rfl
          · exact finishEdge_depth completed _
        have hs : next.depth.size = adj.size := hd ▸ hsize
        have hwork : searchWork adj 1 next stack + 1 = searchWork adj 1 search (f :: stack) := by
          rw [searchWork_of_depth_eq adj 1 search next stack hd]
          exact searchWork_complete adj 1 search f stack hdone
        have hwork0 : searchWork adj 0 next stack = searchWork adj 0 search (f :: stack) := by
          rw [searchWork_of_depth_eq adj 0 search next stack hd]
          simpa using searchWork_complete adj 0 search f stack hdone
        have he : next.edges.size = search.edges.size := by
          dsimp only [next]
          split
          · rfl
          · exact finishEdge_edges_size completed _
        obtain ⟨result, hex, hresult, hbound, hbound0⟩ := ih next stack hs (by omega)
        refine ⟨result, ?_, hresult, by omega, by omega⟩
        rw [searchFrames]
        simp only [hdone, ↓reduceIte]
        change searchFrames adj fuel next stack = some result
        exact hex
      · have hscan : f.next < adj[f.vertex]!.length := by omega
        generalize huExpr : adj[f.vertex]![f.next]! = u
        have hu : u < adj.size := by
          rw [← huExpr]
          exact scannedNeighbor_valid adj hadj f hscan
        have hurange : ¬u ≥ adj.size := by omega
        let advanced : Frame := { f with next := f.next + 1 }
        cases hdepth : search.depth[u]?.join with
        | none =>
          let d := (search.depth[f.vertex]?.join).getD 0 + 1
          let next := discoverChild (addEdge search f.vertex u true).1 f.vertex u search.edges.size
          have hs : next.depth.size = adj.size := by
            simpa [next, discoverChild, addEdge] using hsize
          have hwork : searchWork adj 1 next (⟨u, 0⟩ :: advanced :: stack) + 1 =
              searchWork adj 1 search (f :: stack) := by
            have hh := searchWork_discover adj 1 search hsize f stack ⟨u, hu⟩ d hdepth hscan
            simpa [next, discoverChild, addEdge, advanced, d, searchWork] using hh
          have hwork0 : searchWork adj 0 next (⟨u, 0⟩ :: advanced :: stack) + 1 =
              searchWork adj 0 search (f :: stack) := by
            have hh := searchWork_discover adj 0 search hsize f stack ⟨u, hu⟩ d hdepth hscan
            simpa [next, discoverChild, addEdge, advanced, d, searchWork] using hh
          have he : next.edges.size = search.edges.size + 1 := by simp [next, discoverChild, addEdge]
          obtain ⟨result, hex, hresult, hbound, hbound0⟩ := ih next (⟨u, 0⟩ :: advanced :: stack) hs (by omega)
          refine ⟨result, ?_, hresult, by omega, by omega⟩
          rw [searchFrames]
          simp only [hdone, huExpr, hurange, hdepth, Option.isNone_none, ↓reduceIte]
          change searchFrames adj fuel next (⟨u, 0⟩ :: advanced :: stack) = some result
          exact hex
        | some depth =>
          by_cases hback : search.parent[f.vertex]?.join ≠ some u ∧
              depth < (search.depth[f.vertex]?.join).getD 0
          · let next := finishEdge (addEdge search f.vertex u false).1 search.edges.size
            have hd : next.depth = search.depth := finishEdge_depth _ _
            have hs : next.depth.size = adj.size := hd ▸ hsize
            have hwork : searchWork adj 1 next (advanced :: stack) + 1 =
                searchWork adj 1 search (f :: stack) := by
              rw [searchWork_of_depth_eq adj 1 search next (advanced :: stack) hd]
              exact searchWork_advance adj 1 search f stack hscan
            have hwork0 : searchWork adj 0 next (advanced :: stack) + 1 =
                searchWork adj 0 search (f :: stack) := by
              rw [searchWork_of_depth_eq adj 0 search next (advanced :: stack) hd]
              exact searchWork_advance adj 0 search f stack hscan
            have he : next.edges.size = search.edges.size + 1 := by
              simpa [next, addEdge] using finishEdge_edges_size (addEdge search f.vertex u false).1 search.edges.size
            obtain ⟨result, hex, hresult, hbound, hbound0⟩ := ih next (advanced :: stack) hs (by omega)
            refine ⟨result, ?_, hresult, by omega, by omega⟩
            rw [searchFrames]
            simp only [hdone, huExpr, hurange, hdepth, Option.isNone_some, Bool.false_eq_true,
              Option.getD_some, hback.2, ↓reduceIte]
            split
            · change searchFrames adj fuel next (advanced :: stack) = some result
              exact hex
            · rename_i hnback
              exact False.elim (hnback ⟨hback.1, True.intro⟩)
          · have hwork := searchWork_advance adj 1 search f stack hscan
            have hwork0 := searchWork_advance adj 0 search f stack hscan
            obtain ⟨result, hex, hresult, hbound, hbound0⟩ := ih search (advanced :: stack) hsize (by
              change searchWork adj 1 search ({ f with next := f.next + 1 } :: stack) < fuel
              omega)
            refine ⟨result, ?_, hresult, by dsimp only [advanced] at hbound; omega,
              by dsimp only [advanced] at hbound0; omega⟩
            rw [searchFrames]
            simp only [hdone, huExpr, hurange, hdepth, Option.isNone_some, Bool.false_eq_true,
              Option.getD_some, hback, ↓reduceIte]
            change searchFrames adj fuel search (advanced :: stack) = some result
            exact hex

end GraphMinor.Compute.PlanarityRam
