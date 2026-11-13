module

public import GraphMinor.Compute.PlanarityRamDiscover
import GraphMinor.Compute.PlanarityRamFinish
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Remaining work in the frame search

The note's Part V counts adjacency scans and vertex completions. Unvisited
vertices retain their whole adjacency-list budget. Discovery transfers that
budget to a new frame. Scanning consumes one unit, and completion removes
one additional unit when vertex completions are counted.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity
open scoped BigOperators

/-- The work reserved for undiscovered vertices. -/
def unseenWork (N : ℕ) (depth : Array (Option ℕ)) (weight : Fin N → ℕ) : ℕ :=
  ∑ v : Fin N, if (depth[v.val]?.join).isNone then weight v else 0

/-- Discovering a fresh vertex removes exactly its reserved work. -/
theorem unseenWork_mark {N : ℕ} (depth : Array (Option ℕ)) (weight : Fin N → ℕ)
    (hsize : depth.size = N) (u : Fin N) (d : ℕ) (hu : depth[u.val]?.join = none) :
    unseenWork N depth weight = unseenWork N (depth.set! u.val (some d)) weight + weight u := by
  have hub : u.val < depth.size := hsize.symm ▸ u.isLt
  calc
    unseenWork N depth weight =
        ∑ v : Fin N, ((if ((depth.set! u.val (some d))[v.val]?.join).isNone then weight v else 0) +
          if v = u then weight v else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases he : v = u
      · subst v
        simp [hu, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hub]
      · have hne : u.val ≠ v.val := fun hv => he (Fin.ext hv.symm)
        simp [he, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hne]
    _ = unseenWork N (depth.set! u.val (some d)) weight + weight u := by
      rw [Finset.sum_add_distrib]
      simp [unseenWork]

/-- All vertices initially carry their full work budget. -/
theorem unseenWork_initial (N : ℕ) (weight : Fin N → ℕ) :
    unseenWork N (Array.replicate N none) weight = ∑ v, weight v := by
  apply Finset.sum_congr rfl
  intro v _
  simp [v.isLt]

/-- Work left in the live frames. A completion has weight zero or one. -/
def frameWork (adj : Array (List ℕ)) (completion : ℕ) (stack : List Frame) : ℕ :=
  (stack.map fun f => adj[f.vertex]!.length - f.next + completion).sum

/-- Undiscovered and active work together, without any cost for finished vertices. -/
def searchWork (adj : Array (List ℕ)) (completion : ℕ) (search : Search)
    (stack : List Frame) : ℕ :=
  unseenWork adj.size search.depth (fun v => adj[v.val]!.length + completion) +
    frameWork adj completion stack

/-- An adjacency scan consumes one work unit when discovery does not change
which vertices are visited. -/
theorem searchWork_advance (adj : Array (List ℕ)) (completion : ℕ) (search : Search)
    (f : Frame) (stack : List Frame) (hnext : f.next < adj[f.vertex]!.length) :
    searchWork adj completion search ({ f with next := f.next + 1 } :: stack) + 1 =
      searchWork adj completion search (f :: stack) := by
  simp only [searchWork, frameWork, List.map_cons, List.sum_cons]
  omega

/-- Completing a frame consumes just its completion weight. -/
theorem searchWork_complete (adj : Array (List ℕ)) (completion : ℕ) (search : Search)
    (f : Frame) (stack : List Frame) (hnext : adj[f.vertex]!.length ≤ f.next) :
    searchWork adj completion search stack + completion =
      searchWork adj completion search (f :: stack) := by
  simp only [searchWork, frameWork, List.map_cons, List.sum_cons]
  omega

/-- Discovery transfers the child's reserved work to its new frame. After
advancing the parent, one adjacency-scan unit has been consumed. -/
theorem searchWork_discover (adj : Array (List ℕ)) (completion : ℕ) (search : Search)
    (hsize : search.depth.size = adj.size) (f : Frame) (stack : List Frame)
    (u : Fin adj.size) (d : ℕ) (hu : search.depth[u.val]?.join = none)
    (hnext : f.next < adj[f.vertex]!.length) :
    searchWork adj completion { search with depth := search.depth.set! u.val (some d) }
      (⟨u.val, 0⟩ :: { f with next := f.next + 1 } :: stack) + 1 =
      searchWork adj completion search (f :: stack) := by
  have hmark := unseenWork_mark search.depth
    (fun v : Fin adj.size => adj[v.val]!.length + completion) hsize u d hu
  simp only [searchWork, frameWork, List.map_cons, List.sum_cons, Nat.sub_zero]
  omega

/-- Starting a component moves the fresh root's budget into its first frame. -/
theorem searchWork_start (adj : Array (List ℕ)) (completion : ℕ) (search : Search)
    (hsize : search.depth.size = adj.size) (u : Fin adj.size)
    (hu : search.depth[u.val]?.join = none) :
    searchWork adj completion { search with depth := search.depth.set! u.val (some 0) }
      [⟨u.val, 0⟩] = searchWork adj completion search [] := by
  have hmark := unseenWork_mark search.depth
    (fun v : Fin adj.size => adj[v.val]!.length + completion) hsize u 0 hu
  simpa [searchWork, frameWork] using hmark.symm

/-- Finishing an edge leaves the depth array fixed. -/
theorem finishEdge_depth (search : Search) (i : ℕ) :
    (finishEdge search i).depth = search.depth := by
  cases hpar : search.parentEdge[search.edges[i]!.source]?.join <;>
    simp [finishEdge_eq, setEdgeKey, setEdgePair, hpar]

/-- Finishing an edge does not create or remove any record. -/
theorem finishEdge_edges_size (search : Search) (i : ℕ) :
    (finishEdge search i).edges.size = search.edges.size := by
  cases hpar : search.parentEdge[search.edges[i]!.source]?.join <;>
    simp [finishEdge_eq, setEdgeKey, setEdgePair, hpar]

/-- The work measure uses no search field other than depth. -/
theorem searchWork_of_depth_eq (adj : Array (List ℕ)) (completion : ℕ)
    (search next : Search) (stack : List Frame) (h : next.depth = search.depth) :
    searchWork adj completion next stack = searchWork adj completion search stack := by
  simp only [searchWork, h]

end GraphMinor.Compute.PlanarityRam
