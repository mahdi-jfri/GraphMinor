module

public import GraphMinor.Compute.PlanarityRamFrameBudget
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range

/-!
# Vertex ownership in the DFS frames

Every discovered vertex is either in a live frame or in the completion
list, exactly once. Live-frame depths are their positions from the bottom.
These invariants give capacity for the next completion and, at discovery,
for a new frame. They also bound the depth assigned to a fresh child.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The live and completed vertex labels, used only in the proof invariant. -/
def ownedVertices (search : Search) (stack : List Frame) : List ℕ :=
  stack.map Frame.vertex ++ search.postorder

/-- Vertex ownership and the index/depth conditions of the explicit frames. -/
def FrameInvariant (adj : Array (List ℕ)) (search : Search) (stack : List Frame) : Prop :=
  search.depth.size = adj.size ∧
  (ownedVertices search stack).Nodup ∧
  (∀ v ∈ ownedVertices search stack, v < adj.size) ∧
  (∀ v : Fin adj.size, (search.depth[v.val]?.join).isSome ↔ v.val ∈ ownedVertices search stack) ∧
  (∀ j (hj : j < stack.length), stack[j].next ≤ adj[stack[j].vertex]!.length ∧
    search.depth[stack[j].vertex]?.join = some (stack.length - (j + 1)))

/-- The initial search has no owned or discovered vertex. -/
theorem FrameInvariant.initial (adj : Array (List ℕ)) :
    FrameInvariant adj (initialSearch adj.size) [] := by
  refine ⟨by simp [initialSearch], by simp [ownedVertices, initialSearch], ?_, ?_, ?_⟩
  · simp [ownedVertices, initialSearch]
  · intro v
    simp [initialSearch, v.isLt, ownedVertices]
  · intro j hj
    simp at hj

/-- Search fields other than depth and postorder do not enter this invariant. -/
theorem FrameInvariant.of_fields {adj : Array (List ℕ)} {search next : Search} {stack : List Frame}
    (h : FrameInvariant adj search stack) (hd : next.depth = search.depth)
    (hp : next.postorder = search.postorder) : FrameInvariant adj next stack := by
  simpa only [FrameInvariant, ownedVertices, hd, hp] using h

private theorem distinct_labels_length_le (vertices : List ℕ) (N : ℕ)
    (hn : vertices.Nodup) (hb : ∀ v ∈ vertices, v < N) : vertices.length ≤ N := by
  have hsub : vertices.toFinset ⊆ Finset.range N := by
    intro v hv
    exact Finset.mem_range.mpr (hb v (List.mem_toFinset.mp hv))
  have hh := Finset.card_le_card hsub
  simpa only [List.toFinset_card_of_nodup hn, Finset.card_range] using hh

/-- Live frames and completed vertices together fit in the vertex arrays. -/
theorem FrameInvariant.capacity {adj : Array (List ℕ)} {search : Search} {stack : List Frame}
    (h : FrameInvariant adj search stack) : stack.length + search.postorder.length ≤ adj.size := by
  have hh := distinct_labels_length_le (ownedVertices search stack) adj.size h.2.1 h.2.2.1
  simpa only [ownedVertices, List.length_append, List.length_map] using hh

/-- An undiscovered vertex is not already owned by a frame or completion. -/
theorem FrameInvariant.fresh_not_mem {adj : Array (List ℕ)} {search : Search} {stack : List Frame}
    (h : FrameInvariant adj search stack) (u : Fin adj.size)
    (hu : search.depth[u.val]?.join = none) : u.val ∉ ownedVertices search stack := by
  intro hm
  have hs := (h.2.2.2.1 u).mpr hm
  simp only [hu, Option.isSome_none, Bool.false_eq_true] at hs

/-- A fresh child leaves room for one more owned vertex and hence one frame. -/
theorem FrameInvariant.fresh_capacity {adj : Array (List ℕ)} {search : Search} {stack : List Frame}
    (h : FrameInvariant adj search stack) (u : Fin adj.size)
    (hu : search.depth[u.val]?.join = none) :
    stack.length + search.postorder.length + 1 ≤ adj.size := by
  have hn : (u.val :: ownedVertices search stack).Nodup :=
    List.nodup_cons.mpr ⟨h.fresh_not_mem u hu, h.2.1⟩
  have hb : ∀ v ∈ u.val :: ownedVertices search stack, v < adj.size := by
    intro v hv
    rcases List.mem_cons.mp hv with he | hm
    · exact he ▸ u.isLt
    · exact h.2.2.1 v hm
  have hh := distinct_labels_length_le _ adj.size hn hb
  simpa [ownedVertices, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-- A nonempty stack has a free completion slot. -/
theorem FrameInvariant.completion_room {adj : Array (List ℕ)} {search : Search}
    {f : Frame} {stack : List Frame} (h : FrameInvariant adj search (f :: stack)) :
    search.postorder.length < adj.size := by
  have hh := h.capacity
  simp only [List.length_cons] at hh
  omega

/-- The top frame's depth is the number of frames below it. -/
theorem FrameInvariant.top_depth {adj : Array (List ℕ)} {search : Search}
    {f : Frame} {stack : List Frame} (h : FrameInvariant adj search (f :: stack)) :
    search.depth[f.vertex]?.join = some stack.length := by
  have hh := (h.2.2.2.2 0 (by simp)).2
  simpa using hh

/-- The new child's depth is below the vertex count. -/
theorem FrameInvariant.child_depth_lt {adj : Array (List ℕ)} {search : Search}
    {f : Frame} {stack : List Frame} (h : FrameInvariant adj search (f :: stack))
    (u : Fin adj.size) (hu : search.depth[u.val]?.join = none) :
    (search.depth[f.vertex]?.join).getD 0 + 1 < adj.size := by
  have hh := h.fresh_capacity u hu
  simp only [List.length_cons] at hh
  rw [h.top_depth]
  simp only [Option.getD_some]
  omega

end GraphMinor.Compute.PlanarityRam
