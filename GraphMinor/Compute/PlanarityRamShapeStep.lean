module

public import GraphMinor.Compute.PlanarityRamShape

/-!
# Preserving vertex ownership at a frame step

Discovery moves a fresh vertex into the live stack. Completion moves the
top vertex into the completion list. Advancing a frame changes neither
ownership nor depths. These proofs maintain the capacity and depth
invariants used by the RAM loop.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Discovery pushes a fresh vertex at depth equal to the old stack length. -/
theorem FrameInvariant.push_discovered {adj : Array (List ℕ)} {search : Search} {stack : List Frame}
    (h : FrameInvariant adj search stack) (u : Fin adj.size)
    (hu : search.depth[u.val]?.join = none) :
    FrameInvariant adj { search with depth := search.depth.set! u.val (some stack.length) }
      (⟨u.val, 0⟩ :: stack) := by
  have hub : u.val < search.depth.size := h.1.symm ▸ u.isLt
  have hnot := h.fresh_not_mem u hu
  refine ⟨by simpa using h.1, ?_, ?_, ?_, ?_⟩
  · simpa [ownedVertices] using List.nodup_cons.mpr ⟨hnot, h.2.1⟩
  · intro v hv
    change v ∈ u.val :: ownedVertices search stack at hv
    rcases List.mem_cons.mp hv with he | hm
    · exact he ▸ u.isLt
    · exact h.2.2.1 v hm
  · intro v
    change ((search.depth.set! u.val (some stack.length))[v.val]?.join).isSome ↔
      v.val ∈ u.val :: ownedVertices search stack
    by_cases he : v.val = u.val
    · rw [he]
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hub]
    · have hneq : u.val ≠ v.val := Ne.symm he
      have heval : (search.depth.set! u.val (some stack.length))[v.val]? = search.depth[v.val]? := by
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hneq]
      simpa only [heval, List.mem_cons, he, false_or] using h.2.2.2.1 v
  · intro j hj
    cases j with
    | zero =>
      refine ⟨Nat.zero_le _, ?_⟩
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hub]
    | succ j =>
      have hj' : j < stack.length := by simpa using hj
      have old := h.2.2.2.2 j hj'
      have hm : stack[j].vertex ∈ ownedVertices search stack := by
        apply List.mem_append_left
        exact List.mem_map_of_mem (List.getElem_mem hj')
      have hneq : u.val ≠ stack[j].vertex := by
        intro he
        exact hnot (he ▸ hm)
      refine ⟨old.1, ?_⟩
      simp only [List.getElem_cons_succ, List.length_cons]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hneq, old.2]
      congr 1
      omega

/-- Advancing a nonexhausted frame preserves ownership and its frame-depth relation. -/
theorem FrameInvariant.advance {adj : Array (List ℕ)} {search : Search}
    {f : Frame} {stack : List Frame} (h : FrameInvariant adj search (f :: stack))
    (hscan : f.next < adj[f.vertex]!.length) :
    FrameInvariant adj search ({ f with next := f.next + 1 } :: stack) := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro j hj
  cases j with
  | zero =>
    refine ⟨hscan, ?_⟩
    exact (h.2.2.2.2 0 (by simp)).2
  | succ j => exact h.2.2.2.2 (j + 1) hj

/-- Completion transfers the top vertex into postorder, preserving all ownership. -/
theorem FrameInvariant.complete {adj : Array (List ℕ)} {search : Search}
    {f : Frame} {stack : List Frame} (h : FrameInvariant adj search (f :: stack)) :
    FrameInvariant adj { search with postorder := f.vertex :: search.postorder } stack := by
  have hperm : (ownedVertices { search with postorder := f.vertex :: search.postorder } stack).Perm
      (ownedVertices search (f :: stack)) := List.perm_middle
  refine ⟨h.1, hperm.nodup_iff.mpr h.2.1, ?_, ?_, ?_⟩
  · intro v hv
    exact h.2.2.1 v (hperm.mem_iff.mp hv)
  · intro v
    exact (h.2.2.2.1 v).trans hperm.mem_iff.symm
  · intro j hj
    have old := h.2.2.2.2 (j + 1) (by simp; omega)
    refine ⟨old.1, ?_⟩
    simp only [List.getElem_cons_succ, List.length_cons] at old
    have he : stack.length + 1 - (j + 1 + 1) = stack.length - (j + 1) := by omega
    simpa only [he] using old.2

/-- The tree-child state and new frame preserve the full ownership invariant. -/
theorem FrameInvariant.discoverChild {adj : Array (List ℕ)} {search : Search}
    {f : Frame} {stack : List Frame} (h : FrameInvariant adj search (f :: stack))
    (u : Fin adj.size) (hu : search.depth[u.val]?.join = none)
    (hscan : f.next < adj[f.vertex]!.length) :
    FrameInvariant adj
      (discoverChild (addEdge search f.vertex u.val true).1 f.vertex u.val search.edges.size)
      (⟨u.val, 0⟩ :: { f with next := f.next + 1 } :: stack) := by
  have hm := (h.advance hscan).push_discovered u hu
  apply hm.of_fields
  · simp [PlanarityRam.discoverChild, addEdge, h.top_depth]
  · rfl

end GraphMinor.Compute.PlanarityRam
