module

public import GraphMinor.Compute.GM02ActiveEdges
public import GraphMinor.Compute.GM02TopologicalInputFacts

/-!
# The host flags after a prefix of loop removal

Whether a supplied host edge is a loop at a pattern vertex depends only
on its two supplied endpoints and the fixed pattern vertex set. After
processing the first `j` host edges, exactly those qualifying positions
below `j` have been cleared. Positions not yet processed still have
flag one, so each next qualifying edge is an actual active host loop.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- Test whether the supplied host edge is a loop at a supplied pattern vertex. -/
def gm02HostBranchLoopTest (x : GM02TopologicalInput) (e : Fin x.G.edges.length) : Bool :=
  decide ((x.G.edges[e.val]'e.isLt).1 = (x.G.edges[e.val]'e.isLt).2 ∧
    (x.G.edges[e.val]'e.isLt).1 ∈ x.vertices)

/-- Host active flags after processing the first `j` supplied host edges. -/
def gm02HostLoopFlags (x : GM02TopologicalInput) (j : ℕ) : List ℕ :=
  List.ofFn (fun e : Fin x.G.edges.length =>
    if e.val < j ∧ gm02HostBranchLoopTest x e = true then 0 else 1)

/-- The host loop test is exactly existence of a loop at a pattern vertex. -/
theorem gm02HostBranchLoopTest_iff (x : GM02TopologicalInput) (e : Fin x.G.edges.length) :
    gm02HostBranchLoopTest x e = true ↔ ∃ v, v ∈ V(x.H) ∧ x.G.graph.IsLoopAt e.val v := by
  rw [gm02HostBranchLoopTest, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, hm⟩
    refine ⟨(x.G.edges[e.val]'e.isLt).1.val, Finset.mem_image.2 ⟨_, hm, rfl⟩, ?_⟩
    change x.G.graph.IsLink e.val (x.G.edges[e.val]'e.isLt).1.val (x.G.edges[e.val]'e.isLt).1.val
    simpa only [hp] using x.G.isLink_getElem e.val e.isLt
  · rintro ⟨v, hv, hl⟩
    have hends := (x.G.isLink_getElem e.val e.isLt).isLink_iff.1 hl
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> constructor
    · exact Fin.ext (h₁.trans h₂.symm)
    · have hm : (x.G.edges[e.val]'e.isLt).1.val ∈ (x.vertices.image Fin.val : Finset ℕ) := h₁.symm ▸ hv
      obtain ⟨u, hu, hue⟩ := Finset.mem_image.1 hm
      exact (Fin.ext hue) ▸ hu
    · exact Fin.ext (h₁.trans h₂.symm)
    · have hm : (x.G.edges[e.val]'e.isLt).1.val ∈ (x.vertices.image Fin.val : Finset ℕ) := h₁.symm ▸ hv
      obtain ⟨u, hu, hue⟩ := Finset.mem_image.1 hm
      exact (Fin.ext hue) ▸ hu

/-- Clearing a prefix never changes the physical host edge-array length. -/
theorem gm02HostLoopFlags_length (x : GM02TopologicalInput) (j : ℕ) :
    (gm02HostLoopFlags x j).length = x.G.edges.length := by simp [gm02HostLoopFlags]

/-- Each actual host position has exactly its prefix-loop flag. -/
theorem gm02HostLoopFlags_get (x : GM02TopologicalInput) (j : ℕ) (e : Fin x.G.edges.length) :
    (gm02HostLoopFlags x j)[e.val]? =
      some (if e.val < j ∧ gm02HostBranchLoopTest x e = true then 0 else 1) := by
  simp [gm02HostLoopFlags, e.isLt]

/-- Before any host edge is processed, every edge flag is one. -/
theorem gm02HostLoopFlags_zero (x : GM02TopologicalInput) :
    gm02HostLoopFlags x 0 = List.replicate x.G.edges.length 1 := by
  simp [gm02HostLoopFlags, List.ofFn_const]

/-- The next host edge is still active before its own iteration. -/
theorem gm02HostLoopFlags_next (x : GM02TopologicalInput) (e : Fin x.G.edges.length) :
    (gm02HostLoopFlags x e.val)[e.val]? = some 1 := by
  simp only [gm02HostLoopFlags_get, Nat.lt_irrefl, false_and, ite_false]

/-- A qualifying next edge is an actual active loop at its supplied first endpoint. -/
theorem gm02HostLoopFlags_next_loop (x : GM02TopologicalInput) (e : Fin x.G.edges.length)
    (ht : gm02HostBranchLoopTest x e = true) :
    (x.G.edges[e.val]'e.isLt).1.val ∈ V(x.H) ∧
      (gm02ActiveGraph x.G.graph (gm02HostLoopFlags x e.val)).IsLoopAt e.val
        (x.G.edges[e.val]'e.isLt).1.val := by
  have hp : (x.G.edges[e.val]'e.isLt).1 = (x.G.edges[e.val]'e.isLt).2 ∧
      (x.G.edges[e.val]'e.isLt).1 ∈ x.vertices := of_decide_eq_true ht
  refine ⟨Finset.mem_image.2 ⟨_, hp.2, rfl⟩, gm02HostLoopFlags_next x e, ?_⟩
  simpa only [hp.1] using x.G.isLink_getElem e.val e.isLt

end GraphMinor.Compute
