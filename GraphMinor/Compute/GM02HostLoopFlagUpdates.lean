module

public import GraphMinor.Compute.GM02HostLoopFlags

/-!
# Updating and finishing the host-loop flag prefix

At a qualifying host loop, clearing its own flag advances the processed
prefix. At any other edge, advancing the prefix changes no flag. Once
all supplied host positions have been processed, no active host loop
can remain at a pattern vertex. These are the flag invariants used by
the outer RAM loop.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- Clearing the next qualifying loop advances exactly the host flag prefix. -/
theorem gm02HostLoopFlags_set_next (x : GM02TopologicalInput) (e : Fin x.G.edges.length)
    (ht : gm02HostBranchLoopTest x e = true) :
    (gm02HostLoopFlags x e.val).set e.val 0 = gm02HostLoopFlags x (e.val + 1) := by
  apply List.ext_getElem
  · simp only [List.length_set, gm02HostLoopFlags_length]
  · intro f hf hg
    by_cases hfe : f = e.val
    · subst f
      simp only [gm02HostLoopFlags, List.getElem_set_self, List.getElem_ofFn, Fin.eta,
        Nat.lt_succ_self, ht, and_self, ite_true]
    · have hlt : f < e.val + 1 ↔ f < e.val := by omega
      simp only [gm02HostLoopFlags, List.getElem_set, List.getElem_ofFn,
        Ne.symm hfe, ite_false, hlt]

/-- Processing a host edge that is not a branch loop leaves the flags unchanged. -/
theorem gm02HostLoopFlags_skip_next (x : GM02TopologicalInput) (e : Fin x.G.edges.length)
    (ht : gm02HostBranchLoopTest x e = false) :
    gm02HostLoopFlags x (e.val + 1) = gm02HostLoopFlags x e.val := by
  apply List.ext_getElem
  · simp only [gm02HostLoopFlags_length]
  · intro f hf hg
    by_cases hfe : f = e.val
    · subst f
      simp only [gm02HostLoopFlags, List.getElem_ofFn, Fin.eta, ht,
        Bool.false_eq_true, and_false, ite_false]
    · have hlt : f < e.val + 1 ↔ f < e.val := by omega
      simp only [gm02HostLoopFlags, List.getElem_ofFn, hlt]

/-- Every host prefix array consists of zero-or-one flags. -/
theorem gm02HostLoopFlags_bits (x : GM02TopologicalInput) (j : ℕ) :
    ∀ b ∈ gm02HostLoopFlags x j, b ≤ 1 := by
  intro b hb
  simp only [gm02HostLoopFlags, List.mem_ofFn] at hb
  obtain ⟨f, rfl⟩ := hb
  split <;> decide

/-- After the full host scan there is no active host loop at any pattern vertex. -/
theorem gm02HostLoopFlags_no_branch_loops (x : GM02TopologicalInput) :
    ∀ e v, v ∈ V(x.H) → ¬(gm02ActiveGraph x.G.graph (gm02HostLoopFlags x x.G.edges.length)).IsLoopAt e v := by
  intro e v hv hloop
  have hbase : x.G.graph.IsLoopAt e v := (gm02ActiveGraph_le x.G.graph _).isLink_mono hloop
  have he : e < x.G.edges.length := hbase.edge_mem
  let f : Fin x.G.edges.length := ⟨e, he⟩
  have ht : gm02HostBranchLoopTest x f = true := (gm02HostBranchLoopTest_iff x f).2 ⟨v, hv, hbase⟩
  have hg : (gm02HostLoopFlags x x.G.edges.length)[e]? = some 0 := by
    have hget := gm02HostLoopFlags_get x x.G.edges.length f
    rw [ite_eq_left (And.intro f.isLt ht)] at hget
    exact hget
  have hactive : (gm02HostLoopFlags x x.G.edges.length)[e]? = some 1 := hloop.1
  rw [hg] at hactive
  cases hactive

end GraphMinor.Compute
