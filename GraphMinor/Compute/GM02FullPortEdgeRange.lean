module

public import GraphMinor.Compute.GM02PortPositionRange

/-!
# Every numeric split edge stays inside the retained image

Decode an active terminal's slot through the two-slot bijection. This
supplies its abstract preimage. The two forward adjacency cases then
place both endpoints in the numeric embedding's image. Consequently,
every unused numeric position is isolated.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- An active fixed terminal slot belongs to the retained image. -/
theorem gm02PortPosition_slot_mem_range (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    {k K : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) (hK : x.edges.length ≤ K)
    (p : Fin (2 * K)) (hbound : p.val / 2 < x.edges.length)
    (hflag : hflags[p.val / 2]? = some 1) :
    gm02FullPortTerminal x K p ∈ Set.range (gm02PortPositionEmbedding x gflags hflags edge hK) := by
  let r : Fin (x.edges.length * 2) := ⟨p.val, by omega⟩
  let q := (gm02PortSlotEquiv x.edges.length).symm r
  have hslot : (gm02PortSlotEquiv x.edges.length q).val = p.val :=
    congrArg Fin.val ((gm02PortSlotEquiv x.edges.length).apply_symm_apply r)
  have hfirst : q.1.val = p.val / 2 := by
    rw [← hslot, gm02PortSlotEquiv_div_two]
  have hq : hflags[q.1.val]? = some 1 := by rw [hfirst]; exact hflag
  have hmem := gm02PortPosition_terminal_mem_range x gflags hflags edge hK q hq
  have heq : gm02FullPortPatternTerminal x K hK q = gm02FullPortTerminal x K p := by
    apply Fin.ext
    change x.G.n + x.G.edges.length + _ = x.G.n + x.G.edges.length + p.val
    rw [hslot]
  exact heq ▸ hmem

/-- A forward numeric edge has both endpoints in the image of the abstract split vertices. -/
theorem gm02FullPortForward_mem_range (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code : ℕ) {k K : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hK : x.edges.length ≤ K) (u v : Fin (gm02FullPortSize x K))
    (h : gm02FullPortForward x gflags hflags code K u.val v.val) :
    u ∈ Set.range (gm02PortPositionEmbedding x gflags hflags edge hK) ∧
      v ∈ Set.range (gm02PortPositionEmbedding x gflags hflags edge hK) := by
  rcases h with h | h
  · let a : Fin x.G.n := ⟨u.val, h.1⟩
    let e : Fin x.G.edges.length := ⟨v.val - x.G.n, by omega⟩
    have ha : a ∉ x.vertices := (gm02PortMask_zero_iff x a).1 h.2.2.2.1
    have he := gm02PortPosition_edge_mem_range x gflags hflags edge hK e h.2.2.2.2.1
    have heq : gm02FullPortEdge x K e = v := by
      apply Fin.ext
      change x.G.n + (v.val - x.G.n) = v.val
      omega
    exact ⟨gm02PortPosition_old_mem_range x gflags hflags edge hK a ha, heq ▸ he⟩
  · let e : Fin x.G.edges.length := ⟨u.val - x.G.n, by omega⟩
    let p : Fin (2 * K) := ⟨v.val - (x.G.n + x.G.edges.length), by
      have := v.isLt
      unfold gm02FullPortSize at this
      omega⟩
    have he := gm02PortPosition_edge_mem_range x gflags hflags edge hK e h.2.2.2.2.2.2.1
    have hp := gm02PortPosition_slot_mem_range x gflags hflags edge hK p h.2.2.2.2.1 h.2.2.2.2.2.1
    have heq : gm02FullPortEdge x K e = u := by
      apply Fin.ext
      change x.G.n + (u.val - x.G.n) = u.val
      omega
    have hpq : gm02FullPortTerminal x K p = v := by
      apply Fin.ext
      change x.G.n + x.G.edges.length + (v.val - (x.G.n + x.G.edges.length)) = v.val
      omega
    exact ⟨heq ▸ he, hpq ▸ hp⟩

/-- Every numeric split adjacency has both endpoints in the retained image. -/
theorem gm02FullPortGraph_adj_mem_range (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code : ℕ) {k K : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hK : x.edges.length ≤ K) {u v : Fin (gm02FullPortSize x K)}
    (h : (gm02FullPortGraph x gflags hflags code K).Adj u v) :
    u ∈ Set.range (gm02PortPositionEmbedding x gflags hflags edge hK) ∧
      v ∈ Set.range (gm02PortPositionEmbedding x gflags hflags edge hK) := by
  rw [gm02FullPortGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact gm02FullPortForward_mem_range x gflags hflags code edge hK u v h
  · exact (gm02FullPortForward_mem_range x gflags hflags code edge hK v u h).symm

end GraphMinor.Compute
