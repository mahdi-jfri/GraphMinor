module

public import GraphMinor.Compute.PlanarityRamBounds
public import GraphMinor.Compute.PlanarityRamFrameKeep

/-!
# Finishing records with bounded search data

The data bounds give every index and value needed by `finish_edge`.
Computing its key keeps it within the global bucket range, and inserting
both child values preserves the lowpoint bounds. Thus the local execution
proof can be used without separate hypotheses for every read word.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Optional depth tags are at most N under the search depth bounds. -/
theorem SearchBounded.depth_tag_le {N : ℕ} {search : Search} (h : SearchBounded N search)
    (v : Fin N) : optionWord (search.depth[v.val]?.join) ≤ N := by
  cases hd : search.depth[v.val]?.join with
  | none => simp [optionWord]
  | some d =>
    have hh := h.2.2.2.1 v d hd
    simp only [optionWord]
    omega

/-- The computed key lies in the allocated global bucket range. -/
theorem SearchBounded.finishedKey_le {N : ℕ} {search : Search} (h : SearchBounded N search)
    (i : ℕ) (hi : i < search.edges.size) : finishedKey search i ≤ 2 * N := by
  have he := h.2.2.2.2.2.2 i hi
  have hlo : search.edges[i]!.pair.low < N := he.2.2.1
  have hbit : (decide (search.edges[i]!.pair.second <
      (search.depth[search.edges[i]!.source]?.join).getD 0)).toNat ≤ 1 := by
    cases decide (search.edges[i]!.pair.second <
      (search.depth[search.edges[i]!.source]?.join).getD 0) <;> decide
  unfold finishedKey
  omega

/-- Finishing a valid edge preserves all search data bounds. -/
theorem SearchBounded.finishEdge {N : ℕ} {search : Search} (h : SearchBounded N search)
    (i : ℕ) (hi : i < search.edges.size) : SearchBounded N (finishEdge search i) := by
  have he := h.2.2.2.2.2.2 i hi
  have hkey := h.set_key i (finishedKey search i) hi (h.finishedKey_le i hi)
  cases hpar : search.parentEdge[search.edges[i]!.source]?.join with
  | none => simpa only [finishEdge_eq, hpar] using hkey
  | some p =>
    have hp : p < search.edges.size := h.2.2.2.2.2.1 ⟨search.edges[i]!.source, he.1⟩ p hpar
    have hp' : p < (setEdgeKey search i (finishedKey search i)).edges.size := by
      simpa [setEdgeKey] using hp
    have hpe := hkey.2.2.2.2.2.2 p hp'
    have hfirst := insertLow_lt N (setEdgeKey search i (finishedKey search i)).edges[p]!.pair
      search.edges[i]!.pair.low hpe.2.2.1 hpe.2.2.2.1 he.2.2.1
    have hsecond := insertLow_lt N _ search.edges[i]!.pair.second hfirst.1 hfirst.2 he.2.2.2.1
    have hout := hkey.set_pair p _ hp' hsecond.1 hsecond.2
    simpa only [finishEdge_eq, hpar] using hout

/-- Bounded search data supply all local word hypotheses for finishing an
edge. The bound is linear in N and the number of live records. -/
theorem finishEdgeProg_refines_bounded {N M w : ℕ} {s : State} {search : Search}
    {stack : List Frame} (h : DfsSearchAt N M s search) (hf : FramesAt N s stack)
    (hb : SearchBounded N search) (i : ℕ) (hi : i < search.edges.size)
    (hr : s.regs 45 = i) (hw : 2 * (N + search.edges.size + 1) < 2 ^ w) :
    ∃ s' t, Exec w finishEdgeProg s s' t ∧ t ≤ 70 ∧ FramesAt N s' stack ∧
      DfsSearchAt N M s' (finishEdge search i) := by
  have he := hb.2.2.2.2.2.2 i hi
  have heq : search.edges[i]! = search.edges[i] := getElem!_pos search.edges i hi
  have hvN : search.edges[i].source < N := by simpa only [heq] using he.1
  have hv : search.edges[i].source < search.depth.size := by rw [hb.1]; exact hvN
  have hdepthTag := hb.depth_tag_le ⟨search.edges[i].source, hvN⟩
  have hdw : optionWord search.depth[search.edges[i].source] < 2 ^ w := by
    have hh : optionWord search.depth[search.edges[i].source] ≤ N := by
      simpa only [Array.getElem?_eq_getElem hv, Option.join_some] using hdepthTag
    omega
  have hlow : search.edges[i].pair.low < 2 ^ w := by
    have hh : search.edges[i].pair.low < N := by simpa only [heq] using he.2.2.1
    omega
  have hlow2 : search.edges[i].pair.second < 2 ^ w := by
    have hh : search.edges[i].pair.second < N := by simpa only [heq] using he.2.2.2.1
    omega
  have hkey : finishedKey search i < 2 ^ w := by
    have hh := hb.finishedKey_le i hi
    omega
  have hparent : ∀ p : ℕ, search.parentEdge[search.edges[i].source]?.join = some p →
      p < search.edges.size ∧ p + 1 < 2 ^ w ∧
      search.edges[p]!.pair.low < 2 ^ w ∧ search.edges[p]!.pair.second < 2 ^ w := by
    intro p hp
    have hpi := hb.2.2.2.2.2.1 ⟨search.edges[i].source, hvN⟩ p hp
    have hpe := hb.2.2.2.2.2.2 p hpi
    have hl : search.edges[p]!.pair.low < N := hpe.2.2.1
    have hh : search.edges[p]!.pair.second < N := hpe.2.2.2.1
    exact ⟨hpi, by omega, by omega, by omega⟩
  obtain ⟨s', t, hx, ht, hs⟩ := finishEdgeProg_refines h i hi hr hv (by omega) (by omega)
    (by change search.edges[i].source < 2 ^ w; omega) hlow hlow2 hdw hkey hparent
  refine ⟨s', t, hx, ht, hf.finishEdge_exec hx, ?_⟩
  rw [← reversePostorder_finishEdge] at hs
  exact hs

end GraphMinor.Compute.PlanarityRam
