module

public import GraphMinor.Compute.PlanarityRamFrameKeep

/-!
# The back-edge branch of a frame step

The visited-neighbor branch creates one back-edge record and immediately
finishes it. Its identifier is the old live length, recovered by subtracting
one from the incremented edge counter. No frame is pushed or removed.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Creating and finishing a back edge takes at most 110 steps. The input
conditions give the valid endpoint and parent indices, available record
slot, and word bounds used by the two local programs. -/
theorem backEdgeProg_refines {N M w : ℕ} {s : State} {search : Search}
    {stack : List Frame} (h : DfsSearchAt N M s search) (hf : FramesAt N s stack)
    (v u : ℕ) (hv : v < search.depth.size) (hu : u < search.depth.size)
    (hrv : s.regs 41 = v) (hru : s.regs 43 = u)
    (hedge : search.edges.size < M) (hw : 2 < 2 ^ w)
    (hvw : v < 2 ^ w) (huw : u < 2 ^ w)
    (hvd : optionWord search.depth[v] < 2 ^ w) (hud : optionWord search.depth[u] < 2 ^ w)
    (hecount : search.edges.size + 1 < 2 ^ w)
    (hkey : finishedKey (addEdge search v u false).1 search.edges.size < 2 ^ w)
    (hparent : ∀ p : ℕ, search.parentEdge[v]?.join = some p →
      p < search.edges.size ∧ p + 1 < 2 ^ w ∧
      search.edges[p]!.pair.low < 2 ^ w ∧ search.edges[p]!.pair.second < 2 ^ w) :
    ∃ s' t, Exec w backEdgeProg s s' t ∧ t ≤ 110 ∧ FramesAt N s' stack ∧
      DfsSearchAt N M s' (finishEdge (addEdge search v u false).1 search.edges.size) := by
  let added := (addEdge search v u false).1
  let i := search.edges.size
  change i + 1 < 2 ^ w at hecount
  have hsourceDepth : (search.depth[v]?.join).getD 0 < 2 ^ w := by
    have hh := Nat.lt_of_le_of_lt (Nat.sub_le (optionWord search.depth[v]) 1) hvd
    simpa [optionWord_sub_one, Array.getElem?_eq_getElem hv] using hh
  have htargetDepth : (search.depth[u]?.join).getD 0 < 2 ^ w := by
    have hh := Nat.lt_of_le_of_lt (Nat.sub_le (optionWord search.depth[u]) 1) hud
    simpa [optionWord_sub_one, Array.getElem?_eq_getElem hu] using hh
  obtain ⟨s1, t1, hx1, ht1, hs1⟩ := addEdgeProg_refines h v u false hv hu hrv hru hedge
    (by omega) hvw huw hvd hud hecount
  have hs1' : SearchAt N M s1 (reversePostorder added) := by
    rw [reversePostorder_addEdge]
    exact hs1
  have hf1 := hf.addEdge_exec false hx1
  have hcount : s1.regs 37 = i + 1 := by
    simpa [reversePostorder, added, addEdge, i] using hs1'.2.2.2.1
  let s2 := s1.setReg 45 i
  have hs2 := hs1'.setReg 45 i (by decide) (by decide)
  have hf2 : FramesAt N s2 stack := hf1.setReg 45 i (by decide)
  have hi : i < (reversePostorder added).edges.size := by simp [reversePostorder, added, addEdge, i]
  have he : (reversePostorder added).edges[i] =
      (⟨v, u, false, ⟨(search.depth[u]?.join).getD 0, (search.depth[v]?.join).getD 0⟩, 0⟩ : EdgeRecord) := by
    simp [reversePostorder, added, addEdge, i]
  have hpar : ∀ p : ℕ,
      (reversePostorder added).parentEdge[(reversePostorder added).edges[i].source]?.join = some p →
        p < (reversePostorder added).edges.size ∧ p + 1 < 2 ^ w ∧
        (reversePostorder added).edges[p]!.pair.low < 2 ^ w ∧
        (reversePostorder added).edges[p]!.pair.second < 2 ^ w := by
    intro p hp
    rw [he] at hp
    obtain ⟨hpi, hpw, hpl, hpl2⟩ := hparent p hp
    have hpnew : p < (reversePostorder added).edges.size := by
      simpa [reversePostorder, added, addEdge] using Nat.lt_trans hpi (Nat.lt_succ_self _)
    have hold : (reversePostorder added).edges[p]! = search.edges[p] := by
      rw [getElem!_pos (reversePostorder added).edges p hpnew]
      exact Array.getElem_push_lt hpi
    refine ⟨hpnew, hpw, ?_, ?_⟩
    · simpa only [hold, getElem!_pos search.edges p hpi] using hpl
    · simpa only [hold, getElem!_pos search.edges p hpi] using hpl2
  have hx2 : Exec w (.assign 45 (.op .sub (.reg 37) (.const 1))) s1 s2 4 := by
    apply Exec.assign
    simp [Expr.eval, hcount, BinOp.eval, BinOp.raw, checkWord_of_lt hecount,
      checkWord_of_lt (show 1 < 2 ^ w by omega), checkWord_of_lt (show i < 2 ^ w by omega)]
  obtain ⟨s3, t3, hx3, ht3, hs3⟩ := finishEdgeProg_refines hs2 i hi (by simp only [State.setReg_regs_self])
    (by rw [he]; exact hv) hw (by omega)
    (by rw [he]; exact hvw) (by rw [he]; exact htargetDepth)
    (by rw [he]; exact hsourceDepth) (by simp only [he]; change optionWord search.depth[v] < 2 ^ w; exact hvd)
    hkey hpar
  refine ⟨s3, t1 + (4 + t3), Exec.seq hx1 (Exec.seq hx2 hx3), by omega,
    hf2.finishEdge_exec hx3, ?_⟩
  rw [← reversePostorder_finishEdge] at hs3
  exact hs3

end GraphMinor.Compute.PlanarityRam
