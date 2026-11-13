module

public import GraphMinor.Compute.PlanarityRamFinishKey
public import GraphMinor.Compute.PlanarityRamParentPair

/-!
# Finishing a DFS edge

The program follows `finish_edge`: compute the key, read the source's
incoming edge, and, when one exists, insert both child lowpoints into it.
Optional edge identifiers use a one-word tag, so the parent branch removes
that tag before reading the parent's record.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The fixed edge-finishing command. Register 45 initially holds its index. -/
def finishEdgeProg : Cmd :=
  .seq finishKeyProg
    (.seq (.assign 45 (.read Field.parentEdge.array (.reg 41)))
      (.ite (.reg 45)
        (.seq (.assign 45 (.op .sub (.reg 45) (.const 1))) parentPairProg) .skip))

/-- Separate the key update from the optional parent-pair update. -/
theorem finishEdge_eq (search : Search) (i : ℕ) :
    finishEdge search i =
      match search.parentEdge[search.edges[i]!.source]?.join with
      | none => setEdgeKey search i (finishedKey search i)
      | some p =>
        setEdgePair (setEdgeKey search i (finishedKey search i)) p
          (insertLow (insertLow (setEdgeKey search i (finishedKey search i)).edges[p]!.pair
            search.edges[i]!.pair.low) search.edges[i]!.pair.second) := by
  cases ho : search.parentEdge[search.edges[i]!.source]?.join <;>
    simp [finishEdge, setEdgeKey, setEdgePair, finishedKey, ho]

/-- A key change leaves every valid edge's lowpoint pair fixed, including
when the changed key and the queried pair belong to the same edge. -/
theorem setEdgeKey_pair (search : Search) (i key p : ℕ)
    (hi : i < search.edges.size) (hp : p < search.edges.size) :
    (setEdgeKey search i key).edges[p]!.pair = search.edges[p].pair := by
  unfold setEdgeKey
  by_cases hpi : i = p
  · subst p
    rw [Array.getElem!_set!_self _ _ _ hi]
    simp [getElem!_pos search.edges i hi]
  · rw [Array.getElem!_set!_ne _ _ _ _ hpi]
    rw [getElem!_pos search.edges p hp]

/-- The edge-finishing command refines `finishEdge` in at most seventy
steps. The input conditions require a valid edge and source, word bounds,
and a valid bounded incoming-edge record whenever that pointer is present. -/
theorem finishEdgeProg_refines {N M w : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (i : ℕ) (hi : i < search.edges.size)
    (hr : s.regs 45 = i) (hv : search.edges[i].source < search.depth.size)
    (hw : 2 < 2 ^ w) (hiw : i < 2 ^ w)
    (hvw : search.edges[i].source < 2 ^ w)
    (hlo : search.edges[i].pair.low < 2 ^ w) (hhi : search.edges[i].pair.second < 2 ^ w)
    (hdw : optionWord search.depth[search.edges[i].source] < 2 ^ w)
    (hkey : finishedKey search i < 2 ^ w)
    (hparent : ∀ p : ℕ, search.parentEdge[search.edges[i].source]?.join = some p →
      p < search.edges.size ∧ p + 1 < 2 ^ w ∧
      search.edges[p]!.pair.low < 2 ^ w ∧ search.edges[p]!.pair.second < 2 ^ w) :
    ∃ s' t, Exec w finishEdgeProg s s' t ∧ t ≤ 70 ∧ SearchAt N M s' (finishEdge search i) := by
  obtain ⟨s1, hx1, h1, hsource, hfirst, hsecond, hindex⟩ :=
    finishKeyProg_refines h i hi hr hv hw hiw hvw hlo hhi hdw hkey
  have hvp : search.edges[i].source < search.parentEdge.size := by
    rw [h.2.2.1, ← h.1]
    exact hv
  have hparentPrefix : PrefixAt s1 Field.parentEdge.array N
      (search.parentEdge.toList.map optionWord) := h1.2.2.2.2.2.2.2.1
  have he : search.edges[i]! = search.edges[i] := getElem!_pos search.edges i hi
  have hz : 0 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  cases hpar : search.parentEdge[search.edges[i].source]?.join with
  | none =>
    have hraw : search.parentEdge[search.edges[i].source] = none := by
      simpa only [Array.getElem?_eq_getElem hvp, Option.join_some] using hpar
    have eread : (Expr.read Field.parentEdge.array (.reg 41)).eval w s1 = some 0 := by
      simpa only [hraw, optionWord] using hparentPrefix.read_option_reg hvp hsource hvw
        (by simpa only [hraw, optionWord] using hz)
    let s2 := s1.setReg 45 0
    have hx2 : Exec w (.assign 45 (.read Field.parentEdge.array (.reg 41))) s1 s2 3 :=
      Exec.assign eread
    have hx3 : Exec w (.ite (.reg 45)
        (.seq (.assign 45 (.op .sub (.reg 45) (.const 1))) parentPairProg) .skip) s2 s2 2 :=
      Exec.ite_false (by simpa [Expr.eval, s2] using checkWord_of_lt hz) (Exec.skip s2)
    refine ⟨s2, 28, Exec.seq hx1 (Exec.seq hx2 hx3), by omega, ?_⟩
    simpa only [finishEdge_eq, he, hpar] using h1.setReg 45 0 (by decide) (by decide)
  | some p =>
    obtain ⟨hp, hpw, hpl, hpl2⟩ := hparent p hpar
    have hraw : search.parentEdge[search.edges[i].source] = some p := by
      simpa only [Array.getElem?_eq_getElem hvp, Option.join_some] using hpar
    have eread : (Expr.read Field.parentEdge.array (.reg 41)).eval w s1 = some (p + 1) := by
      simpa only [hraw, optionWord] using hparentPrefix.read_option_reg hvp hsource hvw
        (by simpa only [hraw, optionWord] using hpw)
    let s2 := s1.setReg 45 (p + 1)
    let s3 := s2.setReg 45 p
    have hx2 : Exec w (.assign 45 (.read Field.parentEdge.array (.reg 41))) s1 s2 3 :=
      Exec.assign eread
    have hx3 : Exec w (.assign 45 (.op .sub (.reg 45) (.const 1))) s2 s3 4 := by
      apply Exec.assign
      simp [Expr.eval, s2, BinOp.eval, BinOp.raw, checkWord_of_lt hpw,
        checkWord_of_lt hone, checkWord_of_lt (show p < 2 ^ w by omega)]
    have h3 : SearchAt N M s3 (setEdgeKey search i (finishedKey search i)) :=
      (h1.setReg 45 (p + 1) (by decide) (by decide)).setReg 45 p (by decide) (by decide)
    have hp' : p < (setEdgeKey search i (finishedKey search i)).edges.size := by
      simpa [setEdgeKey] using hp
    have hpair := setEdgeKey_pair search i (finishedKey search i) p hi hp
    have hpair' : (setEdgeKey search i (finishedKey search i)).edges[p].pair =
        search.edges[p].pair := by
      simpa only [getElem!_pos (setEdgeKey search i (finishedKey search i)).edges p hp'] using hpair
    have hlo' : (setEdgeKey search i (finishedKey search i)).edges[p].pair.low < 2 ^ w := by
      rw [hpair']
      simpa only [getElem!_pos search.edges p hp] using hpl
    have hhi' : (setEdgeKey search i (finishedKey search i)).edges[p].pair.second < 2 ^ w := by
      rw [hpair']
      simpa only [getElem!_pos search.edges p hp] using hpl2
    obtain ⟨s4, t4, hx4, ht4, h4⟩ := parentPairProg_refines h3 p hp' (by simp [s3]) hone
      (by omega) hlo' hhi' (by simpa [s3, s2, hfirst] using hlo)
      (by simpa [s3, s2, hsecond] using hhi)
    have hcond : (Expr.reg 45).eval w s2 = some (p + 1) := by
      simpa [Expr.eval, s2] using checkWord_of_lt hpw
    refine ⟨s4, 23 + (3 + (1 + (4 + t4))), Exec.seq hx1 (Exec.seq hx2
      (Exec.ite_true hcond (by omega) (Exec.seq hx3 hx4))), by omega, ?_⟩
    simpa only [finishEdge_eq, he, hpar, getElem!_pos (setEdgeKey search i (finishedKey search i)).edges p hp', hfirst, hsecond,
      s3, s2, State.setReg_regs_ne _ _ (show (43 : ℕ) ≠ 45 by decide),
      State.setReg_regs_ne _ _ (show (44 : ℕ) ≠ 45 by decide)] using h4

end GraphMinor.Compute.PlanarityRam
