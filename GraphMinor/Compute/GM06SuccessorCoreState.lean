module

public import GraphMinor.Compute.GM06SuccessorLoopInitialize
public import GraphMinor.Compute.GM06ReroutingLoopInvariant

/-!
# The literal core memory at a VI (5.7) loop entry

The current drawing relation interprets finite arrays geometrically.
This file ties those finite arrays to their actual RAM addresses.
The core assertion contains only the endpoint, rotation, cuff, path,
mask and inverse-record words, and their three scalar registers.
Linkage membership arrays are rebuilt caches and are not included.

Initialization establishes the core assertion from ordinary input.
Advancing the outer counter preserves it. A rerouting replaces only
its linkage words and bit, while an empty chronological undo record
leaves the numeric contraction history unchanged. The early driver's
literal first instruction reloads the original count into register
100, and none of its remaining instructions writes that register.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- The actual addresses of the finite current drawing arrays and
inverse-record words, as in Section 19 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`). Every field is a literal memory equality. -/ structure
    GM06SuccessorCoreRep {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {L :
    CylinderLinkage k G} (cur : GM06CurrentDrawingRep x G L) (b : Bool)
    (records : List (Option (ℕ × ℕ))) (tail : List ℕ) (s : State) : Prop where
  count : s.arrs 2 = [x.vertexCount]
  endpoints : s.arrs 3 = x.endpoints
  rotations : s.arrs 4 = gm06EncodeRows x.rotations
  inner : s.arrs 6 = x.innerCuff
  outer : s.arrs 7 = x.outerCuff
  linkage : s.arrs 8 = gm06EncodeRows x.linkage
  history : s.arrs 9 = gm06ContractionHistoryWords (records.filterMap id) ++ tail
  active : s.arrs 12 = cur.tagged.map Prod.snd
  live : s.arrs 14 = gm02VertexBits cur.live
  countReg : s.regs 100 = x.vertexCount
  historyReg : s.regs 309 = (records.filterMap id).length
  bit : s.regs 329 = b.toNat

namespace GM06SuccessorCoreRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} {cur : GM06CurrentDrawingRep x G L} {b : Bool}
  {records : List (Option (ℕ × ℕ))} {tail : List ℕ} {s : State}

/-- Updating only the outer iteration counter preserves the complete
current core interpretation. -/
theorem setCounter (core : GM06SuccessorCoreRep cur b records tail s) (i : ℕ) :
    GM06SuccessorCoreRep cur b records tail (s.setReg 900 i) := by
  refine { core with countReg := ?_, historyReg := ?_, bit := ?_ }
  · simpa using core.countReg
  · simpa using core.historyReg
  · simpa using core.bit

/-- A successful actual phase execution changes only the encoded
linkage and the persistent bit in the core. Its empty inverse event
does not change the contraction words or record count. -/
theorem rerouting (core : GM06SuccessorCoreRep cur b records tail s)
    (M : CylinderLinkage k G) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M cur.tagged cur.vertex cur.edge rows)
    {w t : ℕ} {sf : State} (he : Exec w gm06Reduction4PhaseProg s sf t)
    (h8 : sf.arrs 8 = gm06EncodeRows rows) (hbit : sf.regs 329 = 0) :
    GM06SuccessorCoreRep (cur.withLinkage M rows hrows) false (records ++ [none]) tail sf := by
  obtain ⟨ha, hr⟩ := gm06Reduction4PhaseProg_core_frame he
  have hrecords : (records ++ [none]).filterMap id = records.filterMap id := by simp
  refine ⟨(ha 2 (by simp)).trans core.count, (ha 3 (by simp)).trans core.endpoints,
    (ha 4 (by simp)).trans core.rotations, (ha 6 (by simp)).trans core.inner,
    (ha 7 (by simp)).trans core.outer, h8, ?_,
    (ha 12 (by simp)).trans core.active, (ha 14 (by simp)).trans core.live,
    (hr 100 (by simp)).trans core.countReg, ?_, hbit⟩
  · rw [hrecords]; exact (ha 9 (by simp)).trans core.history
  · rw [hrecords]; exact (hr 309 (by simp)).trans core.historyReg

end GM06SuccessorCoreRep

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem early_tail_preserves_count :
    match gm06EarlyReductionsProg with
    | .seq _ rest => (100 : Reg) ∉ rest.writtenRegs
    | _ => False := by
  dsimp only [gm06EarlyReductionsProg]
  decide

/-- Every successful execution of the early driver has reloaded the
original count from array 2. This supplies register 100 to the next
whole phase even after the three early scans all return failure. -/
theorem gm06EarlyReductionsProg_original_count {w t n : ℕ} {s sf : State}
    (he : Exec w gm06EarlyReductionsProg s sf t) (h2 : s.arrs 2 = [n]) :
    sf.regs 100 = n := by
  unfold gm06EarlyReductionsProg at he
  cases he with
  | seq first rest =>
    cases first with
    | @assign _ _ _ value hread =>
      have hv : value = n := by
        by_cases hn : n < 2 ^ w
        · have hh : (Expr.read 2 (.const 0)).eval w s = some n := by
            simp [Expr.eval, checkWord, h2, hn]
          exact Option.some.inj (hread.symm.trans hh)
        · simp [Expr.eval, checkWord, h2, hn] at hread
      have hr := rest.regs_eq_of_not_mem_writtenRegs early_tail_preserves_count
      simpa only [State.setReg_regs_self, hv] using hr

/-- The real initialization prefix returns the literal memory
assertion, with empty numeric history and the original edge map.
All word bounds are derived from the ordinary input interpretation. -/
theorem gm06InitializeSuccessorLoopCoreProg_core
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (input : GM06SuccessorInputRep x G L)
    (hG : IsCylinderSection5Drawing k G) (s : State)
    (hinput : s.arrs 0 = gm06EncodeSuccessorInput x) :
    ∃ (sf : State) (t : ℕ) (cur : GM06CurrentDrawingRep x G L),
      Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06InitializeSuccessorLoopCoreProg s sf t ∧
      t ≤ 100 * (gm06SuccessorInputSize x + 1) ∧
      GM06SuccessorCoreRep cur true [] (List.replicate (2 * (x.vertexCount + G.E.ncard)) 0) sf ∧
      sf.arrs 0 = s.arrs 0 ∧
      sf.regs 905 = 2 * (x.vertexCount + G.E.ncard) + 1 ∧ sf.regs 904 = 1 ∧ sf.regs 900 = 0 ∧
      cur.tagged = input.graph.initialTagged ∧ cur.live = Finset.univ ∧
      cur.vertex = input.graph.vertexLabels ∧ HEq cur.edge input.graph.edgeLabels ∧
      Function.Injective cur.vertex ∧ (∀ p ∈ cur.tagged, p.2 ≤ 1) := by
  obtain ⟨sf, t, cur, he, ht, h0, h2, h3, h4, h6, h7, h8, h12, h14, h9,
      h100, h309, h329, h905, h904, h900, htag, hlive, hv, hedge, hinj, hbits, _⟩ :=
    gm06InitializeSuccessorLoopCoreProg_current input hG s hinput
  have core : GM06SuccessorCoreRep cur true []
      (List.replicate (2 * (x.vertexCount + G.E.ncard)) 0) sf :=
    ⟨h2, h3, h4, h6, h7, h8, h9, h12, h14, h100, h309, h329⟩
  exact ⟨sf, t, cur, he, ht, core, h0, h905, h904, h900, htag, hlive, hv, hedge, hinj, hbits⟩

end GraphMinor.Compute
