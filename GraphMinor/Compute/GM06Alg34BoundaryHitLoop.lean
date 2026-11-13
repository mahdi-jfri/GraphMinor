module

public import GraphMinor.Compute.GM06Alg34BoundaryClearBody

/-!
# The linear RAM scan for new region closure hits

Scan all supplied cells and clear the accumulator whenever a reached
cell contributes the boundary label. The counted-scan invariant keeps
the original arrays and all registers outside the accumulator and
counter fixed. For an inactive source the accumulated test is exactly
the finite region closure-hit predicate.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Scan all cells up to count 105 for contributions to label 205. -/
def gm06BoundaryHitLoopProg : Cmd := gm06ScanLoop 204 gm06BoundaryClearBodyProg

/-- The boundary closure-hit scan takes at most `18 * N + 5` steps,
changes only its accumulator and counter, and preserves every array. -/
theorem gm06BoundaryHitLoopProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (a b : Fin x.cellCount) (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hcount : s.regs 105 = x.cellCount) (hboundary : s.regs 205 = b.val) :
    ∃ s' t, Exec w gm06BoundaryHitLoopProg s s' t ∧ t ≤ 18 * x.cellCount + 5 ∧
      s'.regs 0 = (if x.regionClosureHit vs a (x.cellNumbering.symm b) then 0 else s.regs 0) ∧
      (∀ k, s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 204 → s'.regs q = s.regs q) := by
  let P : State → Prop := fun st =>
    (∀ k, st.arrs k = s.arrs k) ∧
    (∀ q : ℕ, q ≠ 0 → q ≠ 204 → st.regs q = s.regs q)
  have hset : ∀ st v, P st → P (st.setReg 204 v) := by
    intro st v hp
    refine ⟨hp.1, fun q hq₁ hq₂ => ?_⟩
    exact (State.setReg_regs_ne st v hq₂).trans (hp.2 q hq₁ hq₂)
  have hbound : ∀ st, P st → st.regs 105 = x.cellCount := by
    intro st hp
    exact (hp.2 _ (by decide) (by decide)).trans hcount
  have hbody : ∀ i < x.cellCount, ∀ st, P st → st.regs 204 = i →
      ∃ st' t, Exec w gm06BoundaryClearBodyProg st st' t ∧ t ≤ 11 ∧ P st' ∧
        st'.regs 204 = i ∧ st'.regs 0 =
          (if gm06BoundaryContribution x vs a b i then 0 else st.regs 0) := by
    intro i hi st hp hir
    obtain ⟨st', t, hex, ht, hacc, harr, hreg⟩ :=
      gm06BoundaryClearBodyProg_exec x vs a ⟨i, hi⟩ b hw hN hsquare
        ((hp.1 _).trans hmarks) ((hp.1 _).trans hmat)
        ((hp.2 _ (by decide) (by decide)).trans hc) hir
        ((hp.2 _ (by decide) (by decide)).trans hboundary)
    refine ⟨st', t, hex, ht, ⟨?_, ?_⟩, (hreg _ (by decide)).trans hir, hacc⟩
    · intro k; exact (harr k).trans (hp.1 k)
    · intro q hq₁ hq₂; exact (hreg q hq₁).trans (hp.2 q hq₁ hq₂)
  obtain ⟨s', t, hex, ht, hp, _, hacc⟩ :=
    gm06ScanLoop_exec gm06BoundaryClearBodyProg (gm06BoundaryContribution x vs a b) P
      (r := 204) (by decide) hw hN hset hbound hbody
      (s := s) ⟨fun _ => rfl, fun _ _ _ => rfl⟩
  refine ⟨s', t, hex, by change t ≤ 5 + x.cellCount * 18 at ht; omega,
    ?_, hp.1, hp.2⟩
  simpa only [gm06BoundaryContribution_prefix x vs a b ha] using hacc

end GraphMinor.Compute
