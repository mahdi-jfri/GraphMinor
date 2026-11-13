module

public import GraphMinor.Compute.GM06Alg34DualEndpointQuery
public import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Emitting one computed dual endpoint pair

Run the supplied-incidence query for the selected primal edge, then
append its two bounded region labels to the dual payload. The exact
buffer invariant keeps every previously written section unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Append the dual endpoints of edge register 7600 to output array 55. -/
def gm06DualEndpointEmitProg : Cmd :=
  .seq gm06DualEndpointQueryProg (emitPairProg 55 7804 7610 7611)

/-- One edge emits precisely its finite dual endpoint pair, with linear
incidence-scan work and preservation of the surrounding serializer state. -/
theorem gm06DualEndpointEmitProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (hR : 0 < x.regions.length) (e : Fin x.ends.length) {pre : List ℕ} {s : State}
    (hw : 2 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hspan : x.regions.length + 2 < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hedge : s.regs 7600 = e.val) (hsource : s.arrs 52 = List.range x.regions.length)
    (hbuf : IsBuf 55 7804 pre cap s) (hcap : 2 ≤ cap) (hfit : pre.length + 2 < 2 ^ w) :
    let p := (x.dualEdgeEnds e).getD (⟨0, hR⟩, ⟨0, hR⟩)
    ∃ s' t, Exec w gm06DualEndpointEmitProg s s' t ∧
      t ≤ 100 * (x.regions.length + 1) + 24 ∧
      IsBuf 55 7804 (pre ++ [p.1.val, p.2.val]) (cap - 2) s' ∧
      (∀ A : ℕ, A ≠ 54 → A ≠ 55 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7601 ∨ 7611 < r → r ≠ 7804 → s'.regs r = s.regs r) := by
  let p := (x.dualEdgeEnds e).getD (⟨0, hR⟩, ⟨0, hR⟩)
  have hrw : x.regions.length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hx₁, hy₁, ha₁, hg₁⟩ :=
    gm06DualEndpointQueryProg_exec x hR e hw hN hsquare hspan hmat hstride hn hm hedge hsource
  have hb₁ : IsBuf 55 7804 pre cap s₁ :=
    ⟨(ha₁ 55 (by decide)).trans hbuf.1,
      (hg₁ 7804 (Or.inr (by decide))).trans hbuf.2⟩
  obtain ⟨s₂, he₂, hb₂, ha₂, hg₂⟩ := emitPairProg_exec 55 7804 7610 7611
    hb₁ hcap hx₁ hy₁ (by decide) (p.1.isLt.trans hrw) (p.2.isLt.trans hrw) hfit
  refine ⟨s₂, t₁ + 14, .seq he₁ he₂, by omega, hb₂, ?_, ?_⟩
  · intro A h54 h55
    exact (ha₂ A h55).trans (ha₁ A h54)
  · intro r hr h7804
    exact (hg₂ r h7804).trans (hg₁ r hr)

end GraphMinor.Compute
