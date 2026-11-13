module

public import GraphMinor.Compute.GM02EmitPortPair
public import GraphMinor.Compute.GM02DecodePairPosition

/-!
# One position of the split edge scan

Decode the next canonical ordered pair from the scan index, then run
the guarded emission command. The result records exactly whether that
pair is appended. The scan index, its bounds, and all original input
metadata are preserved, so the command can serve as a counting-loop body.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Decode and conditionally emit canonical pair position 64. -/
@[expose] def gm02PortEdgeBody (src : Arr) : Cmd :=
  .seq gm02DecodePairPositionProg (gm02EmitPortPairProg src)

/-- A complete pair-scan step takes at most 95 steps and has the exact conditional buffer update. -/
theorem gm02PortEdgeBody_exec {w K code rem m : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (gflags hflags : List ℕ)
    (i : Fin (gm02FullPortSize x K * gm02FullPortSize x K)) (pre : List ℕ)
    (hsrc : s.arrs src = x.enc) (hG : s.arrs 20 = gflags)
    (hGlen : gflags.length = x.G.edges.length) (hGbits : ∀ b ∈ gflags, b ≤ 1)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length)
    (hHbits : ∀ b ∈ hflags, b ≤ 1) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hslots : s.arrs 23 = List.ofFn (fun j : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code j.val))
    (hi : s.regs 64 = i.val) (hsize : s.regs 66 = gm02FullPortSize x K)
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hbuf : s.arrs 24 = pre ++ List.replicate (rem + 2) 0)
    (hpos : s.regs 67 = pre.length) (hcount : s.regs 68 = m)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hiw : i.val < 2 ^ w) (hfw : x.edges.length < 2 ^ w) (henc : x.enc.length < 2 ^ w)
    (hposw : pre.length + 2 < 2 ^ w) (hcountw : m + 1 < 2 ^ w) :
    ∃ s' t, Exec w (gm02PortEdgeBody src) s s' t ∧ t ≤ 95 ∧
      (let p : Fin (gm02FullPortSize x K) × Fin (gm02FullPortSize x K) := finProdFinEquiv.symm i
       if p.1.val < p.2.val ∧ (gm02FullPortGraph x gflags hflags code K).Adj p.1 p.2 then
        s'.arrs 24 = (pre ++ [p.1.val, p.2.val]) ++ List.replicate rem 0 ∧
          s'.regs 67 = (pre ++ [p.1.val, p.2.val]).length ∧ s'.regs 68 = m + 1
       else s'.arrs 24 = s.arrs 24 ∧ s'.regs 67 = pre.length ∧ s'.regs 68 = m) ∧
      (∀ a, a ≠ 24 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 32 → r ≠ 42 → r ≠ 43 → r ≠ 44 → r ≠ 45 → r ≠ 46 →
        r ≠ 60 → r ≠ 61 → r ≠ 62 → r ≠ 63 → r ≠ 67 → r ≠ 68 → s'.regs r = s.regs r) := by
  obtain ⟨s₀, he₀, hu₀, hv₀, ha₀, hr₀⟩ := gm02DecodePairPositionProg_exec i s hi hsize hiw hN
  obtain ⟨s₁, t₁, he₁, ht₁, hout, ha₁, hr₁⟩ :=
    gm02EmitPortPairProg_exec x s₀ src gflags hflags (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 pre
      ((congrFun ha₀ src).trans hsrc)
      ((congrFun ha₀ 20).trans hG) hGlen hGbits
      ((congrFun ha₀ 21).trans hH) hHlen hHbits
      ((congrFun ha₀ 22).trans hmask) ((congrFun ha₀ 23).trans hslots) hu₀ hv₀
      ((hr₀ 10 (by decide) (by decide)).trans hn)
      ((hr₀ 11 (by decide) (by decide)).trans hm)
      ((hr₀ 15 (by decide) (by decide)).trans hf)
      ((congrFun ha₀ 24).trans hbuf)
      ((hr₀ 67 (by decide) (by decide)).trans hpos)
      ((hr₀ 68 (by decide) (by decide)).trans hcount)
      hw hN hfw henc hposw hcountw
  refine ⟨s₁, 8 + t₁, .seq he₀ he₁, by omega, ?_, ?_, ?_⟩
  · simpa only [ha₀] using hout
  · intro a ha24
    exact (ha₁ a ha24).trans (congrFun ha₀ a)
  · intro r h32 h42 h43 h44 h45 h46 h60 h61 h62 h63 h67 h68
    exact (hr₁ r h32 h42 h43 h44 h45 h46 h62 h63 h67 h68).trans (hr₀ r h60 h61)

end GraphMinor.Compute
