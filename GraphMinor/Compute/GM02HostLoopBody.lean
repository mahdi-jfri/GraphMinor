module

public import GraphMinor.Compute.GM02HostEndpointExpr
public import GraphMinor.Compute.GM02HostBranchLoopExpr
public import GraphMinor.Compute.GM02HostLoopFlagUpdates
public import GraphMinor.Compute.GM02RemoveBranchLoop

/-!
# One host-edge iteration of loop removal

Read the next supplied host edge. If its ends differ, or its vertex is
outside the pattern, retain it. Otherwise the prefix invariant shows
that it is an active loop at a pattern vertex. Run the proved matching
loop removal. Both branches advance the exact host flag prefix and
preserve the topological question, the pattern flag bounds, and all
unrelated working data.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- Process one saved host edge, removing it exactly when it is a branch loop. -/
def gm02HostLoopBody : Cmd :=
  .seq (gm02ReadHostEndsProg inArr) (.ite gm02HostBranchLoopExpr gm02RemoveBranchLoopProg .skip)

/-- One actual host-edge iteration preserves the topological test and advances the exact host flag prefix. -/
theorem gm02HostLoopBody_exec {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (e : Fin x.G.edges.length) (hflags : List ℕ)
    (hsrc : s.arrs inArr = x.enc) (hG : s.arrs 20 = gm02HostLoopFlags x e.val)
    (hH : s.arrs 21 = hflags) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hHlen : hflags.length = x.edges.length) (hbits : ∀ b ∈ hflags, b ≤ 1)
    (hE : s.regs 32 = e.val) (hM : s.regs 15 = x.edges.length)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w gm02HostLoopBody s s' t ∧ t ≤ 41 * x.edges.length + 38 ∧
      s'.arrs 20 = gm02HostLoopFlags x (e.val + 1) ∧
      (s'.arrs 21).length = x.edges.length ∧ (∀ b ∈ s'.arrs 21, b ≤ 1) ∧
      (TopologicallyContains (gm02ActiveGraph x.G.graph (gm02HostLoopFlags x e.val)) (gm02ActiveGraph x.H hflags) ↔
        TopologicallyContains (gm02ActiveGraph x.G.graph (s'.arrs 20)) (gm02ActiveGraph x.H (s'.arrs 21))) ∧
      (∀ a, a ≠ 20 → a ≠ 21 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 40 → r ≠ 41 → r ≠ 42 → r ≠ 43 → r ≠ 44 → s'.regs r = s.regs r) := by
  have hw₁ : 1 < 2 ^ w := by omega
  obtain ⟨s₁, he₁, hleft, hright, ha₁, hr₁⟩ := gm02ReadHostEndsProg_exec x s inArr e hsrc hE hw hn hlen
  have htest := gm02HostBranchLoopExpr_eval x s₁ e
    (by rw [ha₁]; exact hmask) hleft hright hw₁ hn
  cases ht : gm02HostBranchLoopTest x e with
  | false =>
    have htest₀ : gm02HostBranchLoopExpr.eval w s₁ = some 0 := by
      simpa only [ht, Bool.false_eq_true, ↓reduceIte] using htest
    have he₂ : Exec w (.ite gm02HostBranchLoopExpr gm02RemoveBranchLoopProg .skip) s₁ s₁ 9 := by
      simpa only [gm02HostBranchLoopExpr_cost] using Exec.ite_false htest₀ (Exec.skip s₁)
    have hH₁ : s₁.arrs 21 = hflags := (congrFun ha₁ 21).trans hH
    refine ⟨s₁, 23, .seq he₁ he₂, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((congrFun ha₁ 20).trans hG).trans (gm02HostLoopFlags_skip_next x e ht).symm
    · rw [hH₁]; exact hHlen
    · rw [hH₁]; exact hbits
    · simp only [ha₁, hG, hH]
    · intro a _ _; exact congrFun ha₁ a
    · intro r _ _ hr42 _ hr44
      exact hr₁ r hr42 hr44
  | true =>
    have htest₁ : gm02HostBranchLoopExpr.eval w s₁ = some 1 := by
      simpa only [ht, ↓reduceIte] using htest
    have hloop := gm02HostLoopFlags_next_loop x e ht
    obtain ⟨s₂, t₂, he₂, ht₂, hG₂, hH₂, hTopo, ha₂, hr₂⟩ := gm02RemoveBranchLoopProg_exec x s₁
      (gm02HostLoopFlags x e.val) hflags e.val (x.G.edges[e.val]'e.isLt).1.val
      (by rw [ha₁]; exact hsrc) (by rw [ha₁]; exact hG) (by rw [ha₁]; exact hH)
      (gm02HostLoopFlags_length x _) hHlen hbits
      (by rw [gm02HostLoopFlags_length]; exact e.isLt)
      (by rw [hr₁ 32 (by decide) (by decide)]; exact hE)
      (by rw [hr₁ 15 (by decide) (by decide)]; exact hM)
      (by rw [hr₁ 16 (by decide) (by decide)]; exact hoff) hleft hloop.1 hloop.2 hw hn hlen
    have heIf : Exec w (.ite gm02HostBranchLoopExpr gm02RemoveBranchLoopProg .skip) s₁ s₂ (8 + t₂) := by
      simpa only [gm02HostBranchLoopExpr_cost] using Exec.ite_true htest₁ (by decide : 1 ≠ 0) he₂
    refine ⟨s₂, 14 + (8 + t₂), .seq he₁ heIf, by omega, ?_, ?_, ?_, hTopo, ?_, ?_⟩
    · exact hG₂.trans (gm02HostLoopFlags_set_next x e ht)
    · rw [hH₂, gm02MatchedPatternFlags_length]
      exact hHlen
    · rw [hH₂]
      exact gm02MatchedPatternFlags_bits x hflags _ hbits
    · intro a ha20 ha21
      exact (ha₂ a ha20 ha21).trans (congrFun ha₁ a)
    · intro r hr40 hr41 hr42 hr43 hr44
      exact (hr₂ r hr40 hr41 hr43).trans (hr₁ r hr42 hr44)

end GraphMinor.Compute
