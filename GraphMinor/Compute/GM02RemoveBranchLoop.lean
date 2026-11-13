module

public import GraphMinor.Compute.GM02PatternLoopScan
public import GraphMinor.Compute.GM02DeleteMatchedLoop

/-!
# The actual removal of one host loop at a branch vertex

Run the finite matching-pattern-loop search, then clear the host flag
and any returned pattern flag. The execution proof preserves the input
and all unrelated working data. The earlier deletion equivalence proves
that the topological-containment question is unchanged by these actual
array updates.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- Remove the branch loop at saved host edge 32 and vertex 42. -/
def gm02RemoveBranchLoopProg : Cmd :=
  .seq (gm02PatternLoopScanProg inArr) gm02DeleteMatchedLoopProg

/-- The actual search and flag writes preserve the topological test in linear pattern-edge time. -/
theorem gm02RemoveBranchLoopProg_exec {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (gflags hflags : List ℕ) (e v : ℕ)
    (hsrc : s.arrs inArr = x.enc) (hG : s.arrs 20 = gflags) (hH : s.arrs 21 = hflags)
    (hGlen : gflags.length = x.G.edges.length) (hHlen : hflags.length = x.edges.length)
    (hbits : ∀ b ∈ hflags, b ≤ 1) (he : e < gflags.length)
    (hE : s.regs 32 = e) (hM : s.regs 15 = x.edges.length)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card) (hV : s.regs 42 = v)
    (hv : v ∈ V(x.H)) (hloop : (gm02ActiveGraph x.G.graph gflags).IsLoopAt e v)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w gm02RemoveBranchLoopProg s s' t ∧ t ≤ 41 * x.edges.length + 16 ∧
      s'.arrs 20 = gflags.set e 0 ∧ s'.arrs 21 = gm02MatchedPatternFlags x hflags v ∧
      (TopologicallyContains (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) ↔
        TopologicallyContains (gm02ActiveGraph x.G.graph (s'.arrs 20)) (gm02ActiveGraph x.H (s'.arrs 21))) ∧
      (∀ a, a ≠ 20 → a ≠ 21 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 40 → r ≠ 41 → r ≠ 43 → s'.regs r = s.regs r) := by
  have hLen := x.enc_length
  have hMw : x.edges.length < 2 ^ w := by omega
  have hew : e < 2 ^ w := by rw [hGlen] at he; omega
  have hvn : v < x.G.n := x.pattern_vertices_subset hv
  have hvw : v < 2 ^ w := hvn.trans hn
  have hw₁ : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, _, hres, ha₁, hr₁⟩ := gm02PatternLoopScanProg_exec x s inArr hflags v
    hsrc hH hHlen hbits hM hoff hV hw hn hvw hlen
  obtain ⟨s₂, t₂, he₂, ht₂, hG₂, hH₂, hr₂, ha₂⟩ := gm02DeleteMatchedLoopProg_exec x s₁ gflags hflags e v
    (by rw [ha₁]; exact hG) (by rw [ha₁]; exact hH) he hHlen
    (by rw [hr₁ 32 (by decide) (by decide) (by decide)]; exact hE)
    (by rw [hr₁ 15 (by decide) (by decide) (by decide)]; exact hM) hres hw₁ hew hMw
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, hG₂, hH₂, ?_, ?_, ?_⟩
  · simpa only [hG₂, hH₂] using gm02MatchedLoopDeletion_correct x gflags hflags e v he hHlen hv hloop
  · intro a ha20 ha21
    rw [ha₂ a ha20 ha21, ha₁]
  · intro r hr40 hr41 hr43
    rw [hr₂]
    exact hr₁ r hr40 hr41 hr43

end GraphMinor.Compute
