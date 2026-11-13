module

public import GraphMinor.Compute.GM02HostLoopBody
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The complete host-loop removal scan

Process every supplied host edge once. The invariant records the exact
host flag prefix, the pattern flag bounds, and equivalence of the
original and current topological questions. Each body iteration proves
all these properties for its actual writes. At the end, the full-prefix
lemma excludes every host loop at a pattern vertex.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 GraphMinor.Compute.Crossing

/-- Process the full supplied host edge list, removing branch loops and their matches. -/
def gm02HostLoopScanProg : Cmd :=
  .seq (.assign 32 (.const 0)) (forUp 32 (.reg 11) gm02HostLoopBody)

/-- The actual host-loop scan preserves the topological question and removes all branch loops in polynomial time. -/
theorem gm02HostLoopScanProg_exec {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (hflags : List ℕ) (hsrc : s.arrs inArr = x.enc)
    (hG : s.arrs 20 = gm02HostLoopFlags x 0) (hH : s.arrs 21 = hflags)
    (hmask : s.arrs 22 = bitSetList x.vertices)
    (hHlen : hflags.length = x.edges.length) (hbits : ∀ b ∈ hflags, b ≤ 1)
    (hM : s.regs 11 = x.G.edges.length) (hK : s.regs 15 = x.edges.length)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w gm02HostLoopScanProg s s' t ∧
      t ≤ x.G.edges.length * (41 * x.edges.length + 45) + 5 ∧
      s'.arrs 20 = gm02HostLoopFlags x x.G.edges.length ∧
      (s'.arrs 21).length = x.edges.length ∧ (∀ b ∈ s'.arrs 21, b ≤ 1) ∧
      (TopologicallyContains x.G.graph (gm02ActiveGraph x.H hflags) ↔
        TopologicallyContains (gm02ActiveGraph x.G.graph (s'.arrs 20)) (gm02ActiveGraph x.H (s'.arrs 21))) ∧
      (∀ e v, v ∈ V(x.H) → ¬(gm02ActiveGraph x.G.graph (s'.arrs 20)).IsLoopAt e v) ∧
      (∀ a, a ≠ 20 → a ≠ 21 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 32 → r ≠ 40 → r ≠ 41 → r ≠ 42 → r ≠ 43 → r ≠ 44 → s'.regs r = s.regs r) := by
  have hLen := x.enc_length
  have hMw : x.G.edges.length < 2 ^ w := by omega
  have hw₁ : 1 < 2 ^ w := by omega
  have hInitG : gm02ActiveGraph x.G.graph (gm02HostLoopFlags x 0) = x.G.graph := by
    rw [gm02HostLoopFlags_zero]
    exact gm02ActiveGraph_replicate x.G.graph x.G.edges.length Set.Subset.rfl
  let s₀ := s.setReg 32 0
  have he₀ : Exec w (.assign 32 (.const 0)) s s₀ 2 := .assign (eval_const (Nat.two_pow_pos w))
  let I : ℕ → State → Prop := fun j st =>
    st.regs 32 = j ∧ st.arrs 20 = gm02HostLoopFlags x j ∧
      (st.arrs 21).length = x.edges.length ∧ (∀ b ∈ st.arrs 21, b ≤ 1) ∧
      (TopologicallyContains x.G.graph (gm02ActiveGraph x.H hflags) ↔
        TopologicallyContains (gm02ActiveGraph x.G.graph (st.arrs 20)) (gm02ActiveGraph x.H (st.arrs 21))) ∧
      (∀ a, a ≠ 20 → a ≠ 21 → st.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 32 → r ≠ 40 → r ≠ 41 → r ≠ 42 → r ≠ 43 → r ≠ 44 → st.regs r = s.regs r)
  have hI₀ : I 0 s₀ := by
    refine ⟨by simp [s₀], hG, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [s₀, State.setReg_arrs, hH] using hHlen
    · simpa only [s₀, State.setReg_arrs, hH] using hbits
    · simp only [s₀, State.setReg_arrs, hG, hH, hInitG]
    · intro a _ _; rfl
    · intro r hr32 _ _ _ _ _; exact State.setReg_regs_ne _ _ hr32
  obtain ⟨s₁, t₁, he₁, ht₁, hI₁⟩ := forUp_exec' I x.G.edges.length (41 * x.edges.length + 38)
    (r_i := 32) (hi := .reg 11) (body := gm02HostLoopBody) hw₁ hMw
    (fun j hj st hI => by
      refine ⟨hI.1, ?_⟩
      apply eval_reg _ hMw
      rw [hI.2.2.2.2.2.2 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hM)
    (fun j hj st hI => by
      obtain ⟨st', t, he, ht, hG', hHlen', hbits', hTopo', ha', hr'⟩ := gm02HostLoopBody_exec x st ⟨j, hj⟩ (st.arrs 21)
        (by rw [hI.2.2.2.2.2.1 inArr (by decide) (by decide)]; exact hsrc) hI.2.1 rfl
        (by rw [hI.2.2.2.2.2.1 22 (by decide) (by decide)]; exact hmask) hI.2.2.1 hI.2.2.2.1 hI.1
        (by rw [hI.2.2.2.2.2.2 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hK)
        (by rw [hI.2.2.2.2.2.2 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hoff)
        hw hn hlen
      have hTopo : TopologicallyContains x.G.graph (gm02ActiveGraph x.H hflags) ↔
          TopologicallyContains (gm02ActiveGraph x.G.graph (gm02HostLoopFlags x j)) (gm02ActiveGraph x.H (st.arrs 21)) := by
        simpa only [hI.2.1] using hI.2.2.2.2.1
      refine ⟨st', t, he, ht, ?_, ?_⟩
      · refine ⟨State.setReg_regs_self _ _ _, hG', hHlen', hbits', hTopo.trans hTopo', ?_, ?_⟩
        · intro a ha20 ha21
          exact (ha' a ha20 ha21).trans (hI.2.2.2.2.2.1 a ha20 ha21)
        · intro r hr32 hr40 hr41 hr42 hr43 hr44
          rw [State.setReg_regs_ne _ _ hr32]
          exact (hr' r hr40 hr41 hr42 hr43 hr44).trans
            (hI.2.2.2.2.2.2 r hr32 hr40 hr41 hr42 hr43 hr44)
      · rw [hr' 32 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hI.1)
    s₀ hI₀
  refine ⟨s₁, 2 + t₁, .seq he₀ he₁, ?_, hI₁.2.1, hI₁.2.2.1, hI₁.2.2.2.1,
    hI₁.2.2.2.2.1, ?_, hI₁.2.2.2.2.2.1, hI₁.2.2.2.2.2.2⟩
  · have hcost : (Expr.reg 11).cost + 6 + (41 * x.edges.length + 38) = 41 * x.edges.length + 45 := by
      simp only [Expr.cost]
      omega
    rw [hcost] at ht₁
    simp only [Expr.cost] at ht₁
    omega
  · simpa only [hI₁.2.1] using gm02HostLoopFlags_no_branch_loops x

end GraphMinor.Compute
