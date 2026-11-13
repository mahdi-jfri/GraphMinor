module

public import GraphMinor.Compute.GM02InitializeTopological
public import GraphMinor.Compute.GM02HostLoopScan
import Mathlib.Tactic.Linarith

/-!
# Complete branch-loop preprocessing for II (4.6)

Initialize the plain graph-pair input, then run the full host-loop scan.
The actual resulting arrays describe subgraphs with the same vertices,
no host loop at a pattern vertex, and exactly the same topological
question as the original graphs. The initialization and scan bounds
combine into a quadratic bound in the paper's graph-size measure.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- The initialization and complete matched branch-loop removal from II (4.6). -/
def gm02EliminateBranchLoopsProg : Cmd :=
  .seq gm02InitializeTopologicalProg gm02HostLoopScanProg

private theorem preprocessing_time_le (N m k : ℕ) (hm : m ≤ N) (hk : k ≤ N) :
    14 * N + 52 + (m * (41 * k + 45) + 5) ≤ 120 * (N + 1) ^ 2 := by
  have hp := Nat.mul_le_mul hm hk
  nlinarith

/-- The actual branch-loop preprocessing preserves the topological test, removes all branch loops, and takes quadratic time. -/
theorem gm02EliminateBranchLoopsProg_exec {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (hsrc : s.arrs inArr = x.enc) (hw : 2 < 2 ^ w)
    (hsize : gm02TopologicalSize x < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w gm02EliminateBranchLoopsProg s s' t ∧ t ≤ 120 * (gm02TopologicalSize x + 1) ^ 2 ∧
      s'.arrs inArr = x.enc ∧ s'.arrs 22 = bitSetList x.vertices ∧
      s'.regs 10 = x.G.n ∧ s'.regs 11 = x.G.edges.length ∧
      s'.regs 12 = 2 + 2 * x.G.edges.length ∧ s'.regs 13 = x.vertices.card ∧
      s'.regs 14 = 3 + 2 * x.G.edges.length + x.vertices.card ∧
      s'.regs 15 = x.edges.length ∧ s'.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card ∧
      s'.arrs 20 = gm02HostLoopFlags x x.G.edges.length ∧
      (s'.arrs 21).length = x.edges.length ∧ (∀ b ∈ s'.arrs 21, b ≤ 1) ∧
      (TopologicallyContains x.G.graph x.H ↔
        TopologicallyContains (gm02ActiveGraph x.G.graph (s'.arrs 20)) (gm02ActiveGraph x.H (s'.arrs 21))) ∧
      (∀ e v, v ∈ V(x.H) → ¬(gm02ActiveGraph x.G.graph (s'.arrs 20)).IsLoopAt e v) ∧
      (∀ a, a ≠ 20 → a ≠ 21 → a ≠ 22 → s'.arrs a = s.arrs a) := by
  have hnw : x.G.n < 2 ^ w := by unfold gm02TopologicalSize GM02EdgeListInput.size at hsize; omega
  have hmSize : x.G.edges.length ≤ gm02TopologicalSize x := by unfold gm02TopologicalSize GM02EdgeListInput.size; omega
  have hkSize : x.edges.length ≤ gm02TopologicalSize x := by unfold gm02TopologicalSize; omega
  obtain ⟨s₁, t₁, he₁, ht₁, hsrc₁, h10, h11, h12, h13, h14, h15, h16, hG₁, hH₁, hV₁, ha₁⟩ :=
    gm02InitializeTopologicalProg_exec x s hsrc hw hsize hlen
  have hbits : ∀ b ∈ List.replicate x.edges.length 1, b ≤ 1 := by
    intro b hb
    obtain ⟨_, rfl⟩ := List.mem_replicate.1 hb
    exact le_rfl
  obtain ⟨s₂, t₂, he₂, ht₂, hG₂, hHlen₂, hbits₂, hTopo₂, hNoLoop₂, ha₂, hr₂⟩ :=
    gm02HostLoopScanProg_exec x s₁ (List.replicate x.edges.length 1) hsrc₁
      (by simpa only [gm02HostLoopFlags_zero] using hG₁) hH₁ hV₁ (List.length_replicate ..) hbits
      h11 h15 h16 hw hnw hlen
  have hInitH : gm02ActiveGraph x.H (List.replicate x.edges.length 1) = x.H := by
    apply gm02ActiveGraph_replicate
    exact x.pattern_edges.le
  have hmeta : ∀ r, r ≠ 32 → r ≠ 40 → r ≠ 41 → r ≠ 42 → r ≠ 43 → r ≠ 44 → s₂.regs r = s₁.regs r := hr₂
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hG₂,
    hHlen₂, hbits₂, ?_, hNoLoop₂, ?_⟩
  · exact (Nat.add_le_add ht₁ ht₂).trans (preprocessing_time_le _ _ _ hmSize hkSize)
  · rw [ha₂ inArr (by decide) (by decide)]; exact hsrc₁
  · rw [ha₂ 22 (by decide) (by decide)]; exact hV₁
  · rw [hmeta 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10
  · rw [hmeta 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h11
  · rw [hmeta 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h12
  · rw [hmeta 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h13
  · rw [hmeta 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h14
  · rw [hmeta 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h15
  · rw [hmeta 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h16
  · simpa only [hInitH] using hTopo₂
  · intro a ha20 ha21 ha22
    exact (ha₂ a ha20 ha21).trans (ha₁ a ha20 ha21 ha22)

end GraphMinor.Compute
