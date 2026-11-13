module

public import GraphMinor.Compute.GM02ReadTopologicalHeader
public import GraphMinor.Compute.GM02InitEdgeFlags
public import GraphMinor.Compute.GM02InitPatternVertices

/-!
# Initialization of the topological-containment machine

Compose the plain-header reader, the two all-one edge arrays, and the
pattern vertex mask. The resulting state retains every supplied edge
and records exactly the input pattern vertices. The total initialization
time is linear in the sum of the two actual graph sizes.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the supplied graph pair and initialize its three working arrays. -/
def gm02InitializeTopologicalProg : Cmd :=
  .seq (gm02ReadTopologicalHeaderProg inArr) (.seq gm02InitEdgeFlagsProg gm02InitPatternVerticesProg)

/-- The actual initialization program has linear cost and preserves all supplied input words. -/
theorem gm02InitializeTopologicalProg_exec {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (hsrc : s.arrs inArr = x.enc) (hw : 2 < 2 ^ w)
    (hsize : gm02TopologicalSize x < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w gm02InitializeTopologicalProg s s' t ∧
      t ≤ 14 * gm02TopologicalSize x + 52 ∧ s'.arrs inArr = x.enc ∧
      s'.regs 10 = x.G.n ∧ s'.regs 11 = x.G.edges.length ∧
      s'.regs 12 = 2 + 2 * x.G.edges.length ∧ s'.regs 13 = x.vertices.card ∧
      s'.regs 14 = 3 + 2 * x.G.edges.length + x.vertices.card ∧
      s'.regs 15 = x.edges.length ∧ s'.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card ∧
      s'.arrs 20 = List.replicate x.G.edges.length 1 ∧
      s'.arrs 21 = List.replicate x.edges.length 1 ∧ s'.arrs 22 = bitSetList x.vertices ∧
      (∀ a, a ≠ 20 → a ≠ 21 → a ≠ 22 → s'.arrs a = s.arrs a) := by
  have hw₁ : 1 < 2 ^ w := by omega
  have hnw : x.G.n < 2 ^ w := by unfold gm02TopologicalSize GM02EdgeListInput.size at hsize; omega
  have hMw : x.G.edges.length < 2 ^ w := by unfold gm02TopologicalSize GM02EdgeListInput.size at hsize; omega
  have hHw : x.edges.length < 2 ^ w := by unfold gm02TopologicalSize at hsize; omega
  obtain ⟨s₁, he₁, h10, h11, h12, h13, h14, h15, h16, ha₁, _⟩ :=
    gm02ReadTopologicalHeaderProg_exec x inArr s hsrc hw hsize hlen
  obtain ⟨s₂, t₂, he₂, ht₂, hG₂, hH₂, ha₂, hr₂⟩ :=
    gm02InitEdgeFlagsProg_exec x s₁ h11 h15 hw₁ hMw hHw
  have hsrc₂ : s₂.arrs inArr = x.enc := by rw [ha₂ inArr (by decide) (by decide), ha₁]; exact hsrc
  obtain ⟨s₃, t₃, he₃, ht₃, hV₃, ha₃, hr₃⟩ := gm02InitPatternVerticesProg_exec x s₂ hsrc₂
    (by rw [hr₂ 10 (by decide) (by decide)]; exact h10)
    (by rw [hr₂ 12 (by decide) (by decide)]; exact h12)
    (by rw [hr₂ 13 (by decide) (by decide)]; exact h13) hw₁ hnw hlen
  have hmeta : ∀ r, r ≠ 17 → r ≠ 30 → r ≠ 31 → s₃.regs r = s₁.regs r := by
    intro r h17 h30 h31
    rw [hr₃ r h17 h30, hr₂ r h30 h31]
  refine ⟨s₃, 28 + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hV₃, ?_⟩
  · unfold gm02TopologicalSize GM02EdgeListInput.size
    omega
  · rw [ha₃ inArr (by decide)]
    exact hsrc₂
  · rw [hmeta 10 (by decide) (by decide) (by decide)]; exact h10
  · rw [hmeta 11 (by decide) (by decide) (by decide)]; exact h11
  · rw [hmeta 12 (by decide) (by decide) (by decide)]; exact h12
  · rw [hmeta 13 (by decide) (by decide) (by decide)]; exact h13
  · rw [hmeta 14 (by decide) (by decide) (by decide)]; exact h14
  · rw [hmeta 15 (by decide) (by decide) (by decide)]; exact h15
  · rw [hmeta 16 (by decide) (by decide) (by decide)]; exact h16
  · rw [ha₃ 20 (by decide)]; exact hG₂
  · rw [ha₃ 21 (by decide)]; exact hH₂
  · intro a ha20 ha21 ha22
    rw [ha₃ a ha22, ha₂ a ha20 ha21, ha₁]

end GraphMinor.Compute
