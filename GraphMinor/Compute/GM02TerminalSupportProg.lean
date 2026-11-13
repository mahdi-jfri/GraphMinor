module

public import GraphMinor.Compute.GM02ReadTerminatedHeader
public import GraphMinor.Compute.GM02MarkTerminalSupport

/-!
# The complete terminal-support construction for A2

Parse the graph and terminal headers and then mark the supplied endpoint
slice. This routine starts from the plain input alone. It returns the
bits of the termination support, together with the vertex count and
slice metadata needed by the subsequent recursive stages.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Construct the A2 separator subset from the plain terminated input. -/
def gm02TerminalSupportProg (src dst : Arr) : Cmd :=
  .seq (gm02ReadTerminatedHeaderProg src) (gm02MarkTerminalSupportProg src dst)

/-- The A2 subset builder needs no caller-supplied offsets or lengths.
It runs in linear vertex-and-terminal size and preserves the source. -/
theorem gm02TerminalSupportProg_exec {w : ℕ} (x : GM02SimpleTerminatedInput)
    (src dst : Arr) (hne : src ≠ dst) (s : State) (hsrc : s.arrs src = x.enc)
    (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02TerminalSupportProg src dst) s s' t ∧
      t ≤ x.n + 29 + 28 * x.A.index ∧
      s'.arrs dst = bitSetList (gm02TerminalVertices x.A).toFinset ∧
      s'.regs 40 = x.n ∧ s'.regs 280 = 3 + 2 * (edgeListOf x.G).length ∧
      s'.regs 281 = 2 * x.A.index ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 40 → r ≠ 280 → r ≠ 281 → r ≠ 282 → s'.regs r = s.regs r) := by
  obtain ⟨s₁, he₁, h40, h280, h281, ha₁, hr₁⟩ :=
    gm02ReadTerminatedHeaderProg_exec x src s hsrc hn hlen
  obtain ⟨s₂, t₂, he₂, ht₂, hout, ha₂, hr₂⟩ := gm02MarkTerminalSupportProg_exec x src dst hne s₁
    (ha₁ ▸ hsrc) h40 h280 h281 hn hlen
  refine ⟨s₂, _, Exec.seq he₁ he₂, by omega, hout, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hr₂ 40 (by decide)).trans h40
  · exact (hr₂ 280 (by decide)).trans h280
  · exact (hr₂ 281 (by decide)).trans h281
  · intro a ha
    rw [ha₂ a ha, ha₁]
  · intro r h40' h280' h281' h282'
    exact (hr₂ r h282').trans (hr₁ r h40' h280' h281')

end GraphMinor.Compute
