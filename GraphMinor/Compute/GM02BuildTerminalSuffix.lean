module

public import GraphMinor.Compute.GM02InitTerminalBuffer
public import GraphMinor.Compute.GM02TerminalScan
public import GraphMinor.Compute.GM02FinalizeTerminalBuffer

/-!
# Building the terminal encoding suffix

Initialize the terminal buffer, scan active supplied pattern positions,
and fill and copy its count header and endpoint words. The output is
exactly the terminal suffix that accompanies the numeric split graph.
All graph and input arrays survive, and the time is linear in the
supplied pattern edge count.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Build the active terminal count and pair words in array 27. -/
@[expose] def gm02BuildTerminalSuffixProg : Cmd :=
  .seq gm02InitTerminalBufferProg (.seq gm02TerminalScanProg gm02FinalizeTerminalBufferProg)

private theorem outside_terminal_scan {r : ℕ} (h : r < 60 ∨ 82 < r) : r ∉ gm02TerminalScanRegs := by
  simp [gm02TerminalScanRegs]
  omega

private theorem outside_terminal_init {r : ℕ} (h : r < 60 ∨ 82 < r) : r ∉ [73, 74, 75, 76, 77] := by
  simp
  omega

/-- The complete terminal suffix builder has exact output and a linear RAM time bound. -/
theorem gm02BuildTerminalSuffixProg_exec {w K : ℕ} (x : GM02TopologicalInput) (hflags : List ℕ)
    (hK : x.edges.length ≤ K) (s : State)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length) (hbits : ∀ b ∈ hflags, b ≤ 1)
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hcap : 1 + 2 * x.edges.length < 2 ^ w) :
    ∃ s' t, Exec w gm02BuildTerminalSuffixProg s s' t ∧ t ≤ 49 + 73 * x.edges.length ∧
      s'.arrs 27 = [(gm02ActiveTerminalList x hflags K hK).length] ++
        flatEdges (gm02ActiveTerminalList x hflags K hK) ∧
      s'.regs 76 = (gm02ActiveTerminalList x hflags K hK).length ∧ s'.regs 66 = s.regs 66 ∧
      (∀ a, a ≠ 26 → a ≠ 27 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 60 ∨ 82 < r → s'.regs r = s.regs r) := by
  obtain ⟨s₀, he₀, hbuf₀, hbase₀, hzero₀, hpos₀, hcount₀, ha₀, hr₀⟩ :=
    gm02InitTerminalBufferProg_exec x hflags hK s hn hm hf hw hN hcap
  obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, hpos₁, hcount₁, ha₁, hr₁⟩ :=
    gm02TerminalScanProg_exec x hflags hK s₀ ((ha₀ 21 (by decide)).trans hH) hHlen hbits hbase₀ hzero₀
      ((hr₀ 15 (by decide)).trans hf) hbuf₀ hpos₀ hcount₀ hw hN hcap
  obtain ⟨s₂, t₂, he₂, ht₂, hout, ha₂, hr₂⟩ :=
    gm02FinalizeTerminalBufferProg_exec x hflags hK s₁ hbuf₁ hpos₁ hcount₁ (by omega) hN hcap
  refine ⟨s₂, (18 + 2 * x.edges.length) + (t₁ + t₂), .seq he₀ (.seq he₁ he₂), by omega,
    hout, ?_, ?_, ?_, ?_⟩
  · exact (hr₂ 76 (Or.inl (by decide))).trans hcount₁
  · exact (hr₂ 66 (Or.inl (by decide))).trans ((hr₁ 66 (by decide)).trans (hr₀ 66 (by decide)))
  · intro a ha26 ha27
    exact (ha₂ a ha26 ha27).trans ((ha₁ a ha26).trans (ha₀ a ha26))
  · intro r hrange
    have hcopy : r < 80 ∨ 82 < r := hrange.elim (fun h => Or.inl (h.trans (by decide))) Or.inr
    exact (hr₂ r hcopy).trans ((hr₁ r (outside_terminal_scan hrange)).trans
      (hr₀ r (outside_terminal_init hrange)))

end GraphMinor.Compute
