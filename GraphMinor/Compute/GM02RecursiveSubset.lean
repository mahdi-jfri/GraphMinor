module

public import GraphMinor.Compute.GM02AllVertexSupport
public import GraphMinor.Compute.GM02TerminalSupportProg
public import GraphMinor.Compute.GM02BalancedSeparationInput

/-!
# The two separator subsets in II's alternating routines

A1 balances all vertices and A2 balances only terminal endpoints. Both
subsets are constructed from the same plain terminated input. The phase
is fixed program control, while the graph and endpoint data are read
from the input array. A common linear bound covers both constructors.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- The subset specified by the current alternating routine, II pages 316–317. -/
def gm02RecursiveSubset (allVertices : Bool) (x : GM02SimpleTerminatedInput) : Finset (Fin x.n) :=
  if allVertices then Finset.univ else (gm02TerminalVertices x.A).toFinset

/-- Construct the subset bits used by A1 or A2. -/
def gm02RecursiveSubsetProg (allVertices : Bool) (src dst : Arr) : Cmd :=
  if allVertices then gm02AllVertexSupportProg src dst else gm02TerminalSupportProg src dst

/-- Both phase subsets are computed from the plain terminated input in
linear time, preserving every array except the subset output. -/
theorem gm02RecursiveSubsetProg_exec {w : ℕ} (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (src dst : Arr) (hne : src ≠ dst) (s : State) (hsrc : s.arrs src = x.enc)
    (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02RecursiveSubsetProg allVertices src dst) s s' t ∧
      t ≤ 14 * x.n + 29 + 28 * x.A.index ∧
      s'.arrs dst = gm02VertexBits (gm02RecursiveSubset allVertices x) ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 40 → r ≠ 280 → r ≠ 281 → r ≠ 282 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by have hl := x.enc_length; omega
  cases allVertices with
  | false =>
    obtain ⟨s', t, he, ht, hout, _, _, _, ha, hr⟩ :=
      gm02TerminalSupportProg_exec x src dst hne s hsrc hn hlen
    refine ⟨s', t, he, by omega, ?_, ha, hr⟩
    exact hout
  | true =>
    obtain ⟨s', t, he, ht, hk, hout⟩ := gm02AllVertexSupportProg_exec x src dst hne s hsrc hn hw
    refine ⟨s', t, he, by omega, ?_, ?_, ?_⟩
    · simpa only [gm02RecursiveSubset, ↓reduceIte, gm02VertexBits,
        Finset.mem_univ, ite_true, List.ofFn_const] using hout
    · intro a ha
      exact hk.2 a (by simpa only [List.mem_singleton] using ha)
    · intro r _ _ _ hr
      exact hk.1 r (by simpa only [List.mem_singleton] using hr)

end GraphMinor.Compute
