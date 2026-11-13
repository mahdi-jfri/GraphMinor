module

public import GraphMinor.Compute.GM02PortEdgeBody
public import GraphMinor.Compute.GM02PortEdgePrefix

/-!
# The edge scan body advances the canonical encoding prefix

Combine the actual pair-scan command with the filtered-prefix recurrence.
The exact buffer update and remaining capacity follow in both cases,
whether or not the current pair is emitted. This supplies the invariant
step for constructing the numeric graph's canonical encoding.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- The actual edge-scan body advances the full canonical buffer invariant in at most 95 steps. -/
theorem gm02PortEdgeBody_prefix_exec {w K code : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (gflags hflags : List ℕ)
    (i : Fin (gm02FullPortSize x K * gm02FullPortSize x K))
    (hsrc : s.arrs src = x.enc) (hG : s.arrs 20 = gflags)
    (hGlen : gflags.length = x.G.edges.length) (hGbits : ∀ b ∈ gflags, b ≤ 1)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length)
    (hHbits : ∀ b ∈ hflags, b ≤ 1) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hslots : s.arrs 23 = List.ofFn (fun j : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code j.val))
    (hindex : s.regs 64 = i.val) (hsize : s.regs 66 = gm02FullPortSize x K)
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hbuf : s.arrs 24 = gm02PortEdgeBuffer (gm02FullPortGraph x gflags hflags code K) i.val)
    (hpos : s.regs 67 = (gm02PortEdgeWords (gm02FullPortGraph x gflags hflags code K) i.val).length)
    (hcount : s.regs 68 = (gm02EdgePrefix (gm02FullPortGraph x gflags hflags code K) i.val).length)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hfw : x.edges.length < 2 ^ w) (henc : x.enc.length < 2 ^ w)
    (hcap : 2 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) < 2 ^ w) :
    ∃ s' t, Exec w (gm02PortEdgeBody src) s s' t ∧ t ≤ 95 ∧
      s'.arrs 24 = gm02PortEdgeBuffer (gm02FullPortGraph x gflags hflags code K) (i.val + 1) ∧
      s'.regs 67 = (gm02PortEdgeWords (gm02FullPortGraph x gflags hflags code K) (i.val + 1)).length ∧
      s'.regs 68 = (gm02EdgePrefix (gm02FullPortGraph x gflags hflags code K) (i.val + 1)).length ∧
      (∀ a, a ≠ 24 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 32 → r ≠ 42 → r ≠ 43 → r ≠ 44 → r ≠ 45 → r ≠ 46 →
        r ≠ 60 → r ≠ 61 → r ≠ 62 → r ≠ 63 → r ≠ 67 → r ≠ 68 → s'.regs r = s.regs r) := by
  let F := gm02FullPortGraph x gflags hflags code K
  let N := gm02FullPortSize x K
  let m := (gm02EdgePrefix F i.val).length
  let rem := 2 * (N * N - (m + 1))
  have hlen := gm02EdgePrefix_length_le F i.val
  have hi := i.isLt
  have hbuf' : s.arrs 24 = gm02PortEdgeWords F i.val ++ List.replicate (rem + 2) 0 := by
    rw [hbuf, gm02PortEdgeBuffer, gm02PortEdgeBuffer_room]
  have hposw : (gm02PortEdgeWords F i.val).length + 2 < 2 ^ w := by
    rw [gm02PortEdgeWords_length]
    omega
  have hcountw : m + 1 < 2 ^ w := by dsimp only [m]; omega
  obtain ⟨s', t, he, ht, hout, ha, hr⟩ :=
    gm02PortEdgeBody_exec x s src gflags hflags i (gm02PortEdgeWords F i.val)
      hsrc hG hGlen hGbits hH hHlen hHbits hmask hslots hindex hsize hn hm hf
      hbuf' hpos hcount hw hN (by omega) hfw henc hposw hcountw
  refine ⟨s', t, he, ht, ?_, ?_, ?_, ha, hr⟩
  all_goals by_cases hem : (finProdFinEquiv.symm i : Fin N × Fin N).1.val <
      (finProdFinEquiv.symm i : Fin N × Fin N).2.val ∧ (gm02FullPortGraph x gflags hflags code K).Adj (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  · simp only [hem] at hout
    rw [gm02PortEdgeBuffer_succ, ite_eq_left hem]
    exact hout.1
  · simp only [hem, ite_false] at hout
    rw [gm02PortEdgeBuffer_succ, ite_eq_right hem]
    exact hout.1.trans hbuf
  · simp only [hem] at hout
    rw [gm02PortEdgeWords_succ, ite_eq_left hem]
    exact hout.2.1
  · simp only [hem, ite_false] at hout
    rw [gm02PortEdgeWords_succ, ite_eq_right hem]
    exact hout.2.1
  · simp only [hem] at hout
    rw [gm02EdgePrefix_succ, ite_eq_left hem, List.length_append, List.length_singleton]
    exact hout.2.2
  · simp only [hem, ite_false] at hout
    rw [gm02EdgePrefix_succ, ite_eq_right hem]
    exact hout.2.2

end GraphMinor.Compute
