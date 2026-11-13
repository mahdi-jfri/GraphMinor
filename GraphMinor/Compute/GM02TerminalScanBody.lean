module

public import GraphMinor.Compute.GM02AppendTerminalPair
import GraphMinor.Compute.CrossingOpsBasic

/-!
# One step of the active terminal scan

Read the supplied pattern flag at the current position. Append its
fixed pair only when the flag is one. The prefix recurrence proves the
new exact buffer, used position, and pair count. No input array changes.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Append the next supplied pattern position's terminal pair if it is active. -/
@[expose] def gm02TerminalScanBody : Cmd :=
  .ite (.op .eq (.read 21 (.reg 74)) (.const 1)) gm02AppendTerminalPairProg .skip

/-- The guarded terminal step advances the exact prefix invariant in at most 32 steps. -/
theorem gm02TerminalScanBody_exec {w K : ℕ} (x : GM02TopologicalInput) (hflags : List ℕ)
    (hK : x.edges.length ≤ K) (f : Fin x.edges.length) (s : State)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length)
    (hbits : ∀ b ∈ hflags, b ≤ 1) (hbase : s.regs 73 = x.G.n + x.G.edges.length)
    (hf : s.regs 74 = f.val)
    (hbuf : s.arrs 26 = gm02TerminalBuffer x hflags K hK f.val)
    (hpos : s.regs 75 = (gm02TerminalWords x hflags K hK f.val).length)
    (hcount : s.regs 76 = (gm02TerminalPrefix x hflags K hK f.val).length)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hcap : 1 + 2 * x.edges.length < 2 ^ w) :
    ∃ s' t, Exec w gm02TerminalScanBody s s' t ∧ t ≤ 32 ∧
      s'.arrs 26 = gm02TerminalBuffer x hflags K hK (f.val + 1) ∧
      s'.regs 75 = (gm02TerminalWords x hflags K hK (f.val + 1)).length ∧
      s'.regs 76 = (gm02TerminalPrefix x hflags K hK (f.val + 1)).length ∧
      (∀ a, a ≠ 26 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 60 → r ≠ 61 → r ≠ 75 → r ≠ 76 → s'.regs r = s.regs r) := by
  have hfi : f.val < hflags.length := hHlen.symm ▸ f.isLt
  let flag := hflags[f.val]'hfi
  have hflag : flag ≤ 1 := hbits _ (List.getElem_mem hfi)
  have hget : hflags[f.val]? = some flag := List.getElem?_eq_some_iff.2 ⟨hfi, rfl⟩
  have hgetS : (s.arrs 21)[f.val]? = some flag := by rw [hH]; exact hget
  obtain ⟨hi, hval⟩ := List.getElem?_eq_some_iff.1 hgetS
  have hfw : f.val < 2 ^ w := by have := f.isLt; omega
  have hread := (eval_read (eval_reg hf hfw) hi (hval ▸ hflag.trans_lt (by omega))).trans (congrArg some hval)
  have hguard := eval_eq hread (eval_const (by omega : 1 < 2 ^ w)) (by omega)
  have hiff : hflags[f.val]? = some 1 ↔ flag = 1 := by rw [hget]; exact ⟨Option.some.inj, congrArg some⟩
  by_cases hactive : hflags[f.val]? = some 1
  · have hg : (Expr.op .eq (.read 21 (.reg 74)) (.const 1)).eval w s = some 1 := by
      simpa only [hiff.1 hactive, ↓reduceIte] using hguard
    let rem := 2 * (x.edges.length - ((gm02TerminalPrefix x hflags K hK f.val).length + 1))
    have hbuf' : s.arrs 26 = gm02TerminalWords x hflags K hK f.val ++ List.replicate (rem + 2) 0 := by
      rw [hbuf, gm02TerminalBuffer, gm02TerminalBuffer_room]
    have hlen := gm02TerminalPrefix_length_le x hflags K hK f.val
    have hi := f.isLt
    have hposw : (gm02TerminalWords x hflags K hK f.val).length + 2 < 2 ^ w := by
      rw [gm02TerminalWords_length]
      omega
    have hcountw : (gm02TerminalPrefix x hflags K hK f.val).length + 1 < 2 ^ w := by omega
    obtain ⟨s', t, he, ht, hbuf', hpos', hcount', ha, hr⟩ :=
      gm02AppendTerminalPairProg_exec x hK f (gm02TerminalWords x hflags K hK f.val) s
        hbase hf hbuf' hpos hcount hw hN hposw hcountw
    refine ⟨s', 4 + t, .ite_true hg (by decide) he, by omega, ?_, ?_, ?_, ha, hr⟩
    · rw [gm02TerminalBuffer_succ, ite_eq_left hactive]
      exact hbuf'
    · rw [gm02TerminalWords_succ, ite_eq_left hactive]
      exact hpos'
    · rw [gm02TerminalPrefix_succ, ite_eq_left hactive, List.length_append, List.length_singleton]
      exact hcount'
  · have hg : (Expr.op .eq (.read 21 (.reg 74)) (.const 1)).eval w s = some 0 := by
      simpa only [show flag ≠ 1 from fun h => hactive (hiff.2 h), ↓reduceIte] using hguard
    refine ⟨s, 5, .ite_false hg (.skip s), by decide, ?_, ?_, ?_, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
    · rw [gm02TerminalBuffer_succ, ite_eq_right hactive]
      exact hbuf
    · rw [gm02TerminalWords_succ, ite_eq_right hactive]
      exact hpos
    · rw [gm02TerminalPrefix_succ, ite_eq_right hactive]
      exact hcount

end GraphMinor.Compute
