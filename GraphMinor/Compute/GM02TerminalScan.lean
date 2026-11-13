module

public import GraphMinor.Compute.GM02TerminalScanBody
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Scanning the active pattern terminal pairs

The counting-loop invariant records the exact terminal prefix, buffer
position, and pair count after each original pattern position. The body
advances that invariant and preserves the original flags and metadata.
The completed scan writes the whole canonical terminal list in linear
time in the supplied pattern edge count.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- The registers changed by the active terminal scan. -/
@[expose] def gm02TerminalScanRegs : List ℕ := [60, 61, 74, 75, 76]

/-- Scan all original pattern edge positions for their active terminal pairs. -/
@[expose] def gm02TerminalScanProg : Cmd := forUp 74 (.reg 15) gm02TerminalScanBody

/-- The full terminal scan emits precisely the active terminal list in linear RAM time. -/
theorem gm02TerminalScanProg_exec {w K : ℕ} (x : GM02TopologicalInput) (hflags : List ℕ)
    (hK : x.edges.length ≤ K) (s : State)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length) (hbits : ∀ b ∈ hflags, b ≤ 1)
    (hbase : s.regs 73 = x.G.n + x.G.edges.length) (hzero : s.regs 74 = 0)
    (hlen : s.regs 15 = x.edges.length)
    (hbuf : s.arrs 26 = gm02TerminalBuffer x hflags K hK 0)
    (hpos : s.regs 75 = 1) (hcount : s.regs 76 = 0)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hcap : 1 + 2 * x.edges.length < 2 ^ w) :
    ∃ s' t, Exec w gm02TerminalScanProg s s' t ∧ t ≤ 3 + 39 * x.edges.length ∧
      s'.arrs 26 = gm02TerminalBuffer x hflags K hK x.edges.length ∧
      s'.regs 75 = 1 + 2 * (gm02ActiveTerminalList x hflags K hK).length ∧
      s'.regs 76 = (gm02ActiveTerminalList x hflags K hK).length ∧
      (∀ a, a ≠ 26 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ∉ gm02TerminalScanRegs → s'.regs r = s.regs r) := by
  let I : ℕ → State → Prop := fun j st => st.regs 74 = j ∧
    st.arrs 26 = gm02TerminalBuffer x hflags K hK j ∧
    st.regs 75 = (gm02TerminalWords x hflags K hK j).length ∧
    st.regs 76 = (gm02TerminalPrefix x hflags K hK j).length ∧
    (∀ a, a ≠ 26 → st.arrs a = s.arrs a) ∧
    (∀ r, r ∉ gm02TerminalScanRegs → st.regs r = s.regs r)
  have hI : I 0 s := by
    refine ⟨hzero, hbuf, ?_, hcount, fun _ _ => rfl, fun _ _ => rfl⟩
    simpa only [gm02TerminalWords_length, gm02TerminalPrefix_zero, List.length_nil,
      Nat.mul_zero, Nat.add_zero] using hpos
  have hmw : x.edges.length < 2 ^ w := by omega
  obtain ⟨s', t, he, ht, hI'⟩ := forUp_exec' I x.edges.length 32
    (r_i := 74) (hi := .reg 15) (body := gm02TerminalScanBody) (by omega) hmw
    (fun j hj st hst => ⟨hst.1, eval_reg ((hst.2.2.2.2.2 15 (by decide)).trans hlen) hmw⟩)
    (fun j hj st hst => by
      rcases hst with ⟨hindex, hbuffer, hposition, hcounter, harr, hreg⟩
      obtain ⟨st', t, he, ht, hbuf', hpos', hcount', ha', hr'⟩ :=
        gm02TerminalScanBody_exec x hflags hK ⟨j, hj⟩ st
          ((harr 21 (by decide)).trans hH) hHlen hbits
          ((hreg 73 (by decide)).trans hbase) hindex hbuffer hposition hcounter hw hN hcap
      refine ⟨st', t, he, ht, ?_, ?_⟩
      · refine ⟨State.setReg_regs_self .., hbuf', ?_, ?_, ?_, ?_⟩
        · exact (State.setReg_regs_ne st' (j + 1) (by decide : (75 : Reg) ≠ 74)).trans hpos'
        · exact (State.setReg_regs_ne st' (j + 1) (by decide : (76 : Reg) ≠ 74)).trans hcount'
        · intro a ha26
          exact (ha' a ha26).trans (harr a ha26)
        · intro r hrnot
          have hne (a : ℕ) (ha : a ∈ gm02TerminalScanRegs) : r ≠ a := fun h => hrnot (h.symm ▸ ha)
          exact (State.setReg_regs_ne st' (j + 1) (hne 74 (by decide))).trans
            ((hr' r (hne 60 (by decide)) (hne 61 (by decide)) (hne 75 (by decide)) (hne 76 (by decide))).trans
              (hreg r hrnot))
      · exact (hr' 74 (by decide) (by decide) (by decide) (by decide)).trans hindex) s hI
  refine ⟨s', t, he, ?_, hI'.2.1, ?_, ?_, hI'.2.2.2.2.1, hI'.2.2.2.2.2⟩
  · change t ≤ 3 + x.edges.length * 39 at ht
    omega
  · simpa only [gm02TerminalWords_length, gm02TerminalPrefix_full] using hI'.2.2.1
  · simpa only [gm02TerminalPrefix_full] using hI'.2.2.2.1

end GraphMinor.Compute
