module

public import GraphMinor.Compute.GM02ReadSavedHeader
public import GraphMinor.Compute.GM02SavedFrameWords

/-!
# Restoring a saved frame's lengths and loop state

Start the header stream at the recovered frame pointer and read its
eight words into a consecutive control-register block. The read cursor
then points to the saved parent input. The starting pointer and every
array remain intact for the later payload restoration and stack pop.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the eight saved header words into the control block. -/
def gm02RestoreFrameHeaderProg (stack : Arr) (r_start r_read r_base : Reg) : Cmd :=
  .seq (.assign r_read (.reg r_start)) (gm02ReadSavedHeaderProg stack r_read r_base 8)

/-- Restoring the header recovers all three lengths and all five loop-state words. -/
theorem gm02RestoreFrameHeaderProg_exec {w off : ℕ} (stack : Arr)
    (r_start r_read r_base : Reg) (hs : r_base + 8 ≤ r_start) (hr : r_base + 8 ≤ r_read)
    (hsr : r_start ≠ r_read) (P L R rest : List ℕ)
    (mode code aggregate leftAnswer catalogue : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlen : off + 8 < 2 ^ w)
    (hwords : ∀ v ∈ gm02SavedFrameHeader P L R mode code aggregate leftAnswer catalogue, v < 2 ^ w)
    (hstream : AtStream stack off
      (gm02SavedFrameHeader P L R mode code aggregate leftAnswer catalogue ++ rest) s)
    (hstart : s.regs r_start = off) :
    ∃ s' t, Exec w (gm02RestoreFrameHeaderProg stack r_start r_read r_base) s s' t ∧ t ≤ 67 ∧
      s'.regs r_base = P.length ∧ s'.regs (r_base + 1) = L.length ∧
      s'.regs (r_base + 2) = R.length ∧ s'.regs (r_base + 3) = mode ∧
      s'.regs (r_base + 4) = code ∧ s'.regs (r_base + 5) = aggregate ∧
      s'.regs (r_base + 6) = leftAnswer ∧ s'.regs (r_base + 7) = catalogue ∧
      s'.regs r_read = off + 8 ∧ s'.regs r_start = off ∧ s'.arrs = s.arrs ∧
      (∀ r, r ≠ r_read → r < r_base ∨ r_base + 8 ≤ r → s'.regs r = s.regs r) := by
  let H := gm02SavedFrameHeader P L R mode code aggregate leftAnswer catalogue
  let s₁ := s.setReg r_read off
  have he₁ : Exec w (.assign r_read (.reg r_start)) s s₁ 2 :=
    Exec.assign (by simp [Expr.eval, hstart, checkWord_of_lt (by omega : off < 2 ^ w)])
  obtain ⟨s₂, t₂, he₂, ht₂, hvals, hpos, _, ha, hregs⟩ := gm02ReadSavedHeaderProg_exec
    stack r_read r_base H rest s₁ (by simpa only [H, gm02SavedFrameHeader_length] using hr)
    hw (by simpa only [H, gm02SavedFrameHeader_length] using hlen) hwords hstream (by simp [s₁])
  have hv (i : ℕ) (hi : i < 8) : s₂.regs (r_base + i) = H[i]'(by simpa only [H, gm02SavedFrameHeader_length] using hi) :=
    hvals i (by simpa only [H, gm02SavedFrameHeader_length] using hi)
  have hkeep (r : Reg) (hne : r ≠ r_read) (hout : r < r_base ∨ r_base + 8 ≤ r) :
      s₂.regs r = s.regs r := by
    have h := hregs r hne (by simpa only [H, gm02SavedFrameHeader_length] using hout)
    exact h.trans (State.setReg_regs_ne _ _ hne)
  refine ⟨s₂, 2 + t₂, Exec.seq he₁ he₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (hkeep r_start hsr (Or.inr hs)).trans hstart, ha, hkeep⟩
  · simp only [H, gm02SavedFrameHeader_length] at ht₂
    omega
  · simpa only [H, gm02SavedFrameHeader, List.getElem_cons_zero, Nat.add_zero] using hv 0 (by decide)
  · simpa only [H, gm02SavedFrameHeader, List.getElem_cons_succ, List.getElem_cons_zero] using hv 1 (by decide)
  · simpa only [H, gm02SavedFrameHeader, List.getElem_cons_succ, List.getElem_cons_zero] using hv 2 (by decide)
  · simpa only [H, gm02SavedFrameHeader, List.getElem_cons_succ, List.getElem_cons_zero] using hv 3 (by decide)
  · simpa only [H, gm02SavedFrameHeader, List.getElem_cons_succ, List.getElem_cons_zero] using hv 4 (by decide)
  · simpa only [H, gm02SavedFrameHeader, List.getElem_cons_succ, List.getElem_cons_zero] using hv 5 (by decide)
  · simpa only [H, gm02SavedFrameHeader, List.getElem_cons_succ, List.getElem_cons_zero] using hv 6 (by decide)
  · simpa only [H, gm02SavedFrameHeader, List.getElem_cons_succ, List.getElem_cons_zero] using hv 7 (by decide)
  · simpa only [H, gm02SavedFrameHeader_length] using hpos

end GraphMinor.Compute
