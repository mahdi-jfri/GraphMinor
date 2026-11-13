module

public import GraphMinor.Compute.GM02RecursiveReturnProgram
import GraphMinor.Compute.GM02RecursiveWorkFrames

/-!
# Restoring the catalogue and boundary names of a popped parent

Copy the saved catalogue word back to its working register and rebuild
the compact inverse vertex names from the restored parent and side bits.
This leaves the child's answer and every recursive control word intact.
The restored names can therefore be used by the next exact child call.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- A popped parent's plain arrays reconstruct its boundary while retaining its answer. -/
theorem gm02RecursiveRestoreBoundaryProg_exec {w : ℕ} (q : ℕ)
    (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n)) (catalogue : ℕ) (s : State)
    (hsrc : s.arrs (gm02RecursiveParentArr q) = x.enc)
    (hL : s.arrs outArr = bitSetList L) (hR : s.arrs 2 = bitSetList R)
    (hcat : s.regs (gm02RecursiveControlBase q + 7) = catalogue)
    (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) (hc : catalogue < 2 ^ w) :
    ∃ s' t, Exec w (gm02RecursiveRestoreBoundaryProg q) s s' t ∧
      t ≤ 63 * x.n + 28 * x.A.index + 61 ∧
      s'.regs 330 = catalogue ∧ s'.regs outReg = s.regs outReg ∧ s'.regs 40 = x.n ∧
      s'.arrs (gm02RecursiveParentArr q + 4) = List.ofFn
        (fun i : Fin (gm02CompressedBoundaryInput x L R).n =>
          (compactEmb (gm02BoundaryDeletedSet x L R) i).val) ∧
      (∀ j, j ≤ gm02RecursiveParentArr q ∨ gm02RecursiveParentArr q + 4 < j → s'.arrs j = s.arrs j) ∧
      (∀ offset : ℕ, s'.regs (gm02RecursiveControlBase q + offset) =
        s.regs (gm02RecursiveControlBase q + offset)) := by
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  have hpg := gm02RecursiveParentArr_ge q
  have hbg := gm02RecursiveControlBase_ge q
  let s₁ := s.setReg 330 catalogue
  have he₁ : Exec w (.assign 330 (.reg (b + 7))) s s₁ 2 :=
    Exec.assign (by simp [Expr.eval, b, hcat, checkWord_of_lt hc])
  obtain ⟨s₂, t₂, he₂, ht₂, _, _, horig, hn₂, _, _, ha₂⟩ :=
    gm02PrepareBoundaryNumberingProg_exec x L R p
      (by dsimp only [p, Arr] at *; omega) s₁ hsrc hL hR hn hlen
  have hcatNW : (330 : Reg) ∉ (gm02PrepareBoundaryNumberingProg p).writtenRegs := by
    change (330 : Reg) ∉ (gm02PrepareBoundaryNumberingProg 0).writtenRegs
    decide
  have houtNW : outReg ∉ (gm02PrepareBoundaryNumberingProg p).writtenRegs := by
    change (0 : Reg) ∉ (gm02PrepareBoundaryNumberingProg 0).writtenRegs
    decide
  refine ⟨s₂, 2 + t₂, Exec.seq he₁ he₂, by omega, ?_, ?_, hn₂, horig, ha₂, ?_⟩
  · exact (he₂.regs_eq_of_not_mem_writtenRegs hcatNW).trans (by simp [s₁])
  · exact (he₂.regs_eq_of_not_mem_writtenRegs houtNW).trans
      (State.setReg_regs_ne _ _ (by decide : outReg ≠ 330))
  · intro offset
    exact (gm02_regs_eq_of_low_writes he₂ (gm02PrepareBoundaryNumberingProg_writtenRegs_subset p)
      _ (by dsimp only [b, Reg] at *; omega)).trans
      (State.setReg_regs_ne _ _ (by dsimp only [b, Reg] at *; omega))

end GraphMinor.Compute
