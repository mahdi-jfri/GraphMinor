module

public import GraphMinor.Compute.GM06LoopErasureScan
public import GraphMinor.Compute.GM06LoopErasureInit
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The complete closed-subwalk erasure program

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) initializes
the position table and two stacks, scans the input and returns the dart
stack. The final copy uses its actual top, so stale popped entries
are excluded. The execution theorem computes the pure chronological
erasure with a linear bound, including initialization and copying.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Initialize, scan, and return the occupied dart stack in array 607. -/
def gm06EraseClosedSubwalksProg : Cmd :=
  .seq gm06EraseInitProg
    (.seq gm06EraseScanProg
      (gm13TabulateProg 619 (.reg 615) (.read 605 (.reg 619)) 607))

/-- Registers written by complete chronological erasure. -/
def gm06EraseClosedRegs : List ℕ := [616, 614, 615, 619, 610, 611, 612, 613, 617, 618]

/-- Arrays written by complete chronological erasure. -/
def gm06EraseClosedArrs : List ℕ := [604, 605, 606, 607]

/-- Actual ERASE_CLOSED_SUBWALKS computes the exact pure function from
plain finite input. No path or erasure conclusion is an assumption. -/
theorem gm06EraseClosedSubwalksProg_exec {w n source : ℕ} (heads input : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hsource : source < n)
    (hfit : input.length + 2 < 2 ^ w) (hheadsFit : heads.length < 2 ^ w)
    (hinput : ∀ d ∈ input, d < heads.length) (hheads : ∀ v ∈ heads, v < n)
    (h601 : s.arrs 601 = heads) (h603 : s.arrs 603 = input)
    (h606 : s.regs 606 = source) (h648 : s.regs 648 = n) :
    ∃ sf t, Exec w gm06EraseClosedSubwalksProg s sf t ∧
      t ≤ 40 + 83 * input.length + 13 * n ∧
      Keeps gm06EraseClosedRegs gm06EraseClosedArrs s sf ∧
      sf.arrs 607 = gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) source input := by
  let erased := gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) source input
  have hsub : erased.Sublist input := gm06EraseClosedSubwalks_sublist _ _ _
  have helen : erased.length ≤ input.length := hsub.length_le
  have hewords : ∀ d ∈ erased, d < 2 ^ w := fun d hd => (hinput d (hsub.subset hd)).trans hheadsFit
  obtain ⟨s₀, t₀, he₀, ht₀, hk₀, hV₀, hD₀, hP₀, hAbsent₀, hIndex₀⟩ :=
    gm06EraseInitProg_exec input s hw hn hsource hfit h603 h606 h648
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hV₁, hD₁, hP₁⟩ := gm06EraseScanProg_exec heads input s₀
    hw hn hfit hheadsFit hsource hinput hheads hV₀ hD₀ hP₀
    ((hk₀.2 601 (by decide)).trans h601) ((hk₀.2 603 (by decide)).trans h603) hIndex₀ hAbsent₀
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm13TabulateProg_exec (w := w) 619 (.reg 615) (.read 605 (.reg 619))
    607 erased s₁ hw (by omega)
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg ((hk.1 615 (by decide)).trans hD₁.2.2.1) (by omega))
    (fun st i hi hk hr => by
      have ha := hk.2 605 (by decide)
      have hbound : i < (st.arrs 605).length := by rw [ha, hD₁.1]; omega
      have hget : (st.arrs 605)[i]'hbound = erased[i] := by simpa only [ha] using hD₁.2.2.2 i hi
      have he := GraphMinor.Compute.Crossing.eval_read (a := 605)
        (GraphMinor.Compute.Crossing.eval_reg (w := w) hr (by omega)) hbound
        (by rw [hget]; exact hewords _ (List.getElem_mem hi))
      simpa only [hget] using he)
  refine ⟨sf, t₀ + (t₁ + tf), .seq he₀ (.seq he₁ hef), ?_,
    ((hk₀.mono (by simp [gm06EraseClosedRegs]) (by simp [gm06EraseClosedArrs])).trans hk₁
      (by simp [gm06EraseScanRegs, gm06EraseClosedRegs])
      (by simp [gm06EraseScanArrs, gm06EraseClosedArrs])).trans hkf
      (by simp [gm06EraseClosedRegs]) (by simp [gm06EraseClosedArrs]), hdf⟩
  simp only [Expr.cost] at htf
  omega

end GraphMinor.Compute
