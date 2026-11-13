module

public import GraphMinor.Compute.GM06LoopErasureStep
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Scanning a walk with chronological loop erasure

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) processes
every input dart with the position table and two stacks. The invariant
identifies these stacks with erasure of the processed prefix. The
potential charges every pop to a preceding push, giving a linear
bound for the complete scan.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Scratch registers of the chronological scan. -/
def gm06EraseScanRegs : List ℕ := [610, 611, 612, 613, 615, 614, 617, 618]

/-- Mutable arrays of the chronological scan. -/
def gm06EraseScanArrs : List ℕ := [605, 604, 606]

/-- Scan all input darts, maintaining the actual vertex/dart stacks. -/
def gm06EraseScanProg : Cmd := forUp 610 (.len 603) gm06EraseStepProg

/-- The scan computes pure chronological erasure from initialized
stacks. Its linear bound includes all repeated-vertex pop loops. -/
theorem gm06EraseScanProg_exec {w n source : ℕ} (heads input : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hfit : input.length + 2 < 2 ^ w)
    (hheadsFit : heads.length < 2 ^ w) (hsource : source < n)
    (hinput : ∀ d ∈ input, d < heads.length) (hheads : ∀ v ∈ heads, v < n)
    (h604 : IsStack 604 614 (input.length + 1) [source] s)
    (h605 : IsStack 605 615 input.length [] s)
    (h606 : s.arrs 606 = gm06StackPositions n (input.length + 1) [source])
    (h601 : s.arrs 601 = heads) (h603 : s.arrs 603 = input)
    (h610 : s.regs 610 = 0) (h616 : s.regs 616 = input.length + 1) :
    let erased := gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) source input
    ∃ sf t, Exec w gm06EraseScanProg s sf t ∧ t ≤ 3 + 67 * input.length ∧
      Keeps gm06EraseScanRegs gm06EraseScanArrs s sf ∧
      IsStack 604 614 (input.length + 1) (gm06WalkVertices (fun d => heads[d]?.getD 0) source erased) sf ∧
      IsStack 605 615 input.length erased sf ∧
      sf.arrs 606 = gm06StackPositions n (input.length + 1)
        (gm06WalkVertices (fun d => heads[d]?.getD 0) source erased) := by
  let head : ℕ → ℕ := fun d => heads[d]?.getD 0
  let stack := fun i => gm06EraseClosedSubwalks head source (input.take i)
  let vertices := fun i => gm06WalkVertices head source (stack i)
  have hlen (i : ℕ) : (stack i).length ≤ i :=
    (gm06EraseClosedSubwalks_sublist head source (input.take i)).length_le.trans (List.length_take_le _ _)
  have hmem (i : ℕ) : ∀ d ∈ stack i, d ∈ input := fun _ hd =>
    List.mem_of_mem_take ((gm06EraseClosedSubwalks_sublist head source (input.take i)).subset hd)
  let I := fun i st => Keeps gm06EraseScanRegs gm06EraseScanArrs s st ∧ st.regs 610 = i ∧
    IsStack 604 614 (input.length + 1) (vertices i) st ∧
    IsStack 605 615 input.length (stack i) st ∧
    st.arrs 606 = gm06StackPositions n (input.length + 1) (vertices i) ∧
    st.regs 616 = input.length + 1
  let Φ := fun st : State => 22 * (input.length - st.regs 615)
  have hI₀ : I 0 s := by
    refine ⟨Keeps.refl _ _ s, h610, ?_, ?_, ?_, h616⟩
    · simpa only [vertices, stack, List.take_zero, gm06EraseClosedSubwalks, gm06EraseClosedAux, gm06WalkVertices,
        List.map_nil] using h604
    · simpa only [stack, List.take_zero, gm06EraseClosedSubwalks, gm06EraseClosedAux] using h605
    · simpa only [vertices, stack, List.take_zero, gm06EraseClosedSubwalks, gm06EraseClosedAux, gm06WalkVertices,
        List.map_nil] using h606
  obtain ⟨sf, t, he, ht, hIf⟩ := GraphMinor.Compute.Crossing.forUp_exec (w := w) I Φ input.length 60
    (r_i := 610) (hi := .len 603) (body := gm06EraseStepProg) hw (by omega)
    (fun i _ st hs => ⟨hs.2.1, GraphMinor.Compute.Crossing.eval_len
      ((hs.1.2 603 (by decide)).trans h603) (by omega)⟩)
    (by
      intro i hi st hs
      obtain ⟨hk, hr, hV, hD, hP, hAbsent⟩ := hs
      have hwords : ∀ d ∈ stack i, d < 2 ^ w := fun d hd => (hinput d (hmem i d hd)).trans hheadsFit
      have hvertices : ∀ v ∈ vertices i, v < n := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hsource
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
          have hd' := hinput d (hmem i d hd)
          simpa only [head, List.getElem?_eq_getElem hd', Option.getD_some] using
            hheads _ (List.getElem_mem hd')
      obtain ⟨st', t', he', ht', hk', hV', hD', hP'⟩ := gm06EraseStepProg_exec heads input (stack i) st
        hw hn hfit hheadsFit hi hinput hheads (by have := hlen i; omega)
        (gm06EraseClosedSubwalks_nodup head source (input.take i)) hvertices hwords hV hD hP
        ((hk.2 601 (by decide)).trans h601) ((hk.2 603 (by decide)).trans h603) hr hAbsent
      have hnext : stack (i + 1) = gm06EraseClosedStep head source (stack i) input[i] :=
        gm06EraseClosedSubwalks_take_succ head source input i hi
      rw [← hnext] at ht' hV' hD' hP'
      have hkeep : Keeps gm06EraseScanRegs gm06EraseScanArrs st st' :=
        hk'.mono (by simp [gm06EraseScanRegs]) (by simp [gm06EraseScanArrs])
      refine ⟨st', t', he', ?_, ?_, (hk'.1 610 (by decide)).trans hr⟩
      · have htop := hD.2.2.1
        have htop' := hD'.2.2.1
        have hli := hlen i
        have hli' := hlen (i + 1)
        simp only [Φ, State.setReg_regs_ne _ _ (by decide : (615 : ℕ) ≠ 610), htop, htop']
        omega
      · refine ⟨(hk.trans hkeep (by simp) (by simp)).setReg (by simp [gm06EraseScanRegs]) _,
          by simp, ?_, ?_, ?_, ?_⟩
        · exact hV'.of_preserve (by rfl) (by simp)
        · exact hD'.of_preserve (by rfl) (by simp)
        · exact hP'
        · exact (by simpa using (hkeep.1 616 (by decide)).trans hAbsent))
    0 (by omega) s hI₀
  have htop₀ := h605.2.2.1
  have hΦf : Φ sf ≤ 22 * input.length := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  simp only [Φ, htop₀, List.length_nil, Nat.sub_zero, Expr.cost, Nat.sub_zero] at ht
  refine ⟨sf, t, he, by omega, hIf.1, ?_, ?_, ?_⟩
  · simpa only [vertices, stack, List.take_length] using hIf.2.2.1
  · simpa only [stack, List.take_length] using hIf.2.2.2.1
  · simpa only [vertices, stack, List.take_length] using hIf.2.2.2.2.1

end GraphMinor.Compute
