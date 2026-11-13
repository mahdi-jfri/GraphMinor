module

public import GraphMinor.Compute.GM02CodedCandidate

/-!
# Remembering successful separator codes

One iteration of the outer search in II (3.1) tests the current code.
On success it sets a found bit and remembers that code. On failure it
keeps both values unchanged. The stored code will later be decoded to
construct the balanced output separation.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths GraphMinor.Compute.Crossing Classical

/-- Scratch registers used by one iteration of the separator-code search. -/
def gm02CodeSearchRegs (k : ℕ) : List ℕ := 186 :: 191 :: (gm02SlotRegs k ++ gm02CandidateRegs)

/-- Test the current code and remember it when the component test succeeds. -/
def gm02CodeSearchBody (k : ℕ) : Cmd :=
  .seq (gm02CodedCandidateProg k) (.ite (.reg 184)
    (.seq (.assign 186 (.const 1)) (.assign 191 (.reg 190))) .skip)

/-- A search iteration updates the found bit and winning code exactly on
success, with the complete candidate test providing the decision. -/
theorem gm02CodeSearchBody_exec {n k w code : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (Q : Finset (Fin n)) (s : State)
    (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w) (hb : n + 1 < 2 ^ w)
    (hc : code < 2 ^ w) (hp : (n + 1) ^ k < 2 ^ w)
    (hadj : IsAdjList G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hq : s.arrs 5 = gm02VertexBits Q)
    (hcode : s.regs 190 = code) :
    ∃ s' t, Exec w (gm02CodeSearchBody k) s s' t ∧
      t ≤ 28 + k * (8 + 4 * k) + n * (k * 6 + 36) +
        n * (91 + k * 6 + n * (k * 6 + 57) + 29 * totalAdjEntries lists) ∧
      Keeps (gm02CodeSearchRegs k) gm02ComponentArrays s s' ∧
      let X := gm02SlotVertices (n := n) (fun i : Fin k => gm02SeparatorDigit n code i.val)
      let good := ∀ a : Fin n, a ∉ X →
        3 * (GM02.deletedComponent (Graph.ofSimpleGraph G) (X : Set (Fin n)) a ∩
          (Q : Set (Fin n))).ncard ≤ 2 * (Q \ X).card
      s'.regs 186 = (if good then 1 else s.regs 186) ∧
      s'.regs 191 = (if good then code else s.regs 191) := by
  classical
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, htest⟩ := gm02CodedCandidateProg_exec G lists Q s
    hw hn hb hc hp hadj hent hrn hq hcode
  let X := gm02SlotVertices (n := n) (fun i : Fin k => gm02SeparatorDigit n code i.val)
  let good := ∀ a : Fin n, a ∉ X →
    3 * (GM02.deletedComponent (Graph.ofSimpleGraph G) (X : Set (Fin n)) a ∩
      (Q : Set (Fin n))).ncard ≤ 2 * (Q \ X).card
  have hlow (r : ℕ) (hr : r < 200) (hrC : r ∉ gm02CandidateRegs) : s₁.regs r = s.regs r :=
    hk₁.1 r (by simp only [List.mem_append, not_or]; exact ⟨not_mem_gm02SlotRegs hr, hrC⟩)
  have hk₁' : Keeps (gm02CodeSearchRegs k) gm02ComponentArrays s s₁ :=
    hk₁.mono (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) (fun _ h => h)
  by_cases hg : good
  · dsimp only [good, X] at hg
    have hflag : s₁.regs 184 = 1 := by simpa only [ite_eq_left hg] using htest
    let s₂ := s₁.setReg 186 1
    let s₃ := s₂.setReg 191 code
    have he₂ : Exec w (.assign 186 (.const 1)) s₁ s₂ 2 := .assign (eval_const (by omega))
    have he₃ : Exec w (.assign 191 (.reg 190)) s₂ s₃ 2 :=
      .assign (eval_reg (by simpa only [s₂, State.setReg_regs_ne _ _ (show (190 : Reg) ≠ 186 by decide)]
        using (hlow 190 (by decide) (by decide)).trans hcode) hc)
    refine ⟨s₃, t₁ + (1 + (2 + 2)), .seq he₁ (.ite_true
      (eval_reg hflag (by omega)) (by decide) (.seq he₂ he₃)), ?_,
      (hk₁'.setReg (by simp [gm02CodeSearchRegs]) _).setReg (by simp [gm02CodeSearchRegs]) _, ?_⟩
    · omega
    · simp only [s₃, s₂, State.setReg_regs_ne _ _ (show (186 : Reg) ≠ 191 by decide),
        State.setReg_regs_self, ite_eq_left hg, and_self]
  · dsimp only [good, X] at hg
    have hflag : s₁.regs 184 = 0 := by simpa only [ite_eq_right hg] using htest
    refine ⟨s₁, t₁ + (1 + 1), .seq he₁ (.ite_false
      (eval_reg hflag (Nat.two_pow_pos w)) (.skip s₁)), ?_, hk₁', ?_⟩
    · omega
    · simp only [ite_eq_right hg]
      exact ⟨hlow 186 (by decide) (by decide), hlow 191 (by decide) (by decide)⟩

end GraphMinor.Compute
