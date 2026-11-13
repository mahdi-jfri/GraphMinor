module

public import GraphMinor.Compute.GM02ComponentTestLoop

/-!
# Testing one candidate separator on the RAM

Initialize the forbidden labels and count the terminals outside the
separator. Save that total and test every remaining component. This is
the complete test of a candidate vertex set in II (3.1), page 316. The
slot enumeration and construction of a balanced output separation use
this operation.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths GraphMinor.Compute.Crossing Classical

/-- The scratch registers used to test one candidate separator. -/
def gm02CandidateRegs : List ℕ := 185 :: 181 :: 184 :: gm02ComponentRegs

/-- Count remaining terminals, then check every component against that count. -/
def gm02CandidateTestProg (k : ℕ) : Cmd :=
  .seq (gm02ComponentLabelsProg 200 k)
    (.seq (gm02CountIntersectionProg 5 aLab 0)
      (.seq (.assign 185 (.reg 183)) (gm02ComponentTestLoop k)))

/-- The complete candidate test returns one exactly when every remaining
component has at most two thirds of the remaining terminals. Its time is
polynomial, and candidate words and input arrays are preserved. -/
theorem gm02CandidateTestProg_exec {n k w : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (Q : Finset (Fin n)) (f : Fin k → ℕ)
    (hf : ∀ i, f i ≤ n) (s : State) (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w)
    (hadj : IsAdjList G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hq : s.arrs 5 = gm02VertexBits Q)
    (hslots : ∀ i, s.regs (200 + i.val) = f i) :
    ∃ s' t, Exec w (gm02CandidateTestProg k) s s' t ∧
      t ≤ 22 + n * (k * 6 + 36) +
        n * (91 + k * 6 + n * (k * 6 + 57) + 29 * totalAdjEntries lists) ∧
      Keeps gm02CandidateRegs gm02ComponentArrays s s' ∧
      s'.regs 184 = if ∀ a : Fin n, a ∉ gm02SlotVertices f →
        3 * (GM02.deletedComponent (Graph.ofSimpleGraph G)
          (gm02SlotVertices (n := n) f : Set (Fin n)) a ∩ (Q : Set (Fin n))).ncard ≤
          2 * (Q \ gm02SlotVertices f).card then 1 else 0 := by
  have hn' : n < 2 ^ w := (show n ≤ 3 * n by omega).trans_lt hn
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hl₁⟩ := gm02ComponentLabelsProg_exec 200 (by decide)
    f hf s (by omega) hn' hrn hslots
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hc₂⟩ := gm02CountRemaining_exec Q (gm02SlotVertices f)
    5 aLab s₁ (by omega) hn' ((hk₁.1 _ (by decide)).trans hrn)
    ((hk₁.2 _ (by decide)).trans hq) hl₁
  let s₃ := s₂.setReg 185 (Q \ gm02SlotVertices f).card
  have hcount : (Q \ gm02SlotVertices f).card < 2 ^ w :=
    (show (Q \ gm02SlotVertices f).card ≤ n from
      (Finset.card_le_card Finset.sdiff_subset).trans (by simpa using Finset.card_le_univ Q)).trans_lt hn'
  have he₃ : Exec w (.assign 185 (.reg 183)) s₂ s₃ 2 := .assign (eval_reg hc₂ hcount)
  have hk₁' : Keeps gm02CandidateRegs gm02ComponentArrays s s₁ :=
    hk₁.mono (by intro r hr; obtain rfl := List.mem_singleton.1 hr; decide)
      (by intro a ha; obtain rfl := List.mem_singleton.1 ha; decide)
  have hk₂' : Keeps gm02CandidateRegs gm02ComponentArrays s₁ s₂ :=
    hk₂.mono (by
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hr
      · decide
      · obtain rfl := List.mem_singleton.1 hr; decide) (by simp)
  have hk₃ : Keeps gm02CandidateRegs gm02ComponentArrays s s₃ :=
    (hk₁'.trans hk₂' (fun _ h => h) (fun _ h => h)).setReg (by decide) _
  have hadj₃ : IsAdjList G 10 11 12 lists s₃ := hadj.of_arrs_eq
    (hk₃.2 _ (by decide)) (hk₃.2 _ (by decide)) (hk₃.2 _ (by decide))
  have hslots₃ : ∀ i, s₃.regs (200 + i.val) = f i := by
    intro i
    apply (hk₃.1 _ ?_).trans (hslots i)
    dsimp only [Reg]
    simp [gm02CandidateRegs, gm02ComponentRegs]
    omega
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hout⟩ := gm02ComponentTestLoop_exec G lists Q f hf s₃
    hw hn hadj₃ (by simpa only [hk₃.2 12 (by decide)] using hent)
    ((hk₃.1 _ (by decide)).trans hrn) ((hk₃.2 _ (by decide)).trans hq)
    hslots₃ (by simp [s₃])
  have hk₄' : Keeps gm02CandidateRegs gm02ComponentArrays s₃ s₄ :=
    hk₄.mono (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h)
  refine ⟨s₄, t₁ + (t₂ + (2 + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_,
    hk₃.trans hk₄' (fun _ h => h) (fun _ h => h), hout⟩
  have hc : n * (k * 6 + 36) = n * (k * 6 + 19) + n * 17 := by ring
  rw [hc]
  omega

end GraphMinor.Compute
