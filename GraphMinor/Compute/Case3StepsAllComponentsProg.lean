module

public import GraphMinor.Compute.Case3StepsOutsideProg

/-!
# All components outside the core

The program first restricts the adjacency lists to the complement of the core,
then computes the table of component rows. Its running time is bounded by
vertex count times adjacency size. The table is used to form the raw members
in XIII (9.9), step (5), page 104.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Prepare the outside graph and store all component rows in array 12. -/
def case3AllComponentsProg : Cmd :=
  .seq case3OutsideProg
    (.seq (.assign 14 (.reg 1)) (case3ComponentTableProg 10 12 32 14))

/-- The component table can be computed directly from the core and the graph's
adjacency lists. Arrays below 10 are preserved. -/
theorem case3AllComponentsProg_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (lists : Fin x.n → List ℕ) (cap : ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    (hcap : cap < 2 ^ w)
    (hbound : 2 * (edgesInSet x.G (Finset.univ \ Z)).card ≤ cap)
    {s : State} (hadj : IsAdjList x.G 19 20 21 lists s)
    (hent : (s.arrs 21).length < 2 ^ w) (hZ : IsBitSet Z 10 s)
    (hrn : s.regs 1 = x.n) (hrcap : s.regs 2 = cap) :
    ∃ s' t, Exec w case3AllComponentsProg s s' t ∧
      t ≤ x.n * x.n + x.n * (38 * x.n + 26 * totalAdjEntries lists + 47) +
        41 * x.n + cap + 25 * totalAdjEntries lists + 26 ∧
      s'.arrs 12 = case3ComponentRows x Z ∧ s'.arrs 10 = bitSetList Z ∧
      s'.regs 1 = x.n ∧
      (∀ a < 10, s'.arrs a = s.arrs a) ∧ (∀ r < 3, s'.regs r = s.regs r) ∧
      (∀ a, a ≠ 11 → a ≠ 12 → a ≠ 63 → a ≠ 64 → a ≠ 68 → a ≠ 69 → a ≠ 70 →
        s'.arrs a = s.arrs a) ∧ s'.regs 14 = x.n := by
  have hnw : x.n < 2 ^ w := by romega
  obtain ⟨s₁, t₁, hex₁, ht₁, hadj₁, hlen₁, hrn₁, harr₁, hreg₁⟩ :=
    case3OutsideProg_exec x Z lists cap hw hnw hcap hbound hadj hent hZ hrn hrcap
  let s₂ := s₁.setReg 14 x.n
  have hex₂ : Exec w (.assign 14 (.reg 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrn₁, hnw])
  have hZ₂ : s₂.arrs 10 = bitSetList Z := by
    rw [show s₂.arrs 10 = s.arrs 10 from harr₁ _ (by decide) (by decide) (by decide) (by decide)]
    exact hZ.arr_eq_bitSetList
  obtain ⟨s₃, t₃, hex₃, ht₃, hdst₃, hr14₃, harr₃, hreg₃⟩ :=
    case3ComponentTableProg_exec x Z (restrictListFamily (Finset.univ \ Z) lists)
      10 12 32 14 (by decide) (by decide) (by decide) hw hn hsq hZ₂
      (hadj₁.of_arrs_eq rfl rfl rfl)
      (by change (s₁.arrs 70).length < 2 ^ w; rw [hlen₁]; exact hcap)
      (State.setReg_regs_self ..)
  have htot : totalAdjEntries (restrictListFamily (Finset.univ \ Z) lists) ≤ totalAdjEntries lists := by
    rw [totalAdjEntries_restrictListFamily hadj.2, totalAdjEntries_eq_two_mul_card_edgeFinset hadj.2]
    exact Nat.mul_le_mul_left 2 (card_edgesInSet_le_card_edgeFinset x.G _)
  have hmul := Nat.mul_le_mul_left x.n (show
      38 * x.n + 26 * totalAdjEntries (restrictListFamily (Finset.univ \ Z) lists) + 47 ≤
      38 * x.n + 26 * totalAdjEntries lists + 47 by romega)
  refine ⟨s₃, t₁ + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by romega, hdst₃, ?_, ?_, ?_, ?_, ?_, hr14₃⟩
  · rw [harr₃ 10 (by decide) (by decide) (by decide)]
    exact hZ₂
  · rw [hreg₃ 1 (by decide)]
    simpa only [s₂, State.setReg_regs_ne _ _ (show (1 : ℕ) ≠ 14 by decide)] using hrn₁
  · intro a ha
    rw [harr₃ a (by romega) (by romega) (by romega)]
    exact harr₁ a (by romega) (by romega) (by romega) (by romega)
  · intro r hr
    rw [hreg₃ r (by romega)]
    change (s₁.setReg 14 x.n).regs r = s.regs r
    rw [State.setReg_regs_ne _ _ (show r ≠ 14 by romega)]
    exact hreg₁ r (by romega) (by romega) (by romega) (by romega) (by romega) (by romega)
      (by romega) (by romega)
  · intro a h11 h12 h63 h64 h68 h69 h70
    exact (harr₃ a h12 h63 h64).trans (harr₁ a h11 h68 h69 h70)

end GraphMinor.Compute
