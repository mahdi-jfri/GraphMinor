module

public import GraphMinor.Compute.Case3StepsAttachmentBitsProg

/-!
# Computing one attachment row

The program extracts a component, counts its neighbors, and masks the positive
counts by core membership. Thus it writes the attachment set used to group
the raw members of (8.6), preserving the component table and original graph.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- The selected seed is in register 15. Its attachment bitset is written to
array 24, with arrays 22 and 23 used for the component and neighbor counts. -/
def case3AttachmentRowProg : Cmd :=
  .seq case3ComponentDegreesProg (case3AttachmentBitsProg 10 23 24 14 30)

/-- Compute the attachment row of one seed in linear vertex and adjacency
work. Core seeds have empty attachment rows. -/
theorem case3AttachmentRowProg_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (u : Fin x.n) (lists : Fin x.n → List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = case3ComponentRows x Z) (hZ : IsBitSet Z 10 s)
    (hadj : IsAdjList x.G 19 20 21 lists s) (hent : (s.arrs 21).length < 2 ^ w)
    (hrn : s.regs 14 = x.n) (hru : s.regs 15 = u.1) :
    ∃ s' t, Exec w case3AttachmentRowProg s s' t ∧
      t ≤ 57 * x.n + 19 * totalAdjEntries lists + 24 ∧
      s'.arrs 24 = bitSetList (case3AttachmentRowSet x Z u) ∧
      (∀ a, a ≠ 22 → a ≠ 23 → a ≠ 24 → s'.arrs a = s.arrs a) ∧
      (∀ r < 16, s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hdeg₁, harr₁, hreg₁⟩ :=
    case3ComponentDegreesProg_exec x Z u lists hw hn hsq hmat hadj hent hrn hru
  obtain ⟨s₂, t₂, hex₂, ht₂, hatt₂, harr₂, hreg₂⟩ :=
    case3AttachmentBitsProg_exec x Z u 10 23 24 14 30 (by decide) (by decide) (by decide)
      hw hn (hZ.of_arr_eq (harr₁ _ (by decide) (by decide))) hdeg₁
      (by rw [hreg₁ 14 (by decide)]; exact hrn)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hatt₂, ?_, ?_⟩
  · intro a h22 h23 h24
    exact (harr₂ a h24).trans (harr₁ a h22 h23)
  · intro r hr
    rw [hreg₂ r (by romega)]
    exact hreg₁ r hr

end GraphMinor.Compute
