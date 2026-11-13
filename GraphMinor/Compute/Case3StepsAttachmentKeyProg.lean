module

public import GraphMinor.Compute.Case3StepsAttachmentRowProg
public import GraphMinor.Compute.Case3StepsBoundaryKeyProg

/-!
# A key for a component attachment set

The component's neighbor counts give its attachment bitset. Claim (1) of
(8.6) bounds that set by three, so the boundary scan writes a four-word key.
This key will be used to merge raw members with equal boundaries.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Compute the selected seed's attachment key in array 25. -/
def case3AttachmentKeyProg : Cmd :=
  .seq case3AttachmentRowProg (case3BoundaryKeyProg 24 25 14 31 34)

/-- A valid division core gives a four-word attachment key for every seed.
The component table, core, adjacency lists, and seed register are preserved. -/
theorem case3AttachmentKeyProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (u : Fin x.n) (lists : Fin x.n → List ℕ)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = case3ComponentRows x d.core.Z)
    (hZ : IsBitSet d.core.Z 10 s)
    (hadj : IsAdjList x.G 19 20 21 lists s) (hent : (s.arrs 21).length < 2 ^ w)
    (hrn : s.regs 14 = x.n) (hru : s.regs 15 = u.1) :
    ∃ s' t, Exec w case3AttachmentKeyProg s s' t ∧
      t ≤ 76 * x.n + 19 * totalAdjEntries lists + 39 ∧
      s'.arrs 25 = case3BoundaryKey (case3AttachmentRowSet x d.core.Z u) ∧
      (∀ a, a ≠ 22 → a ≠ 23 → a ≠ 24 → a ≠ 25 → s'.arrs a = s.arrs a) ∧
      (∀ r < 16, s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hatt₁, harr₁, hreg₁⟩ :=
    case3AttachmentRowProg_exec x d.core.Z u lists (by omega) hn hsq hmat hZ hadj hent hrn hru
  obtain ⟨s₂, t₂, hex₂, ht₂, hkey₂, harr₂, hreg₂⟩ :=
    case3BoundaryKeyProg_exec (case3AttachmentRowSet x d.core.Z u)
      (case3AttachmentRowSet_card_le_three x d hd u) 24 25 14 31 34
      (by decide) (by decide) (by decide) (by decide) hw hn
      (IsBitSet.of_bitSetList _ _ _ hatt₁)
      (by rw [hreg₁ 14 (by decide)]; exact hrn)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hkey₂, ?_, ?_⟩
  · intro a h22 h23 h24 h25
    exact (harr₂ a h25).trans (harr₁ a h22 h23 h24)
  · intro r hr
    rw [hreg₂ r (by romega) (by romega)]
    exact hreg₁ r hr

end GraphMinor.Compute
