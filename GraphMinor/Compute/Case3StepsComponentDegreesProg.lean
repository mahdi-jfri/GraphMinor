module

public import GraphMinor.Compute.Case3StepsExtractRowProg

/-!
# Counting neighbors in an outside component

After extracting one component row, the adjacency-list degree program counts
neighbors in that component. Positive counts on core vertices determine its
attachment set, as required for merging the raw members in XIII (8.6).
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- The table is in array 12, the selected seed in register 15, and the vertex
count in register 14. Arrays 22 and 23 hold the row and its neighbor counts. -/
def case3ComponentDegreesProg : Cmd :=
  .seq (case3ExtractRowProg 12 22 14 15 16)
    (computeDegIntoProg 19 20 21 22 23 14 24 25 26 27 28 29)

/-- Compute all degrees into a selected component while retaining the core,
component table, adjacency lists, and seed. -/
theorem case3ComponentDegreesProg_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (u : Fin x.n) (lists : Fin x.n → List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = case3ComponentRows x Z)
    (hadj : IsAdjList x.G 19 20 21 lists s) (hent : (s.arrs 21).length < 2 ^ w)
    (hrn : s.regs 14 = x.n) (hru : s.regs 15 = u.1) :
    ∃ s' t, Exec w case3ComponentDegreesProg s s' t ∧
      t ≤ 40 * x.n + 19 * totalAdjEntries lists + 18 ∧
      IsDegIntoArr x.G (case3ComponentRowSet x Z u) 23 s' ∧
      (∀ a, a ≠ 22 → a ≠ 23 → s'.arrs a = s.arrs a) ∧
      (∀ r < 16, s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hrow₁, harr₁, hreg₁⟩ :=
    case3ExtractRowProg_exec x Z u 12 22 14 15 16 (by decide) (by decide)
      hw hn hsq hmat hrn hru
  obtain ⟨s₂, t₂, hex₂, ht₂, hdeg₂, harr₂, hreg₂⟩ :=
    computeDegIntoProg_exec x.G lists (case3ComponentRowSet x Z u)
      19 20 21 22 23 14 24 25 26 27 28 29
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hw (by omega)
      (hadj.of_arrs_eq (harr₁ _ (by decide)) (harr₁ _ (by decide)) (harr₁ _ (by decide)))
      (by rw [harr₁ _ (by decide)]; exact hent) hrow₁
      (by rw [hreg₁ 14 (by decide)]; exact hrn)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hdeg₂, ?_, ?_⟩
  · intro a h22 h23
    exact (harr₂ a h23).trans (harr₁ a h22)
  · intro r hr
    rw [hreg₂ r (by romega) (by romega) (by romega) (by romega) (by romega) (by romega)]
    exact hreg₁ r hr

end GraphMinor.Compute
