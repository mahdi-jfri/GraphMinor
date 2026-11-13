module

public import GraphMinor.Compute.Case3StepsComponentTableProg

/-!
# Adjacency lists outside the core

The component searches use the simple compass graph restricted to the
complement of its core. The program complements the core bitset and filters
the adjacency lists. Filtering retains the original vertex numbering, as
required for the rows in step (5) of XIII (9.9), page 104.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Local storage for preparing the component searches. Registers 1 and 2
contain the vertex count and the capacity of the input adjacency array. -/
def case3OutsideProg : Cmd :=
  .seq (complBitSetProg 10 11 1 12)
    (restrictGraphProg 19 20 21 11 68 69 70 1 2 3 4 5 6 7 8 9)

/-- The outside adjacency arrays have capacity `cap`. The time bound depends
on the number of input adjacency entries and does not scan absent edges. -/
theorem case3OutsideProg_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (lists : Fin x.n → List ℕ) (cap : ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hcap : cap < 2 ^ w)
    (hbound : 2 * (edgesInSet x.G (Finset.univ \ Z)).card ≤ cap)
    {s : State} (hadj : IsAdjList x.G 19 20 21 lists s)
    (hent : (s.arrs 21).length < 2 ^ w) (hZ : IsBitSet Z 10 s)
    (hrn : s.regs 1 = x.n) (hrcap : s.regs 2 = cap) :
    ∃ s' t, Exec w case3OutsideProg s s' t ∧
      t ≤ 16 + 41 * x.n + cap + 25 * totalAdjEntries lists ∧
      IsAdjList (restrictGraph x.G (Finset.univ \ Z)) 68 69 70
        (restrictListFamily (Finset.univ \ Z) lists) s' ∧
      (s'.arrs 70).length = cap ∧ s'.regs 1 = x.n ∧
      (∀ a, a ≠ 11 → a ≠ 68 → a ≠ 69 → a ≠ 70 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 →
        r ≠ 9 → r ≠ 12 → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hY, harr₁, hreg₁⟩ :=
    complBitSetProg_exec Z 10 11 1 12 (by decide) (by decide) hw hn hZ hrn
  obtain ⟨s₂, t₂, hex₂, ht₂, hadj₂, hlen₂, _, harr₂, hreg₂⟩ :=
    restrictGraphProg_exec x.G lists (Finset.univ \ Z) cap
      19 20 21 11 68 69 70 1 2 3 4 5 6 7 8 9
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn hcap hbound
      (hadj.of_arrs_eq (harr₁ _ (by decide)) (harr₁ _ (by decide)) (harr₁ _ (by decide)))
      (by rw [harr₁ _ (by decide)]; exact hent) hY
      (by rw [hreg₁ _ (by decide)]; exact hrn)
      (by rw [hreg₁ _ (by decide)]; exact hrcap)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hadj₂, hlen₂, ?_, ?_, ?_⟩
  · rw [hreg₂ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg₁ 1 (by decide)]
    exact hrn
  · intro a h11 h68 h69 h70
    exact (harr₂ a h68 h69 h70).trans (harr₁ a h11)
  · intro r h3 h4 h5 h6 h7 h8 h9 h12
    exact (hreg₂ r h3 h4 h5 h6 h7 h8 h9).trans (hreg₁ r h12)

end GraphMinor.Compute
