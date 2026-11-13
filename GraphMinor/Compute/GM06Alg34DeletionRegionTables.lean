module

public import GraphMinor.Compute.GM06Alg34ComplementAdjList
public import GraphMinor.Compute.GM06Alg34RootRanks

/-!
# Building the graph and root tables for induced deletion

From the supplied-cell closure matrix and survival masks, build the
complement CSR graph, compute all canonical root flags, and number the
roots. The new region count is obtained from the root mask. Arrays for
the original drawing and its new endpoint and label tables are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Build complement CSR lists, canonical root flags, and the new region count. -/
def gm06DeletionRegionTablesProg : Cmd :=
  .seq gm06ComplementAdjListProg (.seq gm06RootMaskProg gm06RootRanksProg)

/-- The concrete region-table pipeline computes the exact complement
graph and root count in cubic time, preserving all arrays below 28. -/
theorem gm06DeletionRegionTablesProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = gm06ClosureMatrixData x)
    (hc : s.regs 170 = x.cellCount) (hn : s.regs 100 = x.n)
    (hm : s.regs 101 = x.ends.length) (hv : s.arrs 4 = gm06VertexMask vs)
    (he : s.arrs 6 = gm06EdgeMask x vs) :
    ∃ s' t, Exec w gm06DeletionRegionTablesProg s s' t ∧
      t ≤ x.cellCount * (26 * (x.cellCount * x.cellCount) + 46 * x.cellCount + 80) +
        149 * (x.cellCount * x.cellCount) + 48 * x.cellCount + 37 ∧
      s'.arrs 36 = gm06RootMask x vs ∧ s'.regs 203 = (x.regionRoots vs).length ∧
      s'.regs 4 = x.cellCount ∧
      IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s' ∧
      (s'.arrs 32).length = x.cellCount * x.cellCount ∧
      (∀ k : ℕ, k < 28 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, 100 ≤ q → q < 180 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hlists₁, hlen₁, hsize₁, harr₁, hreg₁⟩ :=
    gm06ComplementAdjListProg_exec x vs hw hN hsquare hmat hc hn hm hv he
  have hn₁ : s₁.regs 100 = x.n := (hreg₁ _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans hn
  have hm₁ : s₁.regs 101 = x.ends.length := (hreg₁ _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans hm
  obtain ⟨s₂, t₂, hex₂, ht₂, hroots, harr₂, hreg₂⟩ :=
    gm06RootMaskProg_exec x vs hw hN hsquare hsize₁ hn₁ hm₁
      ((harr₁ _ (by decide)).trans hv) ((harr₁ _ (by decide)).trans he) hlists₁ hlen₁
  obtain ⟨s₃, t₃, hex₃, ht₃, _, htotal, harr₃, hreg₃⟩ :=
    gm06RootRanksProg_exec x vs hw hN hroots
  have hlists₂ : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s₂ :=
    hlists₁.of_arrs_eq (harr₂ _ (by decide) (by decide) (by decide) (by decide))
      (harr₂ _ (by decide) (by decide) (by decide) (by decide))
      (harr₂ _ (by decide) (by decide) (by decide) (by decide))
  refine ⟨s₃, t₁ + (t₂ + t₃), Exec.seq hex₁ (Exec.seq hex₂ hex₃), by omega,
    (harr₃ _ (by decide)).trans hroots, htotal, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hreg₃ _ (by decide) (by decide)).trans
      ((hreg₂ _ (Or.inl (by decide)) (by decide)).trans hsize₁)
  · exact hlists₂.of_arrs_eq (harr₃ _ (by decide)) (harr₃ _ (by decide)) (harr₃ _ (by decide))
  · rw [harr₃ 32 (by decide), harr₂ 32 (by decide) (by decide) (by decide) (by decide)]
    exact hlen₁
  · intro k hk
    exact (harr₃ k (by omega)).trans
      ((harr₂ k (by omega) (by omega) (by omega) (by omega)).trans (harr₁ k hk))
  · intro q hq₁ hq₂
    exact (hreg₃ q (by omega) (by omega)).trans
      ((hreg₂ q (Or.inl (by omega)) (by omega)).trans
        (hreg₁ q hq₁ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))

end GraphMinor.Compute
