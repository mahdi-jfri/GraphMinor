module

public import GraphMinor.Compute.GM06Alg34GapRootScan
import GraphMinor.Compute.GM06Alg34PackedCells

/-!
# Computing the new label of a supplied old gap region

Read an old region number from a register, translate it to its packed
cell number, run the complement search, and scan the canonical root
marks and ranks. This computes the exact region reindexing used by the
finite augmented deletion payload, with a quadratic RAM time bound.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Reindex old region 6402 into 6401 using the prepared complement graph. -/
def gm06GapRegionQueryProg : Cmd :=
  .seq (.assign 187 (.op .add (.reg 100) (.op .add (.reg 101) (.reg 6402))))
    (.seq gm06ComplementBfsProg gm06GapRootScanProg)

/-- The gap-region query computes exactly the finite region update,
using only supplied labels and the already computed complement arrays. -/
theorem gm06GapRegionQueryProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (r : Fin x.regions.length) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.cellCount) (hn : s.regs 100 = x.n)
    (hm : s.regs 101 = x.ends.length) (hr : s.regs 6402 = r.val)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount)
    (hmask : s.arrs 36 = gm06RootMask x vs)
    (hranks : s.arrs 37 = List.ofFn (fun b : Fin x.cellCount => ((gm06RootMask x vs).take b.val).sum)) :
    ∃ s' t, Exec w gm06GapRegionQueryProg s s' t ∧
      t ≤ 26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 37 ∧
      s'.regs 6401 = (x.regionAfterDeletion vs r).val ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 187 → q ≠ 6400 → q ≠ 6401 →
        s'.regs q = s.regs q) := by
  let a := x.cellNumbering (.inr (.inr r))
  have haw : a.val < 2 ^ w := a.isLt.trans hN
  have hsrc : (.op .add (.reg 100) (.op .add (.reg 101) (.reg 6402)) : Expr).eval w s =
      some a.val := by
    have ha : a.val = x.n + (x.ends.length + r.val) := x.cellNumbering_region_val r
    have hnw : x.n < 2 ^ w := by omega
    have hmw : x.ends.length < 2 ^ w := by omega
    have hrw : r.val < 2 ^ w := by omega
    have hmrw : x.ends.length + r.val < 2 ^ w := by omega
    have hsumw : x.n + (x.ends.length + r.val) < 2 ^ w := by omega
    simp [Expr.eval, checkWord, BinOp.eval, BinOp.raw, hn, hm, hr, ha, hnw, hmw, hrw, hmrw, hsumw]
  let s₁ := s.setReg 187 a.val
  have hex₁ : Exec w (.assign 187 (.op .add (.reg 100) (.op .add (.reg 101) (.reg 6402)))) s s₁ 6 :=
    .assign hsrc
  have hlists₁ : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s₁ := hlists
  obtain ⟨s₂, t₂, hex₂, ht₂, hmarks₂, harr₂, hreg₂⟩ :=
    gm06ComplementBfsProg_exec x vs a hw hN hsquare
      (by simpa [s₁] using hsize) (by simp [s₁]) hlists₁ hlen
  obtain ⟨s₃, t₃, hex₃, ht₃, hout, harr₃, hreg₃⟩ :=
    gm06GapRootScanProg_exec x vs r hw hN hmarks₂
      ((harr₂ 36 (by decide) (by decide)).trans hmask)
      ((harr₂ 37 (by decide) (by decide)).trans hranks)
  refine ⟨s₃, 6 + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hout, ?_, ?_⟩
  · intro A hA hA'
    exact (harr₃ A).trans (harr₂ A hA hA')
  · intro q hq hq' hq₀ hq₁
    exact (hreg₃ q hq₀ hq₁).trans ((hreg₂ q hq).trans (State.setReg_regs_ne _ _ hq'))

end GraphMinor.Compute
