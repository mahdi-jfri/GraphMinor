module

public import GraphMinor.Compute.GM06Alg34RootRecordWords

/-!
# Emitting a region record exactly at canonical roots

Read the canonical root flag of the current supplied cell label. A
root starts a BFS and emits its complete induced boundary record.
Other labels emit no words. The root predicate supplies inactivity in
the emitting branch. The source arrays and root flags remain fixed.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Emit a new region record exactly when source label 187 is a canonical root. -/
def gm06RootRecordStepProg : Cmd :=
  .ite (.read 36 (.reg 187)) (.seq gm06ComplementBfsProg gm06RegionRecordProg) .skip

/-- One root-output step emits exactly its selected region record and
preserves the drawing, CSR graph, and canonical root mask. -/
theorem gm06RootRecordStepProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a : Fin x.cellCount) (pfx : List ℕ) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hout : pfx.length + 2 + x.n + x.ends.length < 2 ^ w) {s : State}
    (hrootMask : s.arrs 36 = gm06RootMask x vs)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hvertexMask : s.arrs 4 = gm06VertexMask vs) (hvertexRanks : s.arrs 5 = gm06VertexRanks vs)
    (hedgeMask : s.arrs 6 = gm06EdgeMask x vs) (hedgeRanks : s.arrs 7 = gm06EdgeRanks x vs)
    (hsize : s.regs 4 = x.cellCount) (hsource : s.regs 187 = a.val)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount)
    (hbuf : IsPrefixBuffer 10 pfx ((gm06RootRecordWords x vs a).length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06RootRecordStepProg s s' t ∧
      t ≤ 26 * (x.cellCount * x.cellCount) + 23 * x.cellCount +
        (18 * x.cellCount + 72) * (x.n + x.ends.length) + 90 ∧
      IsPrefixBuffer 10 (pfx ++ gm06RootRecordWords x vs a) cap s' ∧
      s'.regs 143 = (pfx ++ gm06RootRecordWords x vs a).length ∧
      (∀ j : ℕ, j ≠ 9 → j ≠ 10 → j ≠ 11 → j ≠ 33 → j ≠ 34 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, (q < 190 ∨ q = 203) → q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 143 →
        s'.regs q = s.regs q) := by
  have hrootlen : a.val < (s.arrs 36).length := by
    rw [hrootMask, gm06RootMask, List.length_ofFn]; exact a.isLt
  have hrootget : (s.arrs 36)[a.val]'hrootlen = if x.isRegionRoot vs a then 1 else 0 := by
    simp only [hrootMask, gm06RootMask, List.getElem_ofFn]
  have hread : (Expr.read 36 (.reg 187)).eval w s =
      some (if x.isRegionRoot vs a then 1 else 0) := by
    cases hr : x.isRegionRoot vs a <;>
      simp [Expr.eval, checkWord, hsource, a.isLt.trans hN, hrootlen, hrootget,
        hr, hw, Nat.zero_lt_of_lt hw]
  by_cases hroot : x.isRegionRoot vs a = true
  · have ha : x.activeCell vs (x.cellNumbering.symm a) = false :=
      (x.isRegionRoot_iff_no_smaller_reachable vs a).mp hroot |>.1
    obtain ⟨s₁, t₁, hex₁, ht₁, hmarks, harr₁, hreg₁⟩ :=
      gm06ComplementBfsProg_exec x vs a hw hN hsquare hsize hsource hlists hlen
    have hbuf₁ : IsPrefixBuffer 10 pfx ((gm06RegionRecordWords x vs a).length + cap) s₁ := by
      simpa only [gm06RootRecordWords, hroot, ↓reduceIte] using
        hbuf.of_arr_eq (harr₁ 10 (by decide) (by decide))
    obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hcursor₂, harr₂, hreg₂⟩ :=
      gm06RegionRecordProg_exec x vs a pfx hw hN hsquare ha hout hmarks
        ((harr₁ _ (by decide) (by decide)).trans hmat)
        ((hreg₁ _ (Or.inl (by decide))).trans hc)
        ((harr₁ _ (by decide) (by decide)).trans hvertexMask)
        ((harr₁ _ (by decide) (by decide)).trans hvertexRanks)
        ((harr₁ _ (by decide) (by decide)).trans hedgeMask)
        ((harr₁ _ (by decide) (by decide)).trans hedgeRanks)
        ((hreg₁ _ (Or.inl (by decide))).trans hn) ((hreg₁ _ (Or.inl (by decide))).trans hm)
        hbuf₁ ((hreg₁ _ (Or.inl (by decide))).trans hcursor)
    have hread' : (Expr.read 36 (.reg 187)).eval w s = some 1 := by simpa only [hroot, ↓reduceIte] using hread
    refine ⟨s₂, 2 + (t₁ + t₂), Exec.ite_true hread' (by decide) (Exec.seq hex₁ hex₂),
      by omega, ?_, ?_, ?_, ?_⟩
    · simpa only [gm06RootRecordWords, hroot, ↓reduceIte] using hbuf₂
    · simpa only [gm06RootRecordWords, hroot, ↓reduceIte] using hcursor₂
    · intro j hj₁ hj₂ hj₃ hj₄ hj₅
      exact (harr₂ j hj₁ hj₂ hj₃).trans (harr₁ j hj₄ hj₅)
    · intro q hq hq₁ hq₂ hq₃ hq₄
      exact (hreg₂ q (by omega) hq₁ hq₂ hq₃ hq₄ (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).trans (hreg₁ q (by omega))
  · have hread' : (Expr.read 36 (.reg 187)).eval w s = some 0 := by simpa [hroot] using hread
    refine ⟨s, 3, Exec.ite_false hread' (Exec.skip s), by omega, ?_, ?_,
      fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
    · simpa [gm06RootRecordWords, hroot] using hbuf
    · simpa [gm06RootRecordWords, hroot] using hcursor

end GraphMinor.Compute
