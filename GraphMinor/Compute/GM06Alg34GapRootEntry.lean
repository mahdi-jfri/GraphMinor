module

public import GraphMinor.Compute.GM06Alg34GapRootIndex

/-!
# Reading one reached canonical root on the RAM

At a scanned cell, first read its component mark and then its canonical
root flag. Only the unique reached root writes its prefix rank to the
output register. Every other cell preserves that register. This step
reads arrays only and takes at most seven RAM operations.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- At position 6400, record the rank in 6401 exactly when both marks are set. -/
def gm06GapRootEntryProg : Cmd :=
  .ite (.read 33 (.reg 6400))
    (.ite (.read 36 (.reg 6400)) (.assign 6401 (.read 37 (.reg 6400))) .skip) .skip

private theorem read_ofFn {w n A q : ℕ} (f : Fin n → ℕ) (a : Fin n)
    (hn : n < 2 ^ w) (hf : f a < 2 ^ w) {s : State}
    (hA : s.arrs A = List.ofFn f) (hq : s.regs q = a.val) :
    (Expr.read A (.reg q)).eval w s = some (f a) := by
  have hlen : a.val < (s.arrs A).length := by simp [hA, a.isLt]
  have hget : (s.arrs A)[a.val]'hlen = f a := by simp [hA]
  simp [Expr.eval, checkWord, hq, a.isLt.trans hn, hlen, hget, hf]

/-- A root-scan step writes exactly the computed new gap region label
at its unique reached root and preserves all other registers and arrays. -/
theorem gm06GapRootEntryProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.regions.length) (a : Fin x.cellCount) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) {s : State} (ha : s.regs 6400 = a.val)
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs (x.cellNumbering (.inr (.inr r))))
    (hmask : s.arrs 36 = gm06RootMask x vs)
    (hranks : s.arrs 37 = List.ofFn (fun b : Fin x.cellCount => ((gm06RootMask x vs).take b.val).sum)) :
    ∃ s' t, Exec w gm06GapRootEntryProg s s' t ∧ t ≤ 7 ∧
      s'.regs 6401 = (if a = x.regionRootAfterDeletion vs r then
        (x.regionAfterDeletion vs r).val else s.regs 6401) ∧
      (∀ A : ℕ, s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 6401 → s'.regs q = s.regs q) := by
  classical
  let P := (x.complementGraph vs).Reachable (x.cellNumbering (.inr (.inr r))) a
  have hpw : (if P then 1 else 0) < 2 ^ w := by split <;> omega
  have hread := read_ofFn
    (fun b : Fin x.cellCount => if (x.complementGraph vs).Reachable
      (x.cellNumbering (.inr (.inr r))) b then 1 else 0) a hN hpw hmarks ha
  change (Expr.read 33 (.reg 6400)).eval w s = some (if P then 1 else 0) at hread
  have hbw : (if x.isRegionRoot vs a then 1 else 0) < 2 ^ w := by split <;> omega
  have hbit := read_ofFn (fun b : Fin x.cellCount => if x.isRegionRoot vs b then 1 else 0)
    a hN hbw hmask ha
  by_cases he : a = x.regionRootAfterDeletion vs r
  · have hroot := (x.gap_reached_root_iff vs r a).mpr he
    have hp : P := hroot.1
    have hrank : ((gm06RootMask x vs).take a.val).sum = (x.regionAfterDeletion vs r).val :=
      by rw [he]; exact x.regionAfterDeletion_prefix_rank vs r
    have hbound : (x.regionAfterDeletion vs r).val < 2 ^ w := by
      have hh : (x.regionAfterDeletion vs r).val < (x.regionRoots vs).length := by
        simpa only [x.inducedData_regions_length vs] using (x.regionAfterDeletion vs r).isLt
      have hlen := gm06RootMask_sum_le x vs
      rw [gm06RootMask_sum] at hlen
      exact (hh.trans_le hlen).trans hN
    have hval := read_ofFn (fun b : Fin x.cellCount => ((gm06RootMask x vs).take b.val).sum)
      a hN (by rw [hrank]; exact hbound) hranks ha
    rw [hrank] at hval
    have hp' : (Expr.read 33 (.reg 6400)).eval w s = some 1 := by simpa only [ite_eq_left hp] using hread
    have hb' : (Expr.read 36 (.reg 6400)).eval w s = some 1 := by simpa only [hroot.2, ↓reduceIte] using hbit
    refine ⟨s.setReg 6401 (x.regionAfterDeletion vs r).val, 7,
      .ite_true hp' (by decide) (.ite_true hb' (by decide) (.assign hval)), by omega, ?_,
      fun _ => rfl, fun q hq => State.setReg_regs_ne _ _ hq⟩
    simp [he]
  · by_cases hp : P
    · have hb : x.isRegionRoot vs a = false := by
        cases hh : x.isRegionRoot vs a
        · rfl
        · exact False.elim (he ((x.gap_reached_root_iff vs r a).mp ⟨hp, hh⟩))
      have hp' : (Expr.read 33 (.reg 6400)).eval w s = some 1 := by simpa only [ite_eq_left hp] using hread
      have hb' : (Expr.read 36 (.reg 6400)).eval w s = some 0 := by simpa only [hb, Bool.false_eq_true, ↓reduceIte] using hbit
      exact ⟨s, 5, .ite_true hp' (by decide) (.ite_false hb' (.skip s)), by omega,
        by simp [he], fun _ => rfl, fun _ _ => rfl⟩
    · have hp' : (Expr.read 33 (.reg 6400)).eval w s = some 0 := by simpa only [ite_eq_right hp] using hread
      exact ⟨s, 3, .ite_false hp' (.skip s), by omega, by simp [he],
        fun _ => rfl, fun _ _ => rfl⟩

end GraphMinor.Compute
