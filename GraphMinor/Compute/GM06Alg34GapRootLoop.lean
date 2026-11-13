module

public import GraphMinor.Compute.GM06Alg34GapRootEntry
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Scanning the reached root on the RAM

Scan every packed cell once. Before the selected root's position the
output register retains its initial value. After that position it
contains the exact new region label. The root is within the scanned
range, so no initial value of the output register is required.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Scan the completed root mask at positions in register 6400. -/
def gm06GapRootLoopProg : Cmd := forUp 6400 (.len 36) gm06GapRootEntryProg

/-- The scan reads the exact new region label in linear time, preserving
all arrays and every register except its index and output. -/
theorem gm06GapRootLoopProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.regions.length) (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    {s : State} (hzero : s.regs 6400 = 0)
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs (x.cellNumbering (.inr (.inr r))))
    (hmask : s.arrs 36 = gm06RootMask x vs)
    (hranks : s.arrs 37 = List.ofFn (fun b : Fin x.cellCount => ((gm06RootMask x vs).take b.val).sum)) :
    ∃ s' t, Exec w gm06GapRootLoopProg s s' t ∧ t ≤ 14 * x.cellCount + 3 ∧
      s'.regs 6400 = x.cellCount ∧ s'.regs 6401 = (x.regionAfterDeletion vs r).val ∧
      (∀ A : ℕ, s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 6400 → q ≠ 6401 → s'.regs q = s.regs q) := by
  let root := x.regionRootAfterDeletion vs r
  let I : ℕ → State → Prop := fun i st =>
    st.regs 6400 = i ∧
    st.regs 6401 = (if root.val < i then (x.regionAfterDeletion vs r).val else s.regs 6401) ∧
    (∀ A : ℕ, st.arrs A = s.arrs A) ∧
    (∀ q : ℕ, q ≠ 6400 → q ≠ 6401 → st.regs q = s.regs q)
  have hhi : ∀ i ≤ x.cellCount, ∀ st, I i st →
      st.regs 6400 = i ∧ (Expr.len 36).eval w st = some x.cellCount := by
    intro i _ st hs
    exact ⟨hs.1, by simp [Expr.eval, checkWord, hs.2.2.1 36, hmask, gm06RootMask, hN]⟩
  have hbody : ∀ i < x.cellCount, ∀ st, I i st → ∃ st' t,
      Exec w gm06GapRootEntryProg st st' t ∧ t ≤ 7 ∧
      I (i + 1) (st'.setReg 6400 (i + 1)) ∧ st'.regs 6400 = i := by
    intro i hi st hs
    obtain ⟨hir, hacc, harr, hreg⟩ := hs
    obtain ⟨st', t, hex, ht, hvalue, harr', hreg'⟩ :=
      gm06GapRootEntryProg_exec x vs r ⟨i, hi⟩ hw hN hir
        ((harr 33).trans hmarks) ((harr 36).trans hmask) ((harr 37).trans hranks)
    refine ⟨st', t, hex, ht, ⟨by simp, ?_, ?_, ?_⟩,
      (hreg' 6400 (by decide)).trans hir⟩
    · change st'.regs 6401 = _
      by_cases he : i = root.val
      · have hf : (⟨i, hi⟩ : Fin x.cellCount) = x.regionRootAfterDeletion vs r := Fin.ext he
        rw [ite_eq_left hf] at hvalue
        rw [hvalue, ite_eq_left (by omega : root.val < i + 1)]
      · have hf : (⟨i, hi⟩ : Fin x.cellCount) ≠ x.regionRootAfterDeletion vs r := by
          intro hh
          exact he (congrArg (fun a : Fin x.cellCount => a.val) hh)
        rw [ite_eq_right hf] at hvalue
        have heq : (root.val < i + 1) ↔ root.val < i := by omega
        simpa only [heq] using hvalue.trans hacc
    · intro A
      exact (harr' A).trans (harr A)
    · intro q hq hq'
      exact (State.setReg_regs_ne _ _ hq).trans ((hreg' q hq').trans (hreg q hq hq'))
  have hinit : I 0 s := ⟨hzero, by simp, fun _ => rfl, fun _ _ _ => rfl⟩
  obtain ⟨s', t, hex, ht, hir, hacc, harr, hreg⟩ :=
    Crossing.forUp_exec' I x.cellCount 7 hw hN hhi hbody s hinit
  simp only [Expr.cost] at ht
  refine ⟨s', t, hex, by omega, hir, ?_, harr, hreg⟩
  exact hacc.trans (ite_eq_left root.isLt)

end GraphMinor.Compute
