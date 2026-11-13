module

public import GraphMinor.Compute.Case3StepsMemberLoopOwnerProg

/-!
# Advancing the loop-owner scan by one candidate

The selected-group mask skips candidates already represented by another
group. A selected candidate records its still-unassigned vertices. Both
branches advance the same exact owner-table invariant.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Only selected candidates take part in assigning loop owners. -/
def case3LoopOwnerBody : Cmd :=
  .ite (.read 29 (.reg 54)) case3MemberLoopOwnerProg .skip

/-- One candidate advances the loop-owner table and preserves the input tables. -/
theorem case3LoopOwnerBody_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (i : Case3RawIndex x)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hreps : s.arrs 27 = case3ComponentRepList x d.core.Z)
    (hmask : IsBitSet (case3GroupLabelSet x d.core.Z) 29 s)
    (hrn : s.regs 14 = x.n) (hrg : s.regs 54 = case3RawIndexLabel x i)
    (hrL : s.regs 52 = x.n + (case3InputEdges x).length)
    (howners : s.arrs 33 = case3LoopOwnerPrefix x d.core.Z (case3RawIndexLabel x i)) :
    ∃ s' t, Exec w case3LoopOwnerBody s s' t ∧ t ≤ 77 * x.n + 104 ∧
      s'.arrs 33 = case3LoopOwnerPrefix x d.core.Z (case3RawIndexLabel x i + 1) ∧
      (∀ a, a ≠ 25 → a ≠ 30 → a ≠ 33 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52 ∨ r = 54 ∨ 64 ≤ r →
        s'.regs r = s.regs r) := by
  classical
  have hidx : case3RawIndexLabel x i < (s.arrs 29).length := by
    rw [hmask.1]
    exact case3RawIndexLabel_lt x i
  have hkw := (case3RawIndexLabel_lt x i).trans hsize
  have hget : (s.arrs 29)[case3RawIndexLabel x i]'hidx =
      if case3GroupActive x d.core.Z i then 1 else 0 := by
    have hh : (s.arrs 29).getD (case3RawIndexLabel x i) 0 =
        if case3GroupActive x d.core.Z i then 1 else 0 := by
      rw [hmask.arr_eq_bitSetList, ← case3GroupMaskList_eq_bitSetList,
        case3GroupMaskList_getD]
    simpa only [List.getD_eq_getElem _ 0 hidx] using hh
  by_cases hi : case3GroupActive x d.core.Z i
  · have hc : (Expr.read 29 (.reg 54)).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hrg, hkw, hidx, hget, hi, show 1 < 2 ^ w by omega]
    obtain ⟨s', t, hex, ht, _, _, howners', harr, hreg⟩ :=
      case3MemberLoopOwnerProg_exec x d hd ⟨i, hi⟩ hw hn hkeys hm hsize
        hin hZ htab hreps hrn hrg hrL howners
    exact ⟨s', 2 + t, .ite_true hc (by decide) hex, by omega, howners', harr, hreg⟩
  · have hc : (Expr.read 29 (.reg 54)).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hrg, hkw, hidx, hget, hi, show 0 < 2 ^ w by omega]
    exact ⟨s, 3, .ite_false hc (.skip s), by omega,
      howners.trans (case3LoopOwnerPrefix_unselected x d.core.Z i hi).symm,
      fun _ _ _ _ => rfl, fun _ _ => rfl⟩

end GraphMinor.Compute
