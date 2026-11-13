module

public import GraphMinor.Compute.Case3StepsMapWallSectionProg
public import GraphMinor.Compute.Case3StepsCountedLists

/-!
# Scanning all counted wall-path sections

The mapped prefix and the unmapped suffix have identical section lengths.
The cursor therefore follows the original section lengths throughout the
scan. Each section costs a constant per label plus a constant for its count
word, giving a linear bound in the counted encoding length.
-/

public section

namespace GraphMinor.Compute

/-- The section loop renames exactly the remaining lists, preserving their
length words, with a linear bound in the remaining encoding length. -/
theorem case3MapWallSectionsLoopProg_exec {w n N : ℕ} (orig : Fin n → Fin N)
    (pre suf : List ℕ) (lists : List (List (Fin n)))
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hsize : pre.length + (case3CountedLists Fin.val lists).length + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = lists.length) {s : State}
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1))
    (hbuf : s.arrs 46 = pre ++ case3CountedLists (fun u => (orig u).1) (lists.take k) ++
      case3CountedLists Fin.val (lists.drop k) ++ suf)
    (hrpos : s.regs 119 = pre.length + (case3CountedLists Fin.val (lists.take k)).length)
    (hrk : s.regs 118 = k) :
    ∃ s' t, Exec w (forUp 118 (.const lists.length) case3MapWallSectionProg) s s' t ∧
      t ≤ 3 + 23 * (case3CountedLists Fin.val (lists.drop k)).length ∧
      s'.arrs 46 = pre ++ case3CountedLists (fun u => (orig u).1) lists ++ suf := by
  have h0 : 0 < 2 ^ w := by omega
  have hnum := case3CountedLists_numLists_le Fin.val lists
  have hLw : lists.length < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = lists.length := by omega
    have hc : (Expr.op .lt (.reg 118) (.const lists.length)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hk, hLw, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    simpa only [hk, List.take_length, List.drop_length, case3CountedLists, List.flatMap_nil, List.append_nil] using hbuf
  | succ rem ih =>
    have hk : k < lists.length := by omega
    have hkw : k < 2 ^ w := by omega
    have hkp : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg 118) (.const lists.length)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hk, hkw, hLw, hw]
    let xs := lists[k]
    let pre' := pre ++ case3CountedLists (fun u => (orig u).1) (lists.take k)
    let suf' := case3CountedLists Fin.val (lists.drop (k + 1)) ++ suf
    have hprelen : pre'.length = pre.length + (case3CountedLists Fin.val (lists.take k)).length := by
      rw [List.length_append, case3CountedLists_length_eq (fun u => (orig u).1) Fin.val]
    have hdrop : lists.drop k = xs :: lists.drop (k + 1) := List.drop_eq_getElem_cons hk
    have hfull : case3CountedLists Fin.val lists =
        case3CountedLists Fin.val (lists.take k) ++ xs.length ::
          (xs.map Fin.val ++ case3CountedLists Fin.val (lists.drop (k + 1))) := by
      conv_lhs => rw [← List.take_append_drop k lists]
      rw [case3CountedLists_append, hdrop, case3CountedLists_cons]
    have hfullLen : (case3CountedLists Fin.val lists).length =
        (case3CountedLists Fin.val (lists.take k)).length + xs.length +
          (case3CountedLists Fin.val (lists.drop (k + 1))).length + 1 := by
      rw [hfull]
      simp only [List.length_append, List.length_cons, List.length_map]
      omega
    obtain ⟨sB, tB, hexB, htB, hbufB, hrposB, harrB, hregB⟩ :=
      case3MapWallSectionProg_exec orig pre' suf' xs hw hn hN
        (by rw [hprelen]; omega) hlabels
        (by rw [hbuf, hdrop, case3CountedLists_cons]; simp only [pre', suf', List.append_assoc, List.cons_append])
        (hrpos.trans hprelen.symm)
    let sC := sB.setReg 118 (k + 1)
    have hrkB : sB.regs 118 = k := (hregB 118 (by decide) (by decide) (by decide)).trans hrk
    have hexC : Exec w (.assign 118 (.op .add (.reg 118) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrkB, hkw, hw, hkp])
    have hbufC : sC.arrs 46 = pre ++ case3CountedLists (fun u => (orig u).1) (lists.take (k + 1)) ++
        case3CountedLists Fin.val (lists.drop (k + 1)) ++ suf := by
      rw [State.setReg_arrs, hbufB, case3CountedLists_take_succ _ lists k hk]
      simp only [pre', suf', xs, List.append_assoc, List.cons_append]
    have hrposC : sC.regs 119 = pre.length + (case3CountedLists Fin.val (lists.take (k + 1))).length := by
      rw [State.setReg_regs_ne _ _ (show (119 : ℕ) ≠ 118 by decide), hrposB, hprelen,
        case3CountedLists_take_succ Fin.val lists k hk]
      simp only [List.length_append, List.length_cons, List.length_map]
      dsimp only [xs]
      omega
    obtain ⟨s', t, hex, ht, hdst⟩ := ih (k + 1) (by omega) (s := sC)
      ((harrB 47 (by decide)).trans hlabels) hbufC hrposC (State.setReg_regs_self ..)
    refine ⟨s', 3 + (tB + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, ?_, hdst⟩
    rw [hdrop, case3CountedLists_cons]
    simp only [List.length_cons, List.length_append, List.length_map]
    omega

end GraphMinor.Compute
