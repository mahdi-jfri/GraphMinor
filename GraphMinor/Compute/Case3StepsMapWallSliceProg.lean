module

public import GraphMinor.Compute.Case3StepsMapSliceBuffer
public import GraphMinor.Compute.Logic
import Mathlib.Data.List.GetD

/-!
# Renaming one vertex slice of a wall encoding

The program maps a counted contiguous list through the retained original
vertex list. It writes labels in place and leaves the wall's header and
all other path sections untouched. This is the repeated operation used to
return the wall output of (7.2) to original labels.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Rename the 112 labels beginning at 119 in wall array 46 through list 47. -/
def case3MapWallSliceProg : Cmd :=
  .seq (.assign 117 (.const 0))
    (forUp 117 (.reg 112)
      (.write 46 (.op .add (.reg 119) (.reg 117))
        (.read 47 (.read 46 (.op .add (.reg 119) (.reg 117))))))

private theorem mapWallSliceLoop_exec {w n N : ℕ} (orig : Fin n → Fin N)
    (pre suf : List ℕ) (xs : List (Fin n))
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hsize : pre.length + xs.length + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = xs.length) {s : State}
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1))
    (hbuf : s.arrs 46 = pre ++ ((xs.map (fun u => (orig u).1)).take k) ++ (xs.map Fin.val).drop k ++ suf)
    (hrpos : s.regs 119 = pre.length) (hrlen : s.regs 112 = xs.length) (hrk : s.regs 117 = k) :
    ∃ s' t, Exec w (forUp 117 (.reg 112)
      (.write 46 (.op .add (.reg 119) (.reg 117))
        (.read 47 (.read 46 (.op .add (.reg 119) (.reg 117)))))) s s' t ∧
      t ≤ 3 + 16 * rem ∧ s'.arrs 46 = pre ++ xs.map (fun u => (orig u).1) ++ suf := by
  have h0 : 0 < 2 ^ w := by omega
  have hlenw : xs.length < 2 ^ w := by omega
  have hposw : pre.length < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = xs.length := by omega
    have hc : (Expr.op .lt (.reg 117) (.reg 112)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrlen, hk, hlenw, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    have ht : (xs.map (fun u => (orig u).1)).take xs.length = xs.map (fun u => (orig u).1) :=
      List.take_of_length_le (by rw [List.length_map])
    have hd : (xs.map Fin.val).drop xs.length = [] := List.drop_eq_nil_of_le (by rw [List.length_map])
    simpa only [hk, ht, hd, List.append_nil] using hbuf

  | succ rem ih =>
    have hk : k < xs.length := by omega
    have hkw : k < 2 ^ w := by omega
    have hkp : k + 1 < 2 ^ w := by omega
    have hidxw : pre.length + k < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg 117) (.reg 112)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrlen, hk, hkw, hlenw, hw]
    let u := xs[k]
    have hub : u.1 < 2 ^ w := u.2.trans hn
    have hov : (orig u).1 < 2 ^ w := (orig u).2.trans hN
    have hlen : (s.arrs 46).length = pre.length + xs.length + suf.length := by
      rw [hbuf]
      simp only [List.length_append, List.length_take, List.length_map, List.length_drop,
        Nat.min_eq_left hk.le]
      omega
    have hidx : pre.length + k < (s.arrs 46).length := by rw [hlen]; omega
    have hold : (s.arrs 46)[pre.length + k]'hidx = u.1 := by
      rw [← List.getD_eq_getElem _ _ hidx, hbuf,
        case3MapSliceBuffer_getD pre (xs.map Fin.val) (xs.map (fun u => (orig u).1)) suf k
          (by simpa only [List.length_map] using hk) (by simpa only [List.length_map] using hk.le),
        List.getElem_map]
    have hu47 : u.1 < (s.arrs 47).length := by rw [hlabels, List.length_ofFn]; exact u.2
    have hmap : (s.arrs 47)[u.1]'hu47 = (orig u).1 := by simp only [hlabels, List.getElem_ofFn]
    have hread : (Expr.read 47 (.read 46 (.op .add (.reg 119) (.reg 117)))).eval w s = some (orig u).1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos, hrk, hposw, hkw, hidxw,
        hidx, hold, hub, hu47, hmap, hov]
    let sB := s.writeArr 46 (pre.length + k) (orig u).1
    let sC := sB.setReg 117 (k + 1)
    have hexB : Exec w (.write 46 (.op .add (.reg 119) (.reg 117))
        (.read 47 (.read 46 (.op .add (.reg 119) (.reg 117))))) s sB 9 :=
      .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos, hrk, hposw, hkw, hidxw]) hread hidx
    have hexC : Exec w (.assign 117 (.op .add (.reg 117) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, sB, hrk, hkw, hw, hkp])
    have hbufC : sC.arrs 46 = pre ++ (xs.map (fun u => (orig u).1)).take (k + 1) ++
        (xs.map Fin.val).drop (k + 1) ++ suf := by
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_self, hbuf]
      have hs := case3MapSliceBuffer_set pre (xs.map Fin.val) (xs.map (fun u => (orig u).1)) suf
        (by simp only [List.length_map]) k (by simpa only [List.length_map] using hk)
      simpa only [List.getElem_map] using hs
    obtain ⟨s', t, hex, ht, hdst⟩ := ih (k + 1) (by omega) (s := sC)
      (by simpa only [sC, sB, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ (show (47 : ℕ) ≠ 46 by decide)] using hlabels)
      hbufC
      (by simp only [sC, sB, State.setReg_regs_ne _ _ (show (119 : ℕ) ≠ 117 by decide), State.writeArr_regs, hrpos])
      (by simp only [sC, sB, State.setReg_regs_ne _ _ (show (112 : ℕ) ≠ 117 by decide), State.writeArr_regs, hrlen])
      (State.setReg_regs_self ..)
    exact ⟨s', 3 + (9 + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, by omega, hdst⟩

/-- One counted wall-vertex slice is renamed in linear slice time. Only
array 46 and the scan register change. -/
theorem case3MapWallSliceProg_exec {w n N : ℕ} (orig : Fin n → Fin N)
    (pre suf : List ℕ) (xs : List (Fin n))
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hsize : pre.length + xs.length + 1 < 2 ^ w) {s : State}
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1))
    (hbuf : s.arrs 46 = pre ++ xs.map Fin.val ++ suf)
    (hrpos : s.regs 119 = pre.length) (hrlen : s.regs 112 = xs.length) :
    ∃ s' t, Exec w case3MapWallSliceProg s s' t ∧ t ≤ 16 * xs.length + 5 ∧
      s'.arrs 46 = pre ++ xs.map (fun u => (orig u).1) ++ suf ∧
      (∀ a, a ≠ 46 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 117 → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 117 0
  have hex₁ : Exec w (.assign 117 (.const 0)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂⟩ := mapWallSliceLoop_exec orig pre suf xs hw hn hN hsize xs.length 0
    (by omega) (s := s₁) hlabels (by simpa only [s₁, State.setReg_arrs, List.take_zero, List.drop_zero, List.append_nil] using hbuf)
    (by rw [State.setReg_regs_ne _ _ (by decide)]; exact hrpos)
    (by rw [State.setReg_regs_ne _ _ (by decide)]; exact hrlen) (State.setReg_regs_self ..)
  have hex : Exec w case3MapWallSliceProg s s₂ (2 + t₂) := .seq hex₁ hex₂
  refine ⟨s₂, 2 + t₂, hex, by omega, hdst₂, ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [case3MapWallSliceProg, forUp, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [case3MapWallSliceProg, forUp, Cmd.writtenRegs, hr])

end GraphMinor.Compute
