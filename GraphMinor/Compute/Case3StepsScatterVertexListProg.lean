module

public import GraphMinor.Compute.BitSet
public import GraphMinor.Compute.Logic
import Mathlib.Data.List.GetD

/-!
# Writing original-label bitsets from counted vertex lists

The compact member and boundary lists are read through the compass inverse
list. Each resulting original label is inserted in a freshly zeroed bitset.
Repeated labels would still be handled correctly, since insertion is
idempotent. The program is linear in the ambient vertex count and list size.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Scatter a counted list through inverse compass array 32 into a bitset. -/
def case3ScatterVertexListProg (a_src a_dst off r_count : ℕ) : Cmd :=
  .seq (.assign 90 (.len 2))
    (.seq (.alloc a_dst (.reg 90))
      (.seq (.assign 97 (.const 0))
        (forUp 97 (.reg r_count)
          (.write a_dst (.read 32 (.read a_src (.op .add (.const off) (.reg 97)))) (.const 1)))))

private theorem scatterListLoop_exec {w n N : ℕ} (orig : Fin n → Fin N) (xs : List (Fin n))
    (a_src a_dst off r_count : ℕ) (hne : a_src ≠ a_dst) (hd32 : a_dst ≠ 32) (hrcount : r_count ≠ 97)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hsize : off + xs.length + 1 < 2 ^ w) (rem k : ℕ) (hrem : k + rem = xs.length) {s : State}
    (hsrclen : off + xs.length ≤ (s.arrs a_src).length)
    (hsrc : ∀ j : Fin xs.length, (s.arrs a_src).getD (off + j.1) 0 = (xs[j.1]).1)
    (hlistlen : n ≤ (s.arrs 32).length)
    (hlist : ∀ u : Fin n, (s.arrs 32).getD u.1 0 = (orig u).1)
    (hbits : IsBitSet (((xs.take k).map orig).toFinset) a_dst s)
    (hrlen : s.regs r_count = xs.length) (hrk : s.regs 97 = k) :
    ∃ s' t, Exec w (forUp 97 (.reg r_count)
      (.write a_dst (.read 32 (.read a_src (.op .add (.const off) (.reg 97)))) (.const 1))) s s' t ∧
      t ≤ 3 + 14 * rem ∧ IsBitSet ((xs.map orig).toFinset) a_dst s' := by
  classical
  have h0 : 0 < 2 ^ w := by omega
  have hlenw : xs.length < 2 ^ w := by omega
  have hoffw : off < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = xs.length := by omega
    have hc : (Expr.op .lt (.reg 97) (.reg r_count)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrlen, hk, hlenw, h0]
    exact ⟨s, 3, .while_false hc, by omega, by simpa only [hk, List.take_length] using hbits⟩
  | succ rem ih =>
    have hk : k < xs.length := by omega
    have hkw : k < 2 ^ w := by omega
    have hkp : k + 1 < 2 ^ w := by omega
    have hok : off + k < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg 97) (.reg r_count)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrlen, hk, hkw, hlenw, hw]
    let u := xs[k]
    have husrc : off + k < (s.arrs a_src).length := by omega
    have hval : (s.arrs a_src)[off + k]'husrc = u.1 := by
      rw [← List.getD_eq_getElem _ 0 husrc]
      exact hsrc ⟨k, hk⟩
    have hu32 : u.1 < (s.arrs 32).length := lt_of_lt_of_le u.2 hlistlen
    have hmap : (s.arrs 32)[u.1]'hu32 = (orig u).1 := by
      rw [← List.getD_eq_getElem _ 0 hu32]
      exact hlist u
    have huw : u.1 < 2 ^ w := u.2.trans hn
    have how : (orig u).1 < 2 ^ w := (orig u).2.trans hN
    have hread : (Expr.read 32 (.read a_src (.op .add (.const off) (.reg 97)))).eval w s = some (orig u).1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hoffw, hkw, hok, husrc, hval, huw, hu32, hmap, how]
    let sB := s.writeArr a_dst (orig u).1 1
    let sC := sB.setReg 97 (k + 1)
    have hexB : Exec w (.write a_dst (.read 32 (.read a_src (.op .add (.const off) (.reg 97)))) (.const 1)) s sB 7 :=
      .write hread (by simp only [Expr.eval, checkWord, hw, ↓reduceIte]) (by rw [hbits.1]; exact (orig u).2)
    have hexC : Exec w (.assign 97 (.op .add (.reg 97) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, sB, hrk, hkw, hw, hkp])
    have hnext : ((xs.take (k + 1)).map orig).toFinset = insert (orig u) (((xs.take k).map orig).toFinset) := by
      rw [List.take_succ_eq_append_getElem hk, List.map_append, List.toFinset_append]
      simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
        Finset.insert_empty, Finset.union_singleton]
      rfl
    have hbitsC : IsBitSet (((xs.take (k + 1)).map orig).toFinset) a_dst sC := by
      rw [hnext]
      exact (hbits.write_one (orig u)).of_arr_eq rfl
    have harrC (a : ℕ) (ha : a ≠ a_dst) : sC.arrs a = s.arrs a := by
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha]
    obtain ⟨s', t, hex, ht, hbits'⟩ := ih (k + 1) (by omega) (s := sC)
      (by rw [harrC a_src hne]; exact hsrclen)
      (by intro j; rw [harrC a_src hne]; exact hsrc j)
      (by rw [harrC 32 (Ne.symm hd32)]; exact hlistlen)
      (by intro u; rw [harrC 32 (Ne.symm hd32)]; exact hlist u) hbitsC
      (by rw [State.setReg_regs_ne _ _ hrcount]; exact hrlen) (State.setReg_regs_self ..)
    exact ⟨s', 3 + (7 + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, by omega, hbits'⟩

/-- The exact image bitset is written in `N + 14*len + 8` steps, preserving
the source lists and all registers except the ambient count and scan counter. -/
theorem case3ScatterVertexListProg_exec {w n N : ℕ} (orig : Fin n → Fin N) (xs : List (Fin n))
    (a_src a_dst off r_count : ℕ) (hne : a_src ≠ a_dst) (hd32 : a_dst ≠ 32)
    (hr90 : r_count ≠ 90) (hr97 : r_count ≠ 97)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hsize : off + xs.length + 1 < 2 ^ w) {s : State}
    (hrank : (s.arrs 2).length = N)
    (hsrclen : off + xs.length ≤ (s.arrs a_src).length)
    (hsrc : ∀ j : Fin xs.length, (s.arrs a_src).getD (off + j.1) 0 = (xs[j.1]).1)
    (hlistlen : n ≤ (s.arrs 32).length)
    (hlist : ∀ u : Fin n, (s.arrs 32).getD u.1 0 = (orig u).1)
    (hrlen : s.regs r_count = xs.length) :
    ∃ s' t, Exec w (case3ScatterVertexListProg a_src a_dst off r_count) s s' t ∧
      t ≤ N + 14 * xs.length + 8 ∧ IsBitSet (xs.toFinset.image orig) a_dst s' ∧
      (∀ a, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 90 → r ≠ 97 → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 90 N
  let s₂ := s₁.setArr a_dst (List.replicate N 0)
  let s₃ := s₂.setReg 97 0
  have hex₁ : Exec w (.assign 90 (.len 2)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hrank, hN, ↓reduceIte])
  have hex₂ : Exec w (.alloc a_dst (.reg 90)) s₁ s₂ (1 + N) :=
    .alloc (by simp only [Expr.eval, checkWord, s₁, State.setReg_regs_self, hN, ↓reduceIte])
  have hex₃ : Exec w (.assign 97 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have harr₃ (a : ℕ) (ha : a ≠ a_dst) : s₃.arrs a = s.arrs a := by
    simp only [s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ ha]
  obtain ⟨s₄, t₄, hex₄, ht₄, hbits₄⟩ := scatterListLoop_exec orig xs a_src a_dst off r_count hne hd32 hr97
    hw hn hN hsize xs.length 0 (by omega) (s := s₃)
    (by rw [harr₃ a_src hne]; exact hsrclen)
    (by intro j; rw [harr₃ a_src hne]; exact hsrc j)
    (by rw [harr₃ 32 (Ne.symm hd32)]; exact hlistlen)
    (by intro u; rw [harr₃ 32 (Ne.symm hd32)]; exact hlist u)
    (by simp only [List.take_zero, List.map_nil, List.toFinset_nil]
        exact IsBitSet.empty_of_replicate (by simp only [s₃, s₂, State.setReg_arrs, State.setArr_arrs_self]))
    (by simp only [s₃, s₂, s₁, State.setReg_regs_ne _ _ hr97, State.setArr_regs, State.setReg_regs_ne _ _ hr90, hrlen])
    (State.setReg_regs_self ..)
  have hex : Exec w (case3ScatterVertexListProg a_src a_dst off r_count) s s₄ (2 + (1 + N + (2 + t₄))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, 2 + (1 + N + (2 + t₄)), hex, by omega, ?_, ?_, ?_⟩
  · have himage : (xs.map orig).toFinset = xs.toFinset.image orig := by
      ext u
      simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
    rw [← himage]
    exact hbits₄
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [case3ScatterVertexListProg, forUp, Cmd.writtenArrs, ha])
  · intro r h90 h97
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [case3ScatterVertexListProg, forUp, Cmd.writtenRegs, h90, h97])

end GraphMinor.Compute
