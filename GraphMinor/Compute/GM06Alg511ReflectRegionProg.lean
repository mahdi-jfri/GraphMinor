module

public import GraphMinor.Compute.GM06Alg511ReflectDartProg
import Mathlib.Tactic

/-!
# Executing reflection of a region-boundary row

For VI (5.11), page 134, a region-boundary row starts with a region
label. Retain that header. Read the remaining words backwards, take
the opposite directed end, and apply the fixed cuff permutation.
A single scan implements this transformation, including empty rows
and the header-only rows used for isolated boundary vertices.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

private theorem reflectedRegion_get {m k : ℕ} (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    (gm06Alg511ReflectRegionRow m k xs).getD i 0 =
      if i = 0 then xs.getD 0 0 else
        gm06Alg511ReflectAugmentedDart m k (gm06DartMate (xs.getD (xs.length - i) 0)) := by
  have href : i < (gm06Alg511ReflectRegionRow m k xs).length := by
    rw [gm06Alg511ReflectRegionRow_length]
    exact hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem href]
  simp only [Option.getD_some]
  cases xs with
  | nil => simp at hi
  | cons a ys =>
    cases i with
    | zero => simp [gm06Alg511ReflectRegionRow]
    | succ i =>
      have hiY : i < ys.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      have hidx : (a :: ys).length - (i + 1) = (ys.length - 1 - i) + 1 := by
        simp only [List.length_cons]
        omega
      have hjY : ys.length - 1 - i < ys.length := by omega
      simp only [gm06Alg511ReflectRegionRow, List.getElem_cons_succ, List.getElem_map,
        List.getElem_reverse, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      rw [hidx, List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjY]
      rfl

/-- The row-scan body retains position zero and transforms each
later position from the reversed tail. Counts occupy registers 60
and 52. Registers 20,23,24 are the counter and scratch words. -/
def gm06Alg511ReflectRegionBody (src dst : Arr) : Cmd :=
  .ite (.op .eq (.reg 20) (.const 0))
    (.write dst (.reg 20) (.read src (.const 0)))
    (.seq (.assign 23 (.read src (.op .sub (.len src) (.reg 20))))
      (.seq gm06DartMateProg (.seq (.assign 23 (.reg 24))
        (.seq (gm06Alg511ReflectAugmentedDartProg 60 52 23 24)
          (.write dst (.reg 20) (.reg 24))))))

/-- Allocate the result row and scan every word, including its
unchanged region header. -/
def gm06Alg511ReflectRegionRowProg (src dst : Arr) : Cmd :=
  .seq (.alloc dst (.len src)) (.seq (.assign 20 (.const 0))
    (forUp 20 (.len src) (gm06Alg511ReflectRegionBody src dst)))

/-- The full header-preserving row reflection runs in linear time.
Only actual directed edge labels in the row tail are transformed. -/
theorem gm06Alg511ReflectRegionRowProg_exec {w : ℕ} (src dst : Arr) (hne : src ≠ dst)
    (m k : ℕ) (xs : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : 2 * (m + k + k) < 2 ^ w) (hlen : xs.length < 2 ^ w)
    (hwords : ∀ d ∈ xs, d < 2 ^ w)
    (hdarts : ∀ d ∈ xs.tail, d < 2 * (m + k + k))
    (hsrc : s.arrs src = xs) (hrM : s.regs 60 = m) (hrK : s.regs 52 = k) :
    ∃ s' t, Exec w (gm06Alg511ReflectRegionRowProg src dst) s s' t ∧
      t ≤ 6 + 94 * xs.length ∧ Keeps [20, 23, 24] [dst] s s' ∧
      s'.arrs dst = gm06Alg511ReflectRegionRow m k xs := by
  let f : ℕ → ℕ := fun i => if i = 0 then xs.getD 0 0 else
    gm06Alg511ReflectAugmentedDart m k (gm06DartMate (xs.getD (xs.length - i) 0))
  let s₁ := s.setArr dst (List.replicate xs.length 0)
  let s₂ := s₁.setReg 20 0
  have he₁ : Exec w (.alloc dst (.len src)) s s₁ (1 + xs.length) := .alloc (eval_len hsrc hlen)
  have he₂ : Exec w (.assign 20 (.const 0)) s₁ s₂ 2 := .assign (eval_const (Nat.two_pow_pos w))
  let Inv : ℕ → State → Prop := fun i st => Keeps [20, 23, 24] [dst] s st ∧ st.regs 20 = i ∧
    st.arrs dst = (List.range i).map f ++ List.replicate (xs.length - i) 0
  have hstart : Inv 0 s₂ := by
    refine ⟨((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _, by simp [s₂], ?_⟩
    simp [s₂, s₁]
  have hloop := forUp_pot Inv (fun _ => 0) xs.length 86 (r_i := 20) (hi := .len src)
    (body := gm06Alg511ReflectRegionBody src dst) (by omega : 1 < 2 ^ w) hlen
    (fun i _ st hst => ⟨hst.2.1,
      eval_len ((hst.1.2 src (by simpa using hne)).trans hsrc) hlen⟩)
    (fun i hi st hst => by
      have ha : st.arrs src = xs := (hst.1.2 src (by simpa using hne)).trans hsrc
      have hcap : i < (st.arrs dst).length := by
        rw [hst.2.2, List.length_append, List.length_map, List.length_range, List.length_replicate]
        omega
      have htest := eval_eq (eval_reg hst.2.1 (hi.trans hlen))
        (eval_const (Nat.two_pow_pos w)) (by omega : 1 < 2 ^ w)
      by_cases hi0 : i = 0
      · subst i
        have hx0 : xs.getD 0 0 = xs[0] := by simp [hi]
        have hf : f 0 = xs[0] := by dsimp only [f]; rw [ite_eq_left rfl, hx0]
        have hd : xs[0] < 2 ^ w := hwords _ (List.getElem_mem hi)
        have hread := Crossing.eval_read (a := src) (eval_const (Nat.two_pow_pos w))
          (by rw [ha]; exact hi) (by simpa only [ha] using hd)
        have heWrite : Exec w (.write dst (.reg 20) (.read src (.const 0))) st
            (st.writeArr dst 0 (f 0)) 4 :=
          .write (eval_reg hst.2.1 (Nat.two_pow_pos w))
            (by simpa only [ha, hf] using hread) hcap
        have heBody : Exec w (gm06Alg511ReflectRegionBody src dst) st (st.writeArr dst 0 (f 0)) 7 :=
          .ite_true (by simpa only [ite_true] using htest) (by decide : (1 : ℕ) ≠ 0) heWrite
        refine ⟨st.writeArr dst 0 (f 0), 7, heBody, by omega, ?_, by simpa using hst.2.1⟩
        refine ⟨(hst.1.writeArr (by simp) _ _).setReg (by simp) _, by simp, ?_⟩
        simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs, ite_true, hst.2.2]
        exact set_range_map f hi
      · let j := xs.length - i
        have hj : j < xs.length := by dsimp [j]; omega
        have hj0 : j ≠ 0 := by dsimp [j]; omega
        have hxj : xs.getD j 0 = xs[j] := by simp [hj]
        have hd : xs[j] < 2 * (m + k + k) := hdarts _ (List.getElem_mem_tail xs hj0 hj)
        have hdw : xs[j] < 2 ^ w := hd.trans hn
        have hmate : gm06DartMate xs[j] < 2 * (m + k + k) := gm06DartMate_lt hd
        have hmatew : gm06DartMate xs[j] < 2 ^ w := hmate.trans hn
        have hf : f i = gm06Alg511ReflectAugmentedDart m k (gm06DartMate xs[j]) := by
          dsimp only [f]
          rw [ite_eq_right hi0, show xs.length - i = j from rfl, hxj]
        let st₁ := st.setReg 23 xs[j]
        have hjE : (Expr.op .sub (.len src) (.reg 20)).eval w st = some j :=
          eval_sub (eval_len ha hlen) (eval_reg hst.2.1 (hi.trans hlen))
        have hread := Crossing.eval_read (a := src) hjE (by rw [ha]; exact hj)
          (by simpa only [ha] using hdw)
        have heRead : Exec w (.assign 23 (.read src (.op .sub (.len src) (.reg 20)))) st st₁ 5 :=
          .assign (by simpa only [ha] using hread)
        let st₂ := st₁.setReg 24 (gm06DartMate xs[j])
        have heMate : Exec w gm06DartMateProg st₁ st₂ 9 :=
          gm06DartMateProg_exec st₁ hw hn hd (by simp [st₁])
        let st₃ := st₂.setReg 23 (gm06DartMate xs[j])
        have heCopy : Exec w (.assign 23 (.reg 24)) st₂ st₃ 2 :=
          .assign (eval_reg (by simp [st₂]) hmatew)
        obtain ⟨t, heDart, ht⟩ := gm06Alg511ReflectAugmentedDartProg_exec 60 52 23 24 m k
          (gm06DartMate xs[j]) st₃ hw hn hmatew
          (by simpa [st₃, st₂, st₁] using (hst.1.1 60 (by decide)).trans hrM)
          (by simpa [st₃, st₂, st₁] using (hst.1.1 52 (by decide)).trans hrK) (by simp [st₃])
        let st₄ := st₃.setReg 24 (f i)
        have heDart' : Exec w (gm06Alg511ReflectAugmentedDartProg 60 52 23 24) st₃ st₄ t := by
          simpa only [st₄, hf] using heDart
        have hfit : f i < 2 ^ w := by rw [hf]; exact (gm06Alg511ReflectAugmentedDart_lt hmate).trans hn
        have heWrite : Exec w (.write dst (.reg 20) (.reg 24)) st₄ (st₄.writeArr dst i (f i)) 3 :=
          .write (eval_reg (by simpa [st₄, st₃, st₂, st₁] using hst.2.1) (hi.trans hlen))
            (eval_reg (by simp [st₄]) hfit) (by simpa [st₄, st₃, st₂, st₁] using hcap)
        have heBody : Exec w (gm06Alg511ReflectRegionBody src dst) st (st₄.writeArr dst i (f i))
            (3 + (5 + (9 + (2 + (t + 3))))) :=
          .ite_false (by simpa only [hi0, ite_false] using htest)
            (.seq heRead (.seq heMate (.seq heCopy (.seq heDart' heWrite))))
        refine ⟨st₄.writeArr dst i (f i), _, heBody, by omega, ?_,
          by simpa [st₄, st₃, st₂, st₁] using hst.2.1⟩
        refine ⟨(((((hst.1.setReg (by simp) _).setReg (by simp) _).setReg (by simp) _).setReg
          (by simp) _).writeArr (by simp) _ _).setReg (by simp) _, by simp, ?_⟩
        simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs, ite_true, st₄, st₃, st₂, st₁,
          State.setReg_arrs, hst.2.2]
        exact set_range_map f hi)
    0 (Nat.zero_le _) s₂ hstart
  obtain ⟨s', t, he, ht, hk, _, hfinal⟩ := hloop
  refine ⟨s', (1 + xs.length) + (2 + t), .seq he₁ (.seq he₂ he), ?_, hk, ?_⟩
  · simp only [Expr.cost, Nat.sub_zero] at ht
    omega
  · have hmap : (List.range xs.length).map f = gm06Alg511ReflectRegionRow m k xs := by
      apply List.ext_getElem (by rw [List.length_map, List.length_range, gm06Alg511ReflectRegionRow_length])
      intro i hi hi'
      have hiXs : i < xs.length := by simpa only [List.length_map, List.length_range] using hi
      have hget := reflectedRegion_get (m := m) (k := k) xs i hiXs
      have hget' : (gm06Alg511ReflectRegionRow m k xs).getD i 0 =
          (gm06Alg511ReflectRegionRow m k xs)[i] := by simp [hi']
      rw [hget'] at hget
      simpa only [List.getElem_map, List.getElem_range] using hget.symm
    simpa only [Nat.sub_self, List.replicate_zero, List.append_nil, hmap] using hfinal

end GraphMinor.Compute
