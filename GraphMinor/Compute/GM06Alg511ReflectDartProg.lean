module

public import GraphMinor.Compute.GM06Alg511ReflectDrawing
public import GraphMinor.Compute.TwoPathsRotate
public import GraphMinor.Compute.CrossingLiftReverse
import GraphMinor.Compute.CrossingOpsCycleTest
import GraphMinor.Compute.CrossingOpsReplLists
import Mathlib.Tactic

/-!
# Executing the reflected directed-label permutation

For the orientation step of VI (5.11), page 134, the fixed cuff
markers must be relabelled before the successor procedure reads
rotations. A branch tests the original, inner and outer edge blocks.
In a cuff block it reverses the gap index and the parameter-end bit.
The program below computes this permutation in constant time. A
second program applies it to a whole row in linear time, retaining
all source words and all arrays outside its destination.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Reflect one cuff dart relative to its block's first edge index. -/
def gm06Alg511ReflectDartExpr (base : Expr) (rK rD : Reg) : Expr :=
  .op .add (.op .mul (.const 2)
    (.op .add base (.op .sub (.op .sub (.reg rK) (.const 1))
      (.op .sub (.op .div (.reg rD) (.const 2)) base))))
    (.op .sub (.const 1) (.op .mod (.reg rD) (.const 2)))

private theorem reflectDartExpr_eval {w : ℕ} (base : Expr) (rK rD : Reg)
    (B k d : ℕ) (s : State) (hw : 2 < 2 ^ w) (hn : 2 * (B + k) < 2 ^ w)
    (hd : d < 2 ^ w) (hlo : B ≤ d / 2) (hhi : d / 2 < B + k)
    (hbase : base.eval w s = some B) (hrK : s.regs rK = k) (hrD : s.regs rD = d) :
    (gm06Alg511ReflectDartExpr base rK rD).eval w s =
      some (2 * (B + (k - 1 - (d / 2 - B))) + (1 - d % 2)) := by
  have hB : B < 2 ^ w := Expr.eval_lt hbase
  have hk : k < 2 ^ w := by omega
  have hindex : B + (k - 1 - (d / 2 - B)) < B + k := by omega
  have hindexW : B + (k - 1 - (d / 2 - B)) < 2 ^ w := by omega
  have hmul : 2 * (B + (k - 1 - (d / 2 - B))) < 2 ^ w := by omega
  have hresult : 2 * (B + (k - 1 - (d / 2 - B))) + (1 - d % 2) < 2 ^ w := by omega
  have hD := eval_reg hrD hd
  have hK := eval_reg hrK hk
  have htwo := eval_const hw (s := s)
  have hone := eval_const (show 1 < 2 ^ w by omega) (s := s)
  have hj := eval_div hD htwo (by decide : (2 : ℕ) ≠ 0) (by omega : d / 2 < 2 ^ w)
  have hb := eval_mod hD htwo (by decide : (0 : ℕ) < 2)
  exact eval_add (eval_mul htwo
    (eval_add hbase (eval_sub (eval_sub hK hone) (eval_sub hj hbase)) hindexW) hmul)
      (eval_sub hone hb) hresult

/-- Read the original edge count, cuff count and dart from the
specified registers and write its reflected label to the output.
The only changed register is the output. -/
def gm06Alg511ReflectAugmentedDartProg (rM rK rD rOut : Reg) : Cmd :=
  let j := Expr.op .div (.reg rD) (.const 2)
  let mk := Expr.op .add (.reg rM) (.reg rK)
  .ite (.op .lt j (.reg rM)) (.assign rOut (.reg rD))
    (.ite (.op .lt j mk) (.assign rOut (gm06Alg511ReflectDartExpr (.reg rM) rK rD))
      (.ite (.op .lt j (.op .add mk (.reg rK)))
        (.assign rOut (gm06Alg511ReflectDartExpr mk rK rD)) (.assign rOut (.reg rD))))

/-- The complete directed-label permutation takes at most 64 RAM
steps, including both cuff blocks and words outside their range. -/
theorem gm06Alg511ReflectAugmentedDartProg_exec {w : ℕ}
    (rM rK rD rOut : Reg) (m k d : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : 2 * (m + k + k) < 2 ^ w) (hd : d < 2 ^ w)
    (hrM : s.regs rM = m) (hrK : s.regs rK = k) (hrD : s.regs rD = d) :
    ∃ t : ℕ, Exec w (gm06Alg511ReflectAugmentedDartProg rM rK rD rOut) s
      (s.setReg rOut (gm06Alg511ReflectAugmentedDart m k d)) t ∧ t ≤ 64 := by
  have hm : m < 2 ^ w := by omega
  have hk : k < 2 ^ w := by omega
  have hmk : m + k < 2 ^ w := by omega
  have hmkk : m + k + k < 2 ^ w := by omega
  have hM := eval_reg hrM hm
  have hK := eval_reg hrK hk
  have hD := eval_reg hrD hd
  have hj := eval_div hD (eval_const hw) (by decide : (2 : ℕ) ≠ 0) (by omega : d / 2 < 2 ^ w)
  have hMK := eval_add hM hK hmk
  have hMKK := eval_add hMK hK hmkk
  have hw1 : 1 < 2 ^ w := by omega
  have htestM := eval_lt hj hM hw1
  have htestMK := eval_lt hj hMK hw1
  have htestMKK := eval_lt hj hMKK hw1
  by_cases h0 : d / 2 < m
  · have hval : gm06Alg511ReflectAugmentedDart m k d = d := by
      simp only [gm06Alg511ReflectAugmentedDart, h0, ite_true]
    have he : Exec w (gm06Alg511ReflectAugmentedDartProg rM rK rD rOut) s (s.setReg rOut d) 7 :=
      .ite_true (by simpa only [h0, ite_true] using htestM)
        (by decide : (1 : ℕ) ≠ 0) (Exec.assign hD)
    exact ⟨7, by simpa only [hval] using he, by decide⟩
  by_cases h1 : d / 2 < m + k
  · have hE := reflectDartExpr_eval (.reg rM) rK rD m k d s hw
      (by omega : 2 * (m + k) < 2 ^ w) hd (by omega) h1 hM hrK hrD
    have hval : gm06Alg511ReflectAugmentedDart m k d =
        2 * (m + (k - 1 - (d / 2 - m))) + (1 - d % 2) := by
      simp only [gm06Alg511ReflectAugmentedDart, h0, h1, ite_false, ite_true]
    have he : Exec w (gm06Alg511ReflectAugmentedDartProg rM rK rD rOut) s
        (s.setReg rOut (2 * (m + (k - 1 - (d / 2 - m))) + (1 - d % 2))) 32 :=
      .ite_false (by simpa only [h0, ite_false] using htestM)
        (.ite_true (by simpa only [h1, ite_true] using htestMK)
          (by decide : (1 : ℕ) ≠ 0) (Exec.assign hE))
    exact ⟨32, by simpa only [hval] using he, by decide⟩
  by_cases h2 : d / 2 < m + k + k
  · have hE := reflectDartExpr_eval (.op .add (.reg rM) (.reg rK)) rK rD (m + k) k d s
      hw hn hd (by omega) h2 hMK hrK hrD
    have hval : gm06Alg511ReflectAugmentedDart m k d =
        2 * (m + k + (k - 1 - (d / 2 - (m + k)))) + (1 - d % 2) := by
      simp only [gm06Alg511ReflectAugmentedDart, h0, h1, h2, ite_false, ite_true]
    have he : Exec w (gm06Alg511ReflectAugmentedDartProg rM rK rD rOut) s
        (s.setReg rOut (2 * (m + k + (k - 1 - (d / 2 - (m + k)))) + (1 - d % 2))) 45 :=
      .ite_false (by simpa only [h0, ite_false] using htestM)
        (.ite_false (by simpa only [h1, ite_false] using htestMK)
          (.ite_true (by simpa only [h2, ite_true] using htestMKK)
            (by decide : (1 : ℕ) ≠ 0) (Exec.assign hE)))
    exact ⟨45, by simpa only [hval] using he, by decide⟩
  · have hval : gm06Alg511ReflectAugmentedDart m k d = d := by
      simp only [gm06Alg511ReflectAugmentedDart, h0, h1, h2, ite_false]
    have he : Exec w (gm06Alg511ReflectAugmentedDartProg rM rK rD rOut) s (s.setReg rOut d) 23 :=
      .ite_false (by simpa only [h0, ite_false] using htestM)
        (.ite_false (by simpa only [h1, ite_false] using htestMK)
          (.ite_false (by simpa only [h2, ite_false] using htestMKK) (Exec.assign hD)))
    exact ⟨23, by simpa only [hval] using he, by decide⟩

/-- Apply the marker permutation to a whole source row, using
registers 60 and 52 for the two counts and 20,23,24 as scratch. -/
def gm06Alg511ReflectDartArrayProg (src dst : Arr) : Cmd :=
  .seq (.alloc dst (.len src)) (.seq (.assign 20 (.const 0))
    (forUp 20 (.len src)
      (.seq (.assign 23 (.read src (.reg 20)))
        (.seq (gm06Alg511ReflectAugmentedDartProg 60 52 23 24)
          (.write dst (.reg 20) (.reg 24))))))

/-- The array scan computes the exact mapped row in linear time
and preserves every array outside its destination. -/
theorem gm06Alg511ReflectDartArrayProg_exec {w : ℕ} (src dst : Arr) (hne : src ≠ dst)
    (m k : ℕ) (xs : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : 2 * (m + k + k) < 2 ^ w) (hlen : xs.length < 2 ^ w)
    (hwords : ∀ d ∈ xs, d < 2 ^ w) (hsrc : s.arrs src = xs)
    (hrM : s.regs 60 = m) (hrK : s.regs 52 = k) :
    ∃ s' t, Exec w (gm06Alg511ReflectDartArrayProg src dst) s s' t ∧
      t ≤ 6 + 78 * xs.length ∧ Keeps [20, 23, 24] [dst] s s' ∧
      s'.arrs dst = xs.map (gm06Alg511ReflectAugmentedDart m k) := by
  let f : ℕ → ℕ := fun i => gm06Alg511ReflectAugmentedDart m k (xs.getD i 0)
  let s₁ := s.setArr dst (List.replicate xs.length 0)
  let s₂ := s₁.setReg 20 0
  have hlenE : (Expr.len src).eval w s = some xs.length := eval_len hsrc hlen
  have he₁ : Exec w (.alloc dst (.len src)) s s₁ (1 + xs.length) := .alloc hlenE
  have he₂ : Exec w (.assign 20 (.const 0)) s₁ s₂ 2 := .assign (eval_const (Nat.two_pow_pos w))
  let Inv : ℕ → State → Prop := fun i st => Keeps [20, 23, 24] [dst] s st ∧ st.regs 20 = i ∧
    st.arrs dst = (List.range i).map f ++ List.replicate (xs.length - i) 0
  have hstart : Inv 0 s₂ := by
    refine ⟨((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _, by simp [s₂], ?_⟩
    simp [s₂, s₁]
  have hloop := forUp_pot Inv (fun _ => 0) xs.length 70 (r_i := 20) (hi := .len src)
    (body := .seq (.assign 23 (.read src (.reg 20)))
      (.seq (gm06Alg511ReflectAugmentedDartProg 60 52 23 24) (.write dst (.reg 20) (.reg 24))))
    (by omega : 1 < 2 ^ w) hlen
    (fun i _ st hi => ⟨hi.2.1, eval_len
      ((hi.1.2 src (by simpa using hne)).trans hsrc) hlen⟩)
    (fun i hi st hst => by
      have ha : st.arrs src = xs := (hst.1.2 src (by simpa using hne)).trans hsrc
      have hv : xs.getD i 0 = xs[i] := by simp [hi]
      have hd : xs[i] < 2 ^ w := hwords _ (List.getElem_mem hi)
      let st₁ := st.setReg 23 xs[i]
      have hread := Crossing.eval_read (a := src) (eval_reg hst.2.1 (hi.trans hlen))
        (by rw [ha]; exact hi) (by simpa only [ha] using hd)
      have heRead : Exec w (.assign 23 (.read src (.reg 20))) st st₁ 3 :=
        .assign (by simpa only [ha] using hread)
      obtain ⟨t, heDart, ht⟩ := gm06Alg511ReflectAugmentedDartProg_exec 60 52 23 24 m k xs[i] st₁
        hw hn hd (by simpa [st₁] using (hst.1.1 60 (by decide)).trans hrM)
        (by simpa [st₁] using (hst.1.1 52 (by decide)).trans hrK) (by simp [st₁])
      let st₂ := st₁.setReg 24 (gm06Alg511ReflectAugmentedDart m k xs[i])
      have hout : f i < 2 ^ w := by
        change gm06Alg511ReflectAugmentedDart m k (xs.getD i 0) < 2 ^ w
        rw [hv]
        by_cases hvalid : xs[i] < 2 * (m + k + k)
        · exact (gm06Alg511ReflectAugmentedDart_lt hvalid).trans hn
        · rw [gm06Alg511ReflectAugmentedDart_outside (by omega)]
          exact hd
      have hcap : i < (st₂.arrs dst).length := by
        simp only [st₂, st₁, State.setReg_arrs, hst.2.2, List.length_append,
          List.length_map, List.length_range, List.length_replicate]
        omega
      have heWrite : Exec w (.write dst (.reg 20) (.reg 24)) st₂ (st₂.writeArr dst i (f i)) 3 :=
        .write (eval_reg (by simpa [st₂, st₁] using hst.2.1) (hi.trans hlen))
          (eval_reg (by change gm06Alg511ReflectAugmentedDart m k xs[i] = f i; dsimp only [f]; rw [hv]) hout) hcap
      refine ⟨st₂.writeArr dst i (f i), 3 + (t + 3), .seq heRead (.seq heDart heWrite), by omega, ?_, by simpa [st₂, st₁] using hst.2.1⟩
      refine ⟨(((hst.1.setReg (by simp) _).setReg (by simp) _).writeArr (by simp) _ _).setReg (by simp) _,
        by simp, ?_⟩
      simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs, ite_true, st₂, st₁, State.setReg_arrs, hst.2.2]
      exact set_range_map f hi)
    0 (Nat.zero_le _) s₂ hstart
  obtain ⟨s', t, he, ht, hk, _, hfinal⟩ := hloop
  refine ⟨s', (1 + xs.length) + (2 + t), .seq he₁ (.seq he₂ he), ?_, hk, ?_⟩
  · simp only [Expr.cost, Nat.sub_zero] at ht
    omega
  · have hmap : (List.range xs.length).map f = xs.map (gm06Alg511ReflectAugmentedDart m k) := by
      apply List.ext_getElem (by simp)
      intro i hi hi'
      have hiXs : i < xs.length := by simpa only [List.length_map] using hi'
      simp only [List.getElem_map, List.getElem_range]
      change f i = gm06Alg511ReflectAugmentedDart m k xs[i]
      dsimp only [f]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiXs]
      rfl
    simpa only [Nat.sub_self, List.replicate_zero, List.append_nil, hmap] using hfinal

/-- Reverse a supplied rotation row and relabel its fixed cuff
markers, using a distinct scratch array for the reversal. -/
def gm06Alg511ReflectRotationRowProg (src tmp dst : Arr) : Cmd :=
  .seq (Crossing.liftReverseProg src tmp 20) (gm06Alg511ReflectDartArrayProg tmp dst)

/-- The full rotation-row reflection executes in linear time. It
retains its source when that source differs from the destination,
and changes only the designated scratch and destination arrays. -/
theorem gm06Alg511ReflectRotationRowProg_exec {w : ℕ} (src tmp dst : Arr)
    (hsrcTmp : src ≠ tmp) (htmpDst : tmp ≠ dst)
    (m k : ℕ) (xs : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : 2 * (m + k + k) < 2 ^ w) (hlen : xs.length + 1 < 2 ^ w)
    (hwords : ∀ d ∈ xs, d < 2 ^ w) (hsrc : s.arrs src = xs)
    (hrM : s.regs 60 = m) (hrK : s.regs 52 = k) :
    ∃ s' t, Exec w (gm06Alg511ReflectRotationRowProg src tmp dst) s s' t ∧
      t ≤ 12 + 94 * xs.length ∧ Keeps [20, 23, 24] [tmp, dst] s s' ∧
      s'.arrs dst = xs.reverse.map (gm06Alg511ReflectAugmentedDart m k) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hreverse, harrays, hregs⟩ := Crossing.liftReverseProg_exec
    src tmp 20 hsrcTmp xs s hsrc hwords hlen
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout⟩ := gm06Alg511ReflectDartArrayProg_exec
    tmp dst htmpDst m k xs.reverse s₁ hw hn
    (by simpa only [List.length_reverse] using (show xs.length < 2 ^ w by omega))
    (fun d hd => hwords d (List.mem_reverse.mp hd)) hreverse
    ((hregs 60 (by decide)).trans hrM) ((hregs 52 (by decide)).trans hrK)
  have hk₁ : Keeps [20] [tmp] s s₁ :=
    ⟨fun r hr => hregs r (by simpa using hr), fun a ha => harrays a (by simpa using ha)⟩
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_,
    (hk₁.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp), hout⟩
  rw [List.length_reverse] at ht₂
  omega

end GraphMinor.Compute
