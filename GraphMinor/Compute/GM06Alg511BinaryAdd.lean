module

public import GraphMinor.Compute.GM06Alg511BinaryDigits
public import GraphMinor.Compute.CrossingOpsBasic
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsReplLists
import Mathlib.Tactic

/-!
# Word RAM addition of binary digit rows

The large integers in VI (5.11), page 134, are represented by digit
arrays, with one bit per word. Add the two unsigned digit rows a
column at a time, keeping only a one-bit carry in a register.
Missing columns contribute zero. The output has the larger input
width plus a final carry digit. Every arithmetic intermediate is
at most three. Only lengths and array positions depend on input
size, so logarithmic machine words suffice for linear running time.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read the current input digit, or zero beyond the supplied row. -/
def gm06Alg511LoadBinaryDigitProg (a r : ℕ) : Cmd :=
  .ite (.op .lt (.reg 2100) (.len a))
    (.assign r (.read a (.reg 2100))) (.assign r (.const 0))

/-- One ordinary addition column. Arrays 2000 and 2001 contain
unsigned input digits and array 2002 receives the result. -/
def gm06Alg511BinaryAddBody : Cmd :=
  .seq (gm06Alg511LoadBinaryDigitProg 2000 2103)
    (.seq (gm06Alg511LoadBinaryDigitProg 2001 2104)
      (.seq (.assign 2105 (.op .add (.op .add (.reg 2103) (.reg 2104)) (.reg 2102)))
        (.seq (.write 2002 (.reg 2100) (.op .mod (.reg 2105) (.const 2)))
          (.assign 2102 (.op .div (.reg 2105) (.const 2))))))

/-- Add two supplied binary rows, allocating the output and
initializing every index and carry register before reading it. -/
def gm06Alg511BinaryAddWithCarryProg (carry : Bool) : Cmd :=
  .seq (.assign 2101 (.op .add (.len 2000) (.op .sub (.len 2001) (.len 2000))))
    (.seq (.alloc 2002 (.op .add (.reg 2101) (.const 1)))
      (.seq (.assign 2102 (.const carry.toNat))
        (.seq (.assign 2100 (.const 0))
          (.seq (forUp 2100 (.reg 2101) gm06Alg511BinaryAddBody)
            (.write 2002 (.reg 2101) (.reg 2102))))))

/-- Ordinary unsigned addition starts with zero carry. -/
def gm06Alg511BinaryAddProg : Cmd := gm06Alg511BinaryAddWithCarryProg false

private theorem binary_getD_lt (a : List ℕ) (ha : ∀ d ∈ a, d < 2) (i : ℕ) : a.getD i 0 < 2 := by
  by_cases hi : i < a.length
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using
      ha a[i] (List.getElem_mem hi)
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : a.length ≤ i), Option.getD_none]
    decide

/-- A single digit read needs only the digit word, its index and
row length to fit. No bound on the represented integer is used. -/
theorem gm06Alg511LoadBinaryDigitProg_exec {w : ℕ} (a r : ℕ) (xs : List ℕ)
    (s : State) (i : ℕ) (hw : 1 < 2 ^ w) (hi : i < 2 ^ w)
    (hlen : xs.length < 2 ^ w) (hbits : ∀ d ∈ xs, d < 2)
    (ha : s.arrs a = xs) (hindex : s.regs 2100 = i) :
    ∃ t u, Exec w (gm06Alg511LoadBinaryDigitProg a r) s t u ∧ u ≤ 6 ∧
      t.regs r = xs.getD i 0 ∧ Keeps [r] [] s t := by
  let t := s.setReg r (xs.getD i 0)
  have hd : xs.getD i 0 < 2 ^ w := (binary_getD_lt xs hbits i).trans_le (by omega)
  have hcond := Crossing.eval_lt (Crossing.eval_reg hindex hi) (Crossing.eval_len ha hlen) hw
  by_cases hil : i < xs.length
  · have hread : Expr.eval w s (.read a (.reg 2100)) = some (xs.getD i 0) := by
      have he := Crossing.eval_read (a := a) (Crossing.eval_reg hindex hi)
        (by rw [ha]; exact hil) (by simpa only [ha] using (hbits _ (List.getElem_mem hil)).trans_le (by omega : 2 ≤ 2 ^ w))
      simpa only [ha, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some] using he
    exact ⟨t, 6, .ite_true (by simpa only [hil, ite_true] using hcond) (by decide)
      (.assign hread), le_rfl, by simp [t], (Keeps.refl _ _ s).setReg (by simp) _⟩
  · have hz : xs.getD i 0 = 0 := by simp [List.getD_eq_getElem?_getD, hil]
    refine ⟨t, 5, ?_, by decide, by simp [t], (Keeps.refl _ _ s).setReg (by simp) _⟩
    have he : Exec w (.assign r (.const 0)) s (s.setReg r 0) 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
    change Exec w (gm06Alg511LoadBinaryDigitProg a r) s (s.setReg r (xs.getD i 0)) 5
    rw [hz]
    exact .ite_false (by simpa only [hil, ite_false] using hcond) he

private theorem add_body_frame {w : ℕ} {s t : State} {u : ℕ}
    (he : Exec w gm06Alg511BinaryAddBody s t u) :
    Keeps [2103, 2104, 2105, 2102] [2002] s t := by
  have hr : gm06Alg511BinaryAddBody.writtenRegs ⊆ ([2103, 2104, 2105, 2102] : List ℕ).toFinset := by decide
  have ha : gm06Alg511BinaryAddBody.writtenArrs ⊆ ([2002] : List ℕ).toFinset := by decide
  exact ⟨fun r hn => he.regs_eq_of_not_mem_writtenRegs (fun hm => hn (List.mem_toFinset.mp (hr hm))),
    fun a hn => he.arrs_eq_of_not_mem_writtenArrs (fun hm => hn (List.mem_toFinset.mp (ha hm)))⟩

/-- One addition column reads two bits, stores their sum modulo
two and stores the quotient as the next carry, in at most 27 steps. -/
theorem gm06Alg511BinaryAddBody_exec {w : ℕ} (a b out : List ℕ) (i c : ℕ)
    (s : State) (hw : 3 < 2 ^ w) (hi : i < 2 ^ w)
    (ha : a.length < 2 ^ w) (hb : b.length < 2 ^ w) (houti : i < out.length)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) (hc : c < 2)
    (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b) (hO : s.arrs 2002 = out)
    (hindex : s.regs 2100 = i) (hcarry : s.regs 2102 = c) :
    ∃ t u, Exec w gm06Alg511BinaryAddBody s t u ∧ u ≤ 27 ∧
      Keeps [2103, 2104, 2105, 2102] [2002] s t ∧
      t.arrs 2002 = out.set i ((a.getD i 0 + b.getD i 0 + c) % 2) ∧
      t.regs 2102 = (a.getD i 0 + b.getD i 0 + c) / 2 := by
  have hda := binary_getD_lt a habits i
  have hdb := binary_getD_lt b hbbits i
  let v := a.getD i 0 + b.getD i 0 + c
  have hv : v < 2 ^ w := by dsimp [v]; omega
  obtain ⟨s₁, u₁, he₁, ht₁, hd₁, hk₁⟩ := gm06Alg511LoadBinaryDigitProg_exec 2000 2103 a s i
    (by omega) hi ha habits hA hindex
  obtain ⟨s₂, u₂, he₂, ht₂, hd₂, hk₂⟩ := gm06Alg511LoadBinaryDigitProg_exec 2001 2104 b s₁ i
    (by omega) hi hb hbbits ((hk₁.2 2001 (by simp)).trans hB) ((hk₁.1 2100 (by decide)).trans hindex)
  let s₃ := s₂.setReg 2105 v
  have hsum : Exec w (.assign 2105 (.op .add (.op .add (.reg 2103) (.reg 2104)) (.reg 2102))) s₂ s₃ 6 :=
    .assign (Crossing.eval_add
      (Crossing.eval_add (Crossing.eval_reg ((hk₂.1 2103 (by decide)).trans hd₁) (by omega))
        (Crossing.eval_reg hd₂ (by omega)) (by omega))
      (Crossing.eval_reg ((hk₂.1 2102 (by decide)).trans ((hk₁.1 2102 (by decide)).trans hcarry)) (by omega)) hv)
  let s₄ := s₃.writeArr 2002 i (v % 2)
  have hindex₃ : s₃.regs 2100 = i := by
    simpa [s₃] using (hk₂.1 2100 (by decide)).trans ((hk₁.1 2100 (by decide)).trans hindex)
  have hmod : Expr.eval w s₃ (.op .mod (.reg 2105) (.const 2)) = some (v % 2) := by
    simp only [Expr.eval, s₃, State.setReg_regs_self, checkWord_of_lt hv,
      checkWord_of_lt (by omega : 2 < 2 ^ w), BinOp.eval, BinOp.raw]
    exact checkWord_of_lt ((Nat.mod_lt _ (by decide : 0 < 2)).trans_le (by omega))
  have hO₃ : s₃.arrs 2002 = out := (hk₂.2 2002 (by simp)).trans ((hk₁.2 2002 (by simp)).trans hO)
  have hwrite : Exec w (.write 2002 (.reg 2100) (.op .mod (.reg 2105) (.const 2))) s₃ s₄ 5 :=
    .write (Crossing.eval_reg hindex₃ hi) hmod (by rw [hO₃]; exact houti)
  let s₅ := s₄.setReg 2102 (v / 2)
  have hdiv : Exec w (.assign 2102 (.op .div (.reg 2105) (.const 2))) s₄ s₅ 4 :=
    .assign (Crossing.eval_div (Crossing.eval_reg (by simp [s₄, s₃]) hv)
      (Crossing.eval_const (by omega)) (by decide) ((Nat.div_le_self _ _).trans_lt hv))
  have he : Exec w gm06Alg511BinaryAddBody s s₅ (u₁ + (u₂ + (6 + (5 + 4)))) :=
    .seq he₁ (.seq he₂ (.seq hsum (.seq hwrite hdiv)))
  refine ⟨s₅, _, he, by omega, add_body_frame he, ?_, by simp [s₅, v]⟩
  simp only [s₅, s₄, State.setReg_arrs, State.writeArr, State.setArr_arrs_self, hO₃, v]

private def digitPrefix (xs : List ℕ) (i : ℕ) : List ℕ := xs.take i ++ List.replicate (xs.length - i) 0

private theorem prefix_length (xs : List ℕ) (i : ℕ) : (digitPrefix xs i).length = xs.length := by
  simp only [digitPrefix, List.length_append, List.length_take, List.length_replicate]
  omega

private theorem prefix_step (xs : List ℕ) {i : ℕ} (hi : i < xs.length) :
    (digitPrefix xs i).set i xs[i] = digitPrefix xs (i + 1) := by
  have ht : (xs.take i).length = i := List.length_take_of_le hi.le
  have hr : List.replicate (xs.length - i) 0 = 0 :: List.replicate (xs.length - (i + 1)) 0 := by
    rw [show xs.length - i = xs.length - (i + 1) + 1 by omega, List.replicate_succ]
  unfold digitPrefix
  rw [List.set_append_right _ _ (by rw [ht]), ht, Nat.sub_self, hr, List.set_cons_zero,
    List.take_succ_eq_append_getElem hi]
  simp only [List.singleton_append, List.append_assoc]

/-- The complete digitwise adder executes in linear time, with
one final carry column and no magnitude bound on either number. -/
theorem gm06Alg511BinaryAddWithCarryProg_exec {w : ℕ} (a b : List ℕ) (carry : Bool) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max a.length b.length + 1 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2)
    (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b) :
    ∃ t u, Exec w (gm06Alg511BinaryAddWithCarryProg carry) s t u ∧
      u ≤ 25 + 40 * max a.length b.length ∧
      Keeps [2100, 2101, 2102, 2103, 2104, 2105] [2002] s t ∧
      t.arrs 2002 = gm06Alg511BinaryAddDigits (max a.length b.length) a b carry.toNat := by
  have hcc : carry.toNat < 2 := by cases carry <;> decide
  let N := max a.length b.length
  let Z := gm06Alg511BinaryAddDigits N a b carry.toNat
  let R := [2100, 2101, 2102, 2103, 2104, 2105]
  have hlen : Z.length = N + 1 := gm06Alg511BinaryAddDigits_length N a b carry.toNat
  have hN : N < 2 ^ w := by dsimp only [N] at *; omega
  have ha : a.length < 2 ^ w := (Nat.le_max_left _ _).trans_lt hN
  have hb : b.length < 2 ^ w := (Nat.le_max_right _ _).trans_lt hN
  let s₁ := s.setReg 2101 N
  have he₁ : Exec w (.assign 2101 (.op .add (.len 2000) (.op .sub (.len 2001) (.len 2000)))) s s₁ 6 := by
    have hn' : a.length + (b.length - a.length) = N := by dsimp only [N]; omega
    simpa only [hn', s₁, Expr.cost, Nat.reduceAdd] using Exec.assign (r := 2101)
      (Crossing.eval_add (Crossing.eval_len hA ha)
        (Crossing.eval_sub (Crossing.eval_len hB hb) (Crossing.eval_len hA ha)) (by rwa [hn']))
  let s₂ := s₁.setArr 2002 (List.replicate (N + 1) 0)
  have he₂ : Exec w (.alloc 2002 (.op .add (.reg 2101) (.const 1))) s₁ s₂ (N + 4) := by
    simpa only [Expr.cost, Nat.reduceAdd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Exec.alloc (a := 2002) (Crossing.eval_add (Crossing.eval_reg (by simp [s₁]) hN)
        (Crossing.eval_const (by omega)) hsize)
  let s₃ := s₂.setReg 2102 carry.toNat
  let s₄ := s₃.setReg 2100 0
  have he₃ : Exec w (.assign 2102 (.const carry.toNat)) s₂ s₃ 2 := .assign (Crossing.eval_const (hcc.trans_le (by omega)))
  have he₄ : Exec w (.assign 2100 (.const 0)) s₃ s₄ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have hk₄ : Keeps R [2002] s s₄ :=
    ((((Keeps.refl _ _ s).setReg (by simp [R]) _).setArr (by simp) _).setReg (by simp [R]) _).setReg (by simp [R]) _
  let I : ℕ → State → Prop := fun i st => st.regs 2100 = i ∧ st.regs 2101 = N ∧
    st.regs 2102 = gm06Alg511BinaryCarryAfter a b carry.toNat i ∧ st.arrs 2000 = a ∧ st.arrs 2001 = b ∧
      st.arrs 2002 = digitPrefix Z i ∧ Keeps R [2002] s st
  have hI : I 0 s₄ := by
    refine ⟨by simp [s₄], by simp [s₄, s₃, s₂, s₁], by simp [s₄, s₃, gm06Alg511BinaryCarryAfter],
      (hk₄.2 2000 (by decide)).trans hA, (hk₄.2 2001 (by decide)).trans hB, ?_, hk₄⟩
    simp [s₄, s₃, s₂, digitPrefix, hlen]
  obtain ⟨st, tt, heLoop, htLoop, hILoop⟩ := Crossing.forUp_exec' I N 27 (r_i := 2100)
    (hi := .reg 2101) (body := gm06Alg511BinaryAddBody) (by omega) hN
    (fun i hi st h => ⟨h.1, Crossing.eval_reg h.2.1 hN⟩)
    (by
      intro i hi st h
      obtain ⟨hidx, hNst, hcst, haSt, hbSt, hoSt, hkeep⟩ := h
      have hiZ : i < Z.length := by rw [hlen]; omega
      obtain ⟨su, tu, heu, htu, hku, hou, hcu⟩ := gm06Alg511BinaryAddBody_exec
        a b (digitPrefix Z i) i (gm06Alg511BinaryCarryAfter a b carry.toNat i) st hw
        (hi.trans hN) ha hb (by rw [prefix_length]; exact hiZ) habits hbbits
        (gm06Alg511BinaryCarryAfter_lt_two a b carry.toNat i habits hbbits hcc) haSt hbSt hoSt hidx hcst
      have htot := hkeep.trans hku (by simp [R]) (by simp)
      have hdigit : (a.getD i 0 + b.getD i 0 + gm06Alg511BinaryCarryAfter a b carry.toNat i) % 2 = Z[i] := by
        have hh := gm06Alg511BinaryAddDigits_digit N i a b carry.toNat hi
        simpa only [Z, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiZ, Option.getD_some] using hh.symm
      have hiKeep : su.regs 2100 = i := (hku.1 2100 (by decide)).trans hidx
      have htot' := htot.setReg (show 2100 ∈ R by simp [R]) (i + 1)
      refine ⟨su, tu, heu, htu, ?_, hiKeep⟩
      refine ⟨by simp, ?_, ?_,
        (htot'.2 2000 (by decide)).trans hA, (htot'.2 2001 (by decide)).trans hB, ?_, htot'⟩
      · simpa only [State.setReg_regs_ne _ _ (by decide : (2101 : ℕ) ≠ 2100)] using
          (hku.1 2101 (by decide)).trans hNst
      · simpa only [State.setReg_regs_ne _ _ (by decide : (2102 : ℕ) ≠ 2100),
          gm06Alg511BinaryCarryAfter_succ] using hcu
      · simpa only [State.setReg_arrs, hdigit, prefix_step Z hiZ] using hou) s₄ hI
  obtain ⟨hidx, hNst, hcst, _, _, hoSt, hkeep⟩ := hILoop
  let t := st.writeArr 2002 N (gm06Alg511BinaryCarryAfter a b carry.toNat N)
  have heFinal : Exec w (.write 2002 (.reg 2101) (.reg 2102)) st t 3 :=
    .write (Crossing.eval_reg hNst hN)
      (Crossing.eval_reg hcst ((gm06Alg511BinaryCarryAfter_lt_two a b carry.toNat N habits hbbits hcc).trans_le (by omega)))
      (by rw [hoSt, prefix_length, hlen]; omega)
  have hcode : t.arrs 2002 = Z := by
    change (st.arrs 2002).set N (gm06Alg511BinaryCarryAfter a b carry.toNat N) = Z
    rw [hoSt]
    have hiZ : N < Z.length := by rw [hlen]; omega
    have hlast : gm06Alg511BinaryCarryAfter a b carry.toNat N = Z[N] := by
      have hh := gm06Alg511BinaryAddDigits_final N a b carry.toNat
      simpa only [Z, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiZ, Option.getD_some] using hh.symm
    rw [hlast, prefix_step Z hiZ, ← hlen]
    simp [digitPrefix]
  refine ⟨t, 6 + (N + 4 + (2 + (2 + (tt + 3)))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq heLoop heFinal)))), ?_, hkeep.writeArr (by simp) _ _, hcode⟩
  simp only [Expr.cost] at htLoop
  dsimp only [N] at *
  omega

/-- Ordinary unsigned addition is the zero-carry case of the
same verified digitwise machine loop. -/
theorem gm06Alg511BinaryAddProg_exec {w : ℕ} (a b : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max a.length b.length + 1 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2)
    (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b) :
    ∃ t u, Exec w gm06Alg511BinaryAddProg s t u ∧
      u ≤ 25 + 40 * max a.length b.length ∧
      Keeps [2100, 2101, 2102, 2103, 2104, 2105] [2002] s t ∧
      t.arrs 2002 = gm06Alg511BinaryAddDigits (max a.length b.length) a b 0 := by
  exact gm06Alg511BinaryAddWithCarryProg_exec a b false s hw hsize habits hbbits hA hB

/-- Addition runs in linear time in the number of supplied digits,
with logarithmic Word RAM words. Its output is a binary row for the
exact sum, including a final carry column. No numeric magnitude is
used as input size or assumed to fit in a machine word. -/
theorem gm06Alg511BinaryAdd_computes :
    ComputesRelInTime
      (fun x : List Bool × List Bool => x.1.length + x.2.length + 1)
      (fun x s => s.arrs 2000 = x.1.map Bool.toNat ∧ s.arrs 2001 = x.2.map Bool.toNat)
      (fun x s =>
        gm06Alg511BinaryValue (s.arrs 2002) = gm06Alg511BinaryValue (x.1.map Bool.toNat) +
          gm06Alg511BinaryValue (x.2.map Bool.toNat) ∧
        (∀ d ∈ s.arrs 2002, d < 2) ∧
        (s.arrs 2002).length = max x.1.length x.2.length + 1)
      gm06Alg511BinaryAddProg (fun n => n + 1) := by
  refine ⟨60, 2, by decide, by decide, ?_⟩
  intro x s hs
  let a := x.1.map Bool.toNat
  let b := x.2.map Bool.toNat
  let size := x.1.length + x.2.length + 1
  let w := wordSize 2 size
  have hw : 3 < 2 ^ w := by
    have hp := pow_lt_two_pow_wordSize (c := 2) (by decide) size
    have hb : 3 ≤ size + 2 := by dsimp only [size]; omega
    have hh : 3 < (size + 2) ^ 2 := by nlinarith only [hb]
    exact hh.trans hp
  have hsize : max a.length b.length + 1 < 2 ^ w :=
    lt_two_pow_wordSize_of_le (c := 2) (n := size) (by decide) (by
      dsimp only [a, b, size]
      simp only [List.length_map]
      omega)
  have bits (xs : List Bool) : ∀ d ∈ xs.map Bool.toNat, d < 2 := by
    intro d hd
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    cases q <;> decide
  obtain ⟨t, u, he, ht, _, hout⟩ := gm06Alg511BinaryAddProg_exec a b s hw hsize
    (bits x.1) (bits x.2) hs.1 hs.2
  refine ⟨t, u, he, ?_, ?_, ?_, ?_⟩
  · have hm : max a.length b.length ≤ size := by
      dsimp only [a, b, size]
      simp only [List.length_map]
      omega
    dsimp only [size] at *
    omega
  · rw [hout]
    simpa only [Nat.add_zero] using gm06Alg511BinaryAddDigits_value (max a.length b.length) a b 0
      (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  · rw [hout]
    exact gm06Alg511BinaryAddDigits_words _ a b 0 (bits x.1) (bits x.2) (by decide)
  · rw [hout, gm06Alg511BinaryAddDigits_length]
    simp only [a, b, List.length_map]

end GraphMinor.Compute
