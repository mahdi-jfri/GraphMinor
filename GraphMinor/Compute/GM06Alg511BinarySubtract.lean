module

public import GraphMinor.Compute.GM06Alg511BinaryComplement
public import GraphMinor.Compute.GM06Alg511CopyRow
import GraphMinor.Compute.CrossingOpsReplLists
import Mathlib.Tactic

/-!
# Binary subtraction and unsigned comparison on the Word RAM

Choose the larger input digit count as the common width. Complement
the second input through that width and add it to the first with
initial carry one. Copy the low columns as the difference row and
return the borrow bit. That bit is exactly strict unsigned comparison.
Restore the original second operand after the addition. Every pass
is linear in the supplied digit counts, and no magnitude is stored
in a single word. This implements arithmetic for VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Copy the low columns of the adder output, omitting its carry. -/
def gm06Alg511BinaryLowColumnsProg : Cmd :=
  mapProg 2231 (.reg 2230) 2005 2002 (.reg 2231)

/-- Subtract the two unsigned digit arrays, returning the low
columns in array 2005 and the borrow bit in register zero. -/
def gm06Alg511BinarySubtractProg : Cmd :=
  .seq (.assign 2230 (.op .add (.len 2000) (.op .sub (.len 2001) (.len 2000))))
    (.seq gm06Alg511BinaryComplementProg
      (.seq (gm06Alg511CopyRowProg 2001 2004)
        (.seq (gm06Alg511CopyRowProg 2003 2001)
          (.seq (gm06Alg511BinaryAddWithCarryProg true)
            (.seq (gm06Alg511CopyRowProg 2004 2001)
              (.seq gm06Alg511BinaryLowColumnsProg
                (.seq (.assign 2232 (.read 2002 (.reg 2230)))
                  (.assign 0 (.op .sub (.const 1) (.reg 2232))))))))))

private theorem low_columns_exec {w : ℕ} (n : ℕ) (z : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hlen : n ≤ z.length)
    (hbits : ∀ d ∈ z, d < 2) (hz : s.arrs 2002 = z) (hN : s.regs 2230 = n) :
    ∃ t u, Exec w gm06Alg511BinaryLowColumnsProg s t u ∧ u ≤ 6 + 12 * n ∧
      Keeps [2231] [2005] s t ∧ t.arrs 2005 = z.take n := by
  obtain ⟨t, u, he, ht, hk, hout⟩ := mapProg_exec 2231 (.reg 2230) 2005 2002 (.reg 2231)
    (by decide) n id z s hw hn
    (fun st hk => Crossing.eval_reg ((hk.1 2230 (by decide)).trans hN) hn)
    (fun st i hk hi hin => Crossing.eval_reg hi (hin.trans hn))
    (fun i hi => hi.trans_le hlen) (fun d hd => (hbits d hd).trans_le (by omega)) hz
  have heq : (List.range n).map (fun i => z.getD i 0) = z.take n := by
    apply List.ext_getElem (by simp only [List.length_map, List.length_range, List.length_take]; omega)
    intro i hi hj
    have hin : i < n := by simpa only [List.length_map, List.length_range] using hi
    have hiz : i < z.length := hin.trans_le hlen
    simp only [List.getElem_map, List.getElem_range, List.getElem_take,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiz, Option.getD_some]
  refine ⟨t, u, he, ?_, hk, ?_⟩
  · simp only [Expr.cost] at ht
    omega
  · simpa only [id_eq, heq] using hout

private theorem subtract_frame {w : ℕ} {s t : State} {u : ℕ}
    (he : Exec w gm06Alg511BinarySubtractProg s t u) :
    Keeps [0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232]
      [2001, 2002, 2003, 2004, 2005] s t := by
  have hr : gm06Alg511BinarySubtractProg.writtenRegs ⊆
      ([0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232] : List ℕ).toFinset := by decide
  have ha : gm06Alg511BinarySubtractProg.writtenArrs ⊆
      ([2001, 2002, 2003, 2004, 2005] : List ℕ).toFinset := by decide
  exact ⟨fun r hn => he.regs_eq_of_not_mem_writtenRegs (fun hm => hn (List.mem_toFinset.mp (hr hm))),
    fun a hn => he.arrs_eq_of_not_mem_writtenArrs (fun hm => hn (List.mem_toFinset.mp (ha hm)))⟩

/-- The actual subtraction/comparison program runs in linear time
in the digit count, returns the exact low difference columns and
borrow, and restores both original operand arrays. Only digit
counts, individual bits and carry words need to fit the machine. -/
theorem gm06Alg511BinarySubtractProg_exec {w : ℕ} (a b : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max a.length b.length + 1 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2)
    (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b) :
    ∃ t u, Exec w gm06Alg511BinarySubtractProg s t u ∧
      u ≤ 100 + 120 * max a.length b.length ∧
      Keeps [0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232]
        [2002, 2003, 2004, 2005] s t ∧
      t.arrs 2005 = (gm06Alg511BinarySubtractColumns (max a.length b.length) a b).take (max a.length b.length) ∧
      t.regs 0 = gm06Alg511BinarySubtractBorrow (max a.length b.length) a b := by
  let n := max a.length b.length
  let c := gm06Alg511BinaryComplementDigits n b
  let z := gm06Alg511BinarySubtractColumns n a b
  let q := gm06Alg511BinaryCarryAfter a c 1 n
  have hn : n < 2 ^ w := by dsimp only [n]; omega
  have ha : a.length < 2 ^ w := (Nat.le_max_left _ _).trans_lt hn
  have hb : b.length < 2 ^ w := (Nat.le_max_right _ _).trans_lt hn
  have hc : c.length = n := gm06Alg511BinaryComplementDigits_length n b
  have hcbits := gm06Alg511BinaryComplementDigits_words n b
  have hzlen : z.length = n + 1 := gm06Alg511BinaryAddDigits_length n a c 1
  have hzbits : ∀ d ∈ z, d < 2 := gm06Alg511BinaryAddDigits_words n a c 1 habits hcbits (by decide)
  have hq : q < 2 := gm06Alg511BinaryCarryAfter_lt_two a c 1 n habits hcbits (by decide)
  let s₁ := s.setReg 2230 n
  have he₁ : Exec w (.assign 2230 (.op .add (.len 2000) (.op .sub (.len 2001) (.len 2000)))) s s₁ 6 := by
    have heq : a.length + (b.length - a.length) = n := by dsimp only [n]; omega
    simpa only [heq, s₁, Expr.cost, Nat.reduceAdd] using Exec.assign (r := 2230)
      (Crossing.eval_add (Crossing.eval_len hA ha)
        (Crossing.eval_sub (Crossing.eval_len hB hb) (Crossing.eval_len hA ha)) (by rwa [heq]))
  obtain ⟨s₂, u₂, he₂, ht₂, hk₂, hcomp⟩ := gm06Alg511BinaryComplementProg_exec n b s₁
    (by omega) hn hb hbbits hB (by simp [s₁])
  obtain ⟨s₃, u₃, he₃, ht₃, hk₃, hback⟩ := gm06Alg511CopyRowProg_exec 2001 2004 (by decide) b s₂
    (by omega) hb (fun d hd => (hbbits d hd).trans_le (by omega)) ((hk₂.2 2001 (by decide)).trans hB)
  obtain ⟨s₄, u₄, he₄, ht₄, hk₄, hnewB⟩ := gm06Alg511CopyRowProg_exec 2003 2001 (by decide) c s₃
    (by omega) (hc ▸ hn) (fun d hd => (hcbits d hd).trans_le (by omega))
    ((hk₃.2 2003 (by decide)).trans hcomp)
  have hA₄ : s₄.arrs 2000 = a := (hk₄.2 2000 (by decide)).trans
    ((hk₃.2 2000 (by decide)).trans ((hk₂.2 2000 (by decide)).trans hA))
  have hnAdd : max a.length c.length = n := by rw [hc]; exact Nat.max_eq_right (Nat.le_max_left _ _)
  obtain ⟨s₅, u₅, he₅, ht₅, hk₅, hsum⟩ := gm06Alg511BinaryAddWithCarryProg_exec a c true s₄
    hw (by rwa [hnAdd]) habits hcbits hA₄ hnewB
  rw [hnAdd] at ht₅ hsum
  change s₅.arrs 2002 = z at hsum
  have hback₅ : s₅.arrs 2004 = b := (hk₅.2 2004 (by decide)).trans
    ((hk₄.2 2004 (by decide)).trans hback)
  obtain ⟨s₆, u₆, he₆, ht₆, hk₆, hB₆⟩ := gm06Alg511CopyRowProg_exec 2004 2001 (by decide) b s₅
    (by omega) hb (fun d hd => (hbbits d hd).trans_le (by omega)) hback₅
  have hN₆ : s₆.regs 2230 = n := (hk₆.1 2230 (by decide)).trans
    ((hk₅.1 2230 (by decide)).trans ((hk₄.1 2230 (by decide)).trans
      ((hk₃.1 2230 (by decide)).trans ((hk₂.1 2230 (by decide)).trans (by simp [s₁])))))
  have hsum₆ : s₆.arrs 2002 = z := (hk₆.2 2002 (by decide)).trans hsum
  obtain ⟨s₇, u₇, he₇, ht₇, hk₇, hlow⟩ := low_columns_exec n z s₆ (by omega) hn
    (by rw [hzlen]; omega) hzbits hsum₆ hN₆
  have hsum₇ : s₇.arrs 2002 = z := (hk₇.2 2002 (by decide)).trans hsum₆
  have hN₇ : s₇.regs 2230 = n := (hk₇.1 2230 (by decide)).trans hN₆
  have hin : n < z.length := by rw [hzlen]; omega
  have hlast : z.getD n 0 = q := gm06Alg511BinaryAddDigits_final n a c 1
  have hread : Expr.eval w s₇ (.read 2002 (.reg 2230)) = some q := by
    have hh := Crossing.eval_read (a := 2002) (Crossing.eval_reg hN₇ hn)
      (by rw [hsum₇]; exact hin)
      (by simpa only [hsum₇] using (hzbits z[n] (List.getElem_mem hin)).trans_le (by omega : 2 ≤ 2 ^ w))
    have hh' : Expr.eval w s₇ (.read 2002 (.reg 2230)) = some (z.getD n 0) := by
      simpa only [hsum₇, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using hh
    rw [hlast] at hh'
    exact hh'
  let s₈ := s₇.setReg 2232 q
  have he₈ : Exec w (.assign 2232 (.read 2002 (.reg 2230))) s₇ s₈ 3 := .assign hread
  let t := s₈.setReg 0 (1 - q)
  have he₉ : Exec w (.assign 0 (.op .sub (.const 1) (.reg 2232))) s₈ t 4 :=
    .assign (Crossing.eval_sub (Crossing.eval_const (by omega))
      (Crossing.eval_reg (by simp [s₈]) (hq.trans_le (by omega))))
  have he : Exec w gm06Alg511BinarySubtractProg s t
      (6 + (u₂ + (u₃ + (u₄ + (u₅ + (u₆ + (u₇ + (3 + 4)))))))) :=
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ (.seq he₇ (.seq he₈ he₉)))))))
  have hBfinal : t.arrs 2001 = b := (hk₇.2 2001 (by decide)).trans hB₆
  have hframe := subtract_frame he
  refine ⟨t, _, he, ?_, ⟨hframe.1, ?_⟩, hlow, by simp [t, gm06Alg511BinarySubtractBorrow, q, c, n]⟩
  · have hbN : b.length ≤ n := Nat.le_max_right _ _
    dsimp only [c] at ht₄
    rw [gm06Alg511BinaryComplementDigits_length] at ht₄
    omega
  · intro arr harr
    by_cases heq : arr = 2001
    · subst arr; exact hBfinal.trans hB.symm
    · apply hframe.2 arr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at harr ⊢
      tauto

/-- Unsigned binary subtraction with a borrow flag has linear
time and logarithmic machine words in the total supplied digit
count. The output balance specifies the difference exactly even
when the unsigned result underflows the chosen width. -/
theorem gm06Alg511BinarySubtract_computes :
    ComputesRelInTime
      (fun x : List Bool × List Bool => x.1.length + x.2.length + 1)
      (fun x s => s.arrs 2000 = x.1.map Bool.toNat ∧ s.arrs 2001 = x.2.map Bool.toNat)
      (fun x s =>
        gm06Alg511BinaryValue (s.arrs 2005) + gm06Alg511BinaryValue (x.2.map Bool.toNat) =
          gm06Alg511BinaryValue (x.1.map Bool.toNat) + 2 ^ (max x.1.length x.2.length) * s.regs 0 ∧
        (s.regs 0 = 1 ↔ gm06Alg511BinaryValue (x.1.map Bool.toNat) < gm06Alg511BinaryValue (x.2.map Bool.toNat)) ∧
        (∀ d ∈ s.arrs 2005, d < 2) ∧ (s.arrs 2005).length = max x.1.length x.2.length)
      gm06Alg511BinarySubtractProg (fun n => n + 1) := by
  refine ⟨220, 2, by decide, by decide, ?_⟩
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
  obtain ⟨t, u, he, ht, _, hout, hflag⟩ := gm06Alg511BinarySubtractProg_exec a b s hw hsize
    (bits x.1) (bits x.2) hs.1 hs.2
  refine ⟨t, u, he, ?_, ?_, ?_, ?_, ?_⟩
  · have hm : max a.length b.length ≤ size := by
      dsimp only [a, b, size]
      simp only [List.length_map]
      omega
    dsimp only [size] at *
    omega
  · rw [hout, hflag]
    simpa only [a, b, List.length_map] using gm06Alg511BinarySubtractColumns_balance
      (max a.length b.length) a b (Nat.le_max_left _ _) (Nat.le_max_right _ _) (bits x.1) (bits x.2)
  · rw [hflag]
    exact gm06Alg511BinarySubtractBorrow_eq_one_iff _ a b (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      (bits x.1) (bits x.2)
  · rw [hout]
    intro d hd
    exact gm06Alg511BinaryAddDigits_words _ a _ 1 (bits x.1)
      (gm06Alg511BinaryComplementDigits_words _ b) (by decide) d (List.mem_of_mem_take hd)
  · rw [hout]
    simp only [List.length_take, gm06Alg511BinarySubtractColumns, gm06Alg511BinaryAddDigits_length,
      a, b, List.length_map]
    omega

/-- The same actual program decides strict unsigned comparison
in linear time with logarithmic words by returning the proved borrow. -/
theorem gm06Alg511BinaryLess_computes :
    ComputesRelInTime
      (fun x : List Bool × List Bool => x.1.length + x.2.length + 1)
      (fun x s => s.arrs 2000 = x.1.map Bool.toNat ∧ s.arrs 2001 = x.2.map Bool.toNat)
      (fun x s => s.regs 0 = 1 ↔
        gm06Alg511BinaryValue (x.1.map Bool.toNat) < gm06Alg511BinaryValue (x.2.map Bool.toNat))
      gm06Alg511BinarySubtractProg (fun n => n + 1) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := gm06Alg511BinarySubtract_computes
  refine ⟨C, c, hC, hc, ?_⟩
  intro x s hs
  obtain ⟨t, u, he, ht, hout⟩ := hrun x s hs
  exact ⟨t, u, he, ht, hout.2.1⟩

end GraphMinor.Compute
