module

public import GraphMinor.Compute.GM06Alg511BinaryMultiplyPass
import Mathlib.Tactic

/-!
# Binary multiplication on the Word RAM

Keep the two supplied digit rows and an initially empty accumulator.
Scan the first row from low to high. At each set bit, add the second
row shifted by the column index. The accumulator represents the
product of the scanned prefix and the second operand. Its width
is at most the scanned column count plus the second operand width.
The complete scan takes quadratic time in the supplied digit count.
Only digits, carries, lengths and positions occupy machine words.
This supplies multiplication for VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Inspect the current retained first-operand bit, and perform a
shifted addition exactly when that bit is one. -/
def gm06Alg511BinaryMultiplyBody : Cmd :=
  .seq (.assign 2235 (.read 2300 (.reg 2233)))
    (.ite (.reg 2235) gm06Alg511BinaryMultiplyPassProg .skip)

/-- Multiply the supplied unsigned rows, using only binary
arithmetic. Return the product in array 2002 and restore both inputs. -/
def gm06Alg511BinaryMultiplyProg : Cmd :=
  .seq (gm06Alg511CopyRowProg 2000 2300)
    (.seq (gm06Alg511CopyRowProg 2001 2301)
      (.seq (.alloc 2302 (.const 0))
        (.seq (.assign 2233 (.const 0))
          (.seq (forUp 2233 (.len 2300) gm06Alg511BinaryMultiplyBody)
            (.seq (gm06Alg511CopyRowProg 2302 2002)
              (.seq (gm06Alg511CopyRowProg 2300 2000)
                (gm06Alg511CopyRowProg 2301 2001)))))))

private theorem body_frame {w : ℕ} {s t : State} {u : ℕ}
    (he : Exec w gm06Alg511BinaryMultiplyBody s t u) :
    Keeps [20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2235]
      [2000, 2001, 2002, 2302] s t := by
  have hr : gm06Alg511BinaryMultiplyBody.writtenRegs ⊆
      ([20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2235] : List ℕ).toFinset := by decide
  have ha : gm06Alg511BinaryMultiplyBody.writtenArrs ⊆
      ([2000, 2001, 2002, 2302] : List ℕ).toFinset := by decide
  exact ⟨fun r hn => he.regs_eq_of_not_mem_writtenRegs (fun hm => hn (List.mem_toFinset.mp (hr hm))),
    fun a hn => he.arrs_eq_of_not_mem_writtenArrs (fun hm => hn (List.mem_toFinset.mp (ha hm)))⟩

/-- One actual scan column adds the current bit's contribution,
retains both source rows and advances the accumulator width bound. -/
theorem gm06Alg511BinaryMultiplyBody_exec {w : ℕ} (a b acc : List ℕ) (i : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : a.length + b.length + 1 < 2 ^ w)
    (hi : i < a.length) (haccLen : acc.length ≤ i + b.length)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) (haccBits : ∀ d ∈ acc, d < 2)
    (hA : s.arrs 2300 = a) (hB : s.arrs 2301 = b) (hAcc : s.arrs 2302 = acc)
    (hindex : s.regs 2233 = i) :
    ∃ t u out, Exec w gm06Alg511BinaryMultiplyBody s t u ∧
      u ≤ 110 + 100 * (a.length + b.length + 1) ∧
      Keeps [20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2235]
        [2000, 2001, 2002, 2302] s t ∧
      t.arrs 2302 = out ∧ out.length ≤ i + 1 + b.length ∧ (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinaryValue out = gm06Alg511BinaryValue acc +
        (2 ^ i * a[i]) * gm06Alg511BinaryValue b := by
  have hib : i < 2 ^ w := by omega
  have ha : a[i] < 2 := habits _ (List.getElem_mem hi)
  let s₁ := s.setReg 2235 a[i]
  have hread : (Expr.read 2300 (.reg 2233)).eval w s = some a[i] := by
    simpa only [hA] using Crossing.eval_read (a := 2300) (Crossing.eval_reg hindex hib)
      (by simpa only [hA] using hi) (by simpa only [hA] using ha.trans_le (show 2 ≤ 2 ^ w by omega))
  have he₁ : Exec w (.assign 2235 (.read 2300 (.reg 2233))) s s₁ 3 := .assign hread
  have hreg : s₁.regs 2235 = a[i] := by simp [s₁]
  have hev : (Expr.reg 2235).eval w s₁ = some a[i] := Crossing.eval_reg hreg (ha.trans_le (by omega))
  by_cases hz : a[i] = 0
  · have he₂ : Exec w (.ite (.reg 2235) gm06Alg511BinaryMultiplyPassProg .skip) s₁ s₁ 2 := by
      exact .ite_false (by simpa only [hz] using hev) (.skip _)
    have he : Exec w gm06Alg511BinaryMultiplyBody s s₁ 5 := .seq he₁ he₂
    refine ⟨s₁, 5, acc, he, by omega, body_frame he, ?_, by omega, haccBits, ?_⟩
    · simpa only [s₁, State.setReg_arrs] using hAcc
    · simp only [hz, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
  · have hone : a[i] = 1 := by omega
    obtain ⟨t, u, out, he₂, ht₂, hk₂, hout, hlen, hbits, hval⟩ :=
      gm06Alg511BinaryMultiplyPassProg_exec (w := w) b acc i s₁ hw (by omega) haccLen
        hbbits haccBits hB hAcc (by simpa only [s₁, State.setReg_regs_ne _ _ (by decide : (2233 : ℕ) ≠ 2235)] using hindex)
    have he : Exec w gm06Alg511BinaryMultiplyBody s t (3 + (1 + u)) :=
      .seq he₁ (.ite_true hev hz he₂)
    refine ⟨t, _, out, he, by omega, body_frame he, hout, by omega, hbits, ?_⟩
    simpa only [hone, Nat.mul_one] using hval

private theorem multiply_frame {w : ℕ} {s t : State} {u : ℕ}
    (he : Exec w gm06Alg511BinaryMultiplyProg s t u) :
    Keeps [20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2233, 2235]
      [2000, 2001, 2002, 2300, 2301, 2302] s t := by
  have hr : gm06Alg511BinaryMultiplyProg.writtenRegs ⊆
      ([20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2233, 2235] : List ℕ).toFinset := by decide
  have ha : gm06Alg511BinaryMultiplyProg.writtenArrs ⊆
      ([2000, 2001, 2002, 2300, 2301, 2302] : List ℕ).toFinset := by decide
  exact ⟨fun r hn => he.regs_eq_of_not_mem_writtenRegs (fun hm => hn (List.mem_toFinset.mp (hr hm))),
    fun a hn => he.arrs_eq_of_not_mem_writtenArrs (fun hm => hn (List.mem_toFinset.mp (ha hm)))⟩

/-- The full multiplication scan computes the exact product,
returns a binary row of at most the sum of the input widths, and
restores both operand arrays. Its time is quadratic in digit count,
with no assumption that either represented magnitude fits a word. -/
theorem gm06Alg511BinaryMultiplyProg_exec {w : ℕ} (a b : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : a.length + b.length + 1 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2)
    (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b) :
    ∃ t u out, Exec w gm06Alg511BinaryMultiplyProg s t u ∧
      u ≤ 500 * (a.length + b.length + 1) ^ 2 ∧
      Keeps [20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2233, 2235]
        [2002, 2300, 2301, 2302] s t ∧
      t.arrs 2002 = out ∧ out.length ≤ a.length + b.length ∧ (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinaryValue out = gm06Alg511BinaryValue a * gm06Alg511BinaryValue b := by
  have ha : a.length < 2 ^ w := by omega
  have hb : b.length < 2 ^ w := by omega
  have aw : ∀ d ∈ a, d < 2 ^ w := fun d hd => (habits d hd).trans_le (by omega)
  have bw : ∀ d ∈ b, d < 2 ^ w := fun d hd => (hbbits d hd).trans_le (by omega)
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hA₁⟩ := gm06Alg511CopyRowProg_exec 2000 2300 (by decide) a s
    (by omega) ha aw hA
  obtain ⟨s₂, u₂, he₂, ht₂, hk₂, hB₂⟩ := gm06Alg511CopyRowProg_exec 2001 2301 (by decide) b s₁
    (by omega) hb bw ((hk₁.2 2001 (by decide)).trans hB)
  let s₃ := s₂.setArr 2302 []
  let s₄ := s₃.setReg 2233 0
  have he₃ : Exec w (.alloc 2302 (.const 0)) s₂ s₃ 1 := .alloc (Crossing.eval_const (Nat.two_pow_pos w))
  have he₄ : Exec w (.assign 2233 (.const 0)) s₃ s₄ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have hsourceA : s₄.arrs 2300 = a := by
    simpa only [s₄, s₃, State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide : (2300 : ℕ) ≠ 2302)] using
      (hk₂.2 2300 (by decide)).trans hA₁
  have hsourceB : s₄.arrs 2301 = b := by
    simpa only [s₄, s₃, State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide : (2301 : ℕ) ≠ 2302)] using hB₂
  let I : ℕ → State → Prop := fun i st => st.regs 2233 = i ∧ st.arrs 2300 = a ∧ st.arrs 2301 = b ∧
    ∃ acc, st.arrs 2302 = acc ∧ acc.length ≤ i + b.length ∧ (∀ d ∈ acc, d < 2) ∧
      gm06Alg511BinaryValue acc = gm06Alg511BinaryValue (a.take i) * gm06Alg511BinaryValue b
  have hI : I 0 s₄ := by
    refine ⟨by simp [s₄], hsourceA, hsourceB, [], by simp [s₄, s₃], by simp, by simp, ?_⟩
    simp [gm06Alg511BinaryValue]
  obtain ⟨st, ut, heLoop, htLoop, hEnd⟩ := Crossing.forUp_exec' I a.length
    (110 + 100 * (a.length + b.length + 1)) (r_i := 2233) (hi := .len 2300)
    (body := gm06Alg511BinaryMultiplyBody) (by omega) ha
    (fun i hi st h => ⟨h.1, Crossing.eval_len h.2.1 ha⟩)
    (by
      intro i hi st h
      obtain ⟨hidx, hASt, hBSt, acc, hAccSt, haccLen, haccBits, haccVal⟩ := h
      obtain ⟨su, tu, out, heu, htu, hku, hout, hlen, hbits, hval⟩ :=
        gm06Alg511BinaryMultiplyBody_exec a b acc i st hw hsize hi haccLen habits hbbits haccBits hASt hBSt hAccSt hidx
      refine ⟨su, tu, heu, htu, ?_, (hku.1 2233 (by decide)).trans hidx⟩
      refine ⟨by simp, ?_, ?_, out, ?_, hlen, hbits, ?_⟩
      · simpa only [State.setReg_arrs] using (hku.2 2300 (by decide)).trans hASt
      · simpa only [State.setReg_arrs] using (hku.2 2301 (by decide)).trans hBSt
      · simpa only [State.setReg_arrs] using hout
      · rw [hval, haccVal, gm06Alg511BinaryValue_take_succ a i hi, Nat.add_mul]) s₄ hI
  obtain ⟨_, hAEnd, hBEnd, out, hout, houtLen, houtBits, houtVal⟩ := hEnd
  have houtFit : out.length < 2 ^ w := by omega
  have houtWords : ∀ d ∈ out, d < 2 ^ w := fun d hd => (houtBits d hd).trans_le (by omega)
  obtain ⟨s₅, u₅, he₅, ht₅, hk₅, hprod⟩ := gm06Alg511CopyRowProg_exec 2302 2002 (by decide) out st
    (by omega) houtFit houtWords hout
  obtain ⟨s₆, u₆, he₆, ht₆, hk₆, hrestoreA⟩ := gm06Alg511CopyRowProg_exec 2300 2000 (by decide) a s₅
    (by omega) ha aw ((hk₅.2 2300 (by decide)).trans hAEnd)
  obtain ⟨t, u₇, he₇, ht₇, hk₇, hrestoreB⟩ := gm06Alg511CopyRowProg_exec 2301 2001 (by decide) b s₆
    (by omega) hb bw ((hk₆.2 2301 (by decide)).trans ((hk₅.2 2301 (by decide)).trans hBEnd))
  have he : Exec w gm06Alg511BinaryMultiplyProg s t
      (u₁ + (u₂ + (1 + (2 + (ut + (u₅ + (u₆ + u₇))))))) :=
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq heLoop (.seq he₅ (.seq he₆ he₇))))))
  have hk := multiply_frame he
  refine ⟨t, _, out, he, ?_, ?_, (hk₇.2 2002 (by decide)).trans ((hk₆.2 2002 (by decide)).trans hprod),
    houtLen, houtBits, ?_⟩
  · simp only [Expr.cost] at htLoop
    have hbound : a.length * (117 + 100 * (a.length + b.length + 1)) ≤
        (a.length + b.length + 1) * (117 + 100 * (a.length + b.length + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith only [ht₁, ht₂, htLoop, ht₅, ht₆, ht₇, houtLen, hbound]
  · refine ⟨hk.1, fun ar hn => ?_⟩
    by_cases h0 : ar = 2000
    · subst ar
      exact ((hk₇.2 2000 (by decide)).trans hrestoreA).trans hA.symm
    by_cases h1 : ar = 2001
    · subst ar
      exact hrestoreB.trans hB.symm
    exact hk.2 ar (by simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using
      (show ar ≠ 2000 ∧ ar ≠ 2001 ∧ ar ≠ 2002 ∧ ar ≠ 2300 ∧ ar ≠ 2301 ∧ ar ≠ 2302 from
        ⟨h0, h1, by simpa using hn⟩))
  · simpa only [List.take_length] using houtVal

/-- Multiplication has quadratic time in total supplied bit count
with logarithmic machine words. The complete product stays in a
binary digit array, so the theorem has no numeric magnitude premise. -/
theorem gm06Alg511BinaryMultiply_computes :
    ComputesRelInTime
      (fun x : List Bool × List Bool => x.1.length + x.2.length + 1)
      (fun x s => s.arrs 2000 = x.1.map Bool.toNat ∧ s.arrs 2001 = x.2.map Bool.toNat)
      (fun x s => gm06Alg511BinaryValue (s.arrs 2002) =
          gm06Alg511BinaryValue (x.1.map Bool.toNat) * gm06Alg511BinaryValue (x.2.map Bool.toNat) ∧
        (∀ d ∈ s.arrs 2002, d < 2) ∧ (s.arrs 2002).length ≤ x.1.length + x.2.length)
      gm06Alg511BinaryMultiplyProg (fun n => (n + 1) ^ 2) := by
  refine ⟨500, 2, by decide, by decide, ?_⟩
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
  have hsize : a.length + b.length + 1 < 2 ^ w :=
    lt_two_pow_wordSize_of_le (c := 2) (n := size) (by decide) (by simp [a, b, size])
  have bits (xs : List Bool) : ∀ d ∈ xs.map Bool.toNat, d < 2 := by
    intro d hd
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    cases q <;> decide
  obtain ⟨t, u, out, he, ht, _, hout, hlen, hbits, hval⟩ :=
    gm06Alg511BinaryMultiplyProg_exec a b s hw hsize (bits x.1) (bits x.2) hs.1 hs.2
  refine ⟨t, u, he, ?_, ?_, ?_, ?_⟩
  · have heq : a.length + b.length + 1 = size := by simp [a, b, size]
    rw [heq] at ht
    have hp : size ^ 2 ≤ (size + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact ht.trans (Nat.mul_le_mul_left _ hp)
  · simpa only [hout] using hval
  · simpa only [hout] using hbits
  · simpa only [hout, a, b, List.length_map] using hlen

end GraphMinor.Compute
