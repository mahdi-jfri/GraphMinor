module

public import GraphMinor.Compute.GM06Alg511BinaryRemainderPass
import Mathlib.Tactic

/-!
# Binary remainder in quadratic time

Scan the numerator from its highest supplied bit to its lowest.
The retained binary row is the remainder of the scanned prefix.
The proved column program doubles that remainder, inserts the next
bit and reduces it with one subtraction. Its numeric value stays
below the positive divisor. Its row width grows by at most one per
column, even when supplied rows have leading zeros. This proves a
quadratic bound in supplied digit count with logarithmic words.
It supplies the divisibility test for VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

private theorem high_prefix_step (a : List ℕ) (i : ℕ) (hi : i < a.length) :
    gm06Alg511BinaryValue (a.drop (a.length - (i + 1))) =
      a[a.length - (i + 1)] + 2 * gm06Alg511BinaryValue (a.drop (a.length - i)) := by
  have hj : a.length - (i + 1) < a.length := by omega
  rw [List.drop_eq_getElem_cons hj, gm06Alg511BinaryValue,
    show a.length - (i + 1) + 1 = a.length - i by omega]

private theorem column_mod (d r b : ℕ) :
    (d + 2 * (r % b)) % b = (d + 2 * r) % b := by
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- Read the next high-to-low numerator bit and update the binary
partial remainder through the verified column program. -/
def gm06Alg511BinaryRemainderBody : Cmd :=
  .seq (.assign 2531 (.read 2500 (.op .sub (.len 2500) (.op .add (.reg 2530) (.const 1)))))
    gm06Alg511BinaryRemainderPassProg

/-- Return the remainder in array 2002, retaining both supplied
operand rows. The divisor must represent a positive natural number. -/
def gm06Alg511BinaryRemainderProg : Cmd :=
  .seq (gm06Alg511CopyRowProg 2000 2500)
    (.seq (gm06Alg511CopyRowProg 2001 2501)
      (.seq (.alloc 2502 (.const 0))
        (.seq (.assign 2530 (.const 0))
          (.seq (forUp 2530 (.len 2500) gm06Alg511BinaryRemainderBody)
            (.seq (gm06Alg511CopyRowProg 2502 2002)
              (.seq (gm06Alg511CopyRowProg 2500 2000)
                (gm06Alg511CopyRowProg 2501 2001)))))))

private theorem remainder_frame {w : ℕ} {s t : State} {u : ℕ}
    (he : Exec w gm06Alg511BinaryRemainderProg s t u) :
    Keeps [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2530, 2531]
      [2000, 2001, 2002, 2003, 2004, 2005, 2301, 2500, 2501, 2502] s t := by
  have hr : gm06Alg511BinaryRemainderProg.writtenRegs ⊆
      ([0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2530, 2531] : List ℕ).toFinset := by decide
  have ha : gm06Alg511BinaryRemainderProg.writtenArrs ⊆
      ([2000, 2001, 2002, 2003, 2004, 2005, 2301, 2500, 2501, 2502] : List ℕ).toFinset := by decide
  exact ⟨fun r hn => he.regs_eq_of_not_mem_writtenRegs (fun hm => hn (List.mem_toFinset.mp (hr hm))),
    fun a hn => he.arrs_eq_of_not_mem_writtenArrs (fun hm => hn (List.mem_toFinset.mp (ha hm)))⟩

/-- The actual binary long-division scan computes the exact
remainder in quadratic digit-count time and restores both operands.
Its word bounds concern only lengths, positions, bits and carries. -/
theorem gm06Alg511BinaryRemainderProg_exec {w : ℕ} (a b : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : a.length + b.length + 2 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2)
    (hbpos : 0 < gm06Alg511BinaryValue b) (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b) :
    ∃ t u out, Exec w gm06Alg511BinaryRemainderProg s t u ∧
      u ≤ 2000 * (a.length + b.length + 1) ^ 2 ∧
      Keeps [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2530, 2531]
        [2002, 2003, 2004, 2005, 2301, 2500, 2501, 2502] s t ∧
      t.arrs 2002 = out ∧ out.length ≤ a.length + b.length ∧ (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinaryValue out = gm06Alg511BinaryValue a % gm06Alg511BinaryValue b := by
  have haFit : a.length < 2 ^ w := by omega
  have hbFit : b.length < 2 ^ w := by omega
  have aw : ∀ d ∈ a, d < 2 ^ w := fun d hd => (habits d hd).trans_le (by omega)
  have bw : ∀ d ∈ b, d < 2 ^ w := fun d hd => (hbbits d hd).trans_le (by omega)
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hA₁⟩ := gm06Alg511CopyRowProg_exec 2000 2500 (by decide) a s
    (by omega) haFit aw hA
  obtain ⟨s₂, u₂, he₂, ht₂, hk₂, hB₂⟩ := gm06Alg511CopyRowProg_exec 2001 2501 (by decide) b s₁
    (by omega) hbFit bw ((hk₁.2 2001 (by decide)).trans hB)
  let s₃ := s₂.setArr 2502 []
  let s₄ := s₃.setReg 2530 0
  have he₃ : Exec w (.alloc 2502 (.const 0)) s₂ s₃ 1 := .alloc (Crossing.eval_const (Nat.two_pow_pos w))
  have he₄ : Exec w (.assign 2530 (.const 0)) s₃ s₄ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have hsourceA : s₄.arrs 2500 = a := by
    simpa only [s₄, s₃, State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide : (2500 : ℕ) ≠ 2502)] using
      (hk₂.2 2500 (by decide)).trans hA₁
  have hsourceB : s₄.arrs 2501 = b := by
    simpa only [s₄, s₃, State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide : (2501 : ℕ) ≠ 2502)] using hB₂
  let I : ℕ → State → Prop := fun i st => st.regs 2530 = i ∧ st.arrs 2500 = a ∧ st.arrs 2501 = b ∧
    ∃ acc, st.arrs 2502 = acc ∧ acc.length ≤ i + b.length ∧ (∀ d ∈ acc, d < 2) ∧
      gm06Alg511BinaryValue acc = gm06Alg511BinaryValue (a.drop (a.length - i)) % gm06Alg511BinaryValue b
  have hI : I 0 s₄ := by
    refine ⟨by simp [s₄], hsourceA, hsourceB, [], by simp [s₄, s₃], by simp, by simp, ?_⟩
    simp [gm06Alg511BinaryValue]
  obtain ⟨st, ut, heLoop, htLoop, hEnd⟩ := Crossing.forUp_exec' I a.length
    (410 + 400 * (a.length + 2 * b.length + 1)) (r_i := 2530) (hi := .len 2500)
    (body := gm06Alg511BinaryRemainderBody) (by omega) haFit
    (fun i hi st h => ⟨h.1, Crossing.eval_len h.2.1 haFit⟩)
    (by
      intro i hi st h
      obtain ⟨hidx, hASt, hBSt, acc, hAcc, haccLen, haccBits, haccVal⟩ := h
      let j := a.length - (i + 1)
      have hj : j < a.length := by dsimp only [j]; omega
      have hd : a[j] < 2 := habits _ (List.getElem_mem hj)
      have hidxExpr : (Expr.op .sub (.len 2500) (.op .add (.reg 2530) (.const 1))).eval w st = some j :=
        Crossing.eval_sub (Crossing.eval_len hASt haFit)
          (Crossing.eval_add (Crossing.eval_reg hidx (hi.trans haFit)) (Crossing.eval_const (by omega)) (by omega))
      have hread : (Expr.read 2500 (.op .sub (.len 2500) (.op .add (.reg 2530) (.const 1)))).eval w st = some a[j] := by
        simpa only [hASt] using Crossing.eval_read (a := 2500) hidxExpr
          (by simpa only [hASt] using hj) (by simpa only [hASt] using hd.trans_le (show 2 ≤ 2 ^ w by omega))
      let su := st.setReg 2531 a[j]
      have heRead : Exec w (.assign 2531 (.read 2500 (.op .sub (.len 2500) (.op .add (.reg 2530) (.const 1))))) st su 7 :=
        .assign hread
      obtain ⟨sv, v, out, hev, htv, hkv, hout, hlen, hbits, hval⟩ :=
        gm06Alg511BinaryRemainderPassProg_exec (w := w) b acc a[j] su hw (by omega) hbbits haccBits hd hbpos
          (by rw [haccVal]; exact Nat.mod_lt _ hbpos) hBSt hAcc (by simp [su])
      refine ⟨sv, 7 + v, .seq heRead hev, by omega, ?_, ?_⟩
      · refine ⟨by simp, ?_, ?_, out, by simpa only [State.setReg_arrs] using hout, by omega, hbits, ?_⟩
        · simpa only [State.setReg_arrs, su] using (hkv.2 2500 (by decide)).trans hASt
        · simpa only [State.setReg_arrs, su] using (hkv.2 2501 (by decide)).trans hBSt
        · rw [hval, haccVal, column_mod, high_prefix_step a i hi]
      · simpa only [su, State.setReg_regs_ne _ _ (by decide : (2530 : ℕ) ≠ 2531)] using
          (hkv.1 2530 (by decide)).trans hidx) s₄ hI
  obtain ⟨_, hAEnd, hBEnd, out, hout, houtLen, houtBits, houtVal⟩ := hEnd
  have houtFit : out.length < 2 ^ w := by omega
  obtain ⟨s₅, u₅, he₅, ht₅, hk₅, hprod⟩ := gm06Alg511CopyRowProg_exec 2502 2002 (by decide) out st
    (by omega) houtFit (fun d hd => (houtBits d hd).trans_le (by omega)) hout
  obtain ⟨s₆, u₆, he₆, ht₆, hk₆, hrestoreA⟩ := gm06Alg511CopyRowProg_exec 2500 2000 (by decide) a s₅
    (by omega) haFit aw ((hk₅.2 2500 (by decide)).trans hAEnd)
  obtain ⟨t, u₇, he₇, ht₇, hk₇, hrestoreB⟩ := gm06Alg511CopyRowProg_exec 2501 2001 (by decide) b s₆
    (by omega) hbFit bw ((hk₆.2 2501 (by decide)).trans ((hk₅.2 2501 (by decide)).trans hBEnd))
  have he : Exec w gm06Alg511BinaryRemainderProg s t
      (u₁ + (u₂ + (1 + (2 + (ut + (u₅ + (u₆ + u₇))))))) :=
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq heLoop (.seq he₅ (.seq he₆ he₇))))))
  have hk := remainder_frame he
  refine ⟨t, _, out, he, ?_, ⟨hk.1, ?_⟩,
    (hk₇.2 2002 (by decide)).trans ((hk₆.2 2002 (by decide)).trans hprod), houtLen, houtBits, ?_⟩
  · simp only [Expr.cost] at htLoop
    have hbound : a.length * (417 + 400 * (a.length + 2 * b.length + 1)) ≤
        (a.length + b.length) * (817 + 800 * (a.length + b.length)) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith only [ht₁, ht₂, htLoop, ht₅, ht₆, ht₇, houtLen, hbound]
  · intro ar har
    by_cases h0 : ar = 2000
    · subst ar; exact ((hk₇.2 2000 (by decide)).trans hrestoreA).trans hA.symm
    by_cases h1 : ar = 2001
    · subst ar; exact hrestoreB.trans hB.symm
    exact hk.2 ar (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at har ⊢; tauto)
  · simpa only [Nat.sub_self, List.drop_zero] using houtVal

/-- Remainder has quadratic time in total supplied bit count and
logarithmic machine words, for any positive supplied divisor. -/
theorem gm06Alg511BinaryRemainder_computes :
    ComputesRelInTime
      (fun x : List Bool × List Bool => x.1.length + x.2.length + 2)
      (fun x s => s.arrs 2000 = x.1.map Bool.toNat ∧ s.arrs 2001 = x.2.map Bool.toNat ∧
        0 < gm06Alg511BinaryValue (x.2.map Bool.toNat))
      (fun x s => gm06Alg511BinaryValue (s.arrs 2002) =
          gm06Alg511BinaryValue (x.1.map Bool.toNat) % gm06Alg511BinaryValue (x.2.map Bool.toNat) ∧
        (∀ d ∈ s.arrs 2002, d < 2) ∧ (s.arrs 2002).length ≤ x.1.length + x.2.length)
      gm06Alg511BinaryRemainderProg (fun n => (n + 1) ^ 2) := by
  refine ⟨2000, 2, by decide, by decide, ?_⟩
  intro x s hs
  let a := x.1.map Bool.toNat
  let b := x.2.map Bool.toNat
  let size := x.1.length + x.2.length + 2
  let w := wordSize 2 size
  have hw : 3 < 2 ^ w := by
    have hp := pow_lt_two_pow_wordSize (c := 2) (by decide) size
    have hb : 3 ≤ size + 2 := by dsimp only [size]; omega
    have hh : 3 < (size + 2) ^ 2 := by nlinarith only [hb]
    exact hh.trans hp
  have hsize : a.length + b.length + 2 < 2 ^ w :=
    lt_two_pow_wordSize_of_le (c := 2) (n := size) (by decide) (by simp [a, b, size])
  have bits (xs : List Bool) : ∀ d ∈ xs.map Bool.toNat, d < 2 := by
    intro d hd
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    cases q <;> decide
  obtain ⟨t, u, out, he, ht, _, hout, hlen, hbits, hval⟩ :=
    gm06Alg511BinaryRemainderProg_exec a b s hw hsize (bits x.1) (bits x.2) hs.2.2 hs.1 hs.2.1
  refine ⟨t, u, he, ?_, ?_, ?_, ?_⟩
  · have heq : a.length + b.length + 1 ≤ size + 1 := by simp [a, b, size]
    exact ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left heq 2))
  · simpa only [hout] using hval
  · simpa only [hout] using hbits
  · simpa only [hout, a, b, List.length_map] using hlen

end GraphMinor.Compute
