module

public import GraphMinor.Compute.GM06Alg511BinaryTurnColumn
public import GraphMinor.Compute.GM06Alg511TurnWords
import GraphMinor.Compute.GM06RefreshContractedMasks
import Mathlib.Tactic

/-!
# The complete binary turn sum along a stored path

Scan the first linkage path's ordinary darts and add each supplied
binary edge turn in its traversal direction. The retained row is
the exact sum over the scanned prefix. Its magnitude width grows
by at most one per dart beyond the supplied turn-code length.
This gives a quadratic bound in path length and supplied bits,
with no word bound on any edge-turn magnitude or on their sum.
The resulting integer is the same oriented turn sum used by the
geometric winding proof for VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The oriented integer contribution of a dart in binary turn data.
This is a mathematical interpretation, not a machine word. -/
def gm06Alg511BinaryDartTurn (turns : List GM06Alg511BinaryInteger) (dart : ℕ) : ℤ :=
  let value := (turns.map GM06Alg511BinaryInteger.value).getD (dart / 2) 0
  if dart % 2 = 0 then value else -value

/-- At a valid dart the interpreted value is exactly the supplied
edge's integer, with precisely its traversal sign. -/
theorem gm06Alg511BinaryDartTurn_eq_getElem (turns : List GM06Alg511BinaryInteger) (dart : ℕ)
    (hd : dart < 2 * turns.length) :
    gm06Alg511BinaryDartTurn turns dart =
      if dart % 2 = 0 then (turns[dart / 2]'(by omega)).value else -(turns[dart / 2]'(by omega)).value := by
  have hi : dart / 2 < turns.length := by omega
  simp only [gm06Alg511BinaryDartTurn, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

/-- Binary turn data has the same oriented integer interpretation
as the turn list used in the established geometric winding lemmas. -/
theorem gm06Alg511BinaryDartTurn_eq_old (turns : List GM06Alg511BinaryInteger) (dart : ℕ)
    (hd : dart < 2 * turns.length) :
    gm06Alg511BinaryDartTurn turns dart =
      gm06Alg511DartTurn (gm06Alg511TurnWords (turns.map GM06Alg511BinaryInteger.value)) dart := by
  have hi : dart / 2 < (turns.map GM06Alg511BinaryInteger.value).length := by simp only [List.length_map]; omega
  have hm : dart % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hz : dart % 2 = 0
  · have he : dart = 2 * (dart / 2) := by omega
    rw [he, gm06Alg511DartTurn_forward _ _ hi]
    unfold gm06Alg511BinaryDartTurn
    simp only [show 2 * (dart / 2) % 2 = 0 by omega, ite_true,
      show 2 * (dart / 2) / 2 = dart / 2 by omega]
  · have he : dart = 2 * (dart / 2) + 1 := by omega
    rw [he, gm06Alg511DartTurn_reverse _ _ hi]
    unfold gm06Alg511BinaryDartTurn
    simp only [show (2 * (dart / 2) + 1) % 2 = 1 by omega, (by decide : ¬ (1 : ℕ) = 0), ite_false,
      show (2 * (dart / 2) + 1) / 2 = dart / 2 by omega]

/-- Every bit, sign and length prefix in the supplied turn code
is bounded by that code's length. No magnitude appears in it. -/
theorem gm06Alg511BinaryTurnCode_words (turns : List GM06Alg511BinaryInteger) :
    ∀ d ∈ gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words),
      d ≤ (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length := by
  let rows := turns.map GM06Alg511BinaryInteger.words
  intro d hd
  change d ≤ (gm06EncodeRows rows).length
  change d ∈ rows.length :: gm06EncodeRowsPayload rows at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · have hh := gm06EncodeRows_length rows
    omega
  · obtain ⟨row, hrow, hd⟩ := List.mem_flatMap.mp hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact gm06Alg511_encoded_row_length_le hrow
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hrow
      have hb := z.words_lt_two d hd
      have hnonempty : 1 ≤ (gm06EncodeRows rows).length := by simp [gm06EncodeRows]
      omega

/-- Read the next stored path dart and add its supplied oriented
binary turn through the exact column program. -/
def gm06Alg511BinaryTurnSumBody : Cmd :=
  .seq (.assign 2911 (.read 12 (.reg 2910))) gm06Alg511BinaryTurnColumnProg

/-- Compute the signed binary turn sum in array 2902, reading
only the supplied binary turn code 2900 and path darts 12. -/
def gm06Alg511BinaryTurnSumProg : Cmd :=
  .seq (.alloc 2902 (.const 1))
    (.seq (.assign 2910 (.const 0))
      (forUp 2910 (.len 12) gm06Alg511BinaryTurnSumBody))

/-- The actual full turn scan has the exact oriented integer sum,
binary output and quadratic bit/path-count time, retaining the
original supplied turn code and ordinary path list. -/
theorem gm06Alg511BinaryTurnSumProg_exec {w : ℕ} (turns : List GM06Alg511BinaryInteger)
    (darts : List ℕ) (s : State) (hw : 3 < 2 ^ w)
    (hsize : darts.length + 2 * (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 3 < 2 ^ w)
    (hdarts : ∀ d ∈ darts, d < 2 * turns.length)
    (hTurns : s.arrs 2900 = gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)) (hPath : s.arrs 12 = darts) :
    ∃ t u out sign, Exec w gm06Alg511BinaryTurnSumProg s t u ∧
      u ≤ 2000 * (darts.length + (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 1) ^ 2 ∧
      Keeps [0, 7, 8, 9, 11, 20, 31, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2400, 2401, 2402, 2404, 2910, 2911]
        [2000, 2001, 2002, 2003, 2004, 2005, 2901, 2902] s t ∧
      t.arrs 2902 = sign :: out ∧ sign < 2 ∧
      out.length ≤ darts.length + (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length ∧
      (∀ d ∈ out, d < 2) ∧ gm06Alg511BinaryRowValue (sign :: out) = (darts.map (gm06Alg511BinaryDartTurn turns)).sum := by
  let code := gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)
  change darts.length + 2 * code.length + 3 < 2 ^ w at hsize
  have hcount : turns.length ≤ code.length := by
    have hh := gm06EncodeRows_length (turns.map GM06Alg511BinaryInteger.words)
    simp only [List.length_map] at hh
    dsimp only [code]
    omega
  have hcodeFit : code.length < 2 ^ w := by omega
  have hpathFit : darts.length < 2 ^ w := by omega
  have hwords : ∀ d ∈ code, d < 2 ^ w := fun d hd => (gm06Alg511BinaryTurnCode_words turns d hd).trans_lt hcodeFit
  let s₁ := s.setArr 2902 [0]
  let s₂ := s₁.setReg 2910 0
  have he₁ : Exec w (.alloc 2902 (.const 1)) s s₁ 2 := .alloc (Crossing.eval_const (by omega))
  have he₂ : Exec w (.assign 2910 (.const 0)) s₁ s₂ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  let R := [0, 7, 8, 9, 11, 20, 31, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2400, 2401, 2402, 2404, 2910, 2911]
  let A := [2000, 2001, 2002, 2003, 2004, 2005, 2901, 2902]
  let I : ℕ → State → Prop := fun i st => st.regs 2910 = i ∧ st.arrs 2900 = code ∧ st.arrs 12 = darts ∧
    ∃ acc sign, st.arrs 2902 = sign :: acc ∧ sign < 2 ∧ acc.length ≤ i + code.length ∧
      (∀ d ∈ acc, d < 2) ∧ gm06Alg511BinaryRowValue (sign :: acc) = ((darts.take i).map (gm06Alg511BinaryDartTurn turns)).sum ∧ Keeps R A s st
  have hI : I 0 s₂ := by
    refine ⟨by simp [s₂], by simpa only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide : (2900 : ℕ) ≠ 2902)] using hTurns,
      by simpa only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide : (12 : ℕ) ≠ 2902)] using hPath,
      [], 0, by simp [s₂, s₁], by decide, by simp, by simp, rfl, ?_⟩
    exact ((Keeps.refl _ _ s).setArr (by simp [A]) [0]).setReg (by simp [R]) 0
  obtain ⟨t, ut, heLoop, htLoop, hEnd⟩ := Crossing.forUp_exec' (w := w) I darts.length
    (500 + 800 * (darts.length + code.length + 1)) (r_i := 2910) (hi := .len 12)
    (body := gm06Alg511BinaryTurnSumBody) (by omega) hpathFit
    (fun i hi st h => ⟨h.1, Crossing.eval_len h.2.2.1 hpathFit⟩)
    (by
      intro i hi st h
      obtain ⟨hidx, hcode, hpath, acc, sign, hacc, hsign, hlen, hbits, hval, hkeep⟩ := h
      let dart := darts[i]
      have hd : dart < 2 * turns.length := hdarts dart (List.getElem_mem hi)
      have hdFit : dart < 2 ^ w := by omega
      have hread : (Expr.read 12 (.reg 2910)).eval w st = some dart := by
        exact (Crossing.eval_read (a := 12) (Crossing.eval_reg hidx (hi.trans hpathFit))
          (by simpa only [hpath] using hi) (by simpa only [hpath] using hdFit)).trans (by simp [hpath, dart])
      let su := st.setReg 2911 dart
      have heRead : Exec w (.assign 2911 (.read 12 (.reg 2910))) st su 3 := .assign hread
      obtain ⟨sv, v, out, sign', hev, htv, hkv, hout, hsign', hlen', hbits', hval'⟩ :=
        gm06Alg511BinaryTurnColumnProg_exec turns dart sign acc su hw hdFit hd (by change acc.length + code.length + 2 < 2 ^ w; omega) hwords hsign hbits
          hcode hacc (by simp [su])
      have hindex : dart / 2 < turns.length := by omega
      let z := turns[dart / 2]
      have hzrow : z.words ∈ turns.map GM06Alg511BinaryInteger.words := List.mem_map.mpr ⟨turns[dart / 2], List.getElem_mem hindex, rfl⟩
      change v ≤ 450 + 17 * (dart / 2) + 22 * z.words.length + 350 * (acc.length + z.digits.length + 1) at htv
      change out.length ≤ max acc.length z.digits.length + 1 at hlen'
      have hzLen : z.words.length ≤ code.length := gm06Alg511_encoded_row_length_le hzrow
      have hzDigits : z.digits.length ≤ code.length := by rw [GM06Alg511BinaryInteger.words_length] at hzLen; omega
      have hkeep' : Keeps R A s sv := (hkeep.setReg (show 2911 ∈ R by simp [R]) dart).trans hkv (by simp [R]) (by simp [A])
      have hnext := hkeep'.setReg (show 2910 ∈ R by simp [R]) (i + 1)
      refine ⟨sv, 3 + v, .seq heRead hev, by omega, ?_, ?_⟩
      · refine ⟨by simp, ?_, ?_, out, sign', by simpa only [State.setReg_arrs] using hout, hsign', by omega, hbits', ?_, hnext⟩
        · simpa only [State.setReg_arrs, su] using (hkv.2 2900 (by decide)).trans hcode
        · simpa only [State.setReg_arrs, su] using (hkv.2 12 (by decide)).trans hpath
        · rw [hval', hval, List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton, gm06Alg511BinaryDartTurn_eq_getElem turns dart hd]
      · simpa only [su, State.setReg_regs_ne _ _ (by decide : (2910 : ℕ) ≠ 2911)] using (hkv.1 2910 (by decide)).trans hidx) s₂ hI
  obtain ⟨_, _, _, out, sign, hout, hsign, hlen, hbits, hval, hkeep⟩ := hEnd
  have he : Exec w gm06Alg511BinaryTurnSumProg s t (2 + (2 + ut)) := .seq he₁ (.seq he₂ heLoop)
  refine ⟨t, _, out, sign, he, ?_, hkeep, hout, hsign, hlen, hbits, ?_⟩
  · simp only [Expr.cost] at htLoop
    have hbound : darts.length * (507 + 800 * (darts.length + code.length + 1)) ≤
        (darts.length + code.length + 1) * (507 + 800 * (darts.length + code.length + 1)) := Nat.mul_le_mul_right _ (by omega)
    nlinarith only [htLoop, hbound]
  · simpa only [List.take_length] using hval

/-- The complete binary turn scan has quadratic time and logarithmic
words in the supplied code and path lengths. Its input validity
requires only ordinary dart bounds, with no turn magnitude bounds. -/
theorem gm06Alg511BinaryTurnSum_computes :
    ComputesRelInTime
      (fun x : List GM06Alg511BinaryInteger × List ℕ =>
        x.2.length + 2 * (gm06EncodeRows (x.1.map GM06Alg511BinaryInteger.words)).length + 3)
      (fun x s => s.arrs 2900 = gm06EncodeRows (x.1.map GM06Alg511BinaryInteger.words) ∧
        s.arrs 12 = x.2 ∧ ∀ d ∈ x.2, d < 2 * x.1.length)
      (fun x s => ∃ out sign, s.arrs 2902 = sign :: out ∧ sign < 2 ∧
        out.length ≤ x.2.length + (gm06EncodeRows (x.1.map GM06Alg511BinaryInteger.words)).length ∧
        (∀ d ∈ out, d < 2) ∧ gm06Alg511BinaryRowValue (s.arrs 2902) = (x.2.map (gm06Alg511BinaryDartTurn x.1)).sum)
      gm06Alg511BinaryTurnSumProg (fun n => (n + 1) ^ 2) := by
  refine ⟨2000, 2, by decide, by decide, ?_⟩
  intro x s hs
  let size := x.2.length + 2 * (gm06EncodeRows (x.1.map GM06Alg511BinaryInteger.words)).length + 3
  let w := wordSize 2 size
  have hw : 3 < 2 ^ w := by
    have hp := pow_lt_two_pow_wordSize (c := 2) (by decide) size
    have hb : 3 ≤ size + 2 := by dsimp only [size]; omega
    have hh : 3 < (size + 2) ^ 2 := by nlinarith only [hb]
    exact hh.trans hp
  have hsize : x.2.length + 2 * (gm06EncodeRows (x.1.map GM06Alg511BinaryInteger.words)).length + 3 < 2 ^ w :=
    lt_two_pow_wordSize_of_le (c := 2) (n := size) (by decide) (by dsimp only [size]; omega)
  obtain ⟨t, u, out, sign, he, ht, _, hout, hsign, hlen, hbits, hval⟩ :=
    gm06Alg511BinaryTurnSumProg_exec x.1 x.2 s hw hsize hs.2.2 hs.1 hs.2.1
  refine ⟨t, u, he, ?_, out, sign, hout, hsign, hlen, hbits, ?_⟩
  · have hwidth : x.2.length + (gm06EncodeRows (x.1.map GM06Alg511BinaryInteger.words)).length + 1 ≤ size + 1 := by
      dsimp only [size]; omega
    exact ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth 2))
  · simpa only [hout] using hval

end GraphMinor.Compute
