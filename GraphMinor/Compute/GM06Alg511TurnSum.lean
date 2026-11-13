module

public import GraphMinor.Compute.GM06DartMate
public import GraphMinor.Compute.GM06Alg511Input
import Mathlib.Tactic

/-!
# Summing signed turns along a supplied path

For the winding computation in VI (5.11), page 134, list the oriented
edge labels of the path. Store each edge turn as its nonnegative and
nonpositive magnitudes at the two consecutive dart positions. Reading
the dart and its mate gives the positive and negative contributions
in the traversal orientation. Two natural-number accumulators avoid
signed machine words. The loop adds the contributions in path order.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Sum contributions along the first `i` darts of a path. -/
def gm06Alg511TurnPrefix (darts : List ℕ) (f : ℕ → ℕ) (i : ℕ) : ℕ :=
  ((darts.take i).map f).sum

/-- Appending the next dart adds exactly its contribution. -/
theorem gm06Alg511TurnPrefix_succ (darts : List ℕ) (f : ℕ → ℕ)
    {i : ℕ} (hi : i < darts.length) :
    gm06Alg511TurnPrefix darts f (i + 1) =
      gm06Alg511TurnPrefix darts f i + f darts[i] := by
  unfold gm06Alg511TurnPrefix
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Every prefix sum is bounded by the full sum. -/
theorem gm06Alg511TurnPrefix_le (darts : List ℕ) (f : ℕ → ℕ) (i : ℕ) :
    gm06Alg511TurnPrefix darts f i ≤ (darts.map f).sum := by
  have h := congrArg (fun xs : List ℕ => (xs.map f).sum) (List.take_append_drop i darts)
  simp only [List.map_append, List.sum_append] at h
  dsimp only [gm06Alg511TurnPrefix]
  omega

/-- Add the current dart's contribution and its mate's contribution
from array 11 to accumulator registers 21 and 22. -/
def gm06Alg511TurnSumBody : Cmd :=
  .seq (.assign 23 (.read 12 (.reg 20)))
    (.seq gm06DartMateProg
      (.seq (.assign 21 (.op .add (.reg 21) (.read 11 (.reg 23))))
        (.assign 22 (.op .add (.reg 22) (.read 11 (.reg 24))))))

/-- Clear both accumulators and sum all oriented edge contributions
along the path in array 12, using the paired signed words in array 11. -/
def gm06Alg511TurnSumProg : Cmd :=
  .seq (.assign 21 (.const 0))
    (.seq (.assign 22 (.const 0))
      (.seq (.assign 20 (.const 0)) (forUp 20 (.len 12) gm06Alg511TurnSumBody)))

private theorem read_getD {w : ℕ} {s : State} {a : ℕ} {idx : Expr} {j : ℕ}
    (hj : idx.eval w s = some j) (hbound : j < (s.arrs a).length)
    (hword : (s.arrs a).getD j 0 < 2 ^ w) :
    (Expr.read a idx).eval w s = some ((s.arrs a).getD j 0) := by
  have hD : (s.arrs a).getD j 0 = (s.arrs a)[j] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbound, Option.getD_some]
  rw [hD] at hword ⊢
  exact eval_read hj hbound hword

/-- One iteration of the signed-turn sum takes twenty-two steps and
adds the exact two contributions, preserving every array. -/
theorem gm06Alg511TurnSumBody_exec {w m i : ℕ} (words darts : List ℕ)
    (s : State) (hw : 2 < 2 ^ w) (hlen : words.length = 2 * m)
    (hn : 2 * m < 2 ^ w) (hi : i < darts.length) (hiw : i < 2 ^ w)
    (hwords : s.arrs 11 = words) (hpath : s.arrs 12 = darts)
    (hcursor : s.regs 20 = i) (hdart : darts[i] < 2 * m)
    (hpos : s.regs 21 + words.getD darts[i] 0 < 2 ^ w)
    (hneg : s.regs 22 + words.getD (gm06DartMate darts[i]) 0 < 2 ^ w) :
    ∃ s', Exec w gm06Alg511TurnSumBody s s' 22 ∧ s'.arrs = s.arrs ∧
      s'.regs 20 = i ∧
      s'.regs 21 = s.regs 21 + words.getD darts[i] 0 ∧
      s'.regs 22 = s.regs 22 + words.getD (gm06DartMate darts[i]) 0 := by
  let d := darts[i]
  change s.regs 21 + words.getD d 0 < 2 ^ w at hpos
  change s.regs 22 + words.getD (gm06DartMate d) 0 < 2 ^ w at hneg
  have hdw : d < 2 ^ w := hdart.trans hn
  have hmate : gm06DartMate d < 2 * m := gm06DartMate_lt hdart
  have hip : i < (s.arrs 12).length := by rw [hpath]; exact hi
  have heD : (Expr.read 12 (.reg 20)).eval w s = some d := by
    have h := eval_read (a := 12) (eval_reg hcursor hiw)
      hip
      (show (s.arrs 12)[i]'hip < 2 ^ w by simpa only [hpath] using hdw)
    simpa only [hpath] using h
  let s₁ := s.setReg 23 d
  let s₂ := s₁.setReg 24 (gm06DartMate d)
  let s₃ := s₂.setReg 21 (s.regs 21 + words.getD d 0)
  let s₄ := s₃.setReg 22 (s.regs 22 + words.getD (gm06DartMate d) 0)
  have heMate : Exec w gm06DartMateProg s₁ s₂ 9 :=
    gm06DartMateProg_exec s₁ hw hn hdart (by simp [s₁])
  have hrP : (Expr.read 11 (.reg 23)).eval w s₂ = some (words.getD d 0) := by
    simpa only [s₂, s₁, State.setReg_arrs, hwords] using
      (read_getD (a := 11) (s := s₂)
        (eval_reg (by simp [s₂, s₁]) hdw)
        (by simpa [s₂, s₁, hwords, hlen] using hdart)
        (by simpa only [s₂, s₁, State.setReg_arrs, hwords] using
          (show words.getD d 0 < 2 ^ w by omega)))
  have heP : Exec w (.assign 21 (.op .add (.reg 21) (.read 11 (.reg 23)))) s₂ s₃ 5 := by
    apply Exec.assign
    exact eval_add (eval_reg (by simp [s₂, s₁]) (by omega)) hrP hpos
  have hrN : (Expr.read 11 (.reg 24)).eval w s₃ =
      some (words.getD (gm06DartMate d) 0) := by
    simpa only [s₃, s₂, s₁, State.setReg_arrs, hwords] using
      (read_getD (a := 11) (s := s₃)
        (eval_reg (by simp [s₃, s₂]) (hmate.trans hn))
        (by simpa [s₃, s₂, s₁, hwords, hlen] using hmate)
        (by simpa only [s₃, s₂, s₁, State.setReg_arrs, hwords] using
          (show words.getD (gm06DartMate d) 0 < 2 ^ w by omega)))
  have heN : Exec w (.assign 22 (.op .add (.reg 22) (.read 11 (.reg 24)))) s₃ s₄ 5 := by
    apply Exec.assign
    exact eval_add (eval_reg (by simp [s₃, s₂, s₁]) (by omega)) hrN hneg
  refine ⟨s₄, .seq (.assign heD) (.seq heMate (.seq heP heN)), rfl, ?_, ?_, ?_⟩
  · simpa [s₄, s₃, s₂, s₁] using hcursor
  · simp [s₄, s₃, d]
  · simp [s₄, d]

/-- The complete RAM turn accumulator returns both natural-number sums
in linear time, preserving every array. Bounds on the full sums ensure
that no prefix addition overflows. -/
theorem gm06Alg511TurnSumProg_exec {w m : ℕ} (words darts : List ℕ)
    (s : State) (hw : 2 < 2 ^ w) (hlen : words.length = 2 * m)
    (hn : 2 * m < 2 ^ w) (hpathlen : darts.length < 2 ^ w)
    (hwords : s.arrs 11 = words) (hpath : s.arrs 12 = darts)
    (hdarts : ∀ d ∈ darts, d < 2 * m)
    (hpos : (darts.map (fun d => words.getD d 0)).sum < 2 ^ w)
    (hneg : (darts.map (fun d => words.getD (gm06DartMate d) 0)).sum < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511TurnSumProg s s' t ∧
      t ≤ 9 + 29 * darts.length ∧ s'.arrs = s.arrs ∧
      s'.regs 21 = (darts.map (fun d => words.getD d 0)).sum ∧
      s'.regs 22 = (darts.map (fun d => words.getD (gm06DartMate d) 0)).sum := by
  let f := fun d => words.getD d 0
  let g := fun d => words.getD (gm06DartMate d) 0
  let I := fun i (st : State) => st.arrs = s.arrs ∧ st.regs 20 = i ∧
    st.regs 21 = gm06Alg511TurnPrefix darts f i ∧
    st.regs 22 = gm06Alg511TurnPrefix darts g i
  have hbody : ∀ i < darts.length, ∀ st, I i st →
      ∃ st' t, Exec w gm06Alg511TurnSumBody st st' t ∧ t ≤ 22 ∧
        I (i + 1) (st'.setReg 20 (i + 1)) ∧ st'.regs 20 = i := by
    intro i hi st hI
    obtain ⟨harr, hcur, hP, hN⟩ := hI
    have hPbound : st.regs 21 + f darts[i] < 2 ^ w := by
      rw [hP, ← gm06Alg511TurnPrefix_succ darts f hi]
      exact (gm06Alg511TurnPrefix_le darts f (i + 1)).trans_lt hpos
    have hNbound : st.regs 22 + g darts[i] < 2 ^ w := by
      rw [hN, ← gm06Alg511TurnPrefix_succ darts g hi]
      exact (gm06Alg511TurnPrefix_le darts g (i + 1)).trans_lt hneg
    obtain ⟨st', he, hearr, hecur, heP, heN⟩ := gm06Alg511TurnSumBody_exec words darts
      st hw hlen hn hi (hi.trans hpathlen) (by rw [harr, hwords])
      (by rw [harr, hpath]) hcur (hdarts _ (List.getElem_mem hi)) hPbound hNbound
    have hPnew : st'.regs 21 = gm06Alg511TurnPrefix darts f (i + 1) := by
      rw [heP, hP, gm06Alg511TurnPrefix_succ darts f hi]
    have hNnew : st'.regs 22 = gm06Alg511TurnPrefix darts g (i + 1) := by
      rw [heN, hN, gm06Alg511TurnPrefix_succ darts g hi]
    refine ⟨st', 22, he, le_rfl, ?_, hecur⟩
    refine ⟨hearr.trans harr, by simp, ?_, ?_⟩
    · simpa only [State.setReg_regs_ne _ _ (by decide : (21 : ℕ) ≠ 20)] using hPnew
    · simpa only [State.setReg_regs_ne _ _ (by decide : (22 : ℕ) ≠ 20)] using hNnew
  let s₁ := s.setReg 21 0
  let s₂ := s₁.setReg 22 0
  let s₃ := s₂.setReg 20 0
  have hinit : I 0 s₃ := by
    simp [I, s₃, s₂, s₁, gm06Alg511TurnPrefix]
  obtain ⟨s', t, he, ht, hI⟩ := forUp_exec' I darts.length 22
    (r_i := 20) (hi := .len 12) (by omega) hpathlen
    (fun i hi st hst => ⟨hst.2.1,
      eval_len (by rw [hst.1, hpath]) hpathlen⟩) hbody s₃ hinit
  refine ⟨s', 2 + (2 + (2 + t)),
    .seq (.assign (eval_const (Nat.two_pow_pos w)))
      (.seq (.assign (eval_const (Nat.two_pow_pos w)))
        (.seq (.assign (eval_const (Nat.two_pow_pos w))) he)), ?_, hI.1, ?_, ?_⟩
  · simp only [Expr.cost] at ht
    omega
  · simpa only [gm06Alg511TurnPrefix, List.take_length] using hI.2.2.1
  · simpa only [gm06Alg511TurnPrefix, List.take_length] using hI.2.2.2

end GraphMinor.Compute
