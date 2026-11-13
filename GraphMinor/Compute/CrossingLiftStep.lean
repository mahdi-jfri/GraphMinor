module

public import GraphMinor.Compute.CrossingLiftTag
public import GraphMinor.Compute.CrossingLiftEncodedContract
public import GraphMinor.Compute.CrossingLiftEncodedReplacement
public import GraphMinor.Compute.CrossingLiftCost
import GraphMinor.Crossing.LinkLift

/-!
# Dispatching one reverse history step

The tag selects a replacement, contraction or deletion. The first two use the proved
encoded lifting programs. A deletion retains both paths, which remain a crossing in the
larger old graph. Only replacements and contractions incur a cost proportional to the
vertex count.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- Lift the record starting at register `R`, selecting its routine by the stored tag. -/
def liftEncodedStepProg (a_rec Q P a_base R : ℕ) : Cmd :=
  .ite (.op .eq (.read a_rec (.reg R)) (.const 0))
    (liftEncodedReplacementProg a_rec Q P a_base R)
    (.ite (.op .eq (.read a_rec (.reg R)) (.const 1))
      (liftEncodedContractProg a_rec Q P a_base (a_base + 1) (a_base + 2) (a_base + 3) R) .skip)

private theorem step_array_layout (a Q P b : ℕ) (h : [a, Q, P].Nodup)
    (ha : a < b) (hQ : Q < b) (hP : P < b) :
    [a, Q, P, b, b + 1, b + 2, b + 3].Nodup ∧ Q ≠ P := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at h ⊢
  omega

/-- One encoded history step produces exactly a lift through that record and an old
crossing. All hypotheses are the single-step history, new crossing, stored record/paths,
caller memory layout and word bounds. Deletions have no vertex-count cost. -/
theorem liftEncodedStepProg_exec {w N : ℕ} (G G' : SimpleGraph (Fin N))
    (S S' : Set (Fin N)) (D D' L₁ L₂ : List (Fin N)) (r : CrossRecord (Fin N))
    (hstep : IsHistory (G, S, D) [r] (G', S', D'))
    (hcross : IsCrossingPair G' D' L₁ L₂)
    (a_rec Q P a_base R : ℕ) (harr : [a_rec, Q, P].Nodup)
    (hrA : a_rec < a_base) (hQA : Q < a_base) (hPA : P < a_base)
    (pre words spare : List ℕ) (henc : IsRecordEnc r words) (s : State)
    (hrec : s.arrs a_rec = pre ++ words ++ spare) (hstart : s.regs R = pre.length)
    (hQ : s.arrs Q = L₁.map Fin.val) (hP : s.arrs P = L₂.map Fin.val)
    (hw : 65536 * (N + pre.length + words.length + 1) < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (W : List (Fin N) × List (Fin N)),
      Exec w (liftEncodedStepProg a_rec Q P a_base R) s s' t ∧
      t ≤ 50000 * ((N + 1) * liftWorkCount [r] + words.length) ∧
      IsLiftOne r (L₁, L₂) W ∧ IsCrossingPair G D W.1 W.2 ∧
      s'.arrs Q = W.1.map Fin.val ∧ s'.arrs P = W.2.map Fin.val ∧
      (∀ a < a_base, a ≠ Q → a ≠ P → s'.arrs a = s.arrs a) ∧
      (∀ k < R, s'.regs k = s.regs k) := by
  have hlayout := step_array_layout a_rec Q P a_base harr hrA hQA hPA
  have htag := eval_liftRecordTag (w := w) a_rec R r pre words spare henc s hrec hstart
    (by have hh := henc.two_le_length; omega)
  have hwords := henc.two_le_length
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  cases r with
  | repl r =>
    obtain ⟨rfl, rfl, hvalid, hfinal⟩ := hstep
    have hg : G' = r.newGraph := congrArg Prod.fst hfinal
    have hd : D' = D := congrArg (fun st => st.2.2) hfinal
    subst G' D'
    obtain ⟨s1, t1, W, he1, ht1, hi1, hc1, hQ1, hP1, ha1, hr1⟩ := liftEncodedReplacementProg_exec
      (w := w) r D L₁ L₂ hvalid hcross a_rec Q P a_base R hrA hQA hPA hlayout.2
      words pre spare henc s hrec hstart hQ hP
      (by simpa only [Fintype.card_fin] using hcross.1.1.2.1.length_le_card)
      (by simpa only [Fintype.card_fin] using hcross.2.1.1.2.1.length_le_card) hw
    have hc := eval_eq htag (eval_const hw0) hw1
    have hc' : (Expr.op .eq (.read a_rec (.reg R)) (.const 0)).eval w s = some 1 := by
      simpa only [liftRecordTag, ↓reduceIte] using hc
    refine ⟨s1, 4 + t1, W, .ite_true hc' (by omega) he1, ?_, hi1, hc1, hQ1, hP1, ha1, hr1⟩
    simp only [liftWorkCount]; omega
  | contr r =>
    obtain ⟨rfl, rfl, rfl, hvalid, hfinal⟩ := hstep
    have hg : G' = r.newGraph := congrArg Prod.fst hfinal
    have hd : D' = r.newCycle := congrArg (fun st => st.2.2) hfinal
    subst G' D'
    obtain ⟨s1, t1, he1, ht1, ha1, hr1, W, hi1, hc1, hQ1, hP1⟩ := liftEncodedContractProg_exec
      (w := w) r L₁ L₂ a_rec Q P a_base (a_base + 1) (a_base + 2) (a_base + 3) R
      hlayout.1 hvalid hcross pre words spare henc s hrec hstart hQ hP (by omega)
    have hc0 := eval_eq htag (eval_const hw0) hw1
    have hc1' := eval_eq htag (eval_const hw1) hw1
    have hc0' : (Expr.op .eq (.read a_rec (.reg R)) (.const 0)).eval w s = some 0 := by
      simpa only [liftRecordTag, Nat.one_ne_zero, ↓reduceIte] using hc0
    have hc1'' : (Expr.op .eq (.read a_rec (.reg R)) (.const 1)).eval w s = some 1 := by
      simpa only [liftRecordTag, ↓reduceIte] using hc1'
    refine ⟨s1, 4 + (4 + t1), W, .ite_false hc0' (.ite_true hc1'' (by omega) he1),
      ?_, hi1, hc1, hQ1, hP1, ?_, hr1⟩
    · simp only [liftWorkCount]; omega
    · intro a ha haq hap
      exact ha1 a (by simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true]; omega)
  | del H T =>
    obtain ⟨hle, _, _, _, _, hfinal⟩ := hstep
    have hg : G' = H := congrArg Prod.fst hfinal
    have hd : D' = D := congrArg (fun st => st.2.2) hfinal
    subst G' D'
    have hc0 := eval_eq htag (eval_const hw0) hw1
    have hc1 := eval_eq htag (eval_const hw1) hw1
    have hc0' : (Expr.op .eq (.read a_rec (.reg R)) (.const 0)).eval w s = some 0 := by
      simpa only [liftRecordTag, Nat.reduceEqDiff, ↓reduceIte] using hc0
    have hc1' : (Expr.op .eq (.read a_rec (.reg R)) (.const 1)).eval w s = some 0 := by
      simpa only [liftRecordTag, Nat.reduceEqDiff, ↓reduceIte] using hc1
    exact ⟨s, 4 + (4 + 1), (L₁, L₂), .ite_false hc0' (.ite_false hc1' (.skip s)),
      by simp only [liftWorkCount]; omega, rfl, hcross.mono hle, hQ, hP,
      fun _ _ _ _ => rfl, fun _ _ => rfl⟩

end GraphMinor.Compute.Crossing
