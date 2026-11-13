module

public import GraphMinor.Compute.CrossingOpsBasic
import GraphMinor.Compute.TwoPathsFrameEdges

/-!
# Testing an old boundary edge in the recorded pair list

The replacement encoding lists ordered old edges flat, two words per edge. Lemma 1's reverse
rule needs to test whether a consecutive boundary pair is among them. This file scans the
encoded list and returns its exact membership flag, preserving the path and record arrays.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Test the ordered pair in `r_a`, `r_b` in the flat edge list, writing a flag to `r_out`.
The counter and pair count use scratch registers `R` and `R+1`. -/
def liftPairTestProg (edges r_a r_b r_out R : ℕ) : Cmd :=
  .seq (.assign r_out (.const 0))
    (.seq (.assign (R + 1) (.op .div (.len edges) (.const 2)))
      (.seq (.assign R (.const 0))
        (forUp R (.reg (R + 1))
          (.ite (.op .eq (.read edges (.op .mul (.const 2) (.reg R))) (.reg r_a))
            (.ite (.op .eq (.read edges (.op .add (.op .mul (.const 2) (.reg R)) (.const 1))) (.reg r_b))
              (.assign r_out (.const 1)) .skip) .skip))))

private theorem flat_pairs_length {N : ℕ} (E : List (Fin N × Fin N)) :
    (E.flatMap encPair).length = 2 * E.length := by
  exact TwoPaths.length_pairsList E

private theorem flat_pairs_fields {N : ℕ} (E : List (Fin N × Fin N)) (j : ℕ)
    (hj : j < E.length) :
    (E.flatMap encPair)[2 * j]? = some E[j].1.val ∧
      (E.flatMap encPair)[2 * j + 1]? = some E[j].2.val := by
  change (TwoPaths.pairsList E)[2 * j]? = some E[j].1.val ∧
    (TwoPaths.pairsList E)[2 * j + 1]? = some E[j].2.val
  have h := TwoPaths.pairsList_getElem? E j
  simpa only [List.getElem?_eq_getElem hj, Option.map_some] using h

private theorem pair_take_step {V : Type*} {E : List (V × V)} {a b : V} {j : ℕ}
    (hj : j < E.length) :
    (a, b) ∈ E.take (j + 1) ↔ (a, b) ∈ E.take j ∨ E[j] = (a, b) := by
  rw [List.take_succ_eq_append_getElem hj]
  simp only [List.mem_append, List.mem_singleton, eq_comm]

/-- The flat-pair scan returns one precisely for a recorded pair. The edge order and
multiplicities do not matter. All assumptions concern stored data and word/layout bounds. -/
theorem liftPairTestProg_exec {w N : ℕ} (edges r_a r_b r_out R : ℕ)
    (haR : r_a < R) (hbR : r_b < R) (hoR : r_out < R)
    (hao : r_a ≠ r_out) (hbo : r_b ≠ r_out)
    (E : List (Fin N × Fin N)) (a b : Fin N) (s : State)
    (hE : s.arrs edges = E.flatMap encPair)
    (ha : s.regs r_a = a.val) (hb : s.regs r_b = b.val)
    (hw : N + 2 * E.length + 3 < 2 ^ w) :
    ∃ s' t, Exec w (liftPairTestProg edges r_a r_b r_out R) s s' t ∧
      t ≤ 30 * (E.length + 1) ∧ s'.regs r_out = (if (a, b) ∈ E then 1 else 0) ∧
      (∀ c, s'.arrs c = s.arrs c) ∧
      (∀ q < R, q ≠ r_out → s'.regs q = s.regs q) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  let s0 := s.setReg r_out 0
  let s1 := s0.setReg (R + 1) E.length
  let s2 := s1.setReg R 0
  have hecount : (Expr.op .div (.len edges) (.const 2)).eval w s0 = some E.length := by
    have helen : (Expr.len edges).eval w s0 = some (2 * E.length) := by
      have he := eval_len (w := w) (s := s0) hE (by rw [flat_pairs_length]; omega)
      simpa only [flat_pairs_length] using he
    rw [Expr.eval, helen, eval_const hw2]
    simp [BinOp.eval, BinOp.raw, checkWord, show E.length < 2 ^ w by omega]
  let I : ℕ → State → Prop := fun j st =>
    st.regs R = j ∧ st.regs (R + 1) = E.length ∧
    st.regs r_out = (if (a, b) ∈ E.take j then 1 else 0) ∧
    (∀ c, st.arrs c = s.arrs c) ∧
    (∀ q < R, q ≠ r_out → st.regs q = s.regs q)
  have hinit : I 0 s2 := by
    refine ⟨by simp [s2], by simp [s2, s1], ?_, fun _ => rfl, ?_⟩
    · simp [s2, s1, s0, show r_out ≠ R by omega, show r_out ≠ R + 1 by omega]
    · intro q hq hqo
      simp [s2, s1, s0, show q ≠ R by omega, show q ≠ R + 1 by omega, hqo]
  obtain ⟨s3, t3, he3, ht3, hI⟩ := forUp_exec' I E.length 16 hw1 (by omega)
    (r_i := R) (hi := .reg (R + 1))
    (body := .ite (.op .eq (.read edges (.op .mul (.const 2) (.reg R))) (.reg r_a))
      (.ite (.op .eq (.read edges (.op .add (.op .mul (.const 2) (.reg R)) (.const 1))) (.reg r_b))
        (.assign r_out (.const 1)) .skip) .skip)
    (fun j _ st hI => ⟨hI.1, eval_reg hI.2.1 (by omega)⟩)
    (fun j hj st hI => by
      obtain ⟨hi, hn, ho, harr, hr⟩ := hI
      have hs : st.arrs edges = E.flatMap encPair := (harr edges).trans hE
      have hfields := flat_pairs_fields E j hj
      have hgetA : (st.arrs edges)[2 * j]? = some E[j].1.val := hs ▸ hfields.1
      have hgetB : (st.arrs edges)[2 * j + 1]? = some E[j].2.val := hs ▸ hfields.2
      have hreadA : (Expr.read edges (.op .mul (.const 2) (.reg R))).eval w st = some E[j].1.val := by
        obtain ⟨hbound, hval⟩ := List.getElem?_eq_some_iff.mp hgetA
        rw [← hval]
        exact eval_read (eval_mul (eval_const hw2) (eval_reg hi (by omega)) (by omega)) hbound
          (by rw [hval]; exact E[j].1.isLt.trans (by omega))
      have hreadB : (Expr.read edges (.op .add (.op .mul (.const 2) (.reg R)) (.const 1))).eval w st =
          some E[j].2.val := by
        obtain ⟨hbound, hval⟩ := List.getElem?_eq_some_iff.mp hgetB
        rw [← hval]
        exact eval_read (eval_add (eval_mul (eval_const hw2) (eval_reg hi (by omega)) (by omega))
          (eval_const hw1) (by omega)) hbound
          (by rw [hval]; exact E[j].2.isLt.trans (by omega))
      have hca := eval_eq hreadA (eval_reg ((hr r_a haR hao).trans ha) (a.isLt.trans (by omega))) hw1
      have hcb := eval_eq hreadB (eval_reg ((hr r_b hbR hbo).trans hb) (b.isLt.trans (by omega))) hw1
      have hstep := pair_take_step (a := a) (b := b) hj
      by_cases hja : E[j].1 = a
      · have hca1 : (Expr.op .eq (.read edges (.op .mul (.const 2) (.reg R))) (.reg r_a)).eval w st = some 1 := by
          simpa only [hja, ↓reduceIte] using hca
        by_cases hjb : E[j].2 = b
        · have hcb1 : (Expr.op .eq (.read edges (.op .add (.op .mul (.const 2) (.reg R)) (.const 1)))
              (.reg r_b)).eval w st = some 1 := by simpa only [hjb, ↓reduceIte] using hcb
          have hpair : E[j] = (a, b) := Prod.ext hja hjb
          refine ⟨st.setReg r_out 1, 16, .ite_true hca1 (by omega)
            (.ite_true hcb1 (by omega) (.assign (eval_const hw1))), by omega, ?_, ?_⟩
          · refine ⟨by simp, ?_, ?_, harr, ?_⟩
            · simp [show R + 1 ≠ r_out by omega, hn]
            · simp [show r_out ≠ R by omega, (hstep.mpr (Or.inr hpair))]
            · intro q hq hqo; simp [show q ≠ R by omega, hqo, hr q hq hqo]
          · simp [show R ≠ r_out by omega, hi]
        · have hcb0 : (Expr.op .eq (.read edges (.op .add (.op .mul (.const 2) (.reg R)) (.const 1)))
              (.reg r_b)).eval w st = some 0 := by
            simpa only [Fin.val_injective.eq_iff, hjb, ↓reduceIte] using hcb
          have hpair : E[j] ≠ (a, b) := fun h => hjb (congrArg Prod.snd h)
          refine ⟨st, 15, .ite_true hca1 (by omega) (.ite_false hcb0 (.skip st)), by omega, ?_, hi⟩
          refine ⟨by simp, by simp [hn], ?_, harr, ?_⟩
          · simpa only [State.setReg_regs_ne _ _ (show r_out ≠ R by omega), hstep,
              hpair, or_false] using ho
          · intro q hq hqo; simp [show q ≠ R by omega, hr q hq hqo]
      · have hca0 : (Expr.op .eq (.read edges (.op .mul (.const 2) (.reg R))) (.reg r_a)).eval w st = some 0 := by
          simpa only [Fin.val_injective.eq_iff, hja, ↓reduceIte] using hca
        have hpair : E[j] ≠ (a, b) := fun h => hja (congrArg Prod.fst h)
        refine ⟨st, 7, .ite_false hca0 (.skip st), by omega, ?_, hi⟩
        refine ⟨by simp, by simp [hn], ?_, harr, ?_⟩
        · simpa only [State.setReg_regs_ne _ _ (show r_out ≠ R by omega), hstep,
            hpair, or_false] using ho
        · intro q hq hqo; simp [show q ≠ R by omega, hr q hq hqo])
    s2 hinit
  refine ⟨s3, 2 + (4 + (2 + t3)),
    .seq (.assign (eval_const hw0)) (.seq (.assign hecount) (.seq (.assign (eval_const hw0)) he3)),
    ?_, ?_, hI.2.2.2.1, hI.2.2.2.2⟩
  · simp only [Expr.cost] at ht3; omega
  · simpa only [List.take_length] using hI.2.2.1

end GraphMinor.Compute.Crossing
