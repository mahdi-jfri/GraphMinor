module

public import GraphMinor.Compute.Logic
import Mathlib.Data.List.GetD

/-!
# Starting positions of the edge buckets for Algorithm (9.9)

The tail counts determine a consecutive block for each vertex. A running sum
writes the start of each block. The proof uses the sum of the counts to bound
every intermediate word, so zero counts and the empty list are allowed.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Write one bucket start, then add its count to the running total. -/
def alg99BucketStartBody (a_count a_start r : ℕ) : Cmd :=
  .seq (.write a_start (.reg r) (.reg (r + 1)))
    (.assign (r + 1) (.op .add (.reg (r + 1)) (.read a_count (.reg r))))

/-- Form the exclusive prefix sums of the bucket counts. -/
def alg99BucketStartProg (a_count a_start r : ℕ) : Cmd :=
  .seq (.alloc a_start (.len a_count))
    (.seq (.assign r (.const 0))
      (.seq (.assign (r + 1) (.const 0))
        (forUp r (.len a_count) (alg99BucketStartBody a_count a_start r))))

private theorem sum_take_le99 (xs : List ℕ) (k : ℕ) :
    (xs.take k).sum ≤ xs.sum := by
  have h := congrArg List.sum (List.take_append_drop k xs)
  rw [List.sum_append] at h
  omega

private theorem sum_take_succ99 (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    (xs.take (k + 1)).sum = (xs.take k).sum + xs[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The prefix-sum pass writes the starting position of each bucket and leaves
the total count in register `r + 1`. Its only hypotheses are the separate source
and destination arrays, the input array, and the word bounds displayed here. -/
theorem alg99BucketStartProg_exec {w : ℕ} (counts : List ℕ)
    (a_count a_start r : ℕ) (hne : a_count ≠ a_start)
    (hw : 1 < 2 ^ w) (hlen : counts.length < 2 ^ w) (hsum : counts.sum < 2 ^ w)
    (s : State) (hsrc : s.arrs a_count = counts) :
    ∃ s' t, Exec w (alg99BucketStartProg a_count a_start r) s s' t ∧
      t ≤ 23 * counts.length + 8 ∧
      s'.arrs a_start = List.ofFn (fun v : Fin counts.length => (counts.take v.1).sum) ∧
      s'.regs (r + 1) = counts.sum ∧
      (∀ a : ℕ, a ≠ a_start → s'.arrs a = s.arrs a) ∧
      (∀ j : ℕ, j ≠ r → j ≠ r + 1 → s'.regs j = s.regs j) := by
  let s₀ := s.setArr a_start (List.replicate counts.length 0)
  have hex₀ : Exec w (.alloc a_start (.len a_count)) s s₀ (1 + counts.length) :=
    .alloc (by simp [Expr.eval, checkWord, hsrc, hlen])
  let s₁ := s₀.setReg r 0
  have hex₁ : Exec w (.assign r (.const 0)) s₀ s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord])
  let si := s₁.setReg (r + 1) 0
  have hexi : Exec w (.assign (r + 1) (.const 0)) s₁ si 2 :=
    .assign (by simp [Expr.eval, checkWord])
  let I : ℕ → State → Prop := fun k st =>
    st.arrs a_count = counts ∧ st.regs r = k ∧
      st.regs (r + 1) = (counts.take k).sum ∧
      (st.arrs a_start).length = counts.length ∧
      ∀ j < counts.length, j < k →
        (st.arrs a_start).getD j 0 = (counts.take j).sum
  have hloop : ⦃I 0⦄[w]
      forUp r (.len a_count) (alg99BucketStartBody a_count a_start r)
      ⦃I counts.length⦄ ≤ fun _ => 3 + counts.length * 21 := by
    apply Triple.forUp_const I counts.length 14 hw hlen
    · intro k _ st hi
      exact ⟨hi.2.1, by simp [Expr.eval, checkWord, hi.1, hlen]⟩
    · intro k hk st hi
      obtain ⟨hc, hr, hacc, hdst, hprev⟩ := hi
      have hk_w : k < 2 ^ w := hk.trans hlen
      have hpre_w : (counts.take k).sum < 2 ^ w :=
        (sum_take_le99 counts k).trans_lt hsum
      have hnext_w : (counts.take k).sum + counts[k] < 2 ^ w := by
        rw [← sum_take_succ99 counts k hk]
        exact (sum_take_le99 counts (k + 1)).trans_lt hsum
      have hval_w : counts[k] < 2 ^ w := by omega
      let sa := st.writeArr a_start k (counts.take k).sum
      have hexa : Exec w (.write a_start (.reg r) (.reg (r + 1))) st sa 3 :=
        .write (by simp [Expr.eval, checkWord, hr, hk_w])
          (by simp [Expr.eval, checkWord, hacc, hpre_w]) (by rwa [hdst])
      let sb := sa.setReg (r + 1) ((counts.take k).sum + counts[k])
      have hexb : Exec w
          (.assign (r + 1) (.op .add (.reg (r + 1)) (.read a_count (.reg r)))) sa sb 5 := by
        apply Exec.assign
        simp [sa, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr, hacc, hk_w,
          hpre_w, hnext_w, hval_w, hne, hc, hk]
      have hrb : sb.regs r = k := by simp [sb, sa, hr]
      refine ⟨sb, 8, .seq hexa hexb, by dsimp only; omega, ?_, hrb⟩
      refine ⟨?_, by simp, ?_, ?_, ?_⟩
      · simp [sb, sa, hne, hc]
      · simp [sb, sum_take_succ99 counts k hk]
      · simp [sb, sa, hdst]
      · intro j hj hjk
        by_cases heq : j = k
        · subst j
          simp [sb, sa, State.writeArr, hdst, hk]
        · have hjlt : j < k := by omega
          simpa [sb, sa, State.writeArr, heq, Ne.symm heq] using hprev j hj hjlt
  have hi : I 0 si := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [si, s₁, s₀, hne, hsrc]
    · simp [si, s₁]
    · simp [si]
    · simp [si, s₁, s₀]
    · intro j _ hj
      omega
  obtain ⟨s', t, hex, ht, hout⟩ := hloop si hi
  have hexall : Exec w (alg99BucketStartProg a_count a_start r) s s'
      ((1 + counts.length) + (2 + (2 + t))) := .seq hex₀ (.seq hex₁ (.seq hexi hex))
  refine ⟨s', (1 + counts.length) + (2 + (2 + t)), hexall,
    by dsimp only at ht; omega, ?_, ?_, ?_, ?_⟩
  · apply List.ext_getElem (by simp [hout.2.2.2.1])
    intro j hj hj'
    have hjc : j < counts.length := by simpa using hj'
    have hh := hout.2.2.2.2 j hjc hjc
    rw [List.getD_eq_getElem _ _ hj] at hh
    simpa using hh
  · simpa using hout.2.2.1
  · intro a ha
    exact hexall.arrs_eq_of_not_mem_writtenArrs
      (by simp [alg99BucketStartProg, alg99BucketStartBody, forUp, ha])
  · intro j hj hj1
    exact hexall.regs_eq_of_not_mem_writtenRegs
      (by simp [alg99BucketStartProg, alg99BucketStartBody, forUp, hj, hj1])

end GraphMinor.Compute
