module

public import GraphMinor.Compute.Algorithm99LoopBody

/-!
# Step (9) of Algorithm (9.9): the loop

The recursion of Algorithm (9.9) (Graph Minors XIII, pages 104–105) repeats steps (3) to (8)
until it stops. On the Word RAM it is the program `alg99LoopProg`, a `while` loop on the flag in
register `Q + 5` around one iteration `alg99BodyProg`.

The loop ends because each iteration that does not stop at least halves
`|E(G_i)| + |V(G_i)| + 1` (condition (i) of step (2), from step (8)). The same fact bounds the
time: iteration `i` costs at most `K (n + 1) (|E(G_i)| + |V(G_i)| + 1)`, and these numbers halve,
so the total is at most twice the cost of the first iteration. The proof is a strong induction on
`|E(G_i)| + |V(G_i)| + 1` (`alg99LoopProg_exec`).

The loop carries a property `Inv` of states that step (8) keeps. The run of (9.9) on its own
takes `Inv` true; the run inside (10.5) takes "`orig` misses `Z_i`"
(`Alg99Iter.step8_orig_not_mem`).
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph

/-- The loop of (9.9): repeat one iteration while the flag in register `Q + 5` is not `0`. -/
def alg99LoopProg (P97 P : Cmd) (pp h : ℕ) (h2 : 2 ≤ h) (h' : ℕ) (h2' : 2 ≤ h') (B Q : ℕ) :
    Cmd :=
  .while (.reg (Q + 5)) (alg99BodyProg P97 P pp h h2 h' h2' B Q)

/-- What the loop writes in `outArr` when it stops: `Alg99StopOut` for some valid state that
has the property `Inv`. -/
def Alg99LoopOut (pp h ω : ℕ) (h2 : 2 ≤ h) (he : Even h) (C_blk w B : ℕ) {h' n : ℕ}
    {G : MultiDigraph n} (Inv : Alg99Iter h' G → Prop) (out : List ℕ) : Prop :=
  ∃ (st : Alg99Iter h' G) (hst : st.IsValid (pp.choose 2 + 5)), Inv st ∧
    Alg99StopOut pp h ω h2 he C_blk w B st hst out

/-- **Step (9) of Algorithm (9.9)** (Graph Minors XIII, pages 104–105), the loop, on the Word
RAM. From a valid state `st` with the property `Inv`, stored at `B`, with `n` in register
`Q + 6` and the flag `Q + 5` equal to `1`, the loop stops within
`2 (K + 1) (n + 1) (|E(G_i)| + v_i + 1)` steps (`K = alg99IterConst …`) with an output
`Alg99LoopOut` in `outArr`. -/
theorem alg99LoopProg_exec {pp h h' ω C97 c97 C C_blk c K4 : ℕ} {h2 : 2 ≤ h} {he : Even h}
    {h2' : 2 ≤ h'} {he' : Even h'} {P97 P : Cmd} {B Q : ℕ}
    (hP97 : RunsAsSubroutine (alg97Size (h' := h')) (encAlg97In (h' := h'))
      (IsAlg97Output pp (pp.choose 2 + 5) h h') P97 (fun m => m) C97 c97)
    (hP : Case3StepsRuns h h' ω h2 he h2' he' C C_blk c 23 16 (B + 5) 33 (B - 1) (B - 2) (B - 3)
      (B - 4) (B + 6) (Q + 7) (Q + 10) P)
    (hK4 : ∀ n m, alg99Step4Cost (pp.choose 2 + 5) h h' B n m ≤ K4 * (n + m + 1))
    (hB : 40 ≤ B) (hB97 : folioCallerArrBase P97 ≤ B) (hQ : 15 ≤ Q)
    (hQ97 : folioCallerRegBase P97 ≤ Q)
    {n : ℕ} {G : MultiDigraph n} (Inv : Alg99Iter h' G → Prop)
    (hInv : ∀ (st : Alg99Iter h' G) (X V_A Bd : Finset (Fin st.v)) (A_sub : MultiDigraph st.v)
      (W_A : WallOfHeight h' (A_sub.deleteVerticesCompact V_Aᶜ)),
      Inv st → Inv (st.step8 X V_A Bd W_A))
    {w : ℕ} (st : Alg99Iter h' G) (hst : st.IsValid (pp.choose 2 + 5)) (hI : Inv st)
    (hw : wordSize (alg99WordConst pp h h' c97 c C_blk)
      ((n + 1) * (st.Gi.numEdges + st.v + 1)) ≤ w)
    {s : State} (hS : st.StoredIn B s) (hn : s.regs (Q + 6) = n) (hflag : s.regs (Q + 5) = 1) :
    ∃ s' t, Exec w (alg99LoopProg P97 P pp h h2 h' h2' B Q) s s' t ∧
      t ≤ 2 * (alg99IterConst pp h' C97 K4 C C_blk + 1) *
        ((n + 1) * (st.Gi.numEdges + st.v + 1)) ∧
      s'.regs (Q + 6) = n ∧
      Alg99LoopOut pp h ω h2 he C_blk w B Inv (s'.arrs outArr) := by
  set KI := alg99IterConst pp h' C97 K4 C C_blk with hKI
  have hw1 : 1 < 2 ^ w :=
    alg99_word_lt hw (D := 1) (by unfold alg99WordConst; omega) (by omega)
  suffices H : ∀ M (st : Alg99Iter h' G) (s : State), st.Gi.numEdges + st.v + 1 = M →
      st.IsValid (pp.choose 2 + 5) → Inv st →
      wordSize (alg99WordConst pp h h' c97 c C_blk) ((n + 1) * M) ≤ w →
      st.StoredIn B s → s.regs (Q + 6) = n → s.regs (Q + 5) = 1 →
      ∃ s' t, Exec w (alg99LoopProg P97 P pp h h2 h' h2' B Q) s s' t ∧
        t ≤ 2 * (KI + 1) * ((n + 1) * M) ∧ s'.regs (Q + 6) = n ∧
        Alg99LoopOut pp h ω h2 he C_blk w B Inv (s'.arrs outArr) from
    H _ st s rfl hst hI hw hS hn hflag
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro st s hM hst hI hw hS hn hflag
  rw [← hM] at hw
  obtain ⟨s₁, t₁, hex₁, ht₁, hn₁, hcase⟩ :=
    alg99BodyProg_exec hP97 hP hK4 hB hB97 hQ hQ97 hst hw hS hn
  rw [hM, ← hKI] at ht₁
  have hcond : (Expr.reg (Q + 5)).eval w s = some 1 := by
    simp [Expr.eval, hflag, checkWord, hw1]
  have hS1 : 1 ≤ (n + 1) * M := Nat.mul_pos (by omega) (by omega)
  rcases hcase with ⟨hf₁, hout⟩ | ⟨hf₁, X, V_A, Bd, A_sub, W_A, hS', hval, hsize⟩
  · have hc0 : (Expr.reg (Q + 5)).eval w s₁ = some 0 := by
      simp [Expr.eval, hf₁, checkWord, show (0 : ℕ) < 2 ^ w by omega]
    refine ⟨s₁, (Expr.reg (Q + 5)).cost + t₁ + (Expr.reg (Q + 5)).cost,
      .while_true hcond one_ne_zero hex₁ (.while_false hc0), ?_, hn₁, st, hst, hI, hout⟩
    have : 2 * (KI + 1) * ((n + 1) * M) = KI * ((n + 1) * M) + (KI + 2) * ((n + 1) * M) := by
      ring
    have h2 := Nat.mul_le_mul_right ((n + 1) * M) (show 2 ≤ KI + 2 by omega)
    simp only [Expr.cost]
    omega
  · set st' := st.step8 X V_A Bd W_A with hst'
    have hlt : st'.Gi.numEdges + st'.v + 1 < M := by omega
    have hw' : wordSize (alg99WordConst pp h h' c97 c C_blk)
        ((n + 1) * (st'.Gi.numEdges + st'.v + 1)) ≤ w :=
      (wordSize_mono_right _ (Nat.mul_le_mul_left _ (by omega))).trans hw
    obtain ⟨s₂, t₂, hex₂, ht₂, hn₂, hout⟩ :=
      ih _ hlt st' s₁ rfl hval (hInv st X V_A Bd A_sub W_A hI) hw' hS' hn₁ (by rw [hf₁, hflag])
    refine ⟨s₂, (Expr.reg (Q + 5)).cost + t₁ + t₂, .while_true hcond one_ne_zero hex₁ hex₂, ?_,
      hn₂, hout⟩
    have hmono : (KI + 1) * ((n + 1) * (2 * (st'.Gi.numEdges + st'.v + 1))) ≤
        (KI + 1) * ((n + 1) * M) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have e1 : 2 * (KI + 1) * ((n + 1) * (st'.Gi.numEdges + st'.v + 1)) =
        (KI + 1) * ((n + 1) * (2 * (st'.Gi.numEdges + st'.v + 1))) := by ring
    have e2 : 2 * (KI + 1) * ((n + 1) * M) = KI * ((n + 1) * M) + (KI + 1) * ((n + 1) * M) +
        (n + 1) * M := by ring
    simp only [Expr.cost]
    omega

end GraphMinor.Compute
