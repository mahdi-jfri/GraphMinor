module

public import GraphMinor.Compute.GM06Alg34DualNextCuffExpr
public import GraphMinor.Compute.GM06Alg34DualGapInput

/-!
# Computing all gap-region words of the dual

Allocate one word per old cuff position and read the next old primal
vertex at each position. The resulting array is exactly the internal
gap metadata of the finite augmented dual. The loop visits no positions
when the cuff is empty.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Compute the following old cuff labels in array 57. -/
def gm06DualNextCuffProg : Cmd :=
  .seq (.assign 8001 (.len 2)) (.seq (.alloc 57 (.reg 8001))
    (.seq (.assign 8000 (.const 0))
      (forUp 8000 (.reg 8001) (.write 57 (.reg 8000) gm06DualNextCuffExpr))))

/-- The complete next-cuff array is computed in linear time, preserving
all other arrays and all registers outside the two loop counters. -/
theorem gm06DualNextCuffProg_exec {w n : ℕ} (L : List (Fin n)) {s : State}
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hk : L.length < 2 ^ w)
    (hsource : s.arrs 2 = L.map Fin.val) :
    ∃ s' t, Exec w gm06DualNextCuffProg s s' t ∧ t ≤ 100 * (L.length + 1) ∧
      s'.arrs 57 = List.ofFn (fun i : Fin L.length => (L.get (gm06CycleSucc i)).val) ∧
      s'.regs 8001 = L.length ∧
      (∀ A : ℕ, A ≠ 57 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 8000 → q ≠ 8001 → s'.regs q = s.regs q) := by
  let s₁ := s.setReg 8001 L.length
  let s₂ := s₁.setArr 57 (List.replicate L.length 0)
  let s₃ := s₂.setReg 8000 0
  have he₁ : Exec w (.assign 8001 (.len 2)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hsource, hk])
  have he₂ : Exec w (.alloc 57 (.reg 8001)) s₁ s₂ (1 + L.length) :=
    .alloc (by simp [Expr.eval, checkWord, s₁, hk])
  have he₃ : Exec w (.assign 8000 (.const 0)) s₂ s₃ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.zero_lt_of_lt hw))
  let Inv (k : ℕ) (st : State) : Prop :=
    (st.arrs 57).length = L.length ∧
    (∀ j (hj : j < (st.arrs 57).length) (hjL : j < L.length), j < k →
      (st.arrs 57)[j] = (L.get (gm06CycleSucc ⟨j, hjL⟩)).val) ∧
    st.regs 8001 = L.length ∧ st.regs 8000 = k ∧
    (∀ A : ℕ, A ≠ 57 → st.arrs A = s.arrs A) ∧
    (∀ q : ℕ, q ≠ 8000 → q ≠ 8001 → st.regs q = s.regs q)
  have hInv₀ : Inv 0 s₃ := by
    refine ⟨by simp [s₃, s₂], fun _ _ _ hj => by omega,
      by simp [s₃, s₂, s₁], by simp [s₃], ?_, ?_⟩
    · intro A hA; simp [s₃, s₂, s₁, State.setArr, hA]
    · intro q h0 h1; simp [s₃, s₂, s₁, State.setReg, h0, h1]
  have hLoop : ⦃Inv 0⦄[w]
      forUp 8000 (.reg 8001) (.write 57 (.reg 8000) gm06DualNextCuffExpr)
      ⦃Inv L.length⦄ ≤ fun _ => 3 + L.length * (7 + 8) := by
    apply Triple.forUp_const Inv L.length 8 hw hk
    · intro k _ st ⟨_, _, hrn, hri, _, _⟩
      exact ⟨hri, GraphMinor.Compute.Crossing.eval_reg hrn hk⟩
    · intro k hki st ⟨hlen, hval, hrn, hri, ha, hg⟩
      let v := (L.get (gm06CycleSucc ⟨k, hki⟩)).val
      have hs : st.arrs 2 = L.map Fin.val := (ha 2 (by decide)).trans hsource
      have hread : gm06DualNextCuffExpr.eval w st = some v :=
        gm06DualNextCuffExpr_eval L ⟨k, hki⟩ hw hn hk hs hri
      refine ⟨st.writeArr 57 k v, 8,
        .write (i := k) (v := v) (GraphMinor.Compute.Crossing.eval_reg hri (hki.trans hk))
          hread (by rw [hlen]; exact hki), le_rfl,
        ⟨?_, ?_, ?_, by simp, ?_, ?_⟩, by simp [State.writeArr, hri]⟩
      · simp [State.writeArr, hlen]
      · intro j hj hjL hjk
        simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs_self] at hj ⊢
        rw [List.getElem_set]
        split_ifs with h
        · subst j; rfl
        · exact hval j (by simpa using hj) hjL (by omega)
      · simpa only [State.setReg_regs_ne _ _ (by decide : 8001 ≠ 8000), State.writeArr_regs] using hrn
      · intro A hA
        simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs_ne _ _ hA]
        exact ha A hA
      · intro q h0 h1
        simp only [State.setReg_regs_ne _ _ h0, State.writeArr_regs]
        exact hg q h0 h1
  obtain ⟨s₄, t₄, he₄, ht₄, hlen₄, hval₄, hcount₄, _, ha₄, hg₄⟩ := hLoop s₃ hInv₀
  have htime : t₄ ≤ 3 + L.length * (7 + 8) := ht₄
  refine ⟨s₄, 2 + ((1 + L.length) + (2 + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)),
    by omega, ?_, hcount₄, ha₄, hg₄⟩
  apply List.ext_getElem (by simp only [hlen₄, List.length_ofFn])
  intro j hj hj'
  have hjL : j < L.length := by simpa only [hlen₄] using hj
  rw [hval₄ j hj hjL hjL, List.getElem_ofFn]

/-- The generated next-cuff words are precisely the augmented finite
dual's internal single-cuff gap array. -/
theorem gm06DualNextCuffProg_exec_input {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hR : 0 < x.regions.length)
    (g : Fin L.length → Fin x.regions.length) {s : State}
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hk : L.length < 2 ^ w)
    (hsource : s.arrs 2 = L.map Fin.val) :
    ∃ s' t, Exec w gm06DualNextCuffProg s s' t ∧ t ≤ 100 * (L.length + 1) ∧
      s'.arrs 57 = (x.dualGapInput L hR g).discGapWords ∧
      s'.regs 8001 = L.length ∧
      (∀ A : ℕ, A ≠ 57 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 8000 → q ≠ 8001 → s'.regs q = s.regs q) := by
  simpa only [GM06DrawingData.dualGapInput_discGapWords] using
    gm06DualNextCuffProg_exec L hw hn hk hsource

end GraphMinor.Compute
