module

public import GraphMinor.Compute.F92Unpack

/-!
# Bounded copying for the search graph

A CSR representation specifies its used slices, while unused array entries can be arbitrary.
Copy entries with `readMin` so that unused values cannot cause overflow. Values within the
supplied bound are copied unchanged. The routine preserves every other array and lower register.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Copy an array, bounding each value by the word in `r_cap`. -/
def f92CopyBoundedProg (a_src a_dst r_cap r_base : ℕ) : Cmd :=
  .seq (.assign r_base (.len a_src))
    (.seq (.alloc a_dst (.reg r_base))
      (.seq (.assign (r_base + 1) (.const 0))
        (forUp (r_base + 1) (.reg r_base)
          (.write a_dst (.reg (r_base + 1))
            (.readMin a_src (.reg (r_base + 1)) (.reg r_cap))))))

/-- Bounded copying runs in linear time even when the source has unused entries larger
than a word. Its cap and source length must fit in a word. -/
theorem f92CopyBoundedProg_exec {w : ℕ} (a_src a_dst r_cap r_base cap : ℕ)
    (hab : a_src ≠ a_dst) (hrcap : r_cap < r_base)
    (xs : List ℕ) (hw : 1 < 2 ^ w) (hc : cap < 2 ^ w) (hlen : xs.length < 2 ^ w)
    {s : State} (hsrc : s.arrs a_src = xs) (hcap : s.regs r_cap = cap) :
    ∃ s' t, Exec w (f92CopyBoundedProg a_src a_dst r_cap r_base) s s' t ∧
      t ≤ 8 + 17 * xs.length ∧ s'.arrs a_dst = xs.map (fun v => min v cap) ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ q < r_base, s'.regs q = s.regs q) := by
  let s₁ := s.setReg r_base xs.length
  have hex₁ : Exec w (.assign r_base (.len a_src)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hsrc, hlen])
  let s₂ := s₁.setArr a_dst (List.replicate xs.length 0)
  have hex₂ : Exec w (.alloc a_dst (.reg r_base)) s₁ s₂ (1 + xs.length) :=
    .alloc (by simp [Expr.eval, checkWord, s₁, hlen])
  let s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  let Inv (i : ℕ) (st : State) : Prop :=
    st.regs r_base = xs.length ∧ st.regs (r_base + 1) = i ∧
    st.regs r_cap = cap ∧ st.arrs a_src = xs ∧
    ∃ (hd : (st.arrs a_dst).length = xs.length), ∀ j (hj : j < xs.length), j < i →
      (st.arrs a_dst)[j]'(by rw [hd]; exact hj) = min xs[j] cap
  have hloop : ⦃Inv 0⦄[w] forUp (r_base + 1) (.reg r_base)
      (.write a_dst (.reg (r_base + 1))
        (.readMin a_src (.reg (r_base + 1)) (.reg r_cap)))
      ⦃Inv xs.length⦄ ≤ fun _ => 3 + xs.length * 16 := by
    apply Triple.forUp_const Inv xs.length 9 hw hlen
    · intro i _ st hinv
      exact ⟨hinv.2.1, by simp [Expr.eval, checkWord, hinv.1, hlen]⟩
    · intro i hi st ⟨hrn, hri, hrc, hsrc', hdst, hprev⟩
      have hiw := hi.trans hlen
      have hmin : min xs[i] cap < 2 ^ w := (Nat.min_le_right _ _).trans_lt hc
      let st' := st.writeArr a_dst i (min xs[i] cap)
      have hex : Exec w (.write a_dst (.reg (r_base + 1))
          (.readMin a_src (.reg (r_base + 1)) (.reg r_cap))) st st' 6 :=
        .write (by simp [Expr.eval, checkWord, hri, hiw])
          (by simp [Expr.eval, checkWord, hri, hrc, hiw, hc, hsrc', hi, hmin])
          (by rw [hdst]; exact hi)
      refine ⟨st', 6, hex, by dsimp only; omega, ?_, hri⟩
      refine ⟨by simp [st', State.setReg, hrn], by simp,
        by simp [st', State.setReg, show r_cap ≠ r_base + 1 by omega, hrc],
        by simp [st', hab, hsrc'], by simp [st', hdst], ?_⟩
      intro j hj hji
      simp only [State.setReg_arrs, st', State.writeArr_arrs_self]
      by_cases hje : j = i
      · subst j
        rw [List.getElem_set_self]
      · rw [List.getElem_set_ne (by omega)]
        exact hprev j hj (by omega)
  have hinit : Inv 0 s₃ := by
    refine ⟨by simp [s₃, s₂, s₁], by simp [s₃],
      by simp [s₃, s₂, s₁, State.setReg, show r_cap ≠ r_base by omega,
        show r_cap ≠ r_base + 1 by omega, hcap],
      by simp [s₃, s₂, s₁, hab, hsrc], by simp [s₃, s₂], fun _ _ h => by omega⟩
  obtain ⟨s₄, t₄, hex₄, ht₄, _, _, _, _, hd, hvals⟩ := hloop s₃ hinit
  dsimp only at ht₄
  have hex : Exec w (f92CopyBoundedProg a_src a_dst r_cap r_base) s s₄
      (2 + ((1 + xs.length) + (2 + t₄))) := .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, _, hex, by omega, ?_, ?_, ?_⟩
  · apply List.ext_getElem
    · simpa using hd
    · intro i hi hj
      rw [List.getElem_map]
      exact hvals i (by simpa using hj) (by simpa using hj)
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [f92CopyBoundedProg, forUp, Cmd.writtenArrs, ha])
  · intro q hq
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [f92CopyBoundedProg, forUp, Cmd.writtenRegs, show q ≠ r_base by omega,
        show q ≠ r_base + 1 by omega])

end GraphMinor.Compute.Alg92
