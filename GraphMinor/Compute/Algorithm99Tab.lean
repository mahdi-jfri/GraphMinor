module

public import GraphMinor.Compute.Algorithm99State

/-!
# Writing an array entry by entry

Step (8) of Algorithm (9.9) (Graph Minors XIII, page 105) builds several arrays of the next state
in the same way: entry `i` of the new array is a word read from other arrays at an index that
depends on `i` (for example the new `orig` is `orig ∘ compactEmb`). This file gives that loop
once.

`tabProg dst r_n r_i e` allocates `dst` with the length in register `r_n`, and for
`i = 0, 1, …` writes the value of the expression `e` at index `i` (in register `r_i`). If `e` reads
only arrays other than `dst` and registers other than `r_i`, and has value `f i` at index `i`,
then `dst` ends as `List.ofFn (fun i => f i)` (`tabProg_exec`), in time `O(N)` for a fixed `e`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Writes `e` at index `0, …, N - 1` into a fresh array `dst`, where `N` is in register `r_n`
and the index is in register `r_i`. -/
def tabProg (dst : Arr) (r_n r_i : Reg) (e : Expr) : Cmd :=
  .seq (.alloc dst (.reg r_n))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_n) (.write dst (.reg r_i) e)))

/-- **The array written entry by entry.** If, in every state that differs from `s` only in `dst`
and in register `r_i` and has `i < N` in register `r_i`, the expression `e` has the value `f i`,
then `tabProg dst r_n r_i e` writes `List.ofFn (fun i => f i)` into `dst`, in time
`≤ (e.cost + 10) N + 6`. It changes no other array and no register other than `r_i`. -/
theorem tabProg_exec {w N : ℕ} (dst : Arr) (r_n r_i : Reg) (e : Expr) (f : ℕ → ℕ)
    (hne : r_n ≠ r_i) (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) {s : State} (hn : s.regs r_n = N)
    (he : ∀ s' : State, (∀ a, a ≠ dst → s'.arrs a = s.arrs a) →
      (∀ r, r ≠ r_i → s'.regs r = s.regs r) → ∀ i < N, s'.regs r_i = i →
        e.eval w s' = some (f i)) :
    ∃ s' t, Exec w (tabProg dst r_n r_i e) s s' t ∧ t ≤ (e.cost + 10) * N + 6 ∧
      s'.arrs dst = List.ofFn (fun i : Fin N => f i.1) ∧
      (∀ a : ℕ, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_i → s'.regs r = s.regs r) := by
  have c0 := checkWord_of_lt (w := w) (v := 0) (by omega)
  have cn := checkWord_of_lt (w := w) (v := N) hN
  let s₁ := s.setArr dst (List.replicate N 0)
  have hex₁ : Exec w (.alloc dst (.reg r_n)) s s₁ (1 + N) :=
    .alloc (by simp only [Expr.eval, hn, cn])
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 := .assign (by simp only [Expr.eval, c0])
  let Inv (k : ℕ) (st : State) : Prop :=
    (st.arrs dst).length = N ∧
    (∀ j (hj : j < (st.arrs dst).length), j < k → (st.arrs dst)[j] = f j) ∧
    st.regs r_n = N ∧ st.regs r_i = k ∧
    (∀ a : ℕ, a ≠ dst → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ r_i → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₂ := by
    refine ⟨by simp [s₂, s₁], fun j _ hj => by omega, ?_, by simp [s₂], fun a ha => ?_,
      fun r hr => ?_⟩
    · simp only [s₂, s₁, State.setReg_regs_ne _ _ hne, State.setArr_regs, hn]
    · simp only [s₂, s₁, State.setReg_arrs]; exact State.setArr_arrs_ne _ _ ha
    · simp only [s₂, s₁, State.setReg_regs_ne _ _ hr, State.setArr_regs]
  have hLoop : ⦃Inv 0⦄[w] forUp r_i (.reg r_n) (.write dst (.reg r_i) e)
      ⦃Inv N⦄ ≤ fun _ => 3 + N * (7 + (e.cost + 2)) := by
    apply Triple.forUp_const Inv N (e.cost + 2) hw hN
    · intro k _ st ⟨_, _, hrn, hri, _, _⟩
      exact ⟨hri, by simp only [Expr.eval, hrn, cn]⟩
    · intro k hk st ⟨hlen, hval, hrn, hri, harr, hreg⟩
      have ck := checkWord_of_lt (w := w) (v := k) (by omega)
      have hek : e.eval w st = some (f k) := he st harr hreg k hk hri
      refine ⟨st.writeArr dst k (f k), 1 + e.cost + 1,
        .write (i := k) (v := f k) (by simp only [Expr.eval, hri, ck]) hek
        (by rw [hlen]; exact hk), by simp only [Expr.cost]; omega,
        ⟨?_, fun j hj hjk => ?_, ?_, by simp, fun a ha => ?_, fun r hr => ?_⟩,
        by simp [State.writeArr, hri]⟩
      · simp [State.writeArr, State.setReg, hlen]
      · simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs_self] at hj ⊢
        rw [List.getElem_set]
        split_ifs with h
        · rw [h]
        · exact hval j (by simpa using hj) (by omega)
      · simp only [State.setReg_regs_ne _ _ hne, State.writeArr, State.setArr_regs, hrn]
      · simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs_ne _ _ ha, harr a ha]
      · simp only [State.setReg_regs_ne _ _ hr, State.writeArr, State.setArr_regs, hreg r hr]
  obtain ⟨s₃, t₃, hex₃, ht₃, hlen₃, hval₃, _, _, harr₃, hreg₃⟩ := hLoop s₂ hInv₀
  have ht₃₀ : t₃ ≤ 3 + N * (7 + (e.cost + 2)) := ht₃
  have ht₃' : t₃ ≤ 3 + N * (e.cost + 9) := by
    have : 3 + N * (7 + (e.cost + 2)) = 3 + N * (e.cost + 9) := by ring
    omega
  refine ⟨s₃, (1 + N) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), ?_, ?_, harr₃, hreg₃⟩
  · have : N * (e.cost + 9) + N = (e.cost + 10) * N := by ring
    omega
  refine List.ext_getElem (by simp [hlen₃]) fun j h₁ h₂ => ?_
  rw [hval₃ j h₁ (by rw [hlen₃] at h₁; exact h₁), List.getElem_ofFn]

end GraphMinor.Compute
