module

public import GraphMinor.Compute.Parse
public import GraphMinor.Compute.Logic

/-!
# Counting the tails for the output of Algorithm (9.9)

The decomposition returned by (7.2) uses the active-pair edge order. To write
output (i) of the caller interface, edges must be grouped by tail. This file
proves the counting pass of that conversion. Each source word is a vertex
number. The program counts its occurrences in a separate array in linear time.
Loops and parallel edges require no special cases.
-/

@[expose] public section
namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Read one tail and increment its bucket. -/
def alg99TailCountBody (a_src a_count r : ℕ) : Cmd :=
  .seq (.assign (r + 1) (.read a_src (.reg r)))
    (incArrAt a_count (r + 1) (r + 2))

/-- Count the vertex numbers in the source array, starting with zero buckets. -/
def alg99TailCountProg (a_src a_count r r_n : ℕ) : Cmd :=
  .seq (.alloc a_count (.reg r_n))
    (.seq (.assign r (.const 0))
      (forUp r (.len a_src) (alg99TailCountBody a_src a_count r)))

private theorem count_take_succ99 {n : ℕ} (xs : List (Fin n)) (k : ℕ)
    (hk : k < xs.length) (v : Fin n) :
    (xs.take (k + 1)).count v =
      if v = xs[k] then (xs.take k).count (xs[k]) + 1 else (xs.take k).count v := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.count_append, List.count_singleton, beq_iff_eq]
  by_cases h : v = xs[k]
  · simp [h]
  · simp [h, Ne.symm h]

/-- The counting pass writes the exact occurrence counts, in time linear in
both the number of vertices and the source length. Only the bucket array and
three scratch registers can change. -/
theorem alg99TailCountProg_exec {w n : ℕ} (xs : List (Fin n))
    (a_src a_count r r_n : ℕ) (hne : a_src ≠ a_count)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hlen : xs.length < 2 ^ w)
    (s : State) (hsrc : s.arrs a_src = xs.map Fin.val) (hrn : s.regs r_n = n) :
    ∃ s' t, Exec w (alg99TailCountProg a_src a_count r r_n) s s' t ∧
      t ≤ n + 20 * xs.length + 6 ∧
      s'.arrs a_count = List.ofFn (fun v : Fin n => xs.count v) ∧
      (∀ a : ℕ, a ≠ a_count → s'.arrs a = s.arrs a) ∧
      (∀ j : ℕ, j ≠ r → j ≠ r + 1 → j ≠ r + 2 → s'.regs j = s.regs j) := by
  let s₀ := s.setArr a_count (List.replicate n 0)
  have hex₀ : Exec w (.alloc a_count (.reg r_n)) s s₀ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn])
  let I : ℕ → State → Prop := fun k st =>
    st.arrs a_src = xs.map Fin.val ∧ st.regs r = k ∧
      ∃ hh : (st.arrs a_count).length = n,
        ∀ v : Fin n, (st.arrs a_count)[v.1]'(by rw [hh]; exact v.2) =
          (xs.take k).count v
  have hloop : ⦃I 0⦄[w]
      forUp r (.len a_src) (alg99TailCountBody a_src a_count r)
      ⦃I xs.length⦄ ≤ fun _ => 3 + xs.length * 19 := by
    apply Triple.forUp_const I xs.length 12 hw hlen
    · intro k _ st hI
      exact ⟨hI.2.1, by simp [Expr.eval, checkWord, hI.1, hlen]⟩
    · intro k hk st hI
      obtain ⟨hs, hr, hh, hv⟩ := hI
      have hk_w : k < 2 ^ w := hk.trans hlen
      have hx_w : (xs[k]).1 < 2 ^ w := (xs[k]).2.trans hn
      let st₁ := st.setReg (r + 1) (xs[k]).1
      have hex₁ : Exec w (.assign (r + 1) (.read a_src (.reg r))) st st₁ 3 := by
        apply Exec.assign
        simp [Expr.eval, checkWord, hr, hk_w, hs, hk, hx_w]
      have hcnt : (xs.take k).count (xs[k]) + 1 < 2 ^ w := by
        have hc := List.count_le_length (a := xs[k]) (l := xs.take k)
        have ht : (xs.take k).length ≤ k := by simp
        omega
      obtain ⟨st₂, t₂, hex₂, ht₂, hh₂, ha₂, hr₂⟩ :=
        incArrAt_exec a_count (r + 1) (r + 2) (fun v => (xs.take k).count v)
          xs[k] st₁ (by romega) hw hn hcnt (by exact hh)
          (by simp [st₁]) (by exact hv)
      have hreg : st₂.regs r = k := by
        rw [hr₂ r (by romega)]
        simpa [st₁, show r ≠ r + 1 by omega] using hr
      refine ⟨st₂, 3 + t₂, .seq hex₁ hex₂, by dsimp only; omega, ?_, hreg⟩
      dsimp only [I, State.setReg_arrs]
      refine ⟨?_, by simp, hh₂.1, ?_⟩
      · simpa [st₁] using (ha₂ a_src hne).trans hs
      · intro v
        change (st₂.arrs a_count)[v.1]'(by rw [hh₂.1]; exact v.2) = _
        exact (hh₂.2 v).trans (count_take_succ99 xs k hk v).symm
  let si := s₀.setReg r 0
  have hexi : Exec w (.assign r (.const 0)) s₀ si 2 :=
    .assign (by simp [Expr.eval, checkWord])
  have hIinit : I 0 si := by
    refine ⟨?_, by simp [si], by simp [si, s₀], ?_⟩
    · simp [si, s₀, hne, hsrc]
    · intro v
      simp [si, s₀]
  obtain ⟨s', t, hex, ht, hI'⟩ := hloop si hIinit
  have hexall : Exec w (alg99TailCountProg a_src a_count r r_n) s s'
      ((1 + n) + (2 + t)) := .seq hex₀ (.seq hexi hex)
  refine ⟨s', (1 + n) + (2 + t), hexall, by dsimp only at ht; omega, ?_, ?_, ?_⟩
  · apply List.ext_getElem (by simp [hI'.2.2.1])
    intro j hj hj'
    have hjn : j < n := by simpa using hj'
    rw [hI'.2.2.2 ⟨j, hjn⟩]
    simp
  · intro a ha
    apply hexall.arrs_eq_of_not_mem_writtenArrs
    simp [alg99TailCountProg, alg99TailCountBody, incArrAt, forUp, ha]
  · intro j hj hj1 hj2
    apply hexall.regs_eq_of_not_mem_writtenRegs
    simp [alg99TailCountProg, alg99TailCountBody, incArrAt, forUp, hj, hj1, hj2]

end GraphMinor.Compute
