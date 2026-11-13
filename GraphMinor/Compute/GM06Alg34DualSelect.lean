module

public import GraphMinor.Compute.GM06Alg34FilterMapArray

/-!
# Allocating a finite selected-list buffer for the dual

Reserve one slot per source word, clear the selected-word counter and
run the read-only filter-and-label scan. The result is the exact chosen
list followed by unused zeros. Its live length is retained for endpoint
selection and length-prefixed region and division serialization.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Allocate array 54 and select labels from the given source array.
Registers 7601–7605 are the scan counters and its live output length. -/
def gm06DualSelectProg (src : ℕ) (test value : Expr) : Cmd :=
  .seq (.assign 7605 (.len src))
    (.seq (.alloc 54 (.reg 7605))
      (.seq (.assign 7604 (.const 0))
        (gm06FilterMapArrayProg src 54 7601 7602 7603 7604 test value)))

/-- A selection emits at most one word per source word. -/
theorem gm06SelectedWords_length_le (keep : ℕ → Bool) (label : ℕ → ℕ) (L : List ℕ) :
    (L.flatMap (fun y => if keep y then [label y] else [])).length ≤ L.length := by
  induction L with
  | nil => simp only [List.flatMap_nil, List.length_nil, le_refl]
  | cons y L ih =>
    cases hy : keep y <;> simp only [List.flatMap_cons, hy, Bool.false_eq_true,
      ↓reduceIte, List.length_append, List.length_cons, List.length_nil] <;> omega

/-- A complete selected-list buffer is computed with linear work in the
source length and constant cost per read-only test and label expression. -/
theorem gm06DualSelectProg_exec {w src : ℕ} (test value : Expr)
    (keep : ℕ → Bool) (label : ℕ → ℕ) (hs54 : src ≠ 54)
    (hw : 1 < 2 ^ w) {L : List ℕ} {s : State}
    (hsource : s.arrs src = L) (hlen : L.length + 2 < 2 ^ w)
    (hwords : ∀ y ∈ L, y < 2 ^ w)
    (htest : ∀ z y, y ∈ L → (∀ A : ℕ, A ≠ 54 → z.arrs A = s.arrs A) →
      (∀ r : ℕ, r < 7601 ∨ 7605 < r → z.regs r = s.regs r) →
      z.regs 7603 = y → test.eval w z = some (if keep y then 1 else 0))
    (hvalue : ∀ z y, y ∈ L → keep y = true →
      (∀ A : ℕ, A ≠ 54 → z.arrs A = s.arrs A) →
      (∀ r : ℕ, r < 7601 ∨ 7605 < r → z.regs r = s.regs r) →
      z.regs 7603 = y → value.eval w z = some (label y)) :
    let out := L.flatMap (fun y => if keep y then [label y] else [])
    ∃ s' t, Exec w (gm06DualSelectProg src test value) s s' t ∧
      t ≤ L.length + 12 + L.length * (10 + (test.cost + value.cost + 6)) ∧
      s'.arrs 54 = out ++ List.replicate (L.length - out.length) 0 ∧
      s'.regs 7604 = out.length ∧
      (∀ A : ℕ, A ≠ 54 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7601 ∨ 7605 < r → s'.regs r = s.regs r) := by
  let s₁ := s.setReg 7605 L.length
  let s₂ := s₁.setArr 54 (List.replicate L.length 0)
  let s₃ := s₂.setReg 7604 0
  have he₁ : Exec w (.assign 7605 (.len src)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hsource, show L.length < 2 ^ w by omega])
  have he₂ : Exec w (.alloc 54 (.reg 7605)) s₁ s₂ (1 + L.length) :=
    .alloc (by simp [Expr.eval, checkWord, s₁, show L.length < 2 ^ w by omega])
  have he₃ : Exec w (.assign 7604 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have ha₃ (A : ℕ) (hA : A ≠ 54) : s₃.arrs A = s.arrs A := by
    simp [s₃, s₂, s₁, State.setArr, hA]
  have hr₃ (r : ℕ) (hr : r < 7601 ∨ 7605 < r) : s₃.regs r = s.regs r := by
    have h4 : r ≠ 7604 := by omega
    have h5 : r ≠ 7605 := by omega
    simp [s₃, s₂, s₁, State.setReg, h4, h5]
  obtain ⟨s₄, t₄, he₄, ht₄, hb₄, ha₄, hr₄⟩ :=
    gm06FilterMapArrayProg_exec (s := s₃) src 54 7601 7602 7603 7604 test value keep label
      hs54 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw ((ha₃ src hs54).trans hsource) (by omega) hwords
      (pre := []) (cap := L.length) (by simp [IsBuf, s₃, s₂, s₁])
      (gm06SelectedWords_length_le keep label L) (by simpa only [List.length_nil, Nat.zero_add] using hlen)
      (fun z y hy ha hr hry => htest z y hy
        (fun A hA => (ha A hA).trans (ha₃ A hA))
        (fun r hrr => (hr r (by omega) (by omega) (by omega) (by omega)).trans (hr₃ r hrr)) hry)
      (fun z y hy hk ha hr hry => hvalue z y hy hk
        (fun A hA => (ha A hA).trans (ha₃ A hA))
        (fun r hrr => (hr r (by omega) (by omega) (by omega) (by omega)).trans (hr₃ r hrr)) hry)
  refine ⟨s₄, 2 + ((1 + L.length) + (2 + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)),
    by omega, ?_, ?_, ?_, ?_⟩
  · simpa only [IsBuf, List.nil_append] using hb₄.1
  · simpa only [List.nil_append] using hb₄.2
  · intro A hA
    exact (ha₄ A hA).trans (ha₃ A hA)
  · intro r hr
    have h1 : r ≠ 7601 := by
      rcases hr with h | h <;> omega
    have h2 : r ≠ 7602 := by rcases hr with h | h <;> omega
    have h3 : r ≠ 7603 := by rcases hr with h | h <;> omega
    have h4 : r ≠ 7604 := by rcases hr with h | h <;> omega
    exact (hr₄ r h1 h2 h3 h4).trans (hr₃ r hr)

end GraphMinor.Compute
