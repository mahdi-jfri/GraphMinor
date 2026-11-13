module

public import GraphMinor.Compute.TwoPathsRotate

/-!
# Lines 2 and 5 of Algorithm 5.1: find a `C`-path between two vertices that are apart

`findProg` reads the instance (`H` in arrays `aStart`, `aEnd`, `aEnt` and the cycle `C` in
`aCyc`) and decides whether some `C`-path joins two vertices of `C` that are not consecutive on
`C`. When there is none, `C` is crossless (line 3). When there is one, from `a` to `b` say, it
rotates `C` to the form `a A b B` and writes the path in `aPath`, which is the instance that lines
6 to 11 work on.

The steps are: mark `C` (`cycSetup`), look for a chord (`chordScan`), sweep the components of
`H - C` (`sweepProg`), and if a pair was found, build the path (`pathProg`) and rotate the cycle
(`rotProg`). A cycle with fewer than four vertices has no crossing, and `findProg` answers at once.
The whole program takes `O(n + m)` steps.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {n : ℕ}

/-- A tuple with fewer than four entries has no crossing: a crossing needs four indices. -/
theorem not_isCrossed_of_short {V : Type*} {G : SimpleGraph V} {T : List V} (hk : T.length < 4) :
    ¬ IsCrossed G T := by
  rintro ⟨a, b, c, d, Q, R, ⟨i, r, j, t, h1, h2, h3, -, -, -, ht⟩, -⟩
  have := (List.getElem?_eq_some_iff.mp ht).1
  omega

/-- The main part of `findProg`, for cycles with at least four vertices. -/
def findMain : Cmd :=
  .seq cycSetup (.seq chordScan (.seq sweepProg
    (.ite (.op .eq (.reg rFound) (.const 1)) (.seq pathProg rotProg) .skip)))

/-- **Lines 2 and 5 of Algorithm 5.1.** -/
def findProg : Cmd :=
  .ite (.op .lt (.len aCyc) (.const 4)) (.assign rFound (.const 0)) findMain

/-- The registers that `findProg` writes. -/
def findRegs : List ℕ := rLenA :: List.range' 60 39

/-- The arrays that `findProg` writes. -/
def findArrs : List ℕ := [aLab, aPar, aQue, aSrc, aPos, aTmp, aCyc, aPath]

/-- The result of `findProg`: no crossing, or the cycle rotated to `a A b B` and a `C`-path from `a`
to `b`. -/
def FindRes (H : SimpleGraph (Fin n)) (T : List (Fin n)) (s : State) : Prop :=
  (s.regs rFound = 0 ∧ ¬ IsCrossed H T) ∨
    (s.regs rFound = 1 ∧ ∃ (a b : Fin n) (A B : List (Fin n)) (P : H.Walk a b),
      T.rotate (T.idxOf a) = a :: A ++ b :: B ∧ A ≠ [] ∧ B ≠ [] ∧ IsTPath H T P ∧
      s.arrs aCyc = (a :: A ++ b :: B).map Fin.val ∧ s.arrs aPath = P.support.map Fin.val ∧
      s.regs rLenA = A.length)

theorem findMain_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hk4 : 4 ≤ T.length) (hn : 4 * n + 4 < 2 ^ w) (s : State)
    (hcyc : s.arrs aCyc = T.map Fin.val) (h40 : s.regs 40 = n)
    (hadj : IsAdjList H aStart aEnd aEnt lists s) (hent : (s.arrs aEnt).length < 2 ^ w) :
    ∃ s' t, Exec w findMain s s' t ∧ t ≤ 142 + 219 * n + 208 * totalAdjEntries lists ∧
      Keeps findRegs findArrs s s' ∧ FindRes H T s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  -- Mark the cycle.
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hrk₁, hpos₁, hlab₁⟩ := cycSetup_exec T hT hnw hw4 s hcyc h40
  have hpre₁ : ChordPre H lists T s₁ :=
    ⟨hadj.of_arrs_eq (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide)),
      by rw [hk₁.2 _ (by decide)]; exact hcyc, hpos₁, hrk₁, by rw [hk₁.1 _ (by decide)]; exact h40⟩
  have hent₁ : (s₁.arrs aEnt).length < 2 ^ w := by rw [hk₁.2 _ (by decide)]; exact hent
  -- The chords.
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hch⟩ := chordScan_exec H lists T hT hk4 hn s₁ hpre₁ hent₁
  have hpre₂ := hpre₁.keeps hk₂
  have hent₂ : (s₂.arrs aEnt).length < 2 ^ w := by rw [hk₂.2 _ (by simp)]; exact hent₁
  -- The sweep.
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, items, hres⟩ := sweepProg_exec H lists T hT hk4 hn s₂
    ⟨hpre₂.adj, hpre₂.pos, hpre₂.k, hpre₂.n⟩ hent₂ (by rw [hk₂.2 _ (by simp)]; exact hlab₁) hch
  have hk₀₃ : Keeps findRegs findArrs s s₃ :=
    (((hk₁.mono (R' := findRegs) (A' := findArrs) (by decide) (by decide)).trans hk₂ (by decide)
      (by decide)).trans hk₃ (by decide) (by decide))
  have hcond : ∀ st : State, st.regs rFound ≤ 1 →
      (Expr.op .eq (.reg rFound) (.const 1)).eval w st = some (if st.regs rFound = 1 then 1 else 0) :=
    fun st h => eq_eval (reg_eval rfl (by omega)) (by simp [checkWord, hw1]) hw1
  rcases hres with ⟨h0, hno, hnc, hall⟩ | ⟨h1, hpair⟩
  · -- No pair: the cycle is crossless.
    refine ⟨s₃, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.ite_false (by rw [hcond s₃ (by omega), h0]; rfl)
      (.skip s₃)))), ?_, hk₀₃, Or.inl ⟨h0, not_isCrossed_of_sweep hT hno hnc hall⟩⟩
    simp only [Expr.cost]; omega
  · -- A pair: the path and the rotation.
    have hcyc₃ : s₃.arrs aCyc = T.map Fin.val := by rw [hk₃.2 _ (by decide)]; exact hpre₂.cyc
    have h40₃ : s₃.regs 40 = n := by rw [hk₃.1 _ (by decide)]; exact hpre₂.n
    have hadj₃ : IsAdjList H aStart aEnd aEnt lists s₃ :=
      hpre₂.adj.of_arrs_eq (hk₃.2 _ (by decide)) (hk₃.2 _ (by decide)) (hk₃.2 _ (by decide))
    have hent₃ : (s₃.arrs aEnt).length < 2 ^ w := by rw [hk₃.2 _ (by decide)]; exact hent₂
    obtain ⟨s₄, t₄, x, y, P, hex₄, ht₄, hrx, hry, hx, hy, hap, hTP, hpath₄, hk₄, hpos₄, hrk₄⟩ :=
      pathProg_exec H lists T hT hn s₃ hcyc₃ h40₃ hadj₃ hent₃ hpair
    obtain ⟨s₅, t₅, A, B, hex₅, ht₅, hrot, hA, hB, hcyc₅, hlen₅, hk₅⟩ := rotProg_exec T hT hn x y hx
      hy hap s₄ (by rw [hk₄.2 _ (by decide)]; exact hcyc₃) hpos₄ hrk₄
      (by rw [hk₄.1 _ (by decide)]; exact hrx) (by rw [hk₄.1 _ (by decide)]; exact hry)
    refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.ite_true (hcond s₃ (by omega)) (by simp [h1])
      (.seq hex₄ hex₅)))), ?_, ?_, Or.inr ⟨?_, x, y, A, B, P, hrot, hA, hB, hTP, hcyc₅, ?_, hlen₅⟩⟩
    · simp only [Expr.cost]; omega
    · exact (hk₀₃.trans hk₄ (by decide) (by decide)).trans hk₅ (by decide) (by decide)
    · rw [hk₅.1 _ (by decide), hk₄.1 _ (by decide)]; exact h1
    · rw [hk₅.2 _ (by decide)]; exact hpath₄

/-- **Lines 2 and 5 of Algorithm 5.1.** `findProg` either finds that `C` is crossless, or rotates
`C` to the form `a A b B` with `A` and `B` not empty and writes a `C`-path from `a` to `b` in
`aPath`. It takes at most `145 + 219 n + 208 m` steps. -/
theorem findProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hn : 4 * n + 4 < 2 ^ w) (s : State)
    (hcyc : s.arrs aCyc = T.map Fin.val) (h40 : s.regs 40 = n)
    (hadj : IsAdjList H aStart aEnd aEnt lists s) (hent : (s.arrs aEnt).length < 2 ^ w) :
    ∃ s' t, Exec w findProg s s' t ∧ t ≤ 145 + 219 * n + 208 * totalAdjEntries lists ∧
      Keeps findRegs findArrs s s' ∧ FindRes H T s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  have hlen : (Expr.len aCyc).eval w s = some T.length := by
    simp [Expr.eval, checkWord, hcyc]; omega
  have hc := lt_eval hlen (show (Expr.const 4).eval w s = some 4 by simp [checkWord]; omega) hw1
  by_cases hk4 : 4 ≤ T.length
  · obtain ⟨s', t, hex, ht, hk, hres⟩ := findMain_exec H lists T hT hk4 hn s hcyc h40 hadj hent
    refine ⟨s', _, .ite_false (by rw [hc, ite_eq_right_iff.mpr (fun h => absurd h (by omega))]) hex, ?_, hk, hres⟩
    simp only [Expr.cost]; omega
  · refine ⟨s.setReg rFound 0, _, .ite_true hc (by simp; omega)
      (.assign (show (Expr.const 0).eval w s = some 0 by simp [checkWord])), ?_,
      (Keeps.refl _ _ s).setReg (by decide) _, Or.inl ⟨by simp, not_isCrossed_of_short (by omega)⟩⟩
    simp only [Expr.cost]; omega

end GraphMinor.Compute.TwoPaths
