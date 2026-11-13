module

public import GraphMinor.Compute.GM06Alg34DualGapRowEntry
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Computing a row of the dual gap relation

Visit each gap column and record its relation to the fixed source gap.
The loop invariant records all completed columns and preserves the
supplied cuff and block tables. Summing the quadratic queries gives a
cubic row bound.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The zero-one relation row of a supplied source gap. -/
def gm06GapRow (x : GM06DrawingData) (L : List (Fin x.n))
    (i : Fin L.length) : List ℕ :=
  List.ofFn fun j : Fin L.length => if x.dualGapRelated L i j then 1 else 0

/-- Scan all columns of row allocation 43. -/
def gm06GapRowLoopProg : Cmd := forUp 121 (.len 43) gm06GapRowEntryProg

/-- Every column of the finite dual relation row is computed in cubic
time, preserving the source gap and the supplied input tables. -/
theorem gm06GapRowLoopProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    (i : Fin L.length) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) (hi : s.regs 120 = i.val)
    (hj : s.regs 121 = 0) (hcap : (s.arrs 43).length = L.length) :
    ∃ s' t, Exec w gm06GapRowLoopProg s s' t ∧
      t ≤ 3 + L.length * (250 * (L.length + 1) ^ 2 + 10) ∧
      s'.arrs 43 = gm06GapRow x L i ∧ s'.regs 121 = L.length ∧
      (∀ a : ℕ, a ≠ 43 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 121 → q ≠ 122 → q ≠ 123 → q ≠ 124 → q ≠ 125 →
        s'.regs q = s.regs q) := by
  let I : ℕ → State → Prop := fun j st =>
    st.regs 121 = j ∧
    (∃ hl : (st.arrs 43).length = L.length,
      ∀ b : Fin L.length, b.val < j →
        (st.arrs 43)[b.val]'(by rw [hl]; exact b.isLt) =
          if x.dualGapRelated L i b then 1 else 0) ∧
    (∀ a, a ≠ 43 → st.arrs a = s.arrs a) ∧
    (∀ q, q ≠ 0 → q ≠ 121 → q ≠ 122 → q ≠ 123 → q ≠ 124 → q ≠ 125 →
      st.regs q = s.regs q)
  have hhi : ∀ j ≤ L.length, ∀ st, I j st →
      st.regs 121 = j ∧ (Expr.len 43).eval w st = some L.length := by
    intro j _ st hs
    exact ⟨hs.1, by simp [Expr.eval, checkWord, hs.2.1.1, hk]⟩
  have hb : ∀ j < L.length, ∀ st, I j st → ∃ st' t,
      Exec w gm06GapRowEntryProg st st' t ∧
      t ≤ 250 * (L.length + 1) ^ 2 + 3 ∧
      I (j + 1) (st'.setReg 121 (j + 1)) ∧ st'.regs 121 = j := by
    intro j hj st hs
    obtain ⟨hjr, ⟨hl, hpfx⟩, harr, hreg⟩ := hs
    obtain ⟨st', t, he, ht, hbuf, harr', hreg'⟩ :=
      gm06GapRowEntryProg_exec x L hLN hDiv i ⟨j, hj⟩ hw hk hdouble hn hd
        (by rw [harr 2 (by decide)]; exact hL)
        (by rw [harr 3 (by decide)]; exact hD)
        ((hreg 105 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbound)
        ((hreg 120 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi)
        hjr hl
    refine ⟨st', t, he, ht, ?_,
      (hreg' 121 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hjr⟩
    have hl' : (st'.arrs 43).length = L.length := by rw [hbuf, List.length_set]; exact hl
    refine ⟨by simp, ⟨hl', ?_⟩, ?_, ?_⟩
    · intro b hb
      change (st'.arrs 43)[b.val]'(by rw [hl']; exact b.isLt) = _
      simp only [hbuf, List.getElem_set]
      by_cases heq : j = b.val
      · simp only [heq, ↓reduceIte]
      · rw [ite_eq_right heq]
        exact hpfx b (by omega)
    · intro a ha
      exact (harr' a ha).trans (harr a ha)
    · intro q hq h121 h122 h123 h124 h125
      rw [State.setReg_regs_ne _ _ h121]
      exact (hreg' q hq h122 h123 h124 h125).trans
        (hreg q hq h121 h122 h123 h124 h125)
  have hinit : I 0 s := ⟨hj, ⟨hcap, fun b hb => False.elim (by omega)⟩,
    fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  obtain ⟨s', t, he, ht, hj', ⟨hl, hpfx⟩, harr, hreg⟩ :=
    Crossing.forUp_exec' I L.length (250 * (L.length + 1) ^ 2 + 3)
      (by omega) hk hhi hb s hinit
  refine ⟨s', t, he, ?_, ?_, hj', harr, hreg⟩
  · change t ≤ 3 + L.length * (7 + (250 * (L.length + 1) ^ 2 + 3)) at ht
    have hc : 7 + (250 * (L.length + 1) ^ 2 + 3) =
        250 * (L.length + 1) ^ 2 + 10 := by omega
    rw [hc] at ht
    exact ht
  · apply List.ext_getElem (by simpa only [gm06GapRow, List.length_ofFn] using hl)
    intro j hj₁ hj₂
    have hjL : j < L.length := by simpa only [hl] using hj₁
    simpa only [gm06GapRow, List.getElem_ofFn] using hpfx ⟨j, hjL⟩ hjL

end GraphMinor.Compute
