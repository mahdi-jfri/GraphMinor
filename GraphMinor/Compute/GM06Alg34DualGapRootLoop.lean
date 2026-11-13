module

public import GraphMinor.Compute.GM06Alg34DualGapRootEntry
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Scanning the canonical dual gap roots

Visit every source gap and write its least-representative flag. The
prefix invariant identifies every completed mask entry. Summing the
cubic source queries gives a quartic bound.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The exact zero-one mask of canonical dual gap representatives. -/
def gm06GapRootMask (x : GM06DrawingData) (L : List (Fin x.n)) : List ℕ :=
  List.ofFn fun i : Fin L.length => if gm06GapIsRoot x L i then 1 else 0

/-- Scan the sources in root-mask allocation 45. -/
def gm06DualGapRootLoopProg : Cmd := forUp 120 (.len 45) gm06DualGapRootEntryProg

/-- The source scan computes every canonical root flag in quartic time. -/
theorem gm06DualGapRootLoopProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    {s : State} (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) (hsource : s.regs 120 = 0)
    (hcap : (s.arrs 45).length = L.length) :
    ∃ s' t, Exec w gm06DualGapRootLoopProg s s' t ∧
      t ≤ 3 + L.length * (340 * (L.length + 1) ^ 3 + 10) ∧
      s'.arrs 45 = gm06GapRootMask x L ∧ s'.regs 120 = L.length ∧
      (∀ A : ℕ, A ≠ 43 → A ≠ 44 → A ≠ 45 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 120 ∨ 273 ≤ q) → q ≠ 0 → s'.regs q = s.regs q) := by
  let I : ℕ → State → Prop := fun j st =>
    st.regs 120 = j ∧
    (∃ hl : (st.arrs 45).length = L.length,
      ∀ b : Fin L.length, b.val < j →
        (st.arrs 45)[b.val]'(by rw [hl]; exact b.isLt) =
          if gm06GapIsRoot x L b then 1 else 0) ∧
    (∀ A : ℕ, A ≠ 43 → A ≠ 44 → A ≠ 45 → st.arrs A = s.arrs A) ∧
    (∀ q : ℕ, (q < 120 ∨ 273 ≤ q) → q ≠ 0 → st.regs q = s.regs q)
  have hhi : ∀ j ≤ L.length, ∀ st, I j st →
      st.regs 120 = j ∧ (Expr.len 45).eval w st = some L.length := by
    intro j _ st hs
    exact ⟨hs.1, by simp [Expr.eval, checkWord, hs.2.1.1, hk]⟩
  have hb : ∀ j < L.length, ∀ st, I j st → ∃ st' t,
      Exec w gm06DualGapRootEntryProg st st' t ∧
      t ≤ 340 * (L.length + 1) ^ 3 + 3 ∧
      I (j + 1) (st'.setReg 120 (j + 1)) ∧ st'.regs 120 = j := by
    intro j hj st hs
    obtain ⟨hjr, ⟨hl, hpfx⟩, harr, hreg⟩ := hs
    obtain ⟨st', t, he, ht, hbuf, hsource', harr', hreg'⟩ :=
      gm06DualGapRootEntryProg_exec x L hLN hDiv ⟨j, hj⟩ hw hk hdouble hn hd
        (by rw [harr 2 (by decide) (by decide) (by decide)]; exact hL)
        (by rw [harr 3 (by decide) (by decide) (by decide)]; exact hD)
        ((hreg 105 (Or.inl (by decide)) (by decide)).trans hbound) hjr hl
    refine ⟨st', t, he, ht, ?_, hsource'⟩
    have hl' : (st'.arrs 45).length = L.length := by rw [hbuf, List.length_set]; exact hl
    refine ⟨by simp, ⟨hl', ?_⟩, ?_, ?_⟩
    · intro b hb
      change (st'.arrs 45)[b.val]'(by rw [hl']; exact b.isLt) = _
      simp only [hbuf, List.getElem_set]
      by_cases heq : j = b.val
      · simp only [heq, ↓reduceIte]
      · rw [ite_eq_right heq]
        exact hpfx b (by omega)
    · intro A h43 h44 h45
      exact (harr' A h43 h44 h45).trans (harr A h43 h44 h45)
    · intro q hq h0
      change (Function.update st'.regs 120 (j + 1)) q = _
      rw [Function.update_of_ne (by omega : q ≠ 120)]
      exact (hreg' q hq h0).trans (hreg q hq h0)
  have hinit : I 0 s := ⟨hsource, ⟨hcap, fun b hb => False.elim (by omega)⟩,
    fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  obtain ⟨s', t, he, ht, hj', ⟨hl, hpfx⟩, harr, hreg⟩ :=
    Crossing.forUp_exec' I L.length (340 * (L.length + 1) ^ 3 + 3)
      (by omega) hk hhi hb s hinit
  refine ⟨s', t, he, ?_, ?_, hj', harr, hreg⟩
  · change t ≤ 3 + L.length * (7 + (340 * (L.length + 1) ^ 3 + 3)) at ht
    have hc : 7 + (340 * (L.length + 1) ^ 3 + 3) =
        340 * (L.length + 1) ^ 3 + 10 := by omega
    rw [hc] at ht
    exact ht
  · apply List.ext_getElem (by simpa only [gm06GapRootMask, List.length_ofFn] using hl)
    intro j hj₁ hj₂
    have hjL : j < L.length := by simpa only [hl] using hj₁
    simpa only [gm06GapRootMask, List.getElem_ofFn] using hpfx ⟨j, hjL⟩ hjL

end GraphMinor.Compute
