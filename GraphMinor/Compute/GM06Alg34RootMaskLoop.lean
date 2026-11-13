module

public import GraphMinor.Compute.GM06Alg34RootMaskEntry
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Computing all canonical region-root flags

Scan packed source labels in increasing order. Each iteration runs a
root query and fills one root-mask entry. The invariant states that
all earlier flags agree with the finite canonical root predicate. The
source graph and masks are preserved throughout the scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- One canonical root bit per original packed cell label. -/
def gm06RootMask (x : GM06DrawingData) (vs : List (Fin x.n)) : List ℕ :=
  List.ofFn (fun a : Fin x.cellCount => if x.isRegionRoot vs a then 1 else 0)

/-- Scan source register 187 through the root-mask allocation 36. -/
def gm06RootMaskLoopProg : Cmd := forUp 187 (.len 36) gm06RootMaskEntryProg

/-- The root scan computes every canonical root flag in cubic time,
preserving the supplied drawing and complement CSR lists. -/
theorem gm06RootMaskLoopProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) {s : State}
    (hsize : s.regs 4 = x.cellCount) (hsource : s.regs 187 = 0)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hv : s.arrs 4 = gm06VertexMask vs) (he : s.arrs 6 = gm06EdgeMask x vs)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount)
    (hcap : (s.arrs 36).length = x.cellCount) :
    ∃ s' t, Exec w gm06RootMaskLoopProg s s' t ∧
      t ≤ x.cellCount * (26 * (x.cellCount * x.cellCount) + 46 * x.cellCount + 80) + 3 ∧
      s'.arrs 36 = gm06RootMask x vs ∧ s'.regs 187 = x.cellCount ∧
      (∀ k : ℕ, k ≠ 33 → k ≠ 34 → k ≠ 35 → k ≠ 36 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, (q < 190 ∨ 201 ≤ q) → q ≠ 187 → s'.regs q = s.regs q) := by
  let I : ℕ → State → Prop := fun i st =>
    st.regs 187 = i ∧
    (∃ hl : (st.arrs 36).length = x.cellCount,
      ∀ a : Fin x.cellCount, a.val < i → (st.arrs 36)[a.val]'(by rw [hl]; exact a.isLt) =
        if x.isRegionRoot vs a then 1 else 0) ∧
    (∀ k : ℕ, k ≠ 33 → k ≠ 34 → k ≠ 35 → k ≠ 36 → st.arrs k = s.arrs k) ∧
    (∀ q : ℕ, (q < 190 ∨ 201 ≤ q) → q ≠ 187 → st.regs q = s.regs q)
  have hhi : ∀ i ≤ x.cellCount, ∀ st, I i st →
      st.regs 187 = i ∧ (Expr.len 36).eval w st = some x.cellCount := by
    intro i _ st hs
    obtain ⟨hir, ⟨hl, _⟩, _, _⟩ := hs
    exact ⟨hir, by simp [Expr.eval, checkWord, hl, hN]⟩
  have hbody : ∀ i < x.cellCount, ∀ st, I i st → ∃ st' t,
      Exec w gm06RootMaskEntryProg st st' t ∧
      t ≤ 26 * (x.cellCount * x.cellCount) + 46 * x.cellCount + 73 ∧
      I (i + 1) (st'.setReg 187 (i + 1)) ∧ st'.regs 187 = i := by
    intro i hi st hs
    obtain ⟨hir, ⟨hl, hpfx⟩, harr, hreg⟩ := hs
    have hsize' : st.regs 4 = x.cellCount := (hreg _ (Or.inl (by decide)) (by decide)).trans hsize
    have hn' : st.regs 100 = x.n := (hreg _ (Or.inl (by decide)) (by decide)).trans hn
    have hm' : st.regs 101 = x.ends.length := (hreg _ (Or.inl (by decide)) (by decide)).trans hm
    have hlists' : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) st :=
      hlists.of_arrs_eq (harr _ (by decide) (by decide) (by decide) (by decide))
        (harr _ (by decide) (by decide) (by decide) (by decide))
        (harr _ (by decide) (by decide) (by decide) (by decide))
    obtain ⟨st', t, hex, ht, hbuf, harr', hreg'⟩ :=
      gm06RootMaskEntryProg_exec x vs ⟨i, hi⟩ hw hN hsquare hsize' hir hn' hm'
        ((harr _ (by decide) (by decide) (by decide) (by decide)).trans hv)
        ((harr _ (by decide) (by decide) (by decide) (by decide)).trans he)
        hlists' (by rw [harr _ (by decide) (by decide) (by decide) (by decide)]; exact hlen) hl
    refine ⟨st', t, hex, ht, ?_, (hreg' _ (Or.inl (by decide))).trans hir⟩
    have hl' : (st'.arrs 36).length = x.cellCount := by rw [hbuf, List.length_set]; exact hl
    refine ⟨by simp, ⟨hl', ?_⟩, ?_, ?_⟩
    · intro a ha
      change (st'.arrs 36)[a.val]'(by rw [hl']; exact a.isLt) = _
      simp only [hbuf, List.getElem_set]
      by_cases heq : i = a.val
      · simp only [heq, ↓reduceIte]
      · rw [ite_eq_right heq]
        exact hpfx a (by omega)
    · intro k hk₁ hk₂ hk₃ hk₄
      exact (harr' k hk₁ hk₂ hk₃ hk₄).trans (harr k hk₁ hk₂ hk₃ hk₄)
    · intro q hq hq'
      change (Function.update st'.regs 187 (i + 1)) q = _
      rw [Function.update_of_ne hq']
      exact (hreg' q hq).trans (hreg q hq hq')
  have hinit : I 0 s := ⟨hsource, ⟨hcap, fun a ha => False.elim (by omega)⟩,
    fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  obtain ⟨s', t, hex, ht, hir, ⟨hl, hpfx⟩, harr, hreg⟩ :=
    Crossing.forUp_exec' I x.cellCount
      (26 * (x.cellCount * x.cellCount) + 46 * x.cellCount + 73) hw hN hhi hbody s hinit
  refine ⟨s', t, hex, ?_, ?_, hir, harr, hreg⟩
  · change t ≤ 3 + x.cellCount *
      (7 + (26 * (x.cellCount * x.cellCount) + 46 * x.cellCount + 73)) at ht
    have hcost : 7 + (26 * (x.cellCount * x.cellCount) + 46 * x.cellCount + 73) =
        26 * (x.cellCount * x.cellCount) + 46 * x.cellCount + 80 := by omega
    rw [hcost] at ht
    omega
  · apply List.ext_getElem (by simpa only [gm06RootMask, List.length_ofFn] using hl)
    intro i hi₁ hi₂
    have hi : i < x.cellCount := by simpa only [hl] using hi₁
    simpa only [gm06RootMask, List.getElem_ofFn] using hpfx ⟨i, hi⟩ hi

end GraphMinor.Compute
