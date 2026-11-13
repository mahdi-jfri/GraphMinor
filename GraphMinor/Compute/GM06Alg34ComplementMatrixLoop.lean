module

public import GraphMinor.Compute.GM06Alg34ComplementMatrixData
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Filling all complement adjacency entries

Scan the flat positions of matrix 28. After each iteration every
position below the scan index equals the finite complement edge bit.
The source arrays and header counts remain fixed, allowing the same
verified lookup at every pair. The scan also handles a zero allocation.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Fill matrix 28 from flat index 186 up to its allocated length. -/
def gm06ComplementMatrixLoopProg : Cmd :=
  forUp 186 (.len 28) gm06ComplementFlatEntryProg

/-- Starting at flat index zero, the scan computes the exact complement
matrix in at most `122 * N² + 3` steps. -/
theorem gm06ComplementMatrixLoopProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = gm06ClosureMatrixData x)
    (hc : s.regs 170 = x.cellCount) (hi : s.regs 186 = 0)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hv : s.arrs 4 = gm06VertexMask vs) (he : s.arrs 6 = gm06EdgeMask x vs)
    (hcap : (s.arrs 28).length = x.cellCount * x.cellCount) :
    ∃ s' t, Exec w gm06ComplementMatrixLoopProg s s' t ∧
      t ≤ 122 * (x.cellCount * x.cellCount) + 3 ∧
      s'.arrs 28 = gm06ComplementMatrixData x vs ∧
      s'.regs 186 = x.cellCount * x.cellCount ∧
      (∀ k : ℕ, k ≠ 28 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 180 → q ≠ 181 → q ≠ 182 → q ≠ 183 → q ≠ 184 → q ≠ 186 →
        s'.regs q = s.regs q) := by
  let N := x.cellCount * x.cellCount
  let I : ℕ → State → Prop := fun i st =>
    st.regs 186 = i ∧
    (∃ hl : (st.arrs 28).length = N,
      ∀ j : Fin N, j.val < i → (st.arrs 28)[j.val]'(by rw [hl]; exact j.isLt) =
        (gm06ComplementMatrixData x vs)[j.val]'(by
          rw [gm06ComplementMatrixData_length]; exact j.isLt)) ∧
    (∀ k : ℕ, k ≠ 28 → st.arrs k = s.arrs k) ∧
    (∀ q : ℕ, q ≠ 180 → q ≠ 181 → q ≠ 182 → q ≠ 183 → q ≠ 184 → q ≠ 186 →
      st.regs q = s.regs q)
  have hhi : ∀ i ≤ N, ∀ st, I i st →
      st.regs 186 = i ∧ (Expr.len 28).eval w st = some N := by
    intro i _ st hs
    obtain ⟨hir, ⟨hlen, _⟩, _, _⟩ := hs
    exact ⟨hir, by simp [Expr.eval, checkWord, hlen, hsquare, N]⟩
  have hbody : ∀ i < N, ∀ st, I i st → ∃ st' t,
      Exec w gm06ComplementFlatEntryProg st st' t ∧ t ≤ 115 ∧
      I (i + 1) (st'.setReg 186 (i + 1)) ∧ st'.regs 186 = i := by
    intro i hiN st hs
    obtain ⟨hir, ⟨hlen, hpfx⟩, harr, hreg⟩ := hs
    have hc' : st.regs 170 = x.cellCount := (hreg _ (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hc
    have hn' : st.regs 100 = x.n := (hreg _ (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hn
    have hm' : st.regs 101 = x.ends.length := (hreg _ (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hm
    obtain ⟨st', t, hex, ht, hbuf, harr', hreg'⟩ :=
      gm06ComplementFlatEntryProg_exec x vs ⟨i, hiN⟩ hw hN hsquare
        ((harr _ (by decide)).trans hmat) hc' hir hn' hm'
        ((harr _ (by decide)).trans hv) ((harr _ (by decide)).trans he) hlen
    refine ⟨st', t, hex, ht, ?_, (hreg' _ (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hir⟩
    have hlen' : (st'.arrs 28).length = N := by rw [hbuf, List.length_set]; exact hlen
    refine ⟨by simp, ⟨hlen', ?_⟩, ?_, ?_⟩
    · intro j hj
      change (st'.arrs 28)[j.val]'(by rw [hlen']; exact j.isLt) = _
      simp only [hbuf, List.getElem_set]
      by_cases heq : i = j.val
      · simpa only [heq, ↓reduceIte] using (gm06ComplementMatrixData_get x vs j).symm
      · rw [ite_eq_right heq]
        exact hpfx j (by omega)
    · intro k hk
      exact (harr' k hk).trans (harr k hk)
    · intro q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆
      change (Function.update st'.regs 186 (i + 1)) q = _
      rw [Function.update_of_ne hq₆]
      exact (hreg' q hq₁ hq₂ hq₃ hq₄ hq₅).trans (hreg q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆)
  have hinit : I 0 s := ⟨hi, ⟨hcap, fun j hj => False.elim (by omega)⟩,
    fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  obtain ⟨s', t, hex, ht, hI⟩ := Crossing.forUp_exec' I N 115 hw hsquare hhi hbody s hinit
  obtain ⟨hir, ⟨hlen, hpfx⟩, harr, hreg⟩ := hI
  refine ⟨s', t, hex, ?_, ?_, hir, harr, hreg⟩
  · simpa only [Expr.cost, Nat.mul_comm, Nat.add_comm, N] using ht
  · apply List.ext_getElem (hlen.trans (gm06ComplementMatrixData_length x vs).symm)
    intro i hi₁ hi₂
    have hiN : i < N := by simpa only [hlen] using hi₁
    exact hpfx ⟨i, hiN⟩ hiN

end GraphMinor.Compute
