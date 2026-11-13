module

public import GraphMinor.Compute.GM06Alg34VertexRootMaskEntry
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Computing all canonical component-root flags

Scan vertex source labels in increasing order. Each iteration runs a
root query and fills one root-mask entry. The invariant states that
all earlier flags agree with the finite canonical root predicate. The
source graph and masks are preserved throughout the scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- One canonical root bit per original vertex label. -/
def gm06VertexRootMask (x : GM06DrawingData)  : List ℕ :=
  List.ofFn (fun a : Fin x.n => if x.isComponentRoot a then 1 else 0)

/-- Scan source register 187 through the root-mask allocation 36. -/
def gm06VertexRootMaskLoopProg : Cmd := forUp 187 (.len 36) gm06VertexRootMaskEntryProg

/-- The root scan computes every canonical root flag in cubic time,
preserving the supplied drawing and vertex CSR lists. -/
theorem gm06VertexRootMaskLoopProg_exec {w : ℕ} (x : GM06DrawingData) 
    (hw : 1 < 2 ^ w) (hN : x.n < 2 ^ w)
    (hsquare : x.n * x.n < 2 ^ w) {s : State}
    (hsize : s.regs 4 = x.n) (hsource : s.regs 187 = 0)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n)
    (hcap : (s.arrs 36).length = x.n) :
    ∃ s' t, Exec w gm06VertexRootMaskLoopProg s s' t ∧
      t ≤ x.n * (26 * (x.n * x.n) + 46 * x.n + 80) + 3 ∧
      s'.arrs 36 = gm06VertexRootMask x ∧ s'.regs 187 = x.n ∧
      (∀ k : ℕ, k ≠ 33 → k ≠ 34 → k ≠ 35 → k ≠ 36 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, (q < 190 ∨ 201 ≤ q) → q ≠ 187 → s'.regs q = s.regs q) := by
  let I : ℕ → State → Prop := fun i st =>
    st.regs 187 = i ∧
    (∃ hl : (st.arrs 36).length = x.n,
      ∀ a : Fin x.n, a.val < i → (st.arrs 36)[a.val]'(by rw [hl]; exact a.isLt) =
        if x.isComponentRoot a then 1 else 0) ∧
    (∀ k : ℕ, k ≠ 33 → k ≠ 34 → k ≠ 35 → k ≠ 36 → st.arrs k = s.arrs k) ∧
    (∀ q : ℕ, (q < 190 ∨ 201 ≤ q) → q ≠ 187 → st.regs q = s.regs q)
  have hhi : ∀ i ≤ x.n, ∀ st, I i st →
      st.regs 187 = i ∧ (Expr.len 36).eval w st = some x.n := by
    intro i _ st hs
    obtain ⟨hir, ⟨hl, _⟩, _, _⟩ := hs
    exact ⟨hir, by simp [Expr.eval, checkWord, hl, hN]⟩
  have hbody : ∀ i < x.n, ∀ st, I i st → ∃ st' t,
      Exec w gm06VertexRootMaskEntryProg st st' t ∧
      t ≤ 26 * (x.n * x.n) + 46 * x.n + 73 ∧
      I (i + 1) (st'.setReg 187 (i + 1)) ∧ st'.regs 187 = i := by
    intro i hi st hs
    obtain ⟨hir, ⟨hl, hpfx⟩, harr, hreg⟩ := hs
    have hsize' : st.regs 4 = x.n := (hreg _ (Or.inl (by decide)) (by decide)).trans hsize
    have hlists' : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) st :=
      hlists.of_arrs_eq (harr _ (by decide) (by decide) (by decide) (by decide))
        (harr _ (by decide) (by decide) (by decide) (by decide))
        (harr _ (by decide) (by decide) (by decide) (by decide))
    obtain ⟨st', t, hex, ht, hbuf, harr', hreg'⟩ :=
      gm06VertexRootMaskEntryProg_exec x ⟨i, hi⟩ hw hN hsquare hsize' hir
        hlists' (by rw [harr _ (by decide) (by decide) (by decide) (by decide)]; exact hlen) hl
    refine ⟨st', t, hex, ht, ?_, (hreg' _ (Or.inl (by decide))).trans hir⟩
    have hl' : (st'.arrs 36).length = x.n := by rw [hbuf, List.length_set]; exact hl
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
    Crossing.forUp_exec' I x.n
      (26 * (x.n * x.n) + 46 * x.n + 73) hw hN hhi hbody s hinit
  refine ⟨s', t, hex, ?_, ?_, hir, harr, hreg⟩
  · change t ≤ 3 + x.n *
      (7 + (26 * (x.n * x.n) + 46 * x.n + 73)) at ht
    have hcost : 7 + (26 * (x.n * x.n) + 46 * x.n + 73) =
        26 * (x.n * x.n) + 46 * x.n + 80 := by omega
    rw [hcost] at ht
    omega
  · apply List.ext_getElem (by simpa only [gm06VertexRootMask, List.length_ofFn] using hl)
    intro i hi₁ hi₂
    have hi : i < x.n := by simpa only [hl] using hi₁
    simpa only [gm06VertexRootMask, List.getElem_ofFn] using hpfx ⟨i, hi⟩ hi

end GraphMinor.Compute
