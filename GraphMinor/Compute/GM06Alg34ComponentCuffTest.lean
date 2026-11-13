module

public import GraphMinor.Compute.GM06Alg34UnreachedList

/-!
# Testing a cuff against computed component marks

Restore the saved cuff-label offset, read its length from the supplied
cuff-count register, and initialize the conjunction flag. The verified
label scan then tests that every cuff vertex is outside the component.
The saved offset and all component marks remain available for reuse.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test the cuff labels at offset 261, with their supplied length in 105. -/
def gm06ComponentCuffTestProg : Cmd :=
  .seq (.assign 103 (.reg 261)) (.seq (.assign 108 (.reg 105))
    (.seq (.assign 112 (.const 1)) gm06UnreachedListProg))

/-- Restoring and scanning the cuff computes its exact component-disjointness
flag in linear time while preserving all arrays and the saved source offset. -/
theorem gm06ComponentCuffTestProg_exec {w off : ℕ} (x : GM06DrawingData) (a : Fin x.n)
    (L : List (Fin x.n)) (tail : List ℕ) (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hend : off + L.length < 2 ^ w) {s : State}
    (hmarks : s.arrs 33 = gm06VertexReachData x a)
    (hs : AtStream 0 off (L.map Fin.val ++ tail) s)
    (hstart : s.regs 261 = off) (hlen : s.regs 105 = L.length) :
    ∃ s' t, Exec w gm06ComponentCuffTestProg s s' t ∧ t ≤ 22 * L.length + 7 ∧
      s'.regs 112 = (if L.all (fun b => decide (¬ x.vertexGraph.Reachable a b)) then 1 else 0) ∧
      s'.regs 103 = off + L.length ∧
      (∀ A : ℕ, s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 112 → s'.regs q = s.regs q) := by
  have hoff : off < 2 ^ w := by omega
  have hlength : L.length < 2 ^ w := by omega
  let s₁ := s.setReg 103 off
  let s₂ := s₁.setReg 108 L.length
  let s₃ := s₂.setReg 112 1
  have hex₁ : Exec w (.assign 103 (.reg 261)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hstart, hoff])
  have hex₂ : Exec w (.assign 108 (.reg 105)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hlen, hlength])
  have hex₃ : Exec w (.assign 112 (.const 1)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  obtain ⟨s₄, t₄, hex₄, ht₄, hflag₄, hp₄, _, _, ha₄, hg₄⟩ :=
    gm06UnreachedListProg_exec x a L tail true hw hn hend (s := s₃) hmarks hs
      (by simp [s₃, s₂, s₁]) (by simp [s₃, s₂]) (by simp [s₃])
  refine ⟨s₄, 2 + (2 + (2 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, ?_, hp₄, ha₄, ?_⟩
  · simpa only [Bool.true_and] using hflag₄
  · intro q h103 h108 h109 h112
    rw [hg₄ q h103 h108 h109 h112]
    simp [s₃, s₂, s₁, State.setReg, h103, h108, h112]

end GraphMinor.Compute
