module

public import GraphMinor.Compute.GM06Alg34ReachedList

/-!
# Searching the component of a block's first label

After reading a block's first label, search from that label and scan
its remaining labels. The final conjunction says exactly that the
whole block lies in one component. The input and adjacency arrays are
preserved for the next block.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Search the source component and conjoin marks of the remaining block labels. -/
def gm06BlockQueryProg : Cmd :=
  .seq gm06VertexBfsProg (.seq (.assign 112 (.const 1)) gm06ReachedListProg)

/-- The prepared block query computes exactly whether every remaining
label belongs to the source component, in quadratic search time plus
linear scan time. -/
theorem gm06BlockQueryProg_exec {w off : ℕ} (x : GM06DrawingData) (a : Fin x.n)
    (L : List (Fin x.n)) (tail : List ℕ) (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hsquare : x.n * x.n < 2 ^ w) (hend : off + L.length < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.n) (hsource : s.regs 187 = a.val)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n)
    (hs : AtStream 0 off (L.map Fin.val ++ tail) s)
    (hp : s.regs 103 = off) (hcount : s.regs 108 = L.length) :
    ∃ s' t, Exec w gm06BlockQueryProg s s' t ∧
      t ≤ 26 * (x.n * x.n) + 23 * x.n + 22 * L.length + 29 ∧
      s'.regs 112 = (if L.all (fun b => decide (x.vertexGraph.Reachable a b)) then 1 else 0) ∧
      s'.regs 103 = off + L.length ∧ s'.regs 108 = 0 ∧
      AtStream 0 (off + L.length) tail s' ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 112 →
        s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hmarks₁, ha₁, hg₁⟩ :=
    gm06VertexBfsProg_exec x a hw hn hsquare hsize hsource hlists hlen
  let s₂ := s₁.setReg 112 1
  have hex₂ : Exec w (.assign 112 (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  obtain ⟨s₃, t₃, hex₃, ht₃, hans₃, hp₃, hz₃, hs₃, ha₃, hg₃⟩ :=
    gm06ReachedListProg_exec x a L tail true hw hn hend (s := s₂) hmarks₁
      ((hs.of_arr_eq (ha₁ 0 (by decide) (by decide))).of_arr_eq rfl)
      (by simpa [s₂] using (hg₁ 103 (by decide)).trans hp)
      (by simpa [s₂] using (hg₁ 108 (by decide)).trans hcount) (by simp [s₂])
  refine ⟨s₃, t₁ + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    ?_, hp₃, hz₃, hs₃, ?_, ?_⟩
  · simpa only [Bool.true_and] using hans₃
  · intro A h33 h34
    exact (ha₃ A).trans (ha₁ A h33 h34)
  · intro q hq h103 h108 h109 h112
    rw [hg₃ q h103 h108 h109 h112]
    exact (State.setReg_regs_ne _ _ h112).trans (hg₁ q hq)

end GraphMinor.Compute
