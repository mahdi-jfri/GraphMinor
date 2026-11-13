module

public import GraphMinor.Compute.GM06Alg34VertexRootExpr

/-!
# Computing one canonical vertex component root

Search the source component, compute its exclusive prefix sums, and
test the source count for zero. This implements the least-label root
test and leaves the component marks available for its branch payload.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test source register 187 for being the least label in its component. -/
def gm06VertexRootQueryProg : Cmd :=
  .seq gm06VertexBfsProg (.seq gm06VertexReachRanksProg (.assign 200 gm06VertexRootExpr))

/-- The exact root bit and component marks are computed in quadratic time,
while preserving the drawing input and component adjacency arrays. -/
theorem gm06VertexRootQueryProg_exec {w : ℕ} (x : GM06DrawingData) (a : Fin x.n)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.n) (hsource : s.regs 187 = a.val)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n) :
    ∃ s' t, Exec w gm06VertexRootQueryProg s s' t ∧
      t ≤ 26 * (x.n * x.n) + 46 * x.n + 39 ∧
      s'.regs 200 = (if x.isComponentRoot a then 1 else 0) ∧
      s'.arrs 33 = gm06VertexReachData x a ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → A ≠ 35 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 201 ≤ q) → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hm₁, ha₁, hg₁⟩ :=
    gm06VertexBfsProg_exec x a hw hn hsquare hsize hsource hlists hlen
  obtain ⟨s₂, t₂, hex₂, ht₂, hr₂, ha₂, hg₂⟩ :=
    gm06VertexReachRanksProg_exec x a hw hn hm₁
  have hsource₂ : s₂.regs 187 = a.val :=
    (hg₂ 187 (by decide) (by decide)).trans ((hg₁ 187 (by decide)).trans hsource)
  let s₃ := s₂.setReg 200 (if x.isComponentRoot a then 1 else 0)
  have hex₃ : Exec w (.assign 200 gm06VertexRootExpr) s₂ s₃ 5 :=
    .assign (gm06VertexRootExpr_eval x a hw hn hsource₂ hr₂)
  refine ⟨s₃, t₁ + (t₂ + 5), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by simp [s₃], (ha₂ 33 (by decide)).trans hm₁, ?_, ?_⟩
  · intro A h33 h34 h35
    exact (ha₂ A h35).trans (ha₁ A h33 h34)
  · intro q hq
    rw [State.setReg_regs_ne _ _ (by omega : q ≠ 200), hg₂ q (by omega) (by omega)]
    exact hg₁ q (by omega)

end GraphMinor.Compute
