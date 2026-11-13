module

public import GraphMinor.Compute.CitedPlanarity
public import GraphMinor.LRPlanarity.Algorithm

/-!
# Word RAM specification for the left-right Boolean function

Part V, Sections 1 and 2 of `docs/planarity/planarity_test.tex` require one fixed program
with a linear bound. This interface uses the calling convention of
`PlanarityTestStatement`, but its output is the concrete function `LRPlanarity.lrTest`.
It asserts neither geometric correctness nor any cost bound for Lean list operations.
A program proof must represent those sequences by fixed-capacity arrays of linked
records, including constant-time head/tail concatenation and separate anchor pointers.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Part V, Sections 1 and 2: "Array capacities are allocated from N and M. If M is
not part of the input header, we first count the adjacency entries in time O(N+M)."

The program preserves registers below 30 and arrays below 33 and writes the
Boolean result to register 35. Array growth is charged by `Exec`, so a proof
must allocate each working arena once rather than repeatedly append memory. -/
def LRPlanarityRamStatement : Prop :=
  ∃ (prog : Cmd) (C c_w : ℕ), 0 < C ∧ 0 < c_w ∧
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (lists : Fin N → List ℕ),
      ∀ (w : ℕ), wordSize c_w (G.edgeFinset.card + N + 1) ≤ w →
      ∀ (s : State),
        IsAdjList G 30 31 32 lists s →
        (s.arrs 32).length < 2 ^ w →
        s.regs 30 = N →
        ∃ (s' : State) (t : ℕ),
          Exec w prog s s' t ∧
          t ≤ C * (G.edgeFinset.card + N + 1) ∧
          (∀ r < 30, s'.regs r = s.regs r) ∧
          (∀ a < 33, s'.arrs a = s.arrs a) ∧
          s'.regs 35 = (LRPlanarity.lrTest lists).toNat

end GraphMinor.Compute
