module

public import GraphMinor.Compute.TwoPathsSpec
public import GraphMinor.HP25.Sec5Complete

/-!
# Interface of the loop of Algorithm 5.2

This file states `LoopSpec`, the specification of a Word RAM program that runs the `while` loop of
Algorithm 5.2 ("Computing $P$-completions", page 23) of S. Humeau and D. Pous, *On the Two Paths
Theorem and the Two Disjoint Paths Problem*, arXiv:2505.16431v2 (14 August 2025).

The mathematical content of the loop is `GraphMinor.HP25.complete_loop_edges`
(`GraphMinor/HP25/Sec5Complete.lean`), and the memory conventions are those of
`CompletionStatement` (`GraphMinor/Compute/TwoPathsSpec.lean`):
* **Input:** an instance `(H, a A b B, P)` satisfying `IsSplitInput H a b A B P` and stored in memory
  as in `InstanceAt` (`rN`, `rLenA`, `aStart`, `aEnd`, `aEnt`, `aCyc`, `aPath`), together with the
  three additional hypotheses of `complete_loop_edges` for `C = a :: A ++ b :: B`:
  - `P` is induced in `H` (`∀ u ∈ P.support, ∀ v ∈ P.support, H.Adj u v → IsListEdge P.support u v`);
  - `P` is tight (`IsTight H (a :: A ++ b :: B) A B P.support`);
  - every vertex of `P` is sided (`∀ v ∈ P.support, IsSided H {x | x ∈ C ∨ x ∈ P.support} A B v`).
* **Word size:** `w ≥ wordSize c_w ((N + 1) * (M + N + 1))`, where `M = H.edgeFinset.card`, as in
  `CompletionStatement`.
* **Output:** the program stops in at most `c |P'| (N + M + 1)` steps (`Proposition 5.9`, page 24:
  one search of `O(N + M)` steps per step of the loop, and at most `|P'|` steps). It leaves all
  registers below `300` and all arrays below `200` other than `aF` and `aNewPath` unchanged, and
  leaves each record array `200 … 299` (`isRecordArr`) of length at most `c (N + M + 1)`. It writes
  in `aF` a flat list `F` of new edges on `P` (`IsNewEdgeList H P.support F`) and in `aNewPath` the
  vertex list of a path `P'` of `H ⊔ pairGraph N F` from `a` to `b` satisfying all conclusions of
  `complete_loop_edges` (with `H ⊔ pairGraph N F` in place of the output graph) together with the
  edge count bound `F.length / 2 < P'.support.length` of `IsCompletionOutput`.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-- The specification of the loop of Algorithm 5.2 (Humeau and Pous, page 23), combining the
memory and complexity conventions of `CompletionStatement` (`GraphMinor/Compute/TwoPathsSpec.lean`)
with the hypotheses and conclusions of `complete_loop_edges`
(`GraphMinor/HP25/Sec5Complete.lean`). -/
def LoopSpec (loop : Cmd) (c c_w : ℕ) : Prop :=
  ∀ (N : ℕ) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (lists : Fin N → List ℕ)
    (a b : Fin N) (A B : List (Fin N)) (P : H.Walk a b),
    IsSplitInput H a b A B P →
    (∀ u ∈ P.support, ∀ v ∈ P.support, H.Adj u v → IsListEdge P.support u v) →
    IsTight H (a :: A ++ b :: B) A B P.support →
    (∀ v ∈ P.support, IsSided H {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} A B v) →
    ∀ (w : ℕ), wordSize c_w ((N + 1) * (H.edgeFinset.card + N + 1)) ≤ w →
    ∀ (s : State), InstanceAt H lists a b A B P s → (s.arrs aEnt).length < 2 ^ w →
      ∃ (s' : State) (t : ℕ), Exec w loop s s' t ∧
        (∀ r < 300, s'.regs r = s.regs r) ∧
        (∀ x < 200, x ≠ aF → x ≠ aNewPath → s'.arrs x = s.arrs x) ∧
        (∀ x, isRecordArr x → (s'.arrs x).length ≤ c * (N + H.edgeFinset.card + 1)) ∧
        ∃ (F : List ℕ) (P' : (H ⊔ pairGraph N F).Walk a b),
          s'.arrs aF = F ∧ IsNewEdgeList H P.support F ∧
          s'.arrs aNewPath = P'.support.map Fin.val ∧
          (IsCrossed (H ⊔ pairGraph N F) (a :: A ++ b :: B) →
            IsCrossed H (a :: A ++ b :: B)) ∧
          IsTPath (H ⊔ pairGraph N F) (a :: A ++ b :: B) P' ∧
          OnBothSides (H ⊔ pairGraph N F) (a :: A ++ b :: B) A B P' ∧
          Separates (H ⊔ pairGraph N F) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
          (∀ u ∈ P'.support, ∀ v ∈ P'.support, (H ⊔ pairGraph N F).Adj u v →
            IsListEdge P'.support u v) ∧
          IsTight (H ⊔ pairGraph N F) (a :: A ++ b :: B) A B P'.support ∧
          (∀ u v, (H ⊔ pairGraph N F).Adj u v → H.Adj u v ∨ IsListEdge P'.support u v) ∧
          P'.support.Sublist P.support ∧
          (∀ M, M <+: P.support → (∀ v ∈ M,
              IsOnSide H {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ A} v ∧
              IsOnSide H {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ B} v) →
            M <+: P'.support) ∧
          F.length / 2 < P'.support.length ∧
          t ≤ c * P'.support.length * (N + H.edgeFinset.card + 1)

end GraphMinor.Compute.TwoPaths
