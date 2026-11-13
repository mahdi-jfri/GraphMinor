module

public import GraphMinor.Compute.GM02ChildEdgeExclusion
public import GraphMinor.Compute.GM02CopyGraphPrefix

/-!
# Preparing the canonical edge-filter input from a parent encoding

Copy the graph prefix of the retained terminated input, prepare the
chosen child's exclusion bits, and read the edge count from the copied
header. The child membership array is preserved. Thus the edge builder
receives exactly its standard graph and bitset inputs.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- Prepare graph array 0, exclusion array 13, and edge-count register 1. -/
def gm02PrepareChildFilterProg (right : Bool) (src : Arr) : Cmd :=
  .seq (gm02CopyGraphPrefixProg src 0)
    (.seq (gm02ChildEdgeExclusionProg right) (.assign 1 (.read 0 (.const 1))))

/-- Preparation reads all graph data from the plain retained parent input. -/
theorem gm02PrepareChildFilterProg_exec {n w : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (right : Bool) (L B : Finset (Fin n)) (src : Arr) (hs0 : src ≠ 0)
    (rest : List ℕ) (s : State) (hsrc : s.arrs src = encGraph F ++ rest)
    (hL : s.arrs 1 = bitSetList L) (hB : s.arrs 14 = bitSetList B)
    (hn : n < 2 ^ w) (hlen : 2 + 2 * (edgeListOf F).length < 2 ^ w) :
    ∃ s' t, Exec w (gm02PrepareChildFilterProg right src) s s' t ∧
      t ≤ 32 * (edgeListOf F).length + 16 * n + 64 ∧
      s'.arrs 0 = encGraph F ∧
      s'.arrs 13 = bitSetList (gm02ChildEdgeExclusionSet right L) ∧
      s'.arrs 14 = bitSetList B ∧ s'.regs 1 = (edgeListOf F).length ∧
      (∀ a, a ≠ 0 → a ≠ 13 → s'.arrs a = s.arrs a) := by
  have hw : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hG₁, ha₁, _⟩ := gm02CopyGraphPrefixProg_exec F src 0 hs0 rest hn
    hlen s hsrc
  obtain ⟨s₂, t₂, he₂, ht₂, hA₂, ha₂, _⟩ := gm02ChildEdgeExclusionProg_exec right L B s₁
    ((ha₁ 1 (by decide)).trans hL) ((ha₁ 14 (by decide)).trans hB) hw hn
  have hG₂ : s₂.arrs 0 = encGraph F := (ha₂ 0 (by decide)).trans hG₁
  let s₃ := s₂.setReg 1 (edgeListOf F).length
  have he₃ : Exec w (.assign 1 (.read 0 (.const 1))) s₂ s₃ 3 := by
    apply Exec.assign
    simp [Expr.eval, hG₂, encGraph, checkWord_of_lt hw,
      checkWord_of_lt (by omega : (edgeListOf F).length < 2 ^ w)]
  refine ⟨s₃, t₁ + (t₂ + 3), Exec.seq he₁ (Exec.seq he₂ he₃), by omega,
    hG₂, hA₂, ?_, by simp [s₃], ?_⟩
  · exact (ha₂ 14 (by decide)).trans ((ha₁ 14 (by decide)).trans hB)
  · intro a ha0 ha13
    exact (ha₂ a ha13).trans (ha₁ a ha0)

/-- Filter preparation preserves the computed scheme catalogue. -/
theorem gm02PrepareChildFilterProg_catalogue_not_written (right : Bool) (src : Arr) :
    330 ∉ (gm02PrepareChildFilterProg right src).writtenRegs := by
  cases right with
  | false =>
    change 330 ∉ (gm02PrepareChildFilterProg false 0).writtenRegs
    decide
  | true =>
    change 330 ∉ (gm02PrepareChildFilterProg true 0).writtenRegs
    decide

end GraphMinor.Compute
