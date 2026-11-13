module

public import GraphMinor.Compute.GM02ChildVertexDeletion
public import GraphMinor.Compute.GM02PrepareChildFilter
public import GraphMinor.Compute.GM02BuildCompactChild

/-!
# Building a complete child from the parent and selected template

Compute the corrected child vertices from the two side arrays and the
selected template fields. Prepare the canonical edge filter directly
from the retained parent encoding, then compact and pack its graph and
termination. Only the fixed child work arrays change, so the parent and
scheme data remain available for the other recursive call.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02 GraphMinor.Compute.Crossing TwoPaths

/-- The chosen side's corrected vertex set, with the opposite-side order swapped for a right child. -/
def gm02ChosenChildVertices {n : ℕ} (right : Bool) (L R Q Z P : Finset (Fin n)) : Finset (Fin n) :=
  gm02ChildVertices (if right then R else L) (if right then L else R) Q Z P

/-- Build a chosen child from retained parent input and selected template fields. -/
def gm02BuildChildFromTemplateProg (right : Bool)
    (parent support reserved fresh rawPairs a : Arr) : Cmd :=
  .seq (gm02ChildVertexDeletionProg (if right then 2 else 1) (if right then 1 else 2)
      support reserved fresh 14 a)
    (.seq (gm02PrepareChildFilterProg right parent)
      (gm02BuildCompactChildProg a (a + 1) (a + 2) rawPairs (a + 3) (a + 4)))

/-- The complete chosen-child construction preserves every parent and template array. -/
theorem gm02BuildChildFromTemplateProg_exec {n w : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (right : Bool) (L R Q Z P : Finset (Fin n))
    (T : Termination {v : Fin n | v ∉ (gm02ChosenChildVertices right L R Q Z P)ᶜ})
    (parent support reserved fresh rawPairs a : Arr)
    (hp : 17 < parent ∧ parent < a) (hs : 17 < support ∧ support < a)
    (hz : 17 < reserved ∧ reserved < a) (hf : 17 < fresh ∧ fresh < a)
    (htp : 17 < rawPairs ∧ rawPairs < a) (rest : List ℕ) (s : State)
    (hparent : s.arrs parent = encGraph F ++ rest)
    (hL : s.arrs 1 = bitSetList L) (hR : s.arrs 2 = bitSetList R)
    (hQ : s.arrs support = bitSetList Q) (hZ : s.arrs reserved = bitSetList Z)
    (hP : s.arrs fresh = bitSetList P)
    (hPairs : s.arrs rawPairs = flatEdges (edgeListOf T.pairGraph))
    (hcount : s.regs 40 = n) (hn : n < 2 ^ w)
    (hlen : 8 + 2 * (edgeListOf F).length + 2 * T.index < 2 ^ w) :
    ∃ s' t, Exec w (gm02BuildChildFromTemplateProg right parent support reserved fresh rawPairs a)
        s s' t ∧ t ≤ 82 * n + 166 * (edgeListOf F).length + 62 * T.index + 184 ∧
      s'.arrs (a + 4) =
        (gm02FilteredChildInput F (gm02ChildEdgeExclusionSet right L)
          (gm02ChosenChildVertices right L R Q Z P) T).enc ∧
      (∀ j, j ∉ [0, 13, 14, 17, a, a + 1, a + 2, a + 3, a + 4] →
        s'.arrs j = s.arrs j) := by
  have ha : 17 < a := hp.1.trans hp.2
  have hw : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hB₁, hD₁, _, hk₁⟩ := gm02ChildVertexDeletionProg_exec
    (if right then R else L) (if right then L else R) Q Z P
    (if right then 2 else 1) (if right then 1 else 2) support reserved fresh 14 a
    (by cases right <;> decide) (by cases right <;> decide)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) s
    (by cases right <;> assumption) (by cases right <;> assumption)
    hQ hZ hP hcount hn hw
  have keep₁ (j : Arr) (hj : j ≠ 14) (hja : j ≠ a) : s₁.arrs j = s.arrs j :=
    hk₁.2 j (by simp [hj, hja])
  obtain ⟨s₂, t₂, he₂, ht₂, hG₂, hA₂, hB₂, hm₂, ha₂⟩ :=
    gm02PrepareChildFilterProg_exec F right L (gm02ChosenChildVertices right L R Q Z P)
      parent (by dsimp only [Arr] at *; omega) rest s₁
      ((keep₁ parent (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)).trans hparent)
      ((keep₁ 1 (by decide) (by dsimp only [Arr] at *; omega)).trans hL) hB₁ hn (by dsimp only [Arr] at *; omega)
  have hD₂ : s₂.arrs a = bitSetList (gm02ChosenChildVertices right L R Q Z P)ᶜ :=
    (ha₂ a (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)).trans hD₁
  have hPairs₂ : s₂.arrs rawPairs = flatEdges (edgeListOf T.pairGraph) :=
    (ha₂ rawPairs (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)).trans
      ((keep₁ rawPairs (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)).trans hPairs)
  obtain ⟨s₃, t₃, he₃, ht₃, hout, ha₃⟩ := gm02BuildCompactChildProg_exec F
    (gm02ChildEdgeExclusionSet right L) (gm02ChosenChildVertices right L R Q Z P) T
    a (a + 1) (a + 2) rawPairs (a + 3) (a + 4)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega)
    (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) s₂ hn hlen hG₂ hA₂ hB₂ hD₂ hm₂ hPairs₂
  refine ⟨s₃, t₁ + (t₂ + t₃), Exec.seq he₁ (Exec.seq he₂ he₃), by omega, hout, ?_⟩
  intro j hj
  have hjs : j ≠ 0 ∧ j ≠ 13 ∧ j ≠ 14 ∧ j ≠ 17 ∧ j ≠ a ∧ j ≠ a + 1 ∧
      j ≠ a + 2 ∧ j ≠ a + 3 ∧ j ≠ a + 4 := by simpa using hj
  exact (ha₃ j hjs.2.2.2.2.2.1 hjs.2.2.2.1 hjs.2.2.2.2.2.2.1
    hjs.2.2.2.2.2.2.2.1 hjs.2.2.2.2.2.2.2.2).trans
      ((ha₂ j hjs.1 hjs.2.1).trans (keep₁ j hjs.2.2.1 hjs.2.2.2.2.1))

/-- Child construction preserves the parent size and catalogue-selection registers. -/
theorem gm02BuildChildFromTemplateProg_control_not_written (right : Bool)
    (parent support reserved fresh rawPairs a : Arr) :
    40 ∉ (gm02BuildChildFromTemplateProg right parent support reserved fresh rawPairs a).writtenRegs ∧
    330 ∉ (gm02BuildChildFromTemplateProg right parent support reserved fresh rawPairs a).writtenRegs ∧
    346 ∉ (gm02BuildChildFromTemplateProg right parent support reserved fresh rawPairs a).writtenRegs := by
  cases right with
  | false =>
    change 40 ∉ (gm02BuildChildFromTemplateProg false 0 0 0 0 0 0).writtenRegs ∧
      330 ∉ (gm02BuildChildFromTemplateProg false 0 0 0 0 0 0).writtenRegs ∧
      346 ∉ (gm02BuildChildFromTemplateProg false 0 0 0 0 0 0).writtenRegs
    decide
  | true =>
    change 40 ∉ (gm02BuildChildFromTemplateProg true 0 0 0 0 0 0).writtenRegs ∧
      330 ∉ (gm02BuildChildFromTemplateProg true 0 0 0 0 0 0).writtenRegs ∧
      346 ∉ (gm02BuildChildFromTemplateProg true 0 0 0 0 0 0).writtenRegs
    decide

end GraphMinor.Compute
