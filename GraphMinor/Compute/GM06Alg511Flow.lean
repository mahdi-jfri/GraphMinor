module

public import GraphMinor.Compute.GM06Alg511FlowGraph
public import GraphMinor.Compute.Menger
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Reusing the verified initial maximum-flow search in VI (5.11)

The first search on page 134 asks for paths between the two cuffs,
without prescribing a pairing. Supply the endpoint-label graph to
the existing augmenting-path program. Its output gives the requested
number of disjoint simple paths or a smaller separator. Weak Menger
duality proves that the separator branch rules out every such path
family. This file verifies the search on its Menger input layout.
Converting the cylinder word array to that layout is a separate phase.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The initial flow instance uses the two supplied cuff label lists
as the source and target sets. -/
def GM06Alg511Input.flowInput (x : GM06Alg511Input) : DisjointPathsInput where
  n := x.vertexCount
  G := x.flowGraph
  A := Finset.univ.filter (fun i => i.val ∈ x.innerCuff)
  B := Finset.univ.filter (fun i => i.val ∈ x.outerCuff)
  k := x.pathCount

/-- The size used by the verified Menger search is polynomial in the
supplied vertex count and requested number of paths. -/
theorem gm06Alg511FlowSize_le (x : GM06Alg511Input) :
    disjointPathsSize x.flowInput ≤ (x.pathCount + x.vertexCount + 1) ^ 3 := by
  have hm : x.flowGraph.edgeFinset.card ≤ x.vertexCount ^ 2 := by
    have h := x.flowGraph.card_edgeFinset_le_card_choose_two
    simp only [Fintype.card_fin] at h
    exact h.trans (Nat.choose_le_pow _ _)
  change (x.pathCount + 1) * (x.vertexCount + x.flowGraph.edgeFinset.card + 1) ≤ _
  have hfirst : x.pathCount + 1 ≤ x.pathCount + x.vertexCount + 1 := by omega
  have hsecond : x.vertexCount + x.flowGraph.edgeFinset.card + 1 ≤
      (x.pathCount + x.vertexCount + 1) ^ 2 := by nlinarith
  calc
    _ ≤ (x.pathCount + x.vertexCount + 1) * (x.pathCount + x.vertexCount + 1) ^ 2 :=
      Nat.mul_le_mul hfirst hsecond
    _ = _ := by ring

/-- For a valid Menger output, returning paths is equivalent to the
existence of the requested number of disjoint simple cuff-to-cuff paths. -/
theorem gm06Alg511FlowOutput_correct (x : GM06Alg511Input)
    (result : DisjointPathsOutput x.flowInput)
    (hresult : IsValidDisjointPathsOutput x.flowInput result) :
    (∃ P, result = Sum.inl P) ↔
      ∃ P : Fin x.pathCount → ABWalk x.flowGraph x.flowInput.A x.flowInput.B,
        PairwiseVertexDisjoint P ∧ ∀ i, (P i).walk.IsPath := by
  cases result with
  | inl P => exact ⟨fun _ => ⟨P, hresult⟩, fun _ => ⟨P, rfl⟩⟩
  | inr C =>
    constructor
    · rintro ⟨P, hP⟩
      cases hP
    · rintro ⟨P, hP, _⟩
      have hcard := card_le_of_disjoint_walks_and_separator P hP hresult.2
      exact False.elim (Nat.not_le_of_gt hresult.1 hcard)

/-- The existing RAM search, on its explicit finite graph layout,
returns a certified path family or separator and decides whether the
finite cuff-to-cuff path family exists. Constants are uniform in the
supplied cylinder input. -/
theorem gm06Alg511Flow_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511Input) (s : State),
      s.arrs inArr = encDisjointPathsIn x.flowInput →
      ∃ s' t,
        Exec (wordSize c (disjointPathsSize x.flowInput)) disjointPathsEndToEndProg s s' t ∧
        t ≤ C * (x.pathCount + x.vertexCount + 1) ^ 3 ∧
        IsValidDisjointPathsOutput x.flowInput
          (decDisjointPathsOut x.flowInput (s'.arrs outArr)) ∧
        ((∃ P, decDisjointPathsOut x.flowInput (s'.arrs outArr) = Sum.inl P) ↔
          ∃ P : Fin x.pathCount → ABWalk x.flowGraph x.flowInput.A x.flowInput.B,
            PairwiseVertexDisjoint P ∧ ∀ i, (P i).walk.IsPath) := by
  obtain ⟨C, c, hC, hc, hexec⟩ := disjointPaths_computesInTime
  refine ⟨C, c, hC, hc, ?_⟩
  intro x s hs
  obtain ⟨s', t, he, ht, ho⟩ := hexec x.flowInput s hs
  exact ⟨s', t, he, ht.trans (Nat.mul_le_mul_left C (gm06Alg511FlowSize_le x)),
    ho, gm06Alg511FlowOutput_correct x _ ho⟩

end GraphMinor.Compute
