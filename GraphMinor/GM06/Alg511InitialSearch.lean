module

public import GraphMinor.Compute.GM06Alg511SearchInput
public import GraphMinor.GM06.Alg511InitialFlow
import Mathlib.Tactic

/-!
# The initial linkage search from the supplied finite input

Load the ordinary graph/cuff row of the finite input and run the
verified maximum-flow program, as required by VI (5.11), page 134.
The complete drawing fields remain in array 1000 for the subsequent
winding and successor phases. The returned paths branch is equivalent
to the existence of an actual cylinder linkage. No linkage, separator
or decision bit is supplied as input.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

private theorem menger_preserves_saved_input :
    (1000 : ℕ) ∉ disjointPathsEndToEndProg.writtenArrs := by decide

/-- The actual initial search starts from the supplied finite word
array, returns the exact linkage-existence answer, and retains the
original drawing data. Its time is a linear loading bound plus the
uniform cubic bound of maximum flow. -/
theorem alg511_initialSearch_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511WindingInput)
      (G : Drawing ClosedCylinder)
      (rep : GM06SuccessorGraphRep (x.drawing.withLinkage []) G.toGraph)
      (source : Fin x.drawing.pathCount → Fin x.drawing.vertexCount),
      (∀ a ∈ x.drawing.flowInput.A, ∃ i, source i = a) →
      (∀ i, (rep.vertex (source i)).val = cylinderM1Point x.drawing.pathCount i) →
      (∀ a : Fin x.drawing.vertexCount,
        a.val ∈ x.drawing.innerCuff ↔ (rep.vertex a).val ∈ cylinderM1 x.drawing.pathCount) →
      (∀ b : Fin x.drawing.vertexCount,
        b.val ∈ x.drawing.outerCuff ↔ (rep.vertex b).val ∈ cylinderM2 x.drawing.pathCount) →
      ∀ (s : State) (w : ℕ), 1 < 2 ^ w →
      wordSize c (disjointPathsSize x.drawing.flowInput) ≤ w →
      s.arrs 0 = gm06Alg511SearchWords x →
      (gm06Alg511SearchWords x).length < 2 ^ w →
      (∀ v ∈ gm06Alg511SearchWords x, v < 2 ^ w) →
      ∃ s' t, Exec w gm06Alg511InitialSearchProg s s' t ∧
        t ≤ 13 + 44 * (gm06Alg511SearchWords x).length +
          C * (x.drawing.pathCount + x.drawing.vertexCount + 1) ^ 3 ∧
        s'.arrs 1000 = gm06Alg511WindingWords x ∧
        IsValidDisjointPathsOutput x.drawing.flowInput
          (decDisjointPathsOut x.drawing.flowInput (s'.arrs outArr)) ∧
        ((∃ P, decDisjointPathsOut x.drawing.flowInput (s'.arrs outArr) = Sum.inl P) ↔
          Nonempty (CylinderLinkage x.drawing.pathCount G)) := by
  obtain ⟨C, c, hC, hc, hflow⟩ := alg511_initialFlow_exec
  refine ⟨C, c, hC, hc, ?_⟩
  intro x G rep source hsource hpoints hinner houter s w hw hwflow ha hn hwords
  obtain ⟨s₁, t₁, he₁, ht₁, hinput, hsaved⟩ :=
    gm06Alg511LoadSearchProg_exec x s hw ha hn hwords
  obtain ⟨s₂, t₂, he₂, ht₂, hvalid, hanswer⟩ :=
    hflow x.drawing G rep source hsource hpoints hinner houter s₁ hinput
  refine ⟨s₂, t₁ + t₂, .seq he₁ (he₂.mono_wordSize hwflow), by omega, ?_, hvalid, hanswer⟩
  rw [Exec.arrs_eq_of_not_mem_writtenArrs he₂ menger_preserves_saved_input]
  exact hsaved

end GraphMinor.GM06
