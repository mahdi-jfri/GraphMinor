module

public import GraphMinor.GM06.Alg511FlowLinkage
public import GraphMinor.GM06.Alg511FlowOfLinkage
import Mathlib.Tactic

/-!
# Correctness of the initial flow search for actual cylinder drawings

The maximum-flow check of VI (5.11), page 134, is the existence of
an actual cylinder linkage. Apply the existing verified RAM search
on the finite input layout and use the two proved path transfers.
The paths branch constructs an actual linkage. Conversely, an actual
linkage supplies the finite path family, so the separator branch
cannot occur. The time bound is cubic in the path and vertex counts.
This is the flow phase on its Menger layout, not the full algorithm.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- On the finite Menger input layout, the initial flow program of
VI (5.11) decides the existence of an actual cylinder linkage. All
geometric hypotheses interpret supplied graph and cuff labels. -/
theorem alg511_initialFlow_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511Input)
      (G : Drawing ClosedCylinder)
      (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
      (source : Fin x.pathCount → Fin x.vertexCount),
      (∀ a ∈ x.flowInput.A, ∃ i, source i = a) →
      (∀ i, (rep.vertex (source i)).val = cylinderM1Point x.pathCount i) →
      (∀ a : Fin x.vertexCount,
        a.val ∈ x.innerCuff ↔ (rep.vertex a).val ∈ cylinderM1 x.pathCount) →
      (∀ b : Fin x.vertexCount,
        b.val ∈ x.outerCuff ↔ (rep.vertex b).val ∈ cylinderM2 x.pathCount) →
      ∀ s : State, s.arrs inArr = encDisjointPathsIn x.flowInput →
      ∃ s' t,
        Exec (wordSize c (disjointPathsSize x.flowInput)) disjointPathsEndToEndProg s s' t ∧
        t ≤ C * (x.pathCount + x.vertexCount + 1) ^ 3 ∧
        IsValidDisjointPathsOutput x.flowInput
          (decDisjointPathsOut x.flowInput (s'.arrs outArr)) ∧
        ((∃ P, decDisjointPathsOut x.flowInput (s'.arrs outArr) = Sum.inl P) ↔
          Nonempty (CylinderLinkage x.pathCount G)) := by
  obtain ⟨C, c, hC, hc, hflow⟩ := gm06Alg511Flow_exec
  refine ⟨C, c, hC, hc, ?_⟩
  intro x G rep source hsource hpoints hinner houter s hs
  obtain ⟨s', t, he, ht, hvalid, hcorrect⟩ := hflow x s hs
  refine ⟨s', t, he, ht, hvalid, ?_⟩
  constructor
  · intro hout
    obtain ⟨P, hPdisj, hPsimple⟩ := hcorrect.mp hout
    apply alg511_exists_linkage_of_flowPaths x rep source hsource hpoints
      (fun b hb => (houter b).mp (Finset.mem_filter.mp hb).2) P hPdisj hPsimple
  · rintro ⟨L⟩
    exact hcorrect.mpr (alg511_exists_flowPaths_of_linkage x rep hinner houter L)

end GraphMinor.GM06
