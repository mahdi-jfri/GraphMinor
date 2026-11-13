module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.SphereDisc
import GraphMinor.Surface.DrawCarry
import GraphMinor.Surface.ModelCriterion
import GraphMinor.GM19.Section6a

/-!
# The whole-sphere exception in Graph Minors V, (8.11)

Take the connected open set to be the whole sphere. Every circle in
it bounds a closed disc by the sphere-disc theorem. Any open disc
containing the whole sphere would be the sphere, contradicting
compactness. Thus the printed containment assertion needs a condition
excluding this case. The counterexample uses the library sphere model.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

/-- A counterexample to Graph Minors V, (8.11), page 113:
"If $r$ is a connected open subset of a surface $\Sigma$, and every subset of $r$ homeomorphic to a circle bounds a closed disc in $\Sigma$, then there is an open disc $\Delta \subseteq \Sigma$ with $r \subseteq \Delta$."
The sphere itself satisfies the hypotheses and fails the conclusion.
A corrected statement must exclude a whole spherical component. -/
theorem sphere_counterexample_to_8_11 :
    IsClosedSurface (SurfaceModel 0 0 0) ∧
    ∃ r : Set (SurfaceModel 0 0 0),IsConnected r ∧ IsOpen r ∧
      (∀ C : Set (SurfaceModel 0 0 0),C ⊆ r → IsOArc C →
        ∃ D : Set (SurfaceModel 0 0 0),IsClosedDisc D ∧ C=discBd D) ∧
      ¬∃ D : Set (SurfaceModel 0 0 0),IsOpenDisc D ∧ r ⊆ D := by
  have hS := isClosedSurface_model 0 0
  let : CompactSpace (SurfaceModel 0 0 0) := hS.1
  let : T2Space (SurfaceModel 0 0 0) := hS.2.1
  let : ConnectedSpace (SurfaceModel 0 0 0) := (modelCriterion.1 0 0 0).2
  refine ⟨hS,univ,isConnected_univ,isOpen_univ,?_,?_⟩
  · intro C _ hC
    obtain ⟨D,D',-,hD,-,hbd,-⟩ := sphere_disc _ GM19.isSphere_model C hC
    exact ⟨D,hD,hbd.symm⟩
  · rintro ⟨D,hD,hs⟩
    have hDu : D=univ := Set.eq_univ_of_univ_subset hs
    rw [hDu] at hD
    exact GM19.not_isOpenDisc_univ hD

end GraphMinor.GM05
