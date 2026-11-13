module

public import GraphMinor.GM01.CombInteriorFork
public import GraphMinor.GM01.CombReflection
import GraphMinor.GM01.RootedModelComposition

/-!
# Choosing the longer side of an interior-rooted comb

Graph Minors I, (4.9), page 58, uses that the comb has at least `2δ`
cells. An interior root leaves enough cells on at least one side.
Use the first orientation when enough remain to its right. Otherwise
reflect the spine and use that orientation on the reflected comb.
The first and last two cells are excluded in both orientations.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- Reflection reverses the spine position and preserves the attached
binary word, including a root in a binary copy. -/
theorem combReflectVertex_spineIndex {L : ℕ} (v : PathCombVertex L) :
    (pathCombSpineIndex (combReflectVertex v)).val = L - ((pathCombSpineIndex v).val + 1) := by
  cases v with
  | inl i => rfl
  | inr pair => rfl

/-- The source-comb contraction in GM01 (4.9), page 58. A root outside
the first and last two cells yields the forbidden fork when the comb
has at least `2δ` cells. -/
noncomputable def rootedForkModelOfCombInterior {γ δ L : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hlong : 2 * δ ≤ L)
    (v : (pathComb (γ - 1) L).verts)
    (hv : 2 ≤ (pathCombSpineIndex v.val).val)
    (hv' : (pathCombSpineIndex v.val).val < L - 2) :
    RootedMinorModel (rootedForkGraph γ δ hγ hδ)
      (⟨toGraph (pathComb (γ - 1) L), v⟩ : RootedGraph (PathCombVertex L) (Sym2 (PathCombVertex L))) := by
  classical
  by_cases hright : (pathCombSpineIndex v.val).val + δ ≤ L
  · exact rootedForkModelOfCombInteriorRight hγ hδ v hv hright
  · let w : (pathComb (γ - 1) L).verts :=
      ⟨combReflectVertex v.val, combReflectVertex_mem v.property⟩
    have hw : (pathCombSpineIndex w.val).val = L - ((pathCombSpineIndex v.val).val + 1) :=
      combReflectVertex_spineIndex v.val
    have hi := (pathCombSpineIndex v.val).isLt
    have hw2 : 2 ≤ (pathCombSpineIndex w.val).val := by omega
    have hwlong : (pathCombSpineIndex w.val).val + δ ≤ L := by omega
    exact (rootedForkModelOfCombInteriorRight hγ hδ w hw2 hwlong).trans
      (rootedCombReflectionModel v)

end GraphMinor.GM01
