module

public import GraphMinor.GM01.CombRootRight
public import GraphMinor.GM01.CombReflection
public import GraphMinor.GM01.RootedModelComposition
import Lean.Elab.Tactic.Omega

/-!
# A long comb rooted at an arbitrary vertex

The tail comb in Graph Minors I, (4.1), page 55, may be reached at any
vertex. Its cell has either a long enough right-hand interval or a long
enough left-hand interval. In the first case use the proved rooted right
subcomb. In the second case reflect the spine, apply that construction,
and reflect its model back. The unused root cell carries the root path.
-/

public section

namespace GraphMinor.GM01

open SimpleGraph

/-- A comb with at least `2m+1` spine vertices contains the `m`-vertex
comb as a rooted minor at every target vertex. This is the long-side
choice needed for the arbitrary attachment in GM01 (4.1), page 55. -/
theorem rootedPathComb_of_long_comb {γ m N : ℕ} (hm : 0 < m) (hN : 2 * m + 1 ≤ N)
    (v : (pathComb γ N).verts) :
    HasRootedMinor (rootedPathComb γ m hm)
      (⟨toGraph (pathComb γ N), v⟩ : RootedGraph (PathCombVertex N) (Sym2 (PathCombVertex N))) := by
  by_cases hright : (pathCombSpineIndex v.val).val + 1 + m ≤ N
  · exact rootedPathComb_to_right hm v hright
  · let w : (pathComb γ N).verts := ⟨combReflectVertex v.val, combReflectVertex_mem v.property⟩
    have hindex : (pathCombSpineIndex w.val).val = N - ((pathCombSpineIndex v.val).val + 1) := by
      obtain ⟨v, hv⟩ := v
      cases v <;> rfl
    have hbound : (pathCombSpineIndex w.val).val + 1 + m ≤ N := by
      rw [hindex]
      have hv := (pathCombSpineIndex v.val).isLt
      omega
    exact (rootedPathComb_to_right hm w hbound).trans ⟨rootedCombReflectionModel v⟩

end GraphMinor.GM01
