module

public import GraphMinor.Crossing.DefsReplace
import GraphMinor.Crossing.CutSec3

/-!
# From the search output to Lemma 1's path

The program searches the old graph restricted to the component and boundary, allowing
only component vertices in the interior. A simple returned walk is therefore a path in
the smaller restriction to the component and its two prescribed endpoints. This is the
search-path condition used by Lemma 1's splice proof.
-/

public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- The allowed-inner-vertex condition returned by BFS supplies exactly the reverse
search path of Lemma 1 when the endpoints are the first and last boundary visits. -/
theorem liftReplacementSearchPath_of_walk {V : Type*} [DecidableEq V]
    {r : ReplRecord V} {L : List V} {p q : V}
    (hp : firstIn r.boundary L = some p) (hq : lastIn r.boundary L = some q)
    (W : (HP25.restrict r.graph (r.rep ∪ (r.boundary : Set V))).Walk p q)
    (hpath : W.IsPath)
    (hinner : ∀ x ∈ W.support, x ≠ p → x ≠ q → x ∈ r.rep) :
    IsReplSearchPath r L W.support := by
  obtain ⟨hlist, hends⟩ := isPathList_support_of_isPath hpath
  have hsupport : ∀ x ∈ W.support, x ∈ r.rep ∪ {p, q} := by
    intro x hx
    by_cases hxp : x = p
    · exact Or.inr (by simp [hxp])
    by_cases hxq : x = q
    · exact Or.inr (by simp [hxq])
    exact Or.inl (hinner x hx hxp hxq)
  refine ⟨p, q, hp, hq, ⟨hlist.1, hlist.2.1, ?_⟩, hends⟩
  exact hlist.2.2.imp_of_mem_imp
    (fun a b ha hb hab => ⟨hab.1, hsupport a ha, hsupport b hb⟩)

end GraphMinor.Compute.Crossing
