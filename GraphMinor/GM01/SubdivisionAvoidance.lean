module

public import GraphMinor.GM01.SubdivisionSides
import GraphMinor.GM01.SubdivisionConnected

/-!
# Following source edges while avoiding a centre

For the block construction on page 55 of Graph Minors I, later spine
centres remain joined after an earlier spine centre is deleted. A source
edge not incident with the deleted vertex has a replacing path avoiding
its centre, since the only centres on that path are its ends. Following
that path supplies reachability after deletion in the subdivision.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- A source edge not incident with a cut gives a path between its centres
avoiding the cut centre in the subdivision. -/
theorem subdivision_adjacent_centres_reachable_avoiding {α β ν : Type*}
    {S : SimpleGraph ν} {N : Graph α β} {c : ν → α} (hc : Function.Injective c)
    {P : S.edgeSet → Graph α β}
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    {a b r : ν} (hab : S.Adj a b) (har : a ≠ r) (hbr : b ≠ r) :
    Relation.ReflTransGen (N.deleteVerts {c r}).Adj (c a) (c b) := by
  let e : S.edgeSet := ⟨s(a,b), hab⟩
  have hcentrePaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hrnot : c r ∉ V(P e) := by
    intro hm
    have hmem := (subdivision_centre_mem_path_iff hc hcentrePaths e r).mp hm
    change r ∈ s(a,b) at hmem
    rcases Sym2.mem_iff.mp hmem with h | h
    · exact har h.symm
    · exact hbr h.symm
  obtain ⟨a', b', he, hPath, _⟩ := hPaths e
  have hpair : s(a,b) = s(a',b') := he
  have hreach := (graphConnected_of_isGraphPath hPath).2
    (c a') hPath.left_mem (c b') hPath.right_mem
  have htarget : Relation.ReflTransGen (N.deleteVerts {c r}).Adj (c a') (c b') := by
    apply Relation.ReflTransGen.mono ?_ (c a') (c b') hreach
    intro x y hxy
    obtain ⟨edge, hlink⟩ := hxy
    have hx : x ≠ c r := fun heq ↦ hrnot (heq ▸ hlink.left_mem)
    have hy : y ≠ c r := fun heq ↦ hrnot (heq ▸ hlink.right_mem)
    exact ⟨edge, (N.deleteVerts_isLink {c r}).mpr ⟨hlink.mono hPath.le, hx, hy⟩⟩
  rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact htarget
  · exact Std.Symm.symm _ _ htarget

end GraphMinor.GM01
