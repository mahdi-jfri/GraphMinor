module

public import GraphMinor.GM01.RootedBranchModels
public import GraphMinor.GM09.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.GM01.RootedSubdivisionAttachment

/-!
# Root-preserving contraction of a finite subdivision

The skipped-block construction in Graph Minors I, (4.1), page 55, needs
the first retained spine centre in its root branch. Orient source edges
by an injective rank and remove the last edge of each replacing path.
Assign its remaining prefix to the earlier end. Prefixes meet other
prefixes only at their own source centres, so these branch sets are
disjoint and connected. The removed last edges join the branches.
Every centre stays in its own branch, which preserves any chosen root.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- Contract the replacing paths with every source centre in its own
branch. In particular, the specified centre is the target root of the
constructed rooted model. This is the direct path contraction needed
for the skipped block in GM01 (4.1), page 55. -/
noncomputable def rootedModelOfFiniteSubdivision {α β ν : Type*} [Finite ν]
    {S : SimpleGraph ν} {G : Graph α β} (c : ν → α) (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(G)) (P : S.edgeSet → Graph α β)
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds G (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (root : ν) :
    RootedMinorModel
      (⟨Graph.ofSimpleGraph S, ⟨root, mem_univ _⟩⟩ : RootedGraph ν (Sym2 ν))
      (⟨G, ⟨c root, hcentres root⟩⟩ : RootedGraph α β) := by
  exact rootedModelOfFiniteSubdivisionAtVertex c hc hcentres P hPaths hInter root
    ⟨c root, hcentres root⟩ (Or.inl rfl)

end GraphMinor.GM01
