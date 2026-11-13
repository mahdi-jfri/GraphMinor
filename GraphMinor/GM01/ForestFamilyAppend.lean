module

public import GraphMinor.GM01.RootedForestFamilies
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Appending the old nonexceptional forest supports

At the end of Graph Minors I, (5.2), page 61, combine the new family
inside the component with the old nonexceptional supports. The latter
avoid both the component and the root path. Their ordinary minors
are unchanged. Index the two groups by a sum and identify that sum
with the required finite interval. The root set and its rooted minor
are retained.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- Append a disjoint group of actual forest supports to a rooted
family, the final set union in GM01 (5.2), page 61. -/
theorem exists_rooted_forest_family_append {α β : Type*} {G : RootedGraph α β}
    {γ n m : ℕ} (F : RootedForestFamily G γ n) (D : Fin m → Set α)
    (hD : ∀ j, D j ⊆ V(G.graph))
    (hMinor : ∀ j, IsIsoMinor (forestTreeGraph (γ - 1)) (G.graph.induce (D j)))
    (hDD : Pairwise fun i j ↦ Disjoint (D i) (D j))
    (hRoot : ∀ j, Disjoint F.rootSet (D j))
    (hCross : ∀ i j, Disjoint (F.otherSet i) (D j)) :
    Nonempty (RootedForestFamily G γ (n + m)) := by
  let A : Fin n ⊕ Fin m → Set α := Sum.elim F.otherSet D
  have hASub : ∀ i, A i ⊆ V(G.graph) := by
    rintro (i | j)
    · exact F.other_subset i
    · exact hD j
  have hAMinor : ∀ i, IsIsoMinor (forestTreeGraph (γ - 1)) (G.graph.induce (A i)) := by
    rintro (i | j)
    · exact F.other_minor i
    · exact hMinor j
  have hAD : Pairwise fun i j ↦ Disjoint (A i) (A j) := by
    rintro (i | i) (j | j) hij
    · exact F.other_disjoint (fun heq ↦ hij (congrArg Sum.inl heq))
    · exact hCross i j
    · exact (hCross j i).symm
    · exact hDD (fun heq ↦ hij (congrArg Sum.inr heq))
  have hARoot : ∀ i, Disjoint F.rootSet (A i) := by
    rintro (i | j)
    · exact F.root_disjoint i
    · exact hRoot j
  let e : Fin (n + m) ≃ Fin n ⊕ Fin m := finSumFinEquiv.symm
  exact ⟨{
    rootSet := F.rootSet
    otherSet := fun i ↦ A (e i)
    root_subset := F.root_subset
    other_subset := fun i ↦ hASub (e i)
    other_disjoint := fun _ _ hij ↦ hAD (e.injective.ne hij)
    root_disjoint := fun i ↦ hARoot (e i)
    root_mem := F.root_mem
    root_minor := F.root_minor
    other_minor := fun i ↦ hAMinor (e i) }⟩

end GraphMinor.GM01
