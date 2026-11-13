module

public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM01.RootedForks
import GraphMinor.GM01.ForkFourInitialMinors
import GraphMinor.GM01.RootedModelComposition
import Mathlib.Data.Finset.Max

/-!
# Choosing a maximum disjoint forest family

Graph Minors I, Section 5, page 60, chooses the number `N` maximum
subject to (X1) and (X2). A rooted `H_γ` model supplies the family
with no other sets. Every admissible size is bounded by the finite
target vertex count, so the nonempty finite set of admissible sizes
has a maximum. The initial four-fork minor supplies the required
rooted binary-tree model by the proved source contraction.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- The actual maximal-family choice with (X1) and (X2), GM01 page 60.
The maximum ranges over all families satisfying exactly those conditions. -/
theorem exists_max_rooted_forest_family {α β : Type*} (G : RootedGraph α β) (γ : ℕ)
    (hfin : V(G.graph).Finite) (h : HasRootedMinor (binaryRootedTree γ) G) :
    ∃ N : ℕ, ∃ _F : RootedForestFamily G γ N,
      ∀ n : ℕ, RootedForestFamily G γ n → n ≤ N := by
  classical
  let S : Set ℕ := {n | Nonempty (RootedForestFamily G γ n)}
  have hsub : S ⊆ (Finset.range (V(G.graph).ncard + 1) : Set ℕ) := by
    rintro n ⟨F⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (F.card_le hfin))
  have hSfin : S.Finite := (Finset.finite_toSet _).subset hsub
  let s := hSfin.toFinset
  have hs : s.Nonempty := ⟨0, hSfin.mem_toFinset.mpr ⟨RootedForestFamily.root_only G γ h⟩⟩
  let N := s.max' hs
  obtain ⟨F⟩ : Nonempty (RootedForestFamily G γ N) := hSfin.mem_toFinset.mp (Finset.max'_mem s hs)
  refine ⟨N, F, ?_⟩
  intro n F'
  exact Finset.le_max' s n (hSfin.mem_toFinset.mpr ⟨F'⟩)

/-- The four-fork case at the start of Part 3 supplies the maximal
family chosen on page 60 of GM01. -/
theorem exists_max_rooted_forest_family_of_four_fork {α β : Type*}
    (G : RootedGraph α β) (hfin : V(G.graph).Finite) {γ : ℕ} (hγ : 0 < γ)
    (h : HasRootedMinor (rootedForkGraph γ 4 hγ (by decide)) G) :
    ∃ N : ℕ, ∃ _F : RootedForestFamily G γ N,
      ∀ n : ℕ, RootedForestFamily G γ n → n ≤ N := by
  obtain ⟨M⟩ := h
  exact exists_max_rooted_forest_family G γ hfin ⟨(rootedBinaryTreeModelOfForkFour hγ).trans M⟩

end GraphMinor.GM01
