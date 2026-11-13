module

public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM09.Defs
import GraphMinor.GM01.ForestFamilyRootPath
import GraphMinor.GM01.ForestFamilyAppend
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Lean.Elab.Tactic.Omega

/-!
# The maximal-family contradiction in the inside component

Graph Minors I, (5.2), page 61, replaces the exceptional old supports
by more new supports in the component. Extend the new root support
along the actual root path, then append every old nonexceptional
support. Their total is the new family size plus the size of the
complement of the exceptional set. Since the new size exceeds the
exceptional size, this contradicts the maximum choice of the old family.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- The final set construction and count contradiction in GM01 (5.2),
page 61. Maximality is the actual choice of the old family. Every set
of the larger family is constructed by root extension and appending. -/
theorem false_of_larger_component_forest_family {α β : Type*} {γ n m : ℕ}
    (G C : RootedGraph α β) (hCG : C.graph ≤ G.graph)
    (F : RootedForestFamily G γ n)
    (hMax : ∀ k, RootedForestFamily G γ k → k ≤ n)
    (FNew : RootedForestFamily C γ m) (J : Set (Fin n)) (hLarge : J.ncard < m)
    (hAvoid : ∀ j ∉ J, Disjoint V(C.graph) (F.otherSet j))
    {P : Graph α β} (hP : GraphMinor.GM09.IsGraphPathWithEnds G.graph P G.root.val C.root.val)
    (hMeet : V(P) ∩ V(C.graph) = {C.root.val}) (hPS : V(P) ⊆ F.rootSet) : False := by
  classical
  obtain ⟨FExt,hRootEq,hOtherEq⟩ := exists_rooted_forest_family_with_root_path G C hCG FNew hP hMeet
  let K := {j : Fin n // j ∉ J}
  let : Fintype K := Fintype.ofFinite K
  have hKCard : Fintype.card K = Jᶜ.ncard := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  let e : Fin Jᶜ.ncard ≃ K := (Fintype.equivFinOfCardEq hKCard).symm
  let D := fun i : Fin Jᶜ.ncard ↦ F.otherSet (e i).val
  have hDSub : ∀ i, D i ⊆ V(G.graph) := fun i ↦ F.other_subset (e i).val
  have hDMinor : ∀ i, IsIsoMinor (forestTreeGraph (γ - 1)) (G.graph.induce (D i)) :=
    fun i ↦ F.other_minor (e i).val
  have hDD : Pairwise fun i j ↦ Disjoint (D i) (D j) := by
    intro i j hij
    apply F.other_disjoint
    intro heq
    exact hij (e.injective (Subtype.ext heq))
  have hRootD : ∀ j, Disjoint FExt.rootSet (D j) := by
    intro j
    rw [hRootEq]
    exact ((hAvoid (e j).val (e j).property).mono_left FNew.root_subset).union_left
      ((F.root_disjoint (e j).val).mono_left hPS)
  have hCross : ∀ i j, Disjoint (FExt.otherSet i) (D j) := by
    intro i j
    rw [hOtherEq i]
    exact (hAvoid (e j).val (e j).property).mono_left (FNew.other_subset i)
  obtain ⟨FLarge⟩ := exists_rooted_forest_family_append FExt D hDSub hDMinor hDD hRootD hCross
  have hBound := hMax _ FLarge
  have hCount : Jᶜ.ncard + J.ncard = n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using ncard_compl_add_ncard J
  omega

end GraphMinor.GM01
