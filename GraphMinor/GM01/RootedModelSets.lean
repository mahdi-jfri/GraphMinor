module

public import GraphMinor.GM01.RootedGraphs

/-!
# Lifting vertex sets through a rooted model

The contraction argument for Graph Minors I, (4.1), page 55, combines
rooted models. A set of source vertices lifts to the union of their
branches. The union lies in the target graph, and disjoint source sets
have disjoint lifts. These are the set properties needed to construct
the composite model without assuming the contraction step.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph

/-- The union of the branches representing vertices of a source set.
This is the branch construction for composing the rooted models used
in Graph Minors I, (4.1), page 55. -/
def RootedMinorModel.liftSet {α β γ δ : Type*} {H : RootedGraph α β}
    {G : RootedGraph γ δ} (M : RootedMinorModel H G) (S : Set α) : Set γ :=
  ⋃ v : V(H.graph), ⋃ (_ : v.val ∈ S), M.branch v

/-- Membership in the lifted set specifies its source vertex and branch. -/
theorem RootedMinorModel.mem_liftSet_iff {α β γ δ : Type*} {H : RootedGraph α β}
    {G : RootedGraph γ δ} (M : RootedMinorModel H G) (S : Set α) (x : γ) :
    x ∈ M.liftSet S ↔ ∃ v : V(H.graph), v.val ∈ S ∧ x ∈ M.branch v := by
  simp only [RootedMinorModel.liftSet, mem_iUnion, exists_prop]

/-- Every lifted vertex lies in the target graph. -/
theorem RootedMinorModel.liftSet_subset {α β γ δ : Type*} {H : RootedGraph α β}
    {G : RootedGraph γ δ} (M : RootedMinorModel H G) (S : Set α) :
    M.liftSet S ⊆ V(G.graph) := by
  intro x hx
  obtain ⟨v, _, hxv⟩ := (M.mem_liftSet_iff S x).mp hx
  exact M.branch_subset v hxv

/-- Lifting preserves inclusion of vertex sets. -/
theorem RootedMinorModel.liftSet_mono {α β γ δ : Type*} {H : RootedGraph α β}
    {G : RootedGraph γ δ} (M : RootedMinorModel H G) {S T : Set α} (hST : S ⊆ T) :
    M.liftSet S ⊆ M.liftSet T := by
  intro x hx
  obtain ⟨v, hv, hxv⟩ := (M.mem_liftSet_iff S x).mp hx
  exact (M.mem_liftSet_iff T x).mpr ⟨v, hST hv, hxv⟩

/-- Disjoint source sets lift to disjoint unions of branches. -/
theorem RootedMinorModel.liftSet_disjoint {α β γ δ : Type*} {H : RootedGraph α β}
    {G : RootedGraph γ δ} (M : RootedMinorModel H G) {S T : Set α} (hST : Disjoint S T) :
    Disjoint (M.liftSet S) (M.liftSet T) := by
  apply disjoint_left.mpr
  intro x hxS hxT
  obtain ⟨v, hvS, hxv⟩ := (M.mem_liftSet_iff S x).mp hxS
  obtain ⟨w, hwT, hxw⟩ := (M.mem_liftSet_iff T x).mp hxT
  by_cases hvw : v = w
  · subst w
    exact disjoint_left.mp hST hvS hwT
  · exact disjoint_left.mp (M.branch_disjoint hvw) hxv hxw

end GraphMinor.GM01
