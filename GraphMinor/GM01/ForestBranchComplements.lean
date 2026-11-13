module

public import GraphMinor.GM01.ForestTrees
public import GraphMinor.Minor.Model
import GraphMinor.GM01.Basic
import Lean.Elab.Tactic.Omega

/-!
# Branches and connected bypasses in the three-branch tree

For observation (b) on page 40 of Graph Minors I, the three branches
of a sufficiently tall `Y` will each require a large bag. Removing
one branch leaves the centre and the other two branches connected.
Parent steps stay in this complement and reach the centre.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph

/-- One branch of `Y`, without its central vertex. -/
def forestTreeBranchVertices (lam : ℕ) (i : Fin 3) : Set ForestTreeVertex :=
  {v | v ∈ (forestTree lam).verts ∧ ∃ word, v = some (i, word)}

/-- The vertices left after removing one of the three branches. -/
def forestTreeBranchComplement (lam : ℕ) (i : Fin 3) : Set ForestTreeVertex :=
  {v | v ∈ (forestTree lam).verts ∧ ∀ word, v ≠ some (i, word)}

/-- Distinct branches of `Y` are disjoint. -/
theorem forestTreeBranchVertices_disjoint (lam : ℕ) :
    Pairwise fun i j ↦ Disjoint (forestTreeBranchVertices lam i) (forestTreeBranchVertices lam j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro v ⟨_, u, hu⟩ ⟨_, w, hw⟩
  exact hij (congrArg Prod.fst (Option.some.inj (hu.symm.trans hw)))

/-- Every other branch lies in the complement of the selected branch. -/
theorem forestTreeBranchVertices_subset_complement {lam : ℕ} {i j : Fin 3} (hji : j ≠ i) :
    forestTreeBranchVertices lam j ⊆ forestTreeBranchComplement lam i := by
  rintro v ⟨hv, word, rfl⟩
  refine ⟨hv, ?_⟩
  intro w he
  exact hji (congrArg Prod.fst (Option.some.inj he))

/-- The removed branch is disjoint from its complement. -/
theorem forestTreeBranchComplement_disjoint (lam : ℕ) (i : Fin 3) :
    Disjoint (forestTreeBranchComplement lam i) (forestTreeBranchVertices lam i) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨_, hc⟩ ⟨_, word, hw⟩
  exact hc word hw

/-- Taking a parent stays in the complement of one branch. -/
theorem forestTreeBranchComplement_parent {lam : ℕ} {i : Fin 3} {v : ForestTreeVertex}
    (hv : v ∈ forestTreeBranchComplement lam i) :
    forestTreeParent v ∈ forestTreeBranchComplement lam i := by
  refine ⟨forestTreeParent_mem hv.1, ?_⟩
  intro word he
  cases v with
  | none => cases he
  | some p =>
    rcases p with ⟨j, u⟩
    cases u with
    | nil => cases he
    | cons bit u =>
      have hji : j = i := congrArg Prod.fst (Option.some.inj he)
      exact hv.2 (bit :: u) (congrArg (fun k ↦ some (k, bit :: u)) hji)

/-- Deleting a branch leaves a connected subgraph through the centre. -/
theorem forestTreeBranchComplement_connected (lam : ℕ) (i : Fin 3) :
    GraphConnected ((forestTreeGraph lam).induce (forestTreeBranchComplement lam i)) := by
  have hcentre : none ∈ forestTreeBranchComplement lam i :=
    ⟨forestTree_centre_mem lam, fun _ h ↦ by cases h⟩
  have hroot : ∀ v ∈ forestTreeBranchComplement lam i,
      Relation.ReflTransGen ((forestTreeGraph lam).induce (forestTreeBranchComplement lam i)).Adj v none := by
    intro v hv
    induction hd : forestTreeDepth v using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases he : v = none
      · subst v
        exact .refl
      · have hp := forestTreeDepth_parent he
        have hlt : forestTreeDepth (forestTreeParent v) < n := by omega
        have hparent := forestTreeBranchComplement_parent hv
        have hpath := ih _ hlt (forestTreeParent v) hparent rfl
        obtain ⟨e, he'⟩ := (adj_toGraph (forestTree lam) _ _).mpr (forestTree_adj_parent hv.1 he)
        exact (Relation.ReflTransGen.single ⟨e, he', hv, hparent⟩).trans hpath
  refine ⟨⟨none, hcentre⟩, ?_⟩
  intro x hx y hy
  exact (hroot x hx).trans (Std.Symm.symm _ _ (hroot y hy))

end GraphMinor.GM01
