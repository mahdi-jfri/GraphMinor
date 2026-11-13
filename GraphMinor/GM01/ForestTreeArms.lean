module

public import GraphMinor.GM01.ForestTrees
public import GraphMinor.GM09.Basic
import GraphMinor.GM01.GraphSeparators
import GraphMinor.GM01.Basic

/-!
# Paths in one arm of the three-branch tree

The attachment contraction on page 60 of Graph Minors I uses two
branches for a binary tree and the remaining branch to reach its
root. One arm together with the centre is connected: following
parents stays in that arm and ends at the centre. Thus a root in
this arm can reach the centre without entering either other arm.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- One branch of `Y_γ`, including its centre. -/
def forestTreeArm (γ : ℕ) (k : Fin 3) : Set ForestTreeVertex :=
  {v | v ∈ (forestTree γ).verts ∧ (v = none ∨ ∃ word, v = some (k,word))}

/-- The common centre belongs to every arm. -/
theorem forestTreeArm_centre_mem (γ : ℕ) (k : Fin 3) : none ∈ forestTreeArm γ k :=
  ⟨forestTree_centre_mem γ, Or.inl rfl⟩

/-- Taking a parent stays in the selected arm. -/
theorem forestTreeArm_parent_mem {γ : ℕ} {k : Fin 3} {v : ForestTreeVertex}
    (hv : v ∈ forestTreeArm γ k) : forestTreeParent v ∈ forestTreeArm γ k := by
  refine ⟨forestTreeParent_mem hv.1, ?_⟩
  rcases hv.2 with rfl | ⟨word,rfl⟩
  · exact Or.inl rfl
  · cases word with
    | nil => exact Or.inl rfl
    | cons bit word => exact Or.inr ⟨word,rfl⟩

/-- Parent steps in the induced arm reach its centre. -/
theorem forestTreeArm_reachable_centre {γ : ℕ} {k : Fin 3} {v : ForestTreeVertex}
    (hv : v ∈ forestTreeArm γ k) :
    Relation.ReflTransGen ((forestTreeGraph γ).induce (forestTreeArm γ k)).Adj v none := by
  induction hd : forestTreeDepth v using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases h : v = none
    · subst v
      exact .refl
    · have hp := forestTreeDepth_parent h
      have hlt : forestTreeDepth (forestTreeParent v) < n := by omega
      have hparent := forestTreeArm_parent_mem hv
      have hr := ih _ hlt hparent rfl
      have hadj := (adj_toGraph (forestTree γ) _ _).mpr (forestTree_adj_parent hv.1 h)
      have hedge : ((forestTreeGraph γ).induce (forestTreeArm γ k)).Adj v (forestTreeParent v) := by
        obtain ⟨e,he⟩ := hadj
        exact ⟨e,he,hv,hparent⟩
      exact (Relation.ReflTransGen.single hedge).trans hr

/-- A root in the third arm has a path to the centre wholly inside
that arm, the root path used for the page-60 attachment contraction. -/
theorem exists_path_in_forestTreeArm {γ : ℕ} {k : Fin 3} {v : ForestTreeVertex}
    (hv : v ∈ forestTreeArm γ k) :
    ∃ R : Graph ForestTreeVertex (Sym2 ForestTreeVertex),
      IsGraphPathWithEnds (forestTreeGraph γ) R v none ∧ V(R) ⊆ forestTreeArm γ k := by
  obtain ⟨R,hR⟩ := exists_path_of_adj_reachable hv (forestTreeArm_reachable_centre hv)
  exact ⟨R,hR.mono ((forestTreeGraph γ).induce_le (fun _ hx ↦ hx.1)), hR.le.vertexSet_mono⟩

end GraphMinor.GM01
