module

public import GraphMinor.GM01.BinaryTrees
public import GraphMinor.GM01.ForestTrees
import GraphMinor.GM01.CombDegree
import Mathlib.Tactic.FinCases

/-!
# Degree bounds for the two trees in Part 3

Graph Minors I, page 60, replaces the tree minors by subdivisions.
Each binary vertex has at most its parent and its two children.
The three-branch tree has three neighbors at its centre and the
same parent-and-two-children bound elsewhere. The binary root has
only its two children. These explicit neighbor lists prove the
bounds needed by the subcubic subdivision construction.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

private theorem coe_neighborSet_ncard_eq {ν : Type*} (H : (⊤ : SimpleGraph ν).Subgraph) (v : H.verts) :
    (H.coe.neighborSet v).ncard = (H.neighborSet v.val).ncard := by
  have hsub : H.neighborSet v.val ⊆ range (Subtype.val : H.verts → ν) := by
    intro w hw
    exact ⟨⟨w, hw.snd_mem⟩, rfl⟩
  change (Subtype.val ⁻¹' H.neighborSet v.val).ncard = _
  exact Set.ncard_preimage_of_injective_subset_range Subtype.val_injective hsub

/-- A binary-tree vertex has at most its parent and its two children,
as used in GM01 Part 3, page 60. -/
theorem binaryTree_neighborSet_ncard_le_three (γ : ℕ) (word : List Bool) :
    ((binaryTree γ).neighborSet word).ncard ≤ 3 := by
  apply ncard_le_three_of_subset (a := word.tail) (b := false :: word) (c := true :: word)
  intro v hv
  rcases hv.2.2 with ⟨bit, rfl⟩ | ⟨bit, hword⟩
  · cases bit
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · exact Or.inl (by rw [hword]; rfl)

/-- The subcubic bound on the actual binary-tree vertex type. -/
theorem binaryTree_coe_neighborSet_ncard_le_three (γ : ℕ) (v : (binaryTree γ).verts) :
    ((binaryTree γ).coe.neighborSet v).ncard ≤ 3 := by
  rw [coe_neighborSet_ncard_eq]
  exact binaryTree_neighborSet_ncard_le_three γ v.val

/-- The distinguished binary root has at most its two children. -/
theorem binaryTree_root_neighborSet_ncard_le_two (γ : ℕ) :
    ((binaryTree γ).neighborSet []).ncard ≤ 2 := by
  have hsub : (binaryTree γ).neighborSet [] ⊆ {[false], [true]} := by
    intro word hw
    rcases hw.2.2 with ⟨bit, rfl⟩ | ⟨bit, h⟩
    · cases bit
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact False.elim (List.cons_ne_nil bit word h.symm)
  calc
    _ ≤ ({[false], [true]} : Set (List Bool)).ncard :=
      Set.ncard_le_ncard hsub ((Set.finite_singleton _).insert _)
    _ ≤ ({[true]} : Set (List Bool)).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

/-- The root degree bound on the binary tree's actual vertex type. -/
theorem binaryTree_root_coe_neighborSet_ncard_le_two (γ : ℕ) :
    ((binaryTree γ).coe.neighborSet (binaryRootedTree γ).root).ncard ≤ 2 := by
  change ((binaryTree γ).coe.neighborSet (⟨[], binaryTree_root_mem γ⟩ : (binaryTree γ).verts)).ncard ≤ 2
  rw [coe_neighborSet_ncard_eq]
  exact binaryTree_root_neighborSet_ncard_le_two γ

/-- At positive height the binary root has a neighbor, the word `[false]`. -/
theorem binaryTree_root_coe_neighborSet_nonempty {γ : ℕ} (hγ : 0 < γ) :
    ((binaryTree γ).coe.neighborSet (binaryRootedTree γ).root).Nonempty := by
  refine ⟨⟨[false], by change 1 ≤ γ; omega⟩, ?_⟩
  exact ⟨Nat.zero_le _, by change 1 ≤ γ; omega, Or.inl ⟨false, rfl⟩⟩

/-- Every vertex of `Y_γ` has at most three neighbors, as used on
page 60 of GM01 to select its subdivision. -/
theorem forestTree_neighborSet_ncard_le_three (γ : ℕ) (v : ForestTreeVertex) :
    ((forestTree γ).neighborSet v).ncard ≤ 3 := by
  cases v with
  | none =>
    apply ncard_le_three_of_subset (a := some (0, [])) (b := some (1, [])) (c := some (2, []))
    intro w hw
    rcases hw.2.2 with ⟨hwne, hp⟩ | ⟨hne, _⟩
    · cases w with
      | none => exact False.elim (hwne rfl)
      | some pair =>
        obtain ⟨branch, word⟩ := pair
        cases word with
        | nil => fin_cases branch <;> simp
        | cons bit rest => cases hp
    · exact False.elim (hne rfl)
  | some pair =>
    obtain ⟨branch, word⟩ := pair
    apply ncard_le_three_of_subset (a := forestTreeParent (some (branch, word)))
      (b := some (branch, false :: word)) (c := some (branch, true :: word))
    intro w hw
    rcases hw.2.2 with ⟨hwne, hp⟩ | ⟨_, hp⟩
    · cases w with
      | none => exact False.elim (hwne rfl)
      | some pair' =>
        obtain ⟨branch', word'⟩ := pair'
        cases word' with
        | nil => cases hp
        | cons bit rest =>
          have heq : (branch', rest) = (branch, word) := Option.some.inj hp
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          cases bit
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
    · exact Or.inl hp.symm

/-- The subcubic bound on the actual three-branch-tree vertex type. -/
theorem forestTree_coe_neighborSet_ncard_le_three (γ : ℕ) (v : (forestTree γ).verts) :
    ((forestTree γ).coe.neighborSet v).ncard ≤ 3 := by
  rw [coe_neighborSet_ncard_eq]
  exact forestTree_neighborSet_ncard_le_three γ v.val

end GraphMinor.GM01
