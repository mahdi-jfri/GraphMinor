module

public import GraphMinor.GM01.ForestTrees
public import GraphMinor.GM01.RootedGraphs
import GraphMinor.GM01.Basic
import Mathlib.Data.Set.Finite.List

/-!
# The binary trees in the rooted forest-exclusion argument

The proof of Graph Minors I, (1.1), uses the rooted reduction through (3.1).
The trees `H_ℓ` in that reduction are binary trees. We label their vertices
by binary words of length at most `ℓ`, with the empty word as root. Each
edge removes or adds the first bit. Their embedding in a branch of `Y`
proves acyclicity, and parent paths prove connectedness.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

/-- The binary tree `H_ℓ` of Graph Minors I, Section 3, page 51: `H_0` is a
single vertex, `H_1` is `K_{1,2}`, and each later tree adds two neighbours
at every leaf. The root is the empty word. -/
def binaryTree (ℓ : ℕ) : (⊤ : SimpleGraph (List Bool)).Subgraph where
  verts := {word | word.length ≤ ℓ}
  Adj x y := x.length ≤ ℓ ∧ y.length ≤ ℓ ∧
    ((∃ bit, y = bit :: x) ∨ ∃ bit, x = bit :: y)
  adj_sub := by
    intro x y h
    apply (top_adj _ _).2
    intro hxy
    subst y
    rcases h.2.2 with ⟨bit, h⟩ | ⟨bit, h⟩ <;>
      have := congrArg List.length h <;> simp only [List.length_cons] at this <;> omega
  edge_vert := fun h ↦ h.1
  symm := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, h.2.2.symm⟩⟩

/-- The root is a vertex at every depth. -/
theorem binaryTree_root_mem (ℓ : ℕ) : [] ∈ (binaryTree ℓ).verts :=
  Nat.zero_le ℓ

/-- The binary trees have finite vertex sets. -/
theorem binaryTree_vertices_finite (ℓ : ℕ) : (binaryTree ℓ).verts.Finite :=
  List.finite_length_le Bool ℓ

/-- The multigraph `H_ℓ` with its distinguished root. -/
def binaryRootedTree (ℓ : ℕ) : RootedGraph (List Bool) (Sym2 (List Bool)) where
  graph := toGraph (binaryTree ℓ)
  root := ⟨[], binaryTree_root_mem ℓ⟩

/-- The word representation of `H_0` has just its root. -/
theorem binaryTree_zero_verts : (binaryTree 0).verts = {[]} := by
  ext word
  simp only [binaryTree, Set.mem_ofPred_eq, Nat.le_zero, Set.mem_singleton_iff]
  exact List.length_eq_zero_iff

/-- Increasing the depth retains every vertex and edge. -/
theorem binaryTree_mono {ℓ m : ℕ} (h : ℓ ≤ m) : binaryTree ℓ ≤ binaryTree m :=
  ⟨fun _ hw ↦ hw.trans h, fun _ _ hxy ↦ ⟨hxy.1.trans h, hxy.2.1.trans h, hxy.2.2⟩⟩

/-- Every word is reached from the empty word by adding its bits. -/
theorem binaryTree_reachable_root (ℓ : ℕ) {word : List Bool}
    (hw : word ∈ (binaryTree ℓ).verts) :
    Relation.ReflTransGen (toGraph (binaryTree ℓ)).Adj [] word := by
  induction word with
  | nil => exact .refl
  | cons bit word ih =>
    have hword : word ∈ (binaryTree ℓ).verts := by
      change (bit :: word).length ≤ ℓ at hw
      change word.length ≤ ℓ
      simp only [List.length_cons] at hw
      omega
    exact (ih hword).tail ((adj_toGraph (binaryTree ℓ) _ _).2
      ⟨hword, hw, Or.inl ⟨bit, rfl⟩⟩)

/-- Parent paths connect every binary-tree vertex to the root. -/
theorem binaryTree_connected (ℓ : ℕ) : (binaryTree ℓ).Connected := by
  apply (graphConnected_toGraph_iff _).mp
  refine ⟨⟨[], binaryTree_root_mem ℓ⟩, ?_⟩
  intro x hx y hy
  have symm {a b : List Bool} (h : Relation.ReflTransGen (toGraph (binaryTree ℓ)).Adj a b) :
      Relation.ReflTransGen (toGraph (binaryTree ℓ)).Adj b a := by
    induction h with
    | refl => exact .refl
    | @tail c d hab hcd ih => exact (Relation.ReflTransGen.single hcd.symm).trans ih
  exact (symm (binaryTree_reachable_root ℓ hx)).trans (binaryTree_reachable_root ℓ hy)

/-- Place the binary tree in branch zero of the next `Y` tree. The empty
word goes to the first vertex on that branch, and bits are preserved. -/
def binaryTree_branch_embedding (ℓ : ℕ) :
    (binaryTree ℓ).coe →g (forestTree (ℓ + 1)).coe where
  toFun word := ⟨some (0, word.val), Nat.add_le_add_right word.property 1⟩
  map_rel' := by
    intro x y hxy
    refine ⟨Nat.add_le_add_right x.property 1, Nat.add_le_add_right y.property 1, ?_⟩
    rcases hxy.2.2 with ⟨bit, hy⟩ | ⟨bit, hx⟩
    · exact Or.inl ⟨by simp, by simp only [hy, forestTreeParent]⟩
    · exact Or.inr ⟨by simp, by simp only [hx, forestTreeParent]⟩

/-- The branch embedding is injective on vertices. -/
theorem binaryTree_branch_embedding_injective (ℓ : ℕ) :
    Function.Injective (binaryTree_branch_embedding ℓ) := by
  intro x y hxy
  apply Subtype.ext
  have heq := congrArg Subtype.val hxy
  exact congrArg Prod.snd (Option.some.inj heq)

/-- A binary tree is acyclic because it embeds in an acyclic `Y` tree. -/
theorem binaryTree_isAcyclic (ℓ : ℕ) : (binaryTree ℓ).coe.IsAcyclic :=
  (forestTree_isAcyclic (ℓ + 1)).comap (binaryTree_branch_embedding ℓ)
    (binaryTree_branch_embedding_injective ℓ)

/-- The finite connected acyclic binary-tree construction is a tree. -/
theorem binaryTree_isTree (ℓ : ℕ) : IsTreeSubgraph (binaryTree ℓ) :=
  ⟨binaryTree_connected ℓ, binaryTree_isAcyclic ℓ⟩

end GraphMinor.GM01
