module

public import GraphMinor.GM01.PathCombs
public import GraphMinor.GM01.BinaryTrees
import GraphMinor.GM01.PathCombTrees
import GraphMinor.GM01.Basic

/-!
# The rooted fork configuration

The positive-height induction needed for Graph Minors I, (1.1), uses the
configuration `Q(γ,δ)` of Section 3, page 53. Take disjoint copies of
`P(γ−1,δ−1)` and `H_{γ−1}`, add a new root, and join it to the two old
roots. We use option and sum labels to keep those copies disjoint.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

/-- A new root, a vertex of the path comb, or a word in the binary copy. -/
abbrev RootedForkVertex (δ : ℕ) := Option (PathCombVertex (δ - 1) ⊕ List Bool)

/-- The root of the path comb used inside `Q(γ,δ)`. -/
def rootedForkAnchor (δ : ℕ) (hδ : 2 ≤ δ) : PathCombVertex (δ - 1) :=
  Sum.inl ⟨0, by omega⟩

/-- Vertex set of the rooted fork construction. -/
def rootedForkVertices (γ δ : ℕ) : Set (RootedForkVertex δ) :=
  {v | match v with
    | none => True
    | some (.inl p) => p ∈ (pathComb (γ - 1) (δ - 1)).verts
    | some (.inr word) => word ∈ (binaryTree (γ - 1)).verts}

/-- Edges inside the two copies and the two new edges to their roots. -/
def RootedForkAdj (γ δ : ℕ) (hδ : 2 ≤ δ) :
    RootedForkVertex δ → RootedForkVertex δ → Prop
  | none, none => False
  | none, some (.inl p) => p = rootedForkAnchor δ hδ
  | some (.inl p), none => p = rootedForkAnchor δ hδ
  | none, some (.inr word) => word = []
  | some (.inr word), none => word = []
  | some (.inl p), some (.inl q) => (pathComb (γ - 1) (δ - 1)).Adj p q
  | some (.inr word), some (.inr word') => (binaryTree (γ - 1)).Adj word word'
  | some (.inl _), some (.inr _) => False
  | some (.inr _), some (.inl _) => False

/-- The graph `Q(γ,δ)` of Graph Minors I, Section 3, page 53, for `γ ≥ 1`
and `δ ≥ 2`. The formula also defines a graph at `γ = 0`, which is not
used as a paper configuration. -/
def rootedFork (γ δ : ℕ) (hδ : 2 ≤ δ) :
    (⊤ : SimpleGraph (RootedForkVertex δ)).Subgraph where
  verts := rootedForkVertices γ δ
  Adj := RootedForkAdj γ δ hδ
  adj_sub := by
    intro x y h
    apply (top_adj _ _).2
    intro hxy
    subst y
    cases x with
    | none => exact h
    | some x =>
      cases x with
      | inl p => exact h.ne rfl
      | inr word => exact h.ne rfl
  edge_vert := by
    intro x y h
    cases x with
    | none => trivial
    | some x =>
      cases x with
      | inl p =>
        cases y with
        | none =>
          change p ∈ (pathComb (γ - 1) (δ - 1)).verts
          rw [h]
          exact pathComb_spine_mem (γ - 1) (δ - 1) ⟨0, by omega⟩
        | some y =>
          cases y with
          | inl q => exact h.fst_mem
          | inr word => exact False.elim h
      | inr word =>
        cases y with
        | none => rw [h]; exact binaryTree_root_mem _
        | some y =>
          cases y with
          | inl p => exact False.elim h
          | inr word' => exact h.fst_mem
  symm := ⟨by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => exact h
      | some y => cases y <;> exact h
    | some x =>
      cases x with
      | inl p =>
        cases y with
        | none => exact h
        | some y =>
          cases y with
          | inl q => exact h.symm
          | inr word => exact h
      | inr word =>
        cases y with
        | none => exact h
        | some y =>
          cases y with
          | inl p => exact h
          | inr word' => exact h.symm⟩

/-- The new vertex is the distinguished root of `Q(γ,δ)`. -/
def rootedForkGraph (γ δ : ℕ) (_hγ : 0 < γ) (hδ : 2 ≤ δ) :
    RootedGraph (RootedForkVertex δ) (Sym2 (RootedForkVertex δ)) where
  graph := toGraph (rootedFork γ δ hδ)
  root := ⟨none, True.intro⟩

/-- Both old configurations are joined to the new root by their stated
new edges. -/
theorem rootedFork_root_adj_comb (γ δ : ℕ) (hδ : 2 ≤ δ) :
    (rootedFork γ δ hδ).Adj none (some (Sum.inl (rootedForkAnchor δ hδ))) := rfl

/-- The second new edge joins the new root to the binary-tree root. -/
theorem rootedFork_root_adj_binary (γ δ : ℕ) (hδ : 2 ≤ δ) :
    (rootedFork γ δ hδ).Adj none (some (Sum.inr [])) := rfl

/-- The two finite copies and the new root give a finite vertex set. -/
theorem rootedFork_vertices_finite (γ δ : ℕ) (hδ : 2 ≤ δ) :
    (rootedFork γ δ hδ).verts.Finite := by
  have hP := (pathComb_vertices_finite (γ - 1) (δ - 1)).image
    (fun p ↦ (some (Sum.inl p) : RootedForkVertex δ))
  have hH := (binaryTree_vertices_finite (γ - 1)).image
    (fun word ↦ (some (Sum.inr word) : RootedForkVertex δ))
  apply (((Set.finite_singleton none).union hP).union hH).subset
  intro v hv
  cases v with
  | none => exact Or.inl (Or.inl rfl)
  | some v =>
    cases v with
    | inl p => exact Or.inl (Or.inr ⟨p, hv, rfl⟩)
    | inr word => exact Or.inr ⟨word, hv, rfl⟩

/-- Every vertex of the two copies is reached from its old root and hence
from the new root. -/
theorem rootedFork_connected (γ δ : ℕ) (hδ : 2 ≤ δ) : (rootedFork γ δ hδ).Connected := by
  let Q := rootedFork γ δ hδ
  let P := pathComb (γ - 1) (δ - 1)
  let H := binaryTree (γ - 1)
  have liftP {a b : PathCombVertex (δ - 1)} (h : Relation.ReflTransGen (toGraph P).Adj a b) :
      Relation.ReflTransGen (toGraph Q).Adj (some (Sum.inl a)) (some (Sum.inl b)) := by
    induction h with
    | refl => exact .refl
    | @tail c d hab hcd ih =>
      exact ih.tail ((adj_toGraph Q _ _).mpr hcd.choose_spec.2)
  have liftH {a b : List Bool} (h : Relation.ReflTransGen (toGraph H).Adj a b) :
      Relation.ReflTransGen (toGraph Q).Adj (some (Sum.inr a)) (some (Sum.inr b)) := by
    induction h with
    | refl => exact .refl
    | @tail c d hab hcd ih =>
      exact ih.tail ((adj_toGraph Q _ _).mpr hcd.choose_spec.2)
  have hroot : ∀ v ∈ Q.verts, Relation.ReflTransGen (toGraph Q).Adj none v := by
    intro v hv
    cases v with
    | none => exact .refl
    | some v =>
      cases v with
      | inl p =>
        have hP := (graphConnected_toGraph_iff P).mpr (pathComb_connected (γ := γ - 1) (by omega))
        have hpath := hP.2 (rootedForkAnchor δ hδ) (pathComb_spine_mem _ _ _) p hv
        exact (Relation.ReflTransGen.single
          ((adj_toGraph Q _ _).mpr (rootedFork_root_adj_comb γ δ hδ))).trans (liftP hpath)
      | inr word =>
        have hH := (graphConnected_toGraph_iff H).mpr (binaryTree_connected (γ - 1))
        have hpath := hH.2 [] (binaryTree_root_mem _) word hv
        exact (Relation.ReflTransGen.single
          ((adj_toGraph Q _ _).mpr (rootedFork_root_adj_binary γ δ hδ))).trans (liftH hpath)
  apply (graphConnected_toGraph_iff Q).mp
  exact ⟨⟨none, True.intro⟩, fun x hx y hy ↦
    (Std.Symm.symm _ _ (hroot x hx)).trans (hroot y hy)⟩

end GraphMinor.GM01
