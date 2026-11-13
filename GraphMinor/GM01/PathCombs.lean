module

public import GraphMinor.GM01.BinaryTrees
import Mathlib.Data.Set.Finite.List

/-!
# The rooted path of binary trees

Graph Minors I, Section 3, page 53, defines `P(γ, δ)` by attaching a copy
of `H_{γ-1}` at each vertex of a `δ`-vertex path, with the first path vertex
as root. For `γ = 0`, there are no attached copies. This is the rooted
configuration used in the bound (3.1), and hence in the proof of (1.1).
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

/-- A spine vertex or a word in the binary tree attached at a spine vertex. -/
abbrev PathCombVertex (δ : ℕ) := Fin δ ⊕ (Fin δ × List Bool)

/-- Vertex set of the rooted tree `P(γ, δ)` from Graph Minors I, Section 3,
page 53. The words in an attached copy have length less than `γ`, so that
copy is `H_{γ-1}` when `γ ≥ 1`. -/
def pathCombVertices (γ δ : ℕ) : Set (PathCombVertex δ) :=
  {v | match v with
    | .inl _ => True
    | .inr (_, word) => word.length < γ}

/-- The adjacency rule for the paper's `P(γ, δ)`: consecutive spine
vertices, an attachment to an empty word, or an edge in one binary copy. -/
def PathCombAdj (γ δ : ℕ) : PathCombVertex δ → PathCombVertex δ → Prop
  | .inl i, .inl j => (pathGraph δ).Adj i j
  | .inl i, .inr (j, word) => i = j ∧ word = [] ∧ 0 < γ
  | .inr (i, word), .inl j => i = j ∧ word = [] ∧ 0 < γ
  | .inr (i, word), .inr (j, word') =>
      i = j ∧ word.length < γ ∧ word'.length < γ ∧
        ((∃ bit, word' = bit :: word) ∨ ∃ bit, word = bit :: word')

/-- The tree `P(γ, δ)` in Graph Minors I, Section 3, page 53, before
specifying the root. Its spine has exactly `δ` vertices. -/
def pathComb (γ δ : ℕ) : (⊤ : SimpleGraph (PathCombVertex δ)).Subgraph where
  verts := pathCombVertices γ δ
  Adj := PathCombAdj γ δ
  adj_sub := by
    intro x y h
    apply (top_adj _ _).2
    intro hxy
    subst y
    cases x with
    | inl i => exact h.ne rfl
    | inr p =>
      rcases h.2.2.2 with ⟨bit, heq⟩ | ⟨bit, heq⟩ <;>
        have hd := congrArg List.length heq <;>
        simp only [List.length_cons] at hd <;> omega
  edge_vert := by
    intro x y h
    cases x with
    | inl i => trivial
    | inr p =>
      cases y with
      | inl j =>
        change p.2.length < γ
        rw [h.2.1]
        exact h.2.2
      | inr q => exact h.2.1
  symm := ⟨by
    intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact h.symm
      | inr q => exact ⟨h.1.symm, h.2⟩
    | inr p =>
      cases y with
      | inl j => exact ⟨h.1.symm, h.2⟩
      | inr q => exact ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.symm⟩⟩

/-- Every path vertex occurs in the comb. -/
theorem pathComb_spine_mem (γ δ : ℕ) (i : Fin δ) : Sum.inl i ∈ (pathComb γ δ).verts :=
  True.intro

/-- The rooted tree `P(γ, δ)` from Graph Minors I, Section 3, page 53. The
root is the first path vertex. The assumption `δ > 0` is part of the
paper's definition. -/
def rootedPathComb (γ δ : ℕ) (hδ : 0 < δ) :
    RootedGraph (PathCombVertex δ) (Sym2 (PathCombVertex δ)) where
  graph := toGraph (pathComb γ δ)
  root := ⟨Sum.inl ⟨0, hδ⟩, pathComb_spine_mem γ δ _⟩

/-- All attached copies and the spine have finitely many vertices. -/
theorem pathComb_vertices_finite (γ δ : ℕ) : (pathComb γ δ).verts.Finite := by
  have hspine := (Set.finite_univ : (Set.univ : Set (Fin δ)).Finite).image
    (Sum.inl : Fin δ → PathCombVertex δ)
  have hcopies := ((Set.finite_univ : (Set.univ : Set (Fin δ)).Finite).prod
    (List.finite_length_lt Bool γ)).image (Sum.inr : Fin δ × List Bool → PathCombVertex δ)
  apply (hspine.union hcopies).subset
  intro v hv
  cases v with
  | inl i => exact Or.inl ⟨i, Set.mem_univ _, rfl⟩
  | inr p => exact Or.inr ⟨p, ⟨Set.mem_univ _, hv⟩, rfl⟩

/-- At `γ = 0` there are only spine vertices. -/
theorem pathComb_zero_verts (δ : ℕ) :
    (pathComb 0 δ).verts = Set.range (Sum.inl : Fin δ → PathCombVertex δ) := by
  ext v
  cases v <;> simp [pathComb, pathCombVertices]

/-- Consecutive spine vertices retain their path edge. -/
theorem pathComb_spine_adj {γ δ : ℕ} {i j : Fin δ} (h : (pathGraph δ).Adj i j) :
    (pathComb γ δ).Adj (Sum.inl i) (Sum.inl j) := h

/-- Each spine vertex is joined to the root of its attached binary copy. -/
theorem pathComb_attachment_adj {γ δ : ℕ} (hγ : 0 < γ) (i : Fin δ) :
    (pathComb γ δ).Adj (Sum.inl i) (Sum.inr (i, [])) := ⟨rfl, rfl, hγ⟩

/-- Increasing the binary-copy depth retains every vertex and edge. -/
theorem pathComb_mono {γ γ' δ : ℕ} (h : γ ≤ γ') : pathComb γ δ ≤ pathComb γ' δ := by
  constructor
  · intro v hv
    cases v with
    | inl i => trivial
    | inr p => exact lt_of_lt_of_le hv h
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact hxy
      | inr q => exact ⟨hxy.1, hxy.2.1, lt_of_lt_of_le hxy.2.2 h⟩
    | inr p =>
      cases y with
      | inl j => exact ⟨hxy.1, hxy.2.1, lt_of_lt_of_le hxy.2.2 h⟩
      | inr q => exact ⟨hxy.1, lt_of_lt_of_le hxy.2.1 h,
          lt_of_lt_of_le hxy.2.2.1 h, hxy.2.2.2⟩

end GraphMinor.GM01
