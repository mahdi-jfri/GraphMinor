module

public import GraphMinor.Kruskal.SubdivisionNames
import Mathlib.Data.Set.Finite.Lattice

/-!
# Replacing graph edges by chains

Each edge has a prescribed number of internal vertices. Give those vertices
names `(e, k)`. The first segments use odd labels and the final segment uses
an even label. Inserting one more vertex removes that even label and creates
the next odd and even labels, both fresh. These names permit literal edge
subdivision steps, without renaming an edge during a step.
-/

@[expose] public section

namespace GraphMinor.Kruskal

open Graph Set

/-- The vertex immediately before segment `k` on the chain for `e`. -/
def chainStem {V E : Type*} (left : E → V) (e : E) : ℕ → V ⊕ (E × ℕ)
  | 0 => Sum.inl (left e)
  | k + 1 => Sum.inr (e, k)

/-- A chain with `n e` internal vertices has odd labels for its first
segments and label `2 * n e` for its final segment. -/
def chainSlot {E : Type*} (n : E → ℕ) (d : E × ℕ) : Prop :=
  d.2 = 2 * n d.1 ∨ d.2 % 2 = 1 ∧ d.2 < 2 * n d.1

/-- The end of a segment is the original right end for the final segment,
and its indexed internal vertex for every other segment. -/
noncomputable def chainFinish {V E : Type*} (right : E → V) (n : E → ℕ)
    (d : E × ℕ) : V ⊕ (E × ℕ) := by
  classical
  exact if d.2 = 2 * n d.1 then Sum.inl (right d.1) else Sum.inr (d.1, d.2 / 2)

/-- The graph obtained by replacing every edge index by its chain. The
original vertices remain present, even if they are isolated. -/
noncomputable def edgeChains {V E : Type*} (left right : E → V) (n : E → ℕ) :
    Graph (V ⊕ (E × ℕ)) (E × ℕ) where
  vertexSet := {x | match x with
    | Sum.inl _ => True
    | Sum.inr (e, k) => k < n e}
  edgeSet := {d | chainSlot n d}
  IsLink d x y := chainSlot n d ∧
    ((x = chainStem left d.1 (d.2 / 2) ∧ y = chainFinish right n d) ∨
      (x = chainFinish right n d ∧ y = chainStem left d.1 (d.2 / 2)))
  isLink_symm _ _ := ⟨by
    rintro x y ⟨hd, h⟩
    exact ⟨hd, h.elim (fun h ↦ Or.inr h.symm) (fun h ↦ Or.inl h.symm)⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro d x y z w ⟨_, h₁⟩ ⟨_, h₂⟩
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink d :=
    ⟨fun hd ↦ ⟨_, _, hd, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, hd, _⟩ ↦ hd⟩
  left_mem_of_isLink := by
    rintro ⟨e, j⟩ x y ⟨hslot, h⟩
    change j = 2 * n e ∨ j % 2 = 1 ∧ j < 2 * n e at hslot
    have hstem : (match chainStem left e (j / 2) with
        | Sum.inl _ => True | Sum.inr (e', k) => k < n e') := by
      have hbound : j / 2 ≤ n e := by
        rcases hslot with h | ⟨hodd, hlt⟩ <;> omega
      cases hk : j / 2 with
      | zero => trivial
      | succ k =>
        change k < n e
        omega
    have hfinish : (match chainFinish right n (e, j) with
        | Sum.inl _ => True | Sum.inr (e', k) => k < n e') := by
      classical
      unfold chainFinish
      dsimp only [Prod.fst, Prod.snd]
      split_ifs with hj
      · trivial
      · change j / 2 < n e
        rcases hslot with h | ⟨hodd, hlt⟩ <;> omega
    rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hstem
    · exact hfinish

/-- Every edge index always has its final segment. -/
theorem edgeChains_final_link {V E : Type*} (left right : E → V) (n : E → ℕ) (e : E) :
    (edgeChains left right n).IsLink (e, 2 * n e)
      (chainStem left e (n e)) (Sum.inl (right e)) := by
  classical
  have hdiv : 2 * n e / 2 = n e := by omega
  refine ⟨Or.inl rfl, Or.inl ⟨?_, ?_⟩⟩
  · rw [hdiv]
  · simp only [chainFinish, ↓reduceIte]

end GraphMinor.Kruskal
