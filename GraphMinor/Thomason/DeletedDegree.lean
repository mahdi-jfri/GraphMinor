module
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Degree bounds after deleting vertices

Thomason's main theorem, page 264 (1984), deletes earlier branch sets.
Deleting `x` vertices lowers each remaining degree by at most `x` and
lowers the vertex count by exactly `x`. Thus the degree surplus above
half the order falls by at most `x`.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Deleting a finite set removes exactly its cardinality from the order. -/
theorem card_compl_finset_add (X : Finset V) :
    Fintype.card ({w : V | w ∉ X}) + X.card = Fintype.card V := by
  change Fintype.card {w : V // ¬ w ∈ X} + X.card = Fintype.card V
  rw [Fintype.card_subtype_compl]
  simpa using Nat.sub_add_cancel (card_le_univ X)

/-- A remaining vertex loses at most the number of deleted vertices
from its degree. -/
theorem degree_le_degree_induce_compl_add (X : Finset V) (v : ({w : V | w ∉ X})) :
    G.degree v ≤ (G.induce {w : V | w ∉ X}).degree v + X.card := by
  have hmap := G.map_neighborFinset_induce (s := {w : V | w ∉ X}) v
  have hcard := congrArg Finset.card hmap
  have hsplit := card_sdiff_add_card_inter (G.neighborFinset v) X
  have hsmall := card_le_card (inter_subset_right : G.neighborFinset v ∩ X ⊆ X)
  have heq : G.neighborFinset v ∩ ({w : V | w ∉ X}).toFinset = G.neighborFinset v \ X := by
    ext w
    simp
  rw [card_map, heq, card_neighborFinset_eq_degree] at hcard
  rw [card_neighborFinset_eq_degree] at hsplit
  omega

/-- The surplus of twice each degree above the order decreases by at
most the size of the deleted set, as used on p. 264. -/
theorem degree_surplus_induce_compl (X : Finset V) (d : ℕ)
    (hX : X.card ≤ d) (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v) :
    ∀ v, Fintype.card ({w : V | w ∉ X}) + (d - X.card) ≤
      2 * (G.induce {w : V | w ∉ X}).degree v := by
  intro v
  have hc := card_compl_finset_add (V := V) X
  have hd := degree_le_degree_induce_compl_add G X v
  have hh := hdeg v
  omega

/-- Deleting vertices cannot increase the number of non-neighbours of a
remaining vertex. This keeps the degree-sensitive domination ratio
available at every stage of the branch construction. -/
theorem nonneighbor_bound_induce_compl (X : Finset V) (D : ℕ)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1) :
    ∀ v, Fintype.card {w : V | w ∉ X} ≤
      (G.induce {w : V | w ∉ X}).degree v + D + 1 := by
  intro v
  have hc := card_compl_finset_add (V := V) X
  have hd := degree_le_degree_induce_compl_add G X v
  have hh := hdegree v
  omega

end GraphMinor.Thomason
