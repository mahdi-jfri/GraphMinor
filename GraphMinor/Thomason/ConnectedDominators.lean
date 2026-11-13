module

public import GraphMinor.Thomason.DominatingSets
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Data.Nat.Log
import GraphMinor.Thomason.ConnectSmallSets
import GraphMinor.Thomason.LogDominators
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-!
# Connecting a set with logarithmically many added vertices

First dominate the chosen set with a logarithmically small set. Join the
dominating vertices by common neighbours. Adding the dominated vertices
preserves connectivity. This proves the nonempty-set case of Thomason's
Lemma 4 (1984), page 263, with its stated augmentation bound.
-/

public section

namespace GraphMinor.Thomason

open SimpleGraph Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Enlarging a set enlarges the set of vertices it dominates. -/
theorem dominatedVertices_mono {A B : Finset V} (h : A ⊆ B) :
    dominatedVertices G A ⊆ dominatedVertices G B := by
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · exact mem_union_left _ (h hx)
  · obtain ⟨v, hv, hxv⟩ := mem_biUnion.mp hx
    exact mem_union_right _ (mem_biUnion.mpr ⟨v, h hv, hxv⟩)

/-- Adding vertices dominated by a connected induced graph preserves
connectivity of the induced graph on the union. -/
theorem connected_induce_union_of_dominated (U W : Finset V)
    (hconn : (G.induce (U : Set V)).Connected) (hdom : W ⊆ dominatedVertices G U) :
    (G.induce ((U ∪ W : Finset V) : Set V)).Connected := by
  revert hdom
  induction W using Finset.induction_on with
  | empty =>
    intro _
    have heq : ((U ∪ ∅ : Finset V) : Set V) = (U : Set V) := by
      ext x
      simp
    rw [heq]
    exact hconn
  | @insert w S hw ih =>
    intro hdom
    have hdomS : S ⊆ dominatedVertices G U := fun x hx => hdom (mem_insert_of_mem hx)
    have hconnS := ih hdomS
    have hd : w ∈ U ∨ ∃ y ∈ U, G.Adj y w := by
      have h := hdom (mem_insert_self w S)
      simpa only [dominatedVertices, mem_union, mem_biUnion, G.mem_neighborFinset] using h
    rcases hd with hwu | ⟨y, hy, hyw⟩
    · have heq : U ∪ insert w S = U ∪ S := by
        ext x
        simp only [mem_union, mem_insert]
        constructor
        · rintro (h | rfl | h)
          · exact Or.inl h
          · exact Or.inl hwu
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      rw [heq]
      exact hconnS
    · have hsg : (G.induce ({w} : Set V)).Connected :=
        (SimpleGraph.Subgraph.singletonSubgraph_connected (G := G) (v := w)).induce_verts
      have hc := G.connected_induce_union hconnS.preconnected hsg.preconnected
        (show y ∈ ((U ∪ S : Finset V) : Set V) from mem_union_left _ hy)
        (show w ∈ ({w} : Set V) from rfl) hyw
      have heq : ((U ∪ insert w S : Finset V) : Set V) =
          ((U ∪ S : Finset V) : Set V) ∪ {w} := by
        ext x
        simp only [mem_coe, mem_union, mem_insert, Set.mem_union, Set.mem_singleton_iff]
        tauto
      rw [heq]
      exact hc

/-- Thomason's Lemma 4, p. 263, for a nonempty set: at most
`2 floor(log₂ |X|)+1` vertices can be added to make it connected under
the paper's degree hypothesis. -/
theorem exists_logarithmic_connecting_set (X : Finset V) (hne : X.Nonempty)
    (hdeg : ∀ v : V, Fintype.card V + Nat.log 2 X.card ≤ 2 * G.degree v) :
    ∃ U : Finset V, U.card ≤ 2 * Nat.log 2 X.card + 1 ∧
      (G.induce ((X ∪ U : Finset V) : Set V)).Connected := by
  classical
  by_cases hXone : X.card = 1
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hXone
    subst X
    refine ⟨∅, by simp, ?_⟩
    have hsg : (G.induce ({x} : Set V)).Connected :=
      (SimpleGraph.Subgraph.singletonSubgraph_connected (G := G) (v := x)).induce_verts
    have heq : (({x} ∪ ∅ : Finset V) : Set V) = {x} := by
      ext y
      simp
    rw [heq]
    exact hsg
  have hXtwo : 2 ≤ X.card := by
    have hpos := Finset.card_pos.mpr hne
    omega
  have hlog : 0 < Nat.log 2 X.card := Nat.log_pos (by omega) hXtwo
  obtain ⟨x, hx⟩ := hne
  have hsize : 3 ≤ Fintype.card V := by
    have hd := hdeg x
    have hlt := G.degree_lt_card_verts x
    omega
  have hweak (v : V) : Fintype.card V ≤ 2 * G.degree v := by
    have h := hdeg v
    omega
  obtain ⟨Y, hY, hdom⟩ := exists_small_dominating_set G hsize hweak X
  have hYne : Y.Nonempty := by
    by_contra hn
    have hY0 : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hm := hdom hx
    rw [hY0, dominatedVertices_empty] at hm
    exact Finset.notMem_empty x hm
  have hstrict (v : V) : Fintype.card V < 2 * G.degree v := by
    have h := hdeg v
    omega
  obtain ⟨Z, hZ, hconn⟩ := exists_connecting_set G hstrict Y hYne
  let U := Y ∪ Z
  refine ⟨U, ?_, ?_⟩
  · have hcard := Finset.card_union_le Y Z
    have hpos := Finset.card_pos.mpr hYne
    dsimp only [U]
    omega
  · have hdomU : X ⊆ dominatedVertices G U :=
      fun v hv => dominatedVertices_mono G (Finset.subset_union_left) (hdom hv)
    have hc := connected_induce_union_of_dominated G U X hconn hdomU
    have heq : ((X ∪ U : Finset V) : Set V) = ((U ∪ X : Finset V) : Set V) := by
      ext v
      simp only [Finset.mem_coe, Finset.mem_union]
      exact or_comm
    rw [heq]
    exact hc

end GraphMinor.Thomason
