module

public import GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
import GraphMinor.Thomason.PotentialMinor
import GraphMinor.Thomason.ContractionMinor
import GraphMinor.Thomason.DensitySubgraphs
import GraphMinor.Minor.Basic

/-!
# Deletion and contraction bounds for a varying edge threshold

The minimum permitted order is excluded by the complete-graph edge bound.
Thus vertex deletion and edge contraction remain above the order cutoff.
Minimality then bounds the degrees and common-neighbour counts by the
change in the threshold. These are the combinatorial inequalities in
Thomason's Lemma 1 (1984), page 262.
-/

public section

namespace GraphMinor.Thomason

open SimpleGraph Graph

universe u

/-- Choose a minor at the threshold in which deleting a vertex or
contracting an edge falls below the threshold. The resulting degree and
common-neighbour inequalities are derived from the proved edge counts. -/
theorem exists_potential_minor_with_degree_bounds {V : Type u}
    [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : ℕ → ℕ) (m : ℕ) (hmpos : 0 < m)
    (hm : m ≤ Fintype.card V) (hboundary : m.choose 2 < f m)
    (hd : f (Fintype.card V) ≤ G.edgeFinset.card) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
      (_ : Nonempty W),
      m < Fintype.card W ∧
      IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) ∧
      H.edgeFinset.card = f (Fintype.card W) ∧
      (∀ u : W, f (Fintype.card W) < f (Fintype.card W - 1) + H.degree u) ∧
      (∀ u v : W, H.Adj u v →
        f (Fintype.card W) ≤ f (Fintype.card W - 1) + (H.commonNeighbors u v).ncard) := by
  classical
  obtain ⟨W, hW, H, hH, hne, hmW, hminor, hcard, hmin⟩ :=
    exists_minimal_potential_minor G f m hm hd
  let := hW
  let := hH
  let := hne
  have hmW' : m < Fintype.card W := by
    by_contra hsmall
    have hEq : Fintype.card W = m := by omega
    have hbound := H.card_edgeFinset_le_card_choose_two
    rw [hcard, hEq] at hbound
    omega
  refine ⟨W, hW, H, hH, hne, hmW', hminor, hcard, ?_, ?_⟩
  · intro u
    by_contra hsmall
    have hverts := edgeContraction_card_vertices u
    have hcardDel : Fintype.card ({u}ᶜ : Set W) = Fintype.card W - 1 := by omega
    have hmDel : m ≤ Fintype.card ({u}ᶜ : Set W) := by omega
    have hneDel : Nonempty ({u}ᶜ : Set W) := Fintype.card_pos_iff.mp (by omega)
    let K := H.induce ({u}ᶜ : Set W)
    have hcount : K.edgeFinset.card = H.edgeFinset.card - H.degree u := by
      exact (H.card_edgeFinset_induce_compl_singleton u).trans
        (H.card_edgeFinset_deleteIncidenceSet u)
    have hdenK : f (Fintype.card ({u}ᶜ : Set W)) ≤ K.edgeFinset.card := by
      rw [hcardDel, hcount, hcard]
      omega
    have hle := hmin ({u}ᶜ : Set W) inferInstance K inferInstance hneDel hmDel
      (isIsoMinor_ofSimpleGraph_induce H _) hdenK
    omega
  · intro u v huv
    have hcn : (H.commonNeighbors u v).ncard =
        (H.neighborFinset v ∩ H.neighborFinset u).card := by
      simp only [Set.ncard_eq_toFinset_card', SimpleGraph.commonNeighbors_eq,
        Set.toFinset_inter, ← SimpleGraph.neighborFinset_def, Finset.inter_comm]
    rw [hcn]
    by_contra hsmall
    have hverts := edgeContraction_card_vertices v
    have hcardCon : Fintype.card ({v}ᶜ : Set W) = Fintype.card W - 1 := by omega
    have hmCon : m ≤ Fintype.card ({v}ᶜ : Set W) := by omega
    have hneCon : Nonempty ({v}ᶜ : Set W) := ⟨⟨u, huv.ne⟩⟩
    let K := edgeContraction H u v
    have hcount := edgeContraction_card_edges H huv
    have hdenK : f (Fintype.card ({v}ᶜ : Set W)) ≤ K.edgeFinset.card := by
      rw [hcardCon]
      dsimp only [K]
      rw [hcard] at hcount
      omega
    have hle := hmin ({v}ᶜ : Set W) inferInstance K inferInstance hneCon hmCon
      (edgeContraction_isIsoMinor H huv) hdenK
    omega

end GraphMinor.Thomason
