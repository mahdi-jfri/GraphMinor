module

public import GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.PotentialDegreeBounds
import GraphMinor.Thomason.MinorOrder
import GraphMinor.Thomason.NeighborMinor
import GraphMinor.Thomason.DenseNeighborhood
import GraphMinor.Thomason.DensitySubgraphs
import GraphMinor.Minor.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Lean.Elab.Tactic.Omega

/-!
# Neighbourhood reduction with an integer potential

Choose a minor minimal at an order-dependent edge threshold. Its
minimum-degree neighbourhood has bounded order and minimum degree at
least the successive difference of the threshold. Retain the centre
so that every clique in the neighbourhood gains one vertex. This is
the finite counting step underlying Thomason's Lemma 1 (1984), p. 262.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Graph
universe u

/-- The neighbourhood reduction for an explicit monotone integer edge
threshold. The output gives the actual threshold order and all its
numeric constraints, together with the proved clique extension. -/
theorem exists_potential_neighborhood {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : ℕ → ℕ) (hf : Monotone f)
    (m : ℕ) (hmpos : 0 < m) (hm : m ≤ Fintype.card V)
    (hboundary : m.choose 2 < f m) (hden : f (Fintype.card V) ≤ G.edgeFinset.card) :
    ∃ (n : ℕ) (W : Type u) (_ : Fintype W) (J : SimpleGraph W) (_ : DecidableRel J.Adj)
      (_ : Nonempty W),
      m < n ∧ n ≤ Fintype.card V ∧ f n ≤ n.choose 2 ∧
      IsIsoMinor (Graph.ofSimpleGraph J) (Graph.ofSimpleGraph G) ∧
      Fintype.card W ≤ 2 * f n / n ∧
      (∀ v, f n - f (n - 1) ≤ J.degree v) ∧
      ∀ q : ℕ, IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph J) →
        IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 1)))) (Graph.ofSimpleGraph G) := by
  classical
  obtain ⟨X, hX, H, hH, hne, hmX, hminor, hcard, hvertex, hcommon⟩ :=
    exists_potential_minor_with_degree_bounds G f m hmpos hm hboundary hden
  let := hX
  let := hH
  let := hne
  have hNpos : 0 < Fintype.card X := Fintype.card_pos
  have hsum : H.minDegree * Fintype.card X ≤ 2 * f (Fintype.card X) := by
    calc
      H.minDegree * Fintype.card X = ∑ _ : X, H.minDegree := by simp [Nat.mul_comm]
      _ ≤ ∑ v : X, H.degree v := Finset.sum_le_sum (fun v _ => H.minDegree_le_degree v)
      _ = 2 * f (Fintype.card X) := by rw [H.sum_degrees_eq_twice_card_edges, hcard]
  obtain ⟨u, hu⟩ := H.exists_minimal_degree_vertex
  have hdu : 0 < H.degree u := by
    have hv := hvertex u
    have hmono := hf (Nat.sub_le (Fintype.card X) 1)
    omega
  obtain ⟨w, hw⟩ := (H.degree_pos_iff_exists_adj u).mp hdu
  let J := H.induce (H.neighborSet u)
  have hneJ : Nonempty (H.neighborSet u) := ⟨⟨w, hw⟩⟩
  refine ⟨Fintype.card X, H.neighborSet u, inferInstance, J, inferInstance, hneJ,
    hmX, card_le_of_isIsoMinor_ofSimpleGraph hminor, ?_,
    (isIsoMinor_ofSimpleGraph_induce H _).trans hminor, ?_, ?_, ?_⟩
  · rw [← hcard]
    exact H.card_edgeFinset_le_card_choose_two
  · rw [H.card_neighborSet_eq_degree, ← hu]
    exact (Nat.le_div_iff_mul_le hNpos).mpr hsum
  · intro v
    rw [degree_neighborhood_eq_commonNeighbors H u v]
    have hc := hcommon u v.val v.property
    omega
  · intro q hq
    exact (clique_isIsoMinor_of_neighbor_minor H u hq).trans hminor

end GraphMinor.Thomason
