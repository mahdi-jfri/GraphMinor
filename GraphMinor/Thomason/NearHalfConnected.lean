module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Lean.Elab.Tactic.Omega

/-!
# Connectivity at the half-order degree boundary

A non-null graph in which twice every degree is at least the order
minus one is connected. Two non-adjacent vertices have a common
neighbour because their neighbourhoods avoid both endpoints. This
allows the last clique branch to use all remaining vertices.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At the half-order boundary, distinct non-adjacent vertices have a
common neighbour. -/
theorem exists_commonNeighbor_of_near_half
    (hdegree : ∀ v, Fintype.card V ≤ 2 * G.degree v + 1)
    {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v) :
    ∃ w, G.Adj u w ∧ G.Adj v w := by
  have hsub : G.neighborFinset u ∪ G.neighborFinset v ⊆
      ((univ : Finset V).erase u).erase v := by
    intro w hw
    rcases mem_union.mp hw with hw | hw
    · have huw := (G.mem_neighborFinset u w).mp hw
      exact mem_erase.mpr ⟨fun h => hnadj (h ▸ huw), mem_erase.mpr ⟨huw.ne.symm, mem_univ _⟩⟩
    · have hvw := (G.mem_neighborFinset v w).mp hw
      exact mem_erase.mpr ⟨hvw.ne.symm,
        mem_erase.mpr ⟨fun h => hnadj (h ▸ hvw.symm), mem_univ _⟩⟩
  have hc := card_le_card hsub
  have hsum := card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hsum
  have huc := card_erase_of_mem (mem_univ u : u ∈ (univ : Finset V))
  have hvc := card_erase_of_mem (show v ∈ (univ : Finset V).erase u from
    mem_erase.mpr ⟨huv.symm, mem_univ _⟩)
  rw [card_univ] at huc
  have hu := hdegree u
  have hv := hdegree v
  have hpos : 0 < (G.neighborFinset u ∩ G.neighborFinset v).card := by
    have hN : 2 ≤ Fintype.card V := by
      have hh := card_le_univ ({u, v} : Finset V)
      simpa only [card_pair huv] using hh
    omega
  obtain ⟨w, hw⟩ := card_pos.mp hpos
  exact ⟨w, (G.mem_neighborFinset u w).mp (mem_inter.mp hw).1,
    (G.mem_neighborFinset v w).mp (mem_inter.mp hw).2⟩

/-- A non-null graph of degree at least half its order minus one half
is connected. -/
theorem connected_of_near_half [Nonempty V]
    (hdegree : ∀ v, Fintype.card V ≤ 2 * G.degree v + 1) : G.Connected := by
  refine ⟨fun u v => ?_⟩
  by_cases huv : u = v
  · subst v
    exact (SimpleGraph.Walk.nil : G.Walk u u).reachable
  by_cases hadj : G.Adj u v
  · exact (SimpleGraph.Walk.cons hadj .nil).reachable
  obtain ⟨w, huw, hvw⟩ := exists_commonNeighbor_of_near_half G hdegree huv hadj
  exact (SimpleGraph.Walk.cons huw (.cons hvw.symm .nil)).reachable

end GraphMinor.Thomason
