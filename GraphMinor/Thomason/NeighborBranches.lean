module

public import GraphMinor.Thomason.CliqueMinorOfBranches
import GraphMinor.Thomason.InducedSets
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Adding the centre of a neighbourhood as a clique branch

Thomason's Lemma 1 (1984), p. 262, twice constructs a clique minor
inside a neighbourhood. Its centre is a new singleton branch, adjacent
to every old branch. This file proves that step with explicit vertex sets.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The neighbourhood extension used twice in Thomason's Lemma 1,
p. 262. Adding its centre to connected clique branches gives one
additional clique vertex. -/
theorem clique_isIsoMinor_of_neighbor_branches (u : V) {q : ℕ}
    (T : Fin q → Finset (G.neighborSet u))
    (hconn : ∀ i, ((G.induce (G.neighborSet u)).induce (T i : Set (G.neighborSet u))).Connected)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hadj : ∀ i j, i ≠ j → ∃ v ∈ T i, ∃ w ∈ T j,
      (G.induce (G.neighborSet u)).Adj v w) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 1)))) (Graph.ofSimpleGraph G) := by
  let S : Fin q → Finset V := fun i => (T i).map (.subtype (· ∈ G.neighborSet u))
  have hSconn (i : Fin q) : (G.induce (S i : Set V)).Connected :=
    connected_induce_map_subtype G (G.neighborSet u) (T i) (hconn i)
  have hSdis : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i j hij
    exact (Finset.disjoint_map _).mpr (hdis hij)
  have hSunot (i : Fin q) : u ∉ S i := by
    intro hu
    obtain ⟨v, _, hv⟩ := mem_map.mp hu
    exact (G.ne_of_adj v.property) hv.symm
  have hSne (i : Fin q) : (S i).Nonempty := by
    obtain ⟨v⟩ := (hSconn i).nonempty
    exact ⟨v.val, v.property⟩
  let U : Fin (q + 1) → Finset V := Fin.cons {u} S
  apply clique_isIsoMinor_of_branches G U
  · intro i
    refine Fin.cases ?_ (fun j => hSconn j) i
    have heq : ((U 0 : Finset V) : Set V) = {u} := by ext x; simp [U]
    rw [heq]
    exact (SimpleGraph.Subgraph.singletonSubgraph_connected (G := G) (v := u)).induce_verts
  · intro i j hij
    revert hij
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro h; exact (h rfl).elim
      · intro _; exact Finset.disjoint_singleton_left.mpr (hSunot b)
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro _; exact Finset.disjoint_singleton_right.mpr (hSunot a)
      · intro h; exact hSdis (fun hab => h (congrArg Fin.succ hab))
  · intro i j hij
    revert hij
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro h; exact (h rfl).elim
      · intro _
        obtain ⟨v, hv⟩ := hSne b
        obtain ⟨w, hw, rfl⟩ := mem_map.mp hv
        exact ⟨u, mem_singleton_self _, w.val, mem_map.mpr ⟨w, hw, rfl⟩, w.property⟩
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro _
        obtain ⟨v, hv⟩ := hSne a
        obtain ⟨w, hw, rfl⟩ := mem_map.mp hv
        exact ⟨w.val, mem_map.mpr ⟨w, hw, rfl⟩, u, mem_singleton_self _, w.property.symm⟩
      · intro h
        obtain ⟨v, hv, w, hw, hvw⟩ := hadj a b (fun hab => h (congrArg Fin.succ hab))
        exact ⟨v.val, mem_map.mpr ⟨v, hv, rfl⟩, w.val, mem_map.mpr ⟨w, hw, rfl⟩, hvw⟩

end GraphMinor.Thomason
