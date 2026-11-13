module

public import GraphMinor.GM04.TopologicalContainment
public import GraphMinor.Kruskal.LabelledTrees
import Mathlib.Order.WellQuasiOrder

/-!
# Labels for a forest attached to a fixed vertex set

At each forest vertex we record the number of edges to each chosen vertex.
For a fixed number of chosen vertices, these vectors are well-quasi-ordered
by coordinatewise comparison. Labelled Kruskal and Higman then compare
finite forests with such labels. The edge multiplicities within the chosen
vertex set can be compared at the same time, by another finite product of
natural numbers. This file proves only the comparison of this data.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal

/-- Counts of edges from `v` to the vertices indexed by `a`. Counting edges,
rather than recording adjacency, retains parallel-edge multiplicities. -/
noncomputable def attachmentLabel {α β : Type*} {k : ℕ}
    (G : Graph α β) (a : Fin k → α) (v : α) : Fin k → ℕ :=
  fun i ↦ {e | G.IsLink e v (a i)}.ncard

/-- Each set counted by an attachment label is finite in a finite-edge graph. -/
theorem finite_attachment_edges {α β : Type*} {k : ℕ}
    {G : Graph α β} (hE : E(G).Finite) (a : Fin k → α) (v : α) (i : Fin k) :
    {e | G.IsLink e v (a i)}.Finite :=
  hE.subset (fun _ he ↦ he.edge_mem)

/-- Reversing the ends of an edge does not change its multiplicity. In
particular, the multiplicity matrix on the chosen vertices is symmetric. -/
theorem attachmentLabel_symm {α β : Type*} {k : ℕ}
    (G : Graph α β) (a : Fin k → α) (i j : Fin k) :
    attachmentLabel G a (a i) j = attachmentLabel G a (a j) i := by
  unfold attachmentLabel
  congr 1
  ext e
  exact ⟨Graph.IsLink.symm, Graph.IsLink.symm⟩

/-- The label detects the absence of an attachment, even when parallel
edges are allowed. Finiteness is needed because `ncard` vanishes on infinite sets. -/
theorem attachmentLabel_eq_zero_iff {α β : Type*} {k : ℕ}
    {G : Graph α β} (hE : E(G).Finite) (a : Fin k → α) (v : α) (i : Fin k) :
    attachmentLabel G a v i = 0 ↔ ¬ ∃ e, G.IsLink e v (a i) := by
  rw [attachmentLabel, Set.ncard_eq_zero (finite_attachment_edges hE a v i)]
  exact Set.eq_empty_iff_forall_notMem.trans (by simp only [Set.mem_ofPred_eq, not_exists])

/-- A labelled forest and the multiplicities within the chosen vertex set
are jointly well-quasi-ordered. The first coordinate counts edges for pairs
of chosen vertices, including loops on its diagonal. The second coordinate
is the list of forest components, labelled by attachment multiplicities.
This does not assert that an arbitrary graph has such a representation. -/
theorem wellQuasiOrdered_attachment_data (k : ℕ) :
    WellQuasiOrdered (fun p q :
        (Fin k × Fin k → ℕ) × List (LabelledTree (Fin k → ℕ)) ↦
      p.1 ≤ q.1 ∧ List.SublistForall₂ (LabelledTree.Embeds (· ≤ ·)) p.2 q.2) := by
  have hlabel : WellQuasiOrdered (fun a b : Fin k → ℕ ↦ a ≤ b) :=
    wellQuasiOrdered_le
  have hforest := LabelledTree.wellQuasiOrdered_forestEmbeds hlabel
  exact (wellQuasiOrdered_le (α := Fin k × Fin k → ℕ)).prod hforest

end GraphMinor.Mader
