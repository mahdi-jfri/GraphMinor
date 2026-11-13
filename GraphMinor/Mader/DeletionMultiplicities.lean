module

public import GraphMinor.Mader.DeletionVertices
public import GraphMinor.Mader.EndsIso

/-!
# Edge multiplicities for a deletion representation

Count each forest-to-chosen pair of ends. For edges within the chosen set,
use only the ordered pairs whose first index is at most the second. This
counts loops once and avoids counting a non-loop edge in both directions.
Finite edge sets give enumerations of every family of parallel edges.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal GM09

variable {α β : Type*} (G : Graph α β) {X : Set α} {k n : ℕ}
    (a : Fin k ≃ X) {t : Fin n → OrderedTree}
    (ψ : treeForest t ≃g (deleteVertices G X).toSimpleGraph)

/-- Counts of attachment edges at every valid forest vertex. Values at
invalid addresses are zero. -/
noncomputable def deletionAttachmentCounts (i : Fin n) (p : List ℕ) (j : Fin k) : ℕ :=
  if hp : p ∈ (t i).addresses then
    {e | G.IsLink e (ψ ⟨i, ⟨p, hp⟩⟩).val (a j).val}.ncard
  else 0

/-- Counts of edges within the chosen set, using each unordered pair once. -/
noncomputable def deletionCoreCounts (ij : Fin k × Fin k) : ℕ :=
  if ij.1 ≤ ij.2 then {e | G.IsLink e (a ij.1).val (a ij.2).val}.ncard else 0

/-- The attachment count at a valid address counts precisely the edges
with the represented ends. -/
theorem deletionAttachmentCounts_vertex (v : ForestVertex t) (j : Fin k) :
    deletionAttachmentCounts G a ψ v.1 v.2.val j =
      {e | G.IsLink e (ψ v).val (a j).val}.ncard := by
  have hp : v.2.val ∈ (t v.1).addresses := v.2.property
  simp only [deletionAttachmentCounts, dite_eq_left hp]

/-- Every indexed core edge uses an ordered pair of ends. -/
theorem deletionCoreCounts_ordered (e : CoreEdge (deletionCoreCounts G a)) : e.1 ≤ e.2.1 := by
  by_contra h
  have hzero : deletionCoreCounts G a (e.1, e.2.1) = 0 := by
    simp only [deletionCoreCounts, h, ↓reduceIte]
  exact Nat.not_lt_zero e.2.2.val (hzero ▸ e.2.2.isLt)

/-- Enumerate the attachment edges with fixed ends. -/
noncomputable def deletionAttachmentEnumeration (hE : E(G).Finite)
    (v : ForestVertex t) (j : Fin k) :
    Fin (deletionAttachmentCounts G a ψ v.1 v.2.val j) ≃
      {e | G.IsLink e (ψ v).val (a j).val} :=
  (finCongr (deletionAttachmentCounts_vertex G a ψ v j)).trans
    (finiteSetEnumeration _ (hE.subset fun _ he ↦ he.edge_mem))

/-- Enumerate the core edges with a fixed ordered pair of ends. -/
noncomputable def deletionCoreEnumeration (hE : E(G).Finite)
    (i j : Fin k) (hij : i ≤ j) :
    Fin (deletionCoreCounts G a (i, j)) ≃ {e | G.IsLink e (a i).val (a j).val} :=
  (finCongr (by simp only [deletionCoreCounts, hij, ↓reduceIte])).trans
    (finiteSetEnumeration _ (hE.subset fun _ he ↦ he.edge_mem))

end GraphMinor.Mader
