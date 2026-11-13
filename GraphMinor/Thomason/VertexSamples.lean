module

public import GraphMinor.Thomason.SubsetMissingCount
public import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Counting vertex sequences and their uncovered vertices

Choose vertices with replacement, as in the finite sample form of
Wood (2026), arXiv:2610.41060v1, Lemma 7, pp. 5–6. The selected vertices
are the image of the sequence. A second count of sequence–vertex pairs
bounds the sum of all uncovered counts, including sequences with repeats.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The distinct vertices appearing in a sequence of vertex choices. -/
def sampleVertices {k : ℕ} (f : Fin k → V) : Finset V := univ.image f

omit [Fintype V] in
/-- A sample has no more distinct vertices than its length. -/
theorem card_sampleVertices_le {k : ℕ} (f : Fin k → V) : (sampleVertices f).card ≤ k := by
  exact (card_image_le).trans_eq (by simp)

omit [Fintype V] in
/-- A sample of positive length contains a vertex. -/
theorem sampleVertices_nonempty {k : ℕ} (f : Fin k → V) (hk : 0 < k) :
    (sampleVertices f).Nonempty := ⟨f ⟨0, hk⟩, mem_image.mpr ⟨⟨0, hk⟩, mem_univ _, rfl⟩⟩

/-- Samples whose values all lie in a given finite set are counted by
an integer power of its size. -/
theorem card_vertex_sequences_in_finset (A : Finset V) (k : ℕ) :
    ((univ : Finset (Fin k → V)).filter (fun f => ∀ i, f i ∈ A)).card = A.card ^ k := by
  have heq : (univ : Finset (Fin k → V)).filter (fun f => ∀ i, f i ∈ A) =
      Fintype.piFinset (fun _ : Fin k => A) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  rw [heq, Fintype.card_piFinset]
  simp

/-- Requiring the sample's image to lie in a set gives the same count. -/
theorem card_samples_with_vertices_subset (A : Finset V) (k : ℕ) :
    ((univ : Finset (Fin k → V)).filter (fun f => sampleVertices f ⊆ A)).card = A.card ^ k := by
  simpa only [sampleVertices, image_subset_iff, mem_univ, forall_const] using
    card_vertex_sequences_in_finset A k

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Missing all selected vertices is the same as every coordinate
lying in the missed vertex's non-neighbour set. -/
theorem mem_undominatedVertices_sampleVertices_iff {k : ℕ} (f : Fin k → V) (v : V) :
    v ∈ undominatedVertices G (sampleVertices f) ↔ ∀ i, f i ∈ undominatedVertices G {v} := by
  rw [mem_undominatedVertices_iff_subset_singleton]
  simp only [sampleVertices, image_subset_iff, mem_univ, forall_const]

/-- Counting samples and missed vertices in the two orders gives an
exact sum of powers of the non-neighbour counts. -/
theorem sum_card_undominatedVertices_samples (k : ℕ) :
    (∑ f : Fin k → V, (undominatedVertices G (sampleVertices f)).card) =
      ∑ v : V, (undominatedVertices G {v}).card ^ k := by
  let R : (Fin k → V) → V → Prop := fun f v => v ∈ undominatedVertices G (sampleVertices f)
  have hrow (f : Fin k → V) : (univ : Finset V).bipartiteAbove R f =
      undominatedVertices G (sampleVertices f) := by
    ext v
    simp only [mem_bipartiteAbove, mem_univ, true_and, R]
  have hcol (v : V) : (univ : Finset (Fin k → V)).bipartiteBelow R v =
      univ.filter (fun f => ∀ i, f i ∈ undominatedVertices G {v}) := by
    ext f
    simp only [mem_bipartiteBelow, mem_filter, mem_univ, true_and, R,
      mem_undominatedVertices_sampleVertices_iff]
  have hc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    (s := univ) (t := univ)
  simpa only [hrow, hcol, card_vertex_sequences_in_finset] using hc

/-- A bound on every non-neighbour count controls the total uncovered
count over all sequences, including repeated choices. -/
theorem sum_card_undominatedVertices_samples_le (k D : ℕ)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1) :
    (∑ f : Fin k → V, (undominatedVertices G (sampleVertices f)).card) ≤
      Fintype.card V * D ^ k := by
  rw [sum_card_undominatedVertices_samples]
  calc
    (∑ v : V, (undominatedVertices G {v}).card ^ k) ≤ ∑ _v : V, D ^ k := by
      apply sum_le_sum
      intro v _
      have hh := hdegree v
      have hc := card_undominatedVertices_singleton G v
      exact Nat.pow_le_pow_left (by omega : (undominatedVertices G {v}).card ≤ D) k
    _ = Fintype.card V * D ^ k := by simp

end GraphMinor.Thomason
