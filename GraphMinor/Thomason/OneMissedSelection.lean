module

public import GraphMinor.Thomason.RootedSamples
import GraphMinor.Thomason.RootedSampleCount
import GraphMinor.Thomason.FiniteAverage
import GraphMinor.Thomason.NonemptyDominationBound
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Selecting connected branches with one missed adjacency to the root

Pad each root's actual non-neighbour set to the common bound `D`.
Count rooted samples with at most one exceptional tail coordinate, then
remove the earlier exceptional events and apply finite averaging. The
selected sample extends to a connected branch through one common
neighbour, preserving its domination and adjacency properties.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v

/-- The number of candidates with a root and a tail of length `m`. -/
def rootedOneMissedCount (N D m : ℕ) : ℕ :=
  N * ((N - D) ^ m + m * D * (N - D) ^ (m - 1))

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The exact sample count and the total uncovered bound yield a connected
set of order at most `m+2`, outside every earlier exceptional family. -/
theorem exists_connected_oneMissedSet_avoiding
    {I : Type v} [DecidableEq I] (indices : Finset I) (B : I → Finset V) (t : I → ℕ)
    (m D T : ℕ) (hD : D ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hnear : ∀ v, Fintype.card V ≤ 2 * G.degree v + 1)
    (hB : ∀ i ∈ indices, (B i).card ≤ t i)
    (hcount : Fintype.card V * D ^ (m + 1) <
      (rootedOneMissedCount (Fintype.card V) D m - ∑ i ∈ indices, (t i) ^ (m + 1)) * (T + 1) ∨
      (D ≤ T ∧ (∑ i ∈ indices, (t i) ^ (m + 1)) < rootedOneMissedCount (Fintype.card V) D m)) :
    ∃ X : Finset V, X.card ≤ m + 2 ∧ (G.induce (X : Set V)).Connected ∧
      (undominatedVertices G X).card ≤ T ∧ ∀ i ∈ indices, ¬ X ⊆ B i := by
  classical
  have hpad (a : V) : ∃ A : Finset V, undominatedVertices G {a} ⊆ A ∧ A.card = D := by
    have hc : (undominatedVertices G {a}).card ≤ D := by
      rw [card_undominatedVertices_singleton]
      have hh := hdegree a
      omega
    exact exists_superset_card_eq hc hD
  let A : V → Finset V := fun a => (hpad a).choose
  have hA (a : V) : undominatedVertices G {a} ⊆ A a := (hpad a).choose_spec.1
  have hAC (a : V) : (A a).card = D := (hpad a).choose_spec.2
  let S := rootedOneBadSamples A m
  have hM : rootedOneMissedCount (Fintype.card V) D m ≤ S.card := by
    rw [show S.card = rootedOneMissedCount (Fintype.card V) D m from
      card_rootedOneBadSamples A m D hAC]
  have htotal : (∑ f ∈ S, (undominatedVertices G (sampleVertices f)).card) ≤
      Fintype.card V * D ^ (m + 1) :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => Nat.zero_le _)).trans
      (sum_card_undominatedVertices_samples_le G (m + 1) D hdegree)
  have hbound (f : Fin (m + 1) → V) (_ : f ∈ S) :
      (undominatedVertices G (sampleVertices f)).card ≤ D :=
    card_undominatedVertices_le_of_nonempty G _ (sampleVertices_nonempty f (Nat.succ_pos _)) D hdegree
  have hbad (i : I) (hi : i ∈ indices) :
      (S.filter (fun f => sampleVertices f ⊆ B i)).card ≤ (t i) ^ (m + 1) := by
    have hsub : S.filter (fun f => sampleVertices f ⊆ B i) ⊆
        (univ : Finset (Fin (m + 1) → V)).filter (fun f => sampleVertices f ⊆ B i) := by
      intro f hf
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hf).2⟩
    exact (card_le_card hsub).trans
      ((card_samples_with_vertices_subset (B i) (m + 1)).trans_le
        (Nat.pow_le_pow_left (hB i hi) (m + 1)))
  obtain ⟨f, hf, hfundom, hfavoid⟩ := exists_mem_avoiding_of_weight_sum S indices
    (fun i f => sampleVertices f ⊆ B i) (fun f => (undominatedVertices G (sampleVertices f)).card)
    (fun i => (t i) ^ (m + 1)) (rootedOneMissedCount (Fintype.card V) D m)
    (Fintype.card V * D ^ (m + 1)) D T hM htotal hbound hbad hcount
  have htail : Fin.tail f ∈ oneBadSamples (A (f 0)) m := (mem_filter.mp hf).2
  obtain ⟨X, hYX, hcard, hconn⟩ := exists_connected_oneMissed_sample G (f 0) (Fin.tail f)
    (A (f 0)) (hA (f 0)) htail hnear
  rw [Fin.cons_self_tail] at hYX
  refine ⟨X, hcard, hconn, ?_, ?_⟩
  · apply le_trans (card_le_card ?_) hfundom
    intro x hx
    obtain ⟨hxu, hxnot⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨hxu, fun h => hxnot (dominatedVertices_mono G hYX h)⟩
  · intro i hi hsub
    exact hfavoid i hi (hYX.trans hsub)

end GraphMinor.Thomason
