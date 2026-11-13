module

public import GraphMinor.Compute.GM02SeparatorCodes
public import GraphMinor.GM02.ComponentTest
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Completeness of the separator-code search

A balanced separation passes the component test at its common vertex
set. Every permitted common vertex set has a separator code. Conversely,
a successful code represents a small vertex set, and grouping its
components gives a balanced separation. Thus exhaustive rejection of
codes is the negative output required in II (3.1), page 316.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 Classical

/-- Successful codes exist exactly when the balanced separation required
by II (3.1) exists. The inequalities use integer multiples to avoid division. -/
theorem gm02BalancedSeparation_iff_code {n : ℕ} (G : SimpleGraph (Fin n))
    (Q : Finset (Fin n)) (k : ℕ) :
    (∃ H H' : Graph (Fin n) (Sym2 (Fin n)),
      IsSeparation (Graph.ofSimpleGraph G) H H' ∧ (V(H) ∩ V(H')).ncard ≤ k ∧
      3 * ((V(H) \ V(H')) ∩ (Q : Set (Fin n))).ncard ≤
        2 * ((Q : Set (Fin n)) \ (V(H) ∩ V(H'))).ncard ∧
      3 * ((V(H') \ V(H)) ∩ (Q : Set (Fin n))).ncard ≤
        2 * ((Q : Set (Fin n)) \ (V(H) ∩ V(H'))).ncard) ↔
    ∃ code < (n + 1) ^ k, ∀ a : Fin n,
      a ∉ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit n code i.val) →
      3 * (deletedComponent (Graph.ofSimpleGraph G)
        (gm02SlotVertices (n := n) (fun i : Fin k => gm02SeparatorDigit n code i.val) : Set (Fin n)) a ∩
          (Q : Set (Fin n))).ncard ≤
        2 * (Q \ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit n code i.val)).card := by
  rw [balanced_separation_iff_component_test (Graph.ofSimpleGraph G)
    Set.finite_univ (Q : Set (Fin n)) (Set.subset_univ _) k]
  constructor
  · rintro ⟨X, _, hsize, hcomp⟩
    let F := (Set.toFinite X).toFinset
    have hF : (F : Set (Fin n)) = X := Set.Finite.coe_toFinset _
    have hsizeF : F.card ≤ k := by simpa only [← Set.ncard_coe_finset, hF] using hsize
    obtain ⟨code, hc, hcode⟩ := exists_gm02SeparatorCode F hsizeF
    refine ⟨code, hc, ?_⟩
    intro a ha
    have haX : a ∉ X := by simpa only [← hF, ← hcode, Finset.mem_coe] using ha
    have hb := hcomp a ⟨Set.mem_univ _, haX⟩
    have hQF : ((Q : Set (Fin n)) \ X) = (↑(Q \ F) : Set (Fin n)) := by simp only [Finset.coe_sdiff, hF]
    simpa only [hcode, hF, hQF, Set.ncard_coe_finset] using hb
  · rintro ⟨code, hc, hcomp⟩
    let X := gm02SlotVertices (n := n) (fun i : Fin k => gm02SeparatorDigit n code i.val)
    refine ⟨(X : Set (Fin n)), Set.subset_univ _, ?_, ?_⟩
    · simpa only [Set.ncard_coe_finset] using gm02SlotVertices_card_le (n := n)
        (fun i : Fin k => gm02SeparatorDigit n code i.val)
    · intro a ha
      have hb := hcomp a ha.2
      simpa only [← Finset.coe_sdiff, Set.ncard_coe_finset] using hb

end GraphMinor.Compute
