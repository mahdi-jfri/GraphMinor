module

public import GraphMinor.Thomason.ConnectedDominators
import GraphMinor.Thomason.AvoidingSets
import Lean.Elab.Tactic.Omega

/-!
# Selecting one connected branch set

Thomason's main theorem, page 264 (1984), first chooses an
almost-dominating set outside all exceptional families and then joins
it using Lemma 4. Enlarging it preserves domination and avoidance.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The connected-set selection step in Thomason's main theorem, p. 264.
Its hypotheses are the degree and counting inequalities used there. -/
theorem exists_connected_almostDominatingSet_avoiding
    {I : Type v} [DecidableEq I] (S : Finset I) (B : I → Finset V) (t m k : ℕ)
    (hk : 0 < k) (hlog : Nat.log 2 k ≤ m)
    (hm : m + 3 ≤ Fintype.card V)
    (hdeg : ∀ v, Fintype.card V + m ≤ 2 * G.degree v)
    (hB : ∀ i ∈ S, (B i).card ≤ t)
    (hcount : S.card * t.choose k < (m + 3).choose k) :
    ∃ X : Finset V, X.card ≤ k + 2 * Nat.log 2 k + 1 ∧
      (G.induce (X : Set V)).Connected ∧
      (undominatedVertices G X).card ≤ Fintype.card V / 2 ^ k ∧
      ∀ i ∈ S, ¬ X ⊆ B i := by
  obtain ⟨Y, hY, havoid⟩ :=
    exists_almostDominatingSet_avoiding G S B t m k hm hdeg hB hcount
  obtain ⟨hYcard, hYundom⟩ := (mem_almostDominatingSets_iff G k Y).mp hY
  have hYne : Y.Nonempty := card_pos.mp (by omega)
  have hdegree : ∀ v, Fintype.card V + Nat.log 2 Y.card ≤ 2 * G.degree v := by
    intro v
    rw [hYcard]
    exact (Nat.add_le_add_left hlog _).trans (hdeg v)
  obtain ⟨Z, hZcard, hconn⟩ := exists_logarithmic_connecting_set G Y hYne hdegree
  refine ⟨Y ∪ Z, ?_, hconn, ?_, ?_⟩
  · have h := card_union_le Y Z
    rw [hYcard] at hZcard
    omega
  · apply le_trans (card_le_card ?_) hYundom
    intro x hx
    obtain ⟨hxuniv, hxdom⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨hxuniv, fun h => hxdom
      (dominatedVertices_mono G (subset_union_left : Y ⊆ Y ∪ Z) h)⟩
  · intro i hi hsub
    exact havoid i hi (subset_union_left.trans hsub)

end GraphMinor.Thomason
