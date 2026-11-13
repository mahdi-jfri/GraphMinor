module

public import GraphMinor.Thomason.ConnectedDominators
import GraphMinor.Thomason.GeometricSelection
import GraphMinor.Thomason.ConnectSmallSets
import Lean.Elab.Tactic.Omega

/-!
# Connecting degree-sensitive dominating selections

Choose a set with the geometric uncovered bound and outside all
exceptional families. Thomason's Lemma 2 (1984), p. 262, connects its
`k` vertices by adding at most `k-1` common neighbours. Enlargement
preserves domination and the required exceptional-family avoidance.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A connected selection with the geometric uncovered bound and at
most `2k-1` vertices, adjacent to every earlier branch whose exceptional
set is one of the sets `B i`. -/
theorem exists_connected_geometricDominatingSet_avoiding
    {I : Type v} [DecidableEq I] (S : Finset I) (B : I → Finset V) (t M D k : ℕ)
    (hk : 0 < k) (hM : M ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hstrict : ∀ v, Fintype.card V < 2 * G.degree v)
    (hB : ∀ i ∈ S, (B i).card ≤ t)
    (hcount : S.card * t.choose k < M.choose k) :
    ∃ X : Finset V, X.card ≤ 2 * k - 1 ∧
      (G.induce (X : Set V)).Connected ∧
      (undominatedVertices G X).card ≤
        Fintype.card V * D ^ k / (Fintype.card V + 1 - M) ^ k ∧
      ∀ i ∈ S, ¬ X ⊆ B i := by
  obtain ⟨Y, hY, havoid⟩ :=
    exists_geometricDominatingSet_avoiding G S B t M D k hM hdegree hB hcount
  obtain ⟨hYcard, hYundom⟩ := (mem_residualBoundedSets_iff G k _ Y).mp hY
  have hYne : Y.Nonempty := card_pos.mp (by omega)
  obtain ⟨Z, hZcard, hconn⟩ := exists_connecting_set G hstrict Y hYne
  refine ⟨Y ∪ Z, ?_, hconn, ?_, ?_⟩
  · have h := card_union_le Y Z
    omega
  · apply le_trans (card_le_card ?_) hYundom
    intro x hx
    obtain ⟨hxuniv, hxdom⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨hxuniv, fun h => hxdom
      (dominatedVertices_mono G (subset_union_left : Y ⊆ Y ∪ Z) h)⟩
  · intro i hi hsub
    exact havoid i hi (subset_union_left.trans hsub)

end GraphMinor.Thomason
