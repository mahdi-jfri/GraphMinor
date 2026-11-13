module

public import GraphMinor.Thomason.HubSelectionCost
import GraphMinor.Thomason.GeometricSelection
import Lean.Elab.Tactic.Omega

/-!
# Geometric selections with the central-vertex connection cost

Select a set outside all earlier exceptional families using the
geometric subset count, then extend it by the proved central-vertex
construction. Enlarging the set preserves domination and avoidance.
The near-half degree boundary suffices for the connection step.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A geometric dominating selection extends to a connected set with
the central-vertex order bound, avoiding every exceptional family. -/
theorem exists_connected_hubGeometricSet_avoiding
    {I : Type v} [DecidableEq I] (S : Finset I) (B : I → Finset V) (t M D k : ℕ)
    (hk : 0 < k) (hM : M ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hnear : ∀ v, Fintype.card V ≤ 2 * G.degree v + 1)
    (hB : ∀ i ∈ S, (B i).card ≤ t)
    (hcount : S.card * t.choose k < M.choose k) :
    ∃ X : Finset V, X.card ≤ hubSelectionCost (Fintype.card V) D k ∧
      (G.induce (X : Set V)).Connected ∧
      (undominatedVertices G X).card ≤
        Fintype.card V * D ^ k / (Fintype.card V + 1 - M) ^ k ∧
      ∀ i ∈ S, ¬ X ⊆ B i := by
  obtain ⟨Y, hY, havoid⟩ :=
    exists_geometricDominatingSet_avoiding G S B t M D k hM hdegree hB hcount
  obtain ⟨hYcard, hYundom⟩ := (mem_residualBoundedSets_iff G k _ Y).mp hY
  have hYne : Y.Nonempty := card_pos.mp (by omega)
  obtain ⟨X, hYX, hXcard, hconn⟩ := exists_connected_superset_hub G Y hYne D hdegree hnear
  refine ⟨X, ?_, hconn, ?_, ?_⟩
  · simpa only [hYcard] using hXcard
  · apply le_trans (card_le_card ?_) hYundom
    intro x hx
    obtain ⟨hxuniv, hxdom⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨hxuniv, fun h => hxdom (dominatedVertices_mono G hYX h)⟩
  · intro i hi hsub
    exact havoid i hi (hYX.trans hsub)

end GraphMinor.Thomason
