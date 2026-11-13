module

public import GraphMinor.Thomason.ConnectedDominators
import Lean.Elab.Tactic.Omega

/-!
# The uncovered bound of a nonempty selection

Every nonempty selected set dominates at least the vertices dominated
by any one of its members. Thus its uncovered set is no larger than
the maximum number of non-neighbours of a single vertex. This can
improve the geometric estimate for small selections.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A nonempty selected set leaves at most the single-vertex
non-neighbour bound uncovered. -/
theorem card_undominatedVertices_le_of_nonempty (Y : Finset V) (hne : Y.Nonempty)
    (D : ℕ) (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1) :
    (undominatedVertices G Y).card ≤ D := by
  obtain ⟨v, hv⟩ := hne
  have hsub : undominatedVertices G Y ⊆ undominatedVertices G {v} := by
    intro x hx
    obtain ⟨hxuniv, hxdom⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨hxuniv, fun h => hxdom
      (dominatedVertices_mono G (singleton_subset_iff.mpr hv) h)⟩
  apply (card_le_card hsub).trans
  rw [card_undominatedVertices_singleton]
  have hd := hdegree v
  omega

end GraphMinor.Thomason
