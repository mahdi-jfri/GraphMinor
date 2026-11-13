module

public import GraphMinor.GM08.Defs6to18
public import GraphMinor.Surface.Defs
import GraphMinor.GM08.Section9Simulation
import GraphMinor.GM08.Section9Width
import GraphMinor.GM08.Section9GraftDrawing
import GraphMinor.Surface.Disc
import GraphMinor.GM06.DiscRegions

/-!
# Graph Minors VIII (9.4): bounded truncations when a graft is excluded

Choose the nest parameters supplied by (9.3) for the fixed target graft.
A host that does not simulate that graft has no such boundary-linked
nest. Applying (9.2) then bounds every truncation of every host drawing.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u v u' v' w

/-- Graph Minors VIII, (9.4), page 270: excluding a fixed disc-embeddable
graft bounds the tree-width of every truncation of every drawing of a
host graft of the same index. This follows from (9.2) and (9.3). -/
theorem theorem_9_4_proof {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {S : Type w} [TopologicalSpace S] (hΔ : IsClosedDisc (univ : Set S))
    (Y : Graft α β) (hY : EmbedsGraft S Y) :
    ∃ width : ℕ, ∀ (X : Graft α' β'), X.index = Y.index →
      ¬ IsGraftSimulatedIn Y X → ∀ (gd : GraftDrawing X.G X.T S)
        (Dstar : Drawing S), IsTruncation gd.drawing univ Dstar →
        DrawingTreeWidthLE Dstar width := by
  obtain ⟨r, s, hr, hs, hlarge⟩ := theorem_9_3_proof (α' := α') (β' := β') hΔ Y hY
  obtain ⟨width, hw⟩ := theorem_9_2_proof.{w} Y.index r s hr hs
  obtain ⟨x, -⟩ := hΔ.isPathConnected.nonempty
  have : Nonempty S := ⟨x⟩
  refine ⟨width, fun X hX hnot gd Dstar htrunc => ?_⟩
  apply hw hΔ gd.drawing gd.isProper
  · rw [GM06.discBd_univ, graftDrawing_boundary_ncard gd]
    exact hX
  · intro N hBL
    exact hnot (hlarge X hX gd N hBL)
  · exact htrunc

end GraphMinor.GM08
