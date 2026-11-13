module

public import GraphMinor.LRPlanarity.PolygonalizationArrangementPaths
public import GraphMinor.HP25.Embedding
import GraphMinor.LRPlanarity.PolygonalizationLoopErasure
import GraphMinor.Surface.TriPath
import GraphMinor.Surface.EdgeLoop

/-!
# Original edges as paths in their straight subdivision

Part IV, Section 7b of the planarity note subdivides an edge at its bends
without changing its image. The finite arrangement splits any original
line into arrangement edges. Take a simple graph path using only those
edges. Its image is a connected subset of the original line containing
both ends, so it equals the whole original line.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: an original line in a straight arrangement is the
exact image of a simple path in the arrangement graph. -/
theorem straight_arrangement_edge_path {V : Set ℂ} {E : Set (Set ℂ)} (hG : IsGraph V E)
    (hstraight : ∀ e ∈ E, ∃ a b : ℂ, e = segment ℝ a b)
    {L : Set ℂ} {u v : ℂ} (hL : IsLineWithEnds L u v) (hne : u ≠ v)
    (hu : u ∈ V) (hv : v ∈ V) (hsub : L ⊆ gr V E) :
    ∃ w : (segmentArrangementGraph V E).Walk ⟨u, hu⟩ ⟨v, hv⟩,
      w.IsPath ∧ (segmentArrangementEmbedding hG).pathImage w.support = L := by
  classical
  obtain ⟨Y, hYE, hYL, hYunion, _⟩ :=
    hG.exists_subdiv (L ∩ V).ncard rfl hL hne hu hv hsub
  have hGY : IsGraph V Y := ⟨hG.fin, hG.fine.subset hYE,
    fun e he => hG.edge e (hYE he),
    fun e he f hf hef => hG.disj e (hYE he) f (hYE hf) hef⟩
  have hYS : ∀ e ∈ Y, ∃ a b : ℂ, e = segment ℝ a b := fun e he => hstraight e (hYE he)
  have hLY : L ⊆ gr V Y := fun x hx => Or.inr (hYunion.symm ▸ hx)
  obtain ⟨w, hw⟩ := (segment_arrangement_reachable hGY hYS hL hu hv hLY).exists_isPath
  let φY := segmentArrangementEmbedding hGY
  have huv : (⟨u, hu⟩ : V) ≠ ⟨v, hv⟩ := fun he => hne (congrArg Subtype.val he)
  have himage : IsLineWithEnds (φY.pathImage w.support) u v :=
    isLine_walk_pathImage φY huv w hw
  have hwithin : φY.pathImage w.support ⊆ L := by
    intro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    obtain ⟨he, hxe⟩ := mem_iUnion.mp he
    have hadj := HP25.isChain_iff_zip.mp w.isChain_adj_support e he
    exact hYL _ hadj.2 hxe
  have heq : φY.pathImage w.support = L :=
    hL.eq_of_subset himage.isPreconnected_self hwithin himage.left_mem himage.right_mem
  let f : segmentArrangementGraph V Y →g segmentArrangementGraph V E := {
    toFun := id
    map_rel' := fun h => ⟨h.1, hYE h.2⟩
  }
  have hsupp : (w.map f).support = w.support := by
    rw [SimpleGraph.Walk.support_map]
    change w.support.map id = w.support
    exact List.map_id _
  have hpath : (w.map f).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hsupp]
    exact hw.support_nodup
  refine ⟨w.map f, hpath, ?_⟩
  rw [hsupp]
  change φY.pathImage w.support = L
  exact heq

end GraphMinor.LRPlanarity
