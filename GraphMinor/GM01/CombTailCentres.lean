module

public import GraphMinor.GM01.CombLaterRegions
public import GraphMinor.GM01.CombSpineCuts
import Lean.Elab.Tactic.Omega

/-!
# Centres in the tail region

The last-block comb in Graph Minors I, (4.1), page 55, includes the binary
copies on the retained spine interval. Starting from a later spine
centre, follow its attachment edge and then the binary parent edges.
All of these source edges avoid the earlier cut. Their replacing paths
show that every centre in a later binary copy also lies in the tail
region.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- Every source vertex assigned to a later spine position has its centre
in the region beyond an earlier cut. This includes all binary copies,
not only their spine vertices. -/
theorem comb_subdivision_later_vertex_mem_region {α β : Type*} {γ δ : ℕ}
    {N : Graph α β} {c : (pathComb γ δ).verts → α} (hc : Function.Injective c)
    (hcentres : ∀ v, c v ∈ V(N))
    {P : (pathComb γ δ).coe.edgeSet → Graph α β}
    (hPaths : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (i : Fin δ) (v : (pathComb γ δ).verts)
    (hi : i.val < (pathCombSpineIndex v.val).val) :
    c v ∈ vertexAvoidanceRegion N
      (c ⟨Sum.inl ⟨δ - 1, by omega⟩, pathComb_spine_mem γ δ _⟩)
      (c ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩) := by
  let r : (pathComb γ δ).verts := ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩
  let last : Fin δ := ⟨δ - 1, by omega⟩
  let D := vertexAvoidanceRegion N
    (c ⟨Sum.inl last, pathComb_spine_mem γ δ last⟩) (c r)
  have hneq : ∀ w : (pathComb γ δ).verts,
      i.val < (pathCombSpineIndex w.val).val → w ≠ r := by
    intro w hw heq
    have hval := congrArg (fun z : (pathComb γ δ).verts ↦
      (pathCombSpineIndex z.val).val) heq
    change (pathCombSpineIndex w.val).val = i.val at hval
    omega
  have hstep : ∀ (a b : (pathComb γ δ).verts),
      (pathComb γ δ).coe.Adj a b → c a ∈ D →
      i.val < (pathCombSpineIndex a.val).val →
      i.val < (pathCombSpineIndex b.val).val → c b ∈ D := by
    intro a b hab ha hia hib
    have hr := subdivision_adjacent_centres_reachable_avoiding hc hPaths hab
      (hneq a hia) (hneq b hib)
    refine ⟨?_, ha.2.trans hr⟩
    rw [vertexSet_deleteVerts]
    exact ⟨hcentres b, fun heq ↦ hneq b hib (hc heq)⟩
  have hspine : ∀ j : Fin δ, i.val < j.val →
      c ⟨Sum.inl j, pathComb_spine_mem γ δ j⟩ ∈ D := by
    intro j hij
    exact comb_subdivision_later_mem_region hc hcentres hPaths i j last hij
      (by change j.val ≤ δ - 1; omega)
  have hbinary : ∀ (j : Fin δ) (word : List Bool) (hw : word.length < γ), i.val < j.val →
      c ⟨Sum.inr (j, word), hw⟩ ∈ D := by
    intro j word
    induction word with
    | nil =>
      intro hw hij
      apply hstep ⟨Sum.inl j, pathComb_spine_mem γ δ j⟩ ⟨Sum.inr (j, []), hw⟩
        (pathComb_attachment_adj (by change 0 < γ at hw; exact hw) j) (hspine j hij)
      · exact hij
      · exact hij
    | cons bit word ih =>
      intro hw hij
      have hw' : word.length < γ := by simp only [List.length_cons] at hw; omega
      apply hstep ⟨Sum.inr (j, word), hw'⟩ ⟨Sum.inr (j, bit :: word), hw⟩
        ⟨rfl, hw', hw, Or.inl ⟨bit, rfl⟩⟩ (ih hw' hij)
      · exact hij
      · exact hij
  obtain ⟨v, hv⟩ := v
  cases v with
  | inl j => exact hspine j hi
  | inr p =>
    rcases p with ⟨j, word⟩
    exact hbinary j word hv hi

end GraphMinor.GM01
