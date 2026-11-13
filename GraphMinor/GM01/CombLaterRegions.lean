module

public import GraphMinor.GM01.SubdivisionAvoidance
public import GraphMinor.GM01.PathCombs
import GraphMinor.GM01.CombSpineCuts
import Lean.Elab.Tactic.Omega

/-!
# Later spine centres belong to the cut regions

For the page-55 blocks of Graph Minors I, the next cut must lie inside
the preceding region. Follow successive spine edges from that cut to
the last spine vertex. Their replacing paths avoid the earlier cut
centre, so their concatenation gives the required reachability.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- Later spine centres remain joined in the subdivision after an earlier
spine centre is deleted. The proof follows the consecutive spine edges. -/
theorem comb_subdivision_later_reachable {α β : Type*} {γ δ : ℕ}
    {N : Graph α β} {c : (pathComb γ δ).verts → α} (hc : Function.Injective c)
    {P : (pathComb γ δ).coe.edgeSet → Graph α β}
    (hPaths : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (i j t : Fin δ) (hij : i.val < j.val) (hjt : j.val ≤ t.val) :
    Relation.ReflTransGen
      (N.deleteVerts {c ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩}).Adj
      (c ⟨Sum.inl j, pathComb_spine_mem γ δ j⟩)
      (c ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩) := by
  let spine (k : Fin δ) : (pathComb γ δ).verts :=
    ⟨Sum.inl k, pathComb_spine_mem γ δ k⟩
  have aux : ∀ m (hm : m < δ), j.val ≤ m → m ≤ t.val →
      Relation.ReflTransGen (N.deleteVerts {c (spine i)}).Adj
        (c (spine j)) (c (spine ⟨m, hm⟩)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm hjm hmt
      by_cases heq : j.val = m
      · have heq' : j = ⟨m, hm⟩ := Fin.ext heq
        rw [← heq']
      · have hmpos : 0 < m := by omega
        have hprev := ih (m - 1) (by omega) (by omega) (by omega) (by omega)
        have hadj : (pathComb γ δ).coe.Adj (spine ⟨m - 1, by omega⟩) (spine ⟨m, hm⟩) :=
          pathComb_spine_adj (γ := γ) (pathGraph_adj.mpr (Or.inl (by
            change m - 1 + 1 = m
            omega)))
        have hleft : spine ⟨m - 1, by omega⟩ ≠ spine i := by
          intro heq
          have hval := congrArg (fun v : (pathComb γ δ).verts ↦
            (pathCombSpineIndex v.val).val) heq
          change m - 1 = i.val at hval
          omega
        have hright : spine ⟨m, hm⟩ ≠ spine i := by
          intro heq
          have hval := congrArg (fun v : (pathComb γ δ).verts ↦
            (pathCombSpineIndex v.val).val) heq
          change m = i.val at hval
          omega
        exact hprev.trans (subdivision_adjacent_centres_reachable_avoiding hc hPaths hadj hleft hright)
  exact aux t.val t.isLt hjt le_rfl

/-- Each later cut centre belongs to the region beyond an earlier spine
cut. This provides the membership condition for connectivity of the
successive-difference blocks on page 55. -/
theorem comb_subdivision_later_mem_region {α β : Type*} {γ δ : ℕ}
    {N : Graph α β} {c : (pathComb γ δ).verts → α} (hc : Function.Injective c)
    (hcentres : ∀ v, c v ∈ V(N))
    {P : (pathComb γ δ).coe.edgeSet → Graph α β}
    (hPaths : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (i j t : Fin δ) (hij : i.val < j.val) (hjt : j.val ≤ t.val) :
    c ⟨Sum.inl j, pathComb_spine_mem γ δ j⟩ ∈ vertexAvoidanceRegion N
      (c ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩)
      (c ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩) := by
  refine ⟨?_, Std.Symm.symm _ _ (comb_subdivision_later_reachable hc hPaths i j t hij hjt)⟩
  rw [vertexSet_deleteVerts]
  refine ⟨hcentres _, ?_⟩
  intro heq
  have hji : j = i := Sum.inl.inj (congrArg Subtype.val (hc heq))
  have hval := congrArg Fin.val hji
  omega

end GraphMinor.GM01
