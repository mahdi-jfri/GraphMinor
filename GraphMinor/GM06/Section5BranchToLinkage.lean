module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5DeletedStartComponents
import GraphMinor.GM06.Section5FirstHit
import GraphMinor.GM06.Section3Basic
import GraphMinor.GM11.Section4b
import GraphMinor.GM11.Walks

/-!
# Following an initial branch back to the linkage

For the boundary argument in VI (5.1), page 129, start along any
non-loop edge incident with an initial vertex. The component beyond
that vertex contains a linkage vertex, since otherwise Reduction 2
would remove it. A simple walk to its first such vertex gives a
branch that avoids the linkage until its terminal vertex.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

/-- Each non-loop initial edge can be followed to the linkage without
revisiting its initial vertex or meeting the linkage earlier. This
is the branch construction used in the boundary argument of VI (5.1). -/
theorem exists_initial_branch_to_linkage
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    {e : Set ClosedCylinder} {b : ClosedCylinder}
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) b)
    (hb : b ≠ cylinderM1Point k i) :
    ∃ j : Fin k, ∃ x ∈ (L.pathDrawing j).V,
      ∃ R : GraphWalk G.toGraph b x,
        (GraphWalk.cons hl R).IsSimple ∧
        cylinderM1Point k i ∉ R.support ∧
        ∀ y ∈ R.support, (∃ n : Fin k, y ∈ (L.pathDrawing n).V) → y = x := by
  classical
  let s := cylinderM1Point k i
  let J := G.toGraph.induce (G.V \ {s})
  let B := {y | ∃ n : Fin k, y ∈ (L.pathDrawing n).V}
  have hbJ : b ∈ Graph.vertexSet J := ⟨hl.right_mem, hb⟩
  have hle : J ≤ G.toGraph := G.toGraph.induce_le sdiff_subset
  have hmake {x : ClosedCylinder} (R : GraphWalk J b x) (hR : R.IsSimple)
      (hx : x ∈ B) (hfirst : ∀ y ∈ R.support, y ∈ B → y = x) :
      ∃ j : Fin k, ∃ z ∈ (L.pathDrawing j).V,
        ∃ T : GraphWalk G.toGraph b z, (GraphWalk.cons hl T).IsSimple ∧
          s ∉ T.support ∧ ∀ y ∈ T.support, y ∈ B → y = z := by
    let T := R.mono hle
    have hsR : s ∉ R.support := by
      intro hs
      have hh : s ∈ G.V \ {s} := R.mem_vertexSet_of_mem_support hs
      exact hh.2 rfl
    have hsT : s ∉ T.support := by
      rw [show T.support = R.support from GraphWalk.support_mono hle R]
      exact hsR
    obtain ⟨j, hx⟩ := hx
    refine ⟨j, x, hx, T, ?_, hsT, ?_⟩
    · change (s :: T.support).Nodup
      apply List.nodup_cons.mpr
      refine ⟨hsT, ?_⟩
      rw [show T.support = R.support from GraphWalk.support_mono hle R]
      exact hR
    · intro y hy hyB
      apply hfirst y ?_ hyB
      rwa [GraphWalk.support_mono] at hy
  by_cases hbB : b ∈ B
  · exact hmake (GraphWalk.nil hbJ) (by change ([b] : List ClosedCylinder).Nodup; simp)
      hbB (fun y hy _ => List.mem_singleton.mp hy)
  · let K := compOf J b
    have hK : IsGraphComponent K J := isGraphComponent_compOf hbJ
    obtain ⟨j, z, hzK, hzP⟩ := deleted_start_component_meets_linkage L hG hno i hK
    obtain ⟨W⟩ := hK.2.1.2 b (self_mem_reachSet hbJ) z hzK
    obtain ⟨R, hR, _, _⟩ := GraphWalk.exists_isSimple (W.mono hK.1)
    obtain ⟨x, hxB, T, hT, _, _, hfirst⟩ := exists_first_hit_walk R hR hbB ⟨j, hzP⟩
    exact hmake T hT hxB hfirst

end GraphMinor.GM06
