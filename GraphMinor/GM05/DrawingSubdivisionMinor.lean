module

public import GraphMinor.Surface.Defs
public import GraphMinor.GM19.Section6Contract
public import GraphMinor.Statement
import GraphMinor.GM11.SplitEdge
import GraphMinor.GM12.Section4SplitMinorModel
import GraphMinor.GM19.Section6a
import GraphMinor.GM11.RadialCorners
import GraphMinor.Minor.Basic

/-!
# Subdivision preserves the original graph as a minor

For GM V, (8.14), the neighbourhood construction may first subdivide
every edge to remove loops. Use the library's actual edge splitting
and its minor model: each original vertex absorbs the midpoints
assigned to it, and each original edge is represented by its left
half. This also handles loops and isolated vertices.
-/

public section
namespace GraphMinor.GM05
open Set Surface

/-- The edge splitting used for GM V, (8.14), page 113, preserves
the original graph as a minor. The minor model is the already proved
GM XII `isMinorModel_of_splitData`. -/
theorem exists_loopFree_minor_refinement {S : Type} [TopologicalSpace S]
    [T2Space S] [Nonempty S] (D : Drawing S) :
    ∃ K : Drawing S, K.U = D.U ∧ D.V ⊆ K.V ∧ GM19.LoopFree K ∧
      IsIsoMinor D.toGraph K.toGraph := by
  obtain ⟨K,A,B,m,x,y,hU,hV,hprops,hall⟩ := GM11.exists_split D
  have hd : GM11.SplitData D K A B m x y := by
    refine ⟨hU,hV,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hall⟩
    all_goals
      intro e he
      obtain ⟨hA,hB,hm,hmA,hmB,hdis,hunion,hx,hy,hcap,hcapA,hcapB⟩ := hprops e he
      assumption
  have hloop : GM19.LoopFree K := by
    intro e he
    obtain ⟨u,v,huv,hcap⟩ := hd.noLoop e he
    exact ⟨u,v,huv,by rw [GM19.tilde_eq_inter_V K he,hcap],
      GM11.isLine_closure he huv hcap⟩
  refine ⟨K,hU,?_,hloop,?_⟩
  · rw [hV]
    exact subset_union_left
  · exact isIsoMinor_of_isMinorModel D.toGraph K.toGraph D.finite_V D.finite_edges
      K.finite_V K.finite_edges _ _ (GM12.isMinorModel_of_splitData hd)

end GraphMinor.GM05
