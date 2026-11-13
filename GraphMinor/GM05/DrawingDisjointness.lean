module

public import GraphMinor.Surface.Defs
import GraphMinor.GM11.Section6
import GraphMinor.GM19.Section6a

/-!
# Vertex-disjoint subdrawings have disjoint supports

For GM V, (8.14), a common open edge would give a common endpoint.
Thus vertex-disjoint subdrawings also have disjoint edge sets. The
library intersection lemma then makes their full supports disjoint.
-/

public section
namespace GraphMinor.GM05
open Set Graph Surface

/-- Subdrawings with disjoint vertex sets have disjoint full supports. -/
theorem subdrawings_disjoint_of_vertices {S : Type*} [TopologicalSpace S] [T1Space S]
    {D A B : Drawing S} (hA : A.IsSubdrawing D) (hB : B.IsSubdrawing D)
    (hV : Disjoint A.V B.V) : Disjoint A.U B.U := by
  have hE : Disjoint A.E B.E := by
    apply disjoint_left.mpr
    intro e heA heB
    obtain ⟨x,y,hxy⟩ := A.toGraph.exists_isLink_of_mem_edgeSet heA
    have hx : x∈tilde e := by
      rw [GM19.tilde_eq_inter_V A heA,hxy.2.2.2]
      exact .inl rfl
    have hxB : x∈B.V := (GM19.tilde_eq_inter_V B heB ▸ hx).2
    exact disjoint_left.mp hV hxy.left_mem hxB
  rw [disjoint_iff_inter_eq_empty,GM11.U_inter_of_disjoint hA hB hE]
  exact disjoint_iff_inter_eq_empty.mp hV

end GraphMinor.GM05
