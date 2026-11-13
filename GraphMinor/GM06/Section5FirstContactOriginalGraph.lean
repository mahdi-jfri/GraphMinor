module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5AdjoinedEdges
import GraphMinor.GM06.Section5LinkageEnds
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# A first-contact prefix uses only original edges

For the region-boundary construction in VI (5.1), page 129, the
prefix to the first new linkage vertex already avoids initial-cuff
edges. It cannot use a terminal-cuff edge: both ends of such an edge
are linkage vertices, whereas the simple prefix has only its last
vertex on that cuff. A used edge of a simple walk has distinct ends.
Thus every edge of the prefix belongs to the original graph.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
universe u v

private theorem exists_distinct_used_link
    {α : Type u} {β : Type v} {H : Graph α β} {s t : α}
    (W : GraphWalk H s t) (hW : W.IsSimple) {e : β} (he : e ∈ W.edges) :
    ∃ a ∈ W.support, ∃ b ∈ W.support, a ≠ b ∧ H.IsLink e a b := by
  induction W with
  | nil _ => simp at he
  | @cons s a t f hl R ih =>
    rcases List.mem_cons.mp he with hef | heR
    · subst e
      refine ⟨s, List.mem_cons_self, a, List.mem_cons_of_mem s R.start_mem_support, ?_, hl⟩
      intro hsa
      exact (List.nodup_cons.mp hW).1 (hsa.symm ▸ R.start_mem_support)
    · obtain ⟨a, ha, b, hb, hab, hl⟩ := ih hW.of_cons heR
      exact ⟨a, List.mem_cons_of_mem s ha, b, List.mem_cons_of_mem s hb, hab, hl⟩

/-- Every prescribed boundary vertex belongs to one of the linkage
paths, including all terminal vertices by their finite surjectivity. -/
theorem boundary_vertex_mem_linkage_vertices
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) {x : ClosedCylinder} (hx : x ∈ G.V ∩ bd ClosedCylinder) :
    x ∈ ⋃ j : Fin k, (L.pathDrawing j).V := by
  rw [hG.2.2] at hx
  rcases hx with ⟨j, rfl⟩ | hx
  · exact mem_iUnion.mpr ⟨j, (isPathDrawing_end_vertices (L.isPath j)).1⟩
  · obtain ⟨j, hj⟩ := L.curve_one_surjective hx
    exact mem_iUnion.mpr ⟨j, hj ▸ (isPathDrawing_end_vertices (L.isPath j)).2⟩

/-- A prefix to the first noninitial linkage vertex that avoids all
initial-cuff edges is a subdrawing of the original graph, rather
than merely of the drawing with cuffs adjoined. -/
theorem first_contact_prefix_isSubdrawing_original
    {k : ℕ} {G F Q : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) {v : ClosedCylinder}
    (hGF : G.IsSubdrawing F) (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    (hQF : Q.IsSubdrawing F) (hQ : IsPathDrawing Q (cylinderM1Point k i) v)
    (hcontact : Q.V ∩ (⋃ j : Fin k, (L.pathDrawing j).V) ⊆ {cylinderM1Point k i, v})
    (hC1 : ∀ e ∈ Q.E, ¬ e ⊆ cylinderCuff1) : Q.IsSubdrawing G := by
  have hterminal : ∀ x ∈ Q.V, x ∈ cylinderCuff2 → x = v := by
    intro x hxQ hxC2
    have hxG : x ∈ G.V := hFV ▸ hQF.1 hxQ
    have hxbd : x ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inr hxC2
    have hxL := boundary_vertex_mem_linkage_vertices L hG ⟨hxG, hxbd⟩
    rcases hcontact ⟨hxQ, hxL⟩ with hxs | hxv
    · have hsC2 : cylinderM1Point k i ∈ cylinderCuff2 := hxs ▸ hxC2
      have hbad : (1 : ℝ) = 2 := hsC2
      norm_num at hbad
    · exact hxv
  obtain ⟨W, hW, hQV, hQE⟩ := hQ.1
  have hclosedC2 : IsClosed cylinderCuff2 :=
    isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  constructor
  · intro x hx
    exact hFV ▸ hQF.1 hx
  · intro e heQ
    have heF := hQF.2 heQ
    rcases edge_mem_or_subset_boundary_of_adjoining hGF hFU hFV heF with heG | heBd
    · exact heG
    · rcases edge_subset_one_cuff_of_subset_boundary heF heBd with heC1 | heC2
      · exact False.elim (hC1 e heQ heC1)
      · have heW : e ∈ W.edges := by rw [hQE] at heQ; exact heQ
        obtain ⟨a, haW, b, hbW, hab, hlQ⟩ := exists_distinct_used_link W hW heW
        have haQ : a ∈ Q.V := hQV.symm ▸ haW
        have hbQ : b ∈ Q.V := hQV.symm ▸ hbW
        have hlF := (hQF.isLink_iff heQ).mp hlQ
        have haCl : a ∈ closure e :=
          (show a ∈ closure e ∩ F.V from hlF.2.2.2.symm ▸ mem_insert a {b}).1
        have hbCl : b ∈ closure e :=
          (show b ∈ closure e ∩ F.V from hlF.2.2.2.symm ▸ mem_insert_of_mem a rfl).1
        have haC2 := closure_minimal heC2 hclosedC2 haCl
        have hbC2 := closure_minimal heC2 hclosedC2 hbCl
        exact False.elim (hab ((hterminal a haQ haC2).trans (hterminal b hbQ hbC2).symm))

end GraphMinor.GM06
