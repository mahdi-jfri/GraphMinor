module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section3Basic
import GraphMinor.GM11.Walks
import GraphMinor.GM11.OArcCircuit

/-!
# Common edges of two path drawings

The excursion used in Graph Minors VI, Section 4, page 124, has no internal
vertex on the chosen path boundary. If it shared an edge with that boundary,
both ends of the edge would be its own ends, so it would consist of that edge.
Thus an excursion that also meets a set off the boundary can meet the boundary
only at its ends.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

private theorem edges_single_of_link_ends
    {S : Type u} [TopologicalSpace S] {R : Drawing S} {u v : S}
    (W : GraphWalk R.toGraph u v) (hW : W.IsSimple)
    {e : Set S} (he : e ∈ W.edges) (huv : R.toGraph.IsLink e u v) : W.edges = [e] := by
  cases W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons u w v f hf T =>
    have hnot := (List.nodup_cons.mp hW).1
    have hT := (List.nodup_cons.mp hW).2
    change e ∈ f :: T.edges at he
    rcases List.mem_cons.mp he with heq | heT
    · subst f
      have hw : w ∈ ({u, v} : Set S) := by
        rw [← huv.2.2.2, hf.2.2.2]
        exact mem_insert_of_mem u rfl
      rcases mem_insert_iff.mp hw with hwu | hwv
      · exact False.elim (hnot (hwu ▸ T.start_mem_support))
      · have hwv := mem_singleton_iff.mp hwv
        subst w
        have hz := GraphWalk.IsSimple.length_eq_zero hT
        cases T with
        | nil _ => rfl
        | cons _ _ => simp [GraphWalk.length, GraphWalk.edges] at hz
    · exact False.elim (hnot (T.left_mem_support_of_mem_edges heT huv))

private theorem path_subset_edge_of_link_ends
    {S : Type u} [TopologicalSpace S] {R : Drawing S} {u v : S}
    (hR : IsPathDrawing R u v) {e : Set S} (he : e ∈ R.E)
    (huv : R.toGraph.IsLink e u v) : R.U ⊆ closure e := by
  obtain ⟨W, hW, hV, hE⟩ := hR.1
  have heW : e ∈ W.edges := by rw [hE] at he; exact he
  have hsingle := edges_single_of_link_ends W hW heW huv
  have hsupp : W.support = [u, v] := by
    cases W with
    | nil _ => simp [GraphWalk.edges] at hsingle
    | cons hl T =>
      cases T with
      | nil _ => rfl
      | cons _ _ => simp [GraphWalk.edges] at hsingle
  have hRV : R.V ⊆ closure e := by
    rw [hV, hsupp]
    intro x hx
    simp only [mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with heq | heq
    · rw [heq]
      exact (by rw [huv.2.2.2]; exact mem_insert u {v} : u ∈ closure e ∩ R.V).1
    · rw [heq]
      exact (by rw [huv.2.2.2]; exact mem_insert_of_mem u rfl : v ∈ closure e ∩ R.V).1
  rw [R.U_eq]
  refine union_subset hRV ?_
  intro x hx
  obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
  rw [hE, hsingle] at hf
  have hfe : f = e := List.mem_singleton.mp hf
  exact hfe ▸ hxf

private theorem not_oArc_subset_path
    {S : Type u} [TopologicalSpace S] [T2Space S] {R : Drawing S} {u v : S}
    (hR : IsPathDrawing R u v) {F : Set S} (hF : IsOArc F) (hFR : F ⊆ R.U) : False := by
  obtain ⟨f, hf⟩ := hR.2
  obtain ⟨φ⟩ := hF
  let e : unitInterval ≃ₜ range f := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective f hf.1) f.continuous.rangeFactorization
  have hm : ∀ w : Circle, (φ w).1 ∈ range f := by
    intro w
    rw [hf.2.1]
    exact hFR (φ w).property
  let g : Circle → ℝ := fun w => (e.symm ⟨(φ w).1, hm w⟩ : ℝ)
  have hgc : Continuous g := by dsimp [g]; fun_prop
  apply not_injective_circle_real hgc
  intro w z h
  have heq : e.symm ⟨(φ w).1, hm w⟩ = e.symm ⟨(φ z).1, hm z⟩ := Subtype.ext h
  have hvals : (φ w).1 = (φ z).1 :=
    congrArg (fun x : range f => x.1) (e.symm.injective heq)
  exact φ.injective (Subtype.ext hvals)

private theorem path_subset_of_shared_edge
    {S : Type u} [TopologicalSpace S] [T2Space S] {G P R : Drawing S} {u v : S}
    (hRG : R.IsSubdrawing G) (hPG : P.IsSubdrawing G) (hR : IsPathDrawing R u v)
    (hvertices : R.V ∩ P.V ⊆ {u, v}) {e : Set S} (heR : e ∈ R.E) (heP : e ∈ P.E) :
    R.U ⊆ P.U := by
  have hcapP : closure e ∩ R.V = closure e ∩ P.V :=
    (hRG.closure_inter_V heR).trans (hPG.closure_inter_V heP).symm
  rcases R.edge_cond e heR with ⟨a, b, hab, hcap, _⟩ | ⟨a, hcap, hO⟩
  · have haR : a ∈ closure e ∩ R.V := by rw [hcap]; exact mem_insert a {b}
    have hbR : b ∈ closure e ∩ R.V := by rw [hcap]; exact mem_insert_of_mem a rfl
    have haP : a ∈ P.V := (hcapP ▸ haR).2
    have hbP : b ∈ P.V := (hcapP ▸ hbR).2
    have haUV : a = u ∨ a = v := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hvertices ⟨haR.2, haP⟩
    have hbUV : b = u ∨ b = v := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hvertices ⟨hbR.2, hbP⟩
    have hpair : ({a, b} : Set S) = {u, v} := by
      rcases haUV with rfl | rfl
      · rcases hbUV with rfl | rfl
        · exact False.elim (hab rfl)
        · rfl
      · rcases hbUV with rfl | rfl
        · exact pair_comm _ _
        · exact False.elim (hab rfl)
    have hcapUV : closure e ∩ R.V = {u, v} := hcap.trans hpair
    have huR : u ∈ R.V :=
      (by rw [hcapUV]; exact mem_insert u {v} : u ∈ closure e ∩ R.V).2
    have hvR : v ∈ R.V :=
      (by rw [hcapUV]; exact mem_insert_of_mem u rfl : v ∈ closure e ∩ R.V).2
    exact (path_subset_edge_of_link_ends hR heR ⟨heR, huR, hvR, hcapUV⟩).trans
      (P.closure_subset_U heP)
  · exact False.elim (not_oArc_subset_path hR hO (R.closure_subset_U heR))

private theorem vertex_of_mem_subdrawing_of_parent_vertex
    {S : Type u} [TopologicalSpace S] {G R : Drawing S}
    (hRG : R.IsSubdrawing G) {x : S} (hx : x ∈ R.U) (hxG : x ∈ G.V) : x ∈ R.V := by
  by_contra hxR
  obtain ⟨e, he, hxe⟩ := R.exists_edge_of_mem hx hxR
  exact ((hRG.2 he).2.1 hxe).2 hxG

/-- A path with only its ends among the vertices of another subdrawing also
meets that subdrawing only at its ends, provided it reaches a set off that
subdrawing. This upgrades the shortest excursion in Graph Minors VI, Section 4,
page 124, from its vertex condition to its point-set condition. -/
theorem path_intersection_subset_ends_of_vertices
    {S : Type u} [TopologicalSpace S] [T2Space S] {G P R : Drawing S} {u v : S} {X : Set S}
    (hRG : R.IsSubdrawing G) (hPG : P.IsSubdrawing G) (hR : IsPathDrawing R u v)
    (hvertices : R.V ∩ P.V ⊆ {u, v})
    (hmeet : (R.U ∩ X).Nonempty) (hPX : Disjoint P.U X) : R.U ∩ P.U ⊆ {u, v} := by
  intro x hx
  by_cases hxG : x ∈ G.V
  · exact hvertices ⟨vertex_of_mem_subdrawing_of_parent_vertex hRG hx.1 hxG,
      vertex_of_mem_subdrawing_of_parent_vertex hPG hx.2 hxG⟩
  · have hxR : x ∉ R.V := fun h => hxG (hRG.1 h)
    have hxP : x ∉ P.V := fun h => hxG (hPG.1 h)
    obtain ⟨e, heR, hxe⟩ := R.exists_edge_of_mem hx.1 hxR
    obtain ⟨f, hfP, hxf⟩ := P.exists_edge_of_mem hx.2 hxP
    have hef : e = f := G.edge_eq_of_mem (hRG.2 heR) (hPG.2 hfP) hxe hxf
    have heP : e ∈ P.E := hef.symm ▸ hfP
    have hRP := path_subset_of_shared_edge hRG hPG hR hvertices heR heP
    obtain ⟨y, hyR, hyX⟩ := hmeet
    exact False.elim (disjoint_left.mp hPX (hRP hyR) hyX)

end GraphMinor.GM06
