module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5PuncturedRootSeparation
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM11.Walks

/-!
# The actual retained barrier after removing the attachment

For the attached enclosures in VI (5.5), page 130, a preconnected
retained set avoiding the attachment lies on the side of one
component of the vertex-deleted graph. Choose the component of one
of its vertices and construct its incident-edge neighbourhood.
The other side of the resulting separation meets it only at the
attachment. Preconnectedness keeps the retained set on the chosen side.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Construct a retained subdrawing whose puncture is connected
and which contains a specified preconnected retained set avoiding
the attachment. The component is chosen in the actual deleted graph. -/
theorem exists_punctured_barrier_separation_containing_preconnected_set
    {S : Type} [TopologicalSpace S] [T2Space S] (G : Drawing S)
    {s : S} (hs : s ∈ G.V) {X : Set S} (hX : IsPreconnected X)
    (hXG : X ⊆ G.U) (hsX : s ∉ X) {a : S} (haX : a ∈ X) (haG : a ∈ G.V) :
    ∃ T R : Drawing S, T.IsSubdrawing G ∧ s ∈ T.V ∧ X ⊆ T.U ∧
      IsConnected (T.U \ {s}) ∧
      IsGraphSeparation G.toGraph R.toGraph T.toGraph ∧ R.U ∩ T.U ⊆ {s} := by
  let D := induceDrawing G (G.V \ {s})
  have hDG : D.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hDV : D.V = G.V \ {s} := induceDrawing_V G sdiff_subset
  have haD : a ∈ D.V := hDV.symm ▸ ⟨haG, fun he => hsX (mem_singleton_iff.mp he ▸ haX)⟩
  let C := compOf D.toGraph a
  have hC : IsGraphComponent C D.toGraph := isGraphComponent_compOf haD
  have hCV : Graph.vertexSet C ⊆ D.V := hC.1.vertexSet_mono
  let P := induceDrawing D (Graph.vertexSet C)
  have hPD : P.IsSubdrawing D := induceDrawing_isSubdrawing D hCV
  have hPG : P.IsSubdrawing G := ⟨hPD.1.trans hDG.1, hPD.2.trans hDG.2⟩
  have hPV : P.V = Graph.vertexSet C := induceDrawing_V D hCV
  have hPU : P.U = compPointSet C := induceDrawing_U_of_component D hC
  have hP : IsConnected P.U := hPU.symm ▸ isConnected_compPointSet D hC
  have hsP : s ∉ P.U := by
    intro h
    have hsPV := vertex_mem_of_mem_subdrawing_point_set hPG h hs
    have hsDV := hCV (hPV ▸ hsPV)
    rw [hDV] at hsDV
    exact hsDV.2 rfl
  have haP : a ∈ P.V := hPV.symm ▸ self_mem_reachSet haD
  have hport : ∀ e u v, G.toGraph.IsLink e u v → u ∈ P.V → v ∈ P.V ∨ v = s := by
    intro e u v hl huP
    by_cases hvs : v = s
    · exact Or.inr hvs
    · have huC : u ∈ Graph.vertexSet C := hPV ▸ huP
      have huD : u ∈ G.V \ {s} := hDV ▸ hCV huC
      have hvD : v ∈ G.V \ {s} := ⟨hl.right_mem, hvs⟩
      have hlD : D.toGraph.IsLink e u v := by
        rw [induceDrawing_toGraph_eq_induce G sdiff_subset]
        exact ⟨hl, huD, hvD⟩
      exact Or.inl (hPV.symm ▸ (hC.mem_iff_of_isLink hlD).mp huC)
  obtain ⟨T, hsep, hTV, hconn, hPT⟩ := exists_punctured_root_separation hPG hP hs hsP hport
  let R := induceDrawing G (G.V \ P.V)
  have hRV : R.V = G.V \ P.V := induceDrawing_V G sdiff_subset
  have hTG : T.IsSubdrawing G := ⟨hsep.2.1.vertexSet_mono, hsep.2.1.edgeSet_mono⟩
  have hsets := point_sets_of_graph_separation hsep
  have hover : R.U ∩ T.U ⊆ {s} := by
    rw [hsets.2]
    rintro x ⟨hxR, hxT⟩
    rw [hRV] at hxR
    rw [hTV] at hxT
    exact hxT.resolve_left hxR.2
  have hcover : X ⊆ T.U ∪ R.U := by
    rw [union_comm, hsets.1]
    exact hXG
  have hinter : X ∩ (T.U ∩ R.U) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxX, hxT, hxR⟩
    exact hsX (mem_singleton_iff.mp (hover ⟨hxR, hxT⟩) ▸ hxX)
  have hXT : X ⊆ T.U := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hX T.U R.U
      T.isClosed_U R.isClosed_U hcover hinter with h | h
    · exact h
    · have haT := T.V_subset_U (hPT.1 haP)
      exact False.elim (hsX (mem_singleton_iff.mp (hover ⟨h haX, haT⟩) ▸ haX))
  exact ⟨T, R, hTG, hTV.symm ▸ Or.inr rfl, hXT, hconn, hsep, hover⟩

/-- Forget the other separation side after constructing the actual
punctured barrier containing the prescribed preconnected set. -/
theorem exists_punctured_barrier_containing_preconnected_set
    {S : Type} [TopologicalSpace S] [T2Space S] (G : Drawing S)
    {s : S} (hs : s ∈ G.V) {X : Set S} (hX : IsPreconnected X)
    (hXG : X ⊆ G.U) (hsX : s ∉ X) {a : S} (haX : a ∈ X) (haG : a ∈ G.V) :
    ∃ T : Drawing S, T.IsSubdrawing G ∧ s ∈ T.V ∧ X ⊆ T.U ∧ IsConnected (T.U \ {s}) := by
  obtain ⟨T, _, hTG, hsT, hXT, hconn, _, _⟩ :=
    exists_punctured_barrier_separation_containing_preconnected_set G hs hX hXG hsX haX haG
  exact ⟨T, hTG, hsT, hXT, hconn⟩

end GraphMinor.GM06
