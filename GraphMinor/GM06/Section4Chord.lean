module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.Defs
import GraphMinor.GM06.Section4Segment
import GraphMinor.GM11.Walks
import GraphMinor.GM11.Section4b
import GraphMinor.GM11.EvenCircuit
import GraphMinor.GM06.Section5Red
import GraphMinor.GM07.Section3
import GraphMinor.Surface.DiscArcs

/-!
# Paths inside an inclusion-minimal enclosed disc

For Graph Minors VI, Section 4, page 124, a path inside a candidate disc
has the same homotopy class as the boundary segment. Its boundary circle
bounds a disc inside that candidate. If the candidate has no smaller enclosed
disc, the inside path must retain every edge of its path boundary. This rules
out a shortcut across the inside of the candidate.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u

private theorem curvesHomotopic_of_range_subset_closedDisc
    {S : Type u} [TopologicalSpace S] {D : Set S} (hD : IsClosedDisc D)
    {f g : Curve S} (hf : range f ⊆ D) (hg : range g ⊆ D)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) : CurvesHomotopic f g := by
  have hflat : GM11.IsFlat D := by
    intro γ hγ
    obtain ⟨c, _, H, _, hH0, hH1⟩ := hD.isSimplyConnectedSet.2 γ hγ
    exact ⟨c, mem_univ _, H, fun _ => mem_univ _, hH0, hH1⟩
  exact GM07.IsFlat.curvesHomotopic hflat hf hg h0 h1

/-- A path inside a closed disc incident with the segment encloses a disc
inside that disc. This is the shortcut step for the minimal path in Graph
Minors VI, Section 4, page 124. -/
theorem exists_enclosedDisc_below_of_path_in_disc
    {S : Type u} [TopologicalSpace S] {G Q : Drawing S} {s t : S} {A D : Set S}
    (hS : IsSurface S) (hG : G.IsProper)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hD : IsClosedDisc D) (hAD : closure A ⊆ D)
    (a : Curve S) (ha : ParametrizesSet a (closure A) s t)
    (hQ : IsSubpathOf G Q s t) (hQD : Q.U ⊆ D) :
    PathHomotopicToArc Q s t A ∧ ∃ E : Set S, IsEnclosedDisc Q A E ∧ E ⊆ D := by
  let : T2Space S := hS.2.1
  obtain ⟨q, hq⟩ := hQ.2.2.2
  have hqa : CurvesHomotopic q a := curvesHomotopic_of_range_subset_closedDisc hD
    (by rw [hq.2.1]; exact hQD) (by rw [ha.2.1]; exact hAD)
    (hq.2.2.1.trans ha.2.2.1.symm) (hq.2.2.2.trans ha.2.2.2.symm)
  have hQA : PathHomotopicToArc Q s t A := ⟨q, a, hq, ha, hqa⟩
  obtain ⟨E₀, hE₀⟩ := exists_enclosedDisc_of_segment_path hS hG hQ.1 hseg hQA
  have hO : IsOArc (Q.U ∪ closure A) := by
    rw [← hE₀.2.2]
    exact hE₀.1.isOArc_discBd
  obtain ⟨E, hE, _⟩ := disc_oArc D (Q.U ∪ closure A) hD (union_subset hQD hAD) hO
  refine ⟨hQA, E, ⟨hE.2.1, ?_, hE.2.2.1⟩, hE.1⟩
  intro x hx
  apply Surface.discBd_subset E
  rw [hE.2.2.1]
  exact Or.inr (subset_closure hx)

/-- Every path inside an inclusion-minimal enclosed disc retains each edge
of its path boundary. This is the shortcut contradiction used to choose
`P(s,t,S)` in Graph Minors VI, Section 4, page 124. -/
theorem edge_mem_of_subpath_inside_inclusion_minimal
    {S : Type u} [TopologicalSpace S] {G P : Drawing S} {s t : S} {A D : Set S}
    (hS : IsSurface S) (hG : G.IsProper)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hP : IsSubpathOf G P s t) (hPA : PathHomotopicToArc P s t A)
    (hD : IsEnclosedDisc P A D)
    (hmin : ∀ (Q : Drawing S) (E : Set S), IsSubpathOf G Q s t →
      PathHomotopicToArc Q s t A → IsEnclosedDisc Q A E → E ⊆ D → D ⊆ E)
    {Q : Drawing S} (hQ : IsSubpathOf G Q s t) (hQD : Q.U ⊆ D) : P.E ⊆ Q.E := by
  let : T2Space S := hS.2.1
  obtain ⟨_, a, _, ha, _⟩ := hPA
  have hAD : closure A ⊆ D := fun x hx => Surface.discBd_subset D (hD.2.2 ▸ Or.inr hx)
  obtain ⟨hQA, E, hE, hED⟩ :=
    exists_enclosedDisc_below_of_path_in_disc hS hG hseg hD.1 hAD a ha hQ hQD
  have hDE := hmin Q E hQ hQA hE hED
  have heq : D = E := Subset.antisymm hDE hED
  have hAsub : A ⊆ bd S := by
    obtain ⟨x, hx, heq⟩ := hseg.1
    rw [← heq]
    exact (connectedComponentIn_subset _ x).trans sdiff_subset
  have hclA : closure A ⊆ bd S := closure_minimal hAsub (isClosed_bd S)
  intro e he
  have heG := hP.1.2 he
  obtain ⟨w, hw⟩ := heG.1
  have hwG : w ∈ G.U ∧ w ∉ G.V := heG.2.1 hw
  have hwnb : w ∉ bd S := fun hwb => hwG.2 (hG ⟨hwb, hwG.1⟩)
  have hwD : w ∈ discBd D := by
    rw [hD.2.2]
    exact Or.inl (P.closure_subset_U he (subset_closure hw))
  have hwE : w ∈ discBd E := heq ▸ hwD
  rw [hE.2.2] at hwE
  have hwQ : w ∈ Q.U := hwE.resolve_right (fun h => hwnb (hclA h))
  have hwQV : w ∉ Q.V := fun hv => hwG.2 (hQ.1.1 hv)
  obtain ⟨f, hf, hwf⟩ := Q.exists_edge_of_mem hwQ hwQV
  have hef : e = f := G.edge_eq_of_mem heG (hQ.1.2 hf) hw hwf
  exact hef ▸ hf

/-- The same edge-retention property holds for a walk, since removing repeated
vertices keeps the walk inside the disc. This is used to replace a boundary
subpath by an interior chord in Graph Minors VI, Section 4, page 124. -/
theorem edge_mem_of_walk_inside_inclusion_minimal
    {S : Type u} [TopologicalSpace S] {G P : Drawing S} {s t : S} {A D : Set S}
    (hS : IsSurface S) (hG : G.IsProper)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hP : IsSubpathOf G P s t) (hPA : PathHomotopicToArc P s t A)
    (hD : IsEnclosedDisc P A D)
    (hmin : ∀ (Q : Drawing S) (E : Set S), IsSubpathOf G Q s t →
      PathHomotopicToArc Q s t A → IsEnclosedDisc Q A E → E ⊆ D → D ⊆ E)
    (W : GraphWalk G.toGraph s t)
    (hWV : ∀ x ∈ W.support, x ∈ D) (hWE : ∀ e ∈ W.edges, closure e ⊆ D) :
    ∀ e ∈ P.E, e ∈ W.edges := by
  classical
  let : T2Space S := hS.2.1
  obtain ⟨f, hf⟩ := hP.2.2.2
  have hst : s ≠ t := by
    intro heq
    exact zero_ne_one (hf.1 (hf.2.2.1.trans (heq.trans hf.2.2.2.symm)))
  obtain ⟨R, hR, hRV, hRE⟩ := GM11.GraphWalk.exists_isSimple W
  let Q := walkDrawing G R
  have hQG : Q.IsSubdrawing G := walkDrawing_isSubdrawing G R
  have hQ : IsSubpathOf G Q s t :=
    ⟨hQG, hQG.U_subset, isPathDrawing_walkDrawing_of_isSimple G hR hst⟩
  have hQD : Q.U ⊆ D := by
    intro x hx
    rw [mem_walkDrawing_U] at hx
    rcases hx with hx | ⟨e, he, hxe⟩
    · exact hWV x (hRV x hx)
    · exact hWE e (hRE e he) hxe
  have hretain := edge_mem_of_subpath_inside_inclusion_minimal hS hG hseg hP hPA hD hmin hQ hQD
  intro e he
  have heQ := hretain he
  rw [walkDrawing_E] at heQ
  exact hRE e heQ

private theorem lift_walk_inside_disc
    {S : Type u} [TopologicalSpace S] {G R : Drawing S} {u v : S} {D : Set S}
    (hRG : R.IsSubdrawing G) (hRD : R.U ⊆ D) (W : GraphWalk R.toGraph u v) :
    ∃ W' : GraphWalk G.toGraph u v, W'.edges = W.edges ∧
      (∀ x ∈ W'.support, x ∈ D) ∧ (∀ e ∈ W'.edges, closure e ⊆ D) := by
  obtain ⟨W', hs, he⟩ := hRG.exists_walk_up W
  refine ⟨W', he, ?_, ?_⟩
  · intro x hx
    rw [hs] at hx
    exact hRD (R.V_subset_U (W.mem_vertexSet_of_mem_support hx))
  · intro e he'
    rw [he] at he'
    exact (R.closure_subset_U (mem_E_of_mem_edges W he')).trans hRD

private theorem walk_vertices_inside_append
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {s u t : S} {D : Set S}
    (L : GraphWalk G.toGraph s u) (R : GraphWalk G.toGraph u t)
    (hL : ∀ x ∈ L.support, x ∈ D) (hR : ∀ x ∈ R.support, x ∈ D) :
    ∀ x ∈ (L.append R).support, x ∈ D := by
  intro x hx
  rcases (GraphWalk.mem_support_append L R).mp hx with hxL | hxR
  · exact hL x hxL
  · exact hR x hxR

private theorem walk_edges_inside_append
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {s u t : S} {D : Set S}
    (L : GraphWalk G.toGraph s u) (R : GraphWalk G.toGraph u t)
    (hL : ∀ e ∈ L.edges, closure e ⊆ D) (hR : ∀ e ∈ R.edges, closure e ⊆ D) :
    ∀ e ∈ (L.append R).edges, closure e ⊆ D := by
  intro e he
  rw [GraphWalk.edges_append, List.mem_append] at he
  exact he.elim (hL e) (hR e)

/-- An interior chord between two distinct vertices of the path boundary would
replace a nonempty part of that boundary. It therefore contradicts the finite
minimal choice in Graph Minors VI, Section 4, page 124. -/
theorem no_chord_of_inclusion_minimal_enclosed_subpath
    {S : Type u} [TopologicalSpace S] {G P : Drawing S} {s t : S} {A D : Set S}
    (hS : IsSurface S) (hG : G.IsProper)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hP : IsSubpathOf G P s t) (hPA : PathHomotopicToArc P s t A)
    (hD : IsEnclosedDisc P A D)
    (hmin : ∀ (Q : Drawing S) (E : Set S), IsSubpathOf G Q s t →
      PathHomotopicToArc Q s t A → IsEnclosedDisc Q A E → E ⊆ D → D ⊆ E)
    (W : GraphWalk P.toGraph s t) (hW : W.IsSimple)
    (hWE : P.E = {e | e ∈ W.edges})
    {u v : S} (L : GraphWalk P.toGraph s u) (M : GraphWalk P.toGraph u v)
    (N : GraphWalk P.toGraph v t) (hsplit : W = L.append (M.append N)) (huv : u ≠ v)
    {R : Drawing S} (hR : R.IsSubdrawing G) (WR : GraphWalk R.toGraph u v)
    (hRD : R.U ⊆ D) (hinter : R.U ∩ P.U ⊆ {u, v}) : False := by
  classical
  have hPD : P.U ⊆ D := fun x hx => Surface.discBd_subset D (hD.2.2 ▸ Or.inl hx)
  obtain ⟨L', hLedges, hLV, hLE⟩ := lift_walk_inside_disc hP.1 hPD L
  obtain ⟨N', hNedges, hNV, hNE⟩ := lift_walk_inside_disc hP.1 hPD N
  obtain ⟨R', hRedges, hRV, hRE'⟩ := lift_walk_inside_disc hR hRD WR
  have hMne : M.edges ≠ [] := by
    cases M with
    | nil _ => exact False.elim (huv rfl)
    | cons _ _ => simp [GraphWalk.edges]
  obtain ⟨e, heM⟩ := List.exists_mem_of_ne_nil M.edges hMne
  have heP : e ∈ P.E := by
    rw [hWE, hsplit, GraphWalk.edges_append, GraphWalk.edges_append]
    exact List.mem_append_right _ (List.mem_append_left _ heM)
  have hnd := hW.edges_nodup
  rw [hsplit, GraphWalk.edges_append, GraphWalk.edges_append] at hnd
  have heL : e ∉ L.edges := by
    intro he
    exact (List.nodup_append.mp hnd).2.2 e he e
      (List.mem_append_left _ heM) rfl
  have heN : e ∉ N.edges := by
    intro he
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).2.2 e heM e he rfl
  have heR : e ∉ R.E := by
    intro he
    obtain ⟨w, hw⟩ := heP.1
    have hwP : w ∈ P.U := P.closure_subset_U heP (subset_closure hw)
    have hwR : w ∈ R.U := R.closure_subset_U he (subset_closure hw)
    have hwnV : w ∉ G.V := ((hP.1.2 heP).2.1 hw).2
    have huP : u ∈ P.V := M.mem_vertexSet_of_mem_support M.start_mem_support
    have hvP : v ∈ P.V := M.mem_vertexSet_of_mem_support M.end_mem_support
    rcases mem_insert_iff.mp (hinter ⟨hwR, hwP⟩) with heq | heq
    · apply hwnV
      rw [heq]
      exact hP.1.1 huP
    · apply hwnV
      rw [mem_singleton_iff.mp heq]
      exact hP.1.1 hvP
  have heR' : e ∉ WR.edges := by
    intro he
    exact heR (mem_E_of_mem_edges WR he)
  have hWV := walk_vertices_inside_append L' (R'.append N') hLV
    (walk_vertices_inside_append R' N' hRV hNV)
  have hWED := walk_edges_inside_append L' (R'.append N') hLE
    (walk_edges_inside_append R' N' hRE' hNE)
  have heNew := edge_mem_of_walk_inside_inclusion_minimal hS hG hseg hP hPA hD hmin
    (L'.append (R'.append N')) hWV hWED e heP
  rw [GraphWalk.edges_append, GraphWalk.edges_append, hLedges, hRedges, hNedges] at heNew
  rcases List.mem_append.mp heNew with he | he
  · exact heL he
  · rcases List.mem_append.mp he with he | he
    · exact heR' he
    · exact heN he

private theorem walk_append_assoc
    {S : Type u} [TopologicalSpace S] {P : Drawing S} {s u v t : S}
    (L : GraphWalk P.toGraph s u) (M : GraphWalk P.toGraph u v) (N : GraphWalk P.toGraph v t) :
    (L.append M).append N = L.append (M.append N) := by
  induction L with
  | nil _ => rfl
  | cons hl r ih =>
    change GraphWalk.cons hl ((r.append M).append N) = GraphWalk.cons hl (r.append (M.append N))
    rw [ih]

private theorem split_walk_at_two_vertices
    {S : Type u} [TopologicalSpace S] {P : Drawing S} {s t u v : S}
    (W : GraphWalk P.toGraph s t) (hu : u ∈ W.support) (hv : v ∈ W.support) :
    (∃ (L : GraphWalk P.toGraph s u) (M : GraphWalk P.toGraph u v)
      (N : GraphWalk P.toGraph v t), W = L.append (M.append N)) ∨
    (∃ (L : GraphWalk P.toGraph s v) (M : GraphWalk P.toGraph v u)
      (N : GraphWalk P.toGraph u t), W = L.append (M.append N)) := by
  classical
  obtain ⟨L, T, hW⟩ := W.exists_append_of_mem hu
  by_cases hvT : v ∈ T.support
  · obtain ⟨M, N, hT⟩ := T.exists_append_of_mem hvT
    exact Or.inl ⟨L, M, N, by rw [hW, hT]⟩
  · have hvL : v ∈ L.support := by
      rw [hW] at hv
      exact ((GraphWalk.mem_support_append L T).mp hv).resolve_right hvT
    obtain ⟨L', M, hL⟩ := L.exists_append_of_mem hvL
    exact Or.inr ⟨L', M, T, by rw [hW, hL, walk_append_assoc]⟩

/-- An inclusion-minimal enclosed path has no chord in the graph lying inside
its disc and otherwise off its path boundary. This form does not depend on
the order in which the chord's ends occur on the boundary path, as needed in
Graph Minors VI, Section 4, page 124. -/
theorem no_chord_between_vertices_of_inclusion_minimal
    {S : Type u} [TopologicalSpace S] {G P : Drawing S} {s t : S} {A D : Set S}
    (hS : IsSurface S) (hG : G.IsProper)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hP : IsSubpathOf G P s t) (hPA : PathHomotopicToArc P s t A)
    (hD : IsEnclosedDisc P A D)
    (hmin : ∀ (Q : Drawing S) (E : Set S), IsSubpathOf G Q s t →
      PathHomotopicToArc Q s t A → IsEnclosedDisc Q A E → E ⊆ D → D ⊆ E)
    {u v : S} (hu : u ∈ P.V) (hv : v ∈ P.V) (huv : u ≠ v)
    {R : Drawing S} (hR : R.IsSubdrawing G) (WR : GraphWalk R.toGraph u v)
    (hRD : R.U ⊆ D) (hinter : R.U ∩ P.U ⊆ {u, v}) : False := by
  obtain ⟨W, hW, hV, hE⟩ := hP.2.2.1
  have huW : u ∈ W.support := by rw [hV] at hu; exact hu
  have hvW : v ∈ W.support := by rw [hV] at hv; exact hv
  rcases split_walk_at_two_vertices W huW hvW with ⟨L, M, N, hsplit⟩ | ⟨L, M, N, hsplit⟩
  · exact no_chord_of_inclusion_minimal_enclosed_subpath hS hG hseg hP hPA hD hmin
      W hW hE L M N hsplit huv hR WR hRD hinter
  · have hinter' : R.U ∩ P.U ⊆ {v, u} := by rw [Set.pair_comm]; exact hinter
    exact no_chord_of_inclusion_minimal_enclosed_subpath hS hG hseg hP hPA hD hmin
      W hW hE L M N hsplit huv.symm hR WR.reverse hRD hinter'

end GraphMinor.GM06
