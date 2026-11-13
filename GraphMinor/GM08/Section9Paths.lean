module

public import GraphMinor.GM08.Section9
import GraphMinor.GM09.Basic
import GraphMinor.GM11.PaintingRegions
import GraphMinor.GM11.OArcCircuit
import GraphMinor.GM08.Section11Sleeve
import GraphMinor.GM07.CuffCore

/-!
# Paths supported by a connected part of a drawing

The radial paths in a drawing nest are given as preconnected point sets.
For the restriction to a sleeve in VIII (9.1), we need graph walks whose
vertices stay in those sets. Partition the drawing into the vertices
reachable within the set and their incident edges, and the remaining part.
The two closed parts cannot separate a preconnected set.
-/

public section

namespace GraphMinor.GM08

open Set Surface Topology Graph

universe u

/-- Two drawing vertices in a preconnected set are joined by a graph walk
whose vertices all belong to that set. This preserves disjointness when
radial paths of the nest in (9.1) are made into graph paths. -/
theorem exists_walk_supported_by_preconnected {S : Type u} [TopologicalSpace S] [T2Space S]
    (D : Drawing S) {A : Set S} (hA : IsPreconnected A) (hAU : A ⊆ D.U)
    {a b : S} (ha : a ∈ D.V) (haA : a ∈ A) (hb : b ∈ D.V) (hbA : b ∈ A) :
    ∃ W : GraphWalk D.toGraph a b, ∀ x ∈ W.support, x ∈ A := by
  classical
  let G := D.toGraph.induce (D.V ∩ A)
  let Rv : Set S := {v | v ∈ D.V ∧ v ∈ A ∧ Nonempty (GraphWalk G a v)}
  have hRa : a ∈ Rv := ⟨ha, haA, ⟨.nil ⟨ha, haA⟩⟩⟩
  have hstep : ∀ e ∈ D.E, (closure e ∩ Rv).Nonempty →
      ∀ y ∈ closure e, y ∈ D.V → y ∈ A → y ∈ Rv := by
    rintro e he ⟨r, hrc, hrV, hrA, ⟨W⟩⟩ y hy hyV hyA
    by_cases hyr : y = r
    · exact hyr ▸ ⟨hrV, hrA, ⟨W⟩⟩
    have hcap : closure e ∩ D.V = {r, y} := by
      rcases D.edge_cond e he with ⟨u, v, -, hc, -⟩ | ⟨u, hc, -⟩
      · have h1 : r ∈ ({u, v} : Set S) := hc ▸ ⟨hrc, hrV⟩
        have h2 : y ∈ ({u, v} : Set S) := hc ▸ ⟨hy, hyV⟩
        rw [hc]
        rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
        · exact (hyr rfl).elim
        · rfl
        · exact pair_comm _ _
        · exact (hyr rfl).elim
      · have h1 : r ∈ ({u} : Set S) := hc ▸ ⟨hrc, hrV⟩
        have h2 : y ∈ ({u} : Set S) := hc ▸ ⟨hy, hyV⟩
        exact (hyr (h2.trans h1.symm)).elim
    have hl : G.IsLink e r y := ⟨⟨he, hrV, hyV, hcap⟩, ⟨hrV, hrA⟩, ⟨hyV, hyA⟩⟩
    exact ⟨hyV, hyA, ⟨W.append (.cons hl (.nil ⟨hyV, hyA⟩))⟩⟩
  let Et : Set (Set S) := {e ∈ D.E | (closure e ∩ Rv).Nonempty}
  let En : Set (Set S) := {e ∈ D.E | ¬(closure e ∩ Rv).Nonempty}
  let T₁ : Set S := Rv ∪ ⋃ e ∈ Et, closure e
  let T₂ : Set S := (D.V \ Rv) ∪ ⋃ e ∈ En, closure e
  have hT₁ : IsClosed T₁ := by
    apply IsClosed.union (D.finite_V.subset fun v hv => hv.1).isClosed
    exact (D.finite_edges.subset fun e he => he.1).isClosed_biUnion fun _ _ => isClosed_closure
  have hT₂ : IsClosed T₂ := by
    apply IsClosed.union (D.finite_V.subset sdiff_subset).isClosed
    exact (D.finite_edges.subset fun e he => he.1).isClosed_biUnion fun _ _ => isClosed_closure
  have hcov : A ⊆ T₁ ∪ T₂ := by
    intro x hx
    by_cases h : x ∈ D.V
    · by_cases hR : x ∈ Rv
      · exact .inl (.inl hR)
      · exact .inr (.inl ⟨h, hR⟩)
    · obtain ⟨e, he, hxe⟩ := D.exists_edge_of_mem (hAU hx) h
      by_cases ht : (closure e ∩ Rv).Nonempty
      · exact .inl (.inr (mem_biUnion (x := e) ⟨he, ht⟩ (subset_closure hxe)))
      · exact .inr (.inr (mem_biUnion (x := e) ⟨he, ht⟩ (subset_closure hxe)))
  have hdis : ∀ x ∈ A, x ∈ T₁ → x ∈ T₂ → False := by
    have hvert : ∀ x ∈ Rv, ∀ e ∈ En, x ∉ closure e :=
      fun x hx e he hxe => he.2 ⟨x, hxe, hx⟩
    rintro x hxA (hx | hx) hx₂
    · rcases hx₂ with hx₂ | hx₂
      · exact hx₂.2 hx
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx₂
        exact hvert x hx e he hxe
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      rcases hx₂ with hx₂ | hx₂
      · exact hx₂.2 (hstep e he.1 he.2 x hxe hx₂.1 hxA)
      · obtain ⟨e', he', hxe'⟩ := mem_iUnion₂.mp hx₂
        by_cases hV : x ∈ D.V
        · exact hvert x (hstep e he.1 he.2 x hxe hV hxA) e' he' hxe'
        · have h1 : x ∈ e := (D.closure_diff_V he.1) ▸ ⟨hxe, hV⟩
          have h2 : x ∈ e' := (D.closure_diff_V he'.1) ▸ ⟨hxe', hV⟩
          have heq : e = e' := D.edge_eq_of_mem he.1 he'.1 h1 h2
          exact he'.2 (heq ▸ he.2)
  have hbR : b ∈ Rv := by
    by_contra hne
    have hbT₂ : b ∈ T₂ := .inl ⟨hb, hne⟩
    have haT₁ : a ∈ T₁ := .inl hRa
    obtain ⟨z, hzA, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hA _ _ hT₁ hT₂ hcov
      ⟨a, haA, haT₁⟩ ⟨b, hbA, hbT₂⟩
    exact hdis z hzA hz₁ hz₂
  obtain ⟨W⟩ := hbR.2.2
  obtain ⟨W', hs, -⟩ := GM09.exists_walk_up_of_le
    (Graph.induce_le (show D.V ∩ A ⊆ D.V from inter_subset_left)) W
  refine ⟨W', fun x hx => ?_⟩
  rw [hs] at hx
  exact (W.mem_vertexSet_of_mem_support hx).2

/-- A vertex of the ambient drawing lying in a subdrawing is a vertex of that subdrawing. -/
theorem mem_subdrawing_vertex_of_mem_U {S : Type u} [TopologicalSpace S]
    {D C : Drawing S} (hsub : C.IsSubdrawing D) {x : S}
    (hxU : x ∈ C.U) (hxV : x ∈ D.V) : x ∈ C.V := by
  by_contra hnot
  obtain ⟨e, he, hxe⟩ := C.exists_edge_of_mem hxU hnot
  exact ((hsub.2 he).2.1 hxe).2 hxV

/-- A connected subset of a drawing which meets a subdrawing and leaves it
passes through a vertex of the subdrawing. This locates the ends of radial paths. -/
theorem exists_subdrawing_vertex_of_preconnected {S : Type u} [TopologicalSpace S] [T2Space S]
    {D C : Drawing S} (hsub : C.IsSubdrawing D) {A : Set S}
    (hA : IsPreconnected A) (hAU : A ⊆ D.U) (hmeet : (A ∩ C.U).Nonempty)
    (hleaves : ¬ A ⊆ C.U) : (A ∩ C.V).Nonempty := by
  classical
  let T : Set S := D.V ∪ ⋃ e ∈ D.E \ C.E, closure e
  have hT : IsClosed T := D.finite_V.isClosed.union
    ((D.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)
  have hcov : A ⊆ C.U ∪ T := by
    intro x hx
    by_cases hxV : x ∈ D.V
    · exact Or.inr (Or.inl hxV)
    · obtain ⟨e, he, hxe⟩ := D.exists_edge_of_mem (hAU hx) hxV
      by_cases heC : e ∈ C.E
      · exact Or.inl (heC.2.1 hxe).1
      · exact Or.inr (Or.inr (mem_biUnion ⟨he, heC⟩ (subset_closure hxe)))
  obtain ⟨y, hyA, hyout⟩ : ∃ y ∈ A, y ∉ C.U := by
    by_contra hnone
    apply hleaves
    intro y hy
    by_contra hyout
    exact hnone ⟨y, hy, hyout⟩
  have hyT : y ∈ T := (hcov hyA).resolve_left hyout
  obtain ⟨z, hzA, hzC, hzT⟩ := isPreconnected_closed_iff.mp hA _ _ C.isClosed_U hT hcov
    hmeet ⟨y, hyA, hyT⟩
  refine ⟨z, hzA, ?_⟩
  rcases hzT with hzV | hzE
  · exact mem_subdrawing_vertex_of_mem_U hsub hzC hzV
  · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hzE
    by_cases hzV : z ∈ D.V
    · exact mem_subdrawing_vertex_of_mem_U hsub hzC hzV
    · have hze' : z ∈ e := (D.closure_diff_V he.1) ▸ ⟨hze, hzV⟩
      obtain ⟨e', he', hze''⟩ := C.exists_edge_of_mem hzC (fun hz => hzV (hsub.1 hz))
      have heq : e = e' := D.edge_eq_of_mem he.1 (hsub.2 he') hze' hze''
      exact False.elim (he.2 (heq ▸ he'))

/-- If a nest has at least two circuits, each radial path meets each circuit in a vertex.
The path also meets a distinct, disjoint circuit, so it cannot stay in the first one. -/
theorem DrawingNest.exists_radial_vertex_on_circuit {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) {r s : ℕ} (N : DrawingNest D Δ r s) (hs : 2 ≤ s)
    (p : Fin r) (j : Fin s) : (N.radialPath p ∩ (N.circuit j).U ∩ D.V).Nonempty := by
  let l : Fin s := if j.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hjl : j ≠ l := by
    dsimp only [l]
    split_ifs with hj
    · intro heq
      have := congrArg Fin.val heq
      dsimp at this
      omega
    · intro heq
      exact hj (congrArg Fin.val heq)
  obtain ⟨C, -, hCD, hCU⟩ := GM11.exists_circuit_of_oArc
    (N.circuit j).isOArc_U (N.circuit j).U_sub_drawing
  have hmeet : (N.radialPath p ∩ C.U).Nonempty := hCU ▸ N.radialPath_meets_circuit hΔ p j
  have hleaves : ¬ N.radialPath p ⊆ C.U := by
    intro hsub
    obtain ⟨x, hxp, hxl⟩ := N.radialPath_meets_circuit hΔ p l
    exact Set.disjoint_left.mp (N.pairwise_disjoint_circuits hΔ hjl)
      (hCU ▸ hsub hxp) hxl
  obtain ⟨x, hxp, hxC⟩ := exists_subdrawing_vertex_of_preconnected hCD
    (N.isPreconnected_radialPath p) (N.radialPath_sub_U p) hmeet hleaves
  exact ⟨x, ⟨hxp, hCU ▸ C.V_subset_U hxC⟩, hCD.1 hxC⟩

/-- Replace the radial point sets of a nest by genuine path subdrawings.
For at least two circuits, their ends can be chosen at vertices of the first
and last circuits, and all path vertices stay in the original radial set. -/
theorem DrawingNest.exists_radial_path_drawings {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) {r s : ℕ} (N : DrawingNest D Δ r s) (hs : 2 ≤ s) :
    ∃ (P : Fin r → Drawing S) (a b : Fin r → S),
      (∀ p, (P p).IsSubdrawing D ∧ (P p).IsPathBetween (a p) (b p) ∧
        a p ∈ (N.circuit ⟨0, by omega⟩).U ∧
        b p ∈ (N.circuit ⟨s - 1, by omega⟩).U ∧
        (P p).V ⊆ N.radialPath p) ∧
      Pairwise (fun p q => Disjoint (P p).V (P q).V) := by
  classical
  have hex : ∀ p : Fin r, ∃ (P : Drawing S) (a b : S),
      P.IsSubdrawing D ∧ P.IsPathBetween a b ∧
        a ∈ (N.circuit ⟨0, by omega⟩).U ∧
        b ∈ (N.circuit ⟨s - 1, by omega⟩).U ∧ P.V ⊆ N.radialPath p := by
    intro p
    obtain ⟨a, ⟨hap, haC⟩, haV⟩ := N.exists_radial_vertex_on_circuit hΔ hs p ⟨0, by omega⟩
    obtain ⟨b, ⟨hbp, hbC⟩, hbV⟩ :=
      N.exists_radial_vertex_on_circuit hΔ hs p ⟨s - 1, by omega⟩
    obtain ⟨W, hWsub⟩ := exists_walk_supported_by_preconnected D
      (N.isPreconnected_radialPath p) (N.radialPath_sub_U p) haV hap hbV hbp
    obtain ⟨W', hW', hsub, -⟩ := GM09.exists_isSimple_subwalk W
    refine ⟨GM11.walkDrawing D W', a, b, GM11.walkDrawing_isSubdrawing D W',
      GM11.walkDrawing_isPathBetween D hW', haC, hbC, ?_⟩
    intro x hx
    rw [GM11.walkDrawing_V] at hx
    exact hWsub x (hsub x hx)
  choose P a b hP using hex
  refine ⟨P, a, b, hP, fun p q hpq => ?_⟩
  exact Set.disjoint_left.mpr fun x hxp hxq =>
    Set.disjoint_left.mp (N.pairwise_disjoint_paths hpq)
      ⟨(hP p).2.2.2.2 hxp, (hP p).1.1 hxp⟩
      ⟨(hP q).2.2.2.2 hxq, (hP q).1.1 hxq⟩

/-- Trim the radial paths at a chosen circuit after the first one.
The trimmed paths stay in the closed disc bounded by that circuit, while
all their vertices remain in the original radial sets. This is the path
restriction used inside the sleeve in VIII (9.1), page 270. -/
theorem DrawingNest.exists_radial_paths_inside_circuit {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hman : ∀ x : S, IsManifoldPoint x)
    {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {r s : ℕ} (N : DrawingNest D Δ r s) (j : Fin s) (hj : 0 < j.val) :
    ∃ (P : Fin r → Drawing S) (a b : Fin r → S),
      (∀ p, (P p).IsSubdrawing D ∧ (P p).IsPathBetween (a p) (b p) ∧
        a p ∈ (N.circuit ⟨0, by omega⟩).U ∧ b p ∈ (N.circuit j).U ∧
        (P p).V ⊆ N.radialPath p ∧ (P p).U ⊆ (N.circuit j).ins) ∧
      Pairwise (fun p q => Disjoint (P p).V (P q).V) := by
  classical
  have hs : 2 ≤ s := by have := j.isLt; omega
  obtain ⟨C, -, hCD, hCU⟩ := GM11.exists_circuit_of_oArc
    (N.circuit j).isOArc_U (N.circuit j).U_sub_drawing
  have hB : IsClosedDisc (N.circuit j).ins := (N.circuit j).isInside.2.1
  have hbd : discBd (N.circuit j).ins = C.U := (N.circuit j).isInside.2.2.1.trans hCU.symm
  have hex : ∀ p : Fin r, ∃ (P : Drawing S) (a b : S),
      P.IsSubdrawing D ∧ P.IsPathBetween a b ∧
        a ∈ (N.circuit ⟨0, by omega⟩).U ∧ b ∈ (N.circuit j).U ∧
        P.V ⊆ N.radialPath p ∧ P.U ⊆ (N.circuit j).ins := by
    intro p
    obtain ⟨a, ⟨hap, haC⟩, haV⟩ := N.exists_radial_vertex_on_circuit hΔ hs p ⟨0, by omega⟩
    obtain ⟨b, ⟨hbp, hbC⟩, hbV⟩ := N.exists_radial_vertex_on_circuit hΔ hs p j
    have hbCV : b ∈ C.V := mem_subdrawing_vertex_of_mem_U hCD (hCU ▸ hbC) hbV
    obtain ⟨W, hWsub⟩ := exists_walk_supported_by_preconnected D
      (N.isPreconnected_radialPath p) (N.radialPath_sub_U p) haV hap hbV hbp
    obtain ⟨c, hc, W₁, hsub₁, hfirst⟩ := exists_walk_first_mem W hbCV
    obtain ⟨W₂, hsimple, hsub₂, -⟩ := GM09.exists_isSimple_subwalk W₁
    have hoff : ∀ x ∈ W₂.support, x ≠ c → x ∉ C.V := by
      intro x hx hxc hxC
      exact hxc (hfirst x (hsub₂ x hx) hxC)
    have haint : a ∈ discInt (N.circuit j).ins :=
      (insideOArc_iff_mem_discInt hΔ (N.circuit j).isInside).mp
        (N.inside_of_lt (Fin.lt_def.mpr hj) a haC)
    have hside := GM07.walk_U_stays_side hCD continuous_id Function.injective_id
      (hB.isOpen_discInt hman) hB.isClosed.isOpen_compl
      (Set.disjoint_left.mpr (fun _ hx hy => hy hx.1))
      (fun x hx => by
        by_cases hxB : x ∈ (N.circuit j).ins
        · exact Or.inl ⟨hxB, hbd ▸ hx⟩
        · exact Or.inr hxB)
      (fun _ hx hxC => hx.2 (hbd ▸ hxC)) W₂ hsimple hoff haint
    refine ⟨GM11.walkDrawing D W₂, a, c, GM11.walkDrawing_isSubdrawing D W₂,
      GM11.walkDrawing_isPathBetween D hsimple, haC, hCU ▸ C.V_subset_U hc, ?_, ?_⟩
    · intro x hx
      rw [GM11.walkDrawing_V] at hx
      exact hWsub x (hsub₁ x (hsub₂ x hx))
    · intro x hx
      rcases hside x hx with rfl | hxint
      · exact discBd_subset _ (hbd ▸ C.V_subset_U hc)
      · exact hxint.1
  choose P a b hP using hex
  refine ⟨P, a, b, hP, fun p q hpq => ?_⟩
  exact Set.disjoint_left.mpr fun x hxp hxq =>
    Set.disjoint_left.mp (N.pairwise_disjoint_paths hpq)
      ⟨(hP p).2.2.2.2.1 hxp, (hP p).1.1 hxp⟩
      ⟨(hP q).2.2.2.2.1 hxq, (hP q).1.1 hxq⟩

end GraphMinor.GM08
