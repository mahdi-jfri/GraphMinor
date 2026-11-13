module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section12Foundation
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.GM08.Section9Paths
import GraphMinor.GM08.Section9Truncation
import GraphMinor.GM08.Section8Sleeve
import GraphMinor.GM08.Section6
import GraphMinor.Surface.DiscMerge
import GraphMinor.Surface.Disc
import GraphMinor.GM06.DiscRegions

/-!
# Constructing the truncation used in VIII, Section 12

Choose a sleeve for each foundation ring by (8.1) and (8.2). Keep all
vertices and edges outside the rings and add the chosen sleeves. An
outside edge has no endpoint inside a ring because it cannot cross a
normal ring. Thus these prescribed vertices and edges form a subdrawing,
the truncation defined on page 269.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

private theorem closure_edge_not_inside {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {F : Set S} (hS : IsClosedDisc (univ : Set S))
    (hF : IsOArc F) (hn : D.IsNormal F) {e : Set S} (he : e ∈ D.E)
    (hout : ¬ SetInsideOArc univ F e) :
    ∀ x ∈ closure e, ¬ InsideOArc univ F x := by
  have hman := (isSurface_of_closedDisc_univ hS).2.2
  obtain ⟨B, hB, -⟩ := disc_oArc univ F hS (subset_univ _) hF
  have hdis := (edge_inside_or_disjoint_normal_ring hS (subset_univ _) (subset_univ _) hF hn he).resolve_left hout
  have hcl : closure e ⊆ (discInt B)ᶜ := closure_minimal
    (fun x hx hin => disjoint_left.mp hdis hx ((insideOArc_iff_mem_discInt hS hB).mpr hin))
    (hB.2.1.isOpen_discInt hman).isClosed_compl
  exact fun x hx hin => hcl hx ((insideOArc_iff_mem_discInt hS hB).mp hin)

/-- Every foundation induces a truncation, by the sleeve construction
on VIII, page 269. Section 12 applies (9.4) and (11.1) to this drawing. -/
theorem exists_truncation_induced_by {S : Type u} [TopologicalSpace S]
    {D : Drawing S} (hS : IsClosedDisc (univ : Set S)) (hprop : D.IsProper)
    {t : ℕ} {F : Fin t → Set S} (hFound : IsFoundation D univ F) :
    ∃ Dstar : Drawing S, IsTruncationInducedBy D univ F Dstar := by
  classical
  have hbd : D.IsNormal (discBd (univ : Set S)) := by rw [GM06.discBd_univ]; exact hprop
  have hFound' := hFound
  obtain ⟨C, hC, _, _, hF, _, _, _⟩ := hFound
  have hex : ∀ i, ∃ P : Drawing S, IsSleeve D univ (F i) P := fun i =>
    exists_isSleeve hS (subset_univ _) (theorem_8_2_proof hS (subset_univ _) hbd (hC i) (hF i).1)
  choose P hP using hex
  have hPD : ∀ i, (P i).IsSubdrawing D := fun i => (hP i).2.2.2.1
  let V' : Set S := {v ∈ D.V | ∀ i, ¬ InsideOArc univ (F i) v} ∪ ⋃ i, (P i).V
  let E' : Set (Set S) := {e ∈ D.E | ∀ i, ¬ SetInsideOArc univ (F i) e} ∪ ⋃ i, (P i).E
  have hV : V' ⊆ D.V := by
    rintro x (hx | hx)
    · exact hx.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact (hPD i).1 hi
  have hE : E' ⊆ D.E := by
    rintro e (he | he)
    · exact he.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp he
      exact (hPD i).2 hi
  have hcl : ∀ e ∈ E', closure e ∩ D.V ⊆ V' := by
    rintro e (he | he) x hx
    · exact .inl ⟨hx.2, fun i => closure_edge_not_inside hS (hF i).1.2.1
        (hF i).1.2.2.1 he.1 (he.2 i) x hx.1⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp he
      apply Or.inr
      apply mem_iUnion.mpr
      refine ⟨i, mem_subdrawing_vertex_of_mem_U (hPD i) ?_ hx.2⟩
      exact closure_minimal (fun y hy => (hi.2.1 hy).1) (P i).isClosed_U hx.1
  obtain ⟨Dstar, hsub, hDV, hDE⟩ := exists_span_subdrawing_in_disc hS (subset_univ _) hV hE hcl
  exact ⟨Dstar, hFound', hsub, P, hP, hDV, hDE⟩

/-- Every proper drawing in a disc has a truncation. This is the
existence used when applying (9.4) in VIII, Section 12, page 274. -/
theorem exists_truncation {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S) (hprop : D.IsProper) :
    ∃ Dstar : Drawing S, IsTruncation D univ Dstar := by
  obtain ⟨t, F, hF⟩ := exists_foundation hS D hprop
  obtain ⟨Dstar, hD⟩ := exists_truncation_induced_by hS hprop hF
  exact ⟨Dstar, t, F, hD⟩

end GraphMinor.GM08
