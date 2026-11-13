module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4Disc
import GraphMinor.GM06.Section4Routed
import GraphMinor.GM07.Section3
import GraphMinor.GM11.Walks

/-!
# A boundary segment meets a proper path only at its ends

Graph Minors VI (4.1), page 124, uses a segment whose ends are consecutive
boundary vertices. A connected set dense in an injective arc contains every
point of that arc except possibly its ends. Thus the closure of the segment
cannot contain any further boundary vertex. A proper path and the segment
therefore meet only at the ends, as needed for the enclosing-disc construction.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

/-- A connected set whose closure is an injective arc contains its whole
interior. This gives the endpoint property for the segment in Graph Minors VI
(4.1), page 124. -/
theorem closure_arc_subset_of_isPreconnected
    {S : Type u} [TopologicalSpace S] [T2Space S] {A : Set S}
    (hA : IsPreconnected A) (f : Curve S) (hf : f.IsLine)
    (hrange : range f = closure A) : closure A ⊆ A ∪ {f 0, f 1} := by
  have hsub : A ⊆ range f := by rw [hrange]; exact subset_closure
  have hpre : IsPreconnected (f ⁻¹' A) :=
    hA.preimage_of_isClosedMap hf f.continuous.isClosedMap hsub
  intro x hx
  obtain ⟨t, rfl⟩ := hrange.symm ▸ hx
  by_cases htA : f t ∈ A
  · exact Or.inl htA
  have hne : ∀ q ∈ f ⁻¹' A, id q ≠ t := by
    intro q hq hqt
    exact htA (hqt ▸ hq)
  rcases hpre.mapsTo_Ioi_or_Iio continuous_id.continuousOn hne with hupper | hlower
  · have hcover : A ⊆ f '' Ici t := by
      intro y hy
      obtain ⟨q, rfl⟩ := hsub hy
      exact ⟨q, (hupper hy).le, rfl⟩
    have hcl : closure A ⊆ f '' Ici t :=
      closure_minimal hcover ((isClosed_Ici.isCompact).image f.continuous).isClosed
    have hf0 : f 0 ∈ closure A := hrange ▸ mem_range_self 0
    obtain ⟨q, hq, heq⟩ := hcl hf0
    have hq0 : q = 0 := hf heq
    have ht0 : t = 0 := le_antisymm (hq0 ▸ hq) (show (0 : unitInterval) ≤ t from t.property.1)
    exact Or.inr (Or.inl (congrArg f ht0))
  · have hcover : A ⊆ f '' Iic t := by
      intro y hy
      obtain ⟨q, rfl⟩ := hsub hy
      exact ⟨q, (hlower hy).le, rfl⟩
    have hcl : closure A ⊆ f '' Iic t :=
      closure_minimal hcover ((isClosed_Iic.isCompact).image f.continuous).isClosed
    have hf1 : f 1 ∈ closure A := hrange ▸ mem_range_self 1
    obtain ⟨q, hq, heq⟩ := hcl hf1
    have hq1 : q = 1 := hf heq
    have ht1 : t = 1 := le_antisymm (show t ≤ (1 : unitInterval) from t.property.2) (hq1 ▸ hq)
    exact Or.inr (Or.inr (congrArg f ht1))

/-- In the setting of Graph Minors VI (4.1), page 124, a proper path and the
closure of a boundary segment meet only at the two specified ends. -/
theorem path_inter_segment_closure_subset_ends
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {G P : Drawing S} {s t : S} {A : Set S}
    (hG : G.IsProper) (hPG : P.IsSubdrawing G)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hPA : PathHomotopicToArc P s t A) : P.U ∩ closure A ⊆ {s, t} := by
  have hsub : A ⊆ bd S \ (G.V ∩ bd S) := by
    obtain ⟨x, hx, heq⟩ := hseg.1
    rw [← heq]
    exact connectedComponentIn_subset _ x
  have hconn : IsPreconnected A := by
    obtain ⟨x, hx, heq⟩ := hseg.1
    rw [← heq]
    exact isPreconnected_connectedComponentIn
  have hcl : closure A ⊆ bd S :=
    closure_minimal (hsub.trans sdiff_subset) (Surface.isClosed_bd S)
  obtain ⟨_, g, _, hg, _⟩ := hPA
  have hends := closure_arc_subset_of_isPreconnected hconn g hg.1 hg.2.1
  rw [hg.2.2.1, hg.2.2.2] at hends
  intro x hx
  have hxbd := hcl hx.2
  have hxV : x ∈ G.V := hG ⟨hxbd, hPG.U_subset hx.1⟩
  rcases hends hx.2 with hxA | hxends
  · exact False.elim ((hsub hxA).2 ⟨hxV, hxbd⟩)
  · exact hxends

/-- The portion enclosed by a path in the homotopy class of a boundary segment
exists in the setting of Graph Minors VI, Section 4, page 124. -/
theorem exists_enclosedDisc_of_segment_path
    {S : Type u} [TopologicalSpace S] {G P : Drawing S} {s t : S} {A : Set S}
    (hS : IsSurface S) (hG : G.IsProper) (hPG : P.IsSubdrawing G)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hPA : PathHomotopicToArc P s t A) : ∃ Δ : Set S, IsEnclosedDisc P A Δ := by
  let : T2Space S := hS.2.1
  exact exists_enclosedDisc_of_pathHomotopicToArc hS hPA
    (path_inter_segment_closure_subset_ends hG hPG hseg hPA)

/-- The starting path and enclosed portion for the proof of Graph Minors VI
(4.1), page 124, obtained from a hypothetical feasible routed forest. -/
theorem exists_enclosed_subpath_of_hasHomotopicForestSubgraph
    {S : Type u} [TopologicalSpace S] {G H Hst : Drawing S} {s t : S} {A : Set S}
    (hS : IsSurface S) (hG : G.IsProper) (hbd : H.V ∩ bd S = G.V ∩ bd S)
    (hseg : IsSegmentOf (bd S) (H.V ∩ bd S) A)
    (hfeas : HasHomotopicForestSubgraph G H)
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hne : s ≠ t)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A) :
    ∃ (P : Drawing S) (Δ : Set S), IsSubpathOf G P s t ∧
      PathHomotopicToArc P s t A ∧ IsEnclosedDisc P A Δ := by
  let : T2Space S := hS.2.1
  obtain ⟨P, hP, hPA⟩ :=
    exists_subpath_homotopicToArc_of_hasHomotopicForestSubgraph hfeas hs ht hne hHst hHA
  have hsegG : IsSegmentOf (bd S) (G.V ∩ bd S) A := by rw [← hbd]; exact hseg
  obtain ⟨Δ, hΔ⟩ := exists_enclosedDisc_of_segment_path hS hG hP.1 hsegG hPA
  exact ⟨P, Δ, hP, hPA, hΔ⟩

end GraphMinor.GM06
