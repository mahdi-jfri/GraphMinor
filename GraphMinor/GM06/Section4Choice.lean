module

public import GraphMinor.GM06.Defs
import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section4UniqueDisc
import GraphMinor.Surface.DiscArcs
import Mathlib.Order.Preorder.Finite

/-!
# Choosing an enclosed path with no smaller enclosed disc

Graph Minors VI, Section 4, page 124, chooses a path enclosing a minimal
portion of the surface. Inside a fixed candidate disc there are only finitely
many candidate discs: there are finitely many subdrawings, and a boundary
circle determines at most one closed disc inside the fixed disc. Thus a
candidate exists with no strictly smaller candidate below it.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u

private theorem finite_subdrawings {S : Type u} [TopologicalSpace S] (G : Drawing S) :
    {P : Drawing S | P.IsSubdrawing G}.Finite := by
  have hfin := G.finite_V.finite_subsets.prod G.finite_edges.finite_subsets
  refine Set.Finite.of_finite_image (f := fun P : Drawing S => (P.V, P.E))
    (hfin.subset ?_) ?_
  · rintro _ ⟨P, hP, rfl⟩
    exact hP
  · intro P hP Q hQ heq
    exact Drawing.ext_of_V_E (congrArg Prod.fst heq) (congrArg Prod.snd heq)

private theorem finite_enclosed_discs_below
    {S : Type u} [TopologicalSpace S] (G : Drawing S) (s t : S) (A D₀ : Set S)
    (hD₀ : IsClosedDisc D₀) :
    {D : Set S | D ⊆ D₀ ∧ ∃ P : Drawing S,
      IsSubpathOf G P s t ∧ PathHomotopicToArc P s t A ∧ IsEnclosedDisc P A D}.Finite := by
  have hfin := (finite_subdrawings G).image (fun P => P.U ∪ closure A)
  refine Set.Finite.of_finite_image (f := fun D : Set S => discBd D)
    (hfin.subset ?_) ?_
  · rintro _ ⟨D, hD, rfl⟩
    obtain ⟨P, hP, _, hPD⟩ := hD.2
    exact ⟨P, hP.1, hPD.2.2.symm⟩
  · intro D hD E hE heq
    obtain ⟨P, _, _, hPD⟩ := hD.2
    obtain ⟨Q, _, _, hQE⟩ := hE.2
    obtain ⟨K, _, huniq⟩ := disc_oArc D₀ (discBd D) hD₀
      ((discBd_subset D).trans hD.1) hPD.1.isOArc_discBd
    exact (huniq D hD.1 hPD.1 rfl).trans (huniq E hE.1 hQE.1 heq.symm).symm

/-- The finite choice in the definition of the minimal path in Graph Minors VI,
Section 4, page 124: below any candidate enclosed disc there is a candidate
with no strictly smaller enclosed disc below it. -/
theorem exists_inclusion_minimal_enclosed_subpath
    {S : Type u} [TopologicalSpace S] {G P₀ : Drawing S} {s t : S} {A D₀ : Set S}
    (hP₀ : IsSubpathOf G P₀ s t) (hPA₀ : PathHomotopicToArc P₀ s t A)
    (hD₀ : IsEnclosedDisc P₀ A D₀) :
    ∃ (P : Drawing S) (D : Set S), IsSubpathOf G P s t ∧
      PathHomotopicToArc P s t A ∧ IsEnclosedDisc P A D ∧ D ⊆ D₀ ∧
      ∀ (Q : Drawing S) (E : Set S), IsSubpathOf G Q s t →
        PathHomotopicToArc Q s t A → IsEnclosedDisc Q A E → E ⊆ D → D ⊆ E := by
  let C : Set (Set S) := {D | D ⊆ D₀ ∧ ∃ P : Drawing S,
    IsSubpathOf G P s t ∧ PathHomotopicToArc P s t A ∧ IsEnclosedDisc P A D}
  have hfin : C.Finite := finite_enclosed_discs_below G s t A D₀ hD₀.1
  have hne : C.Nonempty := ⟨D₀, subset_rfl, P₀, hP₀, hPA₀, hD₀⟩
  obtain ⟨D, hD⟩ := hfin.exists_minimal hne
  obtain ⟨P, hP, hPA, hPD⟩ := hD.1.2
  refine ⟨P, D, hP, hPA, hPD, hD.1.1, ?_⟩
  intro Q E hQ hQA hQE hED
  exact hD.2 ⟨hED.trans hD.1.1, Q, hQ, hQA, hQE⟩ hED

/-- There are only finitely many enclosed path discs for fixed ends and a fixed
boundary segment in Graph Minors VI, Section 4, page 124. The boundary meets
`bd(S)` at the first end, so each path has only one enclosed disc. -/
theorem finite_enclosed_subpath_discs
    {S : Type u} [TopologicalSpace S] (G : Drawing S) (s t : S) (A : Set S)
    (hS : IsSurface S) (hs : s ∈ bd S) :
    {D : Set S | ∃ P : Drawing S, IsSubpathOf G P s t ∧
      PathHomotopicToArc P s t A ∧ IsEnclosedDisc P A D}.Finite := by
  have hfin := (finite_subdrawings G).image (fun P => P.U ∪ closure A)
  refine Set.Finite.of_finite_image (f := fun D : Set S => discBd D)
    (hfin.subset ?_) ?_
  · rintro _ ⟨D, hD, rfl⟩
    obtain ⟨P, hP, _, hPD⟩ := hD
    exact ⟨P, hP.1, hPD.2.2.symm⟩
  · intro D hD E hE heq
    obtain ⟨P, hP, _, hPD⟩ := hD
    obtain ⟨Q, _, _, hQE⟩ := hE
    obtain ⟨f, hf⟩ := hP.2.2.2
    have hsD : s ∈ discBd D := by
      rw [hPD.2.2, ← hf.2.1]
      exact Or.inl ⟨0, hf.2.2.1⟩
    exact disc_eq_of_discBd_eq_of_mem_bd hS hPD.1 hQE.1 heq hsD hs

end GraphMinor.GM06
