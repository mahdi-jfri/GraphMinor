module

public import GraphMinor.GM07.Defs
public import GraphMinor.GM19.CutDrawing2
import GraphMinor.GM19.CutTwo
import GraphMinor.Surface.CutLoop

/-!
# Circle and line frames of schisms

Each of the six schism shapes is a finite union of circles and joining
lines. Adding the cuffs gives the frame used in the cutting construction
for VIII (18.2). The frame is independent of the graph subdivision.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u

private theorem frame_of_circles_and_lines {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {𝓞 𝓛 : Set (Set S)} (hO : 𝓞.Finite) (hL : 𝓛.Finite)
    (hcircles : ∀ C ∈ 𝓞, IsOArc C)
    (hlines : ∀ P ∈ 𝓛, ∃ a b, a ≠ b ∧ IsLineWithEnds P a b ∧
      a ∈ bd S ∪ ⋃₀ 𝓞 ∧ b ∈ bd S ∪ ⋃₀ 𝓞) :
    GM19.IsCutFrame S (cuffs S ∪ 𝓞) 𝓛 := by
  have hc := cuff_statement S hS
  refine ⟨hc.2.1.union hO, hL, ?_, subset_union_left, ?_⟩
  · rintro C (hC | hC)
    · exact hc.2.2 C hC
    · exact hcircles C hC
  · intro P hP
    rw [sUnion_union, sUnion_cuffs]
    exact hlines P hP

private theorem frame_of_proper_arc {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {F : Set S} (hF : IsProperIArc F) :
    ∃ 𝓐 𝓛, GM19.IsCutFrame S 𝓐 𝓛 ∧ bd S ∪ F = ⋃₀ 𝓐 ∪ ⋃₀ 𝓛 := by
  have : T2Space S := hS.2.1
  obtain ⟨a, b, hab, hbd, hl⟩ := hF
  have ha : a ∈ bd S := (hbd.symm.subset (mem_insert a {b})).2
  have hb : b ∈ bd S := (hbd.symm.subset (mem_insert_of_mem a (mem_singleton b))).2
  refine ⟨cuffs S ∪ ∅, {F}, frame_of_circles_and_lines hS finite_empty (finite_singleton F)
    (fun _ h => h.elim) ?_, ?_⟩
  · rintro L rfl
    exact ⟨a, b, hab, hl, Or.inl ha, Or.inl hb⟩
  · rw [union_empty, sUnion_cuffs, sUnion_singleton]

/-- Every schism in VIII Section 18, page 285, has a finite circle and
line frame. This records the geometric input to its graph cut without
choosing auxiliary subdivision vertices. -/
theorem exists_cutFrame_of_schism {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {F : Set S} (hF : GM07.IsSchism F) :
    ∃ 𝓐 𝓛, GM19.IsCutFrame S 𝓐 𝓛 ∧ bd S ∪ F = ⋃₀ 𝓐 ∪ ⋃₀ 𝓛 := by
  have : T2Space S := hS.2.1
  rcases hF with hi | hii | hiii | hiv | hv | hvi
  · refine ⟨cuffs S ∪ {F}, ∅, frame_of_circles_and_lines hS (finite_singleton F) finite_empty
      (by rintro C rfl; exact hi.1) (fun _ h => h.elim), ?_⟩
    rw [sUnion_union, sUnion_cuffs, sUnion_singleton, sUnion_empty, union_empty]
  · exact frame_of_proper_arc hS hii.1
  · exact frame_of_proper_arc hS hiii.1
  · rcases hiv.1 with hbar | hwedge
    · obtain ⟨A, B, P, a, b, hA, hB, hAB, hP, ha, hb, _, _, rfl⟩ := hbar
      refine ⟨cuffs S ∪ {A, B}, {P}, frame_of_circles_and_lines hS
        ((finite_singleton B).insert A) (finite_singleton P) ?_ ?_, ?_⟩
      · rintro D (rfl | rfl)
        · exact hA
        · exact hB
      · rintro L rfl
        exact ⟨a, b, (fun heq => disjoint_left.mp hAB ha (heq ▸ hb)), hP, Or.inr ⟨A, Or.inl rfl, ha⟩,
          Or.inr ⟨B, Or.inr rfl, hb⟩⟩
      · rw [sUnion_union, sUnion_cuffs, sUnion_pair, sUnion_singleton]
        ac_rfl
    · obtain ⟨A, B, a, hA, hB, _, rfl⟩ := hwedge
      refine ⟨cuffs S ∪ {A, B}, ∅, frame_of_circles_and_lines hS
        ((finite_singleton B).insert A) finite_empty ?_ (fun _ h => h.elim), ?_⟩
      · rintro D (rfl | rfl)
        · exact hA
        · exact hB
      · rw [sUnion_union, sUnion_cuffs, sUnion_pair, sUnion_empty, union_empty]
  · obtain ⟨P, Q, R, a, b, hab, hP, hQ, hR, hPQ, hPR, _, rfl⟩ := hv.1
    refine ⟨cuffs S ∪ {P ∪ Q, P ∪ R}, ∅, frame_of_circles_and_lines hS
      ((finite_singleton (P ∪ R)).insert (P ∪ Q)) finite_empty ?_ (fun _ h => h.elim), ?_⟩
    · rintro D (rfl | rfl)
      · exact oArc_of_lines hP hQ hPQ
      · exact oArc_of_lines hP hR hPR
    · rw [sUnion_union, sUnion_cuffs, sUnion_pair, sUnion_empty, union_empty]
      simp only [union_assoc, union_left_comm, union_comm]
      rw [← union_assoc P P, union_self]
  · obtain ⟨b, A, P, C, D, a, hA, hP, hab, hPA, rfl, hC, _, _, hb, _, _⟩ := hvi
    have ha : a ∈ A := by
      exact (hPA.symm.subset (mem_singleton a)).2
    refine ⟨cuffs S ∪ {A}, {P}, frame_of_circles_and_lines hS
      (finite_singleton A) (finite_singleton P) ?_ ?_, ?_⟩
    · rintro E rfl
      exact hA
    · rintro L rfl
      exact ⟨a, b, hab, hP, Or.inr ⟨A, rfl, ha⟩,
        Or.inl (by
          obtain ⟨z, hz, rfl⟩ := hC
          exact connectedComponentIn_subset _ _ hb)⟩
    · rw [sUnion_union, sUnion_cuffs, sUnion_singleton, sUnion_singleton]
      ac_rfl

end GraphMinor.GM08
