module

public import GraphMinor.GM05.FiniteArcUnionDrawing

/-!
# Planarizing an arc family with every crossing marked

For GM V, (8.14), mark all endpoints and every pairwise crossing
before inserting the arcs. This adds only finitely many points and
changes no support point. Extra prescribed points include the centres
of isolated stars. Every crossing is then a vertex of the union drawing.
-/

public section
namespace GraphMinor.GM05
open Set Surface

/-- The planarized finite union in GM V, (8.14), page 113, with all
endpoints and pairwise crossings explicitly among the vertices. -/
theorem exists_marked_arc_union_drawing {S : Type} [TopologicalSpace S] [T2Space S]
    {A : Set (unitInterval → S)} (hA : A.Finite) (ha : ∀ f ∈ A, IsArcMap f)
    (hmeet : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → (range f ∩ range g).Finite)
    {Z₀ : Set S} (hZ₀ : Z₀.Finite) :
    ∃ D : Drawing S, D.U = Z₀ ∪ ⋃ f ∈ A, range f ∧ Z₀ ⊆ D.V ∧
      (∀ f ∈ A, f 0 ∈ D.V ∧ f 1 ∈ D.V) ∧
      ∀ f ∈ A, ∀ g ∈ A, f ≠ g → range f ∩ range g ⊆ D.V := by
  classical
  let : Fintype A := hA.fintype
  let a : A → unitInterval → S := fun f ↦ f.val
  let X : Set S := ⋃ f : A, ⋃ g : A, if f = g then ∅ else range f.val ∩ range g.val
  have hX : X.Finite := by
    refine finite_iUnion fun f ↦ finite_iUnion fun g ↦ ?_
    split_ifs with hfg
    · exact finite_empty
    · exact hmeet f.val f.prop g.val g.prop (fun he ↦ hfg (Subtype.ext he))
  let Z := ((Z₀ ∪ range (fun f : A ↦ f.val 0)) ∪ range (fun f : A ↦ f.val 1)) ∪ X
  have hZ : Z.Finite := ((hZ₀.union (finite_range _)).union (finite_range _)).union hX
  have h0 : ∀ f, a f 0 ∈ Z := fun f ↦ .inl (.inl (.inr ⟨f,rfl⟩))
  have h1 : ∀ f, a f 1 ∈ Z := fun f ↦ .inl (.inr ⟨f,rfl⟩)
  have hZ₀Z : Z₀ ⊆ Z := fun x hx ↦ .inl (.inl (.inl hx))
  have hcross : ∀ f : A, ∀ g : A, f ≠ g → range f.val ∩ range g.val ⊆ Z := by
    intro f g hfg x hx
    exact .inr (mem_iUnion₂.mpr ⟨f,g,by simpa [hfg] using hx⟩)
  have hZU : Z ⊆ Z₀ ∪ ⋃ f ∈ A, range f := by
    rintro x (((hx | ⟨f,rfl⟩) | ⟨f,rfl⟩) | hx)
    · exact .inl hx
    · exact .inr (mem_iUnion₂.mpr ⟨f.val,f.prop,mem_range_self 0⟩)
    · exact .inr (mem_iUnion₂.mpr ⟨f.val,f.prop,mem_range_self 1⟩)
    · obtain ⟨f,g,hx⟩ := mem_iUnion₂.mp hx
      split_ifs at hx with hfg
      · exact hx.elim
      · exact .inr (mem_iUnion₂.mpr ⟨f.val,f.prop,hx.1⟩)
  obtain ⟨D,hDU,hZV⟩ := exists_drawing_of_finite_crossing_arcs a
    (fun f ↦ ha f.val f.prop) hZ h0 h1
    (fun f g hfg ↦ hmeet f.val f.prop g.val g.prop (fun he ↦ hfg (Subtype.ext he)))
  have hDU' : D.U = Z ∪ ⋃ f ∈ A, range f := by simpa only [a,iUnion_subtype] using hDU
  refine ⟨D,?_,hZ₀Z.trans hZV,?_,?_⟩
  · rw [hDU']
    exact subset_antisymm (union_subset hZU subset_union_right)
      (union_subset (hZ₀Z.trans subset_union_left) subset_union_right)
  · intro f hf
    exact ⟨hZV (h0 ⟨f,hf⟩),hZV (h1 ⟨f,hf⟩)⟩
  · intro f hf g hg hfg
    exact (hcross ⟨f,hf⟩ ⟨g,hg⟩ (fun he ↦ hfg (congrArg Subtype.val he))).trans hZV

end GraphMinor.GM05
