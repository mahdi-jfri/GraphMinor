module

public import GraphMinor.Surface.TopologyStatements
public import Mathlib.Topology.Constructions.SumProd
import GraphMinor.Surface.CutComp
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Joining complementary open surfaces

For the separating case of Graph Minors V, (8.10), the interiors of
the two cut components form the interior of the whole cut surface.
After capping separately, the complements of the two caps form the
complement of their images in the topological sum. The maps here are
the inclusions on each summand.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u v

/-- The complement of one closed set in each summand is the sum of
the two complements, by the two summand inclusions. -/
theorem sum_complement_homeomorph {S : Type u} [TopologicalSpace S]
    {T : Type v} [TopologicalSpace T] {D : Set S} {E : Set T}
    (hD : IsClosed D) (hE : IsClosed E) :
    Nonempty ((↥(Dᶜ) ⊕ ↥(Eᶜ)) ≃ₜ ↥((Sum.inl '' D ∪ Sum.inr '' E)ᶜ)) := by
  let f : ↥(Dᶜ) ⊕ ↥(Eᶜ) → S ⊕ T :=
    Sum.elim (fun x ↦ Sum.inl x.1) (fun y ↦ Sum.inr y.1)
  have hi : Function.Injective f := by
    rintro (x|x) (y|y) he
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj he))
    · simp [f] at he
    · simp [f] at he
    · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj he))
  have hf : IsOpenEmbedding f :=
    (IsOpenEmbedding.inl.comp hD.isOpen_compl.isOpenEmbedding_subtypeVal).sumElim
      (IsOpenEmbedding.inr.comp hE.isOpen_compl.isOpenEmbedding_subtypeVal) hi
  have he : range f=(Sum.inl '' D ∪ Sum.inr '' E)ᶜ := by
    ext x
    cases x <;> simp [f]
  exact ⟨hf.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr he)⟩

/-- The interiors of the two disjoint clopen components form the
interior of their union. The homeomorphism is given by inclusion on
both summands. -/
theorem component_interiors_homeomorph {Y : Type u} [TopologicalSpace Y]
    (hY : IsSurface Y) {W₁ W₂ : Set Y} (hW₁ : IsClopen W₁) (hW₂ : IsClopen W₂)
    (hd : Disjoint W₁ W₂) (hu : W₁ ∪ W₂=univ) :
    Nonempty ((↥((bd W₁)ᶜ) ⊕ ↥((bd W₂)ᶜ)) ≃ₜ ↥((bd Y)ᶜ)) := by
  let f : ↥((bd W₁)ᶜ) ⊕ ↥((bd W₂)ᶜ) → Y :=
    Sum.elim (fun x ↦ x.1.1) (fun y ↦ y.1.1)
  have h₁ : IsOpen ((bd W₁)ᶜ) := (cuff_statement W₁ (isSurface_sub hY hW₁)).1.isOpen_compl
  have h₂ : IsOpen ((bd W₂)ᶜ) := (cuff_statement W₂ (isSurface_sub hY hW₂)).1.isOpen_compl
  have hi : Function.Injective f := by
    rintro (x|x) (y|y) he
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext he))
    · change x.1.1=y.1.1 at he
      exact (Set.disjoint_left.mp hd x.1.2 (he.symm ▸ y.1.2)).elim
    · change x.1.1=y.1.1 at he
      exact (Set.disjoint_left.mp hd y.1.2 (he ▸ x.1.2)).elim
    · exact congrArg Sum.inr (Subtype.ext (Subtype.ext he))
  have hf : IsOpenEmbedding f :=
    (hW₁.2.isOpenEmbedding_subtypeVal.comp h₁.isOpenEmbedding_subtypeVal).sumElim
      (hW₂.2.isOpenEmbedding_subtypeVal.comp h₂.isOpenEmbedding_subtypeVal) hi
  have he : range f=(bd Y)ᶜ := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      cases x with
      | inl x => exact fun hb ↦ x.2 ((mem_bd_sub hW₁.2).mpr hb)
      | inr x => exact fun hb ↦ x.2 ((mem_bd_sub hW₂.2).mpr hb)
    · intro hy
      rcases (hu ▸ mem_univ y : y ∈ W₁ ∪ W₂) with hy₁|hy₂
      · exact ⟨Sum.inl ⟨⟨y,hy₁⟩,fun hb ↦ hy ((mem_bd_sub hW₁.2).mp hb)⟩,rfl⟩
      · exact ⟨Sum.inr ⟨⟨y,hy₂⟩,fun hb ↦ hy ((mem_bd_sub hW₂.2).mp hb)⟩,rfl⟩
  exact ⟨hf.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr he)⟩

/-- If the other summand has no removed set, keep that whole summand
in the complement homeomorphism. -/
theorem sum_complement_empty_right {S : Type u} [TopologicalSpace S]
    {T : Type v} [TopologicalSpace T] {D : Set S} (hD : IsClosed D) :
    Nonempty ((↥(Dᶜ) ⊕ T) ≃ₜ ↥((Sum.inl '' D : Set (S ⊕ T))ᶜ)) := by
  obtain ⟨e⟩ := sum_complement_homeomorph (T := T) hD isClosed_empty
  let eT : ↥((∅ : Set T)ᶜ) ≃ₜ T :=
    (Homeomorph.setCongr (compl_empty : (∅ : Set T)ᶜ=univ)).trans (Homeomorph.Set.univ T)
  have he : (Sum.inl '' D ∪ Sum.inr '' (∅ : Set T) : Set (S ⊕ T))ᶜ=(Sum.inl '' D)ᶜ := by
    rw [image_empty,union_empty]
  exact ⟨(Homeomorph.sumCongr (Homeomorph.refl _) eT.symm).trans
    (e.trans (Homeomorph.setCongr he))⟩

end GraphMinor.GM05
