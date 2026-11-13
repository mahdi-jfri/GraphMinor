module

public import GraphMinor.Surface.TopologyStatements
public import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Separating one surface component from the others

For the disconnected case of GM V, (8.10), an open-and-closed part and
its complement form a topological sum. If the circle lies in that
part, removing the circle leaves its complement there together with
the whole other part. The homeomorphisms below are the inclusions on
both summands.
-/

public section

namespace GraphMinor.GM05

open Set Topology

universe u

/-- An open-and-closed set and its complement form the original space,
with the two inclusion maps as the homeomorphism. -/
theorem clopen_sum_homeomorph {S : Type u} [TopologicalSpace S]
    {U : Set S} (hU : IsClopen U) : Nonempty ((U ⊕ ↥(Uᶜ)) ≃ₜ S) := by
  let f : U ⊕ ↥(Uᶜ) → S := Sum.elim Subtype.val Subtype.val
  have hi : Function.Injective f := by
    rintro (x|x) (y|y) he
    · exact congrArg Sum.inl (Subtype.ext he)
    · change x.1=y.1 at he
      exact (y.2 (he ▸ x.2)).elim
    · change x.1=y.1 at he
      exact (x.2 (he.symm ▸ y.2)).elim
    · exact congrArg Sum.inr (Subtype.ext he)
  have hf : IsOpenEmbedding f := hU.2.isOpenEmbedding_subtypeVal.sumElim
    hU.1.isOpen_compl.isOpenEmbedding_subtypeVal hi
  have hs : Function.Surjective f := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨Sum.inl ⟨x,hx⟩,rfl⟩
    · exact ⟨Sum.inr ⟨x,hx⟩,rfl⟩
  exact ⟨hf.isEmbedding.toHomeomorphOfSurjective hs⟩

/-- Removing a closed set contained in one clopen part leaves the
complement there and the whole other part, via the inclusion maps. -/
theorem clopen_complement_homeomorph {S : Type u} [TopologicalSpace S]
    {U C : Set S} (hU : IsClopen U) (hC : IsClosed C) (hCU : C ⊆ U) :
    Nonempty ((↥((Subtype.val ⁻¹' C : Set U)ᶜ) ⊕ ↥(Uᶜ)) ≃ₜ ↥(Cᶜ)) := by
  let f : ↥((Subtype.val ⁻¹' C : Set U)ᶜ) ⊕ ↥(Uᶜ) → S :=
    Sum.elim (fun x ↦ x.1.1) Subtype.val
  have hi : Function.Injective f := by
    rintro (x|x) (y|y) he
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext he))
    · change x.1.1=y.1 at he
      exact (y.2 (he ▸ x.1.2)).elim
    · change x.1=y.1.1 at he
      exact (x.2 (he.symm ▸ y.1.2)).elim
    · exact congrArg Sum.inr (Subtype.ext he)
  have hpre : IsOpen ((Subtype.val ⁻¹' C : Set U)ᶜ) :=
    (hC.preimage continuous_subtype_val).isOpen_compl
  have hf : IsOpenEmbedding f :=
    (hU.2.isOpenEmbedding_subtypeVal.comp hpre.isOpenEmbedding_subtypeVal).sumElim
      hU.1.isOpen_compl.isOpenEmbedding_subtypeVal hi
  have hr : range f=Cᶜ := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      cases y with
      | inl y => exact y.2
      | inr y => exact fun hy ↦ y.2 (hCU hy)
    · intro hx
      by_cases hxU : x ∈ U
      · exact ⟨Sum.inl ⟨⟨x,hxU⟩,hx⟩,rfl⟩
      · exact ⟨Sum.inr ⟨x,hxU⟩,rfl⟩
  exact ⟨hf.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)⟩

end GraphMinor.GM05
