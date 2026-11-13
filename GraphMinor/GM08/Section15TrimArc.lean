module

public import GraphMinor.Surface.Defs
import GraphMinor.GM08.Section15Tube

/-!
# Shortening a cuff-joining arc

Take the first point on the second closed set, then the last point on
the first set before it. The intervening subarc meets their union only
at its ends. No new drawing vertices are added. This turns a tube
length witness between the cuffs into the proper arc used in (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- An arc joining disjoint closed sets contains a subarc meeting their
union only in its ends. This is the shortening of the length witness
before the disc cut in VIII (15.4), page 282. -/
theorem exists_subarc_between_closed_sets {S : Type w} [TopologicalSpace S] [T2Space S]
    {I A B : Set S} {u v : S} (hI : IsLineWithEnds I u v)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hu : u ∈ A) (hv : v ∈ B) :
    ∃ (J : Set S) (a b : S), J ⊆ I ∧ a ∈ A ∧ b ∈ B ∧
      IsLineWithEnds J a b ∧ J ∩ (A ∪ B) = {a, b} := by
  obtain ⟨e, he0, he1⟩ := hI
  let f : unitInterval → S := fun t => (e t).1
  have hfc : Continuous f := continuous_subtype_val.comp e.continuous
  have hfi : Function.Injective f := Subtype.val_injective.comp e.injective
  have h0 : f 0 ∈ A := by change (e 0).1 ∈ A; rwa [he0]
  have h1 : f 1 ∈ B := by change (e 1).1 ∈ B; rwa [he1]
  have hBc : IsCompact (f ⁻¹' B) := (hB.preimage hfc).isCompact
  obtain ⟨t₂, ht₂, hleast⟩ := hBc.exists_isLeast ⟨1, h1⟩
  have hAc : IsCompact (Iic t₂ ∩ f ⁻¹' A) :=
    (isClosed_Iic.inter (hA.preimage hfc)).isCompact
  obtain ⟨t₁, ⟨ht₁₂, ht₁⟩, hgreatest⟩ :=
    hAc.exists_isGreatest ⟨0, unitInterval.nonneg t₂, h0⟩
  have hlt : t₁ < t₂ := lt_of_le_of_ne ht₁₂ (by
    intro heq
    exact disjoint_left.mp hAB ht₁ (heq.symm ▸ ht₂))
  let J := f '' Icc t₁ t₂
  have haJ : f t₁ ∈ J := mem_image_of_mem f (left_mem_Icc.mpr hlt.le)
  have hbJ : f t₂ ∈ J := mem_image_of_mem f (right_mem_Icc.mpr hlt.le)
  refine ⟨J, f t₁, f t₂, ?_, ht₁, ht₂, subArc_of_lt hfc hfi hlt, ?_⟩
  · rintro x ⟨t, _, rfl⟩
    exact (e t).2
  · apply subset_antisymm
    · rintro x ⟨⟨t, ht, rfl⟩, hxA | hxB⟩
      · have heq : t = t₁ := le_antisymm (hgreatest ⟨ht.2, hxA⟩) ht.1
        exact .inl (congrArg f heq)
      · have heq : t = t₂ := le_antisymm ht.2 (hleast hxB)
        exact .inr (congrArg f heq)
    · rintro x (rfl | rfl)
      · exact ⟨haJ, .inl ht₁⟩
      · exact ⟨hbJ, .inr ht₂⟩

end GraphMinor.GM08
