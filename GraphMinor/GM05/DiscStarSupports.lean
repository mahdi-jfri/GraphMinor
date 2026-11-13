module

public import GraphMinor.Surface.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# Intersections of whole star supports

For GM V, (8.14), a star support includes its centre even if the
vertex has no incident edge. A centre cannot lie in another star:
it is on the disc boundary, where that star contains only its own
centre and ports. All other common points lie on rays, so the ray
intersection bounds give the required bounds for whole stars.
-/

public section
namespace GraphMinor.GM05
open Set Surface

/-- Finite pairwise intersections and no triple meetings for the
whole local stars in GM V, (8.14), page 113, including isolated centres. -/
theorem disc_star_support_intersections {S ι κ : Type*} [TopologicalSpace S] [Finite κ]
    {R : Set S} (x : ι → S) (p : ι × κ → S) (L : ι × κ → Set S)
    (hx : ∀ i, x i ∈ discBd R) (hxne : ∀ i j, i ≠ j → x i ≠ x j)
    (hxp : ∀ i q, x i ≠ p q)
    (hbd : ∀ q, L q ∩ discBd R = {x q.1,p q})
    (hfin : ∀ q r, q ≠ r → (L q ∩ L r).Finite)
    (hthree : ∀ i j k e f g, i ≠ j → j ≠ k → i ≠ k →
      L (i,e) ∩ L (j,f) ∩ L (k,g) = ∅) :
    (∀ i j, i ≠ j →
      (({x i} ∪ ⋃ e, L (i,e)) ∩ ({x j} ∪ ⋃ e, L (j,e))).Finite) ∧
    ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      ({x i} ∪ ⋃ e, L (i,e)) ∩ ({x j} ∪ ⋃ e, L (j,e)) ∩
        ({x k} ∪ ⋃ e, L (k,e)) = ∅ := by
  have hnot : ∀ i j, i ≠ j → x i ∉ ({x j} ∪ ⋃ e, L (j,e)) := by
    intro i j hij hm
    rcases hm with hm | hm
    · exact hxne i j hij hm
    · obtain ⟨e,he⟩ := mem_iUnion.mp hm
      have hh : x i ∈ ({x j,p (j,e)} : Set S) := hbd (j,e) ▸ ⟨he,hx i⟩
      exact hh.elim (hxne i j hij) (hxp i (j,e))
  constructor
  · intro i j hij
    have hf : (⋃ e, ⋃ f, L (i,e) ∩ L (j,f)).Finite :=
      finite_iUnion fun e ↦ finite_iUnion fun f ↦ hfin (i,e) (j,f)
        (fun he ↦ hij (congrArg Prod.fst he))
    apply hf.subset
    rintro z ⟨hz₁,hz₂⟩
    rcases hz₁ with rfl | hz₁
    · exact (hnot i j hij hz₂).elim
    rcases hz₂ with rfl | hz₂
    · exact (hnot j i (Ne.symm hij) (Or.inr hz₁)).elim
    obtain ⟨e,he⟩ := mem_iUnion.mp hz₁
    obtain ⟨f,hf⟩ := mem_iUnion.mp hz₂
    exact mem_iUnion₂.mpr ⟨e,f,he,hf⟩
  · intro i j k hij hjk hik
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨⟨hz₁,hz₂⟩,hz₃⟩
    rcases hz₁ with rfl | hz₁
    · exact hnot i j hij hz₂
    rcases hz₂ with rfl | hz₂
    · exact hnot j i (Ne.symm hij) (Or.inr hz₁)
    rcases hz₃ with rfl | hz₃
    · exact hnot k i (Ne.symm hik) (Or.inr hz₁)
    obtain ⟨e,he⟩ := mem_iUnion.mp hz₁
    obtain ⟨f,hf⟩ := mem_iUnion.mp hz₂
    obtain ⟨g,hg⟩ := mem_iUnion.mp hz₃
    have hm : z ∈ L (i,e) ∩ L (j,f) ∩ L (k,g) := ⟨⟨he,hf⟩,hg⟩
    rw [hthree i j k e f g hij hjk hik] at hm
    exact hm

end GraphMinor.GM05
