module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM08.Section12Shrink
import GraphMinor.GM08.Section8Defs
import GraphMinor.GM08.Section10Push

/-!
# Shrinking a foundation disc in its ambient disc

Carry the configuration to the sphere, apply the complementary-disc
push-off construction, and carry the smaller disc back. The sphere
chart is an embedding on the whole ambient disc, so it preserves the
closed protected set, boundary contacts, and inside points. This gives
the shrinking step of VIII, page 267, in the space used by Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- Shrink a disc in a disc ambient space, preserving its boundary
contacts with a closed set and all protected interior points. This is
the boundary adjustment of the foundation used in VIII, Section 12. -/
theorem exists_shrunk_disc_in_disc {S : Type u} [TopologicalSpace S]
    (hΔ : IsClosedDisc (univ : Set S)) {B K Z : Set S}
    (hB : IsClosedDisc B) (hK : IsClosedDisc K) (hKB : K ⊆ discInt B)
    (hZ : IsClosed Z) :
    ∃ B' : Set S, IsClosedDisc B' ∧ K ⊆ discInt B' ∧ B' ⊆ B ∧
      discBd B' ∩ Z = discBd B ∩ Z ∧ discBd B' ⊆ discInt B ∪ Z ∧
      ∀ x ∈ Z, x ∈ discInt B → x ∈ discInt B' := by
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  have hf := sc.isClosedEmbedding_of_univ hΔ
  have hfi := hf.injective
  have hBs := (sc.disc_f (subset_univ B) hB).1
  have hKs := (sc.disc_f (subset_univ K) hK).1
  have hKBs : f '' K ⊆ discInt (f '' B) := by
    rw [sc.discInt_f (subset_univ B) hB]
    exact image_mono hKB
  obtain ⟨E, hE, hKE, hEB, hEZ, hbdE, hkeep⟩ :=
    exists_shrunk_disc (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩ hBs hKs hKBs
      (hf.isClosedMap Z hZ)
  have hEΔ : E ⊆ f '' (univ : Set S) := hEB.trans (image_mono (subset_univ B))
  let B' := f' '' E
  have hB' : IsClosedDisc B' := (hE.image (sc.f'c.mono hEΔ)
    (sc.fc.mono (subset_univ _)) (sc.ff'.mono hEΔ)).1
  have hfB' : f '' B' = E := by
    exact (sc.ff'.mono hEΔ).image_image
  have hb' : f '' discBd B' = discBd E := by
    rw [← (sc.disc_f (subset_univ B') hB').2, hfB']
  have hi' : f '' discInt B' = discInt E := by
    rw [← sc.discInt_f (subset_univ B') hB', hfB']
  have hpull : ∀ {A : Set S} {x : S}, f x ∈ f '' A → x ∈ A := by
    rintro A x ⟨y, hy, heq⟩
    exact hfi heq ▸ hy
  refine ⟨B', hB', ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply hpull
    rw [hi']
    exact hKE (mem_image_of_mem f hx)
  · calc
      B' ⊆ f' '' (f '' B) := image_mono hEB
      _ = B := sc.f'_f (subset_univ B)
  · apply hfi.image_injective
    rw [image_inter hfi, image_inter hfi, hb', ← (sc.disc_f (subset_univ B) hB).2, hEZ]
  · intro x hx
    have hxE : f x ∈ discBd E := hb' ▸ mem_image_of_mem f hx
    rcases hbdE hxE with hin | hZ'
    · apply Or.inl
      apply hpull
      rw [← sc.discInt_f (subset_univ B) hB]
      exact hin
    · exact Or.inr (hpull hZ')
  · intro x hxZ hxint
    apply hpull
    rw [hi']
    apply hkeep (f x) (mem_image_of_mem f hxZ)
    rw [sc.discInt_f (subset_univ B) hB]
    exact mem_image_of_mem f hxint

end GraphMinor.GM08
