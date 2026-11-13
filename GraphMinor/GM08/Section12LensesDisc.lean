module

public import GraphMinor.Surface.DiscGrow
public import GraphMinor.GM08.Section12Lenses
import GraphMinor.GM08.Section10Push
import GraphMinor.GM07.CuffCells
import GraphMinor.GM06.DiscRegions
import GraphMinor.GM08.Section9DiscContext

/-!
# Thickening a finite family of lines in a disc

Carry the lines and their protected set to a sphere. Protect also the
outside of the ambient disc. The sphere lens construction then stays
inside that disc, since a lens can meet its outside only at the line's
ends. Pull the lenses back. This supplies edge discs in the space of
the derived portrait on VIII, page 272.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u v

/-- Thicken finitely many lines in a disc, protecting a closed set and
the boundary except at the ends. This is the non-loop step of the
derived portrait construction used in VIII, Section 12. -/
theorem exists_edge_lens_family_in_disc {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) {ι : Type v} [Finite ι]
    (L : ι → Set S) (a b : ι → S) (hL : ∀ i, IsLineWithEnds (L i) (a i) (b i))
    (hab : ∀ i, a i ≠ b i) {Z : Set S} (hZ : IsClosed Z)
    (hLZ : ∀ i, L i ∩ Z ⊆ {a i, b i})
    (hLbd : ∀ i, L i ∩ bd S ⊆ {a i, b i})
    (hLL : ∀ i j, i ≠ j → L i ∩ L j ⊆ {a i, b i} ∩ {a j, b j}) :
    ∃ D : ι → Set S,
      (∀ i, IsClosedDisc (D i) ∧ L i ⊆ D i ∧ D i ∩ Z ⊆ {a i, b i} ∧
        a i ∈ discBd (D i) ∧ b i ∈ discBd (D i) ∧
        D i ∩ bd S ⊆ {a i, b i} ∧
        ∀ j, j ≠ i → D i ∩ L j ⊆ L i ∩ L j) ∧
      ∀ i j, i ≠ j → D i ∩ D j ⊆ L i ∩ L j := by
  have : T2Space S := (isSurface_of_closedDisc_univ hS).2.1
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hS
  have hf := sc.isClosedEmbedding_of_univ hS
  have hfi := hf.injective
  let A := f '' (univ : Set S)
  have hA : IsClosedDisc A := (sc.disc_f (subset_univ _) hS).1
  let Z' := f '' Z ∪ (discInt A)ᶜ
  have hZ' : IsClosed Z' := (hf.isClosedMap Z hZ).union
    (hA.isOpen_discInt (by intro x; exact ((isClosedSurface_sphere').2.2 x).isManifoldPoint)).isClosed_compl
  have hInt : f '' discInt (univ : Set S) = discInt A :=
    (sc.discInt_f (subset_univ _) hS).symm
  have hpull : ∀ {C : Set S} {x : S}, f x ∈ f '' C → x ∈ C := by
    rintro C x ⟨y, hy, heq⟩
    exact hfi heq ▸ hy
  have hLZ' : ∀ i, (f '' L i) ∩ Z' ⊆ {f (a i), f (b i)} := by
    rintro i x ⟨⟨y, hy, rfl⟩, hz | hz⟩
    · exact image_pair f (a i) (b i) ▸ mem_image_of_mem f (hLZ i ⟨hy, hpull hz⟩)
    · have hybd : y ∈ bd S := by
        rw [← GM06.discBd_univ]
        by_contra hn
        exact hz (hInt ▸ mem_image_of_mem f (show y ∈ discInt (univ : Set S) from ⟨mem_univ _, hn⟩))
      exact image_pair f (a i) (b i) ▸ mem_image_of_mem f (hLbd i ⟨hy, hybd⟩)
  have hLL' : ∀ i j, i ≠ j → (f '' L i) ∩ (f '' L j) ⊆
      {f (a i), f (b i)} ∩ {f (a j), f (b j)} := by
    intro i j hij x hx
    rw [← image_inter hfi] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨image_pair f (a i) (b i) ▸ mem_image_of_mem f (hLL i j hij hy).1,
      image_pair f (a j) (b j) ▸ mem_image_of_mem f (hLL i j hij hy).2⟩
  obtain ⟨E, hE, hEE⟩ := exists_edge_lens_family
    (S := OnePoint EuclideanPlane) isClosedSurface_sphere'
    (fun i => f '' L i) (fun i => f (a i)) (fun i => f (b i))
    (fun i => GM07.isLineWithEnds_image (hL i) hf.continuous.continuousOn hfi.injOn)
    (fun i h => hab i (hfi h)) hZ' hLZ' hLL'
  have hEA : ∀ i, E i ⊆ A := by
    intro i x hx
    by_contra hn
    have hxout : x ∈ (discInt A)ᶜ := fun hi => hn hi.1
    have hxend := (hE i).2.2.1 ⟨hx, .inr hxout⟩
    rcases hxend with h | h
    · exact hn (h.symm ▸ mem_image_of_mem f (mem_univ (a i)))
    · exact hn (h.symm ▸ mem_image_of_mem f (mem_univ (b i)))
  let D := fun i => f' '' E i
  have hD : ∀ i, IsClosedDisc (D i) := fun i =>
    ((hE i).1.image (sc.f'c.mono (hEA i)) (sc.fc.mono (subset_univ _))
      (sc.ff'.mono (hEA i))).1
  have hDE : ∀ i, f '' D i = E i := fun i => (sc.ff'.mono (hEA i)).image_image
  have hBd : ∀ i, f '' discBd (D i) = discBd (E i) := by
    intro i
    rw [← (sc.disc_f (subset_univ _) (hD i)).2, hDE]
  have hmem : ∀ i x, x ∈ D i ↔ f x ∈ E i := by
    intro i x
    rw [← hDE]
    exact hfi.mem_set_image.symm
  have hend : ∀ i x, f x ∈ ({f (a i), f (b i)} : Set (OnePoint EuclideanPlane)) → x ∈ ({a i, b i} : Set S) := by
    intro i x hx
    rw [← image_pair] at hx
    exact hpull hx
  refine ⟨D, ?_, ?_⟩
  · intro i
    refine ⟨hD i, fun x hx => (hmem i x).mpr ((hE i).2.1 (mem_image_of_mem f hx)),
      fun x hx => hend i x ((hE i).2.2.1 ⟨(hmem i x).mp hx.1, .inl (mem_image_of_mem f hx.2)⟩),
      ?_, ?_, ?_, ?_⟩
    · apply hpull
      rw [hBd]
      exact (hE i).2.2.2.1
    · apply hpull
      rw [hBd]
      exact (hE i).2.2.2.2.1
    · intro x hx
      apply hend i x
      apply (hE i).2.2.1
      refine ⟨(hmem i x).mp hx.1, .inr ?_⟩
      intro hi
      have hxInt := hpull (hInt.symm ▸ hi)
      exact hxInt.2 (GM06.discBd_univ S ▸ hx.2)
    · intro j hji x hx
      have hy := (hE i).2.2.2.2.2 j hji
        ⟨(hmem i x).mp hx.1, mem_image_of_mem f hx.2⟩
      exact ⟨hpull hy.1, hpull hy.2⟩
  · intro i j hij x hx
    have hy := hEE i j hij ⟨(hmem i x).mp hx.1, (hmem j x).mp hx.2⟩
    exact ⟨hpull hy.1, hpull hy.2⟩

end GraphMinor.GM08
