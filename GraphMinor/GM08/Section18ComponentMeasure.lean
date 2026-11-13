module

public import GraphMinor.GM08.Section18Complexity
import GraphMinor.GM08.Section18ClopenComplexity
import GraphMinor.GM08.Section18Maximum
import GraphMinor.Surface.CutComp

/-!
# The measure, one component at a time

The cuts of (18.2) for types (iv) and (v) on page 286 are made one arc at a
time, and each cut may split off new components. To follow the measure `g`
through these steps we look at one component at a time. The measure of a
surface is at most `n` when the measure of every component is at most `n`
(`surfaceComplexity_le_of_components`), and the measure of a component does
not change under a homeomorphism (`connectedSurfaceComplexity_component_homeo`)
or when we pass to an open and closed part
(`connectedSurfaceComplexity_component_subtype`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- The measure of a surface is at most `n` when every component has measure
at most `n`. -/
theorem surfaceComplexity_le_of_components {T : Type w} [TopologicalSpace T] {n : ℕ}
    (h : ∀ x : T, connectedSurfaceComplexity (connectedComponent x) ≤ n) :
    surfaceComplexity T ≤ n := by
  rcases ((fun C : Set T => connectedSurfaceComplexity C) '' spaceComponents T).eq_empty_or_nonempty
    with he | hne
  · rw [surfaceComplexity, he, csSup_empty]
    exact bot_le
  refine csSup_le hne ?_
  rintro m ⟨C, hC, rfl⟩
  rw [Surface.spaceComponents_eq] at hC
  obtain ⟨x, rfl⟩ := hC
  exact h x

/-- The measure of a surface is less than a positive `n` when every component
has measure less than `n`. A surface has finitely many components, so the
largest measure is the measure of one of them. -/
theorem surfaceComplexity_lt_of_components {T : Type w} [TopologicalSpace T]
    (hT : IsSurface T) {n : ℕ} (hn : 0 < n)
    (h : ∀ x : T, connectedSurfaceComplexity (connectedComponent x) < n) :
    surfaceComplexity T < n := by
  rcases ((fun C : Set T => connectedSurfaceComplexity C) '' spaceComponents T).eq_empty_or_nonempty
    with he | hne
  · rw [surfaceComplexity, he, csSup_empty]
    exact hn
  obtain ⟨C, hC, hCeq⟩ := hne.csSup_mem ((finite_spaceComponents_of_surface hT).image _)
  rw [surfaceComplexity, ← hCeq]
  rw [Surface.spaceComponents_eq] at hC
  obtain ⟨x, rfl⟩ := hC
  exact h x

/-- A component has measure at most the measure of the surface. -/
theorem connectedSurfaceComplexity_component_le {T : Type w} [TopologicalSpace T]
    (hT : IsSurface T) (x : T) :
    connectedSurfaceComplexity (connectedComponent x) ≤ surfaceComplexity T :=
  connectedSurfaceComplexity_le_of_mem hT (by rw [Surface.spaceComponents_eq]; exact ⟨x, rfl⟩)

/-- A homeomorphism keeps the measure of each component. -/
theorem connectedSurfaceComplexity_component_homeo {X Y : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    connectedSurfaceComplexity (connectedComponent (e x)) =
      connectedSurfaceComplexity (connectedComponent x) := by
  have himg : e '' connectedComponent x = connectedComponent (e x) := by
    have h := e.image_connectedComponentIn (mem_univ x)
    rwa [connectedComponentIn_univ, image_univ_of_surjective e.surjective,
      connectedComponentIn_univ] at h
  rw [← himg]
  exact (connectedSurfaceComplexity_congr (e.image (connectedComponent x))).symm

/-- In an open and closed part, a component has the same measure as in the
whole surface. -/
theorem connectedSurfaceComplexity_component_subtype {T : Type w} [TopologicalSpace T]
    {R : Set T} (hR : IsClopen R) (x : R) :
    connectedSurfaceComplexity (connectedComponent x) =
      connectedSurfaceComplexity (connectedComponent (x : T)) := by
  have hsub : connectedComponent (x : T) ⊆ R := hR.connectedComponent_subset x.2
  obtain ⟨e⟩ := exists_homeo_sub (connectedComponent (x : T)) hsub
  exact connectedSurfaceComplexity_congr
    ((Homeomorph.setCongr (connectedComponent_subtype_eq hR x)).trans e)

/-- The components of the left part of a disjoint union keep their measure. -/
theorem connectedSurfaceComplexity_component_inl {A B : Type w} [TopologicalSpace A]
    [TopologicalSpace B] (a : A) :
    connectedSurfaceComplexity (connectedComponent (Sum.inl a : A ⊕ B)) =
      connectedSurfaceComplexity (connectedComponent a) := by
  have hR : IsClopen (range (Sum.inl : A → A ⊕ B)) := ⟨isClosed_range_inl, isOpen_range_inl⟩
  let e : A ≃ₜ range (Sum.inl : A → A ⊕ B) := IsEmbedding.inl.toHomeomorph
  rw [← connectedSurfaceComplexity_component_homeo e a,
    connectedSurfaceComplexity_component_subtype hR]
  rfl

/-- The components of the right part of a disjoint union keep their measure. -/
theorem connectedSurfaceComplexity_component_inr {A B : Type w} [TopologicalSpace A]
    [TopologicalSpace B] (b : B) :
    connectedSurfaceComplexity (connectedComponent (Sum.inr b : A ⊕ B)) =
      connectedSurfaceComplexity (connectedComponent b) := by
  have hR : IsClopen (range (Sum.inr : B → A ⊕ B)) := ⟨isClosed_range_inr, isOpen_range_inr⟩
  let e : B ≃ₜ range (Sum.inr : B → A ⊕ B) := IsEmbedding.inr.toHomeomorph
  rw [← connectedSurfaceComplexity_component_homeo e b,
    connectedSurfaceComplexity_component_subtype hR]
  rfl

/-- A component that is homeomorphic to the model `Σ(a, b, c)` has measure
`4a + 2b + c`. -/
theorem connectedSurfaceComplexity_component_model {T : Type w} [TopologicalSpace T]
    {x : T} {a b c : ℕ} (e : connectedComponent x ≃ₜ SurfaceModel a b c) :
    connectedSurfaceComplexity (connectedComponent x) = 4 * a + 2 * b + c :=
  connectedSurfaceComplexity_eq ⟨e⟩

end GraphMinor.GM08
