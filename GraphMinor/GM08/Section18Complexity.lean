module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.ModelCriterion
import GraphMinor.Surface.CutIArc

/-!
# The surface measure in VIII Section 18

The quantity `4a + 2b + c` is independent of the model chosen for a connected
surface. For a surface with several components, take the supremum of the
component values. For surfaces this is the maximum in the paper's definition.
A cut whose components are simpler has smaller measure.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v

/-- The value $g(\Sigma)=4a+2b+c$ for a connected surface, VIII Section 18,
page 286. Model invariance is proved in `connectedSurfaceComplexity_eq`. -/
noncomputable def connectedSurfaceComplexity (S : Type u) [TopologicalSpace S] : ℕ :=
  sInf {n | ∃ a b c : ℕ, Nonempty (S ≃ₜ SurfaceModel a b c) ∧ 4 * a + 2 * b + c = n}

/-- The model value of the connected surface measure is well-defined. -/
theorem connectedSurfaceComplexity_eq {S : Type u} [TopologicalSpace S]
    {a b c : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b c)) :
    connectedSurfaceComplexity S = 4 * a + 2 * b + c := by
  unfold connectedSurfaceComplexity
  refine le_antisymm ?_ ?_
  · exact Nat.sInf_le ⟨a, b, c, he, rfl⟩
  refine le_csInf (s := {n : ℕ | ∃ a b c : ℕ,
    Nonempty (S ≃ₜ SurfaceModel a b c) ∧ 4 * a + 2 * b + c = n})
    ⟨4 * a + 2 * b + c, a, b, c, he, rfl⟩ ?_
  rintro n ⟨a', b', c', ⟨e'⟩, rfl⟩
  obtain ⟨e⟩ := he
  obtain ⟨hc, hg, _⟩ := (modelCriterion.2 a b c a' b' c').mp ⟨e.symm.trans e'⟩
  omega

/-- A homeomorphism preserves the connected surface measure. -/
theorem connectedSurfaceComplexity_congr {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] (e : S ≃ₜ T) :
    connectedSurfaceComplexity S = connectedSurfaceComplexity T := by
  unfold connectedSurfaceComplexity
  apply congrArg sInf
  ext n
  constructor
  · rintro ⟨a, b, c, ⟨h⟩, hn⟩
    exact ⟨a, b, c, ⟨e.symm.trans h⟩, hn⟩
  · rintro ⟨a, b, c, ⟨h⟩, hn⟩
    exact ⟨a, b, c, ⟨e.trans h⟩, hn⟩

/-- The measure of a general surface is the maximum over its components,
as defined in VIII Section 18, page 286. The value for the empty surface is zero. -/
noncomputable def surfaceComplexity (S : Type u) [TopologicalSpace S] : ℕ :=
  sSup ((fun C : Set S => connectedSurfaceComplexity C) '' spaceComponents S)

private theorem spaceComponents_singleton {S : Type u} [TopologicalSpace S] [ConnectedSpace S] :
    spaceComponents S = {univ} := by
  rw [Surface.spaceComponents_eq]
  ext C
  constructor
  · rintro ⟨x, rfl⟩
    exact PreconnectedSpace.connectedComponent_eq_univ x
  · rintro rfl
    obtain ⟨x⟩ := (inferInstance : Nonempty S)
    exact ⟨x, PreconnectedSpace.connectedComponent_eq_univ x⟩

/-- The general and connected definitions agree on a connected surface. -/
theorem surfaceComplexity_eq_connected {S : Type u} [TopologicalSpace S] [ConnectedSpace S] :
    surfaceComplexity S = connectedSurfaceComplexity S := by
  rw [surfaceComplexity, spaceComponents_singleton, image_singleton, csSup_singleton]
  exact connectedSurfaceComplexity_congr (Homeomorph.Set.univ S)

/-- A simpler connected surface has smaller measure. -/
theorem connectedSurfaceComplexity_lt_of_isSimplerThan {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] (h : IsSimplerThan S T) :
    connectedSurfaceComplexity S < connectedSurfaceComplexity T := by
  obtain ⟨a, b, c, a', b', c', hS, hT, _, _, hlt⟩ := h
  rw [connectedSurfaceComplexity_eq hS, connectedSurfaceComplexity_eq hT]
  exact hlt

/-- If every component of a nonempty cut surface is simpler than the
connected original, the maximum of their measures is smaller. This is the
last componentwise step of VIII (18.2), page 286. -/
theorem surfaceComplexity_lt_of_cutIsSimpler {S T : Type u}
    [TopologicalSpace S] [TopologicalSpace T] [Nonempty S] [ConnectedSpace T]
    (h : CutIsSimpler S T) : surfaceComplexity S < surfaceComplexity T := by
  have hnonempty : ((fun C : Set S => connectedSurfaceComplexity C) '' spaceComponents S).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty S)
    exact ⟨_, _, ⟨x, mem_univ x, rfl⟩, rfl⟩
  have hless : ∀ n ∈ (fun C : Set S => connectedSurfaceComplexity C) '' spaceComponents S,
      n < connectedSurfaceComplexity T := by
    rintro n ⟨C, hC, rfl⟩
    exact connectedSurfaceComplexity_lt_of_isSimplerThan (h.2 C hC)
  have hpos : 0 < connectedSurfaceComplexity T := by
    obtain ⟨n, hn⟩ := hnonempty
    exact Nat.zero_lt_of_lt (hless n hn)
  have hsup : surfaceComplexity S ≤ connectedSurfaceComplexity T - 1 := by
    apply csSup_le hnonempty
    intro n hn
    have hn' := hless n hn
    omega
  rw [surfaceComplexity_eq_connected (S := T)]
  omega

end GraphMinor.GM08
