module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM19.CutMap
import GraphMinor.GM07.CutBuild
import GraphMinor.GM07.CutEdge
import GraphMinor.GM11.RadialChord
import GraphMinor.GM19.Section6a
import GraphMinor.Surface.Classification
import GraphMinor.Surface.Cuffs

/-!
# Cutting a connected surface along a line off the boundary

This is the slit of Graph Minors VII, (4.6) (`GM07.exists_cut`), with one
line `M` as the only edge. The cut adds one cuff, which lies over `M`. Each
inner point of `M` has two points over it, each end has one, and every other
point has one.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- **The slit along a line.** Cutting a connected surface along a line `M`
with ends `m₁ ≠ m₂` that misses the boundary gives a connected surface with one
more cuff. Each inner point of `M` has exactly two points over it, and every
other point has exactly one. -/
theorem exists_slit_cut {R : Type w} [TopologicalSpace R] [ConnectedSpace R] (hR : IsSurface R)
    {M : Set R} {m₁ m₂ : R} (hM : IsLineWithEnds M m₁ m₂) (hne : m₁ ≠ m₂)
    (hMbd : Disjoint M (bd R)) :
    ∃ (Y : Type w) (_ : TopologicalSpace Y) (φ : Y → R), IsSurface Y ∧ ConnectedSpace Y ∧
      GM19.IsCutMap φ M ∧ (∀ x ∈ M \ {m₁, m₂}, (φ ⁻¹' {x}).ncard = 2) ∧
      (∀ x ∉ M \ {m₁, m₂}, (φ ⁻¹' {x}).ncard = 1) ∧ IsOArc (φ ⁻¹' M) ∧
      ∃ a b c : ℕ, Nonempty (R ≃ₜ SurfaceModel a b c) ∧
        Nonempty (Y ≃ₜ SurfaceModel a b (c + 1)) := by
  have : T2Space R := hR.2.1
  obtain ⟨a, b, c, ⟨eR⟩⟩ := classification R hR inferInstance
  set G : Drawing R := GM11.lineDrawing hM hne
  set e : Set R := M \ {m₁, m₂}
  have hE : G.E = {e} := GM11.lineDrawing_E hM hne
  have he : e ∈ G.E := hE ▸ rfl
  have hcl : closure e = M := GM11.closure_sdiff_pair hM
  have hG : G.IsProper := by
    intro x hx
    exact absurd hx.1 (disjoint_left.mp hMbd hx.2)
  have hl : (tilde e).ncard = 2 := by
    rw [GM19.tilde_eq_inter_V G he, hcl]
    have hV : G.V = {m₁, m₂} := rfl
    have hsub : ({m₁, m₂} : Set R) ⊆ M := by
      obtain ⟨f, h0, h1⟩ := hM
      rintro y (rfl | rfl)
      · exact h0 ▸ (f 0).2
      · exact h1 ▸ (f 1).2
    rw [hV, inter_eq_right.mpr hsub, ncard_pair hne]
  have hd : closure e ∩ bd R = ∅ := by
    rw [hcl]
    exact hMbd.inter_eq
  obtain ⟨Y, tY, _, φ, G', hc⟩ := GM07.exists_cut hR ⟨eR⟩ G hG he hl hd
  have hY : IsSurface Y := hc.isSurface
  obtain ⟨eY⟩ := hc.homeo_model
  have hYc : ConnectedSpace Y := by
    have := (modelCriterion.1 a b (c + 1)).2
    exact eY.symm.surjective.connectedSpace eY.symm.continuous
  have hsurj : Function.Surjective φ := hc.quotientMap.surjective
  have hone : ∀ x ∉ e, (φ ⁻¹' {x}).ncard = 1 := by
    intro x hx
    obtain ⟨y, rfl⟩ := hsurj x
    refine ncard_eq_one.mpr ⟨y, ?_⟩
    ext z
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro hz
      exact ((hc.inj z y hz).resolve_right fun h => hx (hz ▸ h))
    · rintro rfl
      rfl
  refine ⟨Y, tY, φ, hY, hYc, ⟨hc.quotientMap.continuous, hsurj, ?_, hc.finite_fiber, ?_⟩,
    fun x hx => le_antisymm (hc.fiber_two x) (hc.two_le x hx), hone, ?_, a, b, c, ⟨eR⟩, ⟨eY⟩⟩
  · intro x hx y _ hxy
    exact (hc.inj x y hxy).resolve_right fun h => hx (sdiff_subset h)
  · intro y hy
    rw [hc.bd_eq]
    exact Or.inr (hcl.symm ▸ hy)
  · have h := hc.newCuff
    rw [hcl] at h
    exact (cuff_statement.{w} Y hY).2.2 _ h

end GraphMinor.GM08
