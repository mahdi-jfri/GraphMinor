module

public import GraphMinor.GM06.Alg57VertexStar
public import GraphMinor.GM06.Alg57RotationRestriction
import GraphMinor.GM06.Section5SmallPolar
import GraphMinor.GM06.Section5PolarShrink

/-!
# Small counterclockwise stars

A counterclockwise star chart at a vertex (`IsCcwStar`) can be made as small as we like: we
restrict it to a small disc about its centre. The directions of the darts stay the same
(`IsCcwStar.exists_small`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {Γ : Drawing (OnePoint EuclideanPlane)}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart Γ)} {v : OnePoint EuclideanPlane}
  {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {z : DrawingDart Γ → Circle}

/-- **A counterclockwise star inside any open set around its centre.** -/
theorem IsCcwStar.exists_small (h : IsCcwStar Γ γ R v Φ z)
    (hS : IsClosedSurface (OnePoint EuclideanPlane)) {O : Set (OnePoint EuclideanPlane)}
    (hO : IsOpen O) (hv : v ∈ O) :
    ∃ Φ' : C(ClosedUnitDisc, OnePoint EuclideanPlane), IsCcwStar Γ γ R v Φ' z ∧ range Φ' ⊆ O := by
  obtain ⟨c, hc, Φ', hp', hO', hscale⟩ := exists_small_polar_chart_with_factor hS h.polar hO hv
  refine ⟨Φ', ⟨hp', h.pos.radial_restriction h.polar.inj c hc hscale, h.inj, ?_, ?_, h.succ⟩, hO'⟩
  · intro a ha t ht
    rw [hscale, discScale_polarDiscPoint]
    exact h.spoke a ha _ (by change (0 : ℝ) < c * t; exact mul_pos hc ht)
  · intro w e he hw
    have hrim : polarRimMap Φ w ∈ e := by
      have hn : IsGammaNice Γ e := ⟨{e}, singleton_subset_iff.mpr (Or.inl (Or.inr he)), by simp⟩
      refine (polar_ray_mem_iff h.polar hn w hc).mp ?_
      have : polarRimMap Φ' w = Φ (polarDiscPoint c w) := by
        change Φ' (polarDiscPoint 1 w) = _
        rw [hscale, discScale_polarDiscPoint_one]
      rwa [← this]
    exact h.dirs w e he hrim

end GraphMinor.GM06
