module

public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18FiniteBoundaryMinimum
import GraphMinor.GM08.Section18Schism
import GraphMinor.GM07.CutEdge

/-!
# The zero-alpha case of the small-schism alternative

Choose a minimum whose boundary contacts are drawing vertices. If alpha
is zero, this minimum misses all drawing vertices, so it also misses the
boundary. A boundary-disjoint schismatic set is a schism.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- When alpha vanishes, the small-schism alternative of VIII (18.1)
holds with no drawing vertices on the schism. This includes surfaces
with several cuffs and the branched schismatic shapes. -/
theorem exists_normal_schism_of_alpha_eq_zero {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {a b c : ℕ}
    (h3 : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    (G : Drawing S) (hp : G.IsProper) (hzero : GM07.alpha G = 0) :
    ∃ X, GM07.IsSchism X ∧ G.IsNormal X ∧ (G.V ∩ X).ncard = 0 := by
  have : T2Space S := hS.2.1
  obtain ⟨X, hX, hnX, hcount, hbd⟩ :=
    exists_normal_schismatic_at_alpha_with_boundary_vertices hS h3 hm hcyl G hp
  have hXV : X ∩ G.V = ∅ :=
    (ncard_eq_zero (G.finite_V.inter_of_right X)).mp (hcount.trans hzero)
  have hoff : X ∩ bd S = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x hx
    have hh : x ∈ X ∩ G.V := ⟨hx.1, hbd hx⟩
    rw [hXV] at hh
    exact hh
  have hns : ¬ IsSphere S := GM07.not_isSphere_of_model hm (by omega)
  exact ⟨X, isSchism_of_isSchismatic_off_boundary hS hns hX hoff, hnX,
    by rw [inter_comm, hXV]; exact ncard_empty _⟩

/-- If a drawing has no boundary vertices, its minimum can be chosen
on a normal schism. This is the rootless small-alpha case of VIII (18.1). -/
theorem exists_normal_schism_at_alpha_of_no_boundary_vertices {S : Type u}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S) {a b c : ℕ}
    (h3 : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    (G : Drawing S) (hp : G.IsProper) (hVbd : G.V ∩ bd S = ∅) :
    ∃ X, GM07.IsSchism X ∧ G.IsNormal X ∧ (G.V ∩ X).ncard = GM07.alpha G := by
  have : T2Space S := hS.2.1
  obtain ⟨X, hX, hnX, hcount, hbd⟩ :=
    exists_normal_schismatic_at_alpha_with_boundary_vertices hS h3 hm hcyl G hp
  have hoff : X ∩ bd S = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x hx
    have hh : x ∈ G.V ∩ bd S := ⟨hbd hx, hx.2⟩
    rw [hVbd] at hh
    exact hh
  have hns : ¬ IsSphere S := GM07.not_isSphere_of_model hm (by omega)
  exact ⟨X, isSchism_of_isSchismatic_off_boundary hS hns hX hoff, hnX,
    by rw [inter_comm]; exact hcount⟩

end GraphMinor.GM08
