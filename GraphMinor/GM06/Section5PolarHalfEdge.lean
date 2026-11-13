module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5HalfEdgeConnected
import GraphMinor.GM06.Section5HalfEdgeStar
import GraphMinor.GM06.Section5PolarEdgeAccess
import GraphMinor.GM06.Section5SmallPolar

/-!
# Labelling polar edge directions by directed ends

The finite rotation rows in VI (5.7), page 133, label directed
ends, rather than merely edges. Shrink the polar chart into a
finite star neighbourhood. Each positive radial edge segment is
connected, so it belongs to one and only one incident half-spoke.
The statement keeps the two ends of a loop distinct.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Inside a vertex star, each polar edge ray has a unique directed-end label. -/
theorem polar_edge_ray_has_unique_halfedge
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) {O : Set S}
    (hstar : ∀ y ∈ Γ.U ∩ O, y = v ∨ ∃ a : halfEdges Γ γ v, ∃ t : I,
      0 < t ∧ t < 1 ∧ spoke γ a.1 t = y)
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ) (hΦO : range Φ ⊆ O)
    {e : Set S} (he : e ∈ Γ.E) (w : Circle) (hw : polarRimMap Φ w ∈ e) :
    ∃! a : halfEdges Γ γ v, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t w) ∈ range (spoke γ a.1) := by
  let f : C(I, S) := ⟨fun t => Φ (polarDiscPoint t w), by
    have hc : Continuous (fun t : I => discScale t (polarDiscPoint 1 w)) :=
      continuous_discScale.comp (continuous_id.prodMk continuous_const)
    have heq : (fun t : I => Φ (polarDiscPoint t w)) =
        fun t : I => Φ (discScale t (polarDiscPoint 1 w)) := by
      funext t
      rw [discScale_polarDiscPoint_one]
    rw [heq]
    exact Φ.continuous.comp hc⟩
  have hfe (t : I) (ht : 0 < t) : f t ∈ e := by
    have hh := (polar_ray_mem_atom_iff hp (Or.inl (Or.inr he))
      (polarDiscPoint_one_ne_centre w) t ht).mp hw
    rwa [discScale_polarDiscPoint_one] at hh
  let B := f '' Ioi (0 : I)
  have hB : IsConnected B := ⟨⟨f 1, 1, zero_lt_one, rfl⟩,
    isPreconnected_Ioi.image f f.continuous.continuousOn⟩
  have hBstar : ∀ y ∈ B, ∃ a : halfEdges Γ γ v, ∃ t : I,
      0 < t ∧ t < 1 ∧ spoke γ a.1 t = y := by
    rintro _ ⟨t, ht, rfl⟩
    have hyO : f t ∈ O := hΦO (mem_range_self (polarDiscPoint t w))
    have hyU : f t ∈ Γ.U := (he.2.1 (hfe t ht)).1
    obtain hy | hy := hstar (f t) ⟨hyU, hyO⟩
    · exact False.elim ((he.2.1 (hfe t ht)).2 (hy.symm ▸ hv))
    · exact hy
  obtain ⟨a, ha, huniq⟩ := exists_unique_halfedge_of_connected_star hγ hv hB hBstar
  refine ⟨a, fun t ht => ha (mem_image_of_mem f ht), ?_⟩
  intro b hb
  apply huniq
  rintro _ ⟨t, ht, rfl⟩
  exact hb t ht

/-- A polar chart may be chosen inside any open neighbourhood so that
all its edge directions have unique incident directed-end labels. -/
theorem exists_polar_chart_with_unique_edge_end_labels
    {S : Type u} [TopologicalSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    {O : Set S} (hOo : IsOpen O) (hvO : v ∈ O) :
    ∃ Ψ : C(ClosedUnitDisc, S), IsPolar Γ v Ψ ∧ range Ψ ⊆ O ∧
      ∀ e ∈ Γ.E, ∀ w : Circle, polarRimMap Ψ w ∈ e →
        ∃! a : halfEdges Γ γ v, ∀ t : I, 0 < t →
          Ψ (polarDiscPoint t w) ∈ range (spoke γ a.1) := by
  let : T2Space S := hS.2.1
  obtain ⟨W, hWo, hvW, hstar⟩ := exists_halfedge_star_neighbourhood hγ hv
  obtain ⟨Ψ, hΨ, hΨOW⟩ := exists_small_polar_chart hS hp (hOo.inter hWo) ⟨hvO, hvW⟩
  refine ⟨Ψ, hΨ, fun y hy => (hΨOW hy).1, ?_⟩
  intro e he w hw
  exact polar_edge_ray_has_unique_halfedge hγ hv hstar hΨ
    (fun y hy => (hΨOW hy).2) he w hw

end GraphMinor.GM06
