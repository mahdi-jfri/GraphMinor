module

public import GraphMinor.GM06.Section5PolarHalfEdge
public import GraphMinor.GM06.Section5PolarRay
import GraphMinor.GM06.Section5InitialSubarcsMeet

/-!
# Distinct polar directions have distinct directed-end labels

For the finite rotation interpretation of VI (5.7), page 133,
two rays with the same label would be initial subarcs of the same
half-spoke. They would meet away from the centre. Injectivity of
the disc chart and uniqueness of positive radial coordinates then
force their directions to be equal. Thus the edge directions in
a small polar chart form a finite set of distinct directed ends.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Two polar rays contained in the same incident half-spoke have
the same rim direction. -/
theorem polar_direction_eq_of_same_halfedge
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (a : halfEdges Γ γ v) {w z : Circle}
    (hw : ∀ t : I, 0 < t → Φ (polarDiscPoint t w) ∈ range (spoke γ a.1))
    (hz : ∀ t : I, 0 < t → Φ (polarDiscPoint t z) ∈ range (spoke γ a.1)) : w = z := by
  let f : C(I, S) := ⟨spoke γ a.1, continuous_spoke hγ a.2.1⟩
  have hf : IsArcMap f := ⟨f.continuous, spoke_injective hγ a.2.1⟩
  have hf0 : f 0 = v := (spoke_zero γ a.1).trans a.2.2
  have hsub (d : Circle)
      (hd : ∀ t : I, 0 < t → Φ (polarDiscPoint t d) ∈ range (spoke γ a.1)) :
      range (polarRayMap Φ d) ⊆ range f := by
    rintro _ ⟨t, rfl⟩
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht | ht
    · have ht0 : t = 0 := Subtype.ext ht.symm
      rw [ht0, polarRayMap_zero, hp.centre]
      exact ⟨0, hf0⟩
    · exact hd t ht
  have hstart (d : Circle) : polarRayMap Φ d 0 = f 0 := by
    rw [polarRayMap_zero, hp.centre, hf0]
  obtain ⟨r, s, hr, _, hrs⟩ := exists_positive_meeting_of_initial_subarcs
    f (polarRayMap Φ w) (polarRayMap Φ z) hf
    (isArcMap_polarRayMap hp.inj w) (isArcMap_polarRayMap hp.inj z)
    (hsub w hw) (hsub z hz) (hstart w) (hstart z)
  exact polarDiscPoint_direction_eq hr (hp.inj hrs)

/-- When polar edge rays have directed-end labels, their set of rim
directions is finite. This is a property proved from the geometry. -/
theorem finite_polar_edge_directions_of_labels
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    {e : Set S}
    (hlabel : ∀ w : Circle, polarRimMap Φ w ∈ e →
      ∃ a : halfEdges Γ γ v, ∀ t : I, 0 < t →
        Φ (polarDiscPoint t w) ∈ range (spoke γ a.1)) :
    {w : Circle | polarRimMap Φ w ∈ e}.Finite := by
  classical
  let W := {w : Circle | polarRimMap Φ w ∈ e}
  choose a ha using fun w : W => hlabel w.1 w.2
  have hinj : Function.Injective a := by
    intro w z hwz
    apply Subtype.ext
    apply polar_direction_eq_of_same_halfedge hγ hp (a w) (ha w)
    rw [hwz]
    exact ha z
  let : Finite (halfEdges Γ γ v) := (finite_halfEdges Γ γ v).to_subtype
  let : Finite W := Finite.of_injective a hinj
  exact Set.toFinite W

/-- A polar chart may be chosen arbitrarily small with only finitely
many rim directions for each edge. -/
theorem exists_polar_chart_with_finite_edge_directions
    {S : Type u} [TopologicalSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    {O : Set S} (hOo : IsOpen O) (hvO : v ∈ O) :
    ∃ Ψ : C(ClosedUnitDisc, S), IsPolar Γ v Ψ ∧ range Ψ ⊆ O ∧
      ∀ e ∈ Γ.E, {w : Circle | polarRimMap Ψ w ∈ e}.Finite := by
  let : T2Space S := hS.2.1
  obtain ⟨Ψ, hΨ, hΨO, hlabel⟩ :=
    exists_polar_chart_with_unique_edge_end_labels hS hγ hv hp hOo hvO
  refine ⟨Ψ, hΨ, hΨO, ?_⟩
  intro e he
  exact finite_polar_edge_directions_of_labels hγ hΨ
    (fun w hw => (hlabel e he w hw).exists)

end GraphMinor.GM06
