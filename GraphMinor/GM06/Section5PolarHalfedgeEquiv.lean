module

public import GraphMinor.GM06.Section5PolarDirectionSurjective

/-!
# The geometric directed-end labels of a polar rim

For the rotation input in VI (5.7), page 133, a small polar chart
identifies the incident directed ends with all rim points that lie
on drawing edges. The forward map uses the unique direction of
each end. Every edge direction has a label, so the map is onto.
Uniqueness of labels makes it one-to-one. This is an interpretation
of ordinary drawing data, with no side-test conclusion as a field.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A ray carried by a directed end at positive radii also lies on
its spoke at the centre, since both start at that end vertex. -/
theorem polar_ray_range_subset_halfedge_spoke
    {S : Type u} [TopologicalSpace S] {Γ : Drawing S} {γ : Set S → I → S}
    {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (a : halfEdges Γ γ v) (w : Circle)
    (hw : ∀ t : I, 0 < t → Φ (polarDiscPoint t w) ∈ range (spoke γ a.1)) :
    range (polarRayMap Φ w) ⊆ range (spoke γ a.1) := by
  rintro _ ⟨r, rfl⟩
  by_cases hr : r = 0
  · subst r
    refine ⟨0, ?_⟩
    rw [spoke_zero, a.2.2, polarRayMap_zero, hp.centre]
  · exact hw r (unitInterval.pos_iff_ne_zero.mpr hr)

/-- The rim endpoint of a polar ray labelled by a directed end lies
on that end's edge. It cannot be the vertex at parameter zero. -/
theorem polar_rim_mem_edge_of_halfedge_ray
    {S : Type u} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (a : halfEdges Γ γ v) (w : Circle)
    (hw : ∀ t : I, 0 < t → Φ (polarDiscPoint t w) ∈ range (spoke γ a.1)) :
    polarRimMap Φ w ∈ a.1.1 := by
  obtain ⟨r, hr⟩ := hw 1 zero_lt_one
  have hr0 : 0 < r := unitInterval.pos_iff_ne_zero.mpr (by
    rintro rfl
    have hh : Φ (polarDiscPoint 1 w) = Φ polarCentre := by
      rw [← hr, spoke_zero, a.2.2, hp.centre]
    exact polarDiscPoint_one_ne_centre w (hp.inj hh))
  exact hr ▸ spoke_mem_edge hγ a.2.1 hr0

/-- Unique directed-end labels in a given chart give the rim bijection. -/
theorem exists_halfedge_equiv_of_polar_ray_labels
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (hlabel : ∀ e ∈ Γ.E, ∀ w : Circle, polarRimMap Φ w ∈ e →
      ∃! a : halfEdges Γ γ v, ∀ t : I, 0 < t →
        Φ (polarDiscPoint t w) ∈ range (spoke γ a.1)) :
    ∃ d : halfEdges Γ γ v ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e},
      ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).1) ∈ range (spoke γ a.1) := by
  classical
  have hdir (a : halfEdges Γ γ v) : ∃! w : Circle, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t w) ∈ range (spoke γ a.1) :=
    exists_unique_polar_direction_of_halfedge hγ hv hp
      (fun e he w hw => (hlabel e he w hw).exists) a
  let H := halfEdges Γ γ v
  let W := {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e}
  let d : H → Circle := fun a => (hdir a).choose
  have hd (a : H) : ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a)) ∈ range (spoke γ a.1) :=
    (hdir a).choose_spec.1
  have hdW (a : H) : d a ∈ W :=
    ⟨a.1.1, a.2.1, polar_rim_mem_edge_of_halfedge_ray hγ hp a (d a) (hd a)⟩
  let d' : H → W := fun a => ⟨d a, hdW a⟩
  have hi : Function.Injective d' := by
    intro a b hab
    have hda : d a = d b := congrArg Subtype.val hab
    have hb : ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a)) ∈ range (spoke γ b.1) := by
      rw [hda]
      exact hd b
    exact (hlabel a.1.1 a.2.1 (d a)
      (polar_rim_mem_edge_of_halfedge_ray hγ hp a (d a) (hd a))).unique (hd a) hb
  have hs : Function.Surjective d' := by
    intro w
    obtain ⟨e, he, hw⟩ := w.2
    obtain ⟨a, ha, _⟩ := hlabel e he w.1 hw
    refine ⟨a, Subtype.ext ?_⟩
    exact (hdir a).unique (hd a) ha
  let e : H ≃ W := Equiv.ofBijective d' ⟨hi, hs⟩
  exact ⟨e, hd⟩


/-- A sufficiently small polar chart identifies all incident directed
ends with its edge directions, by the positive radial segments. -/
theorem exists_polar_chart_with_halfedge_equiv
    {S : Type u} [TopologicalSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    {O : Set S} (hOo : IsOpen O) (hvO : v ∈ O) :
    ∃ Ψ : C(ClosedUnitDisc, S), IsPolar Γ v Ψ ∧ range Ψ ⊆ O ∧
      ∃ d : halfEdges Γ γ v ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Ψ w ∈ e},
        ∀ a, ∀ t : I, 0 < t → Ψ (polarDiscPoint t (d a).1) ∈ range (spoke γ a.1) := by
  let : T2Space S := hS.2.1
  obtain ⟨Ψ, hΨ, hΨO, hlabel, _⟩ :=
    exists_polar_chart_with_all_edge_end_directions hS hγ hv hp hOo hvO
  obtain ⟨d, hd⟩ := exists_halfedge_equiv_of_polar_ray_labels hγ hv hΨ hlabel
  exact ⟨Ψ, hΨ, hΨO, d, hd⟩

end GraphMinor.GM06
