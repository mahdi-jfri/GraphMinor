module

public import GraphMinor.GM06.Section5PolarDirectionInjective
import GraphMinor.GM06.Section5PolarAngularProjection
import GraphMinor.GM06.Section5PolarEdgeAccess
import GraphMinor.GM06.Section5HalfEdgeConnected

/-!
# Every incident directed end has a polar rim direction

For the rotation input in VI (5.7), page 133, the rim directions
must account for all incident directed ends. Take a positive point
of a short half-spoke inside the polar chart and move radially to
the rim. The radial segment receives a directed-end label. At the
chosen short point that label must be the original end. The
injectivity result then gives a unique direction for each end.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- If polar edge rays have directed-end labels, each incident end
has a unique rim direction whose whole positive ray lies on that end. -/
theorem exists_unique_polar_direction_of_halfedge
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (hlabel : ∀ e ∈ Γ.E, ∀ w : Circle, polarRimMap Φ w ∈ e →
      ∃ a : halfEdges Γ γ v, ∀ t : I, 0 < t →
        Φ (polarDiscPoint t w) ∈ range (spoke γ a.1))
    (a : halfEdges Γ γ v) :
    ∃! w : Circle, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t w) ∈ range (spoke γ a.1) := by
  let V := (spoke γ a.1) ⁻¹' interior (range Φ)
  have hVo : IsOpen V := isOpen_interior.preimage (continuous_spoke hγ a.2.1)
  have h0V : (0 : I) ∈ V := by
    change spoke γ a.1 0 ∈ interior (range Φ)
    rw [spoke_zero, a.2.2]
    exact hp.nhd
  have h0cl : (0 : I) ∈ closure (Ioo (0 : I) 1) := by
    rw [closure_Ioo (zero_ne_one : (0 : I) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨t, htV, ht⟩ := mem_closure_iff.mp h0cl V hVo h0V
  have hye : spoke γ a.1 t ∈ a.1.1 := spoke_mem_edge hγ a.2.1 ht.1
  have hyv : spoke γ a.1 t ≠ v := fun hy =>
    edge_notMem_V a.2.1 hye (hy.symm ▸ hv)
  obtain ⟨q, _, _, hrepr⟩ := exists_polar_angular_projection hp
  obtain ⟨c, hc, hcy⟩ := hrepr (spoke γ a.1 t) ⟨interior_subset htV, hyv⟩
  let w := q (spoke γ a.1 t)
  have hw : polarRimMap Φ w ∈ a.1.1 := by
    apply (polar_ray_mem_atom_iff hp (Or.inl (Or.inr a.2.1))
      (polarDiscPoint_one_ne_centre w) c hc).mpr
    rw [discScale_polarDiscPoint_one, hcy]
    exact hye
  obtain ⟨b, hb⟩ := hlabel a.1.1 a.2.1 w hw
  obtain ⟨r, hr⟩ := hb c hc
  have hab : a = b := halfedge_eq_of_short_spoke_point hγ hv a b ht.1 ht.2
    (hcy.symm.trans hr.symm)
  subst b
  refine ⟨w, hb, ?_⟩
  intro z hz
  exact polar_direction_eq_of_same_halfedge hγ hp a hz hb

/-- A polar chart can be chosen inside any open neighbourhood so that
its incident directed ends and positive rim rays correspond uniquely. -/
theorem exists_polar_chart_with_all_edge_end_directions
    {S : Type u} [TopologicalSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    {O : Set S} (hOo : IsOpen O) (hvO : v ∈ O) :
    ∃ Ψ : C(ClosedUnitDisc, S), IsPolar Γ v Ψ ∧ range Ψ ⊆ O ∧
      (∀ e ∈ Γ.E, ∀ w : Circle, polarRimMap Ψ w ∈ e →
        ∃! a : halfEdges Γ γ v, ∀ t : I, 0 < t →
          Ψ (polarDiscPoint t w) ∈ range (spoke γ a.1)) ∧
      ∀ a : halfEdges Γ γ v, ∃! w : Circle, ∀ t : I, 0 < t →
        Ψ (polarDiscPoint t w) ∈ range (spoke γ a.1) := by
  let : T2Space S := hS.2.1
  obtain ⟨Ψ, hΨ, hΨO, hlabel⟩ :=
    exists_polar_chart_with_unique_edge_end_labels hS hγ hv hp hOo hvO
  refine ⟨Ψ, hΨ, hΨO, hlabel, ?_⟩
  intro a
  exact exists_unique_polar_direction_of_halfedge hγ hv hΨ
    (fun e he w hw => (hlabel e he w hw).exists) a

end GraphMinor.GM06
