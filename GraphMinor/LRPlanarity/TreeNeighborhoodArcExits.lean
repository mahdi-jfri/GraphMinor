module

public import GraphMinor.Surface.ArcTools
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Exits from the endpoint polygons of an arc

Part IV, Section 7b of the planarity note cuts a cotree arc where it
leaves its source polygon and enters its target polygon. The compact
parameter interval gives a last source parameter and a first target
parameter. Continuity places the two image points on the respective
polygon boundaries. These statements use closed sets, so they apply to
the vertex polygons as well as to round vertex discs.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Topology

/-- The last point of a continuous arc in a closed set is on its frontier,
provided the arc starts in the set and ends outside it. -/
theorem exists_last_closed_set_exit {f : unitInterval → ℂ} (hf : Continuous f)
    {A : Set ℂ} (hA : IsClosed A) (hzero : f 0 ∈ A) (hone : f 1 ∉ A) :
    ∃ t : unitInterval, t < 1 ∧ f t ∈ frontier A ∧ ∀ s, t < s → f s ∉ A := by
  let K : Set unitInterval := f ⁻¹' A
  have hK : IsCompact K := (hA.preimage hf).isCompact
  obtain ⟨t, ht, hmax⟩ := hK.exists_isGreatest ⟨0, hzero⟩
  have ht1 : t < 1 := lt_of_le_of_ne t.2.2 (fun he => hone (he ▸ ht))
  have hout : ∀ s, t < s → f s ∉ A := fun s hts hs => hts.not_ge (hmax hs)
  refine ⟨t, ht1, ?_, hout⟩
  rw [frontier, hA.closure_eq]
  refine ⟨ht, ?_⟩
  intro hi
  have hO : f ⁻¹' interior A ∈ 𝓝 t := (isOpen_interior.preimage hf).mem_nhds hi
  have hcl : t ∈ closure (Ioi t) := by
    rw [closure_Ioi' (⟨1, ht1⟩ : (Ioi t).Nonempty)]
    exact le_rfl
  obtain ⟨s, hsO, hts⟩ := mem_closure_iff_nhds.mp hcl _ hO
  exact hout s hts (interior_subset hsO)

/-- The first point of a continuous arc in a closed set is on its frontier,
provided the arc starts outside the set and ends in it. -/
theorem exists_first_closed_set_entry {f : unitInterval → ℂ} (hf : Continuous f)
    {A : Set ℂ} (hA : IsClosed A) (hzero : f 0 ∉ A) (hone : f 1 ∈ A) :
    ∃ t : unitInterval, 0 < t ∧ f t ∈ frontier A ∧ ∀ s, s < t → f s ∉ A := by
  let K : Set unitInterval := f ⁻¹' A
  have hK : IsCompact K := (hA.preimage hf).isCompact
  obtain ⟨t, ht, hmin⟩ := hK.exists_isLeast ⟨1, hone⟩
  have ht0 : 0 < t := lt_of_le_of_ne t.2.1 (fun he => hzero (he.symm ▸ ht))
  have hout : ∀ s, s < t → f s ∉ A := fun s hst hs => hst.not_ge (hmin hs)
  refine ⟨t, ht0, ?_, hout⟩
  rw [frontier, hA.closure_eq]
  refine ⟨ht, ?_⟩
  intro hi
  have hO : f ⁻¹' interior A ∈ 𝓝 t := (isOpen_interior.preimage hf).mem_nhds hi
  have hcl : t ∈ closure (Iio t) := by
    rw [closure_Iio' (⟨0, ht0⟩ : (Iio t).Nonempty)]
    exact le_rfl
  obtain ⟨s, hsO, hst⟩ := mem_closure_iff_nhds.mp hcl _ hO
  exact hout s hst (interior_subset hsO)

end GraphMinor.LRPlanarity
