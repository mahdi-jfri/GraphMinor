module

public import GraphMinor.GM06.Alg34DualIncidence
public import GraphMinor.GM06.DiscRegions
import GraphMinor.GM11.Regions

/-!
# Interpreting region labels as vertices of an actual disc dual

A disc dual has exactly one vertex in each primal region, and every
dual vertex belongs to such a region. The supplied primal region
bijection therefore labels all dual vertices bijectively. This map is
used only in correctness proofs. The finite dual endpoint operation
continues to read only the supplied incidence lists.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

/-- Interpret a supplied primal region label as its unique vertex in an
actual disc dual. This is a geometric correctness map, not program input. -/
noncomputable def dualVertexLabel (h : GM06DrawingRep x G Δ) (hd : IsDiscDualDrawing G D)
    (r : Fin x.regions.length) : D.V :=
  ⟨(hd.2.2.1 (h.region r).val (h.region r).property).exists.choose,
    (hd.2.2.1 (h.region r).val (h.region r).property).exists.choose_spec.2⟩

/-- The interpreted dual vertex belongs to exactly its supplied primal region. -/
theorem dualVertexLabel_mem_region (h : GM06DrawingRep x G Δ) (hd : IsDiscDualDrawing G D)
    (r : Fin x.regions.length) : (h.dualVertexLabel hd r).val ∈ (h.region r).val :=
  (hd.2.2.1 (h.region r).val (h.region r).property).exists.choose_spec.1

/-- The supplied primal regions label every actual dual vertex exactly once. -/
theorem dualVertexLabel_bijective (h : GM06DrawingRep x G Δ) (hd : IsDiscDualDrawing G D) :
    Function.Bijective (h.dualVertexLabel hd) := by
  constructor
  · intro r s hrs
    apply h.region.injective
    apply Subtype.ext
    have hr := h.dualVertexLabel_mem_region hd r
    rw [congrArg Subtype.val hrs] at hr
    exact GM11.region_eq_of_mem (h.region r).property (h.region s).property hr
      (h.dualVertexLabel_mem_region hd s)
  · intro w
    obtain ⟨r, hr, hwr⟩ := hd.2.2.2.1 w.val w.property
    obtain ⟨a, ha⟩ := h.region.surjective ⟨r, hr⟩
    refine ⟨a, Subtype.ext ?_⟩
    have hwa : w.val ∈ (h.region a).val := by rw [ha]; exact hwr
    exact (hd.2.2.1 (h.region a).val (h.region a).property).unique
      ⟨h.dualVertexLabel_mem_region hd a, (h.dualVertexLabel hd a).property⟩ ⟨hwa, w.property⟩

/-- The geometric bijection identifying finite region labels with dual vertices. -/
@[expose] noncomputable def dualVertexEquiv (h : GM06DrawingRep x G Δ)
    (hd : IsDiscDualDrawing G D) : Fin x.regions.length ≃ D.V :=
  Equiv.ofBijective (h.dualVertexLabel hd) (h.dualVertexLabel_bijective hd)

end GraphMinor.Compute.GM06DrawingRep
