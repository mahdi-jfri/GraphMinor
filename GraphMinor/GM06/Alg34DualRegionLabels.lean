module

public import GraphMinor.GM06.Alg34DualVertices
public import GraphMinor.Compute.GM06Alg34DualRegions
import GraphMinor.GM11.Regions

/-!
# Interpreting primal vertex labels as regions of the disc dual

Each original vertex lies in the complement of the dual drawing and
therefore determines one dual region. The disc-dual separation condition
makes these regions distinct. The double-dual theorem gives a primal
vertex in every dual region, proving that this correspondence is onto.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

/-- Interpret one primal vertex as the dual region containing it. -/
@[expose] noncomputable def dualRegionLabel (h : GM06DrawingRep x G Δ)
    (hd : IsDiscDualDrawing G D) (v : Fin x.n) : D.R :=
  ⟨connectedComponentIn (univ \ D.U) (h.vertex v).val,
    (hd.connectedComponentIn_mem_dual_R (h.vertex v).property).1⟩

/-- The represented original vertex belongs to its interpreted dual region. -/
theorem vertex_mem_dualRegionLabel (h : GM06DrawingRep x G Δ) (hd : IsDiscDualDrawing G D)
    (v : Fin x.n) : (h.vertex v).val ∈ (h.dualRegionLabel hd v).val :=
  (hd.connectedComponentIn_mem_dual_R (h.vertex v).property).2

/-- Primal vertex labels correspond bijectively to the actual dual regions. -/
theorem dualRegionLabel_bijective (h : GM06DrawingRep x G Δ) (hS : IsClosedDiscSpace S)
    (hconn : IsGraphConnected G.toGraph) (hd : IsDiscDualDrawing G D) :
    Function.Bijective (h.dualRegionLabel hd) := by
  constructor
  · intro v w hvw
    apply h.vertex.injective
    apply Subtype.ext
    exact hd.2.2.2.2.2.1 (h.vertex v).val (h.vertex v).property
      (h.vertex w).val (h.vertex w).property (congrArg Subtype.val hvw)
  · intro r
    obtain ⟨v, ⟨hvr, hv⟩, _⟩ := hd.exists_unique_vertex_in_dual_region hS hconn r.property
    obtain ⟨a, ha⟩ := h.vertex.surjective ⟨v, hv⟩
    refine ⟨a, Subtype.ext ?_⟩
    have har : (h.vertex a).val ∈ r.val := by rw [ha]; exact hvr
    exact GM11.region_eq_of_mem (h.dualRegionLabel hd a).property r.property
      (h.vertex_mem_dualRegionLabel hd a) har

/-- The correctness bijection identifying finite primal vertices with dual regions. -/
@[expose] noncomputable def dualRegionEquiv (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hconn : IsGraphConnected G.toGraph) (hd : IsDiscDualDrawing G D) :
    Fin x.n ≃ D.R :=
  Equiv.ofBijective (h.dualRegionLabel hd) (h.dualRegionLabel_bijective hS hconn hd)

end GraphMinor.Compute.GM06DrawingRep
