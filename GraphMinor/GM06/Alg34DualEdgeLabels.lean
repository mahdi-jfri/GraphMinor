module

public import GraphMinor.GM06.Alg34DualRegionLabels

/-!
# Interpreting primal edge labels as edges of the actual dual

Compose the supplied primal edge bijection with the disc-dual edge
bijection. Its crossing and endpoint properties are exactly those in
the definition of a disc dual. This is a correctness map only. The
program's edge labels remain the original finite edge slots.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

/-- The edge bijection supplied by the actual disc-dual relation. -/
noncomputable def dualDrawingEdgeEquiv (hd : IsDiscDualDrawing G D) : G.E ≃ D.E :=
  hd.2.2.2.2.2.2.choose

/-- Interpret original finite edge slots as corresponding actual dual edges. -/
@[expose] noncomputable def dualEdgeEquiv (h : GM06DrawingRep x G Δ)
    (hd : IsDiscDualDrawing G D) : Fin x.ends.length ≃ D.E :=
  h.edge.trans (dualDrawingEdgeEquiv hd)

/-- Each interpreted dual edge has precisely the crossing and region-end
properties in the definition of the actual disc dual. -/
theorem dualEdgeEquiv_spec (h : GM06DrawingRep x G Δ) (hd : IsDiscDualDrawing G D)
    (e : Fin x.ends.length) :
    ((h.dualEdgeEquiv hd e).val ∩ G.U = (h.dualEdgeEquiv hd e).val ∩ (h.edge e).val) ∧
    ((h.edge e).val ∩ D.U = (h.edge e).val ∩ (h.dualEdgeEquiv hd e).val) ∧
    ((h.dualEdgeEquiv hd e).val ∩ (h.edge e).val).ncard = 1 ∧
    (∀ r' ∈ D.R, D.EdgeRegionIncident (h.dualEdgeEquiv hd e).val r' →
      (r' ∩ (h.edge e).val).Nonempty) ∧
    (∀ r₁ ∈ G.R, ∀ r₂ ∈ G.R, ∀ w₁ ∈ r₁ ∩ D.V, ∀ w₂ ∈ r₂ ∩ D.V,
      D.toGraph.IsLink (h.dualEdgeEquiv hd e).val w₁ w₂ ↔
        G.EdgeRegionIncident (h.edge e).val r₁ ∧ G.EdgeRegionIncident (h.edge e).val r₂ ∧
        ∀ r ∈ G.R, G.EdgeRegionIncident (h.edge e).val r → r = r₁ ∨ r = r₂) :=
  hd.2.2.2.2.2.2.choose_spec (h.edge e)

end GraphMinor.Compute.GM06DrawingRep
