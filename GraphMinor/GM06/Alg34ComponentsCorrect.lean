module

public import GraphMinor.GM06.Alg34ComponentCover

/-!
# Correctness of the finite component branches

The computed roots enumerate exactly the drawing components. With no
split block, the computed induced division is precisely each component's
part of the original division. Apply VI (3.3)(iv) to that enumeration
and transport each component problem through its explicit payload
representation. The result refers only to the computed branch inputs.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- The finite component branching used in (3.4) preserves feasibility,
by the proved equivalence (3.3)(iv) on the exact canonical components. -/
theorem componentInputs_feasible_iff (h : GM06DrawingRep x G Δ)
    (hs : x.hasSplitBlock = false) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) (hk : 2 ≤ x.componentRoots.length) :
    IsFeasible x.graph x.divisionSet ↔
      ∀ i : Fin x.componentRoots.length,
        IsFeasible (x.componentData (x.componentRoots.get i)).graph
          (x.componentData (x.componentRoots.get i)).divisionSet := by
  let C := fun i : Fin x.componentRoots.length =>
    GM06.compOf G.toGraph (h.vertex (x.componentRoots.get i)).val
  let D := fun i : Fin x.componentRoots.length => {δ ∈ Δ | δ ⊆ (C i).vertexSet}
  have hpaper := theorem_3_3_iv G Δ x.componentRoots.length C D hk hD hbd
    h.componentRoot_get_injective.injOn h.componentRoot_get_range (fun _ => rfl)
    (fun δ hδ => h.division_subset_root_component hs hD hδ)
  have hbranch : ∀ i, IsFeasible (C i) (D i) ↔
      IsFeasible (x.componentData (x.componentRoots.get i)).graph
        (x.componentData (x.componentRoots.get i)).divisionSet := by
    intro i
    obtain ⟨hi⟩ := h.componentData_rep hs hD (x.componentRoots.get i)
    have hDi : IsDivision (D i) :=
      ⟨hD.1.subset (fun _ hδ => hδ.1), fun δ hδ => hD.2.1 δ hδ.1,
        hD.2.2.subset (fun _ hδ => hδ.1)⟩
    have ht := hi.feasible_iff hDi
    rw [induceDrawing_toGraph_of_component G
      (isGraphComponent_compOf (h.vertex (x.componentRoots.get i)).property)] at ht
    exact ht
  exact (h.feasible_iff hD).symm.trans (hpaper.trans (forall_congr' hbranch))

end GraphMinor.Compute.GM06DrawingRep
