module

public import GraphMinor.GM06.Alg511RegionBoundary

/-!
# Simultaneous region labels and boundary incidence data

For the drawing input of VI (5.11), page 134, enumerate all actual
regions and list their incident original vertices and edges using
the same graph labels. Region finiteness and exact whole-edge
incidence hold before the linkage search. The lists and the region
bijection are existential coverage witnesses, not an encoder that
selects geometric data for the program.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set

/-- Every intended input has simultaneous finite region labels and
exact finite boundary incidence lists, with the supplied graph labels. -/
theorem alg511_exists_region_boundary_data {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (x : GM06SuccessorInput)
    (rep : GM06SuccessorGraphRep x G.toGraph) :
    ∃ (r : ℕ) (region : Fin r ≃ G.R)
      (vs : Fin r → List (Fin x.vertexCount))
      (es : Fin r → List (Fin rep.pairs.length)),
      ∀ i, (vs i).Nodup ∧ (es i).Nodup ∧ closure (region i).val \ (region i).val =
        {p | ∃ j ∈ vs i, (rep.vertex j).val = p} ∪ ⋃ j ∈ es i, (rep.edge j).val := by
  obtain ⟨r, ⟨region⟩⟩ := alg511_exists_region_labels hG
  choose vs es hvs hes hboundary using fun i : Fin r =>
    alg511_exists_region_boundary_labels hG x rep (region i).property
  exact ⟨r, region, vs, es, fun i => ⟨hvs i, hes i, hboundary i⟩⟩

end GraphMinor.GM06
