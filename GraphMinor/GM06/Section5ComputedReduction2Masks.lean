module

public import GraphMinor.GM06.Section5ComputedReduction2

/-!
# Interpreting retained labels as the reduced drawing

The RAM deletion step of VI (5.7), page 133, removes the selected
component from the live label set. Injective vertex labels make
this finite-set difference exactly the vertex set retained by
Reduction 2. Thus the computed masks describe the same induced
drawing as the separation proof.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.Compute

/-- Removing labelled vertices from the represented live set agrees
with taking the difference of the finite live-label sets. -/
theorem live_vertex_image_sdiff {S : Type*} {n : ℕ} (vertex : Fin n ↪ S)
    (A R : Finset (Fin n)) (V : Set S) (hV : V = vertex '' (A : Set (Fin n))) :
    V \ (vertex '' (R : Set (Fin n)) ∩ V) = vertex '' ((A \ R : Finset (Fin n)) : Set (Fin n)) := by
  ext a
  constructor
  · rintro ⟨haV, haX⟩
    obtain ⟨v, hvA, hva⟩ := hV ▸ haV
    refine ⟨v, Finset.mem_sdiff.mpr ⟨hvA, ?_⟩, hva⟩
    intro hvR
    exact haX ⟨⟨v, hvR, hva⟩, haV⟩
  · rintro ⟨v, hv, rfl⟩
    have hvA := (Finset.mem_sdiff.mp hv).1
    have haV : vertex v ∈ V := hV ▸ ⟨v, hvA, rfl⟩
    refine ⟨haV, ?_⟩
    rintro ⟨⟨r, hrR, hrv⟩, _⟩
    exact (Finset.mem_sdiff.mp hv).2 (vertex.injective hrv ▸ hrR)

/-- The live-label difference installed by the computed component
branch is the actual induced drawing in Reduction 2. -/
theorem exists_reduction2_of_computed_live_masks
    {k n : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (A : Finset (Fin n)) (hV : G.V = vertex '' (A : Set (Fin n)))
    (cut source : Fin n) (i : Fin k) (hcut : vertex cut = cylinderM1Point k i)
    (hsource : source ∈ A) (Q : Finset (Fin n))
    (hprotect : ∀ j : Fin k, (L.pathDrawing j).V ⊆ vertex '' (Q : Set (Fin n)))
    (hzero : (Q ∩ GraphMinor.Compute.reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0) :
    let R := GraphMinor.Compute.reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source
    ∃ M : CylinderLinkage k (induceDrawing G (vertex '' ((A \ R : Finset (Fin n)) : Set (Fin n)))),
      IsCylinderSection5Drawing k (induceDrawing G (vertex '' ((A \ R : Finset (Fin n)) : Set (Fin n)))) ∧
      Section5Reduction2Step k G L
        (induceDrawing G (vertex '' ((A \ R : Finset (Fin n)) : Set (Fin n)))) M := by
  let H : SimpleGraph (Fin n) := (gm06PuncturedGraphData tagged cut).vertexGraph
  let R : Finset (Fin n) := GraphMinor.Compute.reachSet H source
  have hR : (R : Set (Fin n)) =
      {r | H.Reachable source r} := by
    ext r
    exact GraphMinor.Compute.mem_reachSet H source r
  have hret : G.V \ (vertex ''
      {r | H.Reachable source r} ∩ G.V) =
        vertex '' ((A \ R : Finset (Fin n)) : Set (Fin n)) := by
    rw [← hR]
    exact live_vertex_image_sdiff vertex A R G.V hV
  have hsourceV : vertex source ∈ G.V := hV ▸ ⟨source, hsource, rfl⟩
  have hh := exists_reduction2_of_computed_component L hG tagged vertex edge hlinks hcover
    cut source i hcut hsourceV Q hprotect hzero
  change ∃ M : CylinderLinkage k (induceDrawing G
      (G.V \ (vertex '' {r : Fin n | H.Reachable source r} ∩ G.V))),
    IsCylinderSection5Drawing k (induceDrawing G
      (G.V \ (vertex '' {r : Fin n | H.Reachable source r} ∩ G.V))) ∧
    Section5Reduction2Step k G L (induceDrawing G
      (G.V \ (vertex '' {r : Fin n | H.Reachable source r} ∩ G.V))) M at hh
  rw [hret] at hh
  exact hh

end GraphMinor.GM06
