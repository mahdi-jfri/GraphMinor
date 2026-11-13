module

public import GraphMinor.GM06.Section5ComputedComponentSeparation
public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5LinkageEnds
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# A computed linkage-disjoint component gives Reduction 2

For VI (5.7), page 133, the component scan counts protected
linkage vertices. A zero count makes its live component disjoint
from every linkage path's vertices. Keep the induced drawing on
the remaining vertices. The computed attachment property gives
the separation in Reduction 2, and the unchanged paths remain a
linkage in the smaller proper cylinder drawing.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.Compute GraphMinor.GM11

/-- A live computed component with zero protected intersection gives
an actual Reduction 2, preserving the supplied linkage paths. -/
theorem exists_reduction2_of_computed_component
    {k n : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (cut source : Fin n) (i : Fin k) (hcut : vertex cut = cylinderM1Point k i)
    (hsourceV : vertex source ∈ G.V) (Q : Finset (Fin n))
    (hprotect : ∀ j : Fin k, (L.pathDrawing j).V ⊆ vertex '' (Q : Set (Fin n)))
    (hzero : (Q ∩ GraphMinor.Compute.reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0) :
    let X := vertex '' {r | (gm06PuncturedGraphData tagged cut).vertexGraph.Reachable source r} ∩ G.V
    ∃ M : CylinderLinkage k (induceDrawing G (G.V \ X)),
      IsCylinderSection5Drawing k (induceDrawing G (G.V \ X)) ∧
      Section5Reduction2Step k G L (induceDrawing G (G.V \ X)) M := by
  classical
  let H : SimpleGraph (Fin n) := (gm06PuncturedGraphData tagged cut).vertexGraph
  let X := vertex '' {r | H.Reachable source r} ∩ G.V
  let R := induceDrawing G (G.V \ X)
  have hzero' : (Q ∩ GraphMinor.Compute.reachSet H source).card = 0 := hzero
  have hcutQ : cut ∈ Q := by
    obtain ⟨q, hq, hvq⟩ := hprotect i (isPathDrawing_end_vertices (L.isPath i)).1
    have hqc : q = cut := vertex.injective (hvq.trans hcut.symm)
    exact hqc ▸ hq
  have hsource : source ≠ cut := by
    intro h
    have hreach : H.Reachable source cut := h ▸ SimpleGraph.Reachable.refl source
    have hpos : 0 < (Q ∩ GraphMinor.Compute.reachSet H source).card := Finset.card_pos.mpr
      ⟨cut, Finset.mem_inter.mpr ⟨hcutQ, (GraphMinor.Compute.mem_reachSet H source cut).mpr hreach⟩⟩
    exact hpos.ne' hzero'
  have hverts (j : Fin k) : (L.pathDrawing j).V ⊆ G.V \ X := by
    intro a ha
    refine ⟨(L.isSubdrawing j).1.1 ha, ?_⟩
    rintro ⟨⟨r, hr, hvr⟩, _⟩
    obtain ⟨q, hq, hvq⟩ := hprotect j ha
    have hrq : r = q := vertex.injective (hvr.trans hvq.symm)
    have hreach : H.Reachable source q := hrq ▸ hr
    have hpos : 0 < (Q ∩ GraphMinor.Compute.reachSet H source).card := Finset.card_pos.mpr
      ⟨q, Finset.mem_inter.mpr ⟨hq, (GraphMinor.Compute.mem_reachSet H source q).mpr hreach⟩⟩
    exact hpos.ne' hzero'
  have hPiR (j : Fin k) : (L.pathDrawing j).IsSubdrawing R := by
    refine ⟨?_, ?_⟩
    · rw [show R.V = G.V \ X from induceDrawing_V G sdiff_subset]
      exact hverts j
    · intro e he
      rw [show R.E = {e ∈ G.E | closure e ∩ G.V ⊆ G.V \ X} from induceDrawing_E G _]
      refine ⟨(L.isSubdrawing j).1.2 he, ?_⟩
      rw [← (L.isSubdrawing j).1.closure_inter_V he]
      exact fun a ha => hverts j ha.2
  let M : CylinderLinkage k R := {
    pathDrawing := L.pathDrawing
    curve := L.curve
    isSubdrawing := fun j => ⟨hPiR j, (hPiR j).U_subset⟩
    isPath := L.isPath
    curve_parametrizes := L.curve_parametrizes
    curve_one_mem := L.curve_one_mem
    pairwise_disjoint := L.pairwise_disjoint }
  have hRG : R.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hR := isCylinderSection5Drawing_of_contains_linkage L hG hRG hPiR
  obtain ⟨T, hsep, hsepV, hneq⟩ := exists_separation_of_computed_punctured_component G
    tagged vertex edge hlinks hcover cut source hsource hsourceV
  have hTG : T.IsSubdrawing G := ⟨hsep.2.1.vertexSet_mono, hsep.2.1.edgeSet_mono⟩
  refine ⟨M, hR, i, T, hsep, hRG.U_subset, hTG.U_subset, ?_, hneq, rfl, rfl⟩
  simpa only [hcut] using hsepV

end GraphMinor.GM06
