module

public import GraphMinor.GM07.Defs
public import GraphMinor.GM07.CutStages
import GraphMinor.GM08.Section18SchismGraph
import GraphMinor.GM19.Section6Tri
import GraphMinor.GM07.Section46PullGraph

/-!
# Pulling a drawing back across a schism cut

Represent the schism by a proper drawing with no isolated vertices. The
cut along its support is then a cut along that drawing. The proved graph
pullback theorem gives exactly the preimages of the original underlying
set and vertex set, and each new edge is the preimage of an old edge.
This proves the drawing assertion before VIII (18.1), page 285.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- A schism is the support of a proper drawing with no isolated vertices.
Its boundary contacts are vertices in the finite graph representation
(VIII Section 18, page 285). -/
theorem exists_drawing_of_schism {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) {F : Set S} (hF : GM07.IsSchism F) :
    ∃ K : Drawing S, K.U = F ∧ K.IsProper ∧ GM07.HasNoIsolatedVertices K := by
  have : T2Space S := hS.2.1
  obtain ⟨V, E, hg, hno, hgr, hmarks⟩ := exists_graph_of_schism hS hF
  let K := hg.toDrawing
  refine ⟨K, hgr, ?_, ?_⟩
  · rintro x ⟨hxbd, hxK⟩
    exact hmarks ⟨hgr ▸ hxK, hxbd⟩
  · intro x hxV
    obtain ⟨e, he, hxe⟩ := hno hxV
    have heK : e \ V ∈ K.E := by
      change e \ V ∈ arcComponentsIn (gr V E \ V)
      rw [GM19.IsGraphD.arcComponents_eq hg]
      exact mem_image_of_mem _ he
    refine ⟨e \ V, heK, hxV, Or.inl heK, ?_⟩
    rw [GM19.IsGraphD.closure_diff hg he]
    exact hxe

/-- The pullback of a proper drawing across a normal schism is a proper
drawing, with exactly the preimage underlying set and vertex set. This is
the assertion before VIII (18.1), page 285. Each edge is also a preimage
of an original edge. -/
theorem exists_pullback_drawing_of_schism_cut {S Y : Type w}
    [TopologicalSpace S] [TopologicalSpace Y] (hS : IsSurface S)
    {F : Set S} (hF : GM07.IsSchism F) {ψ : Y → S}
    (hcut : GM07.IsCutAlongSet F ψ) (G : Drawing S) (hG : G.IsProper)
    (hn : G.IsNormal F) :
    ∃ G' : Drawing Y, GM07.IsPullbackDrawing ψ G G' ∧ G'.IsProper ∧
      ∀ e' ∈ G'.E, ∃ e ∈ G.E, e' = ψ ⁻¹' e := by
  obtain ⟨K, hKU, hKproper, hKno⟩ := exists_drawing_of_schism hS hF
  have hcutK : GM07.IsCutAlongSet K.U ψ := hKU.symm ▸ hcut
  have hnormal : G.IsNormal K.U := hKU.symm ▸ hn
  exact GM07.exists_pullback_graph hS (hcutK.isCutAlongGraph hKproper hKno) hG hnormal

end GraphMinor.GM08
