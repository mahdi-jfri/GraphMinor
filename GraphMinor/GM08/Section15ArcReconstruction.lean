module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM08.Section14
public import GraphMinor.GM07.CutStages
import GraphMinor.GM08.Section15CutGraph
import GraphMinor.GM08.Section15CutRoots
import GraphMinor.GM08.Section15ArcPullback
import GraphMinor.GM08.Section15Reconstruction

/-!
# Reconstructing a graft after an arc cut

Use the old edge labels on the lifted drawing. Its boundary vertices are
its roots. The cutting map has paired fibres and the proved root rule,
so the finite identification theorem recovers the original graft. The
new graft embeds in the cut surface and satisfies the counted index
bound used for short tubes in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface Graph

universe w

/-- The graft on a pulled-back drawing reconstructs the old boundary-rooted
graft by root identifications and has index at most the old index plus
twice the number of vertices on the arc. This assembles the reconstruction
and index estimate in VIII (15.4), page 282. -/
theorem exists_graft_reconstruction_of_arc_cut {S Y : Type w}
    [TopologicalSpace S] [TopologicalSpace Y] (hS : IsSurface S)
    {F : Set S} {ψ : Y → S} (hcut : GM07.IsCutAlongSet F ψ) (hc : IsCutting ψ F)
    {G : Drawing S} {G' : Drawing Y} (hp : GM07.IsPullbackDrawing ψ G G')
    (hG' : G'.IsProper) (he : ∀ e' ∈ G'.E, ∃ e ∈ G.E, e' = ψ ⁻¹' e)
    (X : Graft S (Set S)) (hXG : X.G = G.toGraph) (hXT : X.T = G.V ∩ bd S) :
    ∃ A : Graft Y (Set S), EmbedsGraft Y A ∧
      A.index ≤ X.index + 2 * (G.V ∩ F).ncard ∧
      ∃ (n : ℕ) (Z : Graft Y (Set S)), ObtainedByVertexIdChain n A Z ∧ IsGraftIso Z X := by
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace Y := hcut.isSurface.1
  obtain ⟨K, i, hKV, hKE, hiv, hmap⟩ :=
    exists_cut_graph_with_old_edges hc.1 hc.1.isClosedMap hc.2.1 hp he
  let A : Graft Y (Set S) := {
    G := K
    T := G'.V ∩ bd Y
    T_subset := hKV.symm ▸ inter_subset_left
    finite_G := ⟨hKV.symm ▸ G'.finite_V, hKE.symm ▸ G.finite_edges⟩ }
  have hdraw : EmbedsGraft Y A := by
    refine ⟨{
      drawing := G'
      iso := i
      isProper := hG'
      T_subset_V := A.T_subset
      mem_bd_iff := ?_ }⟩
    intro v hv
    rw [hiv ⟨v, hv⟩]
    exact (and_iff_right (show v ∈ G'.V from hKV ▸ hv)).symm
  have hindex : A.index ≤ X.index + 2 * (G.V ∩ F).ncard := by
    change (G'.V ∩ bd Y).ncard ≤ X.T.ncard + 2 * (G.V ∩ F).ncard
    rw [hp.2, hXT]
    exact boundary_vertices_ncard_le_of_arc_cut G.finite_V hcut hc
  have hquot : X.G = A.G.map ψ := hXG.trans hmap.symm
  have hf : ∀ z, {y ∈ V(A.G) | ψ y = z}.ncard ≤ 2 := by
    intro z
    apply (ncard_le_ncard ?_ (hcut.finite_fiber z)).trans (cutting_fibre_ncard_le_two hc z)
    exact fun y hy => hy.2
  have hroot : ∀ y ∈ V(A.G), y ∈ A.T ↔
      ψ y ∈ X.T ∨ ∃ z ∈ V(A.G), z ≠ y ∧ ψ z = ψ y := by
    change ∀ y ∈ V(K), y ∈ G'.V ∩ bd Y ↔ _
    rw [hKV, hp.2, hXT]
    exact arc_cut_root_rule hcut hc
  obtain ⟨n, Z, hchain, hiso⟩ := exists_vertexIdChain_of_paired_fibres A X ψ hquot hf hroot
  exact ⟨A, hdraw, hindex, n, Z, hchain, hiso⟩

end GraphMinor.GM08
