module

public import GraphMinor.GM19.CutDrawing
public import GraphMinor.GM19.CutMap
public import GraphMinor.Surface.Dissection
import GraphMinor.GM08.Section18LiftedGraph
import GraphMinor.GM08.Section18LiftedFaces
import GraphMinor.GM08.Section18CircleGraphSupport

/-!
# A dissection of the cut surface

Join the lifted graph to the lifted face family. Each face boundary is
a circle in that graph and therefore lies on its edges. This completes
the dissection construction, with unchanged face count and one extra
edge for each cut edge, in the proof of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- The word cut lifts a dissection to a dissection. Faces keep their
count and cut edges are doubled. This is the triangulation construction
and count used by VIII (18.2), page 286. -/
theorem exists_lifted_dissection_of_word_cut {S Y : Type} [TopologicalSpace S]
    [TopologicalSpace Y] [T2Space S] (hY : IsSurface Y)
    {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E 𝓕 : Set (Set S)}
    {A : Set S → unitInterval → S} {lab : Set S → ℕ}
    (hd : IsDissection V E 𝓕) (hw : WordEdges W f V E A lab)
    {D : Set (Set S)} (hDE : D ⊆ E) {ψ : Y → S}
    (hcm : GM19.IsCutMap ψ (⋃₀ D))
    (hlift : ∀ e ∈ D, ∃ r r', GM19.IsEdgeLift ψ (extI (A e)) (GM19.EndFine A D e) r r') :
    ∃ E' 𝓕', IsDissection (ψ ⁻¹' V) E' 𝓕' ∧
      ⋃₀ E' = ψ ⁻¹' ⋃₀ E ∧ E'.ncard = E.ncard + D.ncard ∧ 𝓕'.ncard = 𝓕.ncard := by
  have : T2Space Y := hY.2.1
  obtain ⟨E', hg', hgr', hedgesub, hE'⟩ := exists_lifted_graph_of_word_cut hY hw hDE hcm hlift
  have hclosed : IsClosed (⋃₀ D) := (hw.graph.fine.subset hDE).isClosed_sUnion
    (fun L hL => by obtain ⟨u, v, _, hl, _⟩ := hw.graph.edge L (hDE hL); exact hl.isCompact.isClosed)
  let 𝓕' := (fun Φ => closure (ψ ⁻¹' discInt Φ)) '' 𝓕
  obtain ⟨hfin, hF', hdisc, hcover, hbd, hint, hdisj, hcount⟩ :=
    lifted_faces_of_dissection hY hd hcm hclosed (sUnion_mono hDE)
  have hbdedges : ∀ Φ ∈ 𝓕', discBd Φ ⊆ ⋃₀ E' := by
    intro Φ hΦ
    apply oArc_subset_edges_of_subset_graph hg' (hdisc Φ hΦ).isOArc_discBd
    intro y hy
    rw [hgr']
    exact Or.inr (hbd Φ hΦ hy)
  have hedgeeq : ⋃₀ E' = ψ ⁻¹' ⋃₀ E := by
    apply subset_antisymm hedgesub
    intro y hy
    obtain ⟨Φ, hΦ, hyΦ⟩ := hcover.symm.subset (mem_univ y)
    have hybd : y ∈ discBd Φ := by
      by_contra hn
      exact disjoint_left.mp (hint Φ hΦ) ⟨hyΦ, hn⟩ hy
    exact hbdedges Φ hΦ hybd
  refine ⟨E', 𝓕', ⟨hg', hfin, hdisc, hcover, hbdedges, ?_, hdisj, hcount⟩, hedgeeq, hE', hF'⟩
  exact fun Φ hΦ => (hint Φ hΦ).mono_right hedgesub

end GraphMinor.GM08
