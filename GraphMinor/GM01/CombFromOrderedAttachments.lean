module

public import GraphMinor.GM01.CombModelsOfBinaryArms
public import GraphMinor.GM09.Defs
import GraphMinor.GM01.OrderedPathSpinePieces
import GraphMinor.GM01.SpineAttachmentPrefixes

/-!
# The rooted comb from ordered attachments along a covering path

Graph Minors I, page 60, retains one covering path and its selected
attachments. Partition the covering path at the ordered attachment
vertices. Remove each attachment's final edge and add its prefix to
the corresponding spine piece. The resulting connected pieces and
the disjoint binary arms give the rooted comb by the proved branch
constructor. Every contraction in this construction uses the actual
paths and their clean intersections.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The page-60 rooted comb contraction for attachment vertices already
ordered along their common covering path. -/
theorem rootedPathComb_of_ordered_binary_attachments {α β : Type*} {γ δ N : ℕ}
    (hγ : 0 < γ) (hδ : 0 < δ) (hN : 0 < N) (G : RootedGraph α β)
    (v : Fin N → α) (hv : Injective v) (hV : ∀ i, v i ∈ V(G.graph))
    (hAdj : ∀ i j, j.val = i.val + 1 → G.graph.Adj (v i) (v j))
    (hRoot : G.root.val = v ⟨0,hN⟩) (t : Fin δ → Fin N) (ht : StrictMono t)
    (B : Fin δ → RootedGraph α β) (hBG : ∀ i, (B i).graph ≤ G.graph)
    (MB : ∀ i, RootedMinorModel (binaryRootedTree (γ - 1)) (B i))
    (hDis : ∀ i, Disjoint (range v) V((B i).graph))
    (hBD : Pairwise fun i j ↦ Disjoint V((B i).graph) V((B j).graph))
    (P : Fin δ → Graph α β)
    (hP : ∀ i, IsGraphPathWithEnds G.graph (P i) (v (t i)) (B i).root.val)
    (hPV : ∀ i, V(P i) ∩ range v = {v (t i)})
    (hSelf : ∀ i, V(P i) ∩ V((B i).graph) = {(B i).root.val})
    (hOther : ∀ i j, i ≠ j → Disjoint V(P i) V((B j).graph))
    (hPP : Pairwise fun i j ↦ Disjoint V(P i) V(P j)) :
    HasRootedMinor (rootedPathComb γ δ hδ) G := by
  obtain ⟨C,hCR,hCG,hCC,hCD,hCroot,hA,hSpine⟩ :=
    exists_spine_pieces_of_ordered_path_vertices hδ G.graph v hv hV hAdj t ht
  have hDisC : ∀ i j, Disjoint (C i) V((B j).graph) :=
    fun i j ↦ (hDis j).mono_left (hCR i)
  have hPC : ∀ i j, V(P i) ∩ C j ⊆ {v (t i)} := by
    intro i j x hx
    exact hPV i ▸ ⟨hx.1,hCR j hx.2⟩
  obtain ⟨D,hCDsub,hDG,hDC,hDD,hDB,hJoin,_⟩ :=
    exists_spine_pieces_with_attachment_prefixes G.graph C hCG hCC hCD B hDisC
      (fun i ↦ v (t i)) hA P hP hPC hSelf hOther hPP
  have hRootD : G.root.val ∈ D ⟨0,hδ⟩ := by
    rw [hRoot]
    exact hCDsub _ hCroot
  have hSpineD : ∀ i j, (pathGraph δ).Adj i j →
      ∃ e x, x ∈ D i ∧ ∃ y, y ∈ D j ∧ G.graph.IsLink e x y := by
    intro i j hij
    obtain ⟨e,x,hx,y,hy,he⟩ := hSpine i j hij
    exact ⟨e,x,hCDsub i hx,y,hCDsub j hy,he⟩
  exact ⟨rootedCombModelOfBinaryArms hγ hδ G D hDG hDC hDD hRootD hSpineD
    B hBG MB hDB hBD hJoin⟩

end GraphMinor.GM01
