module

public import GraphMinor.GM01.CombFromLeafCoverAttachments
public import GraphMinor.GM01.BinarySubdivisionLeafCover

/-!
# The attachment contraction on the chosen root subdivision

This combines the constructions in the paragraph before (5.1) on
page 60 of Graph Minors I. The actual binary subdivision and its
separate root path supply the leaf-path cover. Pigeonhole selects
`δ` attachment paths on one member, and their attached forest-tree
minors give the rooted comb. Thus `δ * 2^γ` clean disjoint
attachments are impossible when that rooted comb is excluded.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The complete subdivision/leaf-cover/attachment contraction in
GM01, page 60, immediately before the application of (2.9). -/
theorem rootedPathComb_of_many_binary_subdivision_attachments {α β I : Type*}
    [Nonempty β] [Fintype I] {γ δ : ℕ} (hγ : 0 < γ) (hδ : 0 < δ)
    (G : RootedGraph α β) (hVfin : V(G.graph).Finite) (hEfin : E(G.graph).Finite)
    {N R : Graph α β} (hNG : N ≤ G.graph)
    {c : (binaryTree γ).verts → α} (hc : Injective c)
    {P₀ : (binaryTree γ).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P₀ e))
    (hPaths : ∀ e : (binaryTree γ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P₀ e) (c a) (c b) ∧ V(P₀ e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (binaryTree γ).coe.edgeSet, e ≠ f → V(P₀ e) ∩ V(P₀ f) ⊆ range c)
    (hR : IsGraphPathWithEnds G.graph R G.root.val (c ⟨[],binaryTree_root_mem γ⟩))
    (hMeet : V(R) ∩ V(N) = {c ⟨[],binaryTree_root_mem γ⟩})
    (B : I → RootedGraph α β) (hBG : ∀ i, (B i).graph ≤ G.graph)
    (hBC : ∀ i, GraphConnected (B i).graph)
    (hMinor : ∀ i, IsIsoMinor (forestTreeGraph (γ - 1)) (B i).graph)
    (hDis : ∀ i, Disjoint (V(N) ∪ V(R)) V((B i).graph))
    (hBD : Pairwise fun i j ↦ Disjoint V((B i).graph) V((B j).graph))
    (a : I → α) (hA : ∀ i, a i ∈ V(N) ∪ V(R)) (P : I → Graph α β)
    (hP : ∀ i, IsGraphPathWithEnds G.graph (P i) (a i) (B i).root.val)
    (hPS : ∀ i, V(P i) ∩ (V(N) ∪ V(R)) = {a i})
    (hSelf : ∀ i, V(P i) ∩ V((B i).graph) = {(B i).root.val})
    (hOther : ∀ i j, i ≠ j → Disjoint V(P i) V((B j).graph))
    (hPP : Pairwise fun i j ↦ Disjoint V(P i) V(P j))
    (hCard : Fintype.card I = δ * 2 ^ γ) :
    HasRootedMinor (rootedPathComb γ δ hδ) G := by
  obtain ⟨Q,hQ,hQsub,hCover⟩ := exists_binary_subdivision_leaf_cover hNG hc hV hPaths hInter hR hMeet
  exact rootedPathComb_of_many_leaf_cover_attachments hγ hδ G hVfin hEfin
    (V(N) ∪ V(R)) Q (fun leaf ↦ c ⟨leaf.val,leaf.property.le⟩) hQ
    (fun leaf ↦ (hQsub leaf).vertexSet_mono) hCover B hBG hBC hMinor hDis hBD
    a hA P hP hPS hSelf hOther hPP hCard

end GraphMinor.GM01
