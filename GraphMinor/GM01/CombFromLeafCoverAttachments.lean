module

public import GraphMinor.GM01.CombFromForestAttachments
public import Mathlib.Data.Fintype.Card
import GraphMinor.GM01.LeafCoverPigeonhole
import GraphMinor.GM09.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Selecting the forbidden comb from the binary leaf cover

Graph Minors I, page 60, rules out `δ * 2^γ` clean disjoint
attachments to the chosen forest-tree supports. The binary leaf
paths cover the root support. Assign each attachment endpoint to a
covering leaf path and select exactly `δ` on one of them. Reindex
this selected finite family by `Fin δ` and apply the proved actual
path contraction. All paths, supports, minor models, and clean
intersection conditions are retained by this restriction.
-/

public section

namespace GraphMinor.GM01

open Set Graph Function GraphMinor.GM09

/-- The leaf-cover and pigeonhole contraction on page 60 of GM01.
The covering paths are the actual paths constructed from the root
subdivision. Every selected arm has just the printed forest-tree minor. -/
theorem rootedPathComb_of_many_leaf_cover_attachments {α β I : Type*}
    [Nonempty β] [Fintype I] {γ δ : ℕ} (hγ : 0 < γ) (hδ : 0 < δ)
    (G : RootedGraph α β) (hVfin : V(G.graph).Finite) (hEfin : E(G.graph).Finite)
    (S : Set α)
    (Q : {leaf : List Bool // leaf.length = γ} → Graph α β)
    (last : {leaf : List Bool // leaf.length = γ} → α)
    (hQ : ∀ leaf, IsGraphPathWithEnds G.graph (Q leaf) G.root.val (last leaf))
    (hQS : ∀ leaf, V(Q leaf) ⊆ S) (hCover : S ⊆ ⋃ leaf, V(Q leaf))
    (B : I → RootedGraph α β) (hBG : ∀ i, (B i).graph ≤ G.graph)
    (hBC : ∀ i, GraphConnected (B i).graph)
    (hMinor : ∀ i, IsIsoMinor (forestTreeGraph (γ - 1)) (B i).graph)
    (hDis : ∀ i, Disjoint S V((B i).graph))
    (hBD : Pairwise fun i j ↦ Disjoint V((B i).graph) V((B j).graph))
    (a : I → α) (hA : ∀ i, a i ∈ S) (P : I → Graph α β)
    (hP : ∀ i, IsGraphPathWithEnds G.graph (P i) (a i) (B i).root.val)
    (hPS : ∀ i, V(P i) ∩ S = {a i})
    (hSelf : ∀ i, V(P i) ∩ V((B i).graph) = {(B i).root.val})
    (hOther : ∀ i j, i ≠ j → Disjoint V(P i) V((B j).graph))
    (hPP : Pairwise fun i j ↦ Disjoint V(P i) V(P j))
    (hCard : Fintype.card I = δ * 2 ^ γ) :
    HasRootedMinor (rootedPathComb γ δ hδ) G := by
  classical
  have hHits : ∀ i ∈ (Finset.univ : Finset I), ∃ leaf, a i ∈ V(Q leaf) := by
    intro i _
    exact mem_iUnion.mp (hCover (hA i))
  obtain ⟨leaf,J,hSub,hSize,hHit⟩ := exists_attachment_subset_on_binary_leaf_cover
    (Finset.univ : Finset I) a (fun leaf ↦ V(Q leaf)) hHits
    (by simpa only [Finset.card_univ] using hCard)
  let e : Fin δ ≃ J := (Finset.equivFinOfCardEq hSize).symm
  let f : Fin δ → I := fun i ↦ (e i).val
  have hf : Injective f := fun _ _ h ↦ e.injective (Subtype.ext h)
  have hA' : ∀ i, a (f i) ∈ V(Q leaf) := fun i ↦ hHit (f i) (e i).property
  have hPQ : ∀ i, V(P (f i)) ∩ V(Q leaf) = {a (f i)} := by
    intro i
    apply Subset.antisymm
    · rintro x ⟨hxP,hxQ⟩
      exact hPS (f i) ▸ ⟨hxP,hQS leaf hxQ⟩
    · exact singleton_subset_iff.mpr ⟨(hP (f i)).left_mem,hA' i⟩
  exact rootedPathComb_of_forest_attachments_on_path hγ hδ G hVfin hEfin (hQ leaf)
    (fun i ↦ B (f i)) (fun i ↦ hBG (f i)) (fun i ↦ hBC (f i)) (fun i ↦ hMinor (f i))
    (fun i ↦ (hDis (f i)).mono_left (hQS leaf)) (fun _ _ hij ↦ hBD (hf.ne hij))
    (fun i ↦ a (f i)) hA' (fun i ↦ P (f i)) (fun i ↦ hP (f i)) hPQ
    (fun i ↦ hSelf (f i)) (fun i j hij ↦ hOther (f i) (f j) (hf.ne hij))
    (fun _ _ hij ↦ hPP (hf.ne hij))

end GraphMinor.GM01
