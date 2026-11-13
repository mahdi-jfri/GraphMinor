module

public import GraphMinor.GM01.CombFromOrderedAttachments
import GraphMinor.GM01.PathVertexCoordinates
import GraphMinor.GM01.AttachmentOrder

/-!
# The comb contraction along an actual covering path

For Graph Minors I, page 60, the selected attachments arrive at
distinct vertices of one root-to-leaf path. Enumerate that actual
path, locate its attachment endpoints, and sort them by a permutation
of the selected indices. Reindex every arm and path by the same
permutation. The proved interval and prefix construction then gives
the forbidden rooted comb, retaining the original ambient root.
-/

public section

namespace GraphMinor.GM01

open Set Graph Function GraphMinor.GM09

/-- Clean disjoint attachments from one actual root path to disjoint
rooted binary arms give the rooted comb in the GM01 page-60 contraction.
The endpoint order is constructed from the path, not assumed. -/
theorem rootedPathComb_of_binary_attachments_on_path {α β : Type*} {γ δ : ℕ}
    (hγ : 0 < γ) (hδ : 0 < δ) (G : RootedGraph α β) {Q : Graph α β} {last : α}
    (hQ : IsGraphPathWithEnds G.graph Q G.root.val last)
    (B : Fin δ → RootedGraph α β) (hBG : ∀ i, (B i).graph ≤ G.graph)
    (MB : ∀ i, RootedMinorModel (binaryRootedTree (γ - 1)) (B i))
    (hDis : ∀ i, Disjoint V(Q) V((B i).graph))
    (hBD : Pairwise fun i j ↦ Disjoint V((B i).graph) V((B j).graph))
    (a : Fin δ → α) (hA : ∀ i, a i ∈ V(Q)) (P : Fin δ → Graph α β)
    (hP : ∀ i, IsGraphPathWithEnds G.graph (P i) (a i) (B i).root.val)
    (hPQ : ∀ i, V(P i) ∩ V(Q) = {a i})
    (hSelf : ∀ i, V(P i) ∩ V((B i).graph) = {(B i).root.val})
    (hOther : ∀ i j, i ≠ j → Disjoint V(P i) V((B j).graph))
    (hPP : Pairwise fun i j ↦ Disjoint V(P i) V(P j)) :
    HasRootedMinor (rootedPathComb γ δ hδ) G := by
  classical
  obtain ⟨N,hN,v,hv,hRange,hStart,hAdj⟩ := exists_path_vertex_coordinates hQ
  have hAinj : Injective a := by
    intro i j heq
    by_contra hij
    exact disjoint_left.mp (hPP hij) (hP i).left_mem (heq.symm ▸ (hP j).left_mem)
  have hPositions : ∀ i, ∃ k : Fin N, v k = a i := by
    intro i
    have hm : a i ∈ range v := hRange.symm ▸ hA i
    exact hm
  choose f hf using hPositions
  have hFinj : Injective f := by
    intro i j heq
    exact hAinj ((hf i).symm.trans ((congrArg v heq).trans (hf j)))
  obtain ⟨e,he⟩ := exists_strictMono_attachment_reindexing f hFinj
  have hV : ∀ i, v i ∈ V(G.graph) := by
    intro i
    exact hQ.le.vertexSet_mono (hRange ▸ mem_range_self i)
  have hP' : ∀ i, IsGraphPathWithEnds G.graph (P (e i)) (v (f (e i))) (B (e i)).root.val := by
    intro i
    rw [hf (e i)]
    exact hP (e i)
  have hPV' : ∀ i, V(P (e i)) ∩ range v = {v (f (e i))} := by
    intro i
    rw [hRange,hf (e i)]
    exact hPQ (e i)
  exact rootedPathComb_of_ordered_binary_attachments hγ hδ hN G v hv hV hAdj hStart.symm
    (fun i ↦ f (e i)) he (fun i ↦ B (e i)) (fun i ↦ hBG (e i)) (fun i ↦ MB (e i))
    (fun i ↦ hRange.symm ▸ hDis (e i)) (fun _ _ hij ↦ hBD (e.injective.ne hij))
    (fun i ↦ P (e i)) hP' hPV' (fun i ↦ hSelf (e i))
    (fun i j hij ↦ hOther (e i) (e j) (e.injective.ne hij))
    (fun _ _ hij ↦ hPP (e.injective.ne hij))

end GraphMinor.GM01
