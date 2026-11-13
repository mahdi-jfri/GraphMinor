module

public import GraphMinor.GM01.CombConcatenationModel
public import GraphMinor.GM01.PathLastEdgeCover
import GraphMinor.GM01.RootedBranchModels
import GraphMinor.GM01.RootedModelComposition
import GraphMinor.GM01.ConnectedInducedSets
import GraphMinor.GM01.SubdivisionConnected

/-!
# Joining two comb models along an avoiding path

The contraction in Graph Minors I, (4.10), page 58, joins two disjoint
comb pieces by a path from the last branch of the first to the first
branch of the second. Remove the last edge of that path and add its
prefix to the last branch of the first model. This branch stays
connected and disjoint from all other branches. The removed edge joins
the two source combs. The proved consecutive-interval identification
then gives a rooted comb of summed spine length.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The branch construction for joining the old prefix to `D` in
GM01 (4.10), page 58. The connecting path meets each piece only at its
specified endpoint. -/
noncomputable def rootedModelOfCombJoin {α β : Type*} {γ a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (G G₁ G₂ : RootedGraph α β)
    (hG₁ : G₁.graph ≤ G.graph) (hG₂ : G₂.graph ≤ G.graph)
    (hroot : G₁.root.val = G.root.val) (hdis : Disjoint V(G₁.graph) V(G₂.graph))
    (M₁ : RootedMinorModel (rootedPathComb γ a ha) G₁)
    (M₂ : RootedMinorModel (rootedPathComb γ b hb) G₂)
    {z : α} (hz : z ∈ M₁.branch (pathCombLastSpine γ a ha))
    {P : Graph α β} (hP : IsGraphPathWithEnds G.graph P z G₂.root.val)
    (hP₁ : V(P) ∩ V(G₁.graph) = {z}) (hP₂ : V(P) ∩ V(G₂.graph) = {G₂.root.val}) :
    RootedMinorModel (rootedPathComb γ (a + b) (by omega)) G := by
  classical
  let last := pathCombLastSpine γ a ha
  have hne : z ≠ G₂.root.val := by
    intro heq
    exact Set.disjoint_left.mp hdis (M₁.branch_subset last hz) (heq.symm ▸ G₂.root.property)
  let hex := exists_last_edge_with_vertex_cover hP hne
  let e := hex.choose
  let q := hex.choose_spec.choose
  let Q := hex.choose_spec.choose_spec.choose
  have hlink : P.IsLink e q G₂.root.val := hex.choose_spec.choose_spec.choose_spec.1
  have hQP : Q ≤ P := hex.choose_spec.choose_spec.choose_spec.2.1
  have hQ : IsGraphPathWithEnds G.graph Q z q := hex.choose_spec.choose_spec.choose_spec.2.2.1
  have hNot : G₂.root.val ∉ V(Q) := hex.choose_spec.choose_spec.choose_spec.2.2.2.1
  have hQ₂ : Disjoint V(Q) V(G₂.graph) := by
    apply Set.disjoint_left.mpr
    intro x hx hxG₂
    have hxEnd : x = G₂.root.val := mem_singleton_iff.mp
      (hP₂ ▸ ⟨hQP.vertexSet_mono hx, hxG₂⟩)
    exact hNot (hxEnd ▸ hx)
  have hQOther : ∀ v : (pathComb γ a).verts, v ≠ last → Disjoint V(Q) (M₁.branch v) := by
    intro v hv
    apply Set.disjoint_left.mpr
    intro x hx hxB
    have hxz : x = z := mem_singleton_iff.mp
      (hP₁ ▸ ⟨hQP.vertexSet_mono hx, M₁.branch_subset v hxB⟩)
    exact Set.disjoint_left.mp (M₁.branch_disjoint hv) hxB (hxz.symm ▸ hz)
  let B₁ (v : (pathComb γ a).verts) := if v = last then M₁.branch v ∪ V(Q) else M₁.branch v
  have hOld : ∀ v, M₁.branch v ⊆ B₁ v := by
    intro v
    dsimp only [B₁]
    split_ifs
    · exact subset_union_left
    · exact Subset.rfl
  have hB₁sub : ∀ v, B₁ v ⊆ V(G.graph) := by
    intro v x hx
    by_cases hv : v = last
    · subst v
      simp only [B₁, ↓reduceIte] at hx
      exact hx.elim (fun h ↦ hG₁.vertexSet_mono (M₁.branch_subset last h)) (fun h ↦ hQ.le.vertexSet_mono h)
    · simp only [B₁, hv, ↓reduceIte] at hx
      exact hG₁.vertexSet_mono (M₁.branch_subset v hx)
  have hB₁dis : Pairwise (fun u v ↦ Disjoint (B₁ u) (B₁ v)) := by
    intro u v huv
    by_cases hu : u = last
    · have hv : v ≠ last := fun hv ↦ huv (hu.trans hv.symm)
      simp only [B₁, hu, hv, ↓reduceIte]
      exact (M₁.branch_disjoint (Ne.symm hv)).union_left (hQOther v hv)
    · by_cases hv : v = last
      · simp only [B₁, hu, hv, ↓reduceIte]
        exact (M₁.branch_disjoint hu).union_right (hQOther u hu).symm
      · simp only [B₁, hu, hv, ↓reduceIte]
        exact M₁.branch_disjoint huv
  have hOldConn : ∀ v : (pathComb γ a).verts, GraphConnected (G.graph.induce (M₁.branch v)) := by
    intro v
    exact graphConnected_induce_of_subgraph
      ((G₁.graph.induce_le (M₁.branch_subset v)).trans hG₁) (M₁.branch_connected v)
  have hB₁conn : ∀ v, GraphConnected (G.graph.induce (B₁ v)) := by
    intro v
    by_cases hv : v = last
    · simp only [B₁, hv, ↓reduceIte]
      exact graphConnected_induce_union (hOldConn last)
        (graphConnected_induce_of_subgraph hQ.le (graphConnected_of_isGraphPath hQ))
        ⟨z, hz, hQ.left_mem⟩
    · simpa only [B₁, hv, ↓reduceIte] using hOldConn v
  have hCross : ∀ u v, Disjoint (B₁ u) (M₂.branch v) := by
    intro u v
    have hold : Disjoint (M₁.branch u) (M₂.branch v) :=
      hdis.mono (M₁.branch_subset u) (M₂.branch_subset v)
    have hnew := hQ₂.mono_right (M₂.branch_subset v)
    by_cases hu : u = last
    · simpa only [B₁, hu, ↓reduceIte] using hold.union_left hnew
    · simpa only [B₁, hu, ↓reduceIte] using hold
  let B : ((pathComb γ a).verts ⊕ (pathComb γ b).verts) → Set α := Sum.elim B₁ M₂.branch
  have hBsub : ∀ v, B v ⊆ V(G.graph) := by
    rintro (v | v)
    · exact hB₁sub v
    · exact (M₂.branch_subset v).trans hG₂.vertexSet_mono
  have hBdis : Pairwise (fun u v ↦ Disjoint (B u) (B v)) := by
    rintro (u | u) (v | v) huv
    · exact hB₁dis (fun h ↦ huv (congrArg Sum.inl h))
    · exact hCross u v
    · exact (hCross v u).symm
    · exact M₂.branch_disjoint (fun h ↦ huv (congrArg Sum.inr h))
  have hBconn : ∀ v, GraphConnected (G.graph.induce (B v)) := by
    rintro (v | v)
    · exact hB₁conn v
    · exact graphConnected_induce_of_subgraph
        ((G₂.graph.induce_le (M₂.branch_subset v)).trans hG₂) (M₂.branch_connected v)
  have hAdj : ∀ {u v}, (concatenatedComb γ a b ha hb).Adj u v →
      ∃ edge x, x ∈ B u ∧ ∃ y, y ∈ B v ∧ G.graph.IsLink edge x y := by
    rintro (u | u) (v | v) huv
    · let f : E(toGraph (pathComb γ a)) := ⟨s(u.val,v.val), huv⟩
      obtain ⟨x, hx, y, hy, hxy⟩ := M₁.edge_links f u v ⟨rfl, huv⟩
      exact ⟨(M₁.edgeMap f).val, x, hOld u hx, y, hOld v hy, hxy.mono hG₁⟩
    · obtain ⟨rfl, rfl⟩ := huv
      have hq : q ∈ B₁ last := by simp only [B₁, ↓reduceIte]; exact Or.inr hQ.right_mem
      exact ⟨e, q, hq, G₂.root.val, M₂.root_mem, hlink.mono hP.le⟩
    · obtain ⟨rfl, rfl⟩ := huv
      have hq : q ∈ B₁ last := by simp only [B₁, ↓reduceIte]; exact Or.inr hQ.right_mem
      exact ⟨e, G₂.root.val, M₂.root_mem, q, hq, (hlink.mono hP.le).symm⟩
    · let f : E(toGraph (pathComb γ b)) := ⟨s(u.val,v.val), huv⟩
      obtain ⟨x, hx, y, hy, hxy⟩ := M₂.edge_links f u v ⟨rfl, huv⟩
      exact ⟨(M₂.edgeMap f).val, x, hx, y, hy, hxy.mono hG₂⟩
  have hRoot : G.root.val ∈ B (Sum.inl (rootedPathComb γ a ha).root) :=
    hroot ▸ hOld _ M₁.root_mem
  let M := rootedModelOfBranchSets (concatenatedComb γ a b ha hb) G B hBsub hBdis hBconn hAdj
    (Sum.inl (rootedPathComb γ a ha).root) hRoot
  exact (rootedModelOfCombConcatenation γ a b ha hb).trans M

end GraphMinor.GM01
