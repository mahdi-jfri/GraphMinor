module

public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM01.RootedModelSets
import GraphMinor.GM01.RootedModelRestriction
import GraphMinor.GM01.RootedSubgraphModelMinor
import GraphMinor.GM01.RootedModelComposition
import GraphMinor.GM01.PathWidthSimpleComponents
import GraphMinor.Minor.Basic

/-!
# Transferring a packed forest family through a rooted model

In Graph Minors I, (5.2), page 61, lift every selected fork support
to the union of its target branches. These unions stay disjoint.
Restrict the actual model to each selected support. The root support
retains its rooted binary minor by composition. For another support,
forget the root of its restricted simple-source model and compose
its ordinary forest minor. Thus (X1)/(X2) hold in the actual component.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- Transfer all conditions of the packed family through an actual
rooted model, the fork-to-component step in GM01 (5.2), page 61. -/
theorem exists_rooted_forest_family_of_rooted_model {α β ν : Type*} [Nonempty β]
    {γ n : ℕ} (H : (⊤ : SimpleGraph ν).Subgraph) (hH : H.verts.Finite) (r : H.verts)
    (G : RootedGraph α β) (hV : V(G.graph).Finite) (hE : E(G.graph).Finite)
    (M : RootedMinorModel (⟨toGraph H,r⟩ : RootedGraph ν (Sym2 ν)) G)
    (F : RootedForestFamily (⟨toGraph H,r⟩ : RootedGraph ν (Sym2 ν)) γ n) :
    Nonempty (RootedForestFamily G γ n) := by
  classical
  have hRoot : G.root.val ∈ M.liftSet F.rootSet :=
    (M.mem_liftSet_iff F.rootSet G.root.val).mpr ⟨r,F.root_mem,M.root_mem⟩
  let sourceRoot : V((toGraph H).induce F.rootSet) := ⟨r.val,F.root_mem⟩
  let targetRoot : V(G.graph.induce (M.liftSet F.rootSet)) := ⟨G.root.val,hRoot⟩
  let MR := M.restrictSource F.rootSet F.root_subset sourceRoot targetRoot M.root_mem
  have hRootMinor : HasRootedMinor (binaryRootedTree γ)
      (⟨G.graph.induce (M.liftSet F.rootSet),targetRoot⟩ : RootedGraph α β) :=
    F.root_minor.trans ⟨MR⟩
  have hOther : ∀ i, IsIsoMinor (forestTreeGraph (γ - 1))
      (G.graph.induce (M.liftSet (F.otherSet i))) := by
    intro i
    obtain ⟨v,hv⟩ := F.other_nonempty i
    let v' : H.verts := ⟨v,F.other_subset i hv⟩
    obtain ⟨x,hx⟩ := (M.branch_connected v').1
    have hxLift : x ∈ M.liftSet (F.otherSet i) :=
      (M.mem_liftSet_iff _ x).mpr ⟨v',hv,hx⟩
    let T : RootedGraph α β := ⟨G.graph.induce (M.liftSet (F.otherSet i)),⟨x,hxLift⟩⟩
    let vS : (H.induce (F.otherSet i)).verts := ⟨v,hv⟩
    let MRestr := M.restrictSource (F.otherSet i) (F.other_subset i) ⟨v,hv⟩ ⟨x,hxLift⟩ hx
    have M' : RootedMinorModel (⟨toGraph (H.induce (F.otherSet i)),vS⟩ :
        RootedGraph ν (Sym2 ν)) T := by
      have hRootedEq : (⟨toGraph (H.induce (F.otherSet i)),vS⟩ : RootedGraph ν (Sym2 ν)) =
          ⟨(toGraph H).induce (F.otherSet i),⟨v,hv⟩⟩ := by
        exact (RootedGraph.mk.injEq (toGraph (H.induce (F.otherSet i))) vS
          ((toGraph H).induce (F.otherSet i)) ⟨v,hv⟩).mpr
            ⟨toGraph_induce H (F.otherSet i),HEq.rfl⟩
      exact hRootedEq.symm ▸ MRestr
    have hTG : T.graph ≤ G.graph := G.graph.induce_le (M.liftSet_subset _)
    have hMinor := M'.isIsoMinor_of_subgraph_source (hH.subset (F.other_subset i)) vS T
      (hV.subset hTG.vertexSet_mono) (hE.subset hTG.edgeSet_mono)
    rw [toGraph_induce] at hMinor
    exact (F.other_minor i).trans hMinor
  exact ⟨{
    rootSet := M.liftSet F.rootSet
    otherSet := fun i ↦ M.liftSet (F.otherSet i)
    root_subset := M.liftSet_subset _
    other_subset := fun i ↦ M.liftSet_subset _
    other_disjoint := fun _ _ hij ↦ M.liftSet_disjoint (F.other_disjoint hij)
    root_disjoint := fun i ↦ M.liftSet_disjoint (F.root_disjoint i)
    root_mem := hRoot
    root_minor := hRootMinor
    other_minor := hOther }⟩

end GraphMinor.GM01
