module

public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM01.RootedForks
public import GraphMinor.GM01.GraphSeparators
import GraphMinor.GM01.ForkForestPackingLift
import GraphMinor.GM01.RootSupportComponentPaths
import GraphMinor.GM01.ForestFamilyReplacement

/-!
# The fork exclusion in a component meeting the root support

Graph Minors I, (5.2), page 61, roots this component at the first
vertex reached by a root-support path. The cut separates the old
nonexceptional supports from the component. A large rooted fork
would supply `Ω+1` new supports there. Extend their root support
along the path and append every old nonexceptional support. Since
at most `Ω` old supports are exceptional, the resulting family is
larger than the chosen maximum, a contradiction.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- The geometric fork exclusion in GM01 (5.2), page 61. The clean
root path, actual fork packing, larger family, and cardinality
contradiction are all constructed from the local situation. -/
theorem exists_root_inside_support_not_large_fork {α β : Type*} {γ n Ω : ℕ}
    (hγ : 0 < γ) (G : RootedGraph α β)
    (hVfin : V(G.graph).Finite) (hEfin : E(G.graph).Finite)
    (F : RootedForestFamily G γ n) (hMax : ∀ k, RootedForestFamily G γ k → k ≤ n)
    (X : Set α) (J : Set (Fin n)) (hJ : J.ncard ≤ Ω)
    (hSep : ∀ j ∉ J, GraphSeparates G.graph X F.rootSet (F.otherSet j))
    (K : Graph α β) (hKG : K ≤ G.graph) (hKC : GraphConnected K) (hKS : V(K) = F.rootSet)
    (C : Graph α β) (hCG : C ≤ G.graph.deleteVerts X) (hCC : GraphConnected C)
    (hMeet : (V(C) ∩ F.rootSet).Nonempty) :
    ∃ v : V(C), ¬ HasRootedMinor (rootedForkGraph γ (3 * Ω + 6) hγ (by omega))
      (⟨C,v⟩ : RootedGraph α β) := by
  have hRootK : G.root.val ∈ V(K) := hKS.symm ▸ F.root_mem
  have hMeetK : (V(K) ∩ V(C)).Nonempty := by
    obtain ⟨w,hwC,hwS⟩ := hMeet
    exact ⟨w,hKS.symm ▸ hwS,hwC⟩
  obtain ⟨v,hv,P,hP,hPK,hPC⟩ := exists_clean_root_support_path hKG hKC hRootK (V(C)) hMeetK
  refine ⟨⟨v,hv⟩,?_⟩
  intro hFork
  let CRoot : RootedGraph α β := ⟨C,⟨v,hv⟩⟩
  have hCG' : C ≤ G.graph := hCG.trans Graph.deleteVerts_le
  obtain ⟨FNew⟩ := exists_forest_family_of_large_rooted_fork hγ Ω CRoot
    (hVfin.subset hCG'.vertexSet_mono) (hEfin.subset hCG'.edgeSet_mono) hFork
  have hAvoid : ∀ j ∉ J, Disjoint V(C) (F.otherSet j) := by
    intro j hj
    exact connected_subgraph_disjoint_of_graphSeparates hCG hCC hMeet (hSep j hj)
  have hPS : V(P) ⊆ F.rootSet := hPK.trans hKS.le
  exact false_of_larger_component_forest_family G CRoot hCG' F hMax FNew J
    (Nat.lt_succ_of_le hJ) hAvoid hP hPC hPS

end GraphMinor.GM01
