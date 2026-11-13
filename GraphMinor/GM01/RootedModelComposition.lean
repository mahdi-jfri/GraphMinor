module

public import GraphMinor.GM01.RootedModelSetConnectivity

/-!
# Composition of rooted minor models

The proof of Graph Minors I, (4.1), page 55, constructs a forbidden
rooted minor by deletion and contraction in the comb and its bypass.
Composition replaces each intermediate branch by the union of the target
branches representing its vertices. The branch-union lemmas give
connectivity and disjointness. The composite edge injection preserves
ends, and the two root conditions put the final root in its required
branch.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph

/-- Compose the actual branch sets and edge maps of two rooted models.
This supplies the transitivity used in the contraction argument for
Graph Minors I, (4.1), page 55. -/
def RootedMinorModel.trans {α β γ δ ε ζ : Type*}
    {H : RootedGraph α β} {K : RootedGraph γ δ} {G : RootedGraph ε ζ}
    (M : RootedMinorModel H K) (L : RootedMinorModel K G) : RootedMinorModel H G where
  branch x := L.liftSet (M.branch x)
  branch_subset x := L.liftSet_subset (M.branch x)
  branch_disjoint := fun _ _ hxy ↦ L.liftSet_disjoint (M.branch_disjoint hxy)
  branch_connected x := L.liftSet_connected (M.branch x)
    (M.branch_subset x) (M.branch_connected x)
  edgeMap := M.edgeMap.trans L.edgeMap
  edge_links e x y he := by
    obtain ⟨a, ha, b, hb, hab⟩ := M.edge_links e x y he
    let a' : V(K.graph) := ⟨a, M.branch_subset x ha⟩
    let b' : V(K.graph) := ⟨b, M.branch_subset y hb⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := L.edge_links (M.edgeMap e) a' b' hab
    exact ⟨p, (L.mem_liftSet_iff (M.branch x) p).mpr ⟨a', ha, hp⟩,
      q, (L.mem_liftSet_iff (M.branch y) q).mpr ⟨b', hb, hq⟩, hpq⟩
  root_mem := (L.mem_liftSet_iff (M.branch H.root) G.root.val).mpr
    ⟨K.root, M.root_mem, L.root_mem⟩

/-- Rooted minor containment is transitive, with the composite model
constructed by branch unions. -/
theorem HasRootedMinor.trans {α β γ δ ε ζ : Type*}
    {H : RootedGraph α β} {K : RootedGraph γ δ} {G : RootedGraph ε ζ}
    (hHK : HasRootedMinor H K) (hKG : HasRootedMinor K G) : HasRootedMinor H G := by
  obtain ⟨M⟩ := hHK
  obtain ⟨L⟩ := hKG
  exact ⟨M.trans L⟩

end GraphMinor.GM01
