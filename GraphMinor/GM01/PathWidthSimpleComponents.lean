module

public import GraphMinor.GM01.PathWidth
public import GraphMinor.GM01.RootDeletionComponents
import GraphMinor.GM01.PathWidthComponents
import GraphMinor.GM01.Basic
import Mathlib.Data.Set.Finite.Range

/-!
# Path-width bounds on simple-graph components

The base case in the rooted proof of Graph Minors I, (1.1), deletes the
root and applies (1.4) to the remaining components. This file connects
Mathlib's simple-graph components to the multigraph path-width definition.
The component decompositions are concatenated using the proved finite-parts
construction, with no assumed component-gluing step.
-/

public section

namespace GraphMinor.GM01

open Graph SimpleGraph

variable {α : Type*}

/-- Passing to the multigraph commutes with taking an induced subgraph. -/
theorem toGraph_induce (G : (⊤ : SimpleGraph α).Subgraph) (S : Set α) :
    toGraph (G.induce S) = (toGraph G).induce S := by
  ext e x y
  · rfl
  · simp only [Graph.induce_isLink, isLink_toGraph, Subgraph.induce_adj,
      and_assoc, and_left_comm, and_comm]

/-- The component version of the path-width bound, using the simple-graph
component API in the rooted induction. This is an application of the
proved concatenation construction behind Graph Minors I, (1.4). -/
theorem hasPathWidthLE_of_simple_components (G : (⊤ : SimpleGraph α).Subgraph)
    (hfin : G.verts.Finite) {k : ℕ}
    (hwidth : ∀ C : G.coe.ConnectedComponent, HasPathWidthLE (toGraph (ambientComponent G C)) k) :
    HasPathWidthLE (toGraph G) k := by
  classical
  let : Finite G.verts := hfin.to_subtype
  let S := Set.range (fun C : G.coe.ConnectedComponent ↦ (ambientComponent G C).verts)
  have hS : S.Finite := Set.finite_range _
  have hdisj : S.PairwiseDisjoint id := by
    intro A hA B hB hne
    obtain ⟨C, rfl⟩ := hA
    obtain ⟨D, rfl⟩ := hB
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab : a = b := Subtype.ext (hax.trans hbx.symm)
    have hCD : C = D := ConnectedComponent.eq_of_common_vertex ha (hab.symm ▸ hb)
    exact hne (congrArg (fun D : G.coe.ConnectedComponent ↦ (ambientComponent G D).verts) hCD)
  have hclosed : ∀ s ∈ S, ∀ e x y, (toGraph G).IsLink e x y → x ∈ s → y ∈ s := by
    intro s hs e x y he hx
    obtain ⟨C, rfl⟩ := hs
    exact ambientComponent_closed G C hx he.2
  have hfull : ⋃₀ S = G.verts := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨s, ⟨C, rfl⟩, hx⟩ := Set.mem_sUnion.mp hx
      exact (ambientComponent_le G C).1 hx
    · intro x hx
      let v : G.verts := ⟨x, hx⟩
      let C := G.coe.connectedComponentMk v
      refine Set.mem_sUnion.mpr ⟨(ambientComponent G C).verts, ⟨C, rfl⟩, ?_⟩
      exact ⟨v, rfl, rfl⟩
  have hparts : ∀ s ∈ S, HasPathWidthLE ((toGraph G).induce s) k := by
    intro s hs
    obtain ⟨C, rfl⟩ := hs
    rw [← toGraph_induce, ← ambientComponent_eq_induce G C]
    exact hwidth C
  have hw := hasPathWidthLE_finite_parts (toGraph G) hS hdisj hclosed hparts
  rw [hfull] at hw
  change HasPathWidthLE ((toGraph G).induce V(toGraph G)) k at hw
  rwa [Graph.induce_vertexSet] at hw

/-- Passing to the multigraph commutes with deleting vertices. -/
theorem toGraph_deleteVerts (G : (⊤ : SimpleGraph α).Subgraph) (S : Set α) :
    toGraph (G.deleteVerts S) = (toGraph G).deleteVerts S := by
  ext e x y
  · simp only [vertexSet_toGraph, Subgraph.deleteVerts_verts, Graph.vertexSet_deleteVerts]
  · simp only [Graph.deleteVerts_isLink, isLink_toGraph, Subgraph.deleteVerts_adj]
    constructor
    · rintro ⟨he, hxG, hxS, hyG, hyS, hxy⟩
      exact ⟨⟨he, hxy⟩, hxS, hyS⟩
    · rintro ⟨⟨he, hxy⟩, hxS, hyS⟩
      exact ⟨he, hxy.fst_mem, hxS, hxy.snd_mem, hyS, hxy⟩

end GraphMinor.GM01
