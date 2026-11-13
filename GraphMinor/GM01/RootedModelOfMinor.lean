module

public import GraphMinor.GM01.RootedGraphs
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Rooting an ordinary model at a specified branch

The subdivision setup on page 55 of Graph Minors I retains an ordinary
comb model with its root centre in the first branch. An ordinary model
of a simple source gives the rooted model when that branch contains the
target root. Its connected branch subgraphs remain connected in their
induced graphs, and the incidence conditions give the represented ends
of each source edge.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- Root an ordinary model of a simple graph at any target vertex in the
branch of the chosen source root. All rooted-model conditions are derived
from the ordinary model. -/
def rootedModelOfMinorModel {α γ δ : Type*} {S : SimpleGraph α}
    {G : Graph γ δ} {ηv : α → Set γ} {ηe : Sym2 α → δ}
    (h : IsMinorModel (Graph.ofSimpleGraph S) G ηv ηe)
    (root : α) (target : V(G)) (hroot : target.val ∈ ηv root) :
    RootedMinorModel
      (⟨Graph.ofSimpleGraph S, ⟨root, mem_univ _⟩⟩ : RootedGraph α (Sym2 α))
      (⟨G, target⟩ : RootedGraph γ δ) := by
  refine
    { branch := fun v ↦ ηv v.val
      branch_subset := fun v ↦ h.vertex_subset v.val (mem_univ _)
      branch_disjoint := ?_
      branch_connected := ?_
      edgeMap :=
        ⟨fun e ↦ ⟨ηe e.val, h.edge_mem e.val e.property⟩, ?_⟩
      edge_links := ?_
      root_mem := hroot }
  · intro u v huv
    exact h.vertex_disjoint u.val (mem_univ _) v.val (mem_univ _)
      (fun heq ↦ huv (Subtype.ext heq))
  · intro v
    obtain ⟨K, hK, hV, hconn⟩ := h.connected v.val (mem_univ _)
    have hKG : K ≤ G := hK.trans Graph.deleteEdges_le
    refine ⟨hV ▸ hconn.1, ?_⟩
    intro x hx y hy
    have hxK : x ∈ V(K) := hV.symm ▸ hx
    have hyK : y ∈ V(K) := hV.symm ▸ hy
    apply Relation.ReflTransGen.mono ?_ x y (hconn.2 x hxK y hyK)
    intro a b hab
    obtain ⟨e, he⟩ := hab
    exact ⟨e, he.mono hKG, hV ▸ he.left_mem, hV ▸ he.right_mem⟩
  · intro e f hef
    apply Subtype.ext
    exact h.edge_injOn e.property f.property (congrArg Subtype.val hef)
  · intro e u v he
    have huv : u.val ≠ v.val := by
      have hadj : S.Adj u.val v.val := by
        have hm := e.property
        rw [he.1] at hm
        exact hm
      exact hadj.ne
    obtain ⟨x, hx, hxe⟩ := (h.inc_iff u.val (mem_univ _) e.val e.property).mp he.inc_left
    obtain ⟨y, hy, hye⟩ := (h.inc_iff v.val (mem_univ _) e.val e.property).mp he.inc_right
    have hxy : x ≠ y := by
      intro heq
      exact disjoint_left.mp (h.vertex_disjoint u.val (mem_univ _) v.val (mem_univ _) huv)
        hx (heq.symm ▸ hy)
    have hlink := hxe.isLink_other
    have hyother : y = hxe.other := hye.eq_of_isLink_of_ne_left hlink hxy.symm
    rw [← hyother] at hlink
    exact ⟨x, hx, y, hy, hlink⟩

/-- Rooting the ordinary model preserves each of its branch sets. -/
theorem rootedModelOfMinorModel_branch {α γ δ : Type*} {S : SimpleGraph α}
    {G : Graph γ δ} {ηv : α → Set γ} {ηe : Sym2 α → δ}
    (h : IsMinorModel (Graph.ofSimpleGraph S) G ηv ηe)
    (root : α) (target : V(G)) (hroot : target.val ∈ ηv root)
    (v : V(Graph.ofSimpleGraph S)) :
    (rootedModelOfMinorModel h root target hroot).branch v = ηv v.val := by
  unfold rootedModelOfMinorModel
  rfl

end GraphMinor.GM01
