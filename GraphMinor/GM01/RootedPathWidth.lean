module

public import GraphMinor.GM01.RootedPaths
public import GraphMinor.GM01.PathWidth
import GraphMinor.GM01.PathWidthSimpleComponents
import GraphMinor.GM01.Basic

/-!
# The base case of the rooted path-width induction

In the proof of Graph Minors I, (1.1), the later bound (3.1) is reduced
to a rooted induction. Part 1 of that induction, page 54, excludes a path
rooted at one end. Delete the root, root every remaining component at a
neighbour of the old root, and induct on the maximum length of rooted
paths. The proved component and vertex-deletion bounds combine the
resulting decompositions.
-/

public section

namespace GraphMinor.GM01

open SimpleGraph

variable {α : Type*}

private theorem pathWidthLE_of_root_path_bound_aux (k : ℕ) :
    ∀ (G : (⊤ : SimpleGraph α).Subgraph), G.verts.Finite → G.Connected →
      ∀ root : G.verts,
        (∀ {v : G.verts} (p : G.coe.Walk root v), p.IsPath → p.length ≤ k) →
        HasPathWidthLE (toGraph G) k := by
  classical
  induction k with
  | zero =>
    intro G hfin hconn root hbound
    have hsub : G.verts ⊆ {root.val} := by
      intro x hx
      obtain ⟨p, hp⟩ := (hconn root ⟨x, hx⟩).exists_isPath
      have hlen : p.length = 0 := Nat.eq_zero_of_le_zero (hbound p hp)
      exact (congrArg Subtype.val (Walk.eq_of_length_eq_zero hlen)).symm
    have hcard : G.verts.ncard ≤ 1 := by
      simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub (Set.finite_singleton _)
    refine ⟨⟨1, fun _ ↦ G.verts, fun _ ↦ Set.Subset.rfl, ?_, ?_⟩, ?_⟩
    · intro e x y he
      exact ⟨0, he.left_mem, he.right_mem⟩
    · intro i j l hij hjl x hx
      exact hx.1
    · intro i
      exact ⟨hfin, hcard⟩
  | succ k ih =>
    intro G hfin hconn root hbound
    let D := G.deleteVerts {root.val}
    have hDfin : D.verts.Finite := hfin.subset G.deleteVerts_le.1
    have hcomponents : ∀ C : D.coe.ConnectedComponent,
        HasPathWidthLE (toGraph (ambientComponent D C)) k := by
      intro C
      let K := ambientComponent D C
      have hKD : K ≤ D := ambientComponent_le D C
      have hKG : K ≤ G := hKD.trans G.deleteVerts_le
      obtain ⟨x, hxK, hrootx⟩ := exists_root_neighbor_in_component G hconn root C
      let rootK : K.verts := ⟨x, hxK⟩
      apply ih K (hfin.subset hKG.1) (ambientComponent_connected D C) rootK
      intro v p hp
      let f := Subgraph.inclusion hKG
      let q := p.map f
      have hf : Function.Injective f := by
        intro a b hab
        exact Subtype.ext (congrArg (fun z : G.verts ↦ z.val) hab)
      have hq : q.IsPath := hp.map hf
      have havoid : root ∉ q.support := by
        intro hmem
        rw [Walk.support_map] at hmem
        obtain ⟨a, ha, haroot⟩ := List.mem_map.mp hmem
        have heq : a.val = root.val := congrArg (fun z : G.verts ↦ z.val) haroot
        have haD : a.val ∈ D.verts := hKD.1 a.property
        exact haD.2 (Set.mem_singleton_iff.mpr heq)
      have hedge : G.coe.Adj root (f rootK) := hrootx
      have hnew : (q.cons hedge).IsPath := hq.cons havoid
      have hlen := hbound (q.cons hedge) hnew
      simp only [Walk.length_cons, q, Walk.length_map] at hlen
      exact Nat.le_of_succ_le_succ hlen
    have hDwidth : HasPathWidthLE (toGraph D) k :=
      hasPathWidthLE_of_simple_components D hDfin hcomponents
    have hdel : HasPathWidthLE ((toGraph G).deleteVerts {root.val}) k := by
      rw [← toGraph_deleteVerts]
      exact hDwidth
    have hX : {root.val} ⊆ Graph.vertexSet (toGraph G) :=
      Set.singleton_subset_iff.mpr root.property
    have hw := theorem_1_5_proof hfin hX hdel
    simpa only [Set.ncard_singleton] using hw

/-- If every path beginning at the root has at most `k` edges, a finite
connected graph has path-width at most `k`. The induction deletes the root
and roots each component at an adjacent vertex, as in Part 1 on page 54. -/
theorem pathWidthLE_of_root_path_bound (G : (⊤ : SimpleGraph α).Subgraph)
    (hfin : G.verts.Finite) (hconn : G.Connected) (root : G.verts) (k : ℕ)
    (hbound : ∀ {v : G.verts} (p : G.coe.Walk root v), p.IsPath → p.length ≤ k) :
    HasPathWidthLE (toGraph G) k :=
  pathWidthLE_of_root_path_bound_aux k G hfin hconn root hbound

/-- Part 1 of the rooted induction in the proof of Graph Minors I, (1.1),
via (3.7), page 54: excluding the `δ`-vertex path rooted at one end gives
path-width at most `δ−2`. The root is deleted at each induction step, and
(1.4) and (1.5) combine the component bounds. -/
theorem pathWidthLE_of_not_rootedPathComb (G : (⊤ : SimpleGraph α).Subgraph)
    (hfin : G.verts.Finite) (hconn : G.Connected) (root : G.verts) {δ : ℕ} (hδ : 0 < δ)
    (hno : ¬ HasRootedMinor (rootedPathComb 0 δ hδ)
      (⟨toGraph G, root⟩ : RootedGraph α (Sym2 α))) :
    HasPathWidthLE (toGraph G) (δ - 2) :=
  pathWidthLE_of_root_path_bound G hfin hconn root (δ - 2)
    (fun p hp ↦ path_length_le_of_not_rootedPathComb G root hδ hno p hp)

end GraphMinor.GM01
