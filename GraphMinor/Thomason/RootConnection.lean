module

public import GraphMinor.Thomason.ConnectedDominators
import GraphMinor.Thomason.NearHalfConnected
import Lean.Elab.Tactic.Omega

/-!
# Connecting vertices missed by a chosen root

Keep a root that is already one of the selected vertices. Join each
selected vertex outside its closed neighbourhood through one common
neighbour. The added vertices all lie next to the root. They therefore
form a connected set with the root and dominate the whole selection.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At the half-degree boundary, at most one new vertex is needed for
each selected vertex that is not dominated by the chosen root. -/
theorem exists_connecting_set_from_root (Y : Finset V) (v : V) (hv : v ∈ Y)
    (hnear : ∀ x, Fintype.card V ≤ 2 * G.degree x + 1) :
    ∃ W : Finset V, W.card ≤ (Y ∩ undominatedVertices G {v}).card ∧
      (G.induce ((Y ∪ W : Finset V) : Set V)).Connected := by
  classical
  let B := Y ∩ undominatedVertices G {v}
  have hcommon (z : B) : ∃ w, G.Adj v w ∧ G.Adj z.val w := by
    have hz := (mem_inter.mp z.property).2
    have hnot : ¬ (z.val = v ∨ G.Adj v z.val) := by
      simpa only [undominatedVertices, dominatedVertices_singleton, mem_sdiff,
        mem_univ, true_and, mem_insert, G.mem_neighborFinset] using hz
    exact exists_commonNeighbor_of_near_half G hnear (Ne.symm ((not_or.mp hnot).1)) (not_or.mp hnot).2
  let w : B → V := fun z => (hcommon z).choose
  have hw (z : B) : G.Adj v (w z) ∧ G.Adj z.val (w z) := (hcommon z).choose_spec
  let W := B.attach.image w
  let U := ({v} : Finset V) ∪ W
  have hWcard : W.card ≤ B.card := by
    exact (card_image_le).trans (by rw [card_attach])
  have hroot : (G.induce (({v} : Finset V) : Set V)).Connected := by
    have heq : (({v} : Finset V) : Set V) = {v} := by ext x; simp
    rw [heq]
    exact (SimpleGraph.Subgraph.singletonSubgraph_connected (G := G) (v := v)).induce_verts
  have hWdom : W ⊆ dominatedVertices G {v} := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := mem_image.mp hz
    exact mem_union_right _ (mem_biUnion.mpr ⟨v, mem_singleton_self _,
      (G.mem_neighborFinset v (w a)).mpr (hw a).1⟩)
  have hUconn : (G.induce (U : Set V)).Connected :=
    connected_induce_union_of_dominated G {v} W hroot hWdom
  have hYdom : Y ⊆ dominatedVertices G U := by
    intro z hz
    by_cases hzd : z ∈ dominatedVertices G {v}
    · exact dominatedVertices_mono G (subset_union_left : ({v} : Finset V) ⊆ U) hzd
    · have hzB : z ∈ B := mem_inter.mpr ⟨hz, mem_sdiff.mpr ⟨mem_univ _, hzd⟩⟩
      let a : B := ⟨z, hzB⟩
      have hwa : w a ∈ W := mem_image.mpr ⟨a, mem_attach B a, rfl⟩
      exact mem_union_right _ (mem_biUnion.mpr ⟨w a, mem_union_right _ hwa,
        (G.mem_neighborFinset (w a) z).mpr (hw a).2.symm⟩)
  refine ⟨W, hWcard, ?_⟩
  have hc := connected_induce_union_of_dominated G U Y hUconn hYdom
  have heq : U ∪ Y = Y ∪ W := by
    change (({v} : Finset V) ∪ W) ∪ Y = Y ∪ W
    rw [union_assoc, union_comm W Y, ← union_assoc, singleton_union, insert_eq_of_mem hv]
  rw [heq] at hc
  exact hc

end GraphMinor.Thomason
