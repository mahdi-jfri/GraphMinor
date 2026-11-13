module

public import GraphMinor.Thomason.ConnectedDominators
import GraphMinor.Thomason.PartialDomination
import GraphMinor.Thomason.NearHalfConnected
import Lean.Elab.Tactic.Omega

/-!
# Connecting a selected set through a well-chosen vertex

The averaging argument of Wood, arXiv:2610.41060v1 (2026), Lemma 6,
p. 5, chooses a vertex that already dominates most of the selection.
Only the missed vertices need common neighbours. This gives an integer
connection bound using the actual non-neighbour proportion.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Connect a nonempty selection by adding a central vertex and at most
`floor(|Y|*D/n)` common neighbours, where every vertex has at most `D`
non-neighbours and the half-order degree condition holds. -/
theorem exists_hub_connecting_set (Y : Finset V) (hne : Y.Nonempty) (D : ℕ)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hnear : ∀ v, Fintype.card V ≤ 2 * G.degree v + 1) :
    ∃ Z : Finset V, Z.card ≤ Y.card * D / Fintype.card V + 1 ∧
      (G.induce ((Y ∪ Z : Finset V) : Set V)).Connected := by
  classical
  obtain ⟨y, hy⟩ := hne
  have : Nonempty V := ⟨y⟩
  have hNpos : 0 < Fintype.card V := Fintype.card_pos
  let h := Y.card * D / Fintype.card V
  have hcount : Y.card * D < Fintype.card V * (h + 1) := by
    exact ((Nat.div_lt_iff_lt_mul hNpos).mp (Nat.lt_succ_self _)).trans_eq (Nat.mul_comm _ _)
  have hgood := card_verticesLeavingAtMost G Y h D 1 hdegree hNpos
    (by simpa only [Nat.add_sub_cancel] using hcount)
  obtain ⟨v, hv⟩ := one_le_card.mp hgood
  let B := Y ∩ undominatedVertices G {v}
  have hB : B.card ≤ h := (mem_filter.mp hv).2
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
  refine ⟨U, ?_, ?_⟩
  · have hc := card_union_le ({v} : Finset V) W
    rw [card_singleton] at hc
    change U.card ≤ 1 + W.card at hc
    change U.card ≤ h + 1
    omega
  · have hc := connected_induce_union_of_dominated G U Y hUconn hYdom
    have heq : ((Y ∪ U : Finset V) : Set V) = ((U ∪ Y : Finset V) : Set V) := by
      ext x
      simp only [mem_coe, mem_union, or_comm]
    rw [heq]
    exact hc

end GraphMinor.Thomason
