module

public import GraphMinor.Thomason.SubsetMissingCount
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Edge selections as connected branch candidates

An edge gives a connected selection of two vertices without adding a
connecting vertex. The family of edge endpoint sets has the same size
as the edge set. Its total uncovered count is bounded by the count over
all two-element sets, while the degree sum gives a lower bound on the
number of candidates.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two-vertex selections given by edges of the graph. -/
def edgeSelections : Finset (Finset V) := G.edgeFinset.image Sym2.toFinset

/-- Distinct graph edges have distinct endpoint sets. -/
theorem card_edgeSelections : (edgeSelections G).card = G.edgeFinset.card := by
  apply card_image_of_injective
  intro e f hef
  apply Sym2.ext
  intro v
  simp only [← Sym2.mem_toFinset, hef]

/-- Every edge selection has two vertices. -/
theorem edgeSelections_subset_powersetCard :
    edgeSelections G ⊆ (univ : Finset V).powersetCard 2 := by
  intro Y hY
  obtain ⟨e, he, rfl⟩ := mem_image.mp hY
  exact mem_powersetCard.mpr ⟨subset_univ _,
    Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeFinset he)⟩

/-- An edge selection induces a connected graph. -/
theorem connected_of_mem_edgeSelections (Y : Finset V) (hY : Y ∈ edgeSelections G) :
    (G.induce (Y : Set V)).Connected := by
  obtain ⟨e, he, rfl⟩ := mem_image.mp hY
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := (G.mem_edgeFinset.mp he)
    rw [Sym2.toFinset_mk_eq]
    rw [coe_pair]
    exact SimpleGraph.induce_pair_connected_of_adj hab

/-- The degree sum bounds the number of connected pair selections. -/
theorem twice_card_edgeSelections (r : ℕ) (hdegree : ∀ v, r ≤ G.degree v) :
    Fintype.card V * r ≤ 2 * (edgeSelections G).card := by
  rw [card_edgeSelections, ← G.sum_degrees_eq_twice_card_edges]
  calc
    Fintype.card V * r = ∑ _v : V, r := by simp
    _ ≤ ∑ v : V, G.degree v := sum_le_sum (fun v _ => hdegree v)

/-- Edge selections satisfy the uncovered-count bound for all pairs. -/
theorem sum_card_undominatedVertices_edgeSelections_le (D : ℕ)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1) :
    (∑ Y ∈ edgeSelections G, (undominatedVertices G Y).card) ≤
      Fintype.card V * D.choose 2 := by
  exact (sum_le_sum_of_subset_of_nonneg (edgeSelections_subset_powersetCard G)
    (fun _ _ _ => Nat.zero_le _)).trans
      (sum_card_undominatedVertices_powersetCard_le G 2 D hdegree)

end GraphMinor.Thomason
