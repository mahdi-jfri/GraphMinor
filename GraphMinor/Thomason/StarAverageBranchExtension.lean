module
public import GraphMinor.Thomason.StarAverageSelection
import GraphMinor.Thomason.InducedSets
import GraphMinor.Thomason.DeletedDegree
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Extending a branch family with selections with internal or external centres

Delete the previous branches and apply finite averaging to selections with internal or external centres in the remaining graph. Each earlier exceptional set has its own uncovered bound. Mapping
the selected connected set back gives a new branch adjacent to every
earlier branch, with a controlled uncovered count.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Finite averaging constructs a new connected branch outside the earlier
branches and controls its uncovered vertices. -/
theorem exists_star_average_branch_extension {I : Type v} [Fintype I] [DecidableEq I]
    (T : I → Finset V) (X : Finset V) (d D k b : ℕ) (t : I → ℕ) (internal : Bool)
    (hk : 0 < k) (hX : X.card ≤ d + 1)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hTX : ∀ i, T i ⊆ X)
    (hT : ∀ i, (undominatedVertices G (T i) \ X).card ≤ t i)
    (hcount : Fintype.card V * D.choose k <
      (starCandidateCount (Fintype.card V - X.card) D k internal - ∑ i, (t i).choose k) * (b + 1) ∨
      (D ≤ b ∧ (∑ i, (t i).choose k) < starCandidateCount (Fintype.card V - X.card) D k internal)) :
    ∃ Z : Finset V, Z.card ≤ starCandidateCost (Fintype.card V - X.card) D k internal ∧ Disjoint Z X ∧
      (G.induce (Z : Set V)).Connected ∧
      (undominatedVertices G Z \ X).card ≤
        b ∧
      ∀ i, ∃ z ∈ Z, ∃ w ∈ T i, G.Adj z w := by
  let s : Set V := {v | v ∉ X}
  let H := G.induce s
  let B : I → Finset s := fun i => univ.filter (fun v => v.val ∈ undominatedVertices G (T i))
  have hBmap (i : I) : (B i).map (.subtype (· ∈ s)) = undominatedVertices G (T i) \ X := by
    ext v
    simp only [B, mem_map, mem_filter, mem_univ, true_and, mem_sdiff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw, w.property⟩
    · rintro ⟨hw, hx⟩
      exact ⟨⟨v, hx⟩, hw, rfl⟩
  have hB (i : I) : (B i).card ≤ t i := by
    have hc := congrArg Finset.card (hBmap i)
    rw [card_map] at hc
    exact hc.trans_le (hT i)
  have horder := card_compl_finset_add X
  have hcard : Fintype.card s = Fintype.card V - X.card := by dsimp only [s]; omega
  have hdegree' : ∀ v : s, Fintype.card s ≤ H.degree v + D + 1 :=
    nonneighbor_bound_induce_compl G X D hdegree
  have hnear : ∀ v : s, Fintype.card s ≤ 2 * H.degree v + 1 := by
    intro v
    have hh := hdeg v
    have hloss := degree_le_degree_induce_compl_add G X v
    change G.degree v ≤ H.degree v + X.card at hloss
    change Fintype.card s + X.card = Fintype.card V at horder
    omega
  have hcount' : Fintype.card s * D.choose k <
      (starCandidateCount (Fintype.card s) D k internal - ∑ i ∈ (univ : Finset I), (t i).choose k) * (b + 1) ∨
      (D ≤ b ∧ (∑ i ∈ (univ : Finset I), (t i).choose k) < starCandidateCount (Fintype.card s) D k internal) := by
    rw [hcard]
    rcases hcount with havg | hdirect
    · exact Or.inl (lt_of_le_of_lt
        (Nat.mul_le_mul_right _ (Nat.sub_le (Fintype.card V) X.card)) havg)
    · exact Or.inr hdirect
  obtain ⟨Y, hYcard, hYconn, hYundom, hYavoid⟩ :=
    exists_connected_star_candidate_avoiding H univ B t D k b internal hk hdegree' hnear
      (fun i _ => hB i) hcount'
  let Z := Y.map (.subtype (· ∈ s))
  have hZX : Disjoint Z X := by
    apply Finset.disjoint_left.mpr
    intro v hv hx
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hv
    exact w.property hx
  refine ⟨Z, ?_, hZX, connected_induce_map_subtype G s Y hYconn, ?_, ?_⟩
  · simpa only [Z, card_map, hcard] using hYcard
  · have heq : (undominatedVertices H Y).map (.subtype (· ∈ s)) =
        undominatedVertices G Z \ X := by
      rw [map_undominatedVertices G s Y]
      ext v
      simp only [mem_filter, mem_sdiff, s, Set.mem_ofPred_eq, Z]
    have hc := congrArg Finset.card heq
    rw [card_map] at hc
    rw [← hc]
    simpa only [hcard] using hYundom
  · intro i
    have hnot := hYavoid i (mem_univ i)
    obtain ⟨z, hz, hzB⟩ := not_subset.mp hnot
    have hzdom : z.val ∈ dominatedVertices G (T i) := by
      by_contra h
      exact hzB (mem_filter.mpr ⟨mem_univ _, mem_sdiff.mpr ⟨mem_univ _, h⟩⟩)
    rcases mem_union.mp hzdom with hzT | hzN
    · exact (z.property (hTX i hzT)).elim
    · obtain ⟨w, hw, hwz⟩ := mem_biUnion.mp hzN
      exact ⟨z.val, mem_map.mpr ⟨z, hz, rfl⟩, w, hw,
        ((G.mem_neighborFinset w z.val).mp hwz).symm⟩

end GraphMinor.Thomason
