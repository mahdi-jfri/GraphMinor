module
public import GraphMinor.Thomason.HubGeometricSelection
import GraphMinor.Thomason.InducedSets
import GraphMinor.Thomason.DeletedDegree
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# A branch extension with central-vertex costs

The main theorem of Thomason (1984), p. 264, constructs one new branch
in the complement of the earlier branches. Exceptional vertices are
those not dominated by one of the earlier branches. The counting bound
selects a connected set outside every exceptional family.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The extension step of Thomason's branch-set construction, p. 264.
The earlier branches lie in `X` and each leaves at most `t` uncovered
vertices outside `X`. The new branch is disjoint from `X`, connected,
and joined by an edge to each earlier branch. -/
theorem exists_hub_branch_extension {I : Type v} [Fintype I] [DecidableEq I]
    (T : I → Finset V) (X : Finset V) (d D t M k : ℕ)
    (hk : 0 < k) (hX : X.card ≤ d + 1) (hM : M + X.card ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hTX : ∀ i, T i ⊆ X)
    (hT : ∀ i, (undominatedVertices G (T i) \ X).card ≤ t)
    (hcount : Fintype.card I * t.choose k < M.choose k) :
    ∃ Z : Finset V, Z.card ≤ hubSelectionCost (Fintype.card V - X.card) D k ∧ Disjoint Z X ∧
      (G.induce (Z : Set V)).Connected ∧
      (undominatedVertices G Z \ X).card ≤
        (Fintype.card V - X.card) * D ^ k / (Fintype.card V - X.card + 1 - M) ^ k ∧
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
  have hB (i : I) : (B i).card ≤ t := by
    have hc := congrArg Finset.card (hBmap i)
    rw [card_map] at hc
    exact hc.trans_le (hT i)
  have horder := card_compl_finset_add X
  have hcard : Fintype.card s = Fintype.card V - X.card := by dsimp only [s]; omega
  have hM' : M ≤ Fintype.card s := by dsimp only [s]; omega
  have hdegree' : ∀ v : s, Fintype.card s ≤ H.degree v + D + 1 :=
    nonneighbor_bound_induce_compl G X D hdegree
  have hnear : ∀ v : s, Fintype.card s ≤ 2 * H.degree v + 1 := by
    intro v
    have hh := hdeg v
    have hloss := degree_le_degree_induce_compl_add G X v
    change G.degree v ≤ H.degree v + X.card at hloss
    change Fintype.card s + X.card = Fintype.card V at horder
    omega
  have hcount' : (univ : Finset I).card * t.choose k < M.choose k := by
    simpa only [card_univ] using hcount
  obtain ⟨Y, hYcard, hYconn, hYundom, hYavoid⟩ :=
    exists_connected_hubGeometricSet_avoiding H univ B t M D k hk hM' hdegree' hnear
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
