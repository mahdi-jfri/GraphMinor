module

public import GraphMinor.Thomason.OptimizedAverageSelection
public import GraphMinor.Thomason.HubBranchFamily
import GraphMinor.Thomason.MixedAverageBranchExtension
import GraphMinor.Thomason.NonemptyDominationBound
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Branch families using edges and larger connected selections

Apply the averaged extension successively. Keep the construction order
of the branches, so each retains its own uncovered-vertex bound.
Connection charges control the total number of deleted vertices.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Construct adjacent disjoint connected branches from the finite
average criterion, allowing a different uncovered bound for each branch. -/
theorem exists_mixed_average_branch_family (d D q : ℕ) (k cost t : ℕ → ℕ) (edge : ℕ → Bool)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hparam : ∀ j < q, (edge j = true → k j = 2) ∧ 0 < k j ∧ chargedBudget cost j ≤ d + 1 ∧
      chargedBudget cost j < Fintype.card V ∧
      candidateCost (Fintype.card V - chargedBudget cost j) D (k j) (edge j) ≤ cost j ∧
      (Fintype.card V * D.choose (k j) <
        (candidateCount (Fintype.card V - chargedBudget cost j) D (k j) (edge j) -
          ∑ i ∈ range j, (t i).choose (k j)) * (t j + 1) ∨
        (D ≤ t j ∧ (∑ i ∈ range j, (t i).choose (k j)) <
          candidateCount (Fintype.card V - chargedBudget cost j) D (k j) (edge j)))) :
    ∃ T : Fin q → Finset V,
      (univ.biUnion T).card ≤ chargedBudget cost q ∧
      (∀ i, (G.induce (T i : Set V)).Connected) ∧
      (Pairwise fun i j => Disjoint (T i) (T j)) ∧
      (∀ i j, i ≠ j → ∃ v ∈ T i, ∃ w ∈ T j, G.Adj v w) ∧
      ∀ i, (undominatedVertices G (T i) \ univ.biUnion T).card ≤ t i.val := by
  revert hparam
  induction q with
  | zero =>
    intro _
    refine ⟨Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [chargedBudget]
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
  | succ q ih =>
    intro hparam
    obtain ⟨T, hXcard, hT, hdis, hadj, hundom⟩ :=
      ih (fun j hj => hparam j (Nat.lt_succ_of_lt hj))
    obtain ⟨he, hk, hroom, hremaining, hcost, hcount⟩ := hparam q (Nat.lt_succ_self q)
    let X := univ.biUnion T
    change X.card ≤ chargedBudget cost q at hXcard
    have hTX (i : Fin q) : T i ⊆ X := by
      intro v hv
      exact mem_biUnion.mpr ⟨i, mem_univ _, hv⟩
    have hchoose : candidateCount (Fintype.card V - chargedBudget cost q) D (k q) (edge q) ≤
        candidateCount (Fintype.card V - X.card) D (k q) (edge q) :=
      candidateCount_monotone (Nat.sub_le_sub_left hXcard _) D (k q) (edge q)
    have hsum : (∑ i : Fin q, (t i.val).choose (k q)) =
        ∑ i ∈ range q, (t i).choose (k q) := Fin.sum_univ_eq_sum_range (fun i => (t i).choose (k q)) q
    have hcount' : Fintype.card V * D.choose (k q) <
        (candidateCount (Fintype.card V - X.card) D (k q) (edge q) - ∑ i : Fin q, (t i.val).choose (k q)) *
          (t q + 1) ∨ (D ≤ t q ∧ (∑ i : Fin q, (t i.val).choose (k q)) <
          candidateCount (Fintype.card V - X.card) D (k q) (edge q)) := by
      rw [hsum]
      rcases hcount with havg | ⟨hDt, hdirect⟩
      · exact Or.inl (havg.trans_le (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hchoose _)))
      · exact Or.inr ⟨hDt, hdirect.trans_le hchoose⟩
    obtain ⟨Z, hZcard, hZX, hZconn, hZbound, hZadj⟩ :=
      exists_mixed_average_branch_extension G T X d D (k q) (t q) (fun i => t i.val) (edge q) he hk
        (hXcard.trans hroom) hdegree hdeg hTX hundom hcount'
    have hZcost : Z.card ≤ cost q := hZcard.trans
      ((candidateCost_antitone_order (Nat.sub_le_sub_left hXcard (Fintype.card V))
        (Nat.sub_pos_of_lt hremaining) D (k q) (edge q)).trans hcost)
    let U : Fin (q + 1) → Finset V := Fin.snoc T Z
    have hUunion : univ.biUnion U = Z ∪ X := by
      ext v
      simp [U, X, Fin.exists_fin_succ', or_comm]
    refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hUunion]
      calc
        (Z ∪ X).card ≤ Z.card + X.card := card_union_le _ _
        _ ≤ cost q + chargedBudget cost q := Nat.add_le_add hZcost hXcard
        _ = chargedBudget cost (q + 1) := by rw [chargedBudget, Nat.add_comm]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i <;>
        dsimp only [U]
      · rw [Fin.snoc_last]; exact hZconn
      · rw [Fin.snoc_castSucc]; exact hT j
    · intro i j hij
      revert hij
      refine Fin.lastCases ?_ (fun a => ?_) i <;>
        simp only [U, Fin.snoc_last, Fin.snoc_castSucc]
      · refine Fin.lastCases ?_ (fun b => ?_) j <;>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        · intro h; exact (h rfl).elim
        · intro _
          exact hZX.mono_right (hTX b)
      · refine Fin.lastCases ?_ (fun b => ?_) j <;>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        · intro _
          exact (hZX.mono_right (hTX a)).symm
        · intro h
          exact hdis (fun hab => h (congrArg Fin.castSucc hab))
    · intro i j hij
      revert hij
      refine Fin.lastCases ?_ (fun a => ?_) i <;>
        simp only [U, Fin.snoc_last, Fin.snoc_castSucc]
      · refine Fin.lastCases ?_ (fun b => ?_) j <;>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        · intro h; exact (h rfl).elim
        · intro _; exact hZadj b
      · refine Fin.lastCases ?_ (fun b => ?_) j <;>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        · intro _
          obtain ⟨z, hz, w, hw, hzw⟩ := hZadj a
          exact ⟨w, hw, z, hz, hzw.symm⟩
        · intro h
          exact hadj a b (fun hab => h (congrArg Fin.castSucc hab))
    · intro i
      rw [hUunion]
      refine Fin.lastCases ?_ (fun a => ?_) i <;>
        simp only [U, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last, Fin.val_castSucc]
      · exact (card_le_card (sdiff_subset_sdiff_right _ (subset_union_right : X ⊆ Z ∪ X))).trans hZbound
      · exact (card_le_card (sdiff_subset_sdiff_right _ (subset_union_right : X ⊆ Z ∪ X))).trans
          (hundom a)

end GraphMinor.Thomason
