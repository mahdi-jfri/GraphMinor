module

public import GraphMinor.Thomason.MixedSampleSelection
public import GraphMinor.Thomason.HubBranchFamily
import GraphMinor.Thomason.MixedSampleBranchExtension
import GraphMinor.Thomason.NonemptyDominationBound
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Branch families using three sample methods

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
theorem exists_mixed_sample_branch_family (d D q : ℕ) (k cost t : ℕ → ℕ) (method : ℕ → SelectionMethod)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hparam : ∀ j < q, 0 < k j ∧ chargedBudget cost j ≤ d + 1 ∧
      chargedBudget cost j < Fintype.card V ∧ D + chargedBudget cost j ≤ Fintype.card V ∧
      selectionCost (Fintype.card V - chargedBudget cost j) D (k j) (method j) ≤ cost j ∧
      (selectionUncoveredBound (Fintype.card V) D (k j) (method j) <
        (selectionCount (Fintype.card V - chargedBudget cost j) D (k j) (method j) -
          ∑ i ∈ range j, selectionExceptionBound (t i) (k j) (method j)) * (t j + 1) ∨
        (D ≤ t j ∧ (∑ i ∈ range j, selectionExceptionBound (t i) (k j) (method j)) <
          selectionCount (Fintype.card V - chargedBudget cost j) D (k j) (method j)))) :
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
    obtain ⟨hk, hroom, hremaining, hD, hcost, hcount⟩ := hparam q (Nat.lt_succ_self q)
    let X := univ.biUnion T
    change X.card ≤ chargedBudget cost q at hXcard
    have hTX (i : Fin q) : T i ⊆ X := by
      intro v hv
      exact mem_biUnion.mpr ⟨i, mem_univ _, hv⟩
    have hchoose : selectionCount (Fintype.card V - chargedBudget cost q) D (k q) (method q) ≤
        selectionCount (Fintype.card V - X.card) D (k q) (method q) :=
      selectionCount_mono_order (Nat.sub_le_sub_left hXcard _) D (k q) (method q)
    have hsum : (∑ i : Fin q, selectionExceptionBound (t i.val) (k q) (method q)) =
        ∑ i ∈ range q, selectionExceptionBound (t i) (k q) (method q) := Fin.sum_univ_eq_sum_range (fun i => selectionExceptionBound (t i) (k q) (method q)) q
    have hcount' : selectionUncoveredBound (Fintype.card V) D (k q) (method q) <
        (selectionCount (Fintype.card V - X.card) D (k q) (method q) - ∑ i : Fin q, selectionExceptionBound (t i.val) (k q) (method q)) *
          (t q + 1) ∨ (D ≤ t q ∧ (∑ i : Fin q, selectionExceptionBound (t i.val) (k q) (method q)) <
          selectionCount (Fintype.card V - X.card) D (k q) (method q)) := by
      rw [hsum]
      rcases hcount with havg | ⟨hDt, hdirect⟩
      · exact Or.inl (havg.trans_le (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hchoose _)))
      · exact Or.inr ⟨hDt, hdirect.trans_le hchoose⟩
    obtain ⟨Z, hZcard, hZX, hZconn, hZbound, hZadj⟩ :=
      exists_mixed_sample_branch_extension G T X d D (k q) (t q) (fun i => t i.val) (method q) hk
        ((Nat.add_le_add_left hXcard D).trans hD) (hXcard.trans hroom) hdegree hdeg hTX hundom hcount'
    have hZcost : Z.card ≤ cost q := hZcard.trans
      ((selectionCost_antitone_order (Nat.sub_le_sub_left hXcard (Fintype.card V))
        (Nat.sub_pos_of_lt hremaining) D (k q) (method q)).trans hcost)
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
