module

public import GraphMinor.Thomason.HubGeometricSelection
import GraphMinor.Thomason.HubBranchExtension
import GraphMinor.Thomason.NonemptyDominationBound
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Branch families with degree-sensitive charged costs

The degree-sensitive branch extension may choose a different number
of vertices at each stage. Sum the connection costs to control how many
vertices have been deleted. The geometric uncovered bounds and the
exceptional-family count then justify each successive extension.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

/-- The total numeric charge for the first `j` branch sets. -/
def chargedBudget (cost : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => chargedBudget cost j + cost j

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Construct pairwise adjacent connected branches from explicit numeric
conditions for selections of varying sizes. Every geometric count and
every graph extension is proved, rather than assumed. -/
theorem exists_hub_nonneighbor_branch_family (d D q : ℕ) (k cost : ℕ → ℕ)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hparam : ∀ j < q, 0 < k j ∧ chargedBudget cost j ≤ d + 1 ∧
      chargedBudget cost j < Fintype.card V ∧
      hubSelectionCost (Fintype.card V - chargedBudget cost j) D (k j) ≤ cost j ∧
      j * D.choose (k j) < (Fintype.card V - chargedBudget cost j).choose (k j)) :
    ∃ T : Fin q → Finset V,
      (univ.biUnion T).card ≤ chargedBudget cost q ∧
      (∀ i, (G.induce (T i : Set V)).Connected) ∧
      (Pairwise fun i j => Disjoint (T i) (T j)) ∧
      (∀ i j, i ≠ j → ∃ v ∈ T i, ∃ w ∈ T j, G.Adj v w) ∧
      ∀ i, (undominatedVertices G (T i) \ univ.biUnion T).card ≤ D := by
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
    obtain ⟨hk, hroom, hremaining, hcost, hcount⟩ := hparam q (Nat.lt_succ_self q)
    let X := univ.biUnion T
    change X.card ≤ chargedBudget cost q at hXcard
    have hTX (i : Fin q) : T i ⊆ X := by
      intro v hv
      exact mem_biUnion.mpr ⟨i, mem_univ _, hv⟩
    have hcount' : Fintype.card (Fin q) * D.choose (k q) <
        (Fintype.card V - chargedBudget cost q).choose (k q) := by
      simpa only [Fintype.card_fin] using hcount
    obtain ⟨Z, hZcard, hZX, hZconn, hZundom, hZadj⟩ :=
      exists_hub_branch_extension G T X d D D (Fintype.card V - chargedBudget cost q) (k q) hk
        (hXcard.trans hroom) (by omega)
        hdegree hdeg hTX hundom hcount'
    have hZne : Z.Nonempty := by
      obtain ⟨v⟩ := hZconn.nonempty
      exact ⟨v.val, v.property⟩
    have hZbound : (undominatedVertices G Z \ X).card ≤ D :=
      (card_le_card sdiff_subset).trans
        (card_undominatedVertices_le_of_nonempty G Z hZne D hdegree)
    have hZcost : Z.card ≤ cost q := hZcard.trans
      ((hubSelectionCost_antitone_order (Nat.sub_le_sub_left hXcard (Fintype.card V))
        (Nat.sub_pos_of_lt hremaining) D (k q)).trans hcost)
    let U : Fin (q + 1) → Finset V := Fin.cons Z T
    have hUunion : univ.biUnion U = Z ∪ X := by
      ext v
      simp [U, X, Fin.exists_fin_succ]
    refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hUunion]
      calc
        (Z ∪ X).card ≤ Z.card + X.card := card_union_le _ _
        _ ≤ cost q + chargedBudget cost q := Nat.add_le_add hZcost hXcard
        _ = chargedBudget cost (q + 1) := by rw [chargedBudget, Nat.add_comm]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hZconn
      · exact hT j
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun a => ?_) i
      · refine Fin.cases ?_ (fun b => ?_) j
        · intro h; exact (h rfl).elim
        · intro _
          exact hZX.mono_right (hTX b)
      · refine Fin.cases ?_ (fun b => ?_) j
        · intro _
          exact (hZX.mono_right (hTX a)).symm
        · intro h
          exact hdis (fun hab => h (congrArg Fin.succ hab))
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun a => ?_) i
      · refine Fin.cases ?_ (fun b => ?_) j
        · intro h; exact (h rfl).elim
        · intro _; exact hZadj b
      · refine Fin.cases ?_ (fun b => ?_) j
        · intro _
          obtain ⟨z, hz, w, hw, hzw⟩ := hZadj a
          exact ⟨w, hw, z, hz, hzw.symm⟩
        · intro h
          exact hadj a b (fun hab => h (congrArg Fin.succ hab))
    · intro i
      rw [hUunion]
      refine Fin.cases ?_ (fun a => ?_) i
      · exact (card_le_card (sdiff_subset_sdiff_right _ (subset_union_right : X ⊆ Z ∪ X))).trans hZbound
      · exact (card_le_card (sdiff_subset_sdiff_right _ (subset_union_right : X ⊆ Z ∪ X))).trans
          (hundom a)

end GraphMinor.Thomason
