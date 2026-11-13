module

public import GraphMinor.Thomason.GeometricBranchFamily
import GraphMinor.Thomason.GeometricBranchExtension
import GraphMinor.Thomason.NonemptyDominationBound
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Branch families using the nonempty-set uncovered bound

The degree-sensitive branch extension may choose a different number
of vertices at each stage. Sum the connection costs to control how many
vertices have been deleted. The geometric uncovered bounds and the
exceptional-family count then justify each successive extension.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Construct pairwise adjacent connected branches from explicit numeric
conditions for selections of varying sizes. Every geometric count and
every graph extension is proved, rather than assumed. -/
theorem exists_nonneighbor_branch_family (d D q : ℕ) (k : ℕ → ℕ)
    (hd : d ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hparam : ∀ j < q, 0 < k j ∧ selectionBudget k j < d ∧
      j * D.choose (k j) < (Fintype.card V - selectionBudget k j).choose (k j)) :
    ∃ T : Fin q → Finset V,
      (univ.biUnion T).card ≤ selectionBudget k q ∧
      (∀ i, (G.induce (T i : Set V)).Connected) ∧
      (Pairwise fun i j => Disjoint (T i) (T j)) ∧
      (∀ i j, i ≠ j → ∃ v ∈ T i, ∃ w ∈ T j, G.Adj v w) ∧
      ∀ i, (undominatedVertices G (T i) \ univ.biUnion T).card ≤ D := by
  revert hparam
  induction q with
  | zero =>
    intro _
    refine ⟨Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [selectionBudget]
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
  | succ q ih =>
    intro hparam
    obtain ⟨T, hXcard, hT, hdis, hadj, hundom⟩ :=
      ih (fun j hj => hparam j (Nat.lt_succ_of_lt hj))
    obtain ⟨hk, hroom, hcount⟩ := hparam q (Nat.lt_succ_self q)
    let X := univ.biUnion T
    change X.card ≤ selectionBudget k q at hXcard
    have hTX (i : Fin q) : T i ⊆ X := by
      intro v hv
      exact mem_biUnion.mpr ⟨i, mem_univ _, hv⟩
    have hcount' : Fintype.card (Fin q) * D.choose (k q) <
        (Fintype.card V - selectionBudget k q).choose (k q) := by
      simpa only [Fintype.card_fin] using hcount
    obtain ⟨Z, hZcard, hZX, hZconn, hZundom, hZadj⟩ :=
      exists_geometric_branch_extension G T X d D D (Fintype.card V - selectionBudget k q) (k q) hk
        (hXcard.trans_lt hroom) (by omega)
        hdegree hdeg hTX hundom hcount'
    have hZne : Z.Nonempty := by
      obtain ⟨v⟩ := hZconn.nonempty
      exact ⟨v.val, v.property⟩
    have hZbound : (undominatedVertices G Z \ X).card ≤ D :=
      (card_le_card sdiff_subset).trans
        (card_undominatedVertices_le_of_nonempty G Z hZne D hdegree)
    let U : Fin (q + 1) → Finset V := Fin.cons Z T
    have hUunion : univ.biUnion U = Z ∪ X := by
      ext v
      simp [U, X, Fin.exists_fin_succ]
    refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hUunion]
      have hc := card_union_le Z X
      change X.card ≤ selectionBudget k q at hXcard
      rw [selectionBudget]
      omega
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
