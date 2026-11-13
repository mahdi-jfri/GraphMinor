module

public import GraphMinor.Thomason.ConnectedDominators
import GraphMinor.Thomason.GeometricBranchExtension
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Branch families with varying selection sizes

The degree-sensitive branch extension may choose a different number
of vertices at each stage. Sum the connection costs to control how many
vertices have been deleted. The geometric uncovered bounds and the
exceptional-family count then justify each successive extension.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

/-- The total allowed order of the first `j` connected branch sets,
when the `i`-th selection has `k(i)` vertices. -/
def selectionBudget (k : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => selectionBudget k j + (2 * k j - 1)

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Construct pairwise adjacent connected branches from explicit numeric
conditions for selections of varying sizes. Every geometric count and
every graph extension is proved, rather than assumed. -/
theorem exists_geometric_branch_family (d D q : ℕ) (k M t : ℕ → ℕ)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hparam : ∀ j < q,
      0 < k j ∧ selectionBudget k j < d ∧
      M j + selectionBudget k j ≤ Fintype.card V ∧ t j ≤ t (j + 1) ∧
      j * (t j).choose (k j) < (M j).choose (k j) ∧
      ∀ x ≤ selectionBudget k j,
        (Fintype.card V - x) * D ^ k j /
          (Fintype.card V - x + 1 - M j) ^ k j ≤ t (j + 1)) :
    ∃ T : Fin q → Finset V,
      (univ.biUnion T).card ≤ selectionBudget k q ∧
      (∀ i, (G.induce (T i : Set V)).Connected) ∧
      (Pairwise fun i j => Disjoint (T i) (T j)) ∧
      (∀ i j, i ≠ j → ∃ v ∈ T i, ∃ w ∈ T j, G.Adj v w) ∧
      ∀ i, (undominatedVertices G (T i) \ univ.biUnion T).card ≤ t q := by
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
    obtain ⟨hk, hroom, hM, htmono, hcount, hdecay⟩ := hparam q (Nat.lt_succ_self q)
    let X := univ.biUnion T
    have hTX (i : Fin q) : T i ⊆ X := by
      intro v hv
      exact mem_biUnion.mpr ⟨i, mem_univ _, hv⟩
    have hcount' : Fintype.card (Fin q) * (t q).choose (k q) < (M q).choose (k q) := by
      simpa only [Fintype.card_fin] using hcount
    obtain ⟨Z, hZcard, hZX, hZconn, hZundom, hZadj⟩ :=
      exists_geometric_branch_extension G T X d D (t q) (M q) (k q) hk
        (hXcard.trans_lt hroom) ((Nat.add_le_add_left hXcard _).trans hM)
        hdegree hdeg hTX hundom hcount'
    have hZbound : (undominatedVertices G Z \ X).card ≤ t (q + 1) :=
      hZundom.trans (hdecay X.card hXcard)
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
          ((hundom a).trans htmono)

end GraphMinor.Thomason
