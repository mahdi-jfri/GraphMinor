module
public import GraphMinor.Thomason.ConnectedSelection
import GraphMinor.Thomason.BranchExtension
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Constructing all branch sets

Thomason's main theorem, page 264 (1984), repeatedly selects a small
connected branch. The branches remain disjoint and pairwise adjacent.
Each branch leaves few vertices uncovered outside their current union,
which supplies the exceptional-set bounds at the next step.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The branch-family induction in Thomason's main theorem, p. 264.
The numeric assumptions give the room and counting bound for each
successive application of the branch extension lemma. -/
theorem exists_connected_branch_family (d k q : ℕ) (hk : 0 < k)
    (hd : d ≤ Fintype.card V)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hroom : ∀ j < q, j * (k + 2 * Nat.log 2 k + 1) + (Nat.log 2 k + 3) ≤ d)
    (hcount : ∀ j < q, j * (Fintype.card V / 2 ^ k).choose k <
      (d - j * (k + 2 * Nat.log 2 k + 1)).choose k) :
    ∃ T : Fin q → Finset V,
      (∀ i, (T i).card ≤ k + 2 * Nat.log 2 k + 1 ∧
        (G.induce (T i : Set V)).Connected) ∧
      (Pairwise fun i j => Disjoint (T i) (T j)) ∧
      (∀ i j, i ≠ j → ∃ v ∈ T i, ∃ w ∈ T j, G.Adj v w) ∧
      ∀ i, (undominatedVertices G (T i) \ univ.biUnion T).card ≤
        Fintype.card V / 2 ^ k := by
  revert hroom hcount
  induction q with
  | zero =>
    intro _ _
    refine ⟨Fin.elim0, ?_, ?_, ?_, ?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
  | succ q ih =>
    intro hroom hcount
    obtain ⟨T, hT, hdis, hadj, hundom⟩ := ih
      (fun j hj => hroom j (Nat.lt_succ_of_lt hj))
      (fun j hj => hcount j (Nat.lt_succ_of_lt hj))
    let X := univ.biUnion T
    have hTX (i : Fin q) : T i ⊆ X := by
      intro v hv
      exact mem_biUnion.mpr ⟨i, mem_univ _, hv⟩
    have hXcard : X.card ≤ q * (k + 2 * Nat.log 2 k + 1) := by
      calc
        X.card ≤ ∑ i : Fin q, (T i).card := card_biUnion_le
        _ ≤ ∑ _i : Fin q, (k + 2 * Nat.log 2 k + 1) :=
          sum_le_sum (fun i _ => (hT i).1)
        _ = q * (k + 2 * Nat.log 2 k + 1) := by simp
    have hnewcount : Fintype.card (Fin q) * (Fintype.card V / 2 ^ k).choose k <
        (d - X.card).choose k := by
      simp only [Fintype.card_fin]
      exact (hcount q (Nat.lt_succ_self q)).trans_le
        (Nat.choose_le_choose k (Nat.sub_le_sub_left hXcard d))
    obtain ⟨Z, hZcard, hZX, hZconn, hZundom, hZadj⟩ :=
      exists_branch_extension G T X d (Fintype.card V / 2 ^ k) k hk hd
        (by have hr := hroom q (Nat.lt_succ_self q); omega)
        hdeg hTX hundom hnewcount
    let U : Fin (q + 1) → Finset V := Fin.cons Z T
    have hUunion : univ.biUnion U = Z ∪ X := by
      ext v
      simp [U, X, Fin.exists_fin_succ]
    refine ⟨U, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hZcard, hZconn⟩
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
      · exact (card_le_card (sdiff_subset_sdiff_right _ (subset_union_right : X ⊆ Z ∪ X))).trans hZundom
      · exact (card_le_card (sdiff_subset_sdiff_right _ (subset_union_right : X ⊆ Z ∪ X))).trans (hundom a)

end GraphMinor.Thomason
