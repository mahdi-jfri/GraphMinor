module

public import GraphMinor.Thomason.CliqueMinorOfBranches
import GraphMinor.Thomason.DeletedDegree
import GraphMinor.Thomason.NearHalfConnected
public import GraphMinor.Thomason.DominatingSets
import Mathlib.Data.Fin.Tuple.Basic
import Lean.Elab.Tactic.Omega

/-!
# Using all remaining vertices as the final branch

After constructing the earlier branches, take their complement as the
last branch. The degree surplus makes it connected. Each earlier branch
leaves fewer uncovered remaining vertices than the size of the complement,
so an actual edge joins it to the last branch. No extra selection is needed.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A connected remaining graph adds the final clique branch. The
surplus and uncovered bounds here are numeric conditions on the union
of the already constructed branches. -/
theorem clique_isIsoMinor_with_remaining_branch {q : ℕ} (T : Fin q → Finset V)
    (d D : ℕ)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hconn : ∀ i, (G.induce (T i : Set V)).Connected)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hadj : ∀ i j, i ≠ j → ∃ v ∈ T i, ∃ w ∈ T j, G.Adj v w)
    (hbudget : (univ.biUnion T).card ≤ d + 1)
    (hroom : D + (univ.biUnion T).card < Fintype.card V)
    (hundom : ∀ i, (undominatedVertices G (T i) \ univ.biUnion T).card ≤ D) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 1)))) (Graph.ofSimpleGraph G) := by
  let X := univ.biUnion T
  let R := (univ : Finset V) \ X
  let s : Set V := {v | v ∉ X}
  have hTX (i : Fin q) : T i ⊆ X := by
    intro v hv
    exact mem_biUnion.mpr ⟨i, mem_univ _, hv⟩
  have hcard := card_compl_finset_add X
  have hne : Nonempty s := Fintype.card_pos_iff.mp (by
    change Fintype.card s + X.card = Fintype.card V at hcard
    change D + X.card < Fintype.card V at hroom
    omega)
  have hnear : ∀ v : s, Fintype.card s ≤ 2 * (G.induce s).degree v + 1 := by
    intro v
    have hloss := degree_le_degree_induce_compl_add G X v
    change G.degree v ≤ (G.induce s).degree v + X.card at hloss
    have hh := hdeg v
    change X.card ≤ d + 1 at hbudget
    change Fintype.card s + X.card = Fintype.card V at hcard
    omega
  have hRconn : (G.induce (R : Set V)).Connected := by
    have heq : (R : Set V) = s := by ext v; simp [R, s]
    rw [heq]
    exact connected_of_near_half (G.induce s) hnear
  have hRX : Disjoint R X := by
    apply Finset.disjoint_left.mpr
    intro v hv hx
    exact (mem_sdiff.mp hv).2 hx
  have hRadj (i : Fin q) : ∃ v ∈ R, ∃ w ∈ T i, G.Adj v w := by
    have hRcard : D < R.card := by
      have hc : R.card + X.card = Fintype.card V := by
        simpa only [R, card_univ, univ_inter] using card_sdiff_add_card_inter (univ : Finset V) X
      change D + X.card < Fintype.card V at hroom
      omega
    have hh : (undominatedVertices G (T i) \ X).card < R.card := (hundom i).trans_lt hRcard
    obtain ⟨v, hvR, hvundom⟩ := exists_mem_notMem_of_card_lt_card hh
    have hvX : v ∉ X := (mem_sdiff.mp hvR).2
    have hvdom : v ∈ dominatedVertices G (T i) := by
      by_contra h
      exact hvundom (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, h⟩, hvX⟩)
    rcases mem_union.mp hvdom with hvTi | hvN
    · exact (hvX (hTX i hvTi)).elim
    · obtain ⟨w, hw, hwv⟩ := mem_biUnion.mp hvN
      exact ⟨v, hvR, w, hw, ((G.mem_neighborFinset w v).mp hwv).symm⟩
  let U : Fin (q + 1) → Finset V := Fin.cons R T
  apply clique_isIsoMinor_of_branches G U
  · intro i
    exact Fin.cases hRconn (fun j => hconn j) i
  · intro i j hij
    revert hij
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro h; exact (h rfl).elim
      · intro _; exact hRX.mono_right (hTX b)
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro _; exact (hRX.mono_right (hTX a)).symm
      · intro h; exact hdis (fun hab => h (congrArg Fin.succ hab))
  · intro i j hij
    revert hij
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro h; exact (h rfl).elim
      · intro _; exact hRadj b
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro _
        obtain ⟨v, hv, w, hw, hvw⟩ := hRadj a
        exact ⟨w, hw, v, hv, hvw.symm⟩
      · intro h; exact hadj a b (fun hab => h (congrArg Fin.succ hab))

end GraphMinor.Thomason
