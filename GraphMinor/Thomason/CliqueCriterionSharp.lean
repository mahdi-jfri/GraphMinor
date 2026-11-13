module
public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Data.Nat.Log
import GraphMinor.Thomason.BranchFamilySharp
import GraphMinor.Thomason.CompleteBoundary
import Lean.Elab.Tactic.Omega

/-!
# A clique criterion with the exact exceptional-set count

The connected-branch induction reduces clique containment to two
inequalities on integer parameters. Monotonicity of binomial
coefficients means that it is enough to check the last stage. This is
the counting route in Thomason (1984), main theorem, pp. 263–264.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A sufficient finite-parameter criterion for a clique minor from
Thomason's branch construction. The surplus `d` is an integer lower
bound on twice each degree minus the order. -/
theorem clique_isIsoMinor_of_counting_sharp (d k q N : ℕ) (hk : 0 < k)
    (hd : d + 3 ≤ Fintype.card V) (hN : Fintype.card V ≤ N)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hroom : (q - 1) * (k + 2 * Nat.log 2 k + 1) + Nat.log 2 k ≤ d)
    (hcount : (q - 1) * (N / 2 ^ k).choose k <
      (d - (q - 1) * (k + 2 * Nat.log 2 k + 1) + 3).choose k) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph G) := by
  have hroom' : ∀ j < q,
      j * (k + 2 * Nat.log 2 k + 1) + Nat.log 2 k ≤ d := by
    intro j hj
    exact (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (by omega : j ≤ q - 1)) _).trans hroom
  have hcount' : ∀ j < q, j * (Fintype.card V / 2 ^ k).choose k <
      (d - j * (k + 2 * Nat.log 2 k + 1) + 3).choose k := by
    intro j hj
    have hj' : j ≤ q - 1 := by omega
    calc
      j * (Fintype.card V / 2 ^ k).choose k ≤ (q - 1) * (N / 2 ^ k).choose k :=
        Nat.mul_le_mul hj' (Nat.choose_le_choose k (Nat.div_le_div_right hN))
      _ < (d - (q - 1) * (k + 2 * Nat.log 2 k + 1) + 3).choose k := hcount
      _ ≤ (d - j * (k + 2 * Nat.log 2 k + 1) + 3).choose k :=
        Nat.choose_le_choose k
          (Nat.add_le_add_right (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ hj') d) 3)
  obtain ⟨T, hT, hdis, hadj, _⟩ :=
    exists_connected_branch_family_sharp G d k q hk hd hdeg hroom' hcount'
  exact clique_isIsoMinor_of_branches G T (fun i => (hT i).2) hdis hadj

/-- The exact exceptional-set criterion without an additional order
restriction: the complete-graph boundary supplies the clique directly. -/
theorem clique_isIsoMinor_of_counting_exact [Nonempty V]
    (d k q N : ℕ) (hk : 0 < k) (hN : Fintype.card V ≤ N)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v)
    (hroom : (q - 1) * (k + 2 * Nat.log 2 k + 1) + Nat.log 2 k ≤ d)
    (hcount : (q - 1) * (N / 2 ^ k).choose k <
      (d - (q - 1) * (k + 2 * Nat.log 2 k + 1) + 3).choose k) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph G) := by
  by_cases hd : d + 3 ≤ Fintype.card V
  · exact clique_isIsoMinor_of_counting_sharp G d k q N hk hd hN hdeg hroom hcount
  · have hcomplete := complete_of_large_degree_surplus G d (by omega) hdeg
    apply clique_isIsoMinor_of_complete G hcomplete q
    have hl : 0 < k + 2 * Nat.log 2 k + 1 := by omega
    have hq := Nat.le_mul_of_pos_right (q - 1) hl
    let u := Classical.arbitrary V
    have hdu := hdeg u
    have hlt := G.degree_lt_card_verts u
    omega

end GraphMinor.Thomason
