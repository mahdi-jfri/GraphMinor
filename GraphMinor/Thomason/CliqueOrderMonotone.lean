module

public import GraphMinor.Thomason.CliqueMinorOfBranches
import GraphMinor.Thomason.CliqueBranchesOfMinor
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

/-!
# Restricting a clique minor and comparing density coefficients

Restrict a clique's branch sets along the inclusion of an initial
segment. The exact coefficient in XIII (5.5) increases with the target
order. Together these facts allow one verified density bound to cover
an interval of target orders.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph
universe u

/-- Restrict clique branches along the inclusion `Fin p → Fin q`. -/
theorem clique_isIsoMinor_mono {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℕ} (hpq : p ≤ q)
    (hm : IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph G)) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin p))) (Graph.ofSimpleGraph G) := by
  classical
  obtain ⟨T, hconn, hdis, hadj⟩ := exists_branches_of_clique_isIsoMinor G hm
  let f : Fin p → Fin q := Fin.castLE hpq
  have hinj : Function.Injective f := by
    intro i j hij
    have hh : (f i).val = (f j).val := congrArg (fun v : Fin q => v.val) hij
    exact Fin.ext hh
  exact clique_isIsoMinor_of_branches G (fun i => T (f i)) (fun i => hconn (f i))
    (fun _ _ hij => hdis (fun h => hij (hinj h)))
    (fun _ _ hij => hadj _ _ (fun h => hij (hinj h)))

/-- The exact Thomason coefficient increases on positive integer orders. -/
theorem thomason_coefficient_mono {a p : ℕ} (ha : 1 ≤ a) (hap : a ≤ p) :
    (2.68 : ℝ) * a * Real.sqrt (Real.logb 2 a) ≤
      (2.68 : ℝ) * p * Real.sqrt (Real.logb 2 p) := by
  have hpos : (0 : ℝ) < a := by exact_mod_cast (Nat.zero_lt_one.trans_le ha)
  have hap' : (a : ℝ) ≤ p := by exact_mod_cast hap
  have hlog := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) hpos hap'
  exact mul_le_mul (mul_le_mul_of_nonneg_left hap' (by norm_num))
    (Real.sqrt_le_sqrt hlog) (Real.sqrt_nonneg _) (by positivity)

end GraphMinor.Thomason
