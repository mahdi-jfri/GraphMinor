module

public import GraphMinor.Compute.GM06ActiveDegreeScan
public import GraphMinor.Compute.GM06EndpointValency
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# The active endpoint counter counts the retained endpoint list

For the valency tests in VI (5.7), page 133, each active edge
contributes both of its ends. Splitting the endpoint scan into its
first pair and remaining pairs shows that its sum is precisely the
count in the activity-filtered endpoint list. In particular loops
contribute two, as required by the paper's definition of valency.
-/

public section
namespace GraphMinor.Compute
open scoped BigOperators

private theorem activeEndpointBits_sum_cons (xs mask : List ℕ) (a b u v : ℕ) :
    (gm06ActiveEndpointBits (u :: v :: xs) (b :: mask) a).sum =
      (if b = 1 then 1 else 0) * ((if u = a then 1 else 0) + (if v = a then 1 else 0)) +
        (gm06ActiveEndpointBits xs mask a).sum := by
  simp only [gm06ActiveEndpointBits, List.sum_ofFn, List.length_cons]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.zero_div, List.getElem?_cons_zero, Option.getD_some]
  have hdiv (j : ℕ) : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
  simp only [hdiv, Nat.reduceAdd, Nat.reduceDiv, List.getElem?_cons_zero, Option.getD_some,
    List.getElem?_cons_succ, Nat.mul_add, Nat.add_assoc]

  by_cases hb : b = 1 <;> simp only [hb, ite_true, ite_false] <;> congr 2


/-- Every endpoint contributes at most one to the masked valency
counter, so the counter fits within the endpoint-array length. -/
theorem gm06ActiveEndpointBits_sum_le_length (xs mask : List ℕ) (a : ℕ) :
    (gm06ActiveEndpointBits xs mask a).sum ≤ xs.length := by
  have hb : ∀ b ∈ gm06ActiveEndpointBits xs mask a, b ≤ 1 := by
    intro b hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    split <;> split <;> decide
  simpa only [smul_eq_mul, Nat.mul_one, gm06ActiveEndpointBits, List.length_ofFn] using
    List.sum_le_length_nsmul (gm06ActiveEndpointBits xs mask a) 1 hb

/-- The masked endpoint-bit sum equals the ordinary endpoint count
after filtering inactive original edge rows. -/
theorem gm06ActiveEndpointBits_sum_eq_filtered_count
    (tagged : List ((ℕ × ℕ) × ℕ)) (a : ℕ) :
    (gm06ActiveEndpointBits (gm06EndpointWords (tagged.map Prod.fst))
      (tagged.map Prod.snd) a).sum =
      (gm06EndpointWords ((tagged.filter fun p => p.2 == 1).map Prod.fst)).count a := by
  induction tagged with
  | nil => simp [gm06ActiveEndpointBits, gm06EndpointWords]
  | cons p tagged ih =>
    simp only [List.map_cons, gm06EndpointWords, List.flatMap_cons, List.cons_append,
      List.nil_append] at *
    rw [activeEndpointBits_sum_cons, ih]
    by_cases hb : p.2 = 1 <;> by_cases hu : p.1.1 = a <;> by_cases hv : p.1.2 = a <;>
      simp [hb, hu, hv, gm06EndpointWords, Nat.add_assoc, Nat.add_comm] <;> omega

end GraphMinor.Compute
