module

public import GraphMinor.Compute.Parse
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Indexing the canonical pair scan

The canonical graph encoder lists all ordered vertex pairs in row-major
order and filters increasing adjacent pairs. Identify that list with the
finite product numbering. A single RAM loop can then recover its two
vertices by division and remainder. Filtering successive prefixes gives
the exact edge-list invariant for the split graph builder.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Canonical ordered vertex pairs are exactly the inverse finite-product numbering. -/
theorem gm02AllPairs_eq_ofFn (n : ℕ) :
    allPairs n = List.ofFn (fun i : Fin (n * n) => finProdFinEquiv.symm i) := by
  have hpair (i j : Fin n) (h : i.val * n + j.val < n * n) :
      finProdFinEquiv.symm (⟨i.val * n + j.val, h⟩ : Fin (n * n)) = (i, j) := by
    have heq : (⟨i.val * n + j.val, h⟩ : Fin (n * n)) = finProdFinEquiv (i, j) := by
      apply Fin.ext
      simp only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm, Nat.add_comm]
    rw [heq, Equiv.symm_apply_apply]
  rw [List.ofFn_mul]
  simp only [hpair, List.ofFn_eq_map, allPairs, List.flatMap_def]

/-- The ordered pair scan has exactly the square of the vertex count many positions. -/
theorem gm02AllPairs_length (n : ℕ) : (allPairs n).length = n * n := by
  rw [gm02AllPairs_eq_ofFn, List.length_ofFn]

/-- The pair at a scan position is its finite-product decoding. -/
theorem gm02AllPairs_getElem {n : ℕ} (i : Fin (n * n)) :
    (allPairs n)[i.val]'(by rw [gm02AllPairs_length]; exact i.isLt) = finProdFinEquiv.symm i := by
  simp only [gm02AllPairs_eq_ofFn, List.getElem_ofFn, Fin.eta]

/-- The first vertex at a pair-scan position is obtained by division. -/
theorem gm02AllPairs_fst {n : ℕ} (i : Fin (n * n)) :
    ((finProdFinEquiv.symm i : Fin n × Fin n).1).val = i.val / n := rfl

/-- The second vertex at a pair-scan position is obtained by remainder. -/
theorem gm02AllPairs_snd {n : ℕ} (i : Fin (n * n)) :
    ((finProdFinEquiv.symm i : Fin n × Fin n).2).val = i.val % n := rfl

/-- Increasing adjacent pairs found before a given scan position. -/
def gm02EdgePrefix {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (j : ℕ) :
    List (Fin n × Fin n) :=
  ((allPairs n).take j).filter (fun p => decide (p.1.val < p.2.val ∧ F.Adj p.1 p.2))

/-- No pairs have been emitted before the scan starts. -/
theorem gm02EdgePrefix_zero {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    gm02EdgePrefix F 0 = [] := rfl

/-- The completed scan emits exactly the canonical graph edge list. -/
theorem gm02EdgePrefix_full {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    gm02EdgePrefix F (n * n) = edgeListOf F := by
  rw [gm02EdgePrefix, ← gm02AllPairs_length, List.take_length]
  rfl

/-- Each scan position contributes at most one edge. -/
theorem gm02EdgePrefix_length_le {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (j : ℕ) :
    (gm02EdgePrefix F j).length ≤ j :=
  (List.length_filter_le _ _).trans (List.length_take_le _ _)

/-- Advancing the canonical scan appends just the next pair if it is increasing and adjacent. -/
theorem gm02EdgePrefix_succ {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (i : Fin (n * n)) :
    gm02EdgePrefix F (i.val + 1) =
      if (finProdFinEquiv.symm i : Fin n × Fin n).1.val < (finProdFinEquiv.symm i : Fin n × Fin n).2.val ∧
          F.Adj (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
      then gm02EdgePrefix F i.val ++ [finProdFinEquiv.symm i] else gm02EdgePrefix F i.val := by
  have hi : i.val < (allPairs n).length := by rw [gm02AllPairs_length]; exact i.isLt
  rw [gm02EdgePrefix, List.take_succ_eq_append_getElem hi, List.filter_append, gm02AllPairs_getElem]
  split <;> simp_all [gm02EdgePrefix, -Fin.val_fin_lt]

end GraphMinor.Compute
