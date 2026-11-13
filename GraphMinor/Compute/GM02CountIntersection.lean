module

public import GraphMinor.Compute.GM02CountBits
public import GraphMinor.Compute.GM02BalancedSeparationInput
import Mathlib.Algebra.BigOperators.Fin

/-!
# Counting selected terminals

The component test in II (3.1) counts the intersection of the input
terminal subset with a component. Read the subset bit and test whether
the search label has the requested value (one for a reached vertex, zero
for a free vertex before a search). Their product is the required indicator. The
verified bit-summing loop computes the intersection size in linear time.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths Classical
open scoped BigOperators

/-- Read a subset bit and test whether a search label equals the requested value. -/
def gm02IntersectionBitExpr (subset labels : Arr) (idx : Reg) (wanted : ℕ := 1) : Expr :=
  .op .mul (.read subset (.reg idx))
    (.op .eq (.read labels (.reg idx)) (.const wanted))

/-- Count input terminals with the requested search label. -/
def gm02CountIntersectionProg (subset labels : Arr) (wanted : ℕ := 1) : Cmd :=
  gm02CountBitsProg 182 183 (.reg 40) (gm02IntersectionBitExpr subset labels 182 wanted)

/-- Summing vertex membership bits gives the exact set size. -/
theorem gm02VertexBits_sum {n : ℕ} (Q : Finset (Fin n)) :
    (gm02VertexBits Q).sum = Q.card := by
  simp [gm02VertexBits, List.sum_ofFn]

/-- The intersection-counting program returns the exact cardinality of
selected terminals whose labels equal the requested value. -/
theorem gm02CountIntersectionProg_exec {n w : ℕ} (Q R : Finset (Fin n))
    (mask : Fin n → ℕ) (wanted : ℕ) (hm : ∀ v, mask v ≤ 2)
    (hR : ∀ v, mask v = wanted ↔ v ∈ R)
    (subset labels : Arr) (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w)
    (hrn : s.regs 40 = n) (hq : s.arrs subset = gm02VertexBits Q)
    (hl : s.arrs labels = List.ofFn mask) (hwanted : wanted < 2 ^ w) :
    ∃ s' t, Exec w (gm02CountIntersectionProg subset labels wanted) s s' t ∧
      t ≤ 7 + n * 17 ∧ Keeps [182, 183] [] s s' ∧ s'.regs 183 = (Q ∩ R).card := by
  let words := gm02VertexBits (Q ∩ R)
  have hbit : ∀ v ∈ words, v ≤ 1 := by
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
    split_ifs <;> omega
  obtain ⟨s', t, hex, ht, hk, hout⟩ := gm02CountBitsProg_exec (w := w)
    182 183 (by decide) (.reg 40) (gm02IntersectionBitExpr subset labels 182 wanted) words s
    (by omega) (by simpa [words, gm02VertexBits] using hn) hbit
    (fun st hkeep => by
      simp only [words, gm02VertexBits, List.length_ofFn]
      exact eval_reg ((hkeep.1 40 (by decide)).trans hrn) hn)
    (fun st i hi hkeep hri => by
      have hin : i < n := by simpa only [words, gm02VertexBits, List.length_ofFn] using hi
      let v : Fin n := ⟨i, hin⟩
      have hqst : st.arrs subset = gm02VertexBits Q := (hkeep.2 _ (by simp)).trans hq
      have hlst : st.arrs labels = List.ofFn mask := (hkeep.2 _ (by simp)).trans hl
      have heidx := eval_reg hri (hin.trans hn)
      have heq : (.read subset (.reg 182) : Expr).eval w st =
          some (if v ∈ Q then 1 else 0) := by
        have he := eval_read (a := subset) heidx
          (by simpa [hqst, gm02VertexBits] using hin)
          (by simp only [hqst, gm02VertexBits, List.getElem_ofFn]; split_ifs <;> omega)
        simpa only [hqst, gm02VertexBits, List.getElem_ofFn, v] using he
      have hel : (.read labels (.reg 182) : Expr).eval w st = some (mask v) := by
        have he := eval_read (a := labels) heidx (by simpa [hlst] using hin)
          (by simpa only [hlst, List.getElem_ofFn] using (hm v).trans_lt hw)
        simpa only [hlst, List.getElem_ofFn, v] using he
      have hecmp := eval_eq hel (eval_const hwanted) (by omega)
      have hfit : (if v ∈ Q then 1 else 0) * (if mask v = wanted then 1 else 0) < 2 ^ w := by
        split_ifs <;> omega
      have hemul := eval_mul heq hecmp hfit
      have hword : words[i] = if v ∈ Q ∧ v ∈ R then 1 else 0 := by
        simp only [words, gm02VertexBits, List.getElem_ofFn, Finset.mem_inter, v]
      rw [hword]
      by_cases hvQ : v ∈ Q <;> by_cases hvR : v ∈ R <;>
        simpa only [gm02IntersectionBitExpr, hR v, hvQ, hvR, ↓reduceIte,
          true_and, false_and, Nat.zero_mul, Nat.mul_zero, Nat.one_mul] using hemul)
  refine ⟨s', t, hex, ?_, hk, ?_⟩
  · simpa only [gm02IntersectionBitExpr, Expr.cost, words, gm02VertexBits, List.length_ofFn] using ht
  · exact hout.trans (gm02VertexBits_sum (Q ∩ R))

end GraphMinor.Compute
