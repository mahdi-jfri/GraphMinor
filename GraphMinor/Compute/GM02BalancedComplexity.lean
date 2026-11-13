module

public import GraphMinor.Compute.GM02BalancedSeparationExec
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Polynomial time and logarithmic words for the separator program

A simple graph has at most the square of its vertex count edges. The
exhaustive search visits at most one plus that count raised to the fixed
separator bound. Each candidate test and the output construction have
cubic vertex-count bounds. Thus degree `k + 3` suffices for time, while a
constant multiple of the input-size logarithm suffices for all words.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- A simple edge list has at most one entry per ordered vertex pair. -/
theorem gm02EdgeList_length_le_sq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (edgeListOf G).length ≤ n * n := by
  calc
    _ ≤ (allPairs n).length := List.length_filter_le _ _
    _ = n * n := by simp [allPairs, List.length_flatMap]

/-- The detailed time bound is polynomial in the vertex count for fixed `k`. -/
theorem gm02BalancedTime_polynomial (k n m : ℕ) (hm : m ≤ n * n) :
    gm02BalancedTime k n m ≤ 10000 * (k + 1) ^ 2 * (n + 1) ^ (k + 3) := by
  let A := gm02BalancedParseTime n m + 1 + gm02BalancedOutputTime k n m + 7 + 4 * k
  let B := 35 + 4 * k + k * (8 + 4 * k) + n * (k * 6 + 36) +
    n * (91 + k * 6 + n * (k * 6 + 57) + 58 * m)
  have hN : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_le_succ (Nat.zero_le n))
  have hA : A ≤ (n + 1) ^ k * A := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right A hN
  have hpoly : A + B ≤ 10000 * (k + 1) ^ 2 * (n + 1) ^ 3 := by
    dsimp [A, B, gm02BalancedParseTime, gm02BalancedOutputTime]
    have hm' : m ≤ (n + 1) ^ 2 := by nlinarith [hm]
    calc
      _ ≤ (43 * n + 88 * ((n + 1) ^ 2) + 33) + 1 +
          (44 + k * (8 + 4 * k) + n * (185 + 18 * k + n * (k * 6 + 94) + 58 * ((n + 1) ^ 2))) +
          7 + 4 * k + (35 + 4 * k + k * (8 + 4 * k) + n * (k * 6 + 36) +
            n * (91 + k * 6 + n * (k * 6 + 57) + 58 * ((n + 1) ^ 2))) := by gcongr
      _ ≤ _ := by nlinarith [Nat.zero_le (k * k * n * n * n), Nat.zero_le (k * k * n * n),
        Nat.zero_le (k * k * n), Nat.zero_le (k * n * n * n), Nat.zero_le (k * n * n), Nat.zero_le (n * n * n)]
  calc
    gm02BalancedTime k n m = A + (n + 1) ^ k * B := by
      dsimp [A, B, gm02BalancedTime, gm02BalancedSearchTime]
      ring
    _ ≤ (n + 1) ^ k * A + (n + 1) ^ k * B := Nat.add_le_add_right hA _
    _ = (n + 1) ^ k * (A + B) := (Nat.mul_add _ _ _).symm
    _ ≤ (n + 1) ^ k * (10000 * (k + 1) ^ 2 * (n + 1) ^ 3) := Nat.mul_le_mul_left _ hpoly
    _ = 10000 * (k + 1) ^ 2 * (n + 1) ^ (k + 3) := by rw [pow_add]; ring

/-- All words used by the program fit a logarithmic word size whose
constant depends only on the fixed separator bound. -/
theorem gm02Balanced_wordBounds (k n m : ℕ) (hm : m ≤ n * n) :
    4 < 2 ^ wordSize (k + 6) n ∧ 2 + 2 * m + n < 2 ^ wordSize (k + 6) n ∧
      3 * n < 2 ^ wordSize (k + 6) n ∧ n + 1 < 2 ^ wordSize (k + 6) n ∧
      (n + 1) ^ k < 2 ^ wordSize (k + 6) n := by
  have hbig := pow_lt_two_pow_wordSize (c := k + 6) (by omega) n
  have h3 : (n + 2) ^ 3 ≤ (n + 2) ^ (k + 6) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : 4 ≤ (n + 2) ^ 3 := by nlinarith [Nat.zero_le (n * n * n)]
  have hlen : 2 + 2 * m + n ≤ (n + 2) ^ 3 := by nlinarith [hm, Nat.zero_le (n * n * n)]
  have hn : 3 * n ≤ (n + 2) ^ 3 := by nlinarith [Nat.zero_le (n * n * n)]
  refine ⟨h4.trans_lt (h3.trans_lt hbig), hlen.trans_lt (h3.trans_lt hbig),
    hn.trans_lt (h3.trans_lt hbig), lt_two_pow_wordSize_of_le (by omega) le_rfl, ?_⟩
  exact ((Nat.pow_le_pow_left (Nat.le_succ (n + 1)) k).trans
    (Nat.pow_le_pow_right (by omega) (show k ≤ k + 6 by omega))).trans_lt hbig

/-- The explicit balanced-separation program runs in polynomial time on
plain graph-and-subset encodings, with no algorithmic certificate in the input. -/
theorem gm02Alg31_nat_computes (k : ℕ) :
    ComputesRelInTime gm02Alg31Size (fun x s => s.arrs inArr = x.enc)
      (fun x s => x.correct (k : ℤ) s) (gm02BalancedSeparationProg k)
      (fun n => (n + 1) ^ (k + 3)) := by
  refine ⟨10000 * (k + 1) ^ 2, k + 6, by have hk := Nat.one_le_pow 2 (k + 1) (by omega); omega, by omega, ?_⟩
  intro x s hin
  have hm := gm02EdgeList_length_le_sq x.G
  obtain ⟨hw, hlen, hn, hb, hp⟩ := gm02Balanced_wordBounds k x.n (edgeListOf x.G).length hm
  obtain ⟨s', t, hex, ht, hout⟩ := gm02BalancedSeparationProg_exec x s hw
    (by simpa only [x.enc_length] using hlen) hn hb hp hin
  exact ⟨s', t, hex, ht.trans (gm02BalancedTime_polynomial k x.n (edgeListOf x.G).length hm), hout⟩

end GraphMinor.Compute
