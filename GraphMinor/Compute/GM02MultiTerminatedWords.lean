module

public import GraphMinor.Compute.GM02MultiTerminatedEncoding
public import GraphMinor.Compute.GM02RecursiveWordSize
import GraphMinor.Compute.GM02RecursiveInstanceWords
import Mathlib.Tactic.Linarith

/-!
# Word range and answer transfer for the final simple reduction

The original multiplicity encoding has only quadratically many active
pair triples. Its array length and all accessed header/endpoint words
therefore fit the same root word range as A2. A2's three outcomes
transfer back through numbering, and its width threshold is strictly
stronger than the width requested in II (3.2).
-/

public section
namespace GraphMinor.Compute

/-- The original and reduced plain encodings fit one common root-size word range. -/
theorem gm02MultiTerminated_wordBounds (q w : ℕ) (x : GM02MultiTerminatedInput)
    (hw : wordSize (gm02RecursiveWordConstant q) x.n ≤ w) :
    3 < 2 ^ w ∧ x.n < 2 ^ w ∧ x.enc.length < 2 ^ w ∧ x.simple.enc.length < 2 ^ w := by
  obtain ⟨h4, _⟩ := gm02Recursive_fixed_wordBounds q x.n w hw
  obtain ⟨hn, hsimple, _⟩ := gm02Recursive_instance_wordBounds q x.n w x.simple le_rfl hw
  have hc := (gm02RecursiveWordConstant_bounds q).2.1
  have hpoly : 3 + 3 * x.n ^ 2 + x.n ≤ (x.n + 2) ^ 3 := by
    nlinarith [Nat.zero_le (x.n * x.n * x.n)]
  have hpow : (x.n + 2) ^ 3 ≤ (x.n + 2) ^ gm02RecursiveWordConstant q :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hOrig : x.enc.length < 2 ^ w :=
    ((x.enc_length_le.trans hpoly).trans hpow).trans_lt
      ((pow_lt_two_pow_wordSize (by omega : 1 ≤ gm02RecursiveWordConstant q) x.n).trans_le
        (Nat.pow_le_pow_right (by decide) hw))
  exact ⟨by omega, hn, hOrig, hsimple⟩

/-- The reduced three-way answer gives precisely an original-graph answer when the threshold exceeds the requested width. -/
theorem GM02MultiTerminatedInput.correct_of_simple (x : GM02MultiTerminatedInput)
    (q : ℕ) (w : ℤ) (s : State) (hthreshold : w < (q : ℤ))
    (h : x.simple.recursiveCorrect q s) : x.correct w s := by
  rcases h with ⟨hflag, hfeas⟩ | ⟨hflag, hnot⟩ | ⟨hflag, hwidth⟩
  · exact Or.inl ⟨hflag, x.simple_feasible_iff.mp hfeas⟩
  · exact Or.inr (Or.inl ⟨hflag, fun hf => hnot (x.simple_feasible_iff.mpr hf)⟩)
  · rw [x.simple_width] at hwidth
    have hcast : (q : ℤ) ≤ (GraphMinor.GM02.treeWidth x.G.toGMDigraph.toGraph
        x.G.isFinite_toGMDigraph.finite_V x.G.isFinite_toGMDigraph.finite_E : ℕ) := by
      exact_mod_cast hwidth
    exact Or.inr (Or.inr ⟨hflag, hthreshold.trans_le hcast⟩)

end GraphMinor.Compute
