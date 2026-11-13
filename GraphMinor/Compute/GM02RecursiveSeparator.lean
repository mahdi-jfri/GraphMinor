module

public import GraphMinor.Compute.GM02BuildSeparatorInput
public import GraphMinor.Compute.GM02BalancedComplexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The executable separator step of II's alternating recursion

Construct the graph-and-subset input specified by the phase and run the
proved program for (3.1). The output is an actual balanced separation or
a valid rejection. Constructing the input fits within the separator
program's polynomial bound. Arrays outside the constructor buffers and
the separator's written-array set remain available to the recursion.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Step 1 of A1 or A2: build its input and execute (3.1). -/
def gm02RecursiveSeparatorProg (allVertices : Bool) (k : ℕ) (src graph bits : Arr) : Cmd :=
  .seq (gm02BuildSeparatorInputProg allVertices src graph bits inArr) (gm02BalancedSeparationProg k)

private theorem input_build_time_le (n m j : ℕ) (hm : m ≤ n * n) (hj : 2 * j ≤ n) :
    150 + 64 * m + 30 * n + 28 * j ≤ 150 * (n + 1) ^ 2 := by
  nlinarith

/-- The separator stage of both recursive routines, with actual output
arrays, a polynomial time bound, and preservation of unused arrays. -/
theorem gm02RecursiveSeparatorProg_exec_bits {w k : ℕ} (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (src graph bits : Arr) (hsg : src ≠ graph) (hsb : src ≠ bits)
    (hgb : graph ≠ bits) (hg0 : graph ≠ inArr) (hb0 : bits ≠ inArr)
    (s : State) (hsrc : s.arrs src = x.enc)
    (hw : 4 < 2 ^ w) (hlen : x.enc.length < 2 ^ w)
    (hsep : 2 + 2 * (edgeListOf x.G).length + x.n < 2 ^ w)
    (hn : 3 * x.n < 2 ^ w) (hb : x.n + 1 < 2 ^ w) (hp : (x.n + 1) ^ k < 2 ^ w) :
    ∃ s' t, Exec w (gm02RecursiveSeparatorProg allVertices k src graph bits) s s' t ∧
      t ≤ (10000 * (k + 1) ^ 2 + 150) * (x.n + 1) ^ (k + 3) ∧
      (gm02RecursiveSeparatorInput allVertices x).correct (k : ℤ) s' ∧
      (s'.regs outReg = 1 → ∃ L R : Finset (Fin x.n),
        s'.arrs outArr = gm02VertexBits L ∧ s'.arrs 2 = gm02VertexBits R) ∧
      (∀ a, a ≠ graph → a ≠ bits → a ≠ inArr →
        a ∉ (gm02BalancedSeparationProg k).writtenArrs → s'.arrs a = s.arrs a) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hin₁, ha₁, _⟩ := gm02BuildSeparatorInputProg_exec allVertices x
    src graph bits inArr hsg hsb hgb hg0 hb0 s hsrc hlen hsep
  obtain ⟨s₂, t₂, he₂, ht₂, hout, hbits⟩ := gm02BalancedSeparationProg_exec_bits
    (gm02RecursiveSeparatorInput allVertices x) s₁ hw
    (by simpa only [gm02RecursiveSeparatorInput, GM02Alg31Input.enc_length] using hsep)
    hn hb hp hin₁
  have hbuild := input_build_time_le x.n (edgeListOf x.G).length x.A.index
    (gm02EdgeList_length_le_sq x.G) x.support_size_bound
  have hpow : (x.n + 1) ^ 2 ≤ (x.n + 1) ^ (k + 3) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hsmall : t₁ ≤ 150 * (x.n + 1) ^ (k + 3) :=
    ht₁.trans (hbuild.trans (Nat.mul_le_mul_left 150 hpow))
  have hlarge : t₂ ≤ 10000 * (k + 1) ^ 2 * (x.n + 1) ^ (k + 3) :=
    ht₂.trans (gm02BalancedTime_polynomial k x.n (edgeListOf x.G).length
      (gm02EdgeList_length_le_sq x.G))
  refine ⟨s₂, t₁ + t₂, Exec.seq he₁ he₂, ?_, hout, hbits, ?_⟩
  · calc
      t₁ + t₂ ≤ 150 * (x.n + 1) ^ (k + 3) +
          10000 * (k + 1) ^ 2 * (x.n + 1) ^ (k + 3) := Nat.add_le_add hsmall hlarge
      _ = _ := by ring
  · intro a hag hab ha0 ha
    rw [he₂.arrs_eq_of_not_mem_writtenArrs ha, ha₁ a hag hab ha0]

/-- The executable separator stage with its valid-output and time guarantees. -/
theorem gm02RecursiveSeparatorProg_exec {w k : ℕ} (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (src graph bits : Arr) (hsg : src ≠ graph) (hsb : src ≠ bits)
    (hgb : graph ≠ bits) (hg0 : graph ≠ inArr) (hb0 : bits ≠ inArr)
    (s : State) (hsrc : s.arrs src = x.enc)
    (hw : 4 < 2 ^ w) (hlen : x.enc.length < 2 ^ w)
    (hsep : 2 + 2 * (edgeListOf x.G).length + x.n < 2 ^ w)
    (hn : 3 * x.n < 2 ^ w) (hb : x.n + 1 < 2 ^ w) (hp : (x.n + 1) ^ k < 2 ^ w) :
    ∃ s' t, Exec w (gm02RecursiveSeparatorProg allVertices k src graph bits) s s' t ∧
      t ≤ (10000 * (k + 1) ^ 2 + 150) * (x.n + 1) ^ (k + 3) ∧
      (gm02RecursiveSeparatorInput allVertices x).correct (k : ℤ) s' ∧
      (∀ a, a ≠ graph → a ≠ bits → a ≠ inArr →
        a ∉ (gm02BalancedSeparationProg k).writtenArrs → s'.arrs a = s.arrs a) := by
  obtain ⟨s', t, he, ht, hout, _, ha⟩ := gm02RecursiveSeparatorProg_exec_bits
    allVertices x src graph bits hsg hsb hgb hg0 hb0 s hsrc hw hlen hsep hn hb hp
  exact ⟨s', t, he, ht, hout, ha⟩

end GraphMinor.Compute
