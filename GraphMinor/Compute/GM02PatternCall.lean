module

public import GraphMinor.Compute.GM02InstallHostInput
public import GraphMinor.Compute.GM02ShiftedInjectionCall
import GraphMinor.Compute.GM02TopologicalEncodingWords
import GraphMinor.Compute.GM02TopologicalEncoding

/-!
# One fixed-pattern test for the finite minor scan

Install the plain host input and call the complete shifted injection
search. Its original word coefficient also bounds the host copy. The
copy's linear time fits the same fixed exponent as the pattern test,
and the original input is preserved for the next family member.
-/

public section
namespace GraphMinor.Compute
open Graph GraphMinor.GM02

/-- Install and test one fixed topological pattern from the finite family. -/
@[expose] noncomputable def gm02PatternCallProg (J : GM02EdgeListInput) (w : ℤ) : Cmd :=
  .seq gm02InstallHostInputProg (gm02ShiftedInjectionCallProg J w)

/-- The linear host copy adds only a fixed constant to the pattern-test polynomial coefficient. -/
@[expose] noncomputable def gm02PatternCallCoefficient (J : GM02EdgeListInput) (w : ℤ) : ℕ :=
  gm02InjectionPolynomialCoefficient (gm02PatternWidthParameter J w) J + 45

/-- One complete pattern call computes the three alternatives in polynomial time and preserves the input. -/
theorem gm02PatternCallProg_exec {W : ℕ} (J : GM02EdgeListInput) (w : ℤ)
    (G : GM02EdgeListInput) (s : State) (hsrc : s.arrs inArr = G.enc)
    (hword : wordSize (gm02InjectionWordCoefficient (gm02PatternWidthParameter J w) J) G.size ≤ W) :
    ∃ s' t, Exec W (gm02PatternCallProg J w) s s' t ∧
      t ≤ gm02PatternCallCoefficient J w *
        (G.size + 1) ^ gm02InjectionPolynomialExponent (gm02PatternWidthParameter J w) J ∧
      s'.arrs inArr = G.enc ∧
      ((s'.regs 89 = 1 ∧ ∃ L : Graph ℕ ℕ, TopologicallyContains G.graph L ∧ Nonempty (Iso J.graph L)) ∨
        (s'.regs 89 = 0 ∧ ¬∃ L : Graph ℕ ℕ, TopologicallyContains G.graph L ∧ Nonempty (Iso J.graph L)) ∨
        (s'.regs 89 = 2 ∧ w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ))) := by
  let q := gm02PatternWidthParameter J w
  let D := gm02InjectionPolynomialExponent q J
  let P := (G.size + 1) ^ D
  have hD : 1 ≤ D := by
    dsimp only [D, gm02InjectionPolynomialExponent, gm02TopologicalPolynomialExponent,
      gm02RecursivePolynomialExponent]
    omega
  have hP : 1 ≤ P := Nat.one_le_pow D _ (by omega)
  have hsize : G.size + 1 ≤ P := Nat.le_self_pow (by omega) _
  obtain ⟨hw₀, hn₀, hm₀, _, hl₀, _, _⟩ := gm02Injection_wordBounds q G J
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hword
  have hw : 3 < 2 ^ W := hw₀.trans_le hpow
  have hencBound : G.enc.length ≤ gm02InjectedInputLength G J := by
    rw [G.enc_length]
    unfold gm02InjectedInputLength
    omega
  have hencW : G.enc.length < 2 ^ W := (hencBound.trans_lt hl₀).trans_le hpow
  have hall : ∀ a ∈ G.enc, a < 2 ^ W := fun a ha =>
    (G.enc_all_lt (Nat.lt_of_succ_lt hn₀) hm₀ a ha).trans_le hpow
  obtain ⟨s₀, t₀, he₀, ht₀, hsrc₀, ha₀⟩ := gm02InstallHostInputProg_exec G.enc s hsrc
    (by omega) hencW hall
  obtain ⟨s₁, t₁, he₁, ht₁, hc, ha₁⟩ := gm02ShiftedInjectionCallProg_exec J w G s₀ hsrc₀ hw hword
  have hencP : G.enc.length ≤ 2 * P := by
    have hsmall : G.enc.length ≤ 2 * (G.size + 1) := by
      rw [G.enc_length]
      unfold GM02EdgeListInput.size
      omega
    exact hsmall.trans (Nat.mul_le_mul_left 2 hsize)
  refine ⟨s₁, t₀ + t₁, .seq he₀ he₁, ?_, ?_, hc⟩
  · change t₀ + t₁ ≤ (gm02InjectionPolynomialCoefficient q J + 45) * P
    change t₁ ≤ gm02InjectionPolynomialCoefficient q J * P + 2 at ht₁
    rw [Nat.add_mul]
    omega
  · exact (ha₁ inArr (by decide)).trans ((ha₀ inArr (by decide)).trans hsrc)

end GraphMinor.Compute
