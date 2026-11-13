module

public import GraphMinor.Compute.GM02ValidateChoices
public import GraphMinor.Compute.GM02DecodeDigitsArray
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Decoding and validating a candidate code

Set the digit base from the supplied host edge count, decode the fixed
number of slots, and validate all active pattern edges. Composition
proves that the resulting bit is exactly validity of the code's raw
assignment, starting with the original graph encoding and active flags.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Decode and validate the candidate code in register 190. -/
@[expose] def gm02DecodeAndValidateProg (src : Arr) (K : ℕ) : Cmd :=
  .seq (.assign 40 (.reg 11))
    (.seq (gm02DecodeDigitsArrayProg 23 (2 * K)) (gm02ValidateChoicesProg src))

/-- The complete candidate validation commands return the exact validity bit in polynomial time. -/
theorem gm02DecodeAndValidateProg_exec {w K code : ℕ} (x : GM02TopologicalInput)
    (s : State) (src : Arr) (gflags hflags : List ℕ) (hsrc23 : src ≠ 23)
    (hK : x.edges.length ≤ K) (hsrc : s.arrs src = x.enc)
    (hG : s.arrs 20 = gflags) (hGlen : gflags.length = x.G.edges.length)
    (hGbits : ∀ b ∈ gflags, b ≤ 1) (hH : s.arrs 21 = hflags)
    (hHlen : hflags.length = x.edges.length) (hHbits : ∀ b ∈ hflags, b ≤ 1)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card)
    (hm : s.regs 11 = x.G.edges.length) (hk : s.regs 15 = x.edges.length)
    (hcode : s.regs 190 = code) (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w)
    (hKw : 2 * K < 2 ^ w) (hmw : x.G.edges.length + 1 < 2 ^ w)
    (hcw : code < 2 ^ w) (hpow : (x.G.edges.length + 1) ^ (2 * K) < 2 ^ w)
    (henc : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02DecodeAndValidateProg src K) s s' t ∧
      t ≤ 12 + (2 * K) * (12 + 4 * (2 * K)) + 139 * x.edges.length ∧
      s'.regs 51 = (if gm02PortAssignmentValid x gflags hflags
        (gm02PortAssignmentOfCode x code) then 1 else 0) ∧
      s'.arrs 23 = List.ofFn (fun i : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code i.val) ∧
      (∀ a, a ≠ 23 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 32 → r ≠ 40 → (r < 42 ∨ 51 < r) →
        (r < 200 ∨ 200 + 2 * K ≤ r) → s'.regs r = s.regs r) := by
  let s₀ := s.setReg 40 x.G.edges.length
  have he₀ : Exec w (.assign 40 (.reg 11)) s s₀ 2 := .assign (eval_reg hm (by omega))
  obtain ⟨s₁, t₁, he₁, ht₁, hdigits, hr₁, ha₁⟩ :=
    gm02DecodeDigitsArrayProg_exec 23 (2 * K) s₀ (State.setReg_regs_self ..)
      ((State.setReg_regs_ne s x.G.edges.length (by decide : (190 : Reg) ≠ 40)).trans hcode)
      hmw hcw hpow hKw
  have hframe (r : Reg) (hr40 : r ≠ 40) (hr : r < 200 ∨ 200 + 2 * K ≤ r) :
      s₁.regs r = s.regs r :=
    (hr₁ r hr).trans (State.setReg_regs_ne s x.G.edges.length hr40)
  obtain ⟨s₂, t₂, he₂, ht₂, hvalid, _, ha₂, hr₂⟩ :=
    gm02ValidateChoicesProg_exec x s₁ src gflags hflags hK
      ((ha₁ src hsrc23).trans hsrc) hdigits
      ((ha₁ 20 (by decide)).trans hG) hGlen hGbits
      ((ha₁ 21 (by decide)).trans hH) hHlen hHbits
      ((hframe 16 (by decide) (Or.inl (by decide))).trans hoff)
      ((hframe 11 (by decide) (Or.inl (by decide))).trans hm)
      ((hframe 15 (by decide) (Or.inl (by decide))).trans hk)
      hw hn hKw hmw henc
  refine ⟨s₂, 2 + (t₁ + t₂), .seq he₀ (.seq he₁ he₂), by omega, hvalid,
    (congrFun ha₂ 23).trans hdigits, ?_, ?_⟩
  · intro a ha23
    exact (congrFun ha₂ a).trans (ha₁ a ha23)
  · intro r hr32 hr40 hrange hrslots
    exact (hr₂ r hr32 hrange).trans (hframe r hr40 hrslots)

end GraphMinor.Compute
