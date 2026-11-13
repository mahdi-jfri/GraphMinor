module

public import GraphMinor.Compute.GM02PreparePortInput
public import GraphMinor.Compute.GM02RunPortInput
public import GraphMinor.Compute.GM02PortWidthReport

/-!
# Executing the path test for one valid split candidate

Construct the actual ordinary split instance and run the proved path
program in shifted memory. Feasible and infeasible flags retain their
exact path meaning. A width report above the corrected split bound is
returned as a width report for the original host. All outer input arrays
and the candidate code register are preserved.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- Build and execute the numeric path instance for a valid candidate. -/
@[expose] noncomputable def gm02TestValidPortCodeProg (src : Arr) (K q : ℕ) : Cmd :=
  .seq (gm02PreparePortInputProg src K) (gm02RunPortInputProg q K)

/-- An explicit bound for constructing and testing one candidate's numeric split instance. -/
@[expose] noncomputable def gm02PortCandidateBudget (q : ℕ) (x : GM02TopologicalInput) (K : ℕ) : ℕ :=
  253 + 200 * (gm02FullPortSize x K * gm02FullPortSize x K) + 137 * x.edges.length +
    gm02RecursivePolynomialCoefficient q * (gm02FullPortSize x K + 1) ^ gm02RecursivePolynomialExponent q

private theorem candidate_time_bound (n m e c tp tr : ℕ)
    (hp : tp ≤ 192 + 168 * n + 105 * m) (hr : tr ≤ 16 * e + c + 13)
    (he : e ≤ 3 + 2 * n + 2 * m) : tp + tr ≤ 253 + 200 * n + 137 * m + c := by omega

private theorem candidate_frame {r : ℕ} (h : r < 32 ∨ 89 < r) :
    (r < 32 ∨ 82 < r) ∧ r ≠ 89 ∧ (r < 83 ∨ 86 < r) := by omega

/-- The actual valid-candidate test returns exact feasibility or a justified original-host width report. -/
theorem gm02TestValidPortCodeProg_exec {W K code : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (gflags hflags : List ℕ) (hsrc24 : src ≠ 24) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code))
    (w : ℤ) (q : ℕ) (hq : max w.toNat 2 + 2 * K < q)
    (hsrc : s.arrs src = x.enc) (hG : s.arrs 20 = gflags)
    (hGlen : gflags.length = x.G.edges.length) (hGbits : ∀ b ∈ gflags, b ≤ 1)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length)
    (hHbits : ∀ b ∈ hflags, b ≤ 1) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hslots : s.arrs 23 = List.ofFn (fun j : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code j.val))
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hw : 3 < 2 ^ W) (hN : gm02FullPortSize x K < 2 ^ W) (henc : x.enc.length < 2 ^ W)
    (hjoin : 3 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) + 2 * x.edges.length < 2 ^ W)
    (hword : wordSize (gm02RecursiveWordConstant q) (gm02FullPortSize x K) ≤ W) :
    ∃ s' t, Exec W (gm02TestValidPortCodeProg src K q) s s' t ∧ t ≤ gm02PortCandidateBudget q x K ∧
      (let y := gm02NumericTerminatedInput x gflags hflags code K hK edge hvalid
       (s'.regs 89 = 1 ∧ y.A.Feasible (Graph.ofSimpleGraph y.G)) ∨
       (s'.regs 89 = 0 ∧ ¬y.A.Feasible (Graph.ofSimpleGraph y.G)) ∨
       (s'.regs 89 = 2 ∧ w < treeWidth x.G.graph x.G.finite_vertices x.G.finite_edges)) ∧
      (∀ a, a < 1000 → a ≠ 24 → a ≠ 25 → a ≠ 26 → a ≠ 27 → a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ r, (r < 32 ∨ 89 < r) → r < 290 → s'.regs r = s.regs r) := by
  let y := gm02NumericTerminatedInput x gflags hflags code K hK edge hvalid
  have hkcard : k = E(gm02ActiveGraph x.H hflags).ncard := by
    simpa only [Nat.card_fin] using (Nat.card_congr edge).trans (Nat.card_coe_set_eq _)
  have hk : k ≤ K := hkcard ▸ (gm02ActivePattern_ncard_edges_le x hflags).trans hK
  have hmax := Nat.le_max_right w.toNat 2
  have hq1 : 1 ≤ q := by omega
  have hindex : y.A.index ≤ 3 * q := by
    rw [gm02NumericTerminatedInput_index]
    omega
  obtain ⟨s₀, t₀, he₀, ht₀, hinput, _, ha₀, hr₀⟩ := gm02PreparePortInputProg_exec x s src gflags hflags
    hsrc24 hK edge hvalid hsrc hG hGlen hGbits hH hHlen hHbits hmask hslots hn hm hf
      (by omega) hN henc hjoin
  obtain ⟨s₁, t₁, he₁, ht₁, hcorrect, ha₁, hr₁⟩ :=
    gm02RunPortInputProg_exec q K hq1 y s₀ hinput hindex hword hw
  refine ⟨s₁, t₀ + t₁, .seq he₀ he₁, ?_, ?_, ?_, ?_⟩
  · exact candidate_time_bound _ _ _ _ _ _ ht₀ ht₁
      (gm02NumericTerminatedInput_enc_length_le x gflags hflags code K hK edge hvalid)
  · rcases hcorrect with h | h | ⟨hflag, hwidth⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hflag, gm02Numeric_width_report x gflags hflags code K q w hK edge hvalid hq hwidth⟩)
  · intro a ha1000 h24 h25 h26 h27 h28
    exact (ha₁ a ha1000).trans (ha₀ a h24 h25 h26 h27 h28)
  · intro r hrange hr290
    obtain ⟨hp, h89, hc⟩ := candidate_frame hrange
    exact (hr₁ r (hr290.trans_le ((by decide : 290 ≤ 1000).trans (Nat.le_add_right 1000 (2 * K)))) h89 hc).trans (hr₀ r hp hr290)

end GraphMinor.Compute
