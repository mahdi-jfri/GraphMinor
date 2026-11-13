module

public import GraphMinor.Compute.GM02PrepareInjectedInput
public import GraphMinor.Compute.GM02RunInjectedInput
public import GraphMinor.Compute.GM02InjectedInputLength
public import GraphMinor.Compute.GM02TopologicalComplexity
import GraphMinor.Compute.GM02TopologicalEncodingWords

/-!
# Building and testing one valid vertex injection

Construct its ordinary labelled input from the host and decoded choices,
then execute (4.6) in separate working memory. The labelled program's
polynomial bound applies to the host size plus the fixed pattern size,
so the resulting budget is independent of the chosen injection.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.GM02

/-- Construct and test the labelled copy specified by decoded vertex slots. -/
@[expose] noncomputable def gm02TestValidInjectionProg (H : GM02EdgeListInput) (q : ℕ) : Cmd :=
  .seq (gm02PrepareInjectedInputProg H) (gm02RunInjectedInputProg H.edges.length q H.n)

/-- One fixed budget covers all valid vertex injections of the pattern into the host. -/
@[expose] noncomputable def gm02InjectionCandidateBudget (q : ℕ) (G H : GM02EdgeListInput) : ℕ :=
  98 + 16 * H.n + 8 * H.edges.length +
    G.n * ((gm02InjectionMembershipExpr H.n).cost + 15) + 48 * gm02InjectedInputLength G H +
    gm02TopologicalPolynomialCoefficient q H.edges.length *
      (G.size + H.size + 1) ^ gm02TopologicalPolynomialExponent q H.edges.length

private theorem candidate_frame (r : ℕ) (hr : r < 83 ∨ 89 < r) (hlt : r < 194) :
    r < 194 ∧ r ≠ 89 ∧ (r < 83 ∨ 86 < r) := by omega

/-- The complete valid-injection test gives its exact containment answer or a justified host-width report. -/
theorem gm02TestValidInjectionProg_exec {W : ℕ} (q : ℕ) (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (w : ℤ) (s : State)
    (hq : max w.toNat 2 + 2 * H.edges.length < q)
    (hw : 3 < 2 ^ W) (hn : G.n + 1 < 2 ^ W) (hmG : G.edges.length < 2 ^ W)
    (hcap : 1 + 2 * H.edges.length < 2 ^ W) (hlen : gm02InjectedInputLength G H < 2 ^ W)
    (hword : wordSize (gm02TopologicalWordCoefficient q H.edges.length) (G.size + H.size) ≤ W)
    (hG : s.arrs inArr = G.enc) (hrn : s.regs 40 = G.n)
    (hslots : ∀ i : Fin H.n, s.regs (200 + i.val) = (f i).val) :
    ∃ s' t, Exec W (gm02TestValidInjectionProg H q) s s' t ∧
      t ≤ gm02InjectionCandidateBudget q G H ∧
      ((s'.regs 89 = 1 ∧ TopologicallyContains G.graph (gm02InjectedPattern G H f).H) ∨
        (s'.regs 89 = 0 ∧ ¬TopologicallyContains G.graph (gm02InjectedPattern G H f).H) ∨
        (s'.regs 89 = 2 ∧ w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ))) ∧
      (∀ a, a < 1000 → a ≠ 29 → a ≠ 30 → a ≠ 31 → a ≠ 32 → a ≠ 33 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 194 → (r < 83 ∨ 89 < r) → s'.regs r = s.regs r) := by
  let x := gm02InjectedPattern G H f
  have hlen' : x.enc.length < 2 ^ W := (gm02InjectedPattern_enc_length G H f).trans_lt hlen
  obtain ⟨s₀, t₀, he₀, ht₀, hsrc₀, ha₀, hr₀⟩ := gm02PrepareInjectedInputProg_exec G H f s
    (by omega) hn hmG hcap hlen' hG hrn hslots
  have hall : ∀ a ∈ x.enc, a < 2 ^ W := x.enc_all_lt (by exact Nat.lt_of_succ_lt hn) hmG
    (by simpa only [x, gm02InjectedPattern_edges_length] using (by omega : H.edges.length < 2 ^ W))
  have hword' : wordSize (gm02TopologicalWordCoefficient q H.edges.length) (gm02TopologicalSize x) ≤ W := by
    simpa only [x, gm02InjectedPattern_size] using hword
  obtain ⟨s₁, t₁, he₁, ht₁, hc, ha₁, hr₁⟩ := gm02RunInjectedInputProg_exec q H.n x w s₀
    (by rw [gm02InjectedPattern_edges_length]) hq hsrc₀ hw hlen' hall hword'
  have htime := gm02TopologicalBudget_polynomial q H.edges.length x
  rw [gm02InjectedPattern_size] at htime
  refine ⟨s₁, t₀ + t₁, .seq he₀ he₁, ?_, hc, ?_, ?_⟩
  · rw [gm02InjectedPattern_enc_length] at ht₀
    rw [gm02InjectedPattern_enc_length] at ht₁
    unfold gm02InjectionCandidateBudget
    omega
  · intro a ha h29 h30 h31 h32 h33
    exact (ha₁ a ha).trans (ha₀ a h29 h30 h31 h32 h33)
  · intro r hr hshape
    obtain ⟨_, hr89, hcopy⟩ := candidate_frame r hshape hr
    have hrshift : r < 1000 + H.n := hr.trans_le ((by decide : 194 ≤ 1000).trans (Nat.le_add_right 1000 H.n))
    exact (hr₁ r hrshift hr89 hcopy).trans (hr₀ r hr)

end GraphMinor.Compute
