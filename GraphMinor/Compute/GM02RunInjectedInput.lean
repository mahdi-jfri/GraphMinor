module

public import GraphMinor.Compute.GM02InstallInjectedInput
public import GraphMinor.Compute.GM02ShiftedTopologicalCall

/-!
# Running the labelled test on its constructed ordinary input

Install the computed graph-pair encoding, execute the shifted program
of (4.6), and retain its three-way result in the caller. This connects
the explicit input builder to the proved containment test without
changing the original host array or the outer candidate counter.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.GM02

/-- Install and test one complete labelled pattern input. -/
@[expose] noncomputable def gm02RunInjectedInputProg (K q p : ℕ) : Cmd :=
  .seq gm02InstallInjectedInputProg (gm02ShiftedTopologicalCallProg K q p)

/-- The installed labelled input gives the exact three alternatives and retains the outer scan state. -/
theorem gm02RunInjectedInputProg_exec {W K : ℕ} (q p : ℕ)
    (x : GM02TopologicalInput) (w : ℤ) (s : State) (hK : x.edges.length ≤ K)
    (hq : max w.toNat 2 + 2 * K < q) (hsrc : s.arrs 33 = x.enc) (hw : 3 < 2 ^ W)
    (hlen : x.enc.length < 2 ^ W) (hall : ∀ a ∈ x.enc, a < 2 ^ W)
    (hword : wordSize (gm02TopologicalWordCoefficient q K) (gm02TopologicalSize x) ≤ W) :
    ∃ s' t, Exec W (gm02RunInjectedInputProg K q p) s s' t ∧
      t ≤ 16 * x.enc.length + gm02TopologicalBudget q x K + 13 ∧
      ((s'.regs 89 = 1 ∧ TopologicallyContains x.G.graph x.H) ∨
        (s'.regs 89 = 0 ∧ ¬TopologicallyContains x.G.graph x.H) ∨
        (s'.regs 89 = 2 ∧ w < (treeWidth x.G.graph x.G.finite_vertices x.G.finite_edges : ℕ))) ∧
      (∀ a, a < 1000 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 1000 + p → r ≠ 89 → (r < 83 ∨ 86 < r) → s'.regs r = s.regs r) := by
  obtain ⟨s₀, t₀, he₀, ht₀, hsrc₀, ha₀, hr₀⟩ :=
    gm02InstallInjectedInputProg_exec x.enc s hsrc (by omega) hlen hall
  obtain ⟨s₁, t₁, he₁, ht₁, hc, ha₁, hr₁⟩ :=
    gm02ShiftedTopologicalCallProg_exec q p x w s₀ hK hq hsrc₀ hw hword
  refine ⟨s₁, t₀ + t₁, .seq he₀ he₁, by omega, hc, ?_, ?_⟩
  · intro a ha
    have hne : a ≠ 1000 := Nat.ne_of_lt ha
    exact (ha₁ a ha).trans (ha₀ a hne)
  · intro r hr hr89 hcopy
    exact (hr₁ r hr hr89).trans (hr₀ r hcopy)

end GraphMinor.Compute
