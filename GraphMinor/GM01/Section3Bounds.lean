module

public import GraphMinor.GM01.QuantitativeBounds
public import Mathlib.Algebra.Ring.Parity
import GraphMinor.GM01.QuantitativeFirstEstimates
import GraphMinor.GM01.QuantitativeLastEstimate

/-!
# The four quantitative induction inequalities

Graph Minors I, (3.6), page 53, gives four inequalities for the
functions `p` and `q` and leaves their proof to the reader. The
preceding files prove the scalar exponential margins and lift them
through the iterates. This file states their conjunction with the
printed ranges of the parameters.
-/

public section

namespace GraphMinor.GM01

/-- Graph Minors I, (3.6)(i)–(iv), page 53, with the definitions of
`θ`, `α`, `β`, `f`, `p`, and `q` on that page. The proof supplies the
four estimates that the paper leaves to the reader. -/
theorem theorem_3_6_proof {lam : ℕ} (_hlam : 1 ≤ lam) (hodd : Odd lam) :
    (∀ δ : ℕ, 2 ≤ δ → δ - 2 ≤ pathWidthBound lam 0 δ) ∧
    (∀ γ δ : ℕ, 1 ≤ γ → 2 ≤ δ →
      (gm01Theta lam) ^ 2 +
        pathWidthBound lam (γ - 1) (2 + 4 * (gm01Theta lam) ^ (2 * gm01Theta lam) + 2 * δ) ≤
        forkWidthBound lam γ δ) ∧
    (∀ γ δ : ℕ, 1 ≤ γ → 2 ≤ δ → forkWidthBound lam γ 4 ≤ pathWidthBound lam γ δ) ∧
    (∀ γ δ : ℕ, 1 ≤ γ → γ ≤ lam → 3 ≤ δ →
      (gm01Alpha lam) ^ (δ * 2 ^ γ) +
        max (pathWidthBound lam γ (δ - 1))
          (forkWidthBound lam γ (3 * (gm01Alpha lam) ^ (δ * 2 ^ γ) + 6)) ≤
        pathWidthBound lam γ δ) :=
  ⟨fun δ _ ↦ pathWidthBound_zero lam δ,
    fun γ δ _ _ ↦ forkWidthBound_separator lam γ δ,
    fun _ _ hγ hδ ↦ pathWidthBound_ge_fork_four lam hγ hδ,
    fun _ _ hγ hγlam hδ ↦ pathWidthBound_induction_margin hodd hγ hγlam hδ⟩

end GraphMinor.GM01
