module

public import Mathlib.Order.Monotone.Defs
public import Mathlib.Data.Nat.Basic
import Mathlib.Order.Monotone.Basic

/-!
# The numerical functions in the rooted induction

Graph Minors I, Section 3, page 53, defines the parameters `θ`, `α`,
and `β`, then iterates `x ↦ β^x` to obtain `f_i`. The bounds `p` and
`q` are the stated evaluations of these iterates. We prove the
monotonicity and additive growth of the iterates. These turn the
four estimates in (3.6) into inequalities between their inputs.
-/

public section

namespace GraphMinor.GM01

/-- Graph Minors I, Section 3, page 53: `θ = max(6, 2^((lam+3)/2))`,
for the positive odd parameter `lam`. -/
@[expose] def gm01Theta (lam : ℕ) : ℕ := max 6 (2 ^ ((lam + 3) / 2))

/-- Graph Minors I, Section 3, page 53: `α = 2^(θ^4)`. -/
@[expose] def gm01Alpha (lam : ℕ) : ℕ := 2 ^ ((gm01Theta lam) ^ 4)

/-- Graph Minors I, Section 3, page 53: `β = 2^(θ^6)`. -/
@[expose] def gm01Beta (lam : ℕ) : ℕ := 2 ^ ((gm01Theta lam) ^ 6)

/-- Graph Minors I, Section 3, page 53: `f_0(x) = x` and
`f_i(x) = f_(i-1)(β^x)` for positive `i`. -/
@[expose] def widthIteration (β : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | i + 1, x => widthIteration β i (β ^ x)

/-- Graph Minors I, Section 3, page 53: `p(γ,δ) = f_γ(δ)`,
used for nonnegative `γ` and `δ ≥ 2`. -/
@[expose] def pathWidthBound (lam γ δ : ℕ) : ℕ := widthIteration (gm01Beta lam) γ δ

/-- Graph Minors I, Section 3, page 53: `q(γ,δ) = f_(γ-1)(β+2δ)`,
used for positive `γ` and `δ ≥ 2`. -/
@[expose] def forkWidthBound (lam γ δ : ℕ) : ℕ :=
  widthIteration (gm01Beta lam) (γ - 1) (gm01Beta lam + 2 * δ)

/-- The initial iterate is the identity, as defined on page 53. -/
@[simp] theorem widthIteration_zero (β x : ℕ) : widthIteration β 0 x = x := rfl

/-- The next iterate first applies the exponential, as defined on page 53. -/
@[simp] theorem widthIteration_succ (β i x : ℕ) :
    widthIteration β (i + 1) x = widthIteration β i (β ^ x) := rfl

/-- Each iterate is strictly increasing when the exponential base
is greater than one, as used in the estimates (3.6). -/
theorem widthIteration_strictMono {β : ℕ} (hβ : 1 < β) (i : ℕ) :
    StrictMono (widthIteration β i) := by
  induction i with
  | zero => exact fun _ _ h ↦ h
  | succ i ih => exact ih.comp (fun _ _ h ↦ Nat.pow_lt_pow_right hβ h)

/-- Adding to an input increases its iterate by at least that much.
This supplies the additive margins in GM01 (3.6), page 53. -/
theorem widthIteration_add_le {β : ℕ} (hβ : 1 < β) (i x d : ℕ) :
    d + widthIteration β i x ≤ widthIteration β i (d + x) :=
  (widthIteration_strictMono hβ i).add_le_nat d x

/-- The maximum defining `θ` is at least six. -/
theorem gm01Theta_ge_six (lam : ℕ) : 6 ≤ gm01Theta lam := le_max_left _ _

end GraphMinor.GM01
