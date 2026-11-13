module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.GCongr

/-!
# Graph Minors XXI, proof of (6.4): cuts

In the proof of (6.4) (page 25 of the preprint), a *good line* $F$ is a proper line with both
ends in $V(\Gamma)$ and no internal point in $U(\Gamma)$, and $\Delta(F)$ is the closed disc that
it cuts off on the side of $F^*$. All vertices of `Γ` in `bd(Σ)` lie on the line `F*`, so each jump
has two ends at positions `lo J < hi J` along `F*`. A *cut* is an interval `[x, y]` of positions
together with a flag that says whether a jump with ends exactly at `x` and `y` counts as inside; it
stands for a good line with ends at `x` and `y`, and the jumps inside the cut are those in the disc
`Δ(F)`. Claim (4) of the paper says that there is no chain of `n` nested cuts in which every step
loses a jump (`IsStrictChain`).

The count of the jumps through the tree of regions of `Γ` is in `Section6FourTree`,
`Section6FourCount` and `Section6FourPaths`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Cuts

open Set

universe u

/-- A cut: an interval `[x, y]` of positions along `F*`, and a flag `incl` that says whether a
jump with ends exactly `x` and `y` counts as inside the cut. -/
structure Cut where
  /-- The left end. -/
  x : ℝ
  /-- The right end. -/
  y : ℝ
  /-- Whether a jump with ends `x` and `y` is inside. -/
  incl : Bool

variable {ι : Type u} (lo hi : ι → ℝ) (T : Set ι) (Pos : Set ℝ)

/-- The jump `J` is inside the cut `c`. -/
def Inside (c : Cut) (J : ι) : Prop :=
  c.x ≤ lo J ∧ hi J ≤ c.y ∧ (c.incl = true ∨ lo J ≠ c.x ∨ hi J ≠ c.y)

/-- The jumps of `T` inside the cut `c`. -/
def insideSet (c : Cut) : Set ι := {J ∈ T | Inside lo hi c J}

/-- The cut `c` is admissible: its ends are positions of vertices, `x < y`, and no jump of `T`
crosses it. -/
def Admissible (c : Cut) : Prop :=
  c.x ∈ Pos ∧ c.y ∈ Pos ∧ c.x < c.y ∧
    ∀ J ∈ T, ¬ (c.x < lo J ∧ lo J < c.y ∧ c.y < hi J) ∧ ¬ (lo J < c.x ∧ c.x < hi J ∧ hi J < c.y)

/-- The cut `c'` is nested in `c`: its interval is inside that of `c`, and so are its jumps. This
is "$\Delta(F') \subseteq \Delta(F)$". -/
def Nested (c c' : Cut) : Prop :=
  c.x ≤ c'.x ∧ c'.y ≤ c.y ∧ insideSet lo hi T c' ⊆ insideSet lo hi T c

/-- A strict chain of `k` cuts: admissible, nested, and each loses a jump of the one before. -/
def IsStrictChain {k : ℕ} (c : Fin k → Cut) : Prop :=
  (∀ i, Admissible lo hi T Pos (c i)) ∧ (∀ i j, i < j → Nested lo hi T (c i) (c j)) ∧
    ∀ (i : Fin k) (h : i.1 + 1 < k), ¬ insideSet lo hi T (c i) ⊆ insideSet lo hi T (c ⟨i.1 + 1, h⟩)

end Cuts
end GM21
end GraphMinor
