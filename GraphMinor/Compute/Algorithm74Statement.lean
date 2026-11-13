module

public import GraphMinor.Compute.Specs13

/-!
# Constants of the program for Graph Minors XIII, (7.4)

The statement of (7.4), `Algorithm74Statement`, and the definitions it uses (walls, brick
distance, `H`-paths, models of `K_p`) are in `GraphMinor/Compute/Specs13.lean` and
`GraphMinor/Compute/Wall.lean`. This file keeps the constants of the routing in the program.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Maximum horizontal column shift `W_max(p) = p(p - 1)(4p + 2) + 2p + 6` used when routing
interior terminals to their horizontal trunk rows in `J_h`. -/
def alg74MaxShift (p : ℕ) : ℕ :=
  p * (p - 1) * (4 * p + 2) + 2 * p + 6

/-- Boundary margin `M(p) = W_max(p) + p + 6` separating the interior trunk box from the outer
perimeter frame of `J_h`. -/
def alg74Margin (p : ℕ) : ℕ :=
  alg74MaxShift p + p + 6

/-- Explicit brick distance threshold `r(p)` for GM XIII (7.4):
`r(p) = 4 * M(p) + 60` for `p ≥ 2` (and `1` for `p ≤ 1`). -/
def alg74Radius (p : ℕ) : ℕ :=
  if p ≤ 1 then 1 else 4 * alg74Margin p + 60

end GraphMinor.Compute
