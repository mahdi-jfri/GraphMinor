module

public import GraphMinor.GM07.ExplicitW

/-!
# An explicit bound for `v(Σ(a, b, c), k)` of Graph Minors VII, Section 4

Graph Minors VII, Section 4 (page 224) defines `wMaxModel`, `muModel` and `vModel` from the
surface function `wSurface` of (3.6). Replacing `wSurface` by the explicit upper bound `wExplicit`
from `GraphMinor.GM07.ExplicitW` yields computable upper bounds `wMaxExplicit`, `muExplicit` and
`vModelExplicit`, and under `WExplicitStatement` we have `vModel a b c k ≤ vModelExplicit a b c k`.
-/

@[expose] public section

namespace GraphMinor.GM07

open GraphMinor.Surface

/-- The explicit counterpart of `wMaxModel`, with `wExplicit` in place of `wSurface`. -/
def wMaxExplicit (a b c k : ℕ) : ℕ :=
  (Finset.range (2 * (2 * a + b + c - 1) + 1)).sup fun c' =>
    wExplicit a b c' (2 * k) (3 * (2 * a + b + c - 1))

/-- The explicit counterpart of `muModel`, with `wMaxExplicit` in place of `wMaxModel`. -/
def muExplicit (a b c k : ℕ) : ℕ :=
  2 * (2 * a + b + c) * (k + wMaxExplicit a b c k) + 2 * k

/-- The explicit counterpart of `vModel`, with `wExplicit` in place of `wSurface`. -/
def vModelExplicit (a b c k : ℕ) : ℕ :=
  6 * (2 * a + b + c - 1) * (wMaxExplicit a b c k + 2 * muExplicit a b c k + 1) + 2 * k

/-- `wMaxModel` is at most `wMaxExplicit` under `WExplicitStatement`. -/
theorem wMaxModel_le_wMaxExplicit_of (hW : WExplicitStatement) (a b c k : ℕ) :
    wMaxModel a b c k ≤ wMaxExplicit a b c k :=
  Finset.sup_mono_fun fun c' _ =>
    wSurface_le_wExplicit_of hW a b c' (2 * k) (3 * (2 * a + b + c - 1))

/-- `muModel` is at most `muExplicit` under `WExplicitStatement`. -/
theorem muModel_le_muExplicit_of (hW : WExplicitStatement) (a b c k : ℕ) :
    muModel a b c k ≤ muExplicit a b c k := by
  unfold muModel muExplicit
  have hw := wMaxModel_le_wMaxExplicit_of hW a b c k
  gcongr

/-- Graph Minors VII, Section 4: `vModel a b c k` is at most `vModelExplicit a b c k` under
`WExplicitStatement`. -/
theorem vModel_le_vModelExplicit_of (hW : WExplicitStatement) (a b c k : ℕ) :
    vModel a b c k ≤ vModelExplicit a b c k := by
  unfold vModel vModelExplicit
  have hw := wMaxModel_le_wMaxExplicit_of hW a b c k
  have hμ := muModel_le_muExplicit_of hW a b c k
  gcongr

end GraphMinor.GM07
