module

public import GraphMinor.GM07.Defs

/-!
# An explicit bound for the integer `w(Σ, k, n)` of Graph Minors VII, (3.6)

Graph Minors VII, (3.6) gives an integer `w(Σ, k, n)` by a finiteness argument: there are only
finitely many classes of matchings and forests, and one takes a maximum over them. So its value is
not known, and neither is any bound computed from it. In this library `wSurface S k n` is the least
`w` with `IsW36Bound S k n w`.

Lokshtanov, Pilipczuk, Pilipczuk and Saurabh (*Highly unbreakable graph with a fixed excluded minor
are almost rigid*, arXiv:2210.14629v1, Appendix A, Theorem A.2) prove an explicit bound, from a
theorem of Geelen, Huynh and Richter (*Explicit bounds for graph minors*, J. Combin. Theory Ser. B
132 (2018), Theorem 1.3). For the surface `Σ(a, b, c)`, a matching of size `n` and a forest with `k`
ends on the boundary, the bound is `2k · 3^(2n + 3(2a + b) + c + k)`. The definition `wExplicit`
adds `k` to it, which leaves room for the points of the boundary that the matching and the forest
share.

This file states the bound as `WExplicitStatement`. Since `IsW36Bound S k n w` holds for every `w`
above a value that satisfies it, the statement gives `wSurface (SurfaceModel a b c) k n ≤
wExplicit a b c k n` (`wSurface_le_wExplicit_of`).
-/

@[expose] public section

namespace GraphMinor.GM07

open GraphMinor.Surface

/-- The explicit value for `w(Σ(a, b, c), k, n)`: the bound `2k · 3^(2n + 3(2a + b) + c + k)` of
Lokshtanov, Pilipczuk, Pilipczuk and Saurabh (arXiv:2210.14629v1, Appendix A, Theorem A.2), plus
`k` for the points of the boundary that the matching and the forest share. -/
def wExplicit (a b c k n : ℕ) : ℕ :=
  2 * k * 3 ^ (2 * n + 3 * (2 * a + b) + c + k) + k

/-- Graph Minors VII, (3.6) with the explicit value `wExplicit a b c k n` in place of
`w(Σ(a, b, c), k, n)`. -/
def WExplicitStatement : Prop :=
  ∀ a b c k n : ℕ, IsW36Bound (SurfaceModel a b c) k n (wExplicit a b c k n)

/-- The least integer of (3.6) is at most the explicit value. -/
theorem wSurface_le_wExplicit_of (h : WExplicitStatement) (a b c k n : ℕ) :
    wSurface (SurfaceModel a b c) k n ≤ wExplicit a b c k n :=
  Nat.sInf_le (h a b c k n)

end GraphMinor.GM07
