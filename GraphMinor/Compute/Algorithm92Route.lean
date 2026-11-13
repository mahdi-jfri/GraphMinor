module

public import GraphMinor.Compute.Algorithm92F
public import GraphMinor.Compute.Algorithm92Search

/-!
# Graph Minors XIII, (9.2): the route of the algorithm (`Algorithm92Route.lean`)

Page 101 of Graph Minors XIII: "First, we determine $F$. This takes time $O(\varepsilon)$. Since the
size of $F$ is bounded (exept for divalent vertices) by a function of $l, m$, and $p$, we can find
an $(l, m)$-star or a model of $K_p$ in $H \cup F$ in time $\le C\varepsilon(G)$."

This file puts the steps together, as mathematics: from an `H`-path for each subwall, build `F`
(`fSegs`), compress `H ∪ F` (`compressInput`), read the answer for the compressed input from the
table (`table92`), and lift it to `G` (`exists_isAlg92Output_of_isFSystem`).

* `Alg92Input.weaken`: an input with distance bound `r` is also an input with any smaller bound.
  The algorithm uses `r ≥ 1`, so that distinct subwalls are disjoint.
* `exists_isAlg92Output_of_route`: the route gives a correct output.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

variable {l m p h k r : ℕ}

/-- An input with distance bound `r` is an input with distance bound `r' ≤ r`. -/
def _root_.GraphMinor.Compute.Alg92Input.weaken {r' : ℕ} (x : Alg92Input l m p h k r)
    (hr : r' ≤ r) : Alg92Input l m p h k r' where
  n := x.n
  G := x.G
  W := x.W
  h_sub := x.h_sub
  W_sub := x.W_sub
  hW_valid := x.hW_valid
  hnondiv := x.hnondiv
  hdist a b hab u hu v hv := hr.trans (x.hdist a b hab u hu v hv)

theorem isAlg92Output_weaken {r' : ℕ} (x : Alg92Input l m p h k r) (hr : r' ≤ r)
    (out : List ℕ) : IsAlg92Output l m p (x.weaken hr) out ↔ IsAlg92Output l m p x out :=
  Iff.rfl

/-- Each subwall of an input has an `H`-path from its inside to a vertex of `H` outside it, since
it is non-dividing. -/
theorem exists_isSubwallHPath (x : Alg92Input l m p h k r) (a : Fin k) :
    ∃ P, IsSubwallHPath x.W (x.W_sub a) P := by
  obtain ⟨-, P, hne, hP, hh, hl⟩ := x.hnondiv a
  refine ⟨P, hP, fun y hy => ?_, fun y hy => ?_⟩
  · rw [List.head?_eq_some_head hne, Option.some.injEq] at hy
    rw [← hy]; exact hh
  · rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hy
    rw [← hy]; exact hl

/-- **The route of (9.2) gives a correct output.** Let every input with the parameters `k`, `r` have
a correct output (this is `exists_isAlg92Output`), let `1 ≤ r`, and let `P a` be an `H`-path for
each subwall. Then the table answer for the compressed copy of `H ∪ F`, with `F = fSegs x P`, lifts
to a correct output for `x`. -/
theorem exists_isAlg92Output_of_route (hl : 3 ≤ l)
    (hex : ∀ y : Alg92Input l m p h k r, ∃ out, IsAlg92Output l m p y out) (hr : 1 ≤ r)
    (x : Alg92Input l m p h k r) {P : Fin k → List (Fin x.n)}
    (hP : ∀ a, IsSubwallHPath x.W (x.W_sub a) (P a)) :
    ∃ out, IsAlg92Output l m p x out := by
  have hF := isFSystem_fSegs x hr hP
  have hB : (fVerts x (fSegs x P)).card ≤ bound92 h k :=
    card_fVerts_le hF (le_of_eq (length_fSegs x hr hP))
  exact exists_isAlg92Output_of_isFSystem hl hF (isAlg92Output_table92_compressInput hex hF hB)

end Alg92

end GraphMinor.Compute
