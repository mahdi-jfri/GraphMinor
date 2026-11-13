module

public import GraphMinor.Crossing.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Relation

/-!
# The bounded-flow network and its cut (Sections 2.1 and 2.2 of the note)

Section 2.1 of `docs/crossing/crossing_extractor.tex` computes internally disjoint `z`-`x` paths by
unit augmentations in the split network:

* each vertex `v` becomes two nodes `v_in` and `v_out`;
* the arc `v_in → v_out` has capacity `1`, except at `z` and `x`, where its capacity is `k + 1`;
* for every edge `uv` there are the arcs `u_out → v_in` and `v_out → u_in`, each of capacity
  `k + 1`;
* the source is `z_out` and the sink is `x_in`.

A node of the network is a pair `(v, b)`: `(v, false)` is `v_in` and `(v, true)` is `v_out`.

* `splitCap J T z x k`: the capacities, for the graph `J` with vertex set `T`.
* `IsFlow`, `flowValue`: flows and their values.
* `ResAdj`, `ResReach`: the residual graph and reachability in it.
* `sinkCut`: the set `W` of "nodes of the network that *cannot reach the sink in the residual
  graph*" (Section 2.2).
* `extractCut`: the separator `S = {v : v_in ∈ W, v_out ∉ W}` (Section 2.2).
-/

@[expose] public section

namespace GraphMinor.Crossing

open SimpleGraph

variable {W : Type*}

open Classical in
/-- **The capacities of the split network** (Section 2.1), for the graph `J` with vertex set `T`,
source `z`, sink `x`, and the number `k` of asked paths. The arcs are `v_in → v_out` for the
vertices `v` of `T`, of capacity `1` except `k + 1` at `z` and `x`, and `u_out → v_in` for the
edges `uv` of `J` inside `T`, of capacity `k + 1`. Every other pair has capacity `0`. -/
noncomputable def splitCap (J : SimpleGraph W) (T : Set W) (z x : W) (k : ℕ) :
    W × Bool → W × Bool → ℕ
  | (v, false), (v', true) => if v = v' ∧ v ∈ T then (if v = z ∨ v = x then k + 1 else 1) else 0
  | (u, true), (v, false) => if u ∈ T ∧ v ∈ T ∧ J.Adj u v then k + 1 else 0
  | _, _ => 0

variable {N : Type*} [Fintype N]

/-- A flow `f` from `src` to `snk` for the capacities `cap`: it respects the capacities and is
conserved at every node other than `src` and `snk`. -/
def IsFlow (cap : N → N → ℕ) (src snk : N) (f : N → N → ℕ) : Prop :=
  (∀ a b, f a b ≤ cap a b) ∧ ∀ a, a ≠ src → a ≠ snk → ∑ b, f b a = ∑ b, f a b

/-- The value of a flow: what leaves the source minus what enters it. -/
def flowValue (src : N) (f : N → N → ℕ) : ℤ :=
  (∑ b, (f src b : ℤ)) - ∑ b, (f b src : ℤ)

/-- The residual graph: an arc `a → b` with spare capacity, or with flow on `b → a` to cancel. -/
def ResAdj (cap : N → N → ℕ) (f : N → N → ℕ) (a b : N) : Prop :=
  f a b < cap a b ∨ 0 < f b a

/-- Reachability in the residual graph. -/
def ResReach (cap : N → N → ℕ) (f : N → N → ℕ) (a b : N) : Prop :=
  Relation.ReflTransGen (ResAdj cap f) a b

/-- The set `W` of Section 2.2: "the set of nodes of the network that *cannot reach the sink in
the residual graph*". -/
def sinkCut (cap : N → N → ℕ) (f : N → N → ℕ) (snk : N) : Set N :=
  {a | ¬ ResReach cap f a snk}

open Classical in
/-- **The extracted separator** (Section 2.2): `S = {v : v_in ∈ W, v_out ∉ W}`,
for a flow `f` in the split network of `J` on `T` from `z_out` to `x_in`. -/
noncomputable def extractCut [Fintype W] (J : SimpleGraph W) (T : Set W) (z x : W) (k : ℕ)
    (f : W × Bool → W × Bool → ℕ) : Finset W :=
  Finset.univ.filter fun v =>
    (v, false) ∈ sinkCut (splitCap J T z x k) f (x, false) ∧
      (v, true) ∉ sinkCut (splitCap J T z x k) f (x, false)

end GraphMinor.Crossing
