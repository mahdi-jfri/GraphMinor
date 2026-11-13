module

public import GraphMinor.Crossing.Defs

/-!
# The trial contraction and its lifts (Sections 9 and 11 of the note)

Section 9 of `docs/crossing/crossing_extractor.tex` chooses an edge `uv` with `u` off the cycle
`D`, or with `u` and `v` consecutive on `D`, and then says: "Contract $uv$ to a new vertex $w$,
suppressing loops and duplicate edges. If $u\notin V(D)$, the cycle is unchanged. If both ends are
on $D$, remove $u$ from the cyclic list and keep the name $v$ for $w$."

The merged vertex `w` keeps the name `v` in both forms (Section 11 does the same when
`u ∉ D, v ∈ D`: it "keeps $w=v$"), so the contracted graph has vertex set `V(K) \ {u}`.

* `IsTrialEdge K D u v`: the edge `uv` has one of the two forms.
* `contractGraph K u v` and `contractCycle D u`: the contracted graph `H` and the new cycle.
* `markers K u v`: the original markers `M = N_K(u) \ {v}` of Section 9.
* `ContractRecord`: the record, which holds "the graph and the cycle before the contraction, and
  the edge $uv$" (Section 11).
* `liftOffOff`, `liftOneOn`, `liftBothOn`: the three lifts of Section 11, as functions on vertex
  lists.
-/

@[expose] public section

namespace GraphMinor.Crossing

open SimpleGraph

variable {V : Type*}

/-- **The trial edges** (Section 9): either "the vertex $u$ is not on $D$, and $v$ is arbitrary",
or "the vertices $u$ and $v$ are both on $D$, and they are consecutive on $D$." -/
def IsTrialEdge (K : SimpleGraph V) (D : List V) (u v : V) : Prop :=
  K.Adj u v ∧ (u ∉ D ∨ IsCycleEdge D u v)

/-- **The contraction of `uv`** (Section 9): "Contract $uv$ to a new vertex $w$, suppressing loops
and duplicate edges." The merged vertex keeps the name `v`, and `u` is deleted. -/
def contractGraph (K : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ a ≠ u ∧ b ≠ u ∧ (K.Adj a b ∨ (a = v ∧ K.Adj u b) ∨ (b = v ∧ K.Adj u a))
  symm := ⟨fun a b h => by
    obtain ⟨hab, ha, hb, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
    · exact ⟨Ne.symm hab, hb, ha, Or.inl h.symm⟩
    · exact ⟨Ne.symm hab, hb, ha, Or.inr (Or.inr ⟨h1, h2⟩)⟩
    · exact ⟨Ne.symm hab, hb, ha, Or.inr (Or.inl ⟨h1, h2⟩)⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

variable [DecidableEq V]

/-- **The cycle after the contraction** (Section 9): "If $u\notin V(D)$, the cycle is unchanged. If
both ends are on $D$, remove $u$ from the cyclic list and keep the name $v$ for $w$." -/
def contractCycle (D : List V) (u : V) : List V :=
  if u ∈ D then D.erase u else D

/-- **The original markers** (Section 9): `M = N_K(u) \ {v}`. "These are the *original markers*.
They stay fixed for the whole trial." -/
def markers (K : SimpleGraph V) (u v : V) : Set V :=
  {y | K.Adj u y ∧ y ≠ v}

/-- **The record of a contraction** (Section 11): "The record stores the graph and the cycle before
the contraction, and the edge $uv$." -/
structure ContractRecord (V : Type*) where
  /-- The graph before the contraction. -/
  graph : SimpleGraph V
  /-- Its vertex set. -/
  verts : Set V
  /-- The cycle before the contraction. -/
  cycle : List V
  /-- The deleted end `u` of the contracted edge. -/
  u : V
  /-- The end `v`, whose name the merged vertex keeps. -/
  v : V

namespace ContractRecord

/-- The graph after the contraction. -/
def newGraph (r : ContractRecord V) : SimpleGraph V :=
  contractGraph r.graph r.u r.v

/-- The vertex set after the contraction. -/
def newVerts (r : ContractRecord V) : Set V :=
  r.verts \ {r.u}

/-- The cycle after the contraction. -/
def newCycle (r : ContractRecord V) : List V :=
  contractCycle r.cycle r.u

/-- The contraction is a trial of Section 9: `uv` is a trial edge of the recorded graph and
cycle. -/
def IsValid (r : ContractRecord V) : Prop :=
  HP25.IsSupportedOn r.graph r.verts ∧ HP25.IsCycleList r.graph r.cycle ∧
    IsTrialEdge r.graph r.cycle r.u r.v

end ContractRecord

/-! ### The lifts of Section 11 -/

variable (K : SimpleGraph V) [DecidableRel K.Adj]

/-- **The lift when both ends are off the cycle** (Section 11): "If $w$ is unused, keep the
paths. Otherwise let $a$ and $b$ be the vertices before and after $w$ on its path." In the recorded
graph, choose `u_a ∈ {u, v}` adjacent to `a` and `u_b ∈ {u, v}` adjacent to `b`. "If $u_a=u_b$,
replace $w$ by that vertex. Otherwise replace it by $u_a,u_b$, using the edge $uv$." The choice
takes `v` when `v` is adjacent. -/
def liftOffOff (u v : V) (L : List V) : List V :=
  if v ∈ L then
    let i := L.idxOf v
    let a := L.getD (i - 1) v
    let b := L.getD (i + 1) v
    let ua := if K.Adj v a then v else u
    let ub := if K.Adj v b then v else u
    L.take i ++ (if ua = ub then [ua] else [ua, ub]) ++ L.drop (i + 1)
  else L

/-- The lift at the first vertex of a path, in the case `u ∉ D`, `v ∈ D`
(Section 11, "One end on the cycle"): "If its first edge comes from $v$ in the recorded graph, keep
the end $v$. If it comes from $u$, replace the beginning by $v,u$, followed by that edge." -/
def liftStartOneOn (u v : V) : List V → List V
  | x :: b :: rest => if x = v ∧ ¬ K.Adj v b then v :: u :: b :: rest else x :: b :: rest
  | L => L

/-- **The lift when one end is on the cycle** (Section 11): the case `u ∉ D`, `v ∈ D`, with
`w = v`. "If $w$ is used, it is an end of a crossing path." The start is lifted by
`liftStartOneOn`, and the end in the same way: "For a path that ends at $w$, reverse the order." -/
def liftOneOn (u v : V) (L : List V) : List V :=
  (liftStartOneOn K u v (liftStartOneOn K u v L).reverse).reverse

/-- The lift at the first vertex of a path, when both ends are on the cycle (Section 11): "Choose
whichever of $u,v$ is adjacent, in the recorded graph, to the next vertex of the path, and use it as
the end." -/
def liftStartBothOn (u v : V) : List V → List V
  | x :: b :: rest => if x = v ∧ ¬ K.Adj v b then u :: b :: rest else x :: b :: rest
  | L => L

/-- **The lift when both ends are on the cycle** (Section 11): the endpoint `w = v` is replaced by
whichever of `u`, `v` is adjacent to the next vertex, at the start and at the end. "*Do not
insert the cycle edge $uv$ into the path.*" -/
def liftBothOn (u v : V) (L : List V) : List V :=
  (liftStartBothOn K u v (liftStartBothOn K u v L).reverse).reverse

/-- The lift of a path through a contraction record, by the three cases of Section 11. -/
def ContractRecord.lift (r : ContractRecord V) [DecidableRel r.graph.Adj] (L : List V) :
    List V :=
  if r.u ∈ r.cycle then liftBothOn r.graph r.u r.v L
  else if r.v ∈ r.cycle then liftOneOn r.graph r.u r.v L
  else liftOffOff r.graph r.u r.v L

end GraphMinor.Crossing
