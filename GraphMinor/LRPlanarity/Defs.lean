module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Relation

/-!
# Search forests and left-right constraints

The definitions follow `docs/planarity/planarity_test.tex`, Part I, Sections 1 and 2.
A forest stores only parents and depths. `IsDFS` states the parent and edge conditions
of a depth-first spanning forest. Returns and constraints are defined for this data,
so their use does not assume correctness of a search program.
-/

@[expose] public section

namespace GraphMinor.LRPlanarity

/-- Part I, Section 1: parents and depths of a search forest, with root depth zero. -/
structure Forest (N : ℕ) where
  parent : Fin N → Option (Fin N)
  depth : Fin N → ℕ

/-- Part I, Section 1: the ancestor relation includes the vertex itself. -/
def Forest.Ancestor {N : ℕ} (T : Forest N) (u v : Fin N) : Prop :=
  Relation.ReflTransGen (fun x y => T.parent y = some x) u v

/-- Part I, Section 1: a depth-first spanning forest has adjacent parent-child pairs,
root depth zero, depth increasing by one on parent edges, and comparable ends on every
edge. The latter is the absence of edges between different search branches. -/
def Forest.IsDFS {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N)) : Prop :=
  (∀ v, T.parent v = none → T.depth v = 0) ∧
  (∀ u v, T.parent v = some u → G.Adj u v ∧ T.depth v = T.depth u + 1) ∧
  (∀ u v, G.Adj u v → T.Ancestor u v ∨ T.Ancestor v u)

/-- An oriented edge record is given by its source and target. -/
abbrev Arc (N : ℕ) := Fin N × Fin N

/-- Part I, Section 1: tree edges point from parent to child. -/
def Forest.TreeEdge {N : ℕ} (T : Forest N) (e : Arc N) : Prop :=
  T.parent e.2 = some e.1

/-- Part I, Section 1: back edges point to strict ancestors and are not reverse
incidences of tree edges. -/
def Forest.BackEdge {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (b : Arc N) : Prop :=
  G.Adj b.1 b.2 ∧ T.Ancestor b.2 b.1 ∧ T.depth b.2 < T.depth b.1 ∧
    T.parent b.1 ≠ some b.2

/-- Part I, Section 1: outgoing tree or back edges at a vertex. -/
def Forest.Outgoing {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (v : Fin N) (e : Arc N) : Prop :=
  e.1 = v ∧ (T.TreeEdge e ∨ T.BackEdge G e)

/-- Part I, Section 1: "These are the *strict returns* of e."
A tree branch returns strictly above its source. A back edge returns itself. -/
def Forest.returns {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e : Arc N) : Set (Arc N) :=
  {b | T.BackEdge G b ∧
    ((T.BackEdge G e ∧ b = e) ∨
      (T.TreeEdge e ∧ T.Ancestor e.2 b.1 ∧ T.depth b.2 < T.depth e.1))}

/-- Part I, Section 1: the least return depth, with source depth as sentinel. -/
noncomputable def Forest.low {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e : Arc N) : ℕ := by
  classical
  let depths := (Finset.univ.filter (fun b => b ∈ T.returns G e)).image
    (fun b => T.depth b.2)
  exact (insert (T.depth e.1) depths).min' (by simp)

/-- Part I, Section 1: the thick bit records two different return depths. -/
noncomputable def Forest.thick {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e : Arc N) : Bool :=
  @decide (∃ b ∈ T.returns G e, ∃ c ∈ T.returns G e, T.depth b.2 ≠ T.depth c.2)
    (Classical.propDecidable _)

/-- Part I, Section 1: increasing lowpoint, with thin before thick at equal lowpoint. -/
noncomputable def Forest.key {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e : Arc N) : ℕ :=
  2 * T.low G e + (T.thick G e).toNat

/-- The two colors of Part I, Section 2. -/
inductive Color where
  | left | right
  deriving DecidableEq, Repr, Inhabited

/-- Colors are assigned to all pairs. Constraints use only back edges. -/
abbrev Coloring (N : ℕ) := Arc N → Color

/-- Part I, Section 2: empty and singleton sets are monochromatic. -/
def Monochromatic {α : Type*} (color : α → Color) (s : Set α) : Prop :=
  ∀ b ∈ s, ∀ c ∈ s, color b = color c

/-- Part I, Section 2: `I(e,f)` consists of returns of `e` above `low(f)`. -/
noncomputable def Forest.forkSet {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e f : Arc N) : Set (Arc N) :=
  {b | b ∈ T.returns G e ∧ T.low G f < T.depth b.2}

/-- Part I, Section 2: the two fork sets are monochromatic and have opposite colors
when both are nonempty. -/
def Forest.ForkConstraints {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (color : Coloring N) : Prop :=
  ∀ v e f, T.Outgoing G v e → T.Outgoing G v f → e ≠ f →
    Monochromatic color (T.forkSet G e f) ∧
    Monochromatic color (T.forkSet G f e) ∧
    (∀ b ∈ T.forkSet G e f, ∀ c ∈ T.forkSet G f e, color b ≠ color c)

/-- Part I, Section 2: weak returns include those to the source of the tree edge. -/
def Forest.weakReturns {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (p : Arc N) : Set (Arc N) :=
  {b | T.BackEdge G b ∧ T.Ancestor p.2 b.1 ∧ T.depth b.2 ≤ T.depth p.1}

/-- Part I, Section 2: "We call this *weak alignment*."
All minimum-depth members of each nonempty weak-return set have the same color. -/
def Forest.WeakAlignment {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (color : Coloring N) : Prop :=
  ∀ p, T.TreeEdge p → Monochromatic color
    {b | b ∈ T.weakReturns G p ∧ ∀ c ∈ T.weakReturns G p, T.depth b.2 ≤ T.depth c.2}

end GraphMinor.LRPlanarity
