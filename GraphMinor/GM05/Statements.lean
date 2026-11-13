module

public import GraphMinor.GM05.ExpansionDefs
public import GraphMinor.GM05.ChordalDefs
public import GraphMinor.Planar.Defs

/-!
# The two directions of the Erdős–Pósa characterization

Graph Minors V states (8.2) before proving its two directions, (8.8) and
(8.14). These statements retain those result numbers so the dependency of
(8.2) on the later proofs is explicit.
-/

@[expose] public section

namespace GraphMinor.GM05

open Graph

universe u v u' v'

/-- Graph Minors V, (8.4), page 110:
"If $G$ is chordal and non-null then $G$ has a vertex $v$ such that the vertices adjacent to $v$ are pairwise adjacent." -/
def Theorem84Statement : Prop :=
  ∀ {V : Type u} [Finite V] [Nonempty V] (G : SimpleGraph V),
    IsChordal G → ∃ v, IsSimplicial G v

/-- Graph Minors V, (8.8), page 111:
"If $H$ is planar then $H$ has the Erdös-Pósa property." -/
def Theorem88Statement : Prop :=
  ∀ {α' : Type u'} {β' : Type v'} (H : Graph α' β'),
    IsPlanar H → HasErdosPosaProperty.{u,v,u',v'} H

/-- Graph Minors V, (8.14), page 113:
"$H$ does not have the Erdös–Pósa property."
Here `H` is the finite nonplanar graph fixed before (8.12). -/
def Theorem814Statement : Prop :=
  ∀ {α' : Type u'} {β' : Type v'} (H : Graph α' β'),
    V(H).Finite → E(H).Finite → ¬ IsPlanar H → ¬ HasErdosPosaProperty.{u,v,u',v'} H

end GraphMinor.GM05
