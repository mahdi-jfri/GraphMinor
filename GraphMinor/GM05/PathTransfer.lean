module

public import GraphMinor.GM05.ShadowMinor

/-!
# Paths as vertex sequences in a graph with parallel edges

A path has no repeated vertices, so all its steps have distinct ends.
Requiring an edge for each step is therefore the same in a graph and its
simple shadow. The endpoints, internal vertices and avoidance conditions are
unchanged. These predicates concern vertex paths, without prescribing which
parallel edge is used.
-/

@[expose] public section
namespace GraphMinor.GM05.Full
open Graph GM01
variable {α β : Type*}

/-- A vertex path in the sense of Graph Minors V, page 94: all its vertices
belong to the graph, and each step has an edge in the graph. -/
def PathIsIn (P : Path α) (G : Graph α β) : Prop :=
  P.verts ⊆ V(G) ∧ ∀ ⦃x y⦄, P.toSubgraph.Adj x y → G.Adj x y

/-- A path has exactly the same possible vertex sequences in the shadow. -/
theorem pathIsIn_iff {P : Path α} {G : Graph α β} :
    PathIsIn P G ↔ P.IsIn (simpleShadow G) := by
  constructor
  · intro h
    exact ⟨h.1, fun _ _ hxy => ⟨P.toSubgraph.adj_sub hxy, h.2 hxy⟩⟩
  · intro h
    exact ⟨h.1, fun _ _ hxy => (h.2 hxy).2⟩

/-- A path from one vertex set to another, Graph Minors V, page 94. -/
def PathFromTo (P : Path α) (G : Graph α β) (A B : Set α) : Prop :=
  PathIsIn P G ∧ P.first ∈ A ∧ P.last ∈ B

/-- Taking the shadow does not change the endpoint conditions on a path. -/
theorem pathFromTo_iff {P : Path α} {G : Graph α β} {A B : Set α} :
    PathFromTo P G A B ↔ P.IsFromTo (simpleShadow G) A B := by
  change (PathIsIn P G ∧ _) ↔ (P.IsIn (simpleShadow G) ∧ _)
  rw [pathIsIn_iff]

/-- A vertex set separates two sets when it meets every path between them,
Graph Minors V, page 94. -/
def Separates (G : Graph α β) (X A B : Set α) : Prop :=
  ∀ P : Path α, PathFromTo P G A B → ¬ P.Avoids X

/-- Vertex separation by paths is unchanged in the shadow. -/
theorem separates_iff {G : Graph α β} {X A B : Set α} :
    Separates G X A B ↔ GM01.Separates (simpleShadow G) X A B := by
  unfold Separates GM01.Separates
  simp only [pathFromTo_iff]

end GraphMinor.GM05.Full
