module

public import GraphMinor.GM05.SimpleSubgraphLift
public import GraphMinor.GM05.VertexWeb

/-!
# Webs and spiders with actual edge choices

A path records its vertex sequence and the actual edges along that sequence.
A web requires disjoint actual edges between the two path families. Spiders
also use actual edges, and their specified leaves have actual valency one.
-/

@[expose] public section
namespace GraphMinor.GM05.Full
open Graph SimpleGraph Set
variable {α β : Type*}

/-- A path of Graph Minors V, page 94, retaining the actual graph edges.
The shadow is its vertex sequence, with no loops or parallel edges in the
path itself. The host may still have loops and parallel edges. -/
structure Path (α β : Type*) where
  seq : GM01.Path α
  toGraph : Graph α β
  shadow_eq : simpleShadow toGraph = seq.toSubgraph
  no_loops : ∀ e x, ¬ toGraph.IsLink e x x
  no_parallel : ∀ e f x y, toGraph.IsLink e x y → toGraph.IsLink f x y → e = f

namespace Path
/-- The vertices of a path, V page 94. -/
def verts (P : Path α β) : Set α := P.seq.verts
/-- The actual edges of a path, V page 97. -/
def edgeSet (P : Path α β) : Set β := E(P.toGraph)
/-- A path belongs to a host when all its vertices and actual edges do. -/
def IsIn (P : Path α β) (G : Graph α β) : Prop := P.toGraph ≤ G

/-- The path graph and vertex sequence have the same vertices. -/
theorem vertexSet_eq (P : Path α β) : V(P.toGraph) = P.verts :=
  congrArg SimpleGraph.Subgraph.verts P.shadow_eq

/-- An actual path gives its vertex sequence as a path of the shadow. -/
theorem shadow_le {P : Path α β} {G : Graph α β} (h : P.IsIn G) :
    P.seq.toSubgraph ≤ simpleShadow G := by
  rw [← P.shadow_eq]
  exact simpleShadow_mono h
end Path

/-- An `(m,n)`-web, Graph Minors V, page 97, with actual edge-disjointness
between its two path families. -/
structure IsWeb (G : Graph α β) {m n : ℕ} (A : Fin m → Path α β) (B : Fin n → Path α β) : Prop where
  isIn_left : ∀ i, (A i).IsIn G
  isIn_right : ∀ j, (B j).IsIn G
  disjoint_left : Pairwise fun i j => Disjoint (A i).verts (A j).verts
  disjoint_right : Pairwise fun i j => Disjoint (B i).verts (B j).verts
  meets : ∀ i j, ((A i).verts ∩ (B j).verts).Nonempty
  edge_disjoint : ∀ i j, Disjoint (A i).edgeSet (B j).edgeSet

/-- A web retains the vertex conditions in the shadow, even when opposite
paths use distinct parallel edges between the same pair of vertices. -/
theorem IsWeb.vertexWeb {G : Graph α β} {m n : ℕ}
    {A : Fin m → Path α β} {B : Fin n → Path α β} (h : IsWeb G A B) :
    GM05.VertexWeb (simpleShadow G) (fun i => (A i).seq) (fun j => (B j).seq) :=
  ⟨fun i => Path.shadow_le (h.isIn_left i), fun j => Path.shadow_le (h.isIn_right j),
    h.disjoint_left, h.disjoint_right, h.meets⟩

/-- A spider of a web, Graph Minors V, page 98. Its edges are actual edges,
and every specified intersection vertex has valency one in the spider. -/
structure IsSpider (G : Graph α β) {m n : ℕ}
    (A : Fin m → Path α β) (B : Fin n → Path α β) (C : Graph α β) : Prop where
  le : C ≤ G
  connected : GraphConnected C
  edge_disjoint : ∀ j, Disjoint E(C) (B j).edgeSet
  unique_leaf : ∀ i, ∃ x, V(C) ∩ (A i).verts = {x} ∧ IsLeafOf C x

/-- Existence of a web with pairwise edge-disjoint spiders, V page 99. -/
def HasWebWithSpiders (G : Graph α β) (m n k : ℕ) : Prop :=
  ∃ (A : Fin m → Path α β) (B : Fin n → Path α β) (C : Fin k → Graph α β),
    IsWeb G A B ∧ (∀ i, IsSpider G A B (C i)) ∧ Pairwise (fun i j => Disjoint E(C i) E(C j))

/-- Existence of a web, V page 97. -/
def HasWeb (G : Graph α β) (m n : ℕ) : Prop :=
  ∃ (A : Fin m → Path α β) (B : Fin n → Path α β), IsWeb G A B

end GraphMinor.GM05.Full
