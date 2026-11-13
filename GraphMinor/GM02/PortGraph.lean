module

public import GraphMinor.GM02.Section4Split

/-!
# Split graphs that retain the identity of host edges

The split construction on II, page 319, forgets which original edge
connects two vertices. For the general patterns in (4.6), put one vertex
on each host edge and choose an incident edge for each terminal. Distinct
paths then cannot reuse a host edge. The two terminals of a pattern loop
must choose different incident edges after branch-vertex loops have been
removed by (4.2) and (4.3). This avoids the two counterexamples to (4.5)
given in the correction to (4.5) in `corrections/GM02.md`.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Original vertices, host-edge vertices, and the `2k` split terminals. -/
abbrev PortVertex (α : Type u) (β : Type v) (k : ℕ) := (α ⊕ β) ⊕ (Fin k × Bool)

/-- The copy of an original vertex in the split construction with edge vertices. -/
def portOld {α : Type u} {β : Type v} {k : ℕ} (a : α) : PortVertex α β k := Sum.inl (Sum.inl a)

/-- The vertex recording one particular original edge. -/
def portEdge {α : Type u} {β : Type v} {k : ℕ} (e : β) : PortVertex α β k := Sum.inl (Sum.inr e)

/-- The split terminal for one end of a pattern edge. -/
def portTerminal {α : Type u} {β : Type v} {k : ℕ} (p : Fin k × Bool) : PortVertex α β k := Sum.inr p

/-- One chosen incident host edge per terminal. The two ends of a pattern
loop choose distinct edges, since host loops at branch vertices have already
been removed in the first step of (4.6). This stores only choices and their
incidence conditions, not any path or containment conclusion. -/
structure PortChoice {α : Type u} {β : Type v} {k : ℕ}
    (G : Graph α β) (ends : Fin k → α × α) where
  /-- The particular host edge chosen for each split terminal. -/
  edge : Fin k × Bool → E(G)
  /-- That edge is incident with the prescribed pattern endpoint. -/
  incident : ∀ p, G.Inc (edge p).val (if p.2 then (ends p.1).2 else (ends p.1).1)
  /-- A pattern loop cannot use the same host edge at its two ends. -/
  loop_ne : ∀ i, (ends i).1 = (ends i).2 → edge (i, false) ≠ edge (i, true)

/-- Original non-branch vertices and selected edge incidences form a bipartite graph. -/
def portAdj {α : Type u} {β : Type v} {k : ℕ} (G : Graph α β)
    (pick : Fin k × Bool → β) : PortVertex α β k → PortVertex α β k → Prop
  | Sum.inl (Sum.inl a), Sum.inl (Sum.inr e) => G.Inc e a
  | Sum.inl (Sum.inr e), Sum.inl (Sum.inl a) => G.Inc e a
  | Sum.inr p, Sum.inl (Sum.inr e) => pick p = e
  | Sum.inl (Sum.inr e), Sum.inr p => pick p = e
  | _, _ => False

/-- The simple adjacency graph retains an internal vertex for each particular host edge. -/
def portSimpleGraph {α : Type u} {β : Type v} {k : ℕ} (G : Graph α β)
    (pick : Fin k × Bool → β) : SimpleGraph (PortVertex α β k) where
  Adj := portAdj G pick
  symm := ⟨by
    intro a b h
    rcases a with (a | e) | p <;> rcases b with (b | f) | q <;> exact h⟩
  loopless := ⟨by
    intro a h
    rcases a with (a | e) | p <;> exact h⟩

/-- Delete the pattern's original vertices and retain every edge vertex and terminal. -/
def portVertexSet {α : Type u} {β : Type v} (G H : Graph α β) (k : ℕ) : Set (PortVertex α β k) :=
  portOld '' (V(G) \ V(H)) ∪ (portEdge '' E(G) ∪ range portTerminal)

/-- The terminated graph used to correct the split test for general patterns in (4.6). -/
def portGraph {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) :
    Graph (PortVertex α β k) (Sym2 (PortVertex α β k)) :=
  (Graph.ofSimpleGraph (portSimpleGraph G (fun p => (choice.edge p).val))).induce (portVertexSet G H k)

/-- The graph has exactly the explicitly retained old, edge, and terminal vertices. -/
theorem portGraph_vertexSet {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) :
    V(portGraph G H choice) = portVertexSet G H k := rfl

/-- Its adjacency is the chosen incidence relation restricted to the retained vertices. -/
theorem portGraph_adj_iff {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (a b : PortVertex α β k) :
    (portGraph G H choice).Adj a b ↔ a ∈ portVertexSet G H k ∧ b ∈ portVertexSet G H k ∧
      portAdj G (fun p => (choice.edge p).val) a b := by
  constructor
  · rintro ⟨e, he⟩
    rw [portGraph, Graph.induce_isLink] at he
    exact ⟨he.2.1, he.2.2, (Graph.ofSimpleGraph_adj_iff a b).1 ⟨e, he.1⟩⟩
  · rintro ⟨ha, hb, hab⟩
    refine ⟨s(a, b), ?_⟩
    rw [portGraph, Graph.induce_isLink]
    exact ⟨⟨rfl, (SimpleGraph.mem_edgeSet _).2 hab⟩, ha, hb⟩

/-- The split vertex set is finite whenever the original graph is finite. -/
theorem portVertexSet_finite {α : Type u} {β : Type v} (G H : Graph α β) (k : ℕ)
    (hV : V(G).Finite) (hE : E(G).Finite) : (portVertexSet G H k).Finite :=
  (hV.sdiff.image portOld).union ((hE.image portEdge).union (Set.finite_range portTerminal))

/-- Each terminal is joined to precisely its chosen edge vertex. -/
theorem portTerminal_adj_portEdge_iff {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (p : Fin k × Bool) (e : β) :
    (portGraph G H choice).Adj (portTerminal p) (portEdge e) ↔ (choice.edge p).val = e := by
  rw [portGraph_adj_iff]
  constructor
  · exact fun h => h.2.2
  · intro he
    refine ⟨Or.inr (Or.inr ⟨p, rfl⟩), Or.inr (Or.inl ⟨e, ?_, rfl⟩), he⟩
    exact he ▸ (choice.edge p).property

/-- A terminal has no neighbor other than the vertex of its chosen original edge. -/
theorem portTerminal_adj_iff {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (p : Fin k × Bool) (a : PortVertex α β k) :
    (portGraph G H choice).Adj (portTerminal p) a ↔ a = portEdge (choice.edge p).val := by
  rcases a with (a | e) | q
  · simp [portGraph_adj_iff, portAdj, portTerminal, portEdge]
  · change (portGraph G H choice).Adj (portTerminal p) (portEdge e) ↔ _
    rw [portTerminal_adj_portEdge_iff]
    simp only [portEdge, Sum.inl.injEq, Sum.inr.injEq, eq_comm]
  · simp [portGraph_adj_iff, portAdj, portTerminal, portEdge]

/-- Both vertex and edge sets of the new graph are finite for finite input graphs. -/
theorem portGraph_finite {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    V(portGraph G H choice).Finite ∧ E(portGraph G H choice).Finite := by
  have hX : V(portGraph G H choice).Finite := portVertexSet_finite G H k hV hE
  refine ⟨hX, (hX.image2 Sym2.mk hX).subset ?_⟩
  intro e he
  obtain ⟨a, b, hab⟩ := (portGraph G H choice).exists_isLink_of_mem_edgeSet he
  have heq : e = s(a, b) := hab.1.1
  exact ⟨a, hab.left_mem, b, hab.right_mem, heq.symm⟩

end GraphMinor.GM02
