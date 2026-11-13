module

public import GraphMinor.Compute.GM13SocietyInput
public import GraphMinor.Compute.GM13SocietyPaths
public import GraphMinor.Compute.GM13SocietyPathEdges
public import GraphMinor.Compute.Algorithm99Transport
public import GraphMinor.Compute.Bridge13

/-!
# The society represented by plain multigraph input

We keep the vertex labels `Fin n` of the input throughout. The actual graph
has the multigraph's edge triples, rather than simple unordered edge pairs.
Removing loops and parallel copies preserves its crosses and its cores.
Lifting a path uses the same edge representatives as the endpoint-writing
program.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Surface GM09 GM13 SimpleGraph

/-- The given multigraph on its input vertex labels, with actual edge triples. -/
def GM13SocietyInput.graph (x : GM13SocietyInput) : Graph (Fin x.n) (ℕ × ℕ × ℕ) :=
  Transport.comapGraph ⟨Fin.val, Fin.val_injective⟩ (Function.Embedding.refl _)
    x.G.toGMDigraph.toGraph

/-- The society encoded by the input, allowing loops and parallel edges.
XIII, Section 2, page 68: "The underlying graph of a digraph is obtained by forgetting the directions of its edges." -/
noncomputable def GM13SocietyInput.society (x : GM13SocietyInput) :
    Society (Fin x.n) (ℕ × ℕ × ℕ) where
  G := x.graph
  Ω := x.simple.toSociety.Ω
  finite_V := Set.toFinite _
  finite_E := x.G.isFinite_toGMDigraph.finite_E.subset (by
    rintro e ⟨u, v, hl⟩
    exact hl.edge_mem)
  bar_subset := fun u _ => u.2

/-- The multigraph and its simple input have exactly the same vertices. -/
theorem GM13SocietyInput.vertexSet_graph (x : GM13SocietyInput) :
    V(x.graph) = Set.univ := by
  ext u
  exact iff_of_true u.2 (Set.mem_univ u)

/-- Distinct vertices are adjacent exactly when the simple input joins them. -/
theorem GM13SocietyInput.adj_graph (x : GM13SocietyInput) (u v : Fin x.n)
    (hne : u ≠ v) : x.graph.Adj u v ↔ x.G.toSimpleGraph.Adj u v := by
  constructor
  · rintro ⟨e, hl⟩
    exact WallOfHeight.adj_toSimpleGraph_of_isLink_toGMDigraph hl hne
  · intro ha
    exact ⟨adjEdgeTriple x.G u v, isLink_adjEdgeTriple ha⟩

private theorem gm13_simple_adj (x : GM13SocietyInput) (u v : Fin x.n) :
    x.simple.toSociety.G.Adj u v ↔ x.G.toSimpleGraph.Adj u v := by
  constructor
  · rintro ⟨e, he⟩
    rcases he with ⟨rfl, he⟩
    exact x.G.toSimpleGraph.mem_edgeSet.mp he
  · intro ha
    exact ⟨s(u, v), rfl, x.G.toSimpleGraph.mem_edgeSet.mpr ha⟩

/-- The simple and actual encoded societies have a cross in exactly the same
cases. The conclusion concerns the given society, with actual edges. -/
theorem GM13SocietyInput.hasCross_iff (x : GM13SocietyInput) :
    GM13.HasCross x.simple.toSociety ↔ GM13.HasCross x.society := by
  apply gm13_hasCross_iff
  · exact (Alg81Input.toSociety_G x.simple ▸ Graph.vertexSet_ofSimpleGraph _).trans
      x.vertexSet_graph.symm
  · rfl
  · intro u v hn
    exact (gm13_simple_adj x u v).trans (x.adj_graph u v hn).symm

/-- A core computed on the simple input is the same core of the given society. -/
theorem GM13SocietyInput.isCoreOf_iff (x : GM13SocietyInput)
    {δ : Type*} (C : Graph (Fin x.n) δ) :
    GM13.IsCoreOf x.simple.toSociety C ↔ GM13.IsCoreOf x.society C := by
  constructor
  · apply gm13_isCoreOf_transfer
    · exact (Graph.vertexSet_ofSimpleGraph _).trans x.vertexSet_graph.symm
    · rfl
    · intro u v hn
      exact (gm13_simple_adj x u v).trans (x.adj_graph u v hn).symm
  · apply gm13_isCoreOf_transfer
    · exact x.vertexSet_graph.trans (Graph.vertexSet_ofSimpleGraph _).symm
    · rfl
    · intro u v hn
      exact (x.adj_graph u v hn).trans (gm13_simple_adj x u v).symm

/-- The same 4-linked core works for the given multigraph society. -/
theorem GM13SocietyInput.isFourLinkedCore_iff (x : GM13SocietyInput)
    {δ : Type*} (C : Graph (Fin x.n) δ) :
    GM13.IsFourLinkedCore x.simple.toSociety C ↔ GM13.IsFourLinkedCore x.society C := by
  constructor
  · intro hc
    refine ⟨(x.isCoreOf_iff C).mp hc.isCore, ?_⟩
    exact hc.fourLinked
  · intro hc
    refine ⟨(x.isCoreOf_iff C).mpr hc.isCore, ?_⟩
    exact hc.fourLinked

/-- Replace every simple path edge by the actual edge numbered zero in an
available direction. The vertex labels are unchanged. -/
def gm13LiftWalk (x : GM13SocietyInput) {u v : Fin x.n} :
    x.G.toSimpleGraph.Walk u v → GraphWalk x.graph u v
  | .nil => .nil u.2
  | .cons ha rest => .cons (isLink_adjEdgeTriple ha) (gm13LiftWalk x rest)

/-- Restoring actual edges leaves the ordered vertex list unchanged. -/
theorem gm13LiftWalk_support (x : GM13SocietyInput) {u v : Fin x.n}
    (P : x.G.toSimpleGraph.Walk u v) : (gm13LiftWalk x P).support = P.support := by
  induction P with
  | nil => rfl
  | cons ha rest ih => exact congrArg (List.cons _) ih

private theorem gm13PathEdgeEnds_cons {n : ℕ} (G : MultiDigraph n)
    (u v : Fin n) (L : List (Fin n)) (head : Bool) :
    gm13PathEdgeEnds G (u :: v :: L) head =
      (if head then (adjEdgeTriple G u v).2.1 else (adjEdgeTriple G u v).1) ::
        gm13PathEdgeEnds G (v :: L) head := by
  apply List.ext_getElem
  · simp only [gm13PathEdgeEnds, List.length_ofFn, List.length_cons]
    omega
  · intro i hi hi'
    cases i with
    | zero => simp [gm13PathEdgeEnds]
    | succ i => simp [gm13PathEdgeEnds]

/-- The endpoint arrays written by the program are exactly the endpoints of
the actual edges in the restored walk, in their traversal order. -/
theorem gm13LiftWalk_edgeEnds (x : GM13SocietyInput) {u v : Fin x.n}
    (P : x.G.toSimpleGraph.Walk u v) (head : Bool) :
    (gm13LiftWalk x P).edges.map (fun e => if head then e.2.1 else e.1) =
      gm13PathEdgeEnds x.G P.support head := by
  induction P with
  | nil => simp [gm13LiftWalk, gm13PathEdgeEnds, GraphWalk.edges]
  | @cons u v w ha rest ih =>
    change (if head then (adjEdgeTriple x.G u v).2.1 else (adjEdgeTriple x.G u v).1) ::
      (gm13LiftWalk x rest).edges.map (fun e => if head then e.2.1 else e.1) =
        gm13PathEdgeEnds x.G (u :: rest.support) head
    rw [← rest.cons_tail_support, gm13PathEdgeEnds_cons]
    rw [rest.cons_tail_support, ih]

/-- Every chosen edge is numbered zero within its ordered parallel class. -/
theorem gm13LiftWalk_edgeIndex (x : GM13SocietyInput) {u v : Fin x.n}
    (P : x.G.toSimpleGraph.Walk u v) :
    ∀ e ∈ (gm13LiftWalk x P).edges, e.2.2 = 0 := by
  induction P with
  | nil => simp [gm13LiftWalk, GraphWalk.edges]
  | @cons u v w ha rest ih =>
    intro e he
    change e ∈ adjEdgeTriple x.G u v :: (gm13LiftWalk x rest).edges at he
    rcases List.mem_cons.mp he with rfl | he
    · simp only [adjEdgeTriple]
      split <;> rfl
    · exact ih e he

/-- The two restored path graphs form a cross in the given society. -/
theorem gm13LiftWalk_cross (x : GM13SocietyInput)
    (c : CrossWitness x.G.toSimpleGraph x.omega) (hc : c.IsValid) :
    x.society.IsCross (walkSubgraph (gm13LiftWalk x c.P))
      (walkSubgraph (gm13LiftWalk x c.Q)) := by
  obtain ⟨hp, hq, hd, ho⟩ := hc
  have ho' := (crossesInOmega_iff_crosses x.omega x.nodup_omega
    c.p₁ c.q₁ c.p₂ c.q₂).mp ho
  obtain ⟨ha, hb, hc, he, hab, hce⟩ := crosses_mem_and_ne ho'
  have hps : (gm13LiftWalk x c.P).IsSimple := by
    change (gm13LiftWalk x c.P).support.Nodup
    rw [gm13LiftWalk_support]
    exact hp.support_nodup
  have hqs : (gm13LiftWalk x c.Q).IsSimple := by
    change (gm13LiftWalk x c.Q).support.Nodup
    rw [gm13LiftWalk_support]
    exact hq.support_nodup
  refine ⟨?_, c.p₁, c.p₂, c.q₁, c.q₂,
    ⟨isGraphPathWithEnds_walkSubgraph hps, hab, ha, hb⟩,
    ⟨isGraphPathWithEnds_walkSubgraph hqs, hce, hc, he⟩, ho'⟩
  rw [vertexSet_walkSubgraph, vertexSet_walkSubgraph, Set.disjoint_left]
  intro v hv hv'
  rw [gm13LiftWalk_support] at hv hv'
  exact hd hv hv'

end GraphMinor.Compute
