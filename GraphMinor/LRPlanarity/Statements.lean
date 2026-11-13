module

public import GraphMinor.LRPlanarity.DefsSummary
public import GraphMinor.LRPlanarity.DefsGeometry
public import GraphMinor.Compute.Graph
public import GraphMinor.Surface.TopologyStatements

/-!
# Claims of the left-right planarity note

Every statement below is a proof obligation from `docs/planarity/planarity_test.tex`.
The search, solver, weak-alignment, sufficiency, and necessity statements are the
mathematical inputs to the assembly theorem. The remaining statements separate
lowpoint preprocessing, block semantics, fork order, contour construction, and
polygonalization. None of these claims is included as a field of search data,
a summary, a coloring, or an embedding.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Classical

/-- Part I, Section 1: the two smallest distinct values with upper sentinel `c`.
Values at or above the sentinel do not create another strict return. -/
def LowPairSpec (values : Finset ℕ) (c : ℕ) (pair : LowPair) : Prop :=
  pair.low ≤ c ∧ pair.second ≤ c ∧ pair.low ≤ pair.second ∧
  (∀ k ∈ values, pair.low ≤ k) ∧ (pair.low = c ∨ pair.low ∈ values) ∧
  (pair.second = c ∨ (pair.second ∈ values ∧ pair.low < pair.second)) ∧
  (∀ k ∈ values, pair.low < k → pair.second ≤ k)

/-- Part I, Section 1, `INSERT`: insert one value into a two-lowpoint pair. -/
def LowpointInsertionStatement : Prop :=
  ∀ values c pair k, LowPairSpec values c pair →
    LowPairSpec (insert k values) c (insertLow pair k)

/-- Part I, Section 1: explicit frames compute a depth-first forest and do not
exhaust the prescribed fuel on valid adjacency lists. -/
def SearchStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ),
    Compute.IsAdjListFamily G lists →
    ∃ search, depthFirstSearch (List.ofFn lists).toArray = some search ∧
      (search.forest N).IsDFS G

/-- Part I, Section 1: each undirected edge has exactly one oriented record.
The orientation is the parent-to-child or descendant-to-ancestor orientation. -/
def SearchRecordsStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ) (search : Search),
    Compute.IsAdjListFamily G lists →
    depthFirstSearch (List.ofFn lists).toArray = some search →
    (∀ i, i < search.edges.size → ∃ e : Arc N,
      search.edges[i]!.source = e.1.val ∧ search.edges[i]!.target = e.2.val ∧
      (((search.edges[i]!).tree = true ∧ (search.forest N).TreeEdge e) ∨
        ((search.edges[i]!).tree = false ∧ (search.forest N).BackEdge G e))) ∧
    (∀ u v, G.Adj u v → ∃! i : Fin search.edges.size,
      (search.edges[i.val]!.source = u.val ∧ search.edges[i.val]!.target = v.val) ∨
      (search.edges[i.val]!.source = v.val ∧ search.edges[i.val]!.target = u.val))

/-- Part I, Section 1: postorder lowpoint propagation computes strict returns,
the thick bit, and the key, without enumerating returns. -/
def LowpointsStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ) (search : Search),
    Compute.IsAdjListFamily G lists →
    depthFirstSearch (List.ofFn lists).toArray = some search →
    ∀ i, i < search.edges.size → ∃ e : Arc N,
      search.edges[i]!.source = e.1.val ∧ search.edges[i]!.target = e.2.val ∧
      let T := search.forest N
      let depths := (Finset.univ.filter (fun b => b ∈ T.returns G e)).image
        (fun b => T.depth b.2)
      LowPairSpec depths (T.depth e.1) search.edges[i]!.pair ∧
      search.edges[i]!.pair.low = T.low G e ∧
      search.edges[i]!.key = T.key G e

/-- Part I, Section 1: one global bucket pass gives all records of each source
exactly once and in nondecreasing key order. -/
def BucketOrderStatement : Prop :=
  ∀ n (edges : Array EdgeRecord),
    (∀ i, i < edges.size → edges[i]!.source < n ∧ edges[i]!.key ≤ 2 * n) →
    ∀ v, v < n →
      let outgoing := (bucketOrder n edges)[v]!
      outgoing.Nodup ∧
      (∀ i, i ∈ outgoing ↔ i < edges.size ∧ edges[i]!.source = v) ∧
      outgoing.Pairwise (fun i j => edges[i]!.key ≤ edges[j]!.key)

/-- Part I, Section 2: the primitive constraint for one pair of outgoing edges. -/
def ForkPair {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (color : Coloring N) (e f : Arc N) : Prop :=
  Monochromatic color (T.forkSet G e f) ∧
  Monochromatic color (T.forkSet G f e) ∧
  ∀ b ∈ T.forkSet G e f, ∀ c ∈ T.forkSet G f e, color b ≠ color c

/-- Part II, exact aggregation of new fork constraints: in key order, all new
primitive constraints reduce to two monochromatic classes with opposite colors.
Empty branches are skipped, as prescribed in Part I, Section 1. -/
def ForkAggregationStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N), T.IsDFS G →
    ∀ (color : Coloring N) v first rest new,
      let branches : List (Arc N) := first :: rest ++ [new]
      branches.Nodup →
      (∀ e ∈ branches, T.Outgoing G v e ∧ (T.returns G e).Nonempty) →
      branches.Pairwise (fun e f => T.key G e ≤ T.key G f) →
      let B := T.forkSet G new first
      let U : Set (Arc N) := {b | ∃ e ∈ first :: rest,
        b ∈ T.returns G e ∧ T.low G new < T.depth b.2}
      ((∀ e ∈ first :: rest, ForkPair T G color e new) ↔
        Monochromatic color B ∧ Monochromatic color U ∧
          ∀ b ∈ B, ∀ c ∈ U, color b ≠ color c) ∧
      (U.Nonempty → B.Nonempty)

/-- Part II, exact aggregation: the new branch must be monochromatic above
the first lowpoint, and old returns above the new lowpoint must be opposite.
This is a formula, not an assumption stored in a summary. -/
def MergeFormula (old new : Summary) (color : ℕ → Color) : Prop :=
  let B := nodeSet (new.nodes.filter (fun b => old.least < b.depth))
  let U := nodeSet (old.nodes.filter (fun b => new.least < b.depth))
  old.Holds color ∧ new.Holds color ∧ Monochromatic color B ∧
    Monochromatic color U ∧ (∀ i ∈ B, ∀ j ∈ U, color i ≠ color j) ∧
    (old.least = new.least → Monochromatic color (nodeSet (old.anchor ++ new.anchor)))

/-- Part II, child/old halves and list ordering: `MERGE` rejects exactly when
the aggregated formula is unsatisfiable, and otherwise represents it exactly.
The nonemptiness implication is the conclusion of the fork aggregation argument. -/
def MergeStatement : Prop :=
  ∀ (old new : Summary), old.Valid → new.Valid → old.least ≤ new.least →
    (old.nodes ++ new.nodes |>.map ReturnNode.edge).Nodup →
    ((∃ b ∈ old.nodes, new.least < b.depth) →
      ∃ b ∈ new.nodes, old.least < b.depth) →
    match merge (some old) (some new) with
    | none => ¬ ∃ color, MergeFormula old new color
    | some result =>
      (∀ color, SummaryFormula result color ↔ MergeFormula old new color) ∧
      (∀ s, result = some s → s.Valid) ∧
      nodeSet (summaryNodes result) = nodeSet (old.nodes ++ new.nodes)

/-- Part II, trim at the parent: deleting parent-depth nodes is exact existential
projection, and preserves the summary representation. -/
def TrimStatement : Prop :=
  ∀ (s : Summary) c, s.Valid → (∀ b ∈ s.nodes, b.depth ≤ c) →
    let result := trim (some s) c
    ProjectsTo s.Holds (nodeSet (s.nodes.filter (fun b => b.depth < c)))
      (SummaryFormula result) ∧
    nodeSet (summaryNodes result) = nodeSet (s.nodes.filter (fun b => b.depth < c)) ∧
    ∀ t, result = some t → t.Valid

/-- Part II, base and completion: the Boolean solver accepts exactly when a
coloring satisfies all fork constraints and all weak alignments. -/
def SolverStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ) (search : Search),
    Compute.IsAdjListFamily G lists →
    depthFirstSearch (List.ofFn lists).toArray = some search →
    (lrTest lists = true ↔ ∃ color,
      (search.forest N).ForkConstraints G color ∧
      (search.forest N).WeakAlignment G color)

/-- Part III: adding all weak alignments does not change satisfiability of the
fork constraints. This assertion concerns every depth-first forest. -/
def WeakAlignmentStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N), T.IsDFS G →
    ((∃ color, T.ForkConstraints G color) ↔
      ∃ color, T.ForkConstraints G color ∧ T.WeakAlignment G color)

/-- Part IV, Section 3, Lemma (A): when the first head is deeper, its color
specifies the source fork order. Membership in the two distinct return branches
expresses the local situation of the lemma. -/
def ForkOrderAStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N) (color : Coloring N),
    T.IsDFS G → T.ForkConstraints G color → T.WeakAlignment G color →
    ∀ v e f b c, T.Outgoing G v e → T.Outgoing G v f → e ≠ f →
      b ∈ T.returns G e → c ∈ T.returns G f → T.depth c.2 < T.depth b.2 →
      ((T.signedOutgoing G color v).idxOf e < (T.signedOutgoing G color v).idxOf f ↔
        color b = .left)

/-- Part IV, Section 3, Lemma (B): opposite colors at the same head put L first. -/
def ForkOrderBStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N) (color : Coloring N),
    T.IsDFS G → T.ForkConstraints G color → T.WeakAlignment G color →
    ∀ v e f b c, T.Outgoing G v e → T.Outgoing G v f → e ≠ f →
      b ∈ T.returns G e → c ∈ T.returns G f → b.2 = c.2 →
      color b = .left → color c = .right →
      (T.signedOutgoing G color v).idxOf e < (T.signedOutgoing G color v).idxOf f

/-- Part IV, Sections 2 to 4: the explicit signed contour is a valid contour
and no matched port pairs alternate. -/
def SignedContourStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N) (color : Coloring N),
    T.IsDFS G → T.ForkConstraints G color → T.WeakAlignment G color →
    let order := signedContourOrder T G color
    ValidContourOrder T G order ∧ IsPortWord T G (contourWord T order) ∧
      Nonalternating (contourWord T order)

/-- Part IV, Section 5: a nonalternating contour gives a geometric drawing.
The drawing is polygonal by the explicit upper tree and lower U-shaped paths. -/
def ContourDrawingStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N) (order : ContourOrder N),
    T.IsDFS G → ValidContourOrder T G order → IsPortWord T G (contourWord T order) →
    Nonalternating (contourWord T order) →
    ∃ drawing : HP25.PlaneEmbedding G Set.univ, IsPolygonal drawing

/-- Part IV, Sections 1 to 5: an aligned fork coloring gives a plane embedding. -/
def SufficiencyStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N) (color : Coloring N),
    T.IsDFS G → T.ForkConstraints G color → T.WeakAlignment G color →
    Nonempty (HP25.PlaneEmbedding G Set.univ)

/-- Part IV, opening fork comparison: a nonalternating tree contour yields
exactly the fork coloring defined by target-before-child comparisons. -/
def ContourForkStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N) (order : ContourOrder N),
    T.IsDFS G → ValidContourOrder T G order → IsPortWord T G (contourWord T order) →
    Nonalternating (contourWord T order) → T.ForkConstraints G (contourColor T order)

/-- Part IV, Section 7a: "Polygonalize a finite continuous plane drawing."
The vertex points can be kept fixed. -/
def PolygonalizationStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (drawing : HP25.PlaneEmbedding G Set.univ),
    ∃ polygonal : HP25.PlaneEmbedding G Set.univ,
      IsPolygonal polygonal ∧ polygonal.pt = drawing.pt

/-- Part IV, Section 7b: a thin neighborhood of one polygonal search tree is a
closed disc. Tree images lie in its interior. Cutting each cotree edge at its
two boundary ports leaves one exterior arc, meeting the disc only at those ports. -/
def TreeNeighborhoodStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N)
    (drawing : HP25.PlaneEmbedding G Set.univ), T.IsDFS G → IsPolygonal drawing →
    ∀ root, T.parent root = none →
    ∃ (disc : Set ℂ) (port : Port N → ℂ),
      Surface.IsClosedDisc disc ∧
      (∀ v, T.Ancestor root v → drawing.pt v ∈ interior disc) ∧
      (∀ e, T.TreeEdge e → T.Ancestor root e.1 →
        drawing.line e.1 e.2 ⊆ interior disc) ∧
      Set.InjOn port {p | T.BackEdge G p.edge ∧ T.Ancestor root p.edge.1} ∧
      (∀ b, T.BackEdge G b → T.Ancestor root b.1 →
        port ⟨b, true⟩ ∈ frontier disc ∧ port ⟨b, false⟩ ∈ frontier disc ∧
        Surface.IsLineWithEnds (drawing.line b.1 b.2 \ interior disc)
          (port ⟨b, true⟩) (port ⟨b, false⟩) ∧
        (drawing.line b.1 b.2 \ interior disc) ∩ disc =
          {port ⟨b, true⟩, port ⟨b, false⟩})

/-- Part IV, Section 7c: the four boundary arcs, four radial spokes, and two
alternating exterior arcs construct a plane K5. Euler's edge bound then excludes
the configuration. This statement records the construction before that contradiction. -/
def ExteriorK5Statement : Prop :=
  ∀ (disc A B : Set ℂ) (a c b d : ℂ), Surface.IsClosedDisc disc →
    Surface.PairsCrossOn (frontier disc) a c b d →
    Surface.IsLineWithEnds A a c → Surface.IsLineWithEnds B b d →
    A ∩ disc = {a, c} → B ∩ disc = {b, d} → Disjoint A B →
    Nonempty (HP25.PlaneEmbedding (⊤ : SimpleGraph (Fin 5)) Set.univ)

/-- Part IV, Sections 7b and 7c: cutting a polygonal drawing along any search
forest yields nonalternating contour orders, component by component. -/
def PolygonalContourStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N)
    (drawing : HP25.PlaneEmbedding G Set.univ), T.IsDFS G → IsPolygonal drawing →
    ∃ order, ValidContourOrder T G order ∧ IsPortWord T G (contourWord T order) ∧
      Nonalternating (contourWord T order)

/-- Part IV, Section 7: a geometric embedding gives a nonalternating contour
for any depth-first forest, independently of the algorithm's search order. -/
def GeometricContourStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N), T.IsDFS G →
    Nonempty (HP25.PlaneEmbedding G Set.univ) →
    ∃ order, ValidContourOrder T G order ∧ IsPortWord T G (contourWord T order) ∧
      Nonalternating (contourWord T order)

/-- Part IV, opening fork comparison and Section 7: every plane embedding gives
a fork coloring for every depth-first forest. Alignment is added by Part III. -/
def NecessityStatement : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (T : Forest N), T.IsDFS G →
    Nonempty (HP25.PlaneEmbedding G Set.univ) → ∃ color, T.ForkConstraints G color

end GraphMinor.LRPlanarity
