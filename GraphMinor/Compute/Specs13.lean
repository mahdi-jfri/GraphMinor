module

public import GraphMinor.Compute.Wall
public import GraphMinor.Compute.FolioReductionMath
public import GraphMinor.Compute.Bridge3
public import GraphMinor.GM13.Section7WallWalks

/-!
# The statements of the programs of Graph Minors XIII that other programs call

Graph Minors XIII, Robertson and Seymour, J. Combin. Theory Ser. B **63** (1995), 65–110.
This file fixes, for (7.2), (7.4) and (7.7), the input written in `inArr`, the output written in
`outArr`, and the running time. The file that implements a program proves the statement given
here, and a program that calls it assumes exactly this statement.

Walls are `WallOfHeight` (`Wall.lean`), written as `W.encList`. Graphs are `MultiDigraph`, written
as `G.enc`. The distance in a wall is `WallOfHeight.brickDist`, which equals `GM13`'s distance of
the drawing of Fig. 1 (`WallOfHeight.planeWallDist_eq_brickDist`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 2: Fig. 1 Cell Drawing and Brick Distance (`GM13.Section7*`) -/

/-- The Fig. 1 cell `(2x, 2y)` of the `u`-th branch vertex `(x, y)` of the elementary wall of
height `h` (`GM13.Section7Cells`, page 89). -/
def elemWallVertCell (h : ℕ) (u : Fin (elemWallNumVerts h)) : ℤ × ℤ :=
  let p := (elemWallCoords h)[u.1]'u.2
  (2 * (p.1 : ℤ), 2 * (p.2 : ℤ))

/-- The Fig. 1 open-segment cell of the `k`-th edge `(p₁, p₂)` of the elementary wall of height `h`:
`(2x₁ + 1, 2y₁)` for a horizontal edge `y₁ = y₂`, and `(2x₁, 2y₁ + 1)` for a vertical edge
(`GM13.Section7Cells`, `horizontalCells` and `verticalCells`). -/
def elemWallEdgeCell (h : ℕ) (k : Fin (elemWallEdges h).length) : ℤ × ℤ :=
  let e := (elemWallEdges h)[k.1]'k.2
  let p₁ := (elemWallCoords h)[e.1.1]'e.1.2
  let p₂ := (elemWallCoords h)[e.2.1]'e.2.2
  if p₁.2 = p₂.2 then
    (2 * (p₁.1 : ℤ) + 1, 2 * (p₁.2 : ℤ))
  else
    (2 * (p₁.1 : ℤ), 2 * (p₁.2 : ℤ) + 1)

namespace WallOfHeight

/-- The cell in the Fig. 1 drawing of `W : WallOfHeight h G` containing a vertex `v : Fin n`:
- if `v = W.branchVert u`, the vertex cell `elemWallVertCell h u = (2x, 2y)`;
- if `v ∈ W.internalVerts k`, the open-segment cell `elemWallEdgeCell h k`;
- otherwise `(0, 0)`. -/
def vertCell {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) (v : Fin n) : ℤ × ℤ :=
  match (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
  | some u => elemWallVertCell h u
  | none =>
    match (List.finRange (elemWallEdges h).length).find?
        (fun k => decide (v ∈ W.internalVerts k)) with
    | some k => elemWallEdgeCell h k
    | none => (0, 0)

end WallOfHeight

/-- The brick count distance `[c₁] + [c₂] + min_{q₁, q₂} faceDist(F(q₁), F(q₂))` between two cells
`c₁, c₂ : ℤ × ℤ` in the Fig. 1 drawing of the wall of height `h` (`GM13.Section7WallCells` and
`GM13.Section7WallWalks`). -/
noncomputable def fig1CellBrickDist (h : ℕ) (c₁ c₂ : ℤ × ℤ) : ℕ :=
  GM13.cellInd (GM13.fig1WallCells h) c₁ +
  GM13.cellInd (GM13.fig1WallCells h) c₂ +
  sInf ((fun qq' : (ℤ × ℤ) × (ℤ × ℤ) =>
    (GM13.faceDist h (GM13.wallFace h qq'.1) (GM13.wallFace h qq'.2)).toNat) ''
    (GM13.squaresAbove c₁ ×ˢ GM13.squaresAbove c₂))

/-- **Equivalence with `GM13`'s plane distance (`planeWallDist`) on Fig. 1:**
For any two points `s, t : ℝ × ℝ` in distinct cells (`cellCode s ≠ cellCode t`) of the Fig. 1
wall of even height `h ≥ 1`, `fig1CellBrickDist h (cellCode s) (cellCode t)` is equal to
`GM13.planeWallDist (GM13.fig1WallSet h) (GM13.fig1PlaneEquiv s) (GM13.fig1PlaneEquiv t)`. -/
theorem planeWallDist_fig1_eq_fig1CellBrickDist {h : ℕ} (hh : 1 ≤ h) (he : Even h)
    {s t : ℝ × ℝ} (hst : GM13.cellCode s ≠ GM13.cellCode t) :
    GM13.planeWallDist (GM13.fig1WallSet h) (GM13.fig1PlaneEquiv s) (GM13.fig1PlaneEquiv t) =
      fig1CellBrickDist h (GM13.cellCode s) (GM13.cellCode t) := by
  rw [GM13.fig1WallSet_eq_cellSet]
  unfold fig1CellBrickDist
  set S : Set ℕ :=
    (fun qq' : (ℤ × ℤ) × (ℤ × ℤ) =>
      (GM13.faceDist h (GM13.wallFace h qq'.1) (GM13.wallFace h qq'.2)).toNat) ''
      (GM13.squaresAbove (GM13.cellCode s) ×ˢ GM13.squaresAbove (GM13.cellCode t))
  have hS_ne : S.Nonempty :=
    ((GM13.squaresAbove_nonempty (GM13.cellCode s)).prod
      (GM13.squaresAbove_nonempty (GM13.cellCode t))).image _
  apply le_antisymm
  · have hmem : sInf S ∈ S := Nat.sInf_mem hS_ne
    rcases hmem with ⟨⟨q, q'⟩, ⟨hq, hq'⟩, h_sInf⟩
    have hq1 : q ∈ GM13.squaresAbove (GM13.cellCode s) := hq
    have hq2 : q' ∈ GM13.squaresAbove (GM13.cellCode t) := hq'
    have h_sInf' :
        (GM13.faceDist h (GM13.wallFace h q) (GM13.wallFace h q')).toNat = sInf S := h_sInf
    have hle := GM13.planeWallDist_fig1_le hh he hst hq1 hq2
    omega
  · obtain ⟨q, hq, q', hq', hge⟩ := GM13.le_planeWallDist_fig1 hh he hst
    have h_sInf_le :
        sInf S ≤ (GM13.faceDist h (GM13.wallFace h q) (GM13.wallFace h q')).toNat :=
      Nat.sInf_le ⟨(q, q'), ⟨hq, hq'⟩, rfl⟩
    omega

namespace WallOfHeight

/-- Brick distance `d(u, v)` between two vertices `u, v` of `W : WallOfHeight h G` in the Fig. 1
drawing (`0` if `u = v`, and `fig1CellBrickDist h (W.vertCell u) (W.vertCell v)` if `u ≠ v`). -/
noncomputable def brickDist {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (u v : Fin n) : ℕ :=
  if u = v then 0 else fig1CellBrickDist h (W.vertCell u) (W.vertCell v)

/-- For any vertices `u ≠ v` of `W : WallOfHeight h G` drawn at points `s, t : ℝ × ℝ` in distinct
cells `GM13.cellCode s = W.vertCell u` and `GM13.cellCode t = W.vertCell v`, `W.brickDist u v`
equals `GM13.planeWallDist (GM13.fig1WallSet h) (GM13.fig1PlaneEquiv s) (GM13.fig1PlaneEquiv t)`. -/
theorem planeWallDist_eq_brickDist {h n : ℕ} (hh : 1 ≤ h) (he : Even h)
    {G : MultiDigraph n} (W : WallOfHeight h G) {u v : Fin n} (huv : u ≠ v)
    {s t : ℝ × ℝ} (hs : GM13.cellCode s = W.vertCell u) (ht : GM13.cellCode t = W.vertCell v)
    (hc : W.vertCell u ≠ W.vertCell v) :
    GM13.planeWallDist (GM13.fig1WallSet h) (GM13.fig1PlaneEquiv s) (GM13.fig1PlaneEquiv t) =
      W.brickDist u v := by
  have hst : GM13.cellCode s ≠ GM13.cellCode t := by rw [hs, ht]; exact hc
  rw [planeWallDist_fig1_eq_fig1CellBrickDist hh he hst, hs, ht]
  simp [brickDist, huv]

/-! ### Section 3: `H`-Paths in `G` and Input Specification for (7.4) -/

/-- Two vertices `u, v : Fin n` are joined by an edge of the wall `W : WallOfHeight h G` if `{u, v}`
occurs as a consecutive pair along `W.subdivPathVerts k` for some edge `k` of the elementary wall. -/
def IsWallEdge {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) (u v : Fin n) : Prop :=
  ∃ k : Fin (elemWallEdges h).length,
    (u, v) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) ∨
    (v, u) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1)

/-- An `$H$-path in $G$` for a wall `W : WallOfHeight h G` (GM XIII Section 7, page 90):
"Let $H$ be a subgraph of $G$. An *$H$-path in* $G$ is a path with distinct ends, both in $V(H)$,
and with no edge or internal vertex in $H$." -/
def IsHPath {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) (P : List (Fin n)) : Prop :=
  ∃ hne : P ≠ [],
    2 ≤ P.length ∧
    P.Nodup ∧
    IsSimpleWalkList G P ∧
    P.head hne ∈ W.vertexFinset ∧
    P.getLast hne ∈ W.vertexFinset ∧
    (∀ v ∈ (P.drop 1).dropLast, v ∉ W.vertexFinset) ∧
    (P.length = 2 → ¬ W.IsWallEdge (P.head hne) (P.getLast hne))

/-- The end vertex of the `i`-th path `paths i` selected by `b : Bool`
(`false` for the start vertex `head`, `true` for the end vertex `getLast`). -/
def hPathEnd {n k : ℕ} (paths : Fin k → List (Fin n)) (eb : Fin k × Bool) : Option (Fin n) :=
  match paths eb.1 with
  | [] => none
  | u :: rest => some (if eb.2 then (u :: rest).getLast (List.cons_ne_nil u rest) else u)

end WallOfHeight

/-- Validated input instance to the algorithm of GM XIII (7.4) (page 90), parameterized
by clique size `p` and end-distance threshold `r`:
- `n : ℕ`: number of vertices `|V(G)|`,
- `h : ℕ`: height of the wall `W`,
- `G : MultiDigraph n`: input graph in the multigraph format,
- `W : WallOfHeight h G`: a valid wall of even height `h ≥ 2` in `G`,
- `paths : Fin (p.choose 2) → List (Fin n)`: $\binom{p}{2}$ mutually vertex-disjoint $H$-paths in
  $G$ whose $p(p - 1)$ ends are mutually at brick distance $\ge r$ in $W$. -/
structure Alg74Input (p r : ℕ) where
  /-- Number of vertices `|V(G)|`. -/
  n : ℕ
  /-- Height `h` of the wall `W`. -/
  h : ℕ
  /-- The input graph `G` on `Fin n`. -/
  G : MultiDigraph n
  /-- The wall `H` of height `h` in `G`. -/
  W : WallOfHeight h G
  /-- The $\binom{p}{2}$ $H$-paths $P_1, \dots, P_{\binom{p}{2}}$ in `G`. -/
  paths : Fin (p.choose 2) → List (Fin n)
  /-- `h ≥ 2` is even and `W` is a valid wall in `G`. -/
  hW_valid : 2 ≤ h ∧ Even h ∧ W.IsValid
  /-- Each `paths i` is an $H$-path in `G`. -/
  hpaths_valid : ∀ i : Fin (p.choose 2), W.IsHPath (paths i)
  /-- The paths $P_1, \dots, P_{\binom{p}{2}}$ are mutually vertex-disjoint. -/
  hpaths_disj : ∀ i j : Fin (p.choose 2), i ≠ j → List.Disjoint (paths i) (paths j)
  /-- The $p(p - 1)$ ends of $P_1, \dots, P_{\binom{p}{2}}$ are mutually at brick distance $\ge r$
  in `W`. -/
  hends_dist : ∀ e₁ e₂ : Fin (p.choose 2) × Bool, e₁ ≠ e₂ →
    ∀ u v : Fin n,
      WallOfHeight.hPathEnd paths e₁ = some u →
      WallOfHeight.hPathEnd paths e₂ = some v →
      r ≤ W.brickDist u v

/-- Problem size `ε(G) = |E(G)| + |V(G)| + 1` for GM XIII (7.4) (page 66 and page 90). -/
def alg74Size {p r : ℕ} (x : Alg74Input p r) : ℕ :=
  x.G.numEdges + x.n + 1

/-- Flat `List ℕ` encoding of `k` paths `paths : Fin k → List (Fin n)`:
for each `i : Fin k`, `[(paths i).length] ++ (paths i).map Fin.val`. -/
def encHPaths {n k : ℕ} (paths : Fin k → List (Fin n)) : List ℕ :=
  (List.finRange k).flatMap (fun i => (paths i).length :: (paths i).map Fin.val)

/-- Flat Word RAM input encoding of `x : Alg74Input p r` in `inArr`:
`x.G.enc ++ x.W.encList ++ encHPaths x.paths`. -/
def encAlg74In {p r : ℕ} (x : Alg74Input p r) : List ℕ :=
  x.G.enc ++ x.W.encList ++ encHPaths x.paths

/-! ### Section 4: Model of $K_p$ on the Underlying Graph (`FolioTable.lean`) and Statement -/

/-- Canonical list of the $\binom{p}{2}$ undirected edges `(u, v)` (`u < v`) of the complete graph
$K_p$ on `Fin p`. -/
def completeGraphEdges (p : ℕ) : List (Fin p × Fin p) :=
  (allDirectedPairs p).filter (fun e => decide (e.1 < e.2))

/-- The complete graph $K_p$ on `Fin p` viewed as a `ComputeDigraph` (`FolioTable.lean`) with `p`
vertices and `(completeGraphEdges p).length` edges. -/
def completeComputeDigraph (p : ℕ) : ComputeDigraph where
  numVerts := p
  numEdges := (completeGraphEdges p).length
  tail := fun e => ((completeGraphEdges p)[e.1]'e.2).1
  head := fun e => ((completeGraphEdges p)[e.1]'e.2).2

/-- A model `φ` of a graph `H` in the underlying graph of a digraph `G : ComputeDigraph`, in the
sense of the model definition in `FolioTable.lean` (`DigraphModel`, GM XIII Section 2, page 68):
"Let $G, H$ be both graphs or both digraphs. A *model* $\phi$ of $H$ in $G$ assigns to each edge
$e$ of $H$ an edge $\phi(e)$ of $G$, and to each vertex $v$ of $H$ a non-null connected subgraph
$\phi(v)$ of $G$, such that
(i) the graphs $\phi(v)$ ($v \in V(H)$) are mutually vertex-disjoint, the edges $\phi(e)$
($e \in E(H)$) are all distinct, and for $v \in V(H)$ and $e \in E(H)$, $\phi(e) \notin E(\phi(v))$
(ii) for $e \in E(H)$, if $e$ has head $u$ and tail $v$ (or, in the undirected case, has ends
$u, v$) then $\phi(e)$ has a head in $V(\phi(u))$ and a tail in $V(\phi(v))$ (respectively,
$\phi(e)$ has one end in $V(\phi(u))$ and the other in $V(\phi(v))$)." -/
structure UnderlyingGraphModel (H G : ComputeDigraph) where
  /-- For each vertex `v ∈ V(H)`, a subgraph `φ(v)` of `G`. -/
  vertMap : Fin H.numVerts → DigraphSubgraph G
  /-- For each edge `e ∈ E(H)`, an edge `φ(e)` of `G`. -/
  edgeMap : Fin H.numEdges → Fin G.numEdges
  /-- Each `φ(v)` is a non-null connected subgraph of `G` (on the underlying graph). -/
  connected : ∀ v : Fin H.numVerts, (vertMap v).IsNonNullConnected
  /-- Condition (i), part 1: the graphs `φ(v)` (`v ∈ V(H)`) are mutually vertex-disjoint. -/
  vert_disjoint : ∀ u v : Fin H.numVerts, u ≠ v → Disjoint (vertMap u).verts (vertMap v).verts
  /-- Condition (i), part 2: the edges `φ(e)` (`e ∈ E(H)`) are all distinct. -/
  edge_injective : Function.Injective edgeMap
  /-- Condition (i), part 3: for `v ∈ V(H)` and `e ∈ E(H)`, `φ(e) ∉ E(φ(v))`. -/
  edge_notMem_vert : ∀ (v : Fin H.numVerts) (e : Fin H.numEdges), edgeMap e ∉ (vertMap v).edges
  /-- Condition (ii) in the undirected case: for `e ∈ E(H)` with ends `H.tail e` and `H.head e`,
  `φ(e)` has one end in `V(φ(H.tail e))` and the other in `V(φ(H.head e))`. -/
  ends_mem_vertMap : ∀ e : Fin H.numEdges,
    (G.tail (edgeMap e) ∈ (vertMap (H.tail e)).verts ∧
      G.head (edgeMap e) ∈ (vertMap (H.head e)).verts) ∨
    (G.head (edgeMap e) ∈ (vertMap (H.tail e)).verts ∧
      G.tail (edgeMap e) ∈ (vertMap (H.head e)).verts)

/-- Every directed `DigraphModel H G` (`FolioTable.lean`) is an `UnderlyingGraphModel H G`. -/
def DigraphModel.toUnderlyingGraphModel {H G : ComputeDigraph} (M : DigraphModel H G) :
    UnderlyingGraphModel H G where
  vertMap := M.vertMap
  edgeMap := M.edgeMap
  connected := M.connected
  vert_disjoint := M.vert_disjoint
  edge_injective := M.edge_injective
  edge_notMem_vert := M.edge_notMem_vert
  ends_mem_vertMap e := Or.inl ⟨M.tail_mem_vertMap e, M.head_mem_vertMap e⟩

/-- Flat `List ℕ` encoding of an `UnderlyingGraphModel H G`:
`[H.numVerts, H.numEdges]` followed by the mapped edge endpoints `(tail, head)` for each
`e : Fin H.numEdges` and, for each vertex `u : Fin H.numVerts`, the indicator bitlist
`bitSetList (M.vertMap u).verts` of length `G.numVerts`. -/
def encUnderlyingGraphModel {H G : ComputeDigraph} (M : UnderlyingGraphModel H G) : List ℕ :=
  [H.numVerts, H.numEdges] ++
  (List.finRange H.numEdges).flatMap (fun e =>
    [(G.tail (M.edgeMap e)).1, (G.head (M.edgeMap e)).1]) ++
  (List.finRange H.numVerts).flatMap (fun u =>
    bitSetList (M.vertMap u).verts)

/-- Output specification for GM XIII (7.4) on input `x : Alg74Input p r`:
`out` is the flat encoding `encUnderlyingGraphModel M` of a valid model `M` of $K_p$
(`completeComputeDigraph p`) in `x.G.toComputeDigraph`. -/
def IsAlg74Output (p r : ℕ) (x : Alg74Input p r) (out : List ℕ) : Prop :=
  ∃ M : UnderlyingGraphModel (completeComputeDigraph p) x.G.toComputeDigraph,
    out = encUnderlyingGraphModel M

/-- **Statement of the Algorithm of Graph Minors XIII, (7.4) (page 90)** on the Word RAM:
For every integer `p ≥ 2`, there exists `r ≥ 0` and a Word RAM program `P` with running time
`≤ C * ε(G)` (where `C` depends only on `p`) that, given `G`, a wall `W` in `G` of any even height
`h ≥ 2`, and $\binom{p}{2}$ mutually vertex-disjoint $H$-paths in `G` whose $p(p - 1)$ ends are
mutually at distance `≥ r` in `W`, outputs a model of $K_p$ in `G`. -/
def Algorithm74Statement : Prop :=
  ∀ p : ℕ, 2 ≤ p →
    ∃ r : ℕ, ∃ P : Cmd,
      ComputesArrRelInTime (alg74Size (p := p) (r := r))
        (encAlg74In (p := p) (r := r))
        (IsAlg74Output p r) P (fun m => m)


/-! ### Section 5: (7.7), models of `K_p` from stars -/

namespace WallOfHeight

/-- `P` is one path of an `(l, m)`-star over the wall `W` with center `c` (GM XIII, Section 7,
page 91, conditions (i) and (ii)): "$P_1, \dots, P_l$ are paths of $G$ and all have one end $v$"
and "let the ends of $P_i$ be $v, u_i$; then $u_i \ne v$, and $u_i \in V(H)$, and no edge or
internal vertex of $P_i$ is in $H$". The path is the list of its vertices from `c` to its other
end. -/
def IsStarRay {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) (c : Fin n)
    (P : List (Fin n)) : Prop :=
  ∃ hne : P ≠ [],
    P.head hne = c ∧
    2 ≤ P.length ∧
    P.Nodup ∧
    IsSimpleWalkList G P ∧
    P.getLast hne ∈ W.vertexFinset ∧
    (∀ v ∈ (P.drop 1).dropLast, v ∉ W.vertexFinset) ∧
    (∀ u v, (u, v) ∈ P.zip (P.drop 1) → ¬ W.IsWallEdge u v)

end WallOfHeight

/-- An input of the algorithm of (7.7) (GM XIII, Section 7, page 93): a graph `G`, a wall
`W` of height `h` in `G`, and `p.choose 2` `(l, m)`-stars over `W` with distinct centers. The
`a`-th star has center `centers a` and paths `rays a i` (`i : Fin l`). The stars are as on page 91:
"(i) $P_1, \dots, P_l$ are paths of $G$ and all have one end $v$, and are otherwise mutually
vertex-disjoint (ii) for $1 \le i \le l$, let the ends of $P_i$ be $v, u_i$; then $u_i \ne v$, and
$u_i \in V(H)$, and no edge or internal vertex of $P_i$ is in $H$ (iii) for $1 \le i < j \le l$,
$u_i$ and $u_j$ are at distance $\ge m$ in $H$." Stars with different centers may meet. -/
structure Alg77Input (p l m : ℕ) where
  /-- Number of vertices `|V(G)|`. -/
  n : ℕ
  /-- Height `h` of the wall `W`. -/
  h : ℕ
  /-- The input graph `G` on `Fin n`. -/
  G : MultiDigraph n
  /-- The wall `H` of height `h` in `G`. -/
  W : WallOfHeight h G
  /-- The centers of the stars. -/
  centers : Fin (p.choose 2) → Fin n
  /-- The paths of the stars. -/
  rays : Fin (p.choose 2) → Fin l → List (Fin n)
  /-- `h ≥ 2` is even and `W` is a valid wall in `G`. -/
  hW_valid : 2 ≤ h ∧ Even h ∧ W.IsValid
  /-- The centers are distinct. -/
  hcenters : Function.Injective centers
  /-- (i), (ii): each path starts at the center of its star and is a ray over `W`. -/
  hrays : ∀ a i, W.IsStarRay (centers a) (rays a i)
  /-- (i): two paths of one star meet only at the center. -/
  hrays_meet : ∀ a, ∀ i j : Fin l, i ≠ j → ∀ v, v ∈ rays a i → v ∈ rays a j → v = centers a
  /-- (iii): the ends of two paths of one star are at distance `≥ m` in `W`. -/
  hends_dist : ∀ a, ∀ i j : Fin l, i ≠ j → ∀ u v,
    (rays a i).getLast? = some u → (rays a j).getLast? = some v → m ≤ W.brickDist u v

/-- Problem size `ε(G) = |E(G)| + |V(G)| + 1` for (7.7), as for (7.4). -/
def alg77Size {p l m : ℕ} (x : Alg77Input p l m) : ℕ :=
  x.G.numEdges + x.n + 1

/-- The input of (7.7) in `inArr`: `x.G.enc ++ x.W.encList`, then for each star its center
followed by `encHPaths` of its paths. -/
def encAlg77In {p l m : ℕ} (x : Alg77Input p l m) : List ℕ :=
  x.G.enc ++ x.W.encList ++
    (List.finRange (p.choose 2)).flatMap (fun a => (x.centers a).1 :: encHPaths (x.rays a))

/-- The output of (7.7), as for (7.4): a model of `K_p` in `G`, written out. -/
def IsAlg77Output (p : ℕ) {l m : ℕ} (x : Alg77Input p l m) (out : List ℕ) : Prop :=
  ∃ M : UnderlyingGraphModel (completeComputeDigraph p) x.G.toComputeDigraph,
    out = encUnderlyingGraphModel M

/-- **Graph Minors XIII, (7.7), the algorithm** (Section 7, page 93): "Moreover, there
is an algorithm, with running time $\le C\varepsilon(G)$, where $C$ depends only on $p$, which,
given $\binom{p}{2}$ $(l, m)$-stars with distinct centers over a wall $H$ in a graph $G$, finds a
model of $K_p$ in $G$." -/
def Algorithm77Statement : Prop :=
  ∀ p : ℕ, 2 ≤ p →
    ∃ l m : ℕ, 3 ≤ l ∧ ∃ P : Cmd,
      ComputesArrRelInTime (alg77Size (p := p) (l := l) (m := m))
        (encAlg77In (p := p) (l := l) (m := m)) (IsAlg77Output p) P (fun s => s)

/-! ### Section 6: (7.2), a branch-decomposition or a wall -/

/-- An input of the algorithm of (7.2) (GM XIII, Section 7, page 89): "*Input:* A graph $G$." -/
structure Algorithm72Input where
  /-- Number of vertices `|V(G)|`. -/
  n : ℕ
  /-- The input graph `G` on `Fin n`. -/
  G : MultiDigraph n

/-- Problem size `v² + ε` for (7.2): `(|V(G)| + 1)² + |E(G)| + |V(G)| + 1`. -/
def algorithm72Size (x : Algorithm72Input) : ℕ :=
  (x.n + 1) ^ 2 + x.G.numEdges + x.n + 1

/-- The input of (7.2) in `inArr`: `x.G.enc`. -/
def encAlgorithm72In (x : Algorithm72Input) : List ℕ :=
  x.G.enc

/-- The output of (7.2) (page 89): "Either a branch-decomposition of $G$ of width $\le \omega$, or
a wall of height $h$ which is a subgraph of $G$." The first case is `0` followed by a
decomposition code (`IsValidBranchDecompCode`, the output format of (3.3)); the second is `1`
followed by the wall, written as `W.encList`. -/
def IsAlgorithm72Output (ω h : ℕ) (x : Algorithm72Input) (out : List ℕ) : Prop :=
  (∃ code : List ℕ, out = 0 :: code ∧ IsValidBranchDecompCode ω x.G code) ∨
  (∃ W : WallOfHeight h x.G, W.IsValid ∧ out = 1 :: W.encList)

/-- **Graph Minors XIII, (7.1) and (7.2)** (Section 7, page 89): for every even `h ≥ 2` there is
`ω` and a program as in (7.2), "with running time $O(v^2 + \varepsilon)$". The `ω` is one for which
"every graph with branch-width $\ge \omega/3$ has a minor isomorphic to the elementary wall of
height $h$" (7.1). -/
def Algorithm72Statement : Prop :=
  ∀ h : ℕ, 2 ≤ h → Even h →
    ∃ ω : ℕ, ∃ P : Cmd,
      ComputesArrRelInTime algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h) P
        (fun s => s)

end GraphMinor.Compute
