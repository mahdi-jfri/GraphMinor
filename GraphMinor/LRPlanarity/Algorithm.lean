module

public import GraphMinor.LRPlanarity.Defs
public import Mathlib.Data.List.OfFn

/-!
# The Boolean left-right test

This is the functional meaning of the array algorithm in `docs/planarity/planarity_linear.py` and
`docs/planarity/planarity_test.tex`, Part I. Search uses explicit frames and fuel.
The lowpoint insertion, global bucket pass, merge, trim, and postorder loop follow
that order. Lists below describe the contents of linked lists, not their RAM cost.
A separate RAM specification requires a program with constant-time pointer append.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

/-- Part I, Section 1: the two smallest distinct depths, with repeated upper sentinel. -/
structure LowPair where
  low : ℕ
  second : ℕ
  deriving Inhabited, Repr, DecidableEq

/-- Part I, Section 1, `INSERT`: values above the sentinel are ignored. -/
def insertLow (p : LowPair) (k : ℕ) : LowPair :=
  if k < p.low then ⟨k, p.low⟩
  else if p.low < k ∧ k < p.second then ⟨p.low, k⟩ else p

/-- Part I, Section 1: an oriented edge and its computed lowpoints. -/
structure EdgeRecord where
  source : ℕ
  target : ℕ
  tree : Bool
  pair : LowPair
  key : ℕ := 0
  deriving Inhabited, Repr

/-- Part I, Section 1: explicit vertex and next-adjacency-index frames. -/
structure Frame where
  vertex : ℕ
  next : ℕ
  deriving Inhabited, Repr

/-- The search arrays and postorder. Missing depths denote undiscovered vertices. -/
structure Search where
  depth : Array (Option ℕ)
  parent : Array (Option ℕ)
  parentEdge : Array (Option ℕ)
  edges : Array EdgeRecord
  postorder : List ℕ
  deriving Inhabited, Repr

/-- Initial fixed-size search arrays. -/
def initialSearch (n : ℕ) : Search :=
  ⟨Array.replicate n none, Array.replicate n none, Array.replicate n none, #[], []⟩

/-- Finish an edge and insert both its lowpoints into its source's incoming edge. -/
def finishEdge (s : Search) (i : ℕ) : Search := Id.run do
  let e := s.edges[i]!
  let e := { e with key := 2 * e.pair.low +
    (decide (e.pair.second < (s.depth[e.source]?.join).getD 0)).toNat }
  let mut s := { s with edges := s.edges.set! i e }
  if let some p := s.parentEdge[e.source]?.join then
    let pe := s.edges[p]!
    let pair := insertLow (insertLow pe.pair e.pair.low) e.pair.second
    s := { s with edges := s.edges.set! p { pe with pair := pair } }
  return s

/-- Create an oriented record, initializing lowpoints as in Part I, Section 1. -/
def addEdge (s : Search) (v w : ℕ) (tree : Bool) : Search × ℕ :=
  let h := (s.depth[v]?.join).getD 0
  let low := if tree then h else (s.depth[w]?.join).getD 0
  ({ s with edges := s.edges.push ⟨v, w, tree, ⟨low, h⟩, 0⟩ }, s.edges.size)

/-- One component of the explicit-frame search. `none` denotes exhausted fuel or an
out-of-range neighbor. Each frame step scans an incidence or completes a vertex. -/
def searchFrames (adj : Array (List ℕ)) : ℕ → Search → List Frame → Option Search
  | 0, _, _ :: _ => none
  | _, s, [] => some s
  | fuel + 1, s, f :: stack => Id.run do
    let v := f.vertex
    let neighbors := adj[v]!
    if f.next ≥ neighbors.length then
      let s := { s with postorder := v :: s.postorder }
      let s := match s.parentEdge[v]?.join with
        | none => s
        | some p => finishEdge s p
      return searchFrames adj fuel s stack
    let w := neighbors[f.next]!
    if w ≥ adj.size then return none
    let stack := { f with next := f.next + 1 } :: stack
    if (s.depth[w]?.join).isNone then
      let (s, i) := addEdge s v w true
      let s := { s with
        parent := s.parent.set! w (some v)
        parentEdge := s.parentEdge.set! w (some i)
        depth := s.depth.set! w (some ((s.depth[v]?.join).getD 0 + 1)) }
      return searchFrames adj fuel s (⟨w, 0⟩ :: stack)
    else if s.parent[v]?.join ≠ some w ∧
        (s.depth[w]?.join).getD 0 < (s.depth[v]?.join).getD 0 then
      let (s, i) := addEdge s v w false
      return searchFrames adj fuel (finishEdge s i) stack
    else
      return searchFrames adj fuel s stack

/-- Part I, Section 1: scan roots in label order. The per-component fuel covers all
incidence scans and vertex completions, including on malformed input. -/
def depthFirstSearch (adj : Array (List ℕ)) : Option Search := Id.run do
  let fuel := adj.foldl (fun total l => total + l.length) 0 + adj.size + 1
  let mut s := initialSearch adj.size
  for root in [:adj.size] do
    if (s.depth[root]?.join).isNone then
      s := { s with depth := s.depth.set! root (some 0) }
      match searchFrames adj fuel s [⟨root, 0⟩] with
      | none => return none
      | some t => s := t
  return some { s with postorder := s.postorder.reverse }

/-- Decode raw parent labels, without assuming that the output is a forest. -/
def Search.forest (s : Search) (N : ℕ) : Forest N where
  parent v := (s.parent[v.val]?.join).bind fun p =>
    if hp : p < N then some ⟨p, hp⟩ else none
  depth v := (s.depth[v.val]?.join).getD 0

/-- Part I, Section 1: one global bucket array, scanned once. Each outgoing list
has increasing key. Prepending followed by reversal describes per-source appending. -/
def bucketOrder (n : ℕ) (edges : Array EdgeRecord) : Array (List ℕ) := Id.run do
  let mut buckets := Array.replicate (2 * n + 1) ([] : List ℕ)
  for i in [:edges.size] do
    let k := edges[i]!.key
    buckets := buckets.set! k (i :: buckets[k]!)
  let mut outgoing := Array.replicate n ([] : List ℕ)
  for bucket in buckets do
    for i in bucket do
      let v := edges[i]!.source
      outgoing := outgoing.set! v (i :: outgoing[v]!)
  return outgoing.map List.reverse

/-- Part I, Section 3: a return node retains its back-edge identifier and depth. -/
structure ReturnNode where
  edge : ℕ
  depth : ℕ
  deriving Inhabited, Repr, DecidableEq

/-- Part I, Section 3: the two lists of a block. -/
structure Block where
  left : List ReturnNode
  right : List ReturnNode
  deriving Inhabited, Repr

/-- The empty-list maximum is `-1`, as specified in Part I, Section 3. -/
def listMaximum (l : List ReturnNode) : Int :=
  match l with | [] => -1 | b :: _ => b.depth

/-- A nonempty list's minimum is its last depth. -/
def listMinimum (l : List ReturnNode) : ℕ := (l.getLast?).getD default |>.depth

/-- Block maximum, including the empty-list convention. -/
def Block.maximum (b : Block) : Int := max (listMaximum b.left) (listMaximum b.right)

/-- Block minimum uses only its nonempty sides. -/
def Block.minimum (b : Block) : ℕ :=
  if b.left.isEmpty then listMinimum b.right
  else if b.right.isEmpty then listMinimum b.left
  else min (listMinimum b.left) (listMinimum b.right)

/-- Part I, Section 3: the anchor is separate. The stack is stored top first. -/
structure Summary where
  least : ℕ
  anchor : List ReturnNode
  blocks : List Block
  deriving Inhabited, Repr

/-- Part I, Section 4: consume the child stack, rejecting a two-sided block. -/
def mergeChild : List Block → List ReturnNode → Option (List ReturnNode)
  | [], right => some right
  | q :: rest, right =>
    if !q.left.isEmpty && !q.right.isEmpty then none
    else mergeChild rest (right ++ if q.left.isEmpty then q.right else q.left)

/-- Part I, Section 4: consume old blocks meeting the depths above the new minimum. -/
def mergeOld (b : ℕ) : List Block → List ReturnNode → List ReturnNode →
    Option (List Block × List ReturnNode × List ReturnNode)
  | [], left, right => some ([], left, right)
  | q :: rest, left, right =>
    if q.maximum > (b : Int) then
      let q := if listMaximum q.right > (b : Int) then ⟨q.right, q.left⟩ else q
      if listMaximum q.right > (b : Int) then none
      else mergeOld b rest (left ++ q.left) (right ++ q.right)
    else some (q :: rest, left, right)

/-- Part I, Section 4, `MERGE`. Outer `none` means rejection. Inner `none` means
an empty summary. Concatenations specify the contents after pointer transfers. -/
def merge (old new : Option Summary) : Option (Option Summary) := do
  match old, new with
  | _, none => return old
  | none, _ => return new
  | some s, some t =>
    let right ← mergeChild t.blocks []
    let anchor := if t.least = s.least then s.anchor ++ t.anchor else s.anchor
    let right := if t.least = s.least then right else right ++ t.anchor
    let (blocks, left, right) ← mergeOld t.least s.blocks [] right
    let blocks := if left.isEmpty && right.isEmpty then blocks
      else ⟨left, right⟩ :: blocks
    return some ⟨s.least, anchor, blocks⟩

/-- Part I, Section 5: pop whole blocks at the trimming depth. -/
def trimBlocks (c : ℕ) : List Block → List Block
  | [] => []
  | q :: rest =>
    if q.minimum = c then trimBlocks c rest
    else { q with left := q.left.dropWhile (fun b => b.depth == c)
                  right := q.right.dropWhile (fun b => b.depth == c) } :: rest

/-- Part I, Section 5, `TRIM`: alignments precede deletion at the parent depth. -/
def trim (s : Option Summary) (c : ℕ) : Option Summary :=
  s.bind fun s => if s.least = c then none else some { s with blocks := trimBlocks c s.blocks }

/-- Part I, Section 6: integrate the outgoing edges at one vertex in bucket order,
transferring a child summary by clearing its old slot. -/
def solveOutgoing (search : Search) : List ℕ → Array (Option Summary) →
    Option Summary → Option (Array (Option Summary) × Option Summary)
  | [], results, summary => some (results, summary)
  | i :: rest, results, summary => do
    let e := search.edges[i]!
    let (child, results) := if e.tree then
        (results[e.target]!, results.set! e.target none)
      else (some ⟨(search.depth[e.target]?.join).getD 0,
        [⟨i, (search.depth[e.target]?.join).getD 0⟩], []⟩, results)
    let summary ← merge summary child
    solveOutgoing search rest results summary

/-- Part I, Section 6: the postorder solver returns false at the first rejected merge. -/
def solve (n : ℕ) (search : Search) (outgoing : Array (List ℕ)) : Bool := Id.run do
  let mut results := Array.replicate n (none : Option Summary)
  for v in search.postorder do
    match solveOutgoing search outgoing[v]! results none with
    | none => return false
    | some (rs, summary) =>
      let summary := match search.parent[v]?.join with
        | none => summary
        | some u => trim summary ((search.depth[u]?.join).getD 0)
      results := rs.set! v summary
  return true

/-- The Boolean adjacency-list test of Parts I and V. Invalid input or exhausted
search fuel is rejected. The empty graph is accepted by the same loop. -/
def lrTest {N : ℕ} (lists : Fin N → List ℕ) : Bool :=
  match depthFirstSearch (List.ofFn lists).toArray with
  | none => false
  | some search => solve N search (bucketOrder N search.edges)

end GraphMinor.LRPlanarity
