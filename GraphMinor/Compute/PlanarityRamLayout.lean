module

public import GraphMinor.Compute.Basic
public import GraphMinor.LRPlanarity.Algorithm

/-!
# Array representation of the left-right test

The layout follows Part V, Section 1 of the planarity note. Arrays have their
final capacities from the start. Search arrays store live prefixes. Linked
lists carry back-edge identifiers as well as depth keys. Their representation
records the actual pointer chain, its tail, and the distinct owned addresses.
Block stacks record both node ownership and block ownership.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The fields of the fixed arenas of Part V, Section 1. -/
inductive Field where
  | depth | parent | parentEdge
  | tail | head | tree | low | low2 | key
  | frameVertex | frameNext | postorder
  | bucket | bucketNext | outgoingFirst | outgoingLast | outgoingNext
  | nodeEdge | nodeDepth | nodeNext
  | blockLeftFirst | blockLeftLast | blockRightFirst | blockRightLast | blockBelow
  | summaryLeast | summaryFirst | summaryLast | summaryTop | result
  deriving DecidableEq, Repr

/-- All work arrays are above the three adjacency-list arrays. -/
def Field.array : Field → ℕ
  | .depth => 33 | .parent => 34 | .parentEdge => 35
  | .tail => 36 | .head => 37 | .tree => 38 | .low => 39 | .low2 => 40 | .key => 41
  | .frameVertex => 42 | .frameNext => 43 | .postorder => 44
  | .bucket => 45 | .bucketNext => 46 | .outgoingFirst => 47 | .outgoingLast => 48
  | .outgoingNext => 49 | .nodeEdge => 50 | .nodeDepth => 51 | .nodeNext => 52
  | .blockLeftFirst => 53 | .blockLeftLast => 54 | .blockRightFirst => 55
  | .blockRightLast => 56 | .blockBelow => 57
  | .summaryLeast => 58 | .summaryFirst => 59 | .summaryLast => 60
  | .summaryTop => 61 | .result => 62

/-- `M` counts adjacency entries, so it also bounds the number of oriented
records, back-edge nodes, singleton summaries, and effective merges. Pointer
arenas reserve slot zero for null. Other arrays use ordinary zero-based indices. -/
def Field.capacity (N M : ℕ) : Field → ℕ
  | .depth | .parent | .parentEdge | .frameVertex | .frameNext | .postorder
  | .outgoingFirst | .outgoingLast | .result => N
  | .bucket => 2 * N + 1
  | .nodeEdge | .nodeDepth | .nodeNext
  | .blockLeftFirst | .blockLeftLast | .blockRightFirst | .blockRightLast | .blockBelow
  | .summaryLeast | .summaryFirst | .summaryLast | .summaryTop => M + 1
  | _ => M

/-- Optional natural numbers are stored as zero or one more than the value. -/
def optionWord : Option ℕ → ℕ
  | none => 0
  | some n => n + 1

/-- A live sequence occupies a prefix. Unused words have no specified values. -/
def PrefixAt (s : State) (a capacity : ℕ) (xs : List ℕ) : Prop :=
  (s.arrs a).length = capacity ∧ xs.length ≤ capacity ∧
    (s.arrs a).take xs.length = xs

/-- Search records use the six parallel edge arrays of Part I, Section 1.
Register 37 holds the number of live edge records and register 39 the number
of completed vertices. Optional depths and parents use `optionWord`. -/
def SearchAt (N M : ℕ) (s : State) (search : Search) : Prop :=
  search.depth.size = N ∧ search.parent.size = N ∧ search.parentEdge.size = N ∧
  s.regs 37 = search.edges.size ∧ s.regs 39 = search.postorder.length ∧
  PrefixAt s Field.depth.array N (search.depth.toList.map optionWord) ∧
  PrefixAt s Field.parent.array N (search.parent.toList.map optionWord) ∧
  PrefixAt s Field.parentEdge.array N (search.parentEdge.toList.map optionWord) ∧
  PrefixAt s Field.tail.array M (search.edges.toList.map EdgeRecord.source) ∧
  PrefixAt s Field.head.array M (search.edges.toList.map EdgeRecord.target) ∧
  PrefixAt s Field.tree.array M (search.edges.toList.map fun e => e.tree.toNat) ∧
  PrefixAt s Field.low.array M (search.edges.toList.map fun e => e.pair.low) ∧
  PrefixAt s Field.low2.array M (search.edges.toList.map fun e => e.pair.second) ∧
  PrefixAt s Field.key.array M (search.edges.toList.map EdgeRecord.key) ∧
  PrefixAt s Field.postorder.array N search.postorder

/-- Frames are stored bottom first, so push/pop touch the last live slot.
The functional search keeps its top frame first. -/
def FramesAt (N : ℕ) (s : State) (stack : List Frame) : Prop :=
  s.regs 38 = stack.length ∧
  PrefixAt s Field.frameVertex.array N (stack.reverse.map Frame.vertex) ∧
  PrefixAt s Field.frameNext.array N (stack.reverse.map Frame.next)

/-- The precise node chain of Part I, Section 3. The address list records
ownership, not just the depths of the represented returns. -/
inductive NodeChain (s : State) (capacity : ℕ) :
    ℕ → List ℕ → List ReturnNode → Prop where
  | nil : NodeChain s capacity 0 [] []
  | cons {p q : ℕ} {ps : List ℕ} {b : ReturnNode} {bs : List ReturnNode}
      (positive : 0 < p) (bound : p < capacity)
      (edge : (s.arrs Field.nodeEdge.array)[p]? = some b.edge)
      (depth : (s.arrs Field.nodeDepth.array)[p]? = some b.depth)
      (next : (s.arrs Field.nodeNext.array)[p]? = some q)
      (rest : NodeChain s capacity q ps bs) :
      NodeChain s capacity p (p :: ps) (b :: bs)

/-- A list header names both ends. Null is the tail exactly for an empty list.
Distinct addresses rule out cycles and repeated ownership within the list. -/
def ListAt (s : State) (capacity first last : ℕ)
    (addresses : List ℕ) (nodes : List ReturnNode) : Prop :=
  NodeChain s capacity first addresses nodes ∧
    last = (addresses.getLast?).getD 0 ∧ addresses.Nodup

/-- The block stack of Part I, Section 3. Each block owns two list headers
and the pointer to the next lower block. The two address lists expose every
owned block and every owned return node for disjointness checks. -/
inductive BlockChain (s : State) (capacity : ℕ) :
    ℕ → List ℕ → List ℕ → List Block → Prop where
  | nil : BlockChain s capacity 0 [] [] []
  | cons {p below lf ll rf rl : ℕ} {blocks nodes left right : List ℕ}
      {b : Block} {bs : List Block}
      (positive : 0 < p) (bound : p < capacity)
      (leftFirst : (s.arrs Field.blockLeftFirst.array)[p]? = some lf)
      (leftLast : (s.arrs Field.blockLeftLast.array)[p]? = some ll)
      (rightFirst : (s.arrs Field.blockRightFirst.array)[p]? = some rf)
      (rightLast : (s.arrs Field.blockRightLast.array)[p]? = some rl)
      (next : (s.arrs Field.blockBelow.array)[p]? = some below)
      (leftList : ListAt s capacity lf ll left b.left)
      (rightList : ListAt s capacity rf rl right b.right)
      (rest : BlockChain s capacity below blocks nodes bs) :
      BlockChain s capacity p (p :: blocks) (left ++ right ++ nodes) (b :: bs)

/-- A summary record holds its least depth, separate anchor header, and stack
top. Node and block addresses are distinct throughout this summary. Order
conditions on depths are solver invariants, rather than encoding conditions. -/
def SummaryAt (s : State) (M p : ℕ) (summary : Summary)
    (blocks nodes : List ℕ) : Prop :=
  0 < p ∧ p < M + 1 ∧
  (s.arrs Field.summaryLeast.array)[p]? = some summary.least ∧
  ∃ first last top anchor stackNodes,
    (s.arrs Field.summaryFirst.array)[p]? = some first ∧
    (s.arrs Field.summaryLast.array)[p]? = some last ∧
    (s.arrs Field.summaryTop.array)[p]? = some top ∧
    ListAt s (M + 1) first last anchor summary.anchor ∧
    BlockChain s (M + 1) top blocks stackNodes summary.blocks ∧
    nodes = anchor ++ stackNodes ∧ nodes.Nodup ∧ blocks.Nodup

/-- Work arrays never alias the preserved arrays. -/
theorem Field.array_ge (f : Field) : 33 ≤ f.array := by
  cases f <;> decide

/-- No two fields share an array. -/
theorem Field.array_injective : Function.Injective Field.array := by
  intro a b h
  cases a <;> cases b <;> simp_all [Field.array]

/-- Every individual arena has a linear capacity. -/
theorem Field.capacity_le (N M : ℕ) (f : Field) :
    f.capacity N M ≤ 2 * (N + M + 1) := by
  cases f <;> simp only [Field.capacity] <;> omega

/-- A represented list owns exactly one address per return. -/
theorem NodeChain.length_eq {s : State} {capacity first : ℕ}
    {addresses : List ℕ} {nodes : List ReturnNode}
    (h : NodeChain s capacity first addresses nodes) :
    addresses.length = nodes.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ ih => simpa using ih

/-- Null denotes precisely the empty represented list. -/
theorem NodeChain.first_eq_zero_iff {s : State} {capacity first : ℕ}
    {addresses : List ℕ} {nodes : List ReturnNode}
    (h : NodeChain s capacity first addresses nodes) :
    first = 0 ↔ nodes = [] := by
  cases h with
  | nil => simp
  | cons positive _ _ _ _ _ => simp [Nat.ne_of_gt positive]

/-- Each represented block occupies exactly one block record. -/
theorem BlockChain.length_eq {s : State} {capacity first : ℕ}
    {blocks nodes : List ℕ} {stack : List Block}
    (h : BlockChain s capacity first blocks nodes stack) :
    blocks.length = stack.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ ih => simpa using ih

end GraphMinor.Compute.PlanarityRam
