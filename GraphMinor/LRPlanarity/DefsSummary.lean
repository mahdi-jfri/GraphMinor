module

public import GraphMinor.LRPlanarity.Algorithm

/-!
# Meanings of blocks and summaries

Part I, Section 3 and Part II of `docs/planarity/planarity_test.tex` describe the
same formula in a physical anchor/stack representation and a logical block
representation. This file defines the formula and the ordering and ownership
conditions on the representation. It assumes no merge or projection theorem.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

/-- Part II: the set of variables occurring in a return list. -/
def nodeSet (nodes : List ReturnNode) : Set ℕ := {i | ∃ b ∈ nodes, b.edge = i}

/-- Part II: each side is monochromatic, with opposite colors on nonempty sides. -/
def Block.Holds (block : Block) (color : ℕ → Color) : Prop :=
  Monochromatic color (nodeSet block.left) ∧
  Monochromatic color (nodeSet block.right) ∧
  ∀ i ∈ nodeSet block.left, ∀ j ∈ nodeSet block.right, color i ≠ color j

/-- The nodes of a block, without imposing a color. -/
def Block.nodes (block : Block) : List ReturnNode := block.left ++ block.right

/-- The live nodes of a summary. -/
def Summary.nodes (s : Summary) : List ReturnNode :=
  s.anchor ++ s.blocks.flatMap Block.nodes

/-- Part II: the anchor is an independent monochromatic class. -/
def Summary.Holds (s : Summary) (color : ℕ → Color) : Prop :=
  Monochromatic color (nodeSet s.anchor) ∧ ∀ b ∈ s.blocks, b.Holds color

/-- Part II: empty summaries represent the empty formula. -/
def SummaryFormula (s : Option Summary) (color : ℕ → Color) : Prop :=
  match s with | none => True | some t => t.Holds color

/-- Live nodes, including the empty summary. -/
def summaryNodes (s : Option Summary) : List ReturnNode :=
  match s with | none => [] | some t => t.nodes

/-- Part I, Section 3: nonincreasing depth order in a list. -/
def OrderedNodes (nodes : List ReturnNode) : Prop :=
  nodes.Pairwise (fun b c => c.depth ≤ b.depth)

/-- Part I, Section 3: anchor, list order, stack order, and disjoint ownership.
The stack is top first, so upper depths are at least lower depths. These are
representation conditions, not correctness claims about the algorithm. -/
def Summary.Valid (s : Summary) : Prop :=
  s.anchor ≠ [] ∧
  (∀ b ∈ s.anchor, b.depth = s.least) ∧
  (∀ q ∈ s.blocks, q.nodes ≠ [] ∧ OrderedNodes q.left ∧ OrderedNodes q.right ∧
    ∀ b ∈ q.nodes, s.least < b.depth) ∧
  s.blocks.Pairwise (fun upper lower =>
    ∀ b ∈ upper.nodes, ∀ c ∈ lower.nodes, c.depth ≤ b.depth) ∧
  (s.nodes.map ReturnNode.edge).Nodup

/-- Exact existential projection onto the variables that remain live, Part II (I2). -/
def ProjectsTo (formula : (ℕ → Color) → Prop) (live : Set ℕ)
    (result : (ℕ → Color) → Prop) : Prop :=
  ∀ color, result color ↔ ∃ extension, formula extension ∧
    ∀ i ∈ live, extension i = color i

end GraphMinor.LRPlanarity
