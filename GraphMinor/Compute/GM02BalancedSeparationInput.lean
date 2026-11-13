module

public import GraphMinor.Compute.Parse
public import GraphMinor.GM02.ComponentTest
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Inputs and outputs of the balanced-separation algorithm

II (3.1), page 316, takes a simple graph and a subset of its vertices.
Use numbered vertices, the standard graph edge-list encoding, and one
membership bit per vertex for the subset. A successful output encodes
the two vertex sets of a separation. The edges are recovered by assigning
all edges in the first induced side there and all other edges to the
second side. A negative output asserts that no balanced separation of
the permitted order exists.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- The plain instance of Graph Minors II (3.1), page 316. -/
structure GM02Alg31Input where
  /-- The number of numbered vertices. -/
  n : ℕ
  /-- The input simple graph. -/
  G : SimpleGraph (Fin n)
  /-- Adjacency is finite input data. -/
  [decAdj : DecidableRel G.Adj]
  /-- The specified vertex subset. -/
  Q : Finset (Fin n)

attribute [instance] GM02Alg31Input.decAdj

/-- Encode a subset by its membership bits in vertex order. -/
def gm02VertexBits {n : ℕ} (Q : Finset (Fin n)) : List ℕ :=
  List.ofFn (fun v : Fin n => if v ∈ Q then 1 else 0)

/-- The graph prefix followed by the given subset's membership bits.
No separator or component information is part of the input. -/
def GM02Alg31Input.enc (x : GM02Alg31Input) : List ℕ :=
  encGraph x.G ++ gm02VertexBits x.Q

/-- The size parameter for II (3.1), whose input graph is simple. -/
def gm02Alg31Size (x : GM02Alg31Input) : ℕ := x.n

/-- Decode a bit array as a vertex set. -/
def gm02DecodedVertices {n : ℕ} (bits : List ℕ) : Set (Fin n) :=
  {v | bits[v.val]?.getD 0 = 1}

/-- The graph prefix and the given subset determine the complete input. -/
theorem GM02Alg31Input.enc_length (x : GM02Alg31Input) :
    x.enc.length = 2 + 2 * (edgeListOf x.G).length + x.n := by
  simp only [GM02Alg31Input.enc, List.length_append, length_encGraph,
    gm02VertexBits, List.length_ofFn]

/-- Membership bits recover exactly the specified subset. -/
theorem gm02DecodedVertices_bits {n : ℕ} (Q : Finset (Fin n)) :
    gm02DecodedVertices (gm02VertexBits Q) = (Q : Set (Fin n)) := by
  ext v
  simp only [gm02DecodedVertices, Set.mem_ofPred_eq, gm02VertexBits,
    List.getElem?_ofFn, dite_eq_left v.isLt, Option.getD_some, Fin.eta]
  by_cases hv : v ∈ Q <;> simp [hv]

/-- The exact separation output condition of II (3.1). The two arrays
encode the vertex sets of actual covering subgraphs with partitioned edges.
Balance is multiplied by three to avoid fractions. -/
def GM02Alg31Input.validSides (x : GM02Alg31Input) (w : ℤ)
    (left right : List ℕ) : Prop :=
  ∃ H H' : Graph (Fin x.n) (Sym2 (Fin x.n)),
    GM02.IsSeparation (Graph.ofSimpleGraph x.G) H H' ∧
    V(H) = gm02DecodedVertices left ∧ V(H') = gm02DecodedVertices right ∧
    ((V(H) ∩ V(H')).ncard : ℤ) ≤ w ∧
    3 * ((V(H) \ V(H')) ∩ (x.Q : Set (Fin x.n))).ncard ≤
      2 * ((x.Q : Set (Fin x.n)) \ (V(H) ∩ V(H'))).ncard ∧
    3 * ((V(H') \ V(H)) ∩ (x.Q : Set (Fin x.n))).ncard ≤
      2 * ((x.Q : Set (Fin x.n)) \ (V(H) ∩ V(H'))).ncard

/-- A positive flag is accompanied by both side bit arrays. A negative
flag is valid exactly when no such output separation exists. -/
def GM02Alg31Input.correct (x : GM02Alg31Input) (w : ℤ) (s : State) : Prop :=
  (s.regs outReg = 1 ∧ x.validSides w (s.arrs outArr) (s.arrs 2)) ∨
  (s.regs outReg = 0 ∧ ¬∃ left right, x.validSides w left right)

end GraphMinor.Compute
