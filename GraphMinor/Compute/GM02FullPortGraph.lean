module

public import GraphMinor.Compute.GM02PortAssignmentCodes
public import GraphMinor.Compute.BitSet
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The split graph with all supplied positions retained

Number old vertices first, host edge vertices next, and the fixed set of
candidate terminal slots last. Removed edge positions, old branch
vertices, and inactive terminal slots are isolated. Retaining these
positions avoids any renumbering during the RAM construction of the
corrected split graph for II (4.6), page 319.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The number of allocated split-graph vertex positions. -/
def gm02FullPortSize (x : GM02TopologicalInput) (K : ℕ) : ℕ :=
  x.G.n + x.G.edges.length + 2 * K

/-- Adjacency in increasing order between old and edge vertices or between edge vertices and terminals. -/
def gm02FullPortForward (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K u v : ℕ) : Prop :=
  (u < x.G.n ∧ x.G.n ≤ v ∧ v < x.G.n + x.G.edges.length ∧
    (bitSetList x.vertices)[u]? = some 0 ∧ gflags[v - x.G.n]? = some 1 ∧
    (if he : v - x.G.n < x.G.edges.length then
      (x.G.edges[v - x.G.n]'he).1.val = u ∨ (x.G.edges[v - x.G.n]'he).2.val = u
     else False)) ∨
  (x.G.n ≤ u ∧ u < x.G.n + x.G.edges.length ∧
    x.G.n + x.G.edges.length ≤ v ∧ v < gm02FullPortSize x K ∧
    (v - (x.G.n + x.G.edges.length)) / 2 < x.edges.length ∧
    hflags[(v - (x.G.n + x.G.edges.length)) / 2]? = some 1 ∧
    gflags[u - x.G.n]? = some 1 ∧
    gm02SeparatorDigit x.G.edges.length code (v - (x.G.n + x.G.edges.length)) = u - x.G.n)

instance gm02FullPortForward_decidable (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K : ℕ) :
    DecidableRel (gm02FullPortForward x gflags hflags code K) := by
  intro u v
  unfold gm02FullPortForward
  infer_instance

/-- Each forward adjacency goes from a smaller to a larger numeric vertex name. -/
theorem gm02FullPortForward_lt (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K u v : ℕ) (h : gm02FullPortForward x gflags hflags code K u v) : u < v := by
  rcases h with h | h
  · exact h.1.trans_le h.2.1
  · exact h.2.1.trans_le h.2.2.1

/-- The finite simple split graph on all allocated positions, including isolated unused slots. -/
def gm02FullPortGraph (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) : SimpleGraph (Fin (gm02FullPortSize x K)) :=
  SimpleGraph.fromRel (fun u v => gm02FullPortForward x gflags hflags code K u.val v.val)

instance gm02FullPortGraph_decidable (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (code K : ℕ) :
    DecidableRel (gm02FullPortGraph x gflags hflags code K).Adj := by
  unfold gm02FullPortGraph
  infer_instance

/-- A canonical increasing pair is adjacent precisely when it passes the forward test. -/
theorem gm02FullPortGraph_adj_of_lt (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (u v : Fin (gm02FullPortSize x K)) (huv : u.val < v.val) :
    (gm02FullPortGraph x gflags hflags code K).Adj u v ↔
      gm02FullPortForward x gflags hflags code K u.val v.val := by
  rw [gm02FullPortGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact False.elim (Nat.lt_asymm huv (gm02FullPortForward_lt x gflags hflags code K v.val u.val h))
  · intro h
    exact ⟨fun heq => (Nat.ne_of_lt huv) (congrArg Fin.val heq), Or.inl h⟩

end GraphMinor.Compute
