module

public import GraphMinor.Compute.PlanarityRamUpdate

/-!
# Bounds on search data

DFS stores vertex labels, optional depths and parent-edge identifiers, two
lowpoints, and sorting keys. The predicates here contain only bounds on
those data. They contain no execution, refinement, or termination claim.
They are the bounds maintained in the frame-loop proof.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The endpoint and numeric field bounds for one oriented record. -/
def EdgeBounded (N : ℕ) (edge : EdgeRecord) : Prop :=
  edge.source < N ∧ edge.target < N ∧ edge.pair.low < N ∧
    edge.pair.second < N ∧ edge.key ≤ 2 * N

/-- The fixed array sizes and bounds on all live search data. -/
def SearchBounded (N : ℕ) (search : Search) : Prop :=
  search.depth.size = N ∧ search.parent.size = N ∧ search.parentEdge.size = N ∧
  (∀ v : Fin N, ∀ d : ℕ, search.depth[v.val]?.join = some d → d < N) ∧
  (∀ v : Fin N, ∀ p : ℕ, search.parent[v.val]?.join = some p → p < N) ∧
  (∀ v : Fin N, ∀ i : ℕ, search.parentEdge[v.val]?.join = some i → i < search.edges.size) ∧
  (∀ i : ℕ, i < search.edges.size → EdgeBounded N search.edges[i]!)

/-- The empty search satisfies the field bounds for every vertex count. -/
theorem SearchBounded.initial (N : ℕ) : SearchBounded N (initialSearch N) := by
  refine ⟨by simp [initialSearch], by simp [initialSearch], by simp [initialSearch], ?_, ?_, ?_, ?_⟩
  · intro v d h
    simp [initialSearch, v.isLt] at h
  · intro v p h
    simp [initialSearch, v.isLt] at h
  · intro v i h
    simp [initialSearch, v.isLt] at h
  · intro i hi
    simp [initialSearch] at hi

/-- The insertion operation retains an upper bound on both lowpoints. -/
theorem insertLow_lt (N : ℕ) (pair : LowPair) (k : ℕ)
    (hlo : pair.low < N) (hhi : pair.second < N) (hk : k < N) :
    (insertLow pair k).low < N ∧ (insertLow pair k).second < N := by
  unfold insertLow
  split
  · exact ⟨hk, hlo⟩
  · split
    · exact ⟨hlo, hk⟩
    · exact ⟨hlo, hhi⟩

/-- Setting a key preserves the record bounds when the new key is bounded. -/
theorem EdgeBounded.set_key {N : ℕ} {edge : EdgeRecord} (h : EdgeBounded N edge)
    (key : ℕ) (hk : key ≤ 2 * N) : EdgeBounded N { edge with key := key } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hk⟩

/-- Setting a pair preserves endpoint and key bounds. -/
theorem EdgeBounded.set_pair {N : ℕ} {edge : EdgeRecord} (h : EdgeBounded N edge)
    (pair : LowPair) (hlo : pair.low < N) (hhi : pair.second < N) :
    EdgeBounded N { edge with pair := pair } :=
  ⟨h.1, h.2.1, hlo, hhi, h.2.2.2.2⟩

/-- Changing a valid record's key preserves all search bounds. -/
theorem SearchBounded.set_key {N : ℕ} {search : Search} (h : SearchBounded N search)
    (i key : ℕ) (hi : i < search.edges.size) (hk : key ≤ 2 * N) :
    SearchBounded N (setEdgeKey search i key) := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_, ?_⟩
  · intro v j hj
    simpa [setEdgeKey] using h.2.2.2.2.2.1 v j hj
  · intro j hj
    have hj' : j < search.edges.size := by simpa [setEdgeKey] using hj
    by_cases he : i = j
    · subst j
      simp only [setEdgeKey]
      rw [Array.getElem!_set!_self _ _ _ hi]
      exact (h.2.2.2.2.2.2 i hi).set_key key hk
    · simp only [setEdgeKey]
      rw [Array.getElem!_set!_ne search.edges i j _ he]
      exact h.2.2.2.2.2.2 j hj'

/-- Changing a valid record's lowpoint pair preserves all search bounds. -/
theorem SearchBounded.set_pair {N : ℕ} {search : Search} (h : SearchBounded N search)
    (i : ℕ) (pair : LowPair) (hi : i < search.edges.size)
    (hlo : pair.low < N) (hhi : pair.second < N) :
    SearchBounded N (setEdgePair search i pair) := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_, ?_⟩
  · intro v j hj
    simpa [setEdgePair] using h.2.2.2.2.2.1 v j hj
  · intro j hj
    have hj' : j < search.edges.size := by simpa [setEdgePair] using hj
    by_cases he : i = j
    · subst j
      simp only [setEdgePair]
      rw [Array.getElem!_set!_self _ _ _ hi]
      exact (h.2.2.2.2.2.2 i hi).set_pair pair hlo hhi
    · simp only [setEdgePair]
      rw [Array.getElem!_set!_ne search.edges i j _ he]
      exact h.2.2.2.2.2.2 j hj'

end GraphMinor.Compute.PlanarityRam
