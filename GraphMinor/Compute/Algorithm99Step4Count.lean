module

public import GraphMinor.Compute.Algorithm99Step4

/-!
# Step (4) of Algorithm (9.9): the numbers the program computes

Step (4) of Algorithm (9.9) (Graph Minors XIII, pages 104–105) compares
`ε(K^a) + d_a + |X|` with `ε(G_i)`, where `ε(G) = |E(G)| + |V(G)| + 1` (`GM13.graphSize`) and
`d_a` is the number of edges of `G_i` with one end in `X` and the other in `V(K^a)`
(`GM13.crossEdgesToSet`). The program counts these edges in the multigraph `G_i`. This file says
which counts give the GM numbers: the edges of `K^a` are the edges of `G_i` with both ends in
`V(K^a)` (`ncard_edgeSet_wallCompass_delGraph`), and the edges counted by `d_a` are the edges of
`G_i` from `V(K^a)` to `X` or from `X` to `V(K^a)` (`ncard_crossEdgesToSet`). Both are the number
of edges of a multigraph `G.restrictMult P` that keeps the edges `(u, w)` with `P u w`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph

/-- The edges `(u, w)` of `G` with `P u w`, with their multiplicities. -/
def MultiDigraph.restrictMult {n : ℕ} (G : MultiDigraph n) (P : Fin n → Fin n → Prop)
    [DecidableRel P] : MultiDigraph n where
  edgeMult u w := if P u w then G.edgeMult u w else 0

/-- The GM edges of `G.restrictMult P` are the GM edges of `G` whose tail `u` and head `w`
satisfy `P u w`. -/
theorem MultiDigraph.mem_edgeSet_restrictMult_iff {n : ℕ} (G : MultiDigraph n)
    (P : Fin n → Fin n → Prop) [DecidableRel P] (e : ℕ × ℕ × ℕ) :
    e ∈ (G.restrictMult P).toGMDigraph.edgeSet ↔
      e ∈ G.toGMDigraph.edgeSet ∧ ∃ (hu : e.1 < n) (hw : e.2.1 < n), P ⟨e.1, hu⟩ ⟨e.2.1, hw⟩ := by
  simp only [MultiDigraph.toGMDigraph, restrictMult, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hu, hw, hk⟩
    by_cases hP : P ⟨e.1, hu⟩ ⟨e.2.1, hw⟩
    · simp only [hP, ↓reduceIte] at hk
      exact ⟨⟨hu, hw, hk⟩, hu, hw, hP⟩
    · simp only [hP, ↓reduceIte] at hk
      exact absurd hk (Nat.not_lt_zero _)
  · rintro ⟨⟨hu, hw, hk⟩, _, _, hP⟩
    exact ⟨hu, hw, by simp only [hP, ↓reduceIte]; exact hk⟩

/-- The number of GM edges of `G` whose ends satisfy `P` is `(G.restrictMult P).numEdges`. -/
theorem MultiDigraph.ncard_edgeSet_restrictMult {n : ℕ} (G : MultiDigraph n)
    (P : Fin n → Fin n → Prop) [DecidableRel P] {F : Set (ℕ × ℕ × ℕ)}
    (hF : ∀ e, e ∈ F ↔
      e ∈ G.toGMDigraph.edgeSet ∧ ∃ (hu : e.1 < n) (hw : e.2.1 < n), P ⟨e.1, hu⟩ ⟨e.2.1, hw⟩) :
    F.ncard = (G.restrictMult P).numEdges := by
  have : F = (G.restrictMult P).toGMDigraph.edgeSet := by
    ext e
    rw [hF, MultiDigraph.mem_edgeSet_restrictMult_iff]
  rw [this, MultiDigraph.ncard_edgeSet_toGMDigraph]

/-- The edges of the compass `K` of a wall in `delGraph G X = G \ X`, when `V(K)` is the bit set
`V` and `V` misses `X`, are the edges of `G` with both ends in `V`. -/
theorem ncard_edgeSet_wallCompass_delGraph {n : ℕ} (G : MultiDigraph n) (X V : Finset (Fin n))
    (W : GM13.Wall ℕ (ℕ × ℕ × ℕ)) (hV : V.toNatSet = V(GM13.wallCompass (delGraph G X) W))
    (hVX : Disjoint V X) :
    E(GM13.wallCompass (delGraph G X) W).ncard =
      (G.restrictMult (fun u w => u ∈ V ∧ w ∈ V)).numEdges := by
  apply MultiDigraph.ncard_edgeSet_restrictMult
  intro e
  have hVK : GM13.wallCompassVerts (delGraph G X) W = V.toNatSet := hV.symm
  rw [GM13.wallCompass, Graph.edgeSet_induce, hVK, delGraph_eq_deleteVertices]
  simp only [Set.mem_ofPred_eq, GM09.deleteVertices, Graph.induce_isLink]
  constructor
  · rintro ⟨x, y, ⟨⟨he, hxy⟩, -, -⟩, hx, hy⟩
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨he, ?_⟩
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- head `e.2.1 = u`, tail `e.1 = w`
      change e.2.1 = u.1 at h1
      change e.1 = w.1 at h2
      refine ⟨h2 ▸ w.2, h1 ▸ u.2, ?_, ?_⟩
      · have : (⟨e.1, h2 ▸ w.2⟩ : Fin n) = w := Fin.ext h2
        rw [this]; exact hw
      · have : (⟨e.2.1, h1 ▸ u.2⟩ : Fin n) = u := Fin.ext h1
        rw [this]; exact hu
    · change e.2.1 = w.1 at h1
      change e.1 = u.1 at h2
      refine ⟨h2 ▸ u.2, h1 ▸ w.2, ?_, ?_⟩
      · have : (⟨e.1, h2 ▸ u.2⟩ : Fin n) = u := Fin.ext h2
        rw [this]; exact hu
      · have : (⟨e.2.1, h1 ▸ w.2⟩ : Fin n) = w := Fin.ext h1
        rw [this]; exact hw
  · rintro ⟨he, hu, hw, hPu, hPw⟩
    have hmemu : e.1 ∈ V.toNatSet := ⟨⟨e.1, hu⟩, hPu, rfl⟩
    have hmemw : e.2.1 ∈ V.toNatSet := ⟨⟨e.2.1, hw⟩, hPw, rfl⟩
    have hnotX : ∀ v : Fin n, v ∈ V → v.1 ∉ X.toNatSet := fun v hv hvX =>
      Finset.disjoint_left.mp hVX hv ((mem_toNatSet_iff X v).mp hvX)
    refine ⟨e.2.1, e.1, ⟨⟨he, Or.inl ⟨rfl, rfl⟩⟩, ⟨G.toGMDigraph.head_mem he, ?_⟩,
      ⟨G.toGMDigraph.tail_mem he, ?_⟩⟩, hmemw, hmemu⟩
    · exact hnotX ⟨e.2.1, hw⟩ hPw
    · exact hnotX ⟨e.1, hu⟩ hPu

/-- The edges counted by `d_a` in step (4) of (9.9): the edges of `G_i` with one end in the bit
set `V` and the other in `X` are the edges of `G` from `V` to `X` or from `X` to `V`. -/
theorem ncard_crossEdgesToSet {n : ℕ} (G : MultiDigraph n) (X V : Finset (Fin n)) :
    (GM13.crossEdgesToSet G.toGMDigraph.toGraph V.toNatSet X.toNatSet).ncard =
      (G.restrictMult (fun u w => (u ∈ V ∧ w ∈ X) ∨ (u ∈ X ∧ w ∈ V))).numEdges := by
  apply MultiDigraph.ncard_edgeSet_restrictMult
  intro e
  unfold GM13.crossEdgesToSet
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨he, x, ⟨u, hu, rfl⟩, y, ⟨w, hw, rfl⟩, -, hxy⟩
    refine ⟨he, ?_⟩
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · change e.2.1 = u.1 at h1
      change e.1 = w.1 at h2
      have h1' : (⟨e.2.1, h1 ▸ u.2⟩ : Fin n) = u := Fin.ext h1
      have h2' : (⟨e.1, h2 ▸ w.2⟩ : Fin n) = w := Fin.ext h2
      refine ⟨h2 ▸ w.2, h1 ▸ u.2, Or.inr ⟨?_, ?_⟩⟩
      · rw [h2']; exact hw
      · rw [h1']; exact hu
    · change e.2.1 = w.1 at h1
      change e.1 = u.1 at h2
      have h1' : (⟨e.2.1, h1 ▸ w.2⟩ : Fin n) = w := Fin.ext h1
      have h2' : (⟨e.1, h2 ▸ u.2⟩ : Fin n) = u := Fin.ext h2
      refine ⟨h2 ▸ u.2, h1 ▸ w.2, Or.inl ⟨?_, ?_⟩⟩
      · rw [h2']; exact hu
      · rw [h1']; exact hw
  · rintro ⟨he, hu, hw, hP | hP⟩
    · exact ⟨he, e.1, ⟨⟨e.1, hu⟩, hP.1, rfl⟩, e.2.1, ⟨⟨e.2.1, hw⟩, hP.2, rfl⟩, he,
        Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨he, e.2.1, ⟨⟨e.2.1, hw⟩, hP.2, rfl⟩, e.1, ⟨⟨e.1, hu⟩, hP.1, rfl⟩, he,
        Or.inl ⟨rfl, rfl⟩⟩

/-- `ε(G_i) = |E(G_i)| + n + 1` for the GM graph of a multigraph on `Fin n`. -/
theorem graphSize_toGMDigraph {n : ℕ} (G : MultiDigraph n) :
    GM13.graphSize G.toGMDigraph.toGraph = G.numEdges + n + 1 := by
  unfold GM13.graphSize
  rw [show E(G.toGMDigraph.toGraph) = G.toGMDigraph.edgeSet from rfl,
    show V(G.toGMDigraph.toGraph) = G.toGMDigraph.vertexSet from rfl,
    MultiDigraph.ncard_edgeSet_toGMDigraph, MultiDigraph.ncard_vertexSet_toGMDigraph]

/-- `ε(K)` for the compass `K` of a wall in `G \ X` with vertex bit set `V` missing `X`. -/
theorem graphSize_wallCompass_delGraph {n : ℕ} (G : MultiDigraph n) (X V : Finset (Fin n))
    (W : GM13.Wall ℕ (ℕ × ℕ × ℕ)) (hV : V.toNatSet = V(GM13.wallCompass (delGraph G X) W))
    (hVX : Disjoint V X) :
    GM13.graphSize (GM13.wallCompass (delGraph G X) W) =
      (G.restrictMult (fun u w => u ∈ V ∧ w ∈ V)).numEdges + V.card + 1 := by
  unfold GM13.graphSize
  rw [ncard_edgeSet_wallCompass_delGraph G X V W hV hVX, ← hV, ncard_toNatSet]

end GraphMinor.Compute
