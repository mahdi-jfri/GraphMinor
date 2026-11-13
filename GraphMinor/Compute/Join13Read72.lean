module

public import GraphMinor.Compute.Join13Adapter72Defs

/-!
# Reading the raw certificates used by (7.2)

A raw certificate first lists the mapped edge indices. Each branch set then has
one vertex bit vector and one edge bit vector. These lemmas locate the words
needed by the endpoint-and-vertex-bit encoding of the caller.
-/

public section
namespace GraphMinor.Compute

/-- Locate a word in a list of equally sized blocks. -/
theorem getD_flatMap_fixed72 {α β : Type*} (xs : List α) (f : α → List β)
    (k j i : ℕ) (d : β) (hj : j < xs.length) (hi : i < k)
    (hlen : ∀ x ∈ xs, (f x).length = k) :
    (xs.flatMap f).getD (j * k + i) d = (f xs[j]).getD i d := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    rw [List.flatMap_cons]
    cases j with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      exact List.getD_append _ _ _ _ (by rw [hlen x List.mem_cons_self]; exact hi)
    | succ j =>
      have hxlen := hlen x List.mem_cons_self
      rw [List.getD_append_right _ _ _ _ (by rw [hxlen, Nat.succ_mul]; omega), hxlen]
      have hidx : (j + 1) * k + i - k = j * k + i := by
        rw [Nat.succ_mul]; omega
      rw [hidx]
      exact ih j (by simpa using hj)
        (fun y hy => hlen y (List.mem_cons_of_mem x hy))

/-- Read the representing edge index from the raw certificate. -/
theorem getD_encRawCertEntry_edge72 {G : ComputeDigraph} {q : ℕ}
    (e : RawCertEntry G q) (d : Fin e.H.digraph.numEdges) :
    (encRawCertEntry e).getD d.1 0 = (e.edgeMap d).1 := by
  unfold encRawCertEntry
  rw [List.getD_append _ _ _ _ (by simp [d.2])]
  rw [List.getD_eq_getElem _ _ (by simp [d.2]), List.getElem_map]
  simp

/-- Read a vertex bit, skipping the edge bits of earlier branch sets. -/
theorem getD_encRawCertEntry_vertex72 {G : ComputeDigraph} {q : ℕ}
    (e : RawCertEntry G q) (u : Fin e.H.digraph.numVerts) (x : Fin G.numVerts) :
    (encRawCertEntry e).getD
        (e.H.digraph.numEdges + u.1 * (G.numVerts + G.numEdges) + x.1) 0 =
      (bitSetList (e.vertVerts u)).getD x.1 0 := by
  unfold encRawCertEntry
  rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_map, List.length_finRange]
  have hidx : e.H.digraph.numEdges + u.1 * (G.numVerts + G.numEdges) + x.1 -
      e.H.digraph.numEdges = u.1 * (G.numVerts + G.numEdges) + x.1 := by omega
  rw [hidx]
  rw [getD_flatMap_fixed72 _ _ (G.numVerts + G.numEdges) u.1 x.1 0
    (by simp [u.2]) (by omega)
    (fun _ _ => by simp [length_bitSetList])]
  simp only [List.getElem_finRange]
  rw [List.getD_append _ _ _ _ (by simp [length_bitSetList, x.2])]
  congr 2

/-- Read a vertex bit from the output model, after its two-word header and mapped
edge endpoint pairs. -/
theorem getD_encRawModel72_vertex {G : ComputeDigraph} {q : ℕ}
    (e : RawCertEntry G q) (u : Fin e.H.digraph.numVerts) (x : Fin G.numVerts) :
    (encRawModel72 e).getD
        (2 + 2 * e.H.digraph.numEdges + u.1 * G.numVerts + x.1) 0 =
      (bitSetList (e.vertVerts u)).getD x.1 0 := by
  unfold encRawModel72
  have hlen : ([e.H.digraph.numVerts, e.H.digraph.numEdges] ++
      (List.finRange e.H.digraph.numEdges).flatMap (fun d =>
        [(G.tail (e.edgeMap d)).1, (G.head (e.edgeMap d)).1])).length =
      2 + 2 * e.H.digraph.numEdges := by
    simp [List.length_flatMap, List.map_const', List.sum_replicate, Nat.mul_comm]
    omega
  rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
  have hidx : 2 + 2 * e.H.digraph.numEdges + u.1 * G.numVerts + x.1 -
      (2 + 2 * e.H.digraph.numEdges) = u.1 * G.numVerts + x.1 := by omega
  rw [hidx, getD_flatMap_fixed72 _ _ G.numVerts u.1 x.1 0
    (by simp [u.2]) x.2 (fun _ _ => length_bitSetList _)]
  simp

/-- The endpoint array is indexed by twice the edge index, followed by a bit
that selects the tail or the head. -/
@[expose] def endpointWords72 (G : ComputeDigraph) : List ℕ :=
  (List.finRange G.numEdges).flatMap (fun d => [(G.tail d).1, (G.head d).1])

/-- One pair of words is stored for each edge. -/
theorem length_endpointWords72 (G : ComputeDigraph) :
    (endpointWords72 G).length = 2 * G.numEdges := by
  simp [endpointWords72, List.length_flatMap, List.map_const', List.sum_replicate,
    Nat.mul_comm]

/-- Every endpoint is a vertex of the graph. -/
theorem mem_endpointWords72_lt (G : ComputeDigraph) {x : ℕ}
    (hx : x ∈ endpointWords72 G) : x < G.numVerts := by
  simp only [endpointWords72, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  obtain ⟨d, _, rfl | rfl⟩ := hx
  · exact (G.tail d).2
  · exact (G.head d).2

/-- A mapped endpoint is obtained by looking up the raw edge index and then
selecting one of its two endpoints. -/
theorem getD_mappedEndpointWords72 {G : ComputeDigraph} {q : ℕ}
    (e : RawCertEntry G q) (i : ℕ) (hi : i < 2 * e.H.digraph.numEdges) :
    (endpointWords72 G).getD
        (2 * (encRawCertEntry e).getD (i / 2) 0 + i % 2) 0 =
      ((List.finRange e.H.digraph.numEdges).flatMap (fun d =>
        [(G.tail (e.edgeMap d)).1, (G.head (e.edgeMap d)).1])).getD i 0 := by
  have hd : i / 2 < e.H.digraph.numEdges := by omega
  have hmod : i % 2 < 2 := Nat.mod_lt i (by decide)
  rw [getD_encRawCertEntry_edge72 e ⟨i / 2, hd⟩]
  unfold endpointWords72
  have hidx : 2 * (e.edgeMap ⟨i / 2, hd⟩).1 + i % 2 =
      (e.edgeMap ⟨i / 2, hd⟩).1 * 2 + i % 2 := by omega
  rw [hidx, getD_flatMap_fixed72 _ _ 2 _ _ 0
    (by simp [(e.edgeMap ⟨i / 2, hd⟩).2]) hmod (by intros; rfl)]
  have heq : i = i / 2 * 2 + i % 2 := by omega
  conv_rhs => rw [heq]
  rw [getD_flatMap_fixed72 _ _ 2 _ _ 0 (by simp [hd]) hmod (by intros; rfl)]
  simp

end GraphMinor.Compute
