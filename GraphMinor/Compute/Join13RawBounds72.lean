module

public import GraphMinor.Compute.Join13Output72

/-!
# Linear bounds for the core certificate stream

There are only finitely many representative graphs at fixed detail and root
bound. Each raw model uses at most one edge index per representative edge and
one vertex and edge bitset per representative vertex. This gives a linear
bound in the size of the input graph.
-/

public section
namespace GraphMinor.Compute

/-- Bound the raw certificates for a list of certified representatives. -/
theorem length_rawModels72_le {q δ : ℕ} {G : ComputeDigraph}
    {roots : Fin q → Fin G.numVerts}
    (es : List (CertFolioEntry G Finset.univ Finset.univ roots δ)) :
    (encRawCertModels (es.map CertFolioEntry.toRaw)).length ≤
      es.length * ((q + δ) * (G.numVerts + G.numEdges) + δ) := by
  induction es with
  | nil => simp [encRawCertModels]
  | cons e es ih =>
    have hraw : (encRawCertEntry e.toRaw).length =
        e.H.digraph.numEdges + e.H.digraph.numVerts * (G.numVerts + G.numEdges) := by
      simp [encRawCertEntry, CertFolioEntry.toRaw, List.length_flatMap,
        length_bitSetList, List.map_const', List.sum_replicate]
    unfold encRawCertModels at ih ⊢
    rw [List.map_cons, List.flatMap_cons, List.length_append, hraw,
      List.length_cons, Nat.succ_mul]
    have hv := e.H.numVerts_le_of_hasDetailLe e.hdet
    have hm := e.hdet.1
    have hmul := Nat.mul_le_mul_right (G.numVerts + G.numEdges) hv
    omega

/-- The entire certificate stream has linear length, with a constant depending
only on the detail and root bound. -/
theorem length_coreOutput72_le {q δ : ℕ} {G : ComputeDigraph}
    {roots : Fin q → Fin G.numVerts}
    (T : CertFolioTable G Finset.univ Finset.univ roots δ) :
    (encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList).length ≤
      (maxEncFolioSetRepLen q δ * (q + 2 * δ + 1)) * (G.numVerts + G.numEdges + 1) := by
  have hF := length_encFolioSetRep_le_max (le_refl q) T.toFolioSetRep
  have he := T.length_entries_le_encFolioSetRep.trans hF
  have hraw := length_rawModels72_le T.entries
  change (encRawCertModels T.toRawList).length ≤
    T.entries.length * ((q + δ) * (G.numVerts + G.numEdges) + δ) at hraw
  have hmul := Nat.mul_le_mul_right ((q + δ) * (G.numVerts + G.numEdges) + δ) he
  rw [List.length_append]
  calc
    _ ≤ maxEncFolioSetRepLen q δ + maxEncFolioSetRepLen q δ *
        ((q + δ) * (G.numVerts + G.numEdges) + δ) := by omega
    _ ≤ (maxEncFolioSetRepLen q δ * (q + 2 * δ + 1)) *
        (G.numVerts + G.numEdges + 1) := by
      have hle : (q + δ) * (G.numVerts + G.numEdges) + δ + 1 ≤
          (q + 2 * δ + 1) * (G.numVerts + G.numEdges + 1) := by
        have hh := Nat.mul_le_mul_right (G.numVerts + G.numEdges)
          (show q + δ ≤ q + 2 * δ + 1 by omega)
        simp only [Nat.mul_add, Nat.mul_one] at hh ⊢
        omega
      have hh := Nat.mul_le_mul_left (maxEncFolioSetRepLen q δ) hle
      convert hh using 1 <;> ring

/-- The model table fits the raw stream plus the fixed extra capacity. -/
theorem length_models72_le {q δ : ℕ} {G : ComputeDigraph}
    {roots : Fin q → Fin G.numVerts}
    (T : CertFolioTable G Finset.univ Finset.univ roots δ) :
    (encFolioModels T.toFolioSetRep T.toFolioModels72).length ≤
      (encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList).length + modelExtra72 q δ := by
  have h := length_modelRecords72_toRaw_le T.entries
  have hc := T.length_entries_le_encFolioSetRep.trans
    (length_encFolioSetRep_le_max (le_refl q) T.toFolioSetRep)
  have hm := Nat.mul_le_mul_right (δ + 3) hc
  rw [T.encFolioModels_eq_modelRecords72]
  simp only [List.length_cons, List.length_append]
  change (modelRecords72 T.toRawList).length ≤
    (encRawCertModels T.toRawList).length + T.entries.length * (δ + 3) at h
  dsimp [modelExtra72]
  omega

/-- Model-table words fit when its total length and model dimensions fit. -/
theorem words_models72_lt {w q δ : ℕ} {G : ComputeDigraph}
    {roots : Fin q → Fin G.numVerts}
    (T : CertFolioTable G Finset.univ Finset.univ roots δ)
    (hlen : (encFolioModels T.toFolioSetRep T.toFolioModels72).length < 2 ^ w)
    (hqd : q + δ < 2 ^ w) (hn : G.numVerts < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∀ a ∈ encFolioModels T.toFolioSetRep T.toFolioModels72, a < 2 ^ w := by
  rw [T.encFolioModels_eq_modelRecords72] at hlen ⊢
  simp only [List.singleton_append] at hlen ⊢
  simp only [List.length_cons] at hlen
  intro a ha
  rcases List.mem_cons.1 ha with rfl | ha
  · have hc := T.length_entries_le_encFolioSetRep
    have hl := length_le_modelHeaders72 T.toRawList
    have he : T.toRawList.length = T.entries.length := by simp [CertFolioTable.toRawList]
    have hm : T.toRawList.length ≤ (modelRecords72 T.toRawList).length := by
      unfold modelRecords72
      induction T.toRawList with
      | nil => simp
      | cons e es ih => simp only [List.length_cons, List.flatMap_cons, List.length_append] at *; omega
    omega
  · apply mem_modelRecords72_lt T.toRawList (by omega) ?_ hn hw ha
    intro e he
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 he
    exact ⟨(e.H.numVerts_le_of_hasDetailLe e.hdet).trans_lt hqd,
      e.hdet.1.trans_lt (by omega)⟩

end GraphMinor.Compute
