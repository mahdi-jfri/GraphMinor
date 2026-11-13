module

public import GraphMinor.Compute.Join13ModelTable72

/-!
# Bounds and output format for the (7.2) model table

The output drops branch-set edge bits, replaces each mapped edge by its endpoints,
and adds a length prefix. Thus each record adds at most `δ + 3` words to its raw
certificate. This gives a buffer size linear in the core output length.
-/

public section
namespace GraphMinor.Compute

/-- Every output record adds at most `δ + 3` words to a certified raw model. -/
theorem length_modelRecords72_toRaw_le {G : ComputeDigraph} {q δ : ℕ}
    {roots : Fin q → Fin G.numVerts}
    (es : List (CertFolioEntry G Finset.univ Finset.univ roots δ)) :
    (modelRecords72 (es.map CertFolioEntry.toRaw)).length ≤
      (encRawCertModels (es.map CertFolioEntry.toRaw)).length + es.length * (δ + 3) := by
  induction es with
  | nil => simp [modelRecords72, encRawCertModels]
  | cons e es ih =>
    have hraw : (encRawCertEntry e.toRaw).length =
        e.H.digraph.numEdges + e.H.digraph.numVerts * (G.numVerts + G.numEdges) := by
      simp [encRawCertEntry, CertFolioEntry.toRaw, List.length_flatMap,
        length_bitSetList, List.map_const', List.sum_replicate]
    have hmodel : (encRawModel72 e.toRaw).length =
        2 + 2 * e.H.digraph.numEdges + e.H.digraph.numVerts * G.numVerts := length_encRawModel72 _
    have hm : e.H.digraph.numEdges ≤ δ := e.hdet.1
    have hv := Nat.mul_le_mul_left e.H.digraph.numVerts
      (Nat.le_add_right G.numVerts G.numEdges)
    have hrec : (encRawModel72 e.toRaw).length + 1 ≤ (encRawCertEntry e.toRaw).length + δ + 3 := by
      rw [hraw, hmodel]
      omega
    simp only [List.map_cons, modelRecords72, encRawCertModels, List.flatMap_cons,
      List.length_append, List.length_cons, Nat.succ_mul] at ih ⊢
    omega

/-- The code headers are exactly the folio prefix after its model count. -/
theorem CertFolioTable.encFolioSetRep_eq_modelHeaders72 {G : ComputeDigraph} {q δ : ℕ}
    {roots : Fin q → Fin G.numVerts}
    (T : CertFolioTable G Finset.univ Finset.univ roots δ) :
    encFolioSetRep T.toFolioSetRep = [T.entries.length] ++ modelHeaders72 T.toRawList := by
  simp [encFolioSetRep, CertFolioTable.toFolioSetRep, modelHeaders72,
    CertFolioTable.toRawList, List.flatMap_map, CertFolioEntry.toRaw]

/-- The converted table is the modelling required by the (7.2) interface. -/
theorem CertFolioTable.encFolioModels_eq_modelRecords72 {G : ComputeDigraph} {q δ : ℕ}
    {roots : Fin q → Fin G.numVerts}
    (T : CertFolioTable G Finset.univ Finset.univ roots δ) :
    encFolioModels T.toFolioSetRep T.toFolioModels72 =
      [T.entries.length] ++ modelRecords72 T.toRawList := by
  rw [T.encFolioModels_toFolioModels72]
  simp only [modelRecords72, CertFolioTable.toRawList, List.flatMap_map,
    encRawModel72_toRaw]

/-- The number of certified entries is bounded by the length of the folio prefix. -/
theorem CertFolioTable.length_entries_le_encFolioSetRep {G : ComputeDigraph} {q δ : ℕ}
    {roots : Fin q → Fin G.numVerts}
    (T : CertFolioTable G Finset.univ Finset.univ roots δ) :
    T.entries.length ≤ (encFolioSetRep T.toFolioSetRep).length := by
  rw [T.encFolioSetRep_eq_modelHeaders72, List.length_append, List.length_singleton]
  have h := length_le_modelHeaders72 T.toRawList
  have hlen : T.toRawList.length = T.entries.length := by simp [CertFolioTable.toRawList]
  omega

/-- All words of a model fit whenever its dimensions and graph vertices fit. -/
theorem mem_encRawModel72_lt {w : ℕ} {G : ComputeDigraph} {q : ℕ}
    (e : RawCertEntry G q) (hv : e.H.digraph.numVerts < 2 ^ w)
    (hm : e.H.digraph.numEdges < 2 ^ w) (hn : G.numVerts < 2 ^ w)
    (hw : 1 < 2 ^ w) {x : ℕ} (hx : x ∈ encRawModel72 e) : x < 2 ^ w := by
  unfold encRawModel72 at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · rw [List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hm
    · rw [List.mem_flatMap] at hx
      obtain ⟨d, _, hx⟩ := hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (G.tail (e.edgeMap d)).2.trans hn
      · exact (G.head (e.edgeMap d)).2.trans hn
  · rw [List.mem_flatMap] at hx
    obtain ⟨u, _, hx⟩ := hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact (getElem_bitSetList_le_one _ _ hi).trans_lt hw

/-- A length-prefixed model table consists of words fitting the machine when
its total length and the individual model words fit. -/
theorem mem_modelRecords72_lt {w : ℕ} {G : ComputeDigraph} {q : ℕ}
    (es : List (RawCertEntry G q)) (hlen : (modelRecords72 es).length < 2 ^ w)
    (hdims : ∀ e ∈ es, e.H.digraph.numVerts < 2 ^ w ∧ e.H.digraph.numEdges < 2 ^ w)
    (hn : G.numVerts < 2 ^ w) (hw : 1 < 2 ^ w)
    {x : ℕ} (hx : x ∈ modelRecords72 es) : x < 2 ^ w := by
  induction es with
  | nil => simp [modelRecords72] at hx
  | cons e es ih =>
    have hlen' : (encRawModel72 e).length + 1 + (modelRecords72 es).length < 2 ^ w := by
      simpa only [modelRecords72, List.flatMap_cons, List.length_append, List.length_cons] using hlen
    simp only [modelRecords72, List.flatMap_cons, List.mem_append, List.mem_cons] at hx
    rcases hx with (rfl | hx) | hx
    · omega
    · exact mem_encRawModel72_lt e (hdims e List.mem_cons_self).1
        (hdims e List.mem_cons_self).2 hn hw hx
    · exact ih (by omega) (fun e' he' => hdims e' (List.mem_cons_of_mem e he')) hx

end GraphMinor.Compute
