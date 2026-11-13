module

public import GraphMinor.Compute.Join13Adapter101

/-!
# Model certificates for the (7.2) call to (4.1)

The call in (4.4), used by (7.2), writes the folio and its models in separate
arrays. Its model encoding gives edge endpoints and vertex bit sets. We relate
that encoding to the certified entries returned by the core (4.1) program.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Models for the representatives in a certified folio table, using the decoder
required by the (7.2) subroutine interface. -/
def CertFolioTable.toFolioModels72 {G : ComputeDigraph} {q δ : ℕ}
    {roots : Fin q → Fin G.numVerts}
    (T : CertFolioTable G Finset.univ Finset.univ roots δ)
    (i : Fin T.toFolioSetRep.codes.length) :
    RootedDigraphModel (T.toFolioSetRep.decodedAt i) (withRoots G roots) :=
  have hi : i.1 < T.entries.length := by simpa [CertFolioTable.toFolioSetRep] using i.2
  have heq : T.toFolioSetRep.decodedAt i = (T.entries[i.1]'hi).H :=
    T.toFolioSetRep.decodedAt_eq_of_eq_encRootedDigraph i (T.entries[i.1]'hi).H
      (by simp [CertFolioTable.toFolioSetRep])
  heq.symm ▸ (T.entries[i.1]'hi).model.toRootedDigraphModel

private theorem encRootedDigraphModel_cast {q : ℕ} {H H' G : ComputeRootedDigraph q}
    (h : H = H') (M : RootedDigraphModel H G) :
    encRootedDigraphModel (h ▸ M) = encRootedDigraphModel M := by
  subst h
  rfl

/-- The models of a certified table are serialized in the order of its entries. -/
theorem CertFolioTable.encFolioModels_toFolioModels72 {G : ComputeDigraph} {q δ : ℕ}
    {roots : Fin q → Fin G.numVerts}
    (T : CertFolioTable G Finset.univ Finset.univ roots δ) :
    encFolioModels T.toFolioSetRep T.toFolioModels72 =
      [T.entries.length] ++ T.entries.flatMap (fun e =>
        let words := encRootedDigraphModel e.model.toRootedDigraphModel
        words.length :: words) := by
  unfold encFolioModels
  simp only [CertFolioTable.toFolioSetRep, List.length_map]
  congr 1
  have hblocks :
      (List.finRange T.toFolioSetRep.codes.length).map (fun i =>
        let words := encRootedDigraphModel (T.toFolioModels72 i)
        words.length :: words) =
      T.entries.map (fun e =>
        let words := encRootedDigraphModel e.model.toRootedDigraphModel
        words.length :: words) := by
    rw [← List.ofFn_eq_map]
    apply List.ext_getElem (by simp [CertFolioTable.toFolioSetRep])
    intro i hi hj
    rw [List.getElem_ofFn, List.getElem_map]
    simp only [CertFolioTable.toFolioModels72, encRootedDigraphModel_cast]
  simpa only [← List.flatMap_def, CertFolioTable.toFolioSetRep] using congrArg List.flatten hblocks

/-- The folio and models extracted from a certified table have the same
representatives as the core computation. -/
theorem CertFolioTable.memIso_toFolioModels72_iff {G : ComputeDigraph} {q δ : ℕ}
    {roots : Fin q → Fin G.numVerts}
    (T : CertFolioTable G Finset.univ Finset.univ roots δ)
    (H : ComputeRootedDigraph q) (hH : H.HasDetailLe δ) :
    T.toFolioSetRep.MemIso H ↔ HasRootedDigraphModel H (withRoots G roots) := by
  rw [T.memIso_toFolioSetRep_iff hH, hasPieceRootedModel_univ_iff]

/-- A raw certificate written in the endpoint-and-bit-set format of (7.2). -/
def encRawModel72 {G : ComputeDigraph} {q : ℕ} (e : RawCertEntry G q) : List ℕ :=
  [e.H.digraph.numVerts, e.H.digraph.numEdges] ++
  (List.finRange e.H.digraph.numEdges).flatMap (fun d =>
    [(G.tail (e.edgeMap d)).1, (G.head (e.edgeMap d)).1]) ++
  (List.finRange e.H.digraph.numVerts).flatMap (fun u => bitSetList (e.vertVerts u))

/-- Erasing a certificate's proofs does not change its model encoding. -/
theorem encRawModel72_toRaw {G : ComputeDigraph} {q δ : ℕ}
    {roots : Fin q → Fin G.numVerts}
    (e : CertFolioEntry G Finset.univ Finset.univ roots δ) :
    encRawModel72 e.toRaw = encRootedDigraphModel e.model.toRootedDigraphModel := by
  rfl

/-- The output length counts two words per mapped edge and one bit per vertex
of each branch set. -/
theorem length_encRawModel72 {G : ComputeDigraph} {q : ℕ} (e : RawCertEntry G q) :
    (encRawModel72 e).length =
      2 + 2 * e.H.digraph.numEdges + e.H.digraph.numVerts * G.numVerts := by
  unfold encRawModel72
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_flatMap]
  simp [length_bitSetList, List.map_const', List.sum_replicate, Nat.mul_comm]

/-- Converting a certificate adds at most a fixed number of words per model. -/
theorem length_encRawModel72_toRaw_le {n q δ : ℕ} {G : MultiDigraph n}
    {roots : Fin q → Fin G.toComputeDigraph.numVerts}
    (e : CertFolioEntry G.toComputeDigraph Finset.univ Finset.univ roots δ) :
    (encRawModel72 e.toRaw).length ≤ (encRawCertEntry e.toRaw).length + δ + 2 := by
  rw [length_encRawModel72, length_rawCertEntry_toRaw]
  have hm : e.H.digraph.numEdges ≤ δ := e.hdet.1
  have hv := Nat.mul_le_mul_left e.H.digraph.numVerts
    (Nat.le_add_right G.toComputeDigraph.numVerts G.toComputeDigraph.numEdges)
  change 2 + 2 * e.H.digraph.numEdges +
    e.H.digraph.numVerts * G.toComputeDigraph.numVerts ≤ _
  omega

end GraphMinor.Compute
