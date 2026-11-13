module

public import GraphMinor.Compute.Algorithm41InputBridge

/-!
# Meaning of the Written Folio and Model Data in GM XIII (4.1)

The output reader returns only words, rooted digraphs, and sets read from bit
lists. Validity means that these data are the folio and models of a certified
table. The proofs below recover mathematical certificates from that validity
proof, without adding any computation to the output reader.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The data of a certified table, with its model proofs erased. -/
def CertFolioTable.readOutput {q δ : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)} {r : Fin q → Fin G.numVerts}
    (T : CertFolioTable G VA EA r δ) : Alg41DecodedOutput G q where
  folioCodes := T.toFolioSetRep.codes
  entries := T.entries.map (fun e =>
    { code := encRootedDigraph e.H
      H := e.H
      edgeIdx := fun d => (e.model.edgeMap d).1
      vertVerts := fun u => (e.model.vertMap u).verts
      vertEdges := fun u => (e.model.vertMap u).edges })

/-- The pure reader recovers exactly the written model data. -/
theorem CertFolioTable.readOutput_encode {q δ : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)} {r : Fin q → Fin G.numVerts}
    (T : CertFolioTable G VA EA r δ) :
    decAlg41OutWords G q (encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList) = T.readOutput := by
  simpa only [List.append_nil, CertFolioTable.readOutput] using decAlg41OutWords_encode T []

/-- The read data describe a complete folio and a written model for every member. -/
def IsValidAlg41ReadOutput (δ : ℕ) {ξ ω : ℕ} (x : Alg41Input ξ ω)
    (out : Alg41DecodedOutput x.G x.Z.card) : Prop :=
  ∃ T : CertFolioTable x.G Finset.univ Finset.univ (finsetRootFn x.Z) δ, out = T.readOutput

/-- The same validity condition for a serialized branch-decomposition input. -/
def IsValidAlg41ReadCodeOutput (δ : ℕ) {ξ ω : ℕ} (x : Alg41CodeInput ξ ω)
    (out : Alg41DecodedOutput x.G.toComputeDigraph x.Z.card) : Prop :=
  ∃ T : CertFolioTable x.G.toComputeDigraph Finset.univ Finset.univ (finsetRootFn x.Z) δ,
    out = T.readOutput

/-- A validity proof supplies the table whose data were written. -/
noncomputable def IsValidAlg41ReadOutput.table {δ ξ ω : ℕ} {x : Alg41Input ξ ω}
    {out : Alg41DecodedOutput x.G x.Z.card} (h : IsValidAlg41ReadOutput δ x out) :
    CertFolioTable x.G Finset.univ Finset.univ (finsetRootFn x.Z) δ := h.choose

/-- The read data agree with the table obtained from validity. -/
theorem IsValidAlg41ReadOutput.eq_readOutput {δ ξ ω : ℕ} {x : Alg41Input ξ ω}
    {out : Alg41DecodedOutput x.G x.Z.card} (h : IsValidAlg41ReadOutput δ x out) : out = h.table.readOutput :=
  h.choose_spec

/-- The model certificates represented by a valid read output. -/
theorem IsValidAlg41ReadOutput.certifiedValidity {δ ξ ω : ℕ} {x : Alg41Input ξ ω}
    {out : Alg41DecodedOutput x.G x.Z.card} (h : IsValidAlg41ReadOutput δ x out) :
    IsValidAlg41Output δ x (certTableToAlg41Output x h.table) :=
  isValidAlg41Output_certTableToAlg41Output x δ h.table

/-- Extract the folio represented by the valid read output. -/
noncomputable def IsValidAlg41ReadOutput.toFolioSetRep {δ ξ ω : ℕ} {x : Alg41Input ξ ω}
    {out : Alg41DecodedOutput x.G x.Z.card} (h : IsValidAlg41ReadOutput δ x out) :
    FolioSetRep x.Z.card δ := h.certifiedValidity.toFolioSetRep

/-- The extracted folio has the meaning of GM XIII's folio relative to the input roots. -/
theorem IsValidAlg41ReadOutput.isDeltaFolioRep {n δ ξ ω : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (hZ : Z.card ≤ ξ) {t : ℕ} (ht : 0 < t) {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) {τ : Fin G.toComputeDigraph.numEdges → Fin t}
    (hbd : IsDigraphBranchDecompOfWidthLe ω G.toComputeDigraph (parentTree t p) τ)
    {out : Alg41DecodedOutput G.toComputeDigraph Z.card}
    (h : IsValidAlg41ReadOutput δ (⟨G.toComputeDigraph, Z, hZ, t, ht, p, hp, τ, hbd⟩ : Alg41Input ξ ω) out) :
    IsDeltaFolioRep δ G Z h.toFolioSetRep :=
  h.certifiedValidity.isDeltaFolioRep G Z hZ ht hp hbd

/-- A validity proof for code input supplies its mathematical table. -/
noncomputable def IsValidAlg41ReadCodeOutput.table {δ ξ ω : ℕ} {x : Alg41CodeInput ξ ω}
    {out : Alg41DecodedOutput x.G.toComputeDigraph x.Z.card} (h : IsValidAlg41ReadCodeOutput δ x out) :
    CertFolioTable x.G.toComputeDigraph Finset.univ Finset.univ (finsetRootFn x.Z) δ := h.choose

/-- The model certificates represented by a valid code-input read output. -/
theorem IsValidAlg41ReadCodeOutput.certifiedValidity {δ ξ ω : ℕ} {x : Alg41CodeInput ξ ω}
    {out : Alg41DecodedOutput x.G.toComputeDigraph x.Z.card} (h : IsValidAlg41ReadCodeOutput δ x out) :
    IsValidAlg41CodeOutput δ x (certTableToAlg41CodeOutput x h.table) :=
  isValidAlg41CodeOutput_certTableToAlg41CodeOutput x δ h.table

/-- Extract the folio represented by a valid code-input read output. -/
noncomputable def IsValidAlg41ReadCodeOutput.toFolioSetRep {δ ξ ω : ℕ} {x : Alg41CodeInput ξ ω}
    {out : Alg41DecodedOutput x.G.toComputeDigraph x.Z.card} (h : IsValidAlg41ReadCodeOutput δ x out) :
    FolioSetRep x.Z.card δ := h.certifiedValidity.toFolioSetRep

/-- The extracted code-input folio is the input graph's delta-folio. -/
theorem IsValidAlg41ReadCodeOutput.isDeltaFolioRep {δ ξ ω : ℕ} {x : Alg41CodeInput ξ ω}
    {out : Alg41DecodedOutput x.G.toComputeDigraph x.Z.card} (h : IsValidAlg41ReadCodeOutput δ x out) :
    IsDeltaFolioRep δ x.G x.Z h.toFolioSetRep := h.certifiedValidity.isDeltaFolioRep

end GraphMinor.Compute
