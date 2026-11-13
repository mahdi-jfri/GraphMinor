module

public import GraphMinor.Compute.Join13Output72
public import GraphMinor.Compute.Join13Prefix72

/-!
# Writing both outputs of the (7.2) core call

The model converter uses the saved graph sizes and endpoint stream. Once its
model table is written, a scan copies the folio prefix into the other output
array. Both outputs therefore come from the same certified table.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Convert raw certificates and copy the matching folio prefix. -/
def finishCore72Prog (q δ : ℕ) : Cmd :=
  .seq (.assign 114 (.reg 26))
    (.seq (.assign 115 (.reg 28))
      (.seq (outputModels72Prog q δ 201 40 50 16 110)
        (copyFolioPrefix72Prog 201 15 140)))

/-- The two output arrays encode the same certified folio table. -/
theorem finishCore72Prog_exec {w q δ : ℕ} {G : ComputeDigraph}
    {roots : Fin q → Fin G.numVerts}
    (T : CertFolioTable G Finset.univ Finset.univ roots δ) (s : State)
    (hw : 2 < 2 ^ w) (hn : G.numVerts + G.numEdges < 2 ^ w)
    (hm : 2 * G.numEdges < 2 ^ w) (hqd : q + δ < 2 ^ w)
    (hcap : (s.arrs 201).length + modelExtra72 q δ < 2 ^ w)
    (hwords : ∀ x ∈ encFolioSetRep T.toFolioSetRep, x < 2 ^ w)
    (hsrc : s.arrs 201 = encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList)
    (hends : s.arrs 40 = endpointWords72 G)
    (hrn : s.regs 26 = G.numVerts) (hrm : s.regs 28 = G.numEdges) :
    ∃ s' t, Exec w (finishCore72Prog q δ) s s' t ∧
      t ≤ 300 * ((s.arrs 201).length + modelExtra72 q δ + maxEncFolioSetRepLen q δ + 1) ∧
      s'.arrs 15 = encFolioSetRep T.toFolioSetRep ∧
      s'.arrs 16 = encFolioModels T.toFolioSetRep T.toFolioModels72 := by
  let s₁ := s.setReg 114 G.numVerts
  have he₁ : Exec w (.assign 114 (.reg 26)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrn, show G.numVerts < 2 ^ w by omega])
  let s₂ := s₁.setReg 115 G.numEdges
  have he₂ : Exec w (.assign 115 (.reg 28)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hrm, show G.numEdges < 2 ^ w by omega])
  obtain ⟨s₃, t₃, he₃, ht₃, ho₃, hlen₃⟩ :=
    outputModels72Prog_exec T 201 40 50 16 110 (by decide) (by decide) (by decide)
      s₂ hw hn hm hqd hcap hsrc hends (by simp [s₂, s₁]) (by simp [s₂])
  have ha₃ : s₃.arrs 201 = s.arrs 201 :=
    he₃.arrs_eq_of_not_mem_writtenArrs (by
      intro h
      have := outputModels72Prog_writtenArrs_subset q δ 201 40 50 16 110 h
      simp at this)
  have hcount : T.toFolioSetRep.codes.length ≤ (encFolioSetRep T.toFolioSetRep).length := by
    simpa [CertFolioTable.toFolioSetRep] using T.length_entries_le_encFolioSetRep
  have hlenF : (encFolioSetRep T.toFolioSetRep).length ≤ (s.arrs 201).length := by
    rw [hsrc, List.length_append]; omega
  have hFmax := length_encFolioSetRep_le_max (le_refl q) T.toFolioSetRep
  obtain ⟨s₄, t₄, he₄, ht₄, ho₄⟩ :=
    copyFolioPrefix72Prog_exec T.toFolioSetRep (encRawCertModels T.toRawList)
      201 15 140 (by decide) s₃ (by omega) (by omega)
      (by rw [← hsrc]; omega) hwords (ha₃.trans hsrc)
  refine ⟨s₄, 2 + (2 + (t₃ + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_, ho₄, ?_⟩
  · change t₃ ≤ 200 * ((s.arrs 201).length + modelExtra72 q δ + maxEncFolioSetRepLen q δ + 1) at ht₃
    omega
  · rw [he₄.arrs_eq_of_not_mem_writtenArrs (by rw [copyFolioPrefix72Prog_writtenArrs]; decide)]
    exact ho₃

end GraphMinor.Compute
