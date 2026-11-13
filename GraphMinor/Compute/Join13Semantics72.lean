module

public import GraphMinor.Compute.Join13Internal72
public import GraphMinor.Compute.Join441

/-!
# The empty-root adapter's mathematical output

The core uses the empty root set, while the caller uses the empty root list.
Their root maps agree because their domain is empty. Transporting the certified
models along this equality preserves their serialization.
-/

public section
namespace GraphMinor.Compute

private theorem encFolioModels_castTarget72 {q δ : ℕ} (F : FolioSetRep q δ)
    {G G' : ComputeRootedDigraph q} (h : G = G')
    (models : ∀ i : Fin F.codes.length, RootedDigraphModel (F.decodedAt i) G) :
    encFolioModels F (fun i => h ▸ models i) = encFolioModels F models := by
  subst G'
  rfl

/-- The core's empty-set roots agree with the caller's empty-list roots. -/
theorem multiCoreInput72_rooted_eq {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) :
    let x := multiCoreInput72 G bdCode hbd
    withRoots x.G (finsetRootFn x.Z) = G.toMultiComputeRootedDigraph [] := by
  apply congrArg (fun r : Fin 0 → Fin n => withRoots G.toMultiComputeDigraph r)
  exact Subsingleton.elim _ _

/-- Certified core models give the caller's models with identical words and
with the same folio membership property. -/
theorem coreModels72_for_caller {n B δ : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) :
    let x := multiCoreInput72 G bdCode hbd
    let T := computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ
    ∃ models : ∀ i : Fin T.toFolioSetRep.codes.length,
        RootedDigraphModel (T.toFolioSetRep.decodedAt i) (G.toMultiComputeRootedDigraph []),
      encFolioModels T.toFolioSetRep models = encFolioModels T.toFolioSetRep T.toFolioModels72 ∧
      ∀ H : ComputeRootedDigraph 0, H.HasDetailLe δ →
        (T.toFolioSetRep.MemIso H ↔ HasRootedDigraphModel H (G.toMultiComputeRootedDigraph [])) := by
  let x := multiCoreInput72 G bdCode hbd
  let T := computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ
  have htarget := multiCoreInput72_rooted_eq G bdCode hbd
  refine ⟨fun i => htarget ▸ T.toFolioModels72 i, encFolioModels_castTarget72 _ htarget _, ?_⟩
  intro H hH
  rw [← htarget]
  exact T.memIso_toFolioModels72_iff H hH

end GraphMinor.Compute
