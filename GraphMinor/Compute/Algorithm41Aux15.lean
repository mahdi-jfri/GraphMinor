module

public import GraphMinor.Compute.Algorithm41Aux14

/-!
# Chaining the Folio Computation and Model Output for GM XIII (4.1)

This file connects the bottom-up tree pass, isolated-vertex completion, and
model-output pass. Starting from the initialized working arrays, the program
writes the folio and every model to the output array. Preprocessing, array
initialization, and global word-size bounds are separate from this execution lemma.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The computation and output passes, after preprocessing and array initialization. -/
def alg41FinishProg (δ ξ ω : ℕ) : Cmd :=
  .seq (treeDPLoopProg δ ξ ω)
    (.seq (isoVertLoopProg δ ξ ω) (serialize41FinalProg δ ξ ω))

/-- The initialized DP and output passes write the certified table computed by `computeFolioDP`.
All arena bounds reserve room for both the tree and isolated-vertex passes. -/
theorem alg41FinishProg_exec {w δ ξ ω kv₀ ke₀ : ℕ} (inp : Alg41CoreInput ξ ω)
    (hw : Alg41WordBounds w δ ξ ω inp)
    (hnm : inp.G.numVerts + inp.G.numEdges < 2 ^ w)
    (hV : V_max δ ξ ω < 2 ^ w) (hC : C_max δ ξ ω < 2 ^ w)
    (hcode : 2 + Q_max ξ ω + 2 * δ < 2 ^ w)
    (hstream :
      (encFolioSetRep (computeFolioDP inp.G inp.Z δ inp.ht inp.p inp.hp inp.τ).toFolioSetRep ++
        encRawCertModels (computeFolioDP inp.G inp.Z δ inp.ht inp.p inp.hp inp.τ).toRawList).length < 2 ^ w)
    {s₀ : State} (hinv : TreeDPStateInv δ ξ ω inp s₀)
    (har : ArenaStateInv inp.G kv₀ ke₀ s₀)
    (hkv_w : kv₀ + inp.t * K_node δ ξ ω + inp.G.numVerts * K_iso δ ξ ω < 2 ^ w)
    (hke_w : ke₀ + inp.t * K_node δ ξ ω + inp.G.numVerts * K_iso δ ξ ω < 2 ^ w)
    (hkv_cap : kv₀ + inp.t * K_node δ ξ ω + inp.G.numVerts * K_iso δ ξ ω ≤ (s₀.arrs a_vkd).length)
    (hke_cap : ke₀ + inp.t * K_node δ ξ ω + inp.G.numVerts * K_iso δ ξ ω ≤ (s₀.arrs a_ekd).length) :
    let T := computeFolioDP inp.G inp.Z δ inp.ht inp.p inp.hp inp.τ
    ∃ s' t_dp t_iso t_out kv ke,
      Exec w (alg41FinishProg δ ξ ω) s₀ s' (t_dp + (t_iso + t_out)) ∧
      t_dp ≤ 10 + inp.t * (15 + C_treeNode δ ξ ω) ∧
      t_iso ≤ 5 + inp.G.numVerts * (C_isoStep δ ξ ω + 9) ∧
      kv ≤ kv₀ + inp.t * K_node δ ξ ω + inp.G.numVerts * K_iso δ ξ ω ∧
      ke ≤ ke₀ + inp.t * K_node δ ξ ω + inp.G.numVerts * K_iso δ ξ ω ∧
      t_out ≤ 3 * T_max δ ξ ω +
        (output41LengthExpr ⟨inp.Z.card, T.toRawList.map (·.H)⟩).cost + 5 +
        (encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList).length +
        7 * (encFolioSetRep T.toFolioSetRep).length +
        C_emit41Model δ ξ ω kv ke inp.G.numVerts inp.G.numEdges * T.toRawList.length ∧
      s'.arrs outArr = encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList := by
  let T := computeFolioDP inp.G inp.Z δ inp.ht inp.p inp.hp inp.τ
  rcases treeDPLoopProg_exec inp hw hinv har (by omega) (by omega) (by omega) (by omega) with
    ⟨s₁, t_dp, kv₁, ke₁, hex_dp, ht_dp, _, hkv₁, _, hke₁, hinv₁, har₁, hlenV₁, hlenE₁, hbuf₁⟩
  rcases isoVertLoopProg_exec inp hw hinv₁ har₁ (by omega) (by omega)
      (by rw [hlenV₁]; omega) (by rw [hlenE₁]; omega) hbuf₁ with
    ⟨s₂, t_iso, kv₂, ke₂, hex_iso, ht_iso, _, hkv₂, _, hke₂, hinv₂, har₂, hbuf₂⟩
  have hstream' : (enc41FolioPrefix (T.toRawList.map (·.H)) ++ encRawCertModels T.toRawList).length < 2 ^ w := by
    rw [enc41FolioPrefix_table]
    exact hstream
  rcases serialize41FinalProg_exec hbuf₂ har₂ (by have := hw.hw8; omega)
      hw.hn_w hw.hm_w hnm (by omega) (by omega) hV hw.hS_w hC hcode hw.hT_w
      hstream' hinv₂.hr0 hinv₂.hr1 with
    ⟨s₃, t_out, hex_out, ht_out, hout, _, _⟩
  rw [enc41FolioPrefix_table] at ht_out hout
  exact ⟨s₃, t_dp, t_iso, t_out, kv₂, ke₂, .seq hex_dp (.seq hex_iso hex_out),
    ht_dp, ht_iso, by omega, by omega, ht_out, hout⟩

end GraphMinor.Compute
