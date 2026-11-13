module

public import GraphMinor.Compute.Algorithm41Aux19

/-!
# Linear Running Time for the Core of GM XIII (4.1)

This file combines preprocessing, allocation, the folio computation, and the
writing of all models. Every pass contributes a constant times the input size.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Fixed running-time coefficient for writing a single model. -/
def C_model41 (δ ξ ω : ℕ) : ℕ :=
  2 + 8 * V_max δ ξ ω + (84 * K_cap41 δ ξ ω + 64) * V_max δ ξ ω

/-- The model-output time is linear whenever the arenas are linear in the input size. -/
theorem C_emit41Model_le {δ ξ ω kv ke n m s : ℕ} (hs : 1 ≤ s)
    (hnm : n + m ≤ s) (hkv : kv ≤ K_cap41 δ ξ ω * s) (hke : ke ≤ K_cap41 δ ξ ω * s) :
    C_emit41Model δ ξ ω kv ke n m ≤ C_model41 δ ξ ω * s := by
  have h42v := Nat.mul_le_mul_left 42 hkv
  have h42e := Nat.mul_le_mul_left 42 hke
  have h18 := Nat.mul_le_mul_left 18 hnm
  have h46 := Nat.mul_le_mul_left 46 hs
  rw [Nat.mul_one] at h46
  have hpart : 42 * kv + 42 * ke + 18 * (n + m) + 46 ≤ (84 * K_cap41 δ ξ ω + 64) * s := by
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega
  have hpartV := Nat.mul_le_mul_right (V_max δ ξ ω) hpart
  have hbase := Nat.mul_le_mul_left (2 + 8 * V_max δ ξ ω) hs
  rw [Nat.mul_one] at hbase
  unfold C_emit41Model C_model41
  have hsum := Nat.add_le_add hbase hpartV
  simpa only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm s (V_max δ ξ ω)] using hsum

/-- Complete core program for a numbered branch-decomposition input. -/
def alg41CoreProg (δ ξ ω : ℕ) : Cmd :=
  .seq (alg41InitProg δ ξ ω) (alg41FinishProg δ ξ ω)

/-- Fixed coefficient for the total running time of the core program. -/
def C_core41 (δ ξ ω : ℕ) : ℕ :=
  (270 + 28 * (3 + K_cap41 δ ξ ω)) + 10 + 2 * (15 + C_treeNode δ ξ ω) +
    5 + (C_isoStep δ ξ ω + 9) + 3 * T_max δ ξ ω + (3 + 8 * C_max δ ξ ω) + 5 +
    8 * L_stream41 δ ξ ω + C_model41 δ ξ ω * C_max δ ξ ω

/-- The core program writes the folio and every model in linear time from the encoded input.
The logarithmic word size depends only on the fixed parameters and input size. -/
theorem alg41CoreProg_exec {δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω) {s₀ : State}
    (hinput : s₀.arrs inArr = encAlg41CoreIn inp) :
    let T := computeFolioDP inp.G inp.Z δ inp.ht inp.p inp.hp inp.τ
    ∃ s' time,
      Exec (wordSize (B_word41 δ ξ ω + 1) (alg41CoreSize inp)) (alg41CoreProg δ ξ ω) s₀ s' time ∧
      time ≤ C_core41 δ ξ ω * alg41CoreSize inp ∧
      s'.arrs outArr = encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList := by
  let s := alg41CoreSize inp
  let w := wordSize (B_word41 δ ξ ω + 1) s
  let T := computeFolioDP inp.G inp.Z δ inp.ht inp.p inp.hp inp.τ
  have hs : 1 ≤ s := by unfold s alg41CoreSize; omega
  have hglobal : B_word41 δ ξ ω * s < 2 ^ w := linear41_lt_two_pow_wordSize _ _
  obtain ⟨hw, hw3, hsz, hcap_w, hnm, hV, hC, hcode⟩ := core41_word_bounds inp hglobal
  have hstream := stream41_word_bound inp hglobal
  rcases alg41InitProg_exec inp hw3 hsz hcap_w hinput with
    ⟨s₁, t_init, hex_init, ht_init, hinv, har, hlenV, hlenE⟩
  have hreserve := (arena41Capacity_bounds δ ξ ω inp.G.numVerts inp.t).2.2.2.2.2.2
  have hreserve_w := hreserve.trans_lt hcap_w
  rcases alg41FinishProg_exec inp hw hnm hV hC hcode hstream hinv har hreserve_w hreserve_w
      (by rw [hlenV]; exact hreserve) (by rw [hlenE]; exact hreserve) with
    ⟨s₂, t_dp, t_iso, t_out, kv, ke, hex_finish, ht_dp, ht_iso, hkv, hke, ht_out, hout⟩
  have hcap_size := arena41Capacity_le_size inp δ
  have hkv_size := hkv.trans (hreserve.trans hcap_size)
  have hke_size := hke.trans (hreserve.trans hcap_size)
  have hnm_size : inp.G.numVerts + inp.G.numEdges ≤ s := by unfold s alg41CoreSize; omega
  have ht_size : inp.t ≤ 2 * s := by have := inp.ht_le; unfold s alg41CoreSize; omega
  have hn_size : inp.G.numVerts ≤ s := by unfold s alg41CoreSize; omega
  have hZ : inp.Z.card ≤ Q_max ξ ω := by have := inp.hZ; unfold Q_max; omega
  have hcount : T.toRawList.length ≤ C_max δ ξ ω := by
    have hc := T.length_entries_le
    have hC' := length_allDetailLeCodes_lt_C_max δ ξ ω hZ
    simpa only [CertFolioTable.toRawList, List.length_map] using hc.trans (Nat.le_of_lt hC')
  have hstream_size : (encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList).length ≤
      L_stream41 δ ξ ω * s := by
    have h := stream41_length_le T hZ
    simpa only [s, alg41CoreSize, Nat.add_comm inp.G.numEdges inp.G.numVerts] using h
  have hprefix_size : (encFolioSetRep T.toFolioSetRep).length ≤ L_stream41 δ ξ ω * s := by
    rw [List.length_append] at hstream_size
    omega
  have hcost : (output41LengthExpr ⟨inp.Z.card, T.toRawList.map (·.H)⟩).cost ≤ 3 + 8 * C_max δ ξ ω := by
    simp only [output41LengthExpr, Expr.cost, model41WordsExpr_cost, List.length_map]
    omega
  have hmodel := C_emit41Model_le hs hnm_size hkv_size hke_size
  have hmodel_total : C_emit41Model δ ξ ω kv ke inp.G.numVerts inp.G.numEdges * T.toRawList.length ≤
      (C_model41 δ ξ ω * C_max δ ξ ω) * s := by
    have hmul := Nat.mul_le_mul hmodel hcount
    simpa only [Nat.mul_assoc, Nat.mul_comm s (C_max δ ξ ω)] using hmul
  have hinit_cap := Nat.mul_le_mul_left 28 hcap_size
  have hdp_mul := Nat.mul_le_mul_right (15 + C_treeNode δ ξ ω) ht_size
  have hiso_mul := Nat.mul_le_mul_right (C_isoStep δ ξ ω + 9) hn_size
  have hpre_mul := Nat.mul_le_mul_left 7 hprefix_size
  have hconst := Nat.mul_le_mul_left
    (20 + 28 * 3 + 10 + 5 + 3 * T_max δ ξ ω + (3 + 8 * C_max δ ξ ω) + 5) hs
  rw [Nat.mul_one] at hconst
  refine ⟨s₂, t_init + (t_dp + (t_iso + t_out)), .seq hex_init hex_finish, ?_, hout⟩
  dsimp only [s, T] at *
  unfold C_core41
  simp only [C_isoStep, Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at ht_init hinit_cap hdp_mul hiso_mul hmodel_total hconst ht_iso ht_dp ht_out hpre_mul ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] at ht_init hinit_cap hdp_mul hiso_mul hmodel_total hconst ht_iso ht_dp ht_out hpre_mul ⊢
  omega

/-- The core computes the written folio and model stream in linear time. -/
theorem algorithm_4_1_core (δ ξ ω : ℕ) :
    ComputesArrRelInTime (alg41CoreSize (ξ := ξ) (ω := ω)) encAlg41CoreIn
      (fun x out => out = encFolioSetRep
        (computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ).toFolioSetRep ++
          encRawCertModels (computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ).toRawList)
      (alg41CoreProg δ ξ ω) (fun n => n) := by
  refine ⟨C_core41 δ ξ ω, B_word41 δ ξ ω + 1, ?_, by omega, ?_⟩
  · unfold C_core41
    omega
  · intro x s hs
    exact alg41CoreProg_exec x hs

end GraphMinor.Compute
