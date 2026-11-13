module

public import GraphMinor.Compute.Join13ModelConversion

/-!
# The (4.1) adapter for (10.1)

The wrapper saves graph sizes, packs the input, runs the core program, and converts its output.
-/

@[expose] public section
namespace GraphMinor.Compute
open SimpleGraph Classical

theorem length_encRawCertModels_le {n δ q : ℕ} {G : MultiDigraph n}
    {r_fn : Fin q → Fin G.toComputeDigraph.numVerts}
    (es : List (CertFolioEntry G.toComputeDigraph Finset.univ Finset.univ r_fn δ)) :
    (encRawCertModels (es.map CertFolioEntry.toRaw)).length ≤
      es.length * ((q + δ) * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges) + δ) := by
  induction es with
  | nil => simp [encRawCertModels]
  | cons e es ih =>
    unfold encRawCertModels at ih ⊢
    rw [List.map_cons, List.flatMap_cons, List.length_append, length_rawCertEntry_toRaw,
      List.length_cons, Nat.succ_mul]
    have hv_le : e.H.digraph.numVerts ≤ q + δ := e.H.numVerts_le_of_hasDetailLe e.hdet
    have hm_le : e.H.digraph.numEdges ≤ δ := e.hdet.1
    have hmul := Nat.mul_le_mul_right (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges) hv_le
    omega

theorem words_encFolioSetRep_append_raw_le {n δ : ℕ} {G : MultiDigraph n} {Z : Finset (Fin n)}
    (T : CertFolioTable G.toComputeDigraph Finset.univ Finset.univ (finsetRootFn Z) δ)
    {u : ℕ} (hu : u ∈ encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList) :
    u ≤ (encFolioSetRep T.toFolioSetRep).length + Z.card + 2 * δ + G.numEdges + 2 := by
  have hm_eq : G.toComputeDigraph.numEdges = G.numEdges := G.length_directedEdgesList
  rw [List.mem_append] at hu
  rcases hu with huF | huR
  · have hlen_codes : T.entries.length ≤ (encFolioSetRep T.toFolioSetRep).length := by
      unfold encFolioSetRep CertFolioTable.toFolioSetRep
      simp only [List.length_append, List.length_singleton]
      have h : ∀ cs : List (List ℕ), cs.length ≤
          (cs.flatMap (fun c => c.length :: c)).length := by
        intro cs
        induction cs with
        | nil => simp
        | cons c cs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega
      have hh := h (T.entries.map (fun e => encRootedDigraph e.H))
      simp only [List.length_map] at hh
      omega
    unfold encFolioSetRep CertFolioTable.toFolioSetRep at huF
    rw [List.singleton_append, List.mem_cons, List.mem_flatMap] at huF
    rcases huF with rfl | ⟨c, hc_mem, huc⟩
    · rw [List.length_map]
      exact le_trans hlen_codes (by omega)
    · rw [List.mem_map] at hc_mem
      rcases hc_mem with ⟨e, _, rfl⟩
      rw [List.mem_cons] at huc
      rcases huc with rfl | huc
      · have hlen := length_encRootedDigraph_le_of_hasDetailLe e.hdet
        omega
      · have hw := mem_encRootedDigraph_le_of_hasDetailLe e.hdet huc
        omega
  · unfold encRawCertModels CertFolioTable.toRawList at huR
    rw [List.mem_flatMap] at huR
    rcases huR with ⟨raw_e, hraw_e, hu_e⟩
    rw [List.mem_map] at hraw_e
    rcases hraw_e with ⟨e, _, rfl⟩
    unfold encRawCertEntry CertFolioEntry.toRaw at hu_e
    rw [List.mem_append] at hu_e
    rcases hu_e with hu_edge | hu_vert
    · rw [List.mem_map] at hu_edge
      rcases hu_edge with ⟨e', _, rfl⟩
      have hlt := (e.model.edgeMap e').2
      omega
    · rw [List.mem_flatMap] at hu_vert
      rcases hu_vert with ⟨p, hp_mem, hu_p⟩
      rw [List.mem_append] at hu_p
      dsimp only at hu_p
      rcases hu_p with huv | hue
      · rcases List.getElem_of_mem huv with ⟨i, hi, rfl⟩
        have := getElem_bitSetList_le_one (e.model.vertMap p).verts i hi
        omega
      · rcases List.getElem_of_mem hue with ⟨i, hi, rfl⟩
        have := getElem_bitSetList_le_one (e.model.vertMap p).edges i hi
        omega

set_option maxHeartbeats 200000 in
/-- **Adapter 2 (`Claim41 → Alg41Spec101`):**
The core claim `Claim41` for GM XIII Algorithm (4.1) implies `Alg41Spec101 p ξ δ B`, the form of
(4.1) that `Algorithm101Defs.lean` uses for GM XIII (10.1). -/
theorem alg41Spec101_of_claim41 (h41 : Claim41) (p ξ δ B : ℕ) :
    Alg41Spec101 p ξ δ B := by
  let b := alg105ArrBase p
  rcases h41 δ ξ B with ⟨P, C_P, c_P, hC_P, hc_P, hP⟩
  let r_save : Reg := P.writtenRegs.sup id + 70
  let r_base : Reg := r_save + 2
  let a_dst : Arr := P.writtenArrs.sup id + b + 20
  let prog : Cmd :=
    .seq (.assign r_save (.reg 26))
    (.seq (.assign (r_save + 1) (.reg 28))
    (.seq (normalizeBD41Prog b)
    (.seq (packAlg41InProg b)
    (.seq P
          (convertRawOutTo101Prog ξ δ a_dst r_save r_base)))))
  let C_raw := maxEncFolioSetRepLen ξ δ * (ξ + δ + δ + 2)
  let C_conv := maxEncFolioSetRepLen ξ δ * ((ξ + δ) * 120 + 60 * δ + 200) + 100
  let C_tot := 300 + C_P + C_conv + 36 * C_raw + extraModelCap ξ δ + ξ + 2 * δ + 10
  let c_tot := c_P + C_tot + 6
  refine ⟨prog, C_tot, c_tot, by omega, by omega, ?_⟩
  intro w n_i G_i Z_i t par f_tau s N hw hZ hbd hb0 hb1 hr26 hr28 hr52 hb2_len hb2_get hb3_len hb3_get hb5 hb6
  let x := writtenToAlg41CodeInput G_i Z_i hZ t par f_tau hbd
  have hN_eq : alg41CoreSize x.toCoreInput = N := by
    rw [x.alg41CoreSize_toCoreInput]
    dsimp [alg41CodeSize, x, writtenToAlg41CodeInput, N]
    omega
  have hpow_w : (N + 2) ^ c_tot < 2 ^ w := by
    have h1 := pow_lt_two_pow_wordSize (c := c_tot) (by omega) N
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) hw)
  have hlin_pow : c_tot * (N + 1) ≤ (N + 2) ^ c_tot := mul_succ_le_pow_add_two c_tot N
  have hbase_ge3 : 3 ≤ N + 2 := by omega
  have hsz_w : 5 * (G_i.numEdges + n_i + 1) < 2 ^ w := by
    have hcube : (N + 2) ^ 3 ≤ (N + 2) ^ c_tot :=
      Nat.pow_le_pow_right (by omega) (by omega : 3 ≤ c_tot)
    have hexp : 5 * N + 2 < (N + 2) ^ 3 := by
      have h1 : (N + 2) ^ 3 = (N + 2) * ((N + 2) * (N + 2)) := by
        rw [show (3 : ℕ) = 2 + 1 by rfl, Nat.pow_succ, Nat.pow_two, Nat.mul_comm]
      have h2 : 3 * ((N + 2) * (N + 2)) ≤ (N + 2) * ((N + 2) * (N + 2)) :=
        Nat.mul_le_mul_right _ hbase_ge3
      have h3 : 2 * N + 4 ≤ (N + 2) * (N + 2) := by
        rw [Nat.add_mul, Nat.mul_add]; omega
      omega
    dsimp [N] at *
    omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hn_w : n_i < 2 ^ w := by omega
  have hm_w : G_i.numEdges < 2 ^ w := by omega
  let s_a := s.setReg r_save n_i
  have hex_a : Exec w (.assign r_save (.reg 26)) s s_a 2 :=
    .assign (by simp [Expr.eval, checkWord, hr26, hn_w])
  let s_b := s_a.setReg (r_save + 1) G_i.numEdges
  have hex_b : Exec w (.assign (r_save + 1) (.reg 28)) s_a s_b 2 :=
    .assign (by
      simp only [s_a, Expr.eval, checkWord]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg, r_save]; omega), hr28]
      simp [hm_w])
  rcases normalizeBD41Prog_exec (s := s_b) G_i Z_i hZ b par f_tau hw2 hm_w hbd
    (by
      simp only [s_b, s_a]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg, r_save]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg, r_save]; omega)]
      exact hr28)
    (by
      simp only [s_b, s_a]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg, r_save]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg, r_save]; omega)]
      exact hr52)
    (by simpa only [s_b, s_a, State.setReg_arrs] using hb2_len)
    (fun z hz => by simpa only [s_b, s_a, State.setReg_arrs] using hb2_get z hz)
    (by simpa only [s_b, s_a, State.setReg_arrs] using hb3_len)
    (fun e he => by simpa only [s_b, s_a, State.setReg_arrs] using hb3_get e he) with
    ⟨s₁, t₁, hex₁, ht₁, hr52_1, hb2_1, hb3_1, harr₁, hreg₁⟩
  rcases packAlg41InProg_exec (s := s₁) G_i Z_i hZ p par f_tau hw3 hsz_w hbd
    (by
      rw [hreg₁ 26 (by decide)]
      simp only [s_b, s_a]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg, r_save]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg, r_save]; omega)]
      exact hr26)
    (by
      rw [hreg₁ 28 (by decide)]
      simp only [s_b, s_a]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg, r_save]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg, r_save]; omega)]
      exact hr28)
    hr52_1
    (by rw [harr₁ (b + 1) (by dsimp [b, alg105ArrBase, Arr]; omega) (by dsimp [b, alg105ArrBase, Arr]; omega)]; exact hb1)
    hb2_1 hb3_1
    (by rw [harr₁ (b + 5) (by dsimp [b, alg105ArrBase, Arr]; omega) (by dsimp [b, alg105ArrBase, Arr]; omega)]; exact hb5)
    (by rw [harr₁ (b + 6) (by dsimp [b, alg105ArrBase, Arr]; omega) (by dsimp [b, alg105ArrBase, Arr]; omega)]; exact hb6) with
    ⟨s₂, t₂, hex₂, ht₂, hin₂⟩
  have hin₂' : s₂.arrs inArr = encAlg41CoreIn x.toCoreInput := by
    rw [x.encAlg41CoreIn_toCoreInput, hin₂]
  have hw_P : wordSize c_P (alg41CoreSize x.toCoreInput) ≤ w := by
    rw [hN_eq]
    exact Nat.le_trans (wordSize_mono_left (by dsimp [c_tot]; omega) N) hw
  rcases hP x.toCoreInput s₂ hin₂' with ⟨s₃, t₃, hex₃_0, ht₃, hout₃⟩
  dsimp only at ht₃
  have hex₃ : Exec w P s₂ s₃ t₃ := Exec.mono_wordSize hw_P hex₃_0
  rw [hN_eq] at ht₃
  let T := computeFolioDP x.toCoreInput.G x.toCoreInput.Z δ x.toCoreInput.ht
    x.toCoreInput.p x.toCoreInput.hp x.toCoreInput.τ
  have hout₃_len : (s₃.arrs outArr).length ≤ C_raw * N := by
    rw [hout₃, List.length_append]
    have hF_le : (encFolioSetRep T.toFolioSetRep).length ≤ maxEncFolioSetRepLen ξ δ :=
      length_encFolioSetRep_le_max hZ T.toFolioSetRep
    have hk_le : T.entries.length ≤ maxEncFolioSetRepLen ξ δ := by
      have h1 : T.toFolioSetRep.codes.length ≤ (encFolioSetRep T.toFolioSetRep).length := by
        unfold encFolioSetRep
        simp only [List.length_append, List.length_singleton]
        have : T.toFolioSetRep.codes.length ≤ (T.toFolioSetRep.codes.flatMap (fun c => c.length :: c)).length := by
          induction T.toFolioSetRep.codes with
          | nil => simp
          | cons c cs ih =>
            simp only [List.flatMap_cons, List.length_append, List.length_cons]
            omega
        omega
      have h2 : T.entries.length = T.toFolioSetRep.codes.length := by simp [CertFolioTable.toFolioSetRep]
      omega
    have hraw_le := length_encRawCertModels_le T.entries
    have hm_eq : G_i.toComputeDigraph.numEdges = G_i.numEdges := G_i.length_directedEdgesList
    have h1 : (Z_i.card + δ) * (G_i.toComputeDigraph.numVerts + G_i.toComputeDigraph.numEdges) + δ ≤
        (ξ + δ + δ + 1) * N := by
      change (Z_i.card + δ) * (n_i + G_i.toComputeDigraph.numEdges) + δ ≤ (ξ + δ + δ + 1) * (n_i + G_i.numEdges + 1)
      rw [hm_eq]
      have hm := Nat.mul_le_mul_right (n_i + G_i.numEdges)
        (Nat.add_le_add_right hZ δ)
      have hm' := Nat.mul_le_mul_right (n_i + G_i.numEdges)
        (show ξ + δ ≤ ξ + δ + δ + 1 by omega)
      conv_rhs => rw [Nat.mul_add, Nat.mul_one]
      omega
    have h2 : (encRawCertModels T.toRawList).length ≤ maxEncFolioSetRepLen ξ δ * ((ξ + δ + δ + 1) * N) := by
      exact Nat.le_trans hraw_le (Nat.mul_le_mul hk_le h1)
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hFN := Nat.mul_le_mul_left (maxEncFolioSetRepLen ξ δ) hN
    calc
      _ ≤ maxEncFolioSetRepLen ξ δ * N +
          maxEncFolioSetRepLen ξ δ * ((ξ + δ + δ + 1) * N) :=
        Nat.add_le_add (hF_le.trans (by simpa using hFN)) h2
      _ = C_raw * N := by dsimp [C_raw]; ring
  have hout₃_w : ∀ u ∈ s₃.arrs outArr, u < 2 ^ w := by
    intro u hu
    rw [hout₃] at hu
    have hle := words_encFolioSetRep_append_raw_le T hu
    have hF_le : (encFolioSetRep T.toFolioSetRep).length ≤ maxEncFolioSetRepLen ξ δ :=
      length_encFolioSetRep_le_max hZ T.toFolioSetRep
    have hZ' : Z_i.card ≤ ξ := hZ
    have hmax_le : maxEncFolioSetRepLen ξ δ ≤ C_raw := by
      dsimp [C_raw]
      exact Nat.le_mul_of_pos_right _ (by omega)
    change u ≤ (encFolioSetRep T.toFolioSetRep).length + Z_i.card + 2 * δ + G_i.numEdges + 2 at hle
    have hcpos : 1 ≤ c_tot := by dsimp [c_tot]; omega
    have hmul : N ≤ c_tot * N := Nat.le_mul_of_pos_left N hcpos
    have hlinear := lt_of_le_of_lt hlin_pow hpow_w
    rw [Nat.mul_add, Nat.mul_one] at hlinear
    have hctot : C_raw + ξ + 2 * δ + 10 ≤ c_tot := by dsimp [c_tot, C_tot]; omega
    dsimp only [N] at hlinear hmul
    omega
  have hr_save_not : r_save ∉ P.writtenRegs := by
    intro hmem
    have hle := Finset.le_sup (f := id) hmem
    dsimp [id, r_save, Reg] at hle
    omega
  have hr_save1_not : r_save + 1 ∉ P.writtenRegs := by
    intro hmem
    have hle := Finset.le_sup (f := id) hmem
    dsimp [id, r_save, Reg] at hle
    omega
  have hpack (r : ℕ) (hr : 58 ≤ r) : r ∉ (packAlg41InProg b).writtenRegs := by
    simp [packAlg41InProg, appendSliceProg, forUp, Cmd.writtenRegs]
    dsimp [Reg] at *
    omega
  have hr_save_pack_not : r_save ∉ (packAlg41InProg b).writtenRegs :=
    hpack r_save (by dsimp [r_save, Reg]; omega)
  have hr_save1_pack_not : r_save + 1 ∉ (packAlg41InProg b).writtenRegs :=
    hpack (r_save + 1) (by dsimp [r_save, Reg]; omega)
  have hr_save₃ : s₃.regs r_save = n_i := by
    rw [Exec.regs_eq_of_not_mem_writtenRegs hex₃ hr_save_not,
        Exec.regs_eq_of_not_mem_writtenRegs hex₂ hr_save_pack_not,
        hreg₁ r_save (by dsimp [r_save, Reg]; omega)]
    simp only [s_b, s_a]
    rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
    simp
  have hr_save1₃ : s₃.regs (r_save + 1) = G_i.numEdges := by
    rw [Exec.regs_eq_of_not_mem_writtenRegs hex₃ hr_save1_not,
        Exec.regs_eq_of_not_mem_writtenRegs hex₂ hr_save1_pack_not,
        hreg₁ (r_save + 1) (by dsimp [r_save, Reg]; omega)]
    simp [s_b]
  rcases convertRawOutTo101Prog_exec (s := s₃) hZ T a_dst r_save r_base
    (by dsimp [a_dst, outArr, Arr]; omega)
    (le_refl _) hw1 hout₃ hout₃_w
    (by
      have hC : C_raw ≤ c_tot := by dsimp [c_tot, C_tot]; omega
      have he : extraModelCap ξ δ ≤ c_tot := by dsimp [c_tot, C_tot]; omega
      have hm := Nat.mul_le_mul_right N hC
      have hl := lt_of_le_of_lt hlin_pow hpow_w
      rw [Nat.mul_add, Nat.mul_one] at hl
      omega)
    hn_w hm_w hr_save₃ hr_save1₃ with
    ⟨s₄, t₄, hex₄, ht₄, hout₄, hout₄_len, hout₄_w⟩
  refine ⟨s₄, 2 + (2 + (t₁ + (t₂ + (t₃ + t₄)))), T.toParsedFolioAndModels,
    .seq hex_a (.seq hex_b (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)))),
    ?_, ?_, hout₄_w, ?_, T.isDeltaFolioRep_toParsedFolioAndModels⟩
  · have hN : 1 ≤ N := by dsimp [N]; omega
    have ht1 : t₁ ≤ 9 * N := by dsimp [N]; omega
    change t₂ ≤ 150 * N at ht₂
    change t₄ ≤ C_conv * N + 35 * (s₃.arrs outArr).length at ht₄
    have hm := Nat.mul_le_mul_left 35 hout₃_len
    have hC : 163 + C_P + C_conv + 35 * C_raw ≤ C_tot := by dsimp [C_tot]; omega
    have hCN := Nat.mul_le_mul_right N hC
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul] at hCN
    rw [← Nat.mul_assoc] at hm
    omega
  · have hN : 1 ≤ N := by dsimp [N]; omega
    have he := Nat.mul_le_mul_left (extraModelCap ξ δ) hN
    have hC : C_raw + extraModelCap ξ δ ≤ C_tot := by dsimp [C_tot]; omega
    have hCN := Nat.mul_le_mul_right N hC
    rw [Nat.add_mul] at hCN
    simp only [Nat.mul_one] at he
    omega
  · rw [hout₄]
    exact parseFolioAndModelsFull_encFolioAndModels T.toParsedFolioAndModels

end GraphMinor.Compute
