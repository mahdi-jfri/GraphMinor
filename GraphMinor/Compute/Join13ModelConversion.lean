module

public import GraphMinor.Compute.Join13ModelLoops

/-!
# Converting the raw model stream

The conversion copies the folio prefix and changes bit sets into lists of indices.
-/

@[expose] public section
namespace GraphMinor.Compute
open SimpleGraph Classical

/-- Length prefixes add at most two words for each branch set. -/
private theorem length_encModelFull_le_raw {n δ q : ℕ} {G : MultiDigraph n}
    {r_fn : Fin q → Fin G.toComputeDigraph.numVerts}
    (e : CertFolioEntry G.toComputeDigraph Finset.univ Finset.univ r_fn δ) :
    (encModelFull e.model.toRootedDigraphModel).length ≤
      (encRawCertEntry e.toRaw).length + (q + δ) * 2 + 1 := by
  have h := length_encLengthPrefixed_vert_le
    (fun u => (e.model.vertMap u).verts) (fun u => (e.model.vertMap u).edges)
    (List.finRange e.H.digraph.numVerts)
  rw [List.length_finRange] at h
  dsimp only [withRoots] at h
  have hv := e.H.numVerts_le_of_hasDetailLe e.hdet
  have hmul := Nat.mul_le_mul_right 2 hv
  rw [length_rawCertEntry_toRaw]
  unfold encModelFull
  rw [List.length_append, List.length_ofFn]
  change e.H.digraph.numEdges + _ ≤ _
  have heq : e.H.digraph.numVerts *
      (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges + 2) =
      e.H.digraph.numVerts * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges) +
        e.H.digraph.numVerts * 2 := by rw [Nat.mul_add]
  dsimp only [MultiDigraph.toComputeDigraph] at h heq ⊢
  omega

/-- Extra capacity constant `C_extra ξ δ` for `a_dst` when converting `encRawCertModels` into
`encModelList`. -/
def extraModelCap (ξ δ : ℕ) : ℕ :=
  maxEncFolioSetRepLen ξ δ * ((ξ + δ) * 2 + δ + 1)

/-- Post-processing program for `Alg41Spec101`: converts `outArr` (`= encFolioSetRep F ++ encRawCertModels`)
into `encFolioAndModels out` in `outArr`, reading saved `(n, m)` from `(r_save, r_save + 1)` and
using scratch array `a_dst` and scratch registers `r_base .. r_base + 13`. -/
def convertRawOutTo101Prog (ξ δ : ℕ) (a_dst : Arr) (r_save r_base : Reg) : Cmd :=
  let r_hdr := r_base
  let r_src := r_base + 1
  let r_dst := r_base + 2
  let r_n := r_base + 3
  let r_m := r_base + 4
  let r_krem := r_base + 5
  let r_cap := r_base + 6
  .seq (.assign r_n (.reg r_save))
  (.seq (.assign r_m (.reg (r_save + 1)))
  (.seq (.assign r_src (.const 1))
  (.seq (.assign r_krem (.read outArr (.const 0)))
  (.seq (.assign (r_base + 7) (.const 0))
  (.seq (forUp (r_base + 7) (.reg r_krem) (scanFolioPrefixBody outArr r_src (r_base + 8)))
  (.seq (.assign r_cap (.op .add (.len outArr) (.const (extraModelCap ξ δ))))
  (.seq (.alloc a_dst (.reg r_cap))
  (.seq (.assign r_hdr (.const 0))
  (.seq (.assign r_dst (.const 0))
  (.seq (.assign (r_base + 8) (.reg r_src))
  (.seq (copyWordsLoop outArr a_dst r_hdr r_dst (r_base + 8) (r_base + 9))
  (.seq (.assign r_hdr (.const 1))
  (.seq (.assign r_krem (.read outArr (.const 0)))
  (.seq (convertAllModelsLoop outArr a_dst r_base)
        (readSliceProg a_dst (.const 0) outArr (.reg r_dst) (r_base + 9))))))))))))))))

set_option maxHeartbeats 400000 in
theorem convertRawOutTo101Prog_exec {w n ξ δ : ℕ} {G : MultiDigraph n} {Z : Finset (Fin n)}
    (hZ : Z.card ≤ ξ)
    (T : CertFolioTable G.toComputeDigraph Finset.univ Finset.univ (finsetRootFn Z) δ)
    (a_dst : Arr) (r_save r_base : Reg)
    (ha_dst : outArr < a_dst)
    (hr_save : r_save + 2 ≤ r_base)
    (hw : 1 < 2 ^ w)
    {s : State}
    (hout : s.arrs outArr = encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList)
    (hout_w : ∀ x ∈ s.arrs outArr, x < 2 ^ w)
    (hcap_w : (s.arrs outArr).length + extraModelCap ξ δ < 2 ^ w)
    (hn_w : n < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hr_n : s.regs r_save = n)
    (hr_m : s.regs (r_save + 1) = G.numEdges) :
    let out := T.toParsedFolioAndModels
    ∃ s' t,
      Exec w (convertRawOutTo101Prog ξ δ a_dst r_save r_base) s s' t ∧
      t ≤ (maxEncFolioSetRepLen ξ δ * ((ξ + δ) * 120 + 60 * δ + 200) + 100) * (n + G.numEdges + 1) +
          35 * (s.arrs outArr).length ∧
      s'.arrs outArr = encFolioAndModels out ∧
      (s'.arrs outArr).length ≤ (s.arrs outArr).length + extraModelCap ξ δ ∧
      (∀ x ∈ s'.arrs outArr, x < 2 ^ w) := by
  let F := T.toFolioSetRep
  let rawModels := encRawCertModels T.toRawList
  have h0_w : 0 < 2 ^ w := by omega
  have hm_eq : G.toComputeDigraph.numEdges = G.numEdges := G.length_directedEdgesList
  have hn_eq : G.toComputeDigraph.numVerts = n := rfl
  have hF_pos : 0 < (encFolioSetRep F).length := by simp [encFolioSetRep]
  have hF_le_max : (encFolioSetRep F).length ≤ maxEncFolioSetRepLen ξ δ :=
    length_encFolioSetRep_le_max hZ F
  have hk_le_max : T.entries.length ≤ maxEncFolioSetRepLen ξ δ := by
    have h1 : F.codes.length ≤ (encFolioSetRep F).length := by
      unfold encFolioSetRep
      simp only [List.length_append, List.length_singleton]
      have : F.codes.length ≤ (F.codes.flatMap (fun c => c.length :: c)).length := by
        induction F.codes with
        | nil => simp
        | cons c cs ih =>
          simp only [List.flatMap_cons, List.length_append, List.length_cons]
          omega
      omega
    have h2 : T.entries.length = F.codes.length := by simp [F, CertFolioTable.toFolioSetRep]
    omega
  have hout_len_pos : 0 < (s.arrs outArr).length := by rw [hout]; simp [encFolioSetRep]
  have hout_len_w : (s.arrs outArr).length < 2 ^ w := by omega
  have hget0 : (s.arrs outArr)[0]'hout_len_pos = F.codes.length := by
    dsimp [F]
    simp [hout, encFolioSetRep]
  have hk_w : F.codes.length < 2 ^ w := by
    apply hout_w F.codes.length
    rw [hout]; exact List.mem_append_left _ List.mem_cons_self
  have hpos_F_w : (encFolioSetRep F).length < 2 ^ w := by
    have hlen_w := hout_len_w
    rw [hout, List.length_append] at hlen_w
    change (encFolioSetRep F).length + _ < 2 ^ w at hlen_w
    omega
  have hne_s2 : r_base + 3 ≠ r_save + 1 := by dsimp [Reg] at hr_save ⊢; omega
  let s₁ := s.setReg (r_base + 3) n
  have hex₁ : Exec w (.assign (r_base + 3) (.reg r_save)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr_n, hn_w])
  have hrs₁_m : s₁.regs (r_save + 1) = G.numEdges := by
    simp only [s₁]
    rw [State.setReg_regs_ne _ _ hne_s2.symm]
    exact hr_m
  let s₂ := s₁.setReg (r_base + 4) G.numEdges
  have hex₂ : Exec w (.assign (r_base + 4) (.reg (r_save + 1))) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrs₁_m, hm_w])
  let s₃ := s₂.setReg (r_base + 1) 1
  have hex₃ : Exec w (.assign (r_base + 1) (.const 1)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₄ := s₃.setReg (r_base + 5) F.codes.length
  have hex₄ : Exec w (.assign (r_base + 5) (.read outArr (.const 0))) s₃ s₄ 3 :=
    .assign (by simp [s₃, s₂, s₁, Expr.eval, checkWord, h0_w, hout_len_pos, hget0, hk_w])
  let s₄a := s₄.setReg (r_base + 7) 0
  have hex₄a : Exec w (.assign (r_base + 7) (.const 0)) s₄ s₄a 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have ha_scan :
      s₄a.arrs outArr = [F.codes.length] ++ F.codes.flatMap (fun c => c.length :: c) ++ rawModels := by
    change s.arrs outArr = _
    rw [hout]; rfl
  rcases scanFolioPrefixLoop_exec outArr (r_base + 7) (r_base + 5) (r_base + 1) (r_base + 8)
    (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
    (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
    hw F.codes [F.codes.length] rawModels 0
    (by simpa using hk_w)
    (by simpa [encFolioSetRep] using hpos_F_w)
    ha_scan (by simp [s₄a])
    (by
      simp only [s₄a, s₄]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp)
    (by
      simp only [s₄a, s₄, s₃]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp) with
    ⟨s₅, t₅, hex₅, ht₅, hr_src₅, harr₅, hreg₅⟩
  have hF_len_eq : ([F.codes.length] ++ F.codes.flatMap (fun c => c.length :: c)).length =
      (encFolioSetRep F).length := rfl
  rw [hF_len_eq] at hr_src₅
  have hout₅ : s₅.arrs outArr = s.arrs outArr := harr₅ outArr
  let cap := (s.arrs outArr).length + extraModelCap ξ δ
  have hcap_const_w : extraModelCap ξ δ < 2 ^ w := by omega
  let s₆ := s₅.setReg (r_base + 6) cap
  have hex₆ : Exec w (.assign (r_base + 6) (.op .add (.len outArr) (.const (extraModelCap ξ δ)))) s₅ s₆ 4 :=
    .assign (by simp [cap, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hout₅,
      hout_len_w, hcap_const_w, hcap_w])
  let s₇ := s₆.setArr a_dst (List.replicate cap 0)
  have hex₇ : Exec w (.alloc a_dst (.reg (r_base + 6))) s₆ s₇ (1 + cap) :=
    .alloc (by simp [s₆, cap, Expr.eval, checkWord, hcap_w])
  let s₈ := s₇.setReg r_base 0
  have hex₈ : Exec w (.assign r_base (.const 0)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₉ := s₈.setReg (r_base + 2) 0
  have hex₉ : Exec w (.assign (r_base + 2) (.const 0)) s₈ s₉ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₁₀ := s₉.setReg (r_base + 8) (encFolioSetRep F).length
  have hex₁₀ : Exec w (.assign (r_base + 8) (.reg (r_base + 1))) s₉ s₁₀ 2 :=
    .assign (by
      simp only [Expr.eval, s₉, s₈, s₇, s₆]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setArr_regs,
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp [checkWord, hr_src₅, hpos_F_w])
  rcases copyWordsLoop_exec (s := s₁₀) outArr a_dst r_base (r_base + 2) (r_base + 8) (r_base + 9)
    (Nat.ne_of_lt ha_dst) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
    (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
    hw (encFolioSetRep F) [] rawModels [] cap
    (by dsimp [cap, F, rawModels]; rw [hout]; simp; omega)
    (by simpa [hout, F, rawModels] using hout_len_w)
    (by simp [cap, hcap_w])
    (fun u hu => hout_w u (by rw [hout]; exact List.mem_append_left _ hu))
    (by simp [s₁₀, s₉, s₈, s₇, s₆, Nat.ne_of_lt ha_dst, hout₅, hout, F, rawModels])
    (by simp [s₁₀, s₉, s₈, s₇])
    (by
      simp only [s₁₀, s₉, s₈]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp)
    (by
      simp only [s₁₀, s₉]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp)
    (by simp [s₁₀]) with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hdst₁₁, _, hr_dst₁₁, _, harr₁₁, hreg₁₁⟩
  simp only [List.nil_append] at hdst₁₁ hr_dst₁₁
  have hout₁₁ : s₁₁.arrs outArr = s.arrs outArr := by
    rw [harr₁₁ outArr (Nat.ne_of_lt ha_dst)]
    simp [s₁₀, s₉, s₈, s₇, s₆, Nat.ne_of_lt ha_dst, hout₅]
  let s₁₂ := s₁₁.setReg r_base 1
  have hex₁₂ : Exec w (.assign r_base (.const 1)) s₁₁ s₁₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hout₁₂ : s₁₂.arrs outArr = s.arrs outArr := hout₁₁
  have hout₁₂_pos : 0 < (s₁₂.arrs outArr).length := by rw [hout₁₂]; exact hout_len_pos
  have hget₁₂ : (s₁₂.arrs outArr)[0]'hout₁₂_pos = F.codes.length := by
    simp [hout₁₂, hget0]
  let s₁₃ := s₁₂.setReg (r_base + 5) F.codes.length
  have hex₁₃ : Exec w (.assign (r_base + 5) (.read outArr (.const 0))) s₁₂ s₁₃ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hout₁₂_pos, hget₁₂, hk_w])
  have hrem_cap :
      (encRawCertModels (T.entries.map CertFolioEntry.toRaw)).length +
        T.entries.length * ((Z.card + δ) * 2 + 1) ≤
        cap - (encFolioSetRep F).length := by
    have hcap_sub : cap - (encFolioSetRep F).length = rawModels.length + extraModelCap ξ δ := by
      have hlen_eq : (s.arrs outArr).length = (encFolioSetRep F).length + rawModels.length := by
        dsimp [F, rawModels]
        rw [hout, List.length_append]
        rfl
      dsimp [cap]
      omega
    rw [hcap_sub]
    have hmul1 : (Z.card + δ) * 2 + 1 ≤ (ξ + δ) * 2 + δ + 1 := by omega
    have hmul2 : T.entries.length * ((Z.card + δ) * 2 + 1) ≤ extraModelCap ξ δ := by
      unfold extraModelCap
      exact Nat.mul_le_mul hk_le_max hmul1
    have hraw_eq : (encRawCertModels (T.entries.map CertFolioEntry.toRaw)).length = rawModels.length := rfl
    rw [hraw_eq]
    omega
  have ha_hdr₁₃ :
      s₁₃.arrs outArr =
        [F.codes.length] ++
          T.entries.flatMap (fun e => (encRootedDigraph e.H).length :: encRootedDigraph e.H) ++
          rawModels := by
    change s₁₁.arrs outArr = _
    rw [hout₁₁, hout]
    dsimp [F, CertFolioTable.toFolioSetRep, encFolioSetRep]
    rw [List.flatMap_map]
    rfl
  have ha_src₁₃ :
      s₁₃.arrs outArr =
        encFolioSetRep F ++ encRawCertModels (T.entries.map CertFolioEntry.toRaw) ++ [] := by
    change s₁₁.arrs outArr = _
    rw [hout₁₁, hout, List.append_nil]
    rfl
  rcases convertAllModelsLoop_exec (s := s₁₃) outArr a_dst r_base (Nat.ne_of_lt ha_dst) hw
    T.entries [F.codes.length] rawModels (encFolioSetRep F) [] (encFolioSetRep F)
    (cap - (encFolioSetRep F).length)
    hrem_cap
    (by rw [← ha_hdr₁₃]; change (s₁₁.arrs outArr).length < 2 ^ w; rw [hout₁₁]; exact hout_len_w)
    (by rw [← ha_src₁₃]; change (s₁₁.arrs outArr).length < 2 ^ w; rw [hout₁₁]; exact hout_len_w)
    (by
      have hlen_eq : (s.arrs outArr).length = (encFolioSetRep F).length + rawModels.length := by
        dsimp [F, rawModels]
        rw [hout, List.length_append]
        rfl
      dsimp [cap]
      omega)
    (fun e he u hu => by
      apply hout_w u
      rw [← hout₁₁, show s₁₁.arrs outArr = s₁₃.arrs outArr from rfl, ha_hdr₁₃]
      simp only [List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨e, he, hu⟩))
    (fun u hu => by
      apply hout_w u
      rw [hout]
      exact List.mem_append_right _ hu)
    ha_hdr₁₃ ha_src₁₃ hdst₁₁
    (by
      simp only [s₁₃, s₁₂]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp)
    (by
      simp only [s₁₃, s₁₂]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          hreg₁₁ (r_base + 1) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
      simp only [s₁₀, s₉, s₈, s₇, s₆]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp only [State.setArr_regs]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      exact hr_src₅)
    (by
      simp only [s₁₃, s₁₂]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      exact hr_dst₁₁)
    (by
      simp only [s₁₃, s₁₂]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          hreg₁₁ (r_base + 3) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
      simp only [s₁₀, s₉, s₈, s₇, s₆]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp only [State.setArr_regs]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          hreg₅ (r_base + 3) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
      simp only [s₄a, s₄, s₃, s₂]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp [s₁])
    (by
      simp only [s₁₃, s₁₂]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          hreg₁₁ (r_base + 4) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
      simp only [s₁₀, s₉, s₈, s₇, s₆]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp only [State.setArr_regs]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          hreg₅ (r_base + 4) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
      simp only [s₄a, s₄, s₃]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp [s₂])
    (by simp [s₁₃, F, CertFolioTable.toFolioSetRep]) with
    ⟨s₁₄, t₁₄, hex₁₄, ht₁₄, hdst₁₄, hr_dst₁₄, harr₁₄, _⟩
  let out := T.toParsedFolioAndModels
  have hout_eq :
      encFolioSetRep F ++ T.entries.flatMap (fun e => encModelFull e.model.toRootedDigraphModel) =
        encFolioAndModels out :=
    (T.encFolioAndModels_toParsedFolioAndModels).symm
  rw [hout_eq] at hdst₁₄ hr_dst₁₄
  have hout_len_le : (encFolioAndModels out).length ≤ cap := by
    have h1 := congrArg List.length hdst₁₄
    rw [List.length_append, List.length_replicate] at h1
    have h2 : (encFolioAndModels out).length ≤ (s₁₄.arrs a_dst).length := by omega
    have h3 : (s₁₄.arrs a_dst).length = cap := by
      rw [hdst₁₄, List.length_append, List.length_replicate, ← hout_eq, List.length_append]
      have hlen_eq : (s.arrs outArr).length = (encFolioSetRep F).length + rawModels.length := by
        dsimp [F, rawModels]
        rw [hout, List.length_append]
        rfl
      have hmod_le :
          (T.entries.flatMap (fun e => encModelFull e.model.toRootedDigraphModel)).length ≤
            cap - (encFolioSetRep F).length := by
        have hlen_mod :
            (T.entries.flatMap (fun e => encModelFull e.model.toRootedDigraphModel)).length ≤
              (encRawCertModels (T.entries.map CertFolioEntry.toRaw)).length +
                T.entries.length * ((Z.card + δ) * 2 + 1) := by
          clear * -
          induction T.entries with
          | nil => simp [encRawCertModels]
          | cons e es ih =>
            unfold encRawCertModels at ih ⊢
            rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.length_append,
              List.length_append, List.length_cons, Nat.succ_mul]
            have hle := length_encModelFull_le_raw e
            omega
        exact Nat.le_trans hlen_mod hrem_cap
      have hF_le_cap : (encFolioSetRep F).length ≤ cap := by
        dsimp [cap]; omega
      omega
    omega
  have hout_words_w : ∀ x ∈ encFolioAndModels out, x < 2 ^ w := by
    intro x hx
    rw [← hout_eq, List.mem_append] at hx
    rcases hx with hxF | hxM
    · exact hout_w x (by rw [hout]; exact List.mem_append_left _ hxF)
    · rw [List.mem_flatMap] at hxM
      rcases hxM with ⟨e, _, hx_e⟩
      exact words_encModelFull_lt e.model.toRootedDigraphModel hn_w (by rwa [hm_eq]) x hx_e
  have hdst₁₄' : s₁₄.arrs a_dst = ([] : List ℕ) ++ encFolioAndModels out ++
      List.replicate (cap - (encFolioSetRep F).length -
        (T.entries.flatMap (fun e => encModelFull e.model.toRootedDigraphModel)).length) 0 := by
    simpa using hdst₁₄
  rcases readSliceProg_exec (w := w) (n := (encFolioAndModels out).length) (off := 0)
    a_dst outArr (.const 0) (r_base + 2) (r_base + 9)
    (Ne.symm (Nat.ne_of_lt ha_dst)) (by dsimp [Reg]; omega)
    [] (encFolioAndModels out)
    (List.replicate (cap - (encFolioSetRep F).length -
      (T.entries.flatMap (fun e => encModelFull e.model.toRootedDigraphModel)).length) 0)
    rfl rfl hout_words_w hw (by omega)
    (by simp [Expr.eval, checkWord, h0_w])
    hdst₁₄' hr_dst₁₄ with
    ⟨s₁₅, t₁₅, hex₁₅, ht₁₅, hdst₁₅, _, _⟩
  refine ⟨s₁₅,
    2 + (2 + (2 + (3 + (2 + (t₅ + (4 + ((1 + cap) + (2 + (2 + (2 + (t₁₁ + (2 + (3 + (t₁₄ + t₁₅)))))))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₄a (.seq hex₅ (.seq hex₆ (.seq hex₇
      (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ (.seq hex₁₃ (.seq hex₁₄ hex₁₅)))))))))))))),
    ?_, hdst₁₅, by rw [hdst₁₅]; exact hout_len_le, by rw [hdst₁₅]; exact hout_words_w⟩
  simp only [Expr.cost] at ht₁₅
  have hcodes_le : F.codes.length ≤ maxEncFolioSetRepLen ξ δ := by
    have h2 : T.entries.length = F.codes.length := by simp [F, CertFolioTable.toFolioSetRep]
    omega
  have ht₁₄_bound :
      t₁₄ ≤ maxEncFolioSetRepLen ξ δ *
        ((ξ + δ) * (28 * (n + G.numEdges) + 50) + 19 * δ + 30) + 1 := by
    have h1 : (Z.card + δ) * (28 * (G.toComputeDigraph.numVerts + G.toComputeDigraph.numEdges) + 50) + 19 * δ + 30 ≤
        (ξ + δ) * (28 * (n + G.numEdges) + 50) + 19 * δ + 30 := by
      rw [hn_eq, hm_eq]
      have hZ' : Z.card + δ ≤ ξ + δ := by omega
      have hmul := Nat.mul_le_mul_right (28 * (n + G.numEdges) + 50) hZ'
      omega
    have h2 := Nat.mul_le_mul hk_le_max h1
    omega
  have hcap_def : cap = (s.arrs outArr).length + maxEncFolioSetRepLen ξ δ * ((ξ + δ) * 2 + δ + 1) := rfl
  have hslack := Nat.zero_le (maxEncFolioSetRepLen ξ δ *
    ((92 * (ξ + δ) + 60 * δ + 200) * (n + G.numEdges) +
      36 * (ξ + δ) + 24 * δ + 117) + 100 * (n + G.numEdges) + 59 +
      18 * (s.arrs outArr).length)
  nlinarith only [ht₅, ht₁₁, ht₁₄_bound, ht₁₅, hcodes_le, hF_le_max,
    hout_len_le, hcap_def, hslack]


end GraphMinor.Compute
