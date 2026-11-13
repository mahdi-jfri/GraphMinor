module

public import GraphMinor.Compute.Join13TableBounds72

/-!
# The model-output wrapper for the (7.2) call

The wrapper scans the folio prefix to locate the raw certificates. It allocates
a buffer using the record-length bound, converts all models, and copies the
used buffer into the caller's output array.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Fixed extra buffer capacity for the length-prefixed model table. -/
def modelExtra72 (q δ : ℕ) : ℕ := maxEncFolioSetRepLen q δ * (δ + 3) + 1

/-- Convert the model part of the core output into the caller's output array. -/
def outputModels72Prog (q δ a_src a_ends a_buf a_out r : ℕ) : Cmd :=
  .seq (.assign (r + 9) (.read a_src (.const 0)))
  (.seq (.assign r (.const 1))
  (.seq (.assign (r + 11) (.const 0))
  (.seq (forUp (r + 11) (.reg (r + 9)) (scanFolioPrefixBody a_src r (r + 12)))
  (.seq (.assign (r + 8) (.const 1))
  (.seq (.assign (r + 13) (.op .add (.len a_src) (.const (modelExtra72 q δ))))
  (.seq (.alloc a_buf (.reg (r + 13)))
  (.seq (.write a_buf (.const 0) (.reg (r + 9)))
  (.seq (.assign (r + 1) (.const 1))
  (.seq (modelTable72Loop a_src a_ends a_buf r)
        (readSliceProg a_buf (.const 0) a_out (.reg (r + 1)) (r + 14)))))))))))

/-- The wrapper writes only its buffer and output arrays. -/
theorem outputModels72Prog_writtenArrs_subset (q δ a_src a_ends a_buf a_out r : ℕ) :
    (outputModels72Prog q δ a_src a_ends a_buf a_out r).writtenArrs ⊆ {a_buf, a_out} := by
  intro a ha
  simp [outputModels72Prog, modelTable72Loop, modelTable72Body, writeModelRecord72Prog,
    writeModelBody72Prog, bufPush2, writeEndpoints72Prog, writeVertexBits72Prog,
    fillModelPart72Prog, scanFolioPrefixBody, readSliceProg, readSliceBody, forUp, Cmd.writtenArrs] at ha ⊢
  tauto

/-- Every register written by the wrapper lies in its scratch range. -/
theorem outputModels72Prog_writtenRegs_ge (q δ a_src a_ends a_buf a_out r j : ℕ)
    (hj : j ∈ (outputModels72Prog q δ a_src a_ends a_buf a_out r).writtenRegs) : r ≤ j := by
  simp [outputModels72Prog, modelTable72Loop, modelTable72Body, writeModelRecord72Prog,
    writeModelBody72Prog, bufPush2, writeEndpoints72Prog, writeVertexBits72Prog,
    fillModelPart72Prog, scanFolioPrefixBody, readSliceProg, readSliceBody, forUp, Cmd.writtenRegs] at hj
  omega

/-- The output wrapper writes the exact modelling associated with the core's
certified folio table, in time linear in the core output length. -/
theorem outputModels72Prog_exec {w q δ : ℕ} {G : ComputeDigraph}
    {roots : Fin q → Fin G.numVerts}
    (T : CertFolioTable G Finset.univ Finset.univ roots δ)
    (a_src a_ends a_buf a_out r : ℕ)
    (hsrc_buf : a_src ≠ a_buf) (hends_buf : a_ends ≠ a_buf) (hbuf_out : a_buf ≠ a_out)
    (s : State) (hw : 2 < 2 ^ w) (hn : G.numVerts + G.numEdges < 2 ^ w)
    (hends_len : 2 * G.numEdges < 2 ^ w) (hqd : q + δ < 2 ^ w)
    (hcap : (s.arrs a_src).length + modelExtra72 q δ < 2 ^ w)
    (hsrc : s.arrs a_src = encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList)
    (hends : s.arrs a_ends = endpointWords72 G)
    (hr_n : s.regs (r + 4) = G.numVerts) (hr_m : s.regs (r + 5) = G.numEdges) :
    ∃ s' t, Exec w (outputModels72Prog q δ a_src a_ends a_buf a_out r) s s' t ∧
      t ≤ 200 * ((s.arrs a_src).length + modelExtra72 q δ + maxEncFolioSetRepLen q δ + 1) ∧
      s'.arrs a_out = encFolioModels T.toFolioSetRep T.toFolioModels72 ∧
      (s'.arrs a_out).length ≤ (s.arrs a_src).length + modelExtra72 q δ := by
  let F := T.toFolioSetRep
  let es := T.toRawList
  let cap := (s.arrs a_src).length + modelExtra72 q δ
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hcount : T.entries.length ≤ maxEncFolioSetRepLen q δ :=
    T.length_entries_le_encFolioSetRep.trans (length_encFolioSetRep_le_max (le_refl q) F)
  have hfolio_pos : 0 < (encFolioSetRep F).length := by simp [encFolioSetRep]
  have hfolio_len : (encFolioSetRep F).length ≤ (s.arrs a_src).length := by
    rw [hsrc, List.length_append]
    exact Nat.le_add_right _ _
  have hcount_src := T.length_entries_le_encFolioSetRep.trans hfolio_len
  have hsrc_pos : 0 < (s.arrs a_src).length := by omega
  have hsrc_w : (s.arrs a_src).length < 2 ^ w := by omega
  have hcount_w : T.entries.length < 2 ^ w := by omega
  have hcodes : F.codes.length = T.entries.length := by simp [F, CertFolioTable.toFolioSetRep]
  have hpreEq : [T.entries.length] ++ F.codes.flatMap (fun c => c.length :: c) =
      encFolioSetRep F := by unfold encFolioSetRep; rw [hcodes]
  have hes : es.length = T.entries.length := by simp [es, CertFolioTable.toRawList]
  have hdims : ∀ e ∈ es, e.H.digraph.numVerts < 2 ^ w ∧ e.H.digraph.numEdges < 2 ^ w := by
    intro e he
    rw [show es = T.entries.map CertFolioEntry.toRaw from rfl, List.mem_map] at he
    obtain ⟨e, _, rfl⟩ := he
    exact ⟨(e.H.numVerts_le_of_hasDetailLe e.hdet).trans_lt hqd, e.hdet.1.trans_lt (by omega)⟩
  have hrecords := length_modelRecords72_toRaw_le T.entries
  have hcap_records : 1 + (modelRecords72 es).length ≤ cap := by
    have hm := Nat.mul_le_mul_right (δ + 3) hcount
    have hraw_len : (encRawCertModels es).length ≤ (s.arrs a_src).length := by
      rw [hsrc, List.length_append]
      exact Nat.le_add_left _ _
    dsimp only [cap, modelExtra72]
    change (modelRecords72 es).length ≤ (encRawCertModels es).length + T.entries.length * (δ + 3) at hrecords
    omega
  have hsrc_headers : s.arrs a_src = [T.entries.length] ++ modelHeaders72 es ++ encRawCertModels es := by
    rw [hsrc, T.encFolioSetRep_eq_modelHeaders72]
  have hget0 : (s.arrs a_src).getD 0 0 = T.entries.length := by rw [hsrc_headers]; rfl
  let s₁ := s.setReg (r + 9) T.entries.length
  have hex₁ : Exec w (.assign (r + 9) (.read a_src (.const 0))) s s₁ 3 := by
    apply Exec.assign
    rw [List.getD_eq_getElem _ _ hsrc_pos] at hget0
    simp [Expr.eval, checkWord, hsrc_pos, hget0, hcount_w]
  let s₂ := s₁.setReg r 1
  have hex₂ : Exec w (.assign r (.const 1)) s₁ s₂ 2 := .assign (by simp [Expr.eval, checkWord, h1])
  let s₃ := s₂.setReg (r + 11) 0
  have hex₃ : Exec w (.assign (r + 11) (.const 0)) s₂ s₃ 2 := .assign (by simp [Expr.eval, checkWord, h0])
  obtain ⟨s₄, t₄, hex₄, ht₄, hr_src₄, ha₄, hreg₄⟩ :=
    scanFolioPrefixLoop_exec (s := s₃) a_src (r + 11) (r + 9) r (r + 12)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      h1 F.codes [T.entries.length] (encRawCertModels es) 0
      (by simpa [F, CertFolioTable.toFolioSetRep] using hcount_w)
      (by rw [hpreEq]; exact Nat.lt_of_le_of_lt hfolio_len hsrc_w)
      (by change s.arrs a_src = _; rw [hpreEq]; exact hsrc)
      (by simp [s₃]) (by simp [s₃, s₂, s₁, F, CertFolioTable.toFolioSetRep])
      (by simp [s₃, s₂])
  have hsource₄ : s₄.arrs a_src = s.arrs a_src := by rw [ha₄]; rfl
  have hsourcepos₄ : s₄.regs r = (encFolioSetRep F).length := by
    simpa [encFolioSetRep, F, CertFolioTable.toFolioSetRep] using hr_src₄
  have hregs₄ (j : ℕ) (h0 : j ≠ r) (h11 : j ≠ r + 11) (h12 : j ≠ r + 12)
      (h9 : j ≠ r + 9) : s₄.regs j = s.regs j := by
    rw [hreg₄ j h11 h0 h12]
    simp [s₃, s₂, s₁, h0, h11, h9]
  let s₅ := s₄.setReg (r + 8) 1
  have hex₅ : Exec w (.assign (r + 8) (.const 1)) s₄ s₅ 2 := .assign (by simp [Expr.eval, checkWord, h1])
  let s₆ := s₅.setReg (r + 13) cap
  have hex₆ : Exec w (.assign (r + 13) (.op .add (.len a_src) (.const (modelExtra72 q δ)))) s₅ s₆ 4 :=
    .assign (by simp [s₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hsource₄, hsrc_w, cap,
      show modelExtra72 q δ < 2 ^ w by omega, hcap])
  let s₇ := s₆.setArr a_buf (List.replicate cap 0)
  have hex₇ : Exec w (.alloc a_buf (.reg (r + 13))) s₆ s₇ (1 + cap) :=
    .alloc (by simp [s₆, Expr.eval, checkWord, show cap < 2 ^ w from hcap])
  let s₈ := s₇.writeArr a_buf 0 T.entries.length
  have hex₈ : Exec w (.write a_buf (.const 0) (.reg (r + 9))) s₇ s₈ 3 := by
    apply Exec.write
    · simp [Expr.eval, checkWord]
    · have hr : s₇.regs (r + 9) = T.entries.length := by
        change ((s₄.setReg (r + 8) 1).setReg (r + 13) cap).regs (r + 9) = _
        rw [State.setReg_regs_ne _ _ (show (r + 9 : ℕ) ≠ r + 13 by omega),
          State.setReg_regs_ne _ _ (show (r + 9 : ℕ) ≠ r + 8 by omega),
          hreg₄ (r + 9) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
        simp [s₃, s₂, s₁]
      simp [Expr.eval, checkWord, hr, hcount_w]
    · simp [s₇]
      omega
  let s₉ := s₈.setReg (r + 1) 1
  have hex₉ : Exec w (.assign (r + 1) (.const 1)) s₈ s₉ 2 := .assign (by simp [Expr.eval, checkWord, h1])
  have hd₉ : s₉.arrs a_buf = [T.entries.length] ++ List.replicate (cap - 1) 0 := by
    simp only [s₉, s₈, State.setReg_arrs, State.writeArr_arrs_self, s₇, State.setArr_arrs_self]
    have hcap_pos : 0 < cap := by omega
    rw [show cap = (cap - 1) + 1 by omega, List.replicate_succ, List.set_cons_zero]
    rfl
  have hs₉ : s₉.arrs a_src = s.arrs a_src := by simp [s₉, s₈, s₇, s₆, s₅, hsrc_buf, hsource₄]
  have he₉ : s₉.arrs a_ends = endpointWords72 G := by
    change ((s₄.setArr a_buf (List.replicate cap 0)).writeArr a_buf 0 T.entries.length).arrs a_ends = _
    rw [State.writeArr_arrs_ne _ _ _ hends_buf, State.setArr_arrs_ne _ _ hends_buf, ha₄]
    exact hends
  obtain ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hd₁₀, _, hrd₁₀, _, _, hk₁₀⟩ :=
    modelTable72Loop_exec es a_src a_ends a_buf r hsrc_buf hends_buf
      [T.entries.length] (encRawCertModels es) (encFolioSetRep F) [] [T.entries.length] (cap - 1) s₉
      hw hn hends_len hdims (by omega) (by simp; omega)
      (by rw [← hsrc_headers]; exact hsrc_w)
      (by simpa [hsrc] using hsrc_w)
      (by rw [hs₉]; exact hsrc_headers)
      (by rw [hs₉]; simpa only [List.append_nil] using hsrc)
      he₉ hd₉
      (by
        change (((s₄.setReg (r + 8) 1).setReg (r + 13) cap).setReg (r + 1) 1).regs r = _
        rw [State.setReg_regs_ne _ _ (show (r : ℕ) ≠ r + 1 by omega),
          State.setReg_regs_ne _ _ (show (r : ℕ) ≠ r + 13 by omega),
          State.setReg_regs_ne _ _ (show (r : ℕ) ≠ r + 8 by omega)]
        exact hsourcepos₄)
      (by simp [s₉])
      (by simp [s₉, s₈, s₇, s₆, s₅, hregs₄ (r + 4) (by omega) (by omega) (by omega) (by omega), hr_n])
      (by simp [s₉, s₈, s₇, s₆, s₅, hregs₄ (r + 5) (by omega) (by omega) (by omega) (by omega), hr_m])
      (by simp [s₉, s₈, s₇, s₆, s₅])
      (by
        change (((s₄.setReg (r + 8) 1).setReg (r + 13) cap).setReg (r + 1) 1).regs (r + 9) = _
        rw [State.setReg_regs_ne _ _ (show (r + 9 : ℕ) ≠ r + 1 by omega),
          State.setReg_regs_ne _ _ (show (r + 9 : ℕ) ≠ r + 13 by omega),
          State.setReg_regs_ne _ _ (show (r + 9 : ℕ) ≠ r + 8 by omega),
          hreg₄ _ (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
        simp [s₃, s₂, s₁, hes])
  let out := encFolioModels T.toFolioSetRep T.toFolioModels72
  have hout : out = [T.entries.length] ++ modelRecords72 es := T.encFolioModels_eq_modelRecords72
  have hout_len : out.length ≤ cap := by rw [hout, List.length_append, List.length_singleton]; omega
  have hout_words : ∀ x ∈ out, x < 2 ^ w := by
    intro x hx
    rw [hout, List.mem_append] at hx
    rcases hx with hx | hx
    · have heq : x = T.entries.length := by simpa only [List.mem_singleton] using hx
      simpa only [heq] using hcount_w
    · exact mem_modelRecords72_lt es (by omega) hdims (by omega) h1 hx
  rw [← hout] at hd₁₀ hrd₁₀
  obtain ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hd₁₁, _, _⟩ :=
    readSliceProg_exec (s := s₁₀) (off := 0) (n := out.length) a_buf a_out (.const 0) (r + 1) (r + 14) hbuf_out (by omega)
      [] out (List.replicate (cap - 1 - (modelRecords72 es).length) 0) rfl rfl hout_words h1
      (by simpa only [Nat.zero_add] using Nat.lt_of_le_of_lt hout_len hcap)
      (by simp [Expr.eval, checkWord]) (by simpa using hd₁₀) hrd₁₀
  refine ⟨s₁₁, 3 + (2 + (2 + (t₄ + (2 + (4 + ((1 + cap) + (3 + (2 + (t₁₀ + t₁₁))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex₁₁))))))))),
    ?_, hd₁₁, by rw [hd₁₁]; exact hout_len⟩
  have hrawlen : (encRawCertModels es).length ≤ (s.arrs a_src).length := by rw [hsrc, List.length_append]; exact Nat.le_add_left _ _
  rw [hcodes] at ht₄
  rw [hes] at ht₁₀
  simp only [Expr.cost] at ht₁₁
  dsimp only [cap]
  omega

end GraphMinor.Compute
