module

public import GraphMinor.Compute.Join13ModelRecord72

/-!
# Converting the model table for (7.2)

The core output contains the folio codes followed by raw model certificates.
The codes give the two dimensions of each model. The loop reads those dimensions,
writes one length-prefixed model, and advances to the next code and certificate.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The self-delimiting representative-code part of a raw model table. -/
def modelHeaders72 {G : ComputeDigraph} {q : ℕ} (es : List (RawCertEntry G q)) : List ℕ :=
  es.flatMap (fun e => (encRootedDigraph e.H).length :: encRootedDigraph e.H)

/-- The caller's length-prefixed model records. -/
def modelRecords72 {G : ComputeDigraph} {q : ℕ} (es : List (RawCertEntry G q)) : List ℕ :=
  es.flatMap (fun e => (encRawModel72 e).length :: encRawModel72 e)

/-- Each representative code contributes at least its length word. -/
theorem length_le_modelHeaders72 {G : ComputeDigraph} {q : ℕ} (es : List (RawCertEntry G q)) :
    es.length ≤ (modelHeaders72 es).length := by
  induction es with
  | nil => simp [modelHeaders72]
  | cons e es ih =>
    simp only [modelHeaders72, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

/-- Read one model's dimensions and write its record. Registers `r + 8` and
`r + 9` hold the code position and the number of remaining models. -/
def modelTable72Body (a_src a_ends a_dst r : ℕ) : Cmd :=
  .seq (.assign (r + 10) (.read a_src (.reg (r + 8))))
  (.seq (.assign (r + 8) (.op .add (.reg (r + 8)) (.const 1)))
  (.seq (.assign (r + 2) (.read a_src (.reg (r + 8))))
  (.seq (.assign (r + 3) (.read a_src (.op .add (.reg (r + 8)) (.const 1))))
  (.seq (.assign (r + 8) (.op .add (.reg (r + 8)) (.reg (r + 10))))
  (.seq (writeModelRecord72Prog a_src a_ends a_dst r)
        (.assign (r + 9) (.op .sub (.reg (r + 9)) (.const 1))))))))

/-- Convert all records, stopping when the model count reaches zero. -/
def modelTable72Loop (a_src a_ends a_dst r : ℕ) : Cmd :=
  .while (.reg (r + 9)) (modelTable72Body a_src a_ends a_dst r)

private theorem getD_header72 {G : ComputeDigraph} {q : ℕ} (e : RawCertEntry G q)
    (pre post : List ℕ) (j : ℕ) (hj : j < 3) :
    (pre ++ ((encRootedDigraph e.H).length :: encRootedDigraph e.H) ++ post).getD
        (pre.length + j) 0 =
      [(encRootedDigraph e.H).length, e.H.digraph.numVerts, e.H.digraph.numEdges].getD j 0 := by
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  have hfirst : (encRootedDigraph e.H).length :: encRootedDigraph e.H =
      [(encRootedDigraph e.H).length, e.H.digraph.numVerts, e.H.digraph.numEdges] ++
      (List.ofFn (fun i => (e.H.roots i).1) ++
        (List.finRange e.H.digraph.numEdges).flatMap (fun d =>
          [(e.H.digraph.head d).1, (e.H.digraph.tail d).1])) := by rfl
  rw [hfirst, List.append_assoc, List.getD_append _ _ _ _ (by simpa using hj)]

/-- The table loop converts exactly the listed raw certificates. Its time is
linear in their total length plus their number. -/
theorem modelTable72Loop_exec {w : ℕ} {G : ComputeDigraph} {q : ℕ}
    (es : List (RawCertEntry G q)) (a_src a_ends a_dst r : ℕ)
    (hsrc_dst : a_src ≠ a_dst) (hends_dst : a_ends ≠ a_dst)
    (pre_hdr post_hdr pre_src post_src pre_dst : List ℕ) (rem : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : G.numVerts + G.numEdges < 2 ^ w)
    (hends_len : 2 * G.numEdges < 2 ^ w)
    (hdims : ∀ e ∈ es, e.H.digraph.numVerts < 2 ^ w ∧ e.H.digraph.numEdges < 2 ^ w)
    (hrem : (modelRecords72 es).length ≤ rem)
    (hcap : pre_dst.length + rem < 2 ^ w)
    (hhdr_len : (pre_hdr ++ modelHeaders72 es ++ post_hdr).length < 2 ^ w)
    (hsrc_len : (pre_src ++ encRawCertModels es ++ post_src).length < 2 ^ w)
    (hhdr : s.arrs a_src = pre_hdr ++ modelHeaders72 es ++ post_hdr)
    (hsrc : s.arrs a_src = pre_src ++ encRawCertModels es ++ post_src)
    (hends : s.arrs a_ends = endpointWords72 G)
    (hdst : s.arrs a_dst = pre_dst ++ List.replicate rem 0)
    (hr_src : s.regs r = pre_src.length) (hr_dst : s.regs (r + 1) = pre_dst.length)
    (hr_n : s.regs (r + 4) = G.numVerts) (hr_m : s.regs (r + 5) = G.numEdges)
    (hr_hdr : s.regs (r + 8) = pre_hdr.length) (hr_count : s.regs (r + 9) = es.length) :
    ∃ s' t, Exec w (modelTable72Loop a_src a_ends a_dst r) s s' t ∧
      t ≤ 110 * ((encRawCertModels es).length + es.length) + 1 ∧
      s'.arrs a_dst = pre_dst ++ modelRecords72 es ++
        List.replicate (rem - (modelRecords72 es).length) 0 ∧
      s'.regs r = (pre_src ++ encRawCertModels es).length ∧
      s'.regs (r + 1) = (pre_dst ++ modelRecords72 es).length ∧
      s'.regs (r + 8) = (pre_hdr ++ modelHeaders72 es).length ∧
      s'.regs (r + 9) = 0 ∧
      Keeps [r, r + 1, r + 2, r + 3, r + 6, r + 8, r + 9, r + 10] [a_dst] s s' := by
  induction es generalizing pre_hdr pre_src pre_dst rem s with
  | nil =>
    refine ⟨s, 1, .while_false (by simp [Expr.eval, checkWord, hr_count]), by simp [encRawCertModels],
      ?_, ?_, ?_, ?_, hr_count, Keeps.refl _ _ s⟩
    · simpa [modelRecords72] using hdst
    · simpa [encRawCertModels] using hr_src
    · simpa [modelRecords72] using hr_dst
    · simpa [modelHeaders72] using hr_hdr
  | cons e es ih =>
    let c := encRootedDigraph e.H
    let record := (encRawModel72 e).length :: encRawModel72 e
    have hdim := hdims e List.mem_cons_self
    have hc2 : 2 ≤ c.length := by simp [c, encRootedDigraph]
    have hheader : s.arrs a_src = pre_hdr ++ (c.length :: c) ++ (modelHeaders72 es ++ post_hdr) := by
      simpa [modelHeaders72, c, List.append_assoc] using hhdr
    have hheader_sz : pre_hdr.length + 1 + c.length + (modelHeaders72 es).length + post_hdr.length < 2 ^ w := by
      have hh := hhdr_len
      simp only [modelHeaders72, List.flatMap_cons, List.length_append, List.length_cons] at hh
      dsimp only [c, modelHeaders72]
      omega
    have hsource : s.arrs a_src = pre_src ++ encRawCertEntry e ++ (encRawCertModels es ++ post_src) := by
      simpa [encRawCertModels, List.append_assoc] using hsrc
    have hrec_len : record.length + (modelRecords72 es).length ≤ rem := by
      simpa only [modelRecords72, record, List.flatMap_cons, List.length_append, List.length_cons] using hrem
    have hcount_w : (e :: es).length < 2 ^ w := by
      have hle := length_le_modelHeaders72 (e :: es)
      simp only [List.length_append] at hhdr_len
      omega
    have hget0 : (s.arrs a_src).getD pre_hdr.length 0 = c.length := by
      rw [hheader]
      simp [c]
    have hget1 : (s.arrs a_src).getD (pre_hdr.length + 1) 0 = e.H.digraph.numVerts := by
      rw [hheader]
      simpa [c] using getD_header72 e pre_hdr (modelHeaders72 es ++ post_hdr) 1 (by decide)
    have hget2 : (s.arrs a_src).getD (pre_hdr.length + 1 + 1) 0 = e.H.digraph.numEdges := by
      rw [hheader]
      simpa [c, Nat.add_assoc] using getD_header72 e pre_hdr (modelHeaders72 es ++ post_hdr) 2 (by decide)
    have hreadlen : pre_hdr.length + 2 < (s.arrs a_src).length := by
      rw [hheader]; simp only [List.length_append, List.length_cons]; omega
    let s₁ := s.setReg (r + 10) c.length
    have hex₁ : Exec w (.assign (r + 10) (.read a_src (.reg (r + 8)))) s s₁ 3 :=
      exec_assign_read_getD (r + 10) a_src (r + 8) hr_hdr (by omega) (by omega) hget0 (by omega)
    let s₂ := s₁.setReg (r + 8) (pre_hdr.length + 1)
    have hex₂ : Exec w (.assign (r + 8) (.op .add (.reg (r + 8)) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_hdr,
        show pre_hdr.length < 2 ^ w by omega, show pre_hdr.length + 1 < 2 ^ w by omega,
        show 1 < 2 ^ w by omega])
    let s₃ := s₂.setReg (r + 2) e.H.digraph.numVerts
    have hex₃ : Exec w (.assign (r + 2) (.read a_src (.reg (r + 8)))) s₂ s₃ 3 :=
      exec_assign_read_getD (r + 2) a_src (r + 8) (idx := pre_hdr.length + 1) (by simp [s₂]) (by omega)
        (by change pre_hdr.length + 1 < (s.arrs a_src).length; omega) hget1 hdim.1
    let s₄ := s₃.setReg (r + 3) e.H.digraph.numEdges
    have hex₄ : Exec w (.assign (r + 3) (.read a_src (.op .add (.reg (r + 8)) (.const 1)))) s₃ s₄ 5 := by
      apply Exec.assign
      have hidx : (.op .add (.reg (r + 8)) (.const 1) : Expr).eval w s₃ = some (pre_hdr.length + 1 + 1) := by
        simp [s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          show pre_hdr.length + 1 < 2 ^ w by omega,
          show pre_hdr.length + 1 + 1 < 2 ^ w by omega, show 1 < 2 ^ w by omega]
      have hbound : pre_hdr.length + 1 + 1 < (s₃.arrs a_src).length := by exact hreadlen
      have hget : (s₃.arrs a_src)[pre_hdr.length + 1 + 1] = e.H.digraph.numEdges := by
        rw [← List.getD_eq_getElem _ _ hbound]
        exact hget2
      simpa only [hget] using read_eval hidx hbound (by rw [hget]; exact hdim.2)
    let s₅ := s₄.setReg (r + 8) (pre_hdr.length + 1 + c.length)
    have hex₅ : Exec w (.assign (r + 8) (.op .add (.reg (r + 8)) (.reg (r + 10)))) s₄ s₅ 4 :=
      .assign (by simp [s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        show pre_hdr.length + 1 < 2 ^ w by omega, show c.length < 2 ^ w by omega,
        show pre_hdr.length + 1 + c.length < 2 ^ w by omega])
    have hregs₅ (j : ℕ) (h2 : j ≠ r + 2) (h3 : j ≠ r + 3)
        (h8 : j ≠ r + 8) (h10 : j ≠ r + 10) : s₅.regs j = s.regs j := by
      simp [s₅, s₄, s₃, s₂, s₁, h2, h3, h8, h10]
    obtain ⟨s₆, t₆, hex₆, ht₆, hd₆, hrs₆, hrd₆, hk₆⟩ :=
      writeModelRecord72Prog_exec e a_src a_ends a_dst r hsrc_dst hends_dst
        pre_src (encRawCertModels es ++ post_src) pre_dst rem s₅ hw hn hends_len hdim.1 hdim.2
        (by have hh := hrec_len; simp only [record, List.length_cons] at hh; omega) hcap
        (by simpa [encRawCertModels, List.append_assoc] using hsrc_len)
        hsource hends hdst
        (by rw [hregs₅ r (by omega) (by omega) (by omega) (by omega), hr_src])
        (by rw [hregs₅ _ (by omega) (by omega) (by omega) (by omega), hr_dst])
        (by simp [s₅, s₄, s₃]) (by simp [s₅, s₄])
        (by rw [hregs₅ _ (by omega) (by omega) (by omega) (by omega), hr_n])
        (by rw [hregs₅ _ (by omega) (by omega) (by omega) (by omega), hr_m])
    let s₇ := s₆.setReg (r + 9) es.length
    have hex₇ : Exec w (.assign (r + 9) (.op .sub (.reg (r + 9)) (.const 1))) s₆ s₇ 4 := by
      apply Exec.assign
      have hr : s₆.regs (r + 9) = (e :: es).length := by
        rw [hk₆.1 (r + 9) (by simp), hregs₅ _ (by omega) (by omega) (by omega) (by omega), hr_count]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr,
        show es.length + 1 < 2 ^ w by simpa only [List.length_cons] using hcount_w,
        show es.length < 2 ^ w by simp at hcount_w; omega, show 1 < 2 ^ w by omega]
    have ha₇ (a : ℕ) (ha : a ≠ a_dst) : s₇.arrs a = s.arrs a := by
      exact hk₆.2 a (by simpa using ha)
    obtain ⟨s', t', hex', ht', hd', hrs', hrd', hrh', hrc', hk'⟩ :=
      ih (pre_hdr ++ (c.length :: c)) (pre_src ++ encRawCertEntry e) (pre_dst ++ record)
        (rem - record.length) s₇ (fun x hx => hdims x (List.mem_cons_of_mem e hx))
        (by omega) (by simp only [List.length_append]; omega)
        (by simpa [modelHeaders72, c, List.append_assoc] using hhdr_len)
        (by simpa [encRawCertModels, List.append_assoc] using hsrc_len)
        (by rw [ha₇ _ hsrc_dst, hhdr]; simp [modelHeaders72, c, List.append_assoc])
        (by rw [ha₇ _ hsrc_dst, hsrc]; simp [encRawCertModels, List.append_assoc])
        ((ha₇ _ hends_dst).trans hends)
        hd₆
        (by rw [State.setReg_regs_ne _ _ (show (r : ℕ) ≠ r + 9 by omega)]; exact hrs₆)
        (by rw [State.setReg_regs_ne _ _ (show (r + 1 : ℕ) ≠ r + 9 by omega)]; exact hrd₆)
        (by rw [State.setReg_regs_ne _ _ (show (r + 4 : ℕ) ≠ r + 9 by omega), hk₆.1 _ (by simp),
          hregs₅ _ (by omega) (by omega) (by omega) (by omega), hr_n])
        (by rw [State.setReg_regs_ne _ _ (show (r + 5 : ℕ) ≠ r + 9 by omega), hk₆.1 _ (by simp),
          hregs₅ _ (by omega) (by omega) (by omega) (by omega), hr_m])
        (by
          simp only [s₇]
          rw [State.setReg_regs_ne _ _ (show (r + 8 : ℕ) ≠ r + 9 by omega), hk₆.1 _ (by simp)]
          simp only [s₅, State.setReg_regs_self, List.length_append, List.length_cons]
          omega)
        (by simp [s₇])
    have hbody : Exec w (modelTable72Body a_src a_ends a_dst r) s s₇
        (3 + (4 + (3 + (5 + (4 + (t₆ + 4)))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))
    refine ⟨s', 1 + (3 + (4 + (3 + (5 + (4 + (t₆ + 4)))))) + t',
      .while_true (v := (e :: es).length)
        (by simp only [Expr.eval, checkWord, hr_count, hcount_w, ↓reduceIte]) (by simp) hbody hex',
      ?_, ?_, ?_, ?_, ?_, hrc', ?_⟩
    · simp only [encRawCertModels, List.flatMap_cons, List.length_append, List.length_cons] at ht' ⊢
      rw [Nat.mul_add] at ht' ⊢
      omega
    · have hsub : rem - record.length - (modelRecords72 es).length =
          rem - (modelRecords72 (e :: es)).length := by
        simp only [modelRecords72, List.flatMap_cons, List.length_append, record, List.length_cons]
        omega
      rw [hsub] at hd'
      simpa only [modelRecords72, List.flatMap_cons, record, List.append_assoc] using hd' 
    · simpa [encRawCertModels, List.append_assoc] using hrs'
    · simpa [modelRecords72, List.append_assoc, record] using hrd'
    · simpa [modelHeaders72, List.append_assoc, c] using hrh'
    · refine ⟨fun j hj => ?_, fun a ha => ?_⟩
      · rw [hk'.1 j hj, State.setReg_regs_ne _ _ (by simp only [List.mem_cons, not_or] at hj; tauto),
          hk₆.1 j (by simp only [List.mem_cons, not_or] at hj ⊢; tauto)]
        apply hregs₅
        all_goals simp only [List.mem_cons, not_or] at hj; tauto
      · rw [hk'.2 a ha]
        exact ha₇ a (by simpa using ha)

end GraphMinor.Compute
