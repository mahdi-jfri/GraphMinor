module

public import GraphMinor.Compute.Algorithm41Aux13

/-!
# Output Allocation for GM XIII (4.1)

The final abstract folio table determines the exact length of the output as an
affine function of the input vertex and edge counts. This file computes that
length on the Word RAM before writing the folio and its models.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Number of words in the model blocks for the given abstract folio members. -/
def model41Words {q : ℕ} (n m : ℕ) : List (ComputeRootedDigraph q) → ℕ
  | [] => 0
  | H :: Hs => H.digraph.numEdges + H.digraph.numVerts * (n + m) + model41Words n m Hs

/-- Expression computing the model-output length from `r_0` and `r_1`. -/
def model41WordsExpr {q : ℕ} : List (ComputeRootedDigraph q) → Expr
  | [] => .const 0
  | H :: Hs => .op .add
      (.op .add (.const H.digraph.numEdges)
        (.op .mul (.const H.digraph.numVerts) (.op .add (.reg 0) (.reg 1))))
      (model41WordsExpr Hs)

/-- The model word count depends only on the abstract members and input sizes. -/
theorem length_encRawCertModels {q : ℕ} {G : ComputeDigraph} (es : List (RawCertEntry G q)) :
    (encRawCertModels es).length = model41Words G.numVerts G.numEdges (es.map (·.H)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simpa only [encRawCertModels, List.flatMap_cons, List.length_append,
      length_encRawCertEntry, List.map_cons, model41Words] using
      congrArg (fun k => (encRawCertEntry e).length + k) ih

/-- Evaluation of the output-length expression, including bounds for every intermediate word. -/
theorem model41WordsExpr_eval {w q n m : ℕ} (Hs : List (ComputeRootedDigraph q))
    (hw : 0 < 2 ^ w) (hn : n < 2 ^ w) (hm : m < 2 ^ w) (hnm : n + m < 2 ^ w)
    (hbound : ∀ H ∈ Hs, H.digraph.numVerts < 2 ^ w ∧ H.digraph.numEdges < 2 ^ w)
    (hlen : model41Words n m Hs < 2 ^ w) {s : State}
    (hr0 : s.regs 0 = n) (hr1 : s.regs 1 = m) :
    (model41WordsExpr Hs).eval w s = some (model41Words n m Hs) := by
  induction Hs with
  | nil => simp [model41WordsExpr, model41Words, checkWord, hw]
  | cons H Hs ih =>
    have hH := hbound H (List.mem_cons_self ..)
    have htail : model41Words n m Hs < 2 ^ w := by dsimp only [model41Words] at hlen; omega
    have hprod : H.digraph.numVerts * (n + m) < 2 ^ w := by dsimp only [model41Words] at hlen; omega
    have hblock : H.digraph.numEdges + H.digraph.numVerts * (n + m) < 2 ^ w := by
      dsimp only [model41Words] at hlen
      omega
    have hrec := ih (fun H hH => hbound H (List.mem_cons_of_mem _ hH)) htail
    have hlen' := hlen
    dsimp only [model41Words] at hlen'
    rw [model41WordsExpr]
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0, hr1, hn, hm, hnm,
      hH.1, hH.2, hprod, hblock, hrec, hlen', model41Words]


/-- Exact output length, computed from the fixed member list and the two input sizes. -/
def output41LengthExpr (tab : AbstractTable) : Expr :=
  .op .add (.const (enc41FolioPrefix tab.2).length) (model41WordsExpr tab.2)

/-- Allocate the output array and serialize one fixed abstract table. -/
def serialize41TableProg (δ ξ ω : ℕ) (tab : AbstractTable) : Cmd :=
  .seq (.alloc outArr (output41LengthExpr tab))
    (.seq (.assign 9 (.const 0)) (serialize41BodyProg δ ξ ω tab))

/-- The output-length expression equals the length of the folio and all model blocks. -/
theorem output41LengthExpr_eval {w δ ξ ω : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)} {s : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s)
    (hw : 0 < 2 ^ w) (hn : G.numVerts < 2 ^ w) (hm : G.numEdges < 2 ^ w)
    (hnm : G.numVerts + G.numEdges < 2 ^ w) (hV : V_max δ ξ ω < 2 ^ w)
    (hlen : (enc41FolioPrefix (es.map (·.H)) ++ encRawCertModels es).length < 2 ^ w)
    (hr0 : s.regs 0 = G.numVerts) (hr1 : s.regs 1 = G.numEdges) :
    (output41LengthExpr ⟨Z.card, es.map (·.H)⟩).eval w s =
      some (enc41FolioPrefix (es.map (·.H)) ++ encRawCertModels es).length := by
  have hmodel := length_encRawCertModels es
  have htotal : (enc41FolioPrefix (es.map (·.H))).length +
      model41Words G.numVerts G.numEdges (es.map (·.H)) < 2 ^ w := by
    simpa only [List.length_append, hmodel] using hlen
  have hbound : ∀ H ∈ es.map (·.H), H.digraph.numVerts < 2 ^ w ∧ H.digraph.numEdges < 2 ^ w := by
    intro H hH
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hH
    have hdet := hbuf.hdet e he
    exact ⟨(numVerts_lt_V_max hbuf.hq_le hdet).trans hV,
      (numEdges_lt_V_max (ξ := ξ) (ω := ω) hdet).trans hV⟩
  have hrec := model41WordsExpr_eval (es.map (·.H)) hw hn hm hnm hbound (by omega) hr0 hr1
  unfold output41LengthExpr
  simp only [Expr.eval, hrec]
  simp [BinOp.eval, BinOp.raw, checkWord, show (enc41FolioPrefix (es.map (·.H))).length < 2 ^ w by omega,
    htotal, List.length_append, hmodel]

/-- GM XIII (4.1), step (4), page 76: allocate and write the folio together with
all its models. The output stream is read directly by `decAlg41OutWords`. -/
theorem serialize41TableProg_exec {w δ ξ ω kv ke : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)} {s : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s) (har : ArenaStateInv G kv ke s)
    (hw : 2 < 2 ^ w) (hn : G.numVerts < 2 ^ w) (hm : G.numEdges < 2 ^ w)
    (hnm : G.numVerts + G.numEdges < 2 ^ w)
    (hkv : kv < 2 ^ w) (hke : ke < 2 ^ w)
    (hV : V_max δ ξ ω < 2 ^ w) (hS : S_tab δ ξ ω < 2 ^ w)
    (hC : C_max δ ξ ω < 2 ^ w) (hcode : 2 + Q_max ξ ω + 2 * δ < 2 ^ w)
    (hlen : (enc41FolioPrefix (es.map (·.H)) ++ encRawCertModels es).length < 2 ^ w)
    (hr0 : s.regs 0 = G.numVerts) (hr1 : s.regs 1 = G.numEdges) :
    ∃ s' t,
      Exec w (serialize41TableProg δ ξ ω ⟨Z.card, es.map (·.H)⟩) s s' t ∧
      t ≤ (output41LengthExpr ⟨Z.card, es.map (·.H)⟩).cost + 5 +
        (enc41FolioPrefix (es.map (·.H)) ++ encRawCertModels es).length +
        7 * (enc41FolioPrefix (es.map (·.H))).length +
        C_emit41Model δ ξ ω kv ke G.numVerts G.numEdges * es.length ∧
      s'.arrs outArr = enc41FolioPrefix (es.map (·.H)) ++ encRawCertModels es ∧
      (∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) := by
  let words := enc41FolioPrefix (es.map (·.H)) ++ encRawCertModels es
  let tab : AbstractTable := ⟨Z.card, es.map (·.H)⟩
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setArr outArr (List.replicate words.length 0)
  have hex₁ : Exec w (.alloc outArr (output41LengthExpr tab)) s s₁
      ((output41LengthExpr tab).cost + words.length) :=
    .alloc (output41LengthExpr_eval hbuf h0 hn hm hnm hV hlen hr0 hr1)
  let s₂ := s₁.setReg 9 0
  have hex₂ : Exec w (.assign 9 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0])
  have harr₂ : ∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s₂.arrs a = s.arrs a := by
    intro a _ _ ha
    simp [s₂, s₁, ha]
  have hreg₂ : ∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s₂.regs r = s.regs r := by
    intro r _ _ hr
    simp [s₂, s₁, State.setReg, hr]
  rcases serialize41BodyProg_exec hw hn hm hkv hke hS hC hcode []
      (cap := words.length) (by simp [words]) hlen
      (hbuf.output_frame harr₂ hreg₂) (har.output_frame harr₂ hreg₂)
      (by rw [hreg₂ 0 (by decide) (by decide) (by decide)]; exact hr0)
      (by rw [hreg₂ 1 (by decide) (by decide) (by decide)]; exact hr1)
      (by simp [s₂, s₁]) (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hout₃, _, harr₃, hreg₃⟩
  refine ⟨s₃, ((output41LengthExpr tab).cost + words.length) + (2 + t₃),
    .seq hex₁ (.seq hex₂ hex₃), ?_, ?_, ?_, ?_⟩
  · dsimp only [words, tab]
    omega
  · simpa [words, List.length_append] using hout₃
  · intro a ha hb hc
    exact (harr₃ a ha hb hc).trans (harr₂ a ha hb hc)
  · intro r hr h7 h9
    exact (hreg₃ r hr h7 h9).trans (hreg₂ r hr h7 h9)

/-- Final output pass: choose the table-specific allocation and writing program. -/
def serialize41FinalProg (δ ξ ω : ℕ) : Cmd :=
  branchOnBound (T_max δ ξ ω) r_tidA (fun tid =>
    serialize41TableProg δ ξ ω (decAbstractTable δ ξ ω tid))

/-- The final finite dispatch allocates and writes the computed folio and its modelling. -/
theorem serialize41FinalProg_exec {w δ ξ ω kv ke : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)} {s : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s) (har : ArenaStateInv G kv ke s)
    (hw : 2 < 2 ^ w) (hn : G.numVerts < 2 ^ w) (hm : G.numEdges < 2 ^ w)
    (hnm : G.numVerts + G.numEdges < 2 ^ w)
    (hkv : kv < 2 ^ w) (hke : ke < 2 ^ w)
    (hV : V_max δ ξ ω < 2 ^ w) (hS : S_tab δ ξ ω < 2 ^ w)
    (hC : C_max δ ξ ω < 2 ^ w) (hcode : 2 + Q_max ξ ω + 2 * δ < 2 ^ w)
    (hT : T_max δ ξ ω < 2 ^ w)
    (hlen : (enc41FolioPrefix (es.map (·.H)) ++ encRawCertModels es).length < 2 ^ w)
    (hr0 : s.regs 0 = G.numVerts) (hr1 : s.regs 1 = G.numEdges) :
    ∃ s' t,
      Exec w (serialize41FinalProg δ ξ ω) s s' t ∧
      t ≤ 3 * T_max δ ξ ω + (output41LengthExpr ⟨Z.card, es.map (·.H)⟩).cost + 5 +
        (enc41FolioPrefix (es.map (·.H)) ++ encRawCertModels es).length +
        7 * (enc41FolioPrefix (es.map (·.H))).length +
        C_emit41Model δ ξ ω kv ke G.numVerts G.numEdges * es.length ∧
      s'.arrs outArr = enc41FolioPrefix (es.map (·.H)) ++ encRawCertModels es ∧
      (∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) := by
  rcases serialize41TableProg_exec hbuf har hw hn hm hnm hkv hke hV hS hC hcode hlen hr0 hr1 with
    ⟨s', t, hex, ht, hout, harr, hreg⟩
  let tab : AbstractTable := ⟨Z.card, es.map (·.H)⟩
  have hlen_tab : tab.2.length ≤ (allDetailLeCodes tab.1 δ).length := by
    simpa [tab] using hbuf.hlen_le
  have hdet : ∀ H ∈ tab.2, H.HasDetailLe δ := by
    intro H hH
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hH
    exact hbuf.hdet e he
  have hdec := decAbstractTable_encAbstractTable δ ξ ω tab hbuf.hq_le hlen_tab hdet
  have hbody : Exec w (serialize41TableProg δ ξ ω
      (decAbstractTable δ ξ ω (encAbstractTable δ ξ ω tab))) s s' t := by
    rw [hdec]
    exact hex
  have hwpos : 0 < w := Nat.pos_of_ne_zero (fun h => by simp [h] at hw)
  rcases Exec.branchOnBound (w := w) (K := T_max δ ξ ω) (r_in := r_tidA)
      (body := fun tid => serialize41TableProg δ ξ ω (decAbstractTable δ ξ ω tid))
      (x := encAbstractTable δ ξ ω tab) hwpos hT
      (show s.regs r_tidA = encAbstractTable δ ξ ω tab from hbuf.htid)
      (encAbstractTable_lt δ ξ ω tab hbuf.hq_le hlen_tab) hbody with
    ⟨t', ht', hex'⟩
  exact ⟨s', t', hex', by omega, hout, harr, hreg⟩

end GraphMinor.Compute
