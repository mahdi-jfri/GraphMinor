module

public import GraphMinor.Compute.Algorithm41Aux12

/-!
# Folio Prefix Output for GM XIII (4.1)

The folio members are a fixed list in each branch of the finite table dispatch.
This file verifies the constant-word writer for that list and the model-shape
projection used to select the corresponding model-output commands.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Append a fixed list of words to the model-output buffer. -/
def emit41ConstWordsProg : List ℕ → Cmd
  | [] => .skip
  | x :: xs => .seq (emit41WordProg (.const x)) (emit41ConstWordsProg xs)

/-- The constant-word writer writes every word and counts each write. -/
theorem emit41ConstWordsProg_exec {w cap : ℕ} (words pref : List ℕ)
    (hw : 1 < 2 ^ w) (hwords : ∀ x ∈ words, x < 2 ^ w)
    (hcap : pref.length + words.length ≤ cap) (hcap_w : cap < 2 ^ w)
    {s : State}
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hpos : s.regs 9 = pref.length) :
    ∃ s' t, Exec w (emit41ConstWordsProg words) s s' t ∧ t ≤ 1 + 7 * words.length ∧
      s'.arrs outArr = (pref ++ words) ++ List.replicate (cap - (pref.length + words.length)) 0 ∧
      s'.regs 9 = pref.length + words.length ∧
      (∀ a : ℕ, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ 9 → s'.regs r = s.regs r) := by
  induction words generalizing pref s with
  | nil =>
    exact ⟨s, 1, .skip s, by simp, by simpa using hout, by simpa using hpos,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | cons x xs ih =>
    have hx := hwords x (List.mem_cons_self ..)
    rcases emit41WordProg_exec (v := x) (.const x) pref hw
        (by simp only [List.length_cons] at hcap; omega) hcap_w
        (by simp [Expr.eval, checkWord, hx]) hout hpos with
      ⟨s₁, t₁, hex₁, ht₁, hout₁, hpos₁, harr₁, hreg₁⟩
    rcases ih (pref ++ [x]) (fun y hy => hwords y (List.mem_cons_of_mem _ hy))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcap)
        (by simpa using hout₁) (by simpa using hpos₁) with
      ⟨s₂, t₂, hex₂, ht₂, hout₂, hpos₂, harr₂, hreg₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Expr.cost] at ht₁
      rw [List.length_cons, Nat.mul_succ]
      omega
    · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hout₂
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpos₂
    · intro a ha
      exact (harr₂ a ha).trans (harr₁ a ha)
    · intro r hr
      exact (hreg₂ r hr).trans (hreg₁ r hr)

/-- The folio prefix associated with the abstract member list, in the same format as
`encFolioSetRep`. -/
def enc41FolioPrefix {q : ℕ} (Hs : List (ComputeRootedDigraph q)) : List ℕ :=
  Hs.length :: (Hs.map encRootedDigraph).flatMap (fun c => c.length :: c)

/-- Sizes and slot indices used by the model writer. -/
def model41Shapes {q : ℕ} (Hs : List (ComputeRootedDigraph q)) : List (ℕ × ℕ × ℕ) :=
  (List.finRange Hs.length).map (fun i => (i.1, Hs[i.1].digraph.numVerts, Hs[i.1].digraph.numEdges))

/-- Enumerating the entries of a list by index recovers the list. -/
theorem map_finRange_getElem41 {α : Type*} (xs : List α) :
    (List.finRange xs.length).map (fun i => xs[i.1]) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- The abstract table gives exactly the model shapes of its raw entries. -/
theorem model41Shapes_raw {q : ℕ} {G : ComputeDigraph} (es : List (RawCertEntry G q)) :
    model41Shapes (es.map (·.H)) = (List.finRange es.length).map (fun i =>
      (i.1, es[i.1].H.digraph.numVerts, es[i.1].H.digraph.numEdges)) := by
  apply List.ext_getElem
  · simp [model41Shapes]
  · intro i hi hj
    simp [model41Shapes]

/-- The abstract folio prefix agrees with the certified table encoding. -/
theorem enc41FolioPrefix_table {q δ : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} (T : CertFolioTable G VA EA r δ) :
    enc41FolioPrefix (T.toRawList.map (·.H)) = encFolioSetRep T.toFolioSetRep := by
  simp [enc41FolioPrefix, encFolioSetRep, CertFolioTable.toFolioSetRep,
    CertFolioTable.toRawList, CertFolioEntry.toRaw, List.map_map, Function.comp_def]


/-- Write the folio prefix and all models for a fixed abstract table. -/
def serialize41BodyProg (δ ξ ω : ℕ) (tab : AbstractTable) : Cmd :=
  .seq (emit41ConstWordsProg (enc41FolioPrefix tab.2))
    (emit41ModelsProg δ ξ ω (model41Shapes tab.2))

/-- Every word in a valid abstract folio prefix fits in a fixed parameter bound. -/
theorem mem_enc41FolioPrefix_lt {w δ ξ ω : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)} {s : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s)
    (hC : C_max δ ξ ω < 2 ^ w) (hcode : 2 + Q_max ξ ω + 2 * δ < 2 ^ w) :
    ∀ x ∈ enc41FolioPrefix (es.map (·.H)), x < 2 ^ w := by
  intro x hx
  simp only [enc41FolioPrefix, List.length_map, List.mem_cons, List.mem_flatMap,
    List.mem_map, List.mem_cons] at hx
  rcases hx with rfl | ⟨c, ⟨H, ⟨e, he, rfl⟩, rfl⟩, hx⟩
  · have := hbuf.hlen_le
    have := length_allDetailLeCodes_lt_C_max δ ξ ω hbuf.hq_le
    omega
  · have hdet := hbuf.hdet e he
    rcases hx with rfl | hx
    · have := length_encRootedDigraph_le_of_hasDetailLe hdet
      have := hbuf.hq_le
      omega
    · have := mem_encRootedDigraph_le_of_hasDetailLe hdet hx
      have := hbuf.hq_le
      omega

/-- The final table body writes its folio and modelling as a single stream.
The prefix is fixed by the abstract table, and the model data comes from the computed arrays. -/
theorem serialize41BodyProg_exec {w δ ξ ω kv ke cap : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)}
    (hw : 2 < 2 ^ w) (hn_w : G.numVerts < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hkv_w : kv < 2 ^ w) (hke_w : ke < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (hC : C_max δ ξ ω < 2 ^ w) (hcode : 2 + Q_max ξ ω + 2 * δ < 2 ^ w)
    (pref : List ℕ)
    (hcap : pref.length + (enc41FolioPrefix (es.map (·.H))).length + (encRawCertModels es).length ≤ cap)
    (hcap_w : cap < 2 ^ w) {s : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s) (har : ArenaStateInv G kv ke s)
    (hr0 : s.regs 0 = G.numVerts) (hr1 : s.regs 1 = G.numEdges)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hpos : s.regs 9 = pref.length) :
    ∃ s' t,
      Exec w (serialize41BodyProg δ ξ ω ⟨Z.card, es.map (·.H)⟩) s s' t ∧
      t ≤ 2 + 7 * (enc41FolioPrefix (es.map (·.H))).length +
        C_emit41Model δ ξ ω kv ke G.numVerts G.numEdges * es.length ∧
      s'.arrs outArr = (pref ++ (enc41FolioPrefix (es.map (·.H)) ++ encRawCertModels es)) ++
        List.replicate (cap - (pref.length + (enc41FolioPrefix (es.map (·.H))).length +
          (encRawCertModels es).length)) 0 ∧
      s'.regs 9 = pref.length + (enc41FolioPrefix (es.map (·.H))).length + (encRawCertModels es).length ∧
      (∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) := by
  rcases emit41ConstWordsProg_exec (enc41FolioPrefix (es.map (·.H))) pref (by omega)
      (mem_enc41FolioPrefix_lt hbuf hC hcode) (by omega) hcap_w hout hpos with
    ⟨s₁, t₁, hex₁, ht₁, hout₁, hpos₁, harr₁, hreg₁⟩
  rcases emit41ModelsProg_exec (List.finRange es.length) hw hn_w hm_w hkv_w hke_w hS_w
      (pref ++ enc41FolioPrefix (es.map (·.H)))
      (by simpa only [map_finRange_getElem41, List.length_append] using hcap) hcap_w
      (hbuf.output_frame (fun a _ _ ha => harr₁ a ha) (fun r _ _ hr => hreg₁ r hr))
      (har.output_frame (fun a _ _ ha => harr₁ a ha) (fun r _ _ hr => hreg₁ r hr))
      (by rw [hreg₁ 0 (by decide)]; exact hr0)
      (by rw [hreg₁ 1 (by decide)]; exact hr1)
      (by simpa using hout₁) (by simpa using hpos₁) with
    ⟨s₂, t₂, hex₂, ht₂, hout₂, hpos₂, harr₂, hreg₂⟩
  rw [← model41Shapes_raw] at hex₂
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_finRange] at ht₂
    omega
  · simpa only [map_finRange_getElem41, List.length_append, List.append_assoc] using hout₂
  · simpa only [map_finRange_getElem41, List.length_append] using hpos₂
  · intro a ha hb hc
    exact (harr₂ a ha hb hc).trans (harr₁ a hc)
  · intro r hr h7 h9
    exact (hreg₂ r hr h7 h9).trans (hreg₁ r h9)


/-- Select the output writer from the computed table identifier in `r_tidA`.
The finite program contains only abstract member shapes and folio-code words. -/
def serialize41DispatchProg (δ ξ ω : ℕ) : Cmd :=
  branchOnBound (T_max δ ξ ω) r_tidA (fun tid =>
    serialize41BodyProg δ ξ ω (decAbstractTable δ ξ ω tid))

/-- Finite output dispatch writes the computed table's folio prefix and models. -/
theorem serialize41DispatchProg_exec {w δ ξ ω kv ke cap : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)}
    (hw : 2 < 2 ^ w) (hn_w : G.numVerts < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hkv_w : kv < 2 ^ w) (hke_w : ke < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (hC : C_max δ ξ ω < 2 ^ w) (hcode : 2 + Q_max ξ ω + 2 * δ < 2 ^ w)
    (hT : T_max δ ξ ω < 2 ^ w) (pref : List ℕ)
    (hcap : pref.length + (enc41FolioPrefix (es.map (·.H))).length + (encRawCertModels es).length ≤ cap)
    (hcap_w : cap < 2 ^ w) {s : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s) (har : ArenaStateInv G kv ke s)
    (hr0 : s.regs 0 = G.numVerts) (hr1 : s.regs 1 = G.numEdges)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hpos : s.regs 9 = pref.length) :
    ∃ s' t,
      Exec w (serialize41DispatchProg δ ξ ω) s s' t ∧
      t ≤ 3 * T_max δ ξ ω + 2 + 7 * (enc41FolioPrefix (es.map (·.H))).length +
        C_emit41Model δ ξ ω kv ke G.numVerts G.numEdges * es.length ∧
      s'.arrs outArr = (pref ++ (enc41FolioPrefix (es.map (·.H)) ++ encRawCertModels es)) ++
        List.replicate (cap - (pref.length + (enc41FolioPrefix (es.map (·.H))).length +
          (encRawCertModels es).length)) 0 ∧
      s'.regs 9 = pref.length + (enc41FolioPrefix (es.map (·.H))).length + (encRawCertModels es).length ∧
      (∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) := by
  rcases serialize41BodyProg_exec hw hn_w hm_w hkv_w hke_w hS_w hC hcode
      pref hcap hcap_w hbuf har hr0 hr1 hout hpos with
    ⟨s', t, hex, ht, hout', hpos', harr, hreg⟩
  let tab : AbstractTable := ⟨Z.card, es.map (·.H)⟩
  have hlen : tab.2.length ≤ (allDetailLeCodes tab.1 δ).length := by
    simpa [tab] using hbuf.hlen_le
  have hdet : ∀ H ∈ tab.2, H.HasDetailLe δ := by
    intro H hH
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hH
    exact hbuf.hdet e he
  have hdec := decAbstractTable_encAbstractTable δ ξ ω tab hbuf.hq_le hlen hdet
  have hbody : Exec w (serialize41BodyProg δ ξ ω
      (decAbstractTable δ ξ ω (encAbstractTable δ ξ ω tab))) s s' t := by
    rw [hdec]
    exact hex
  have hwpos : 0 < w := Nat.pos_of_ne_zero (fun h => by simp [h] at hw)
  rcases Exec.branchOnBound (w := w) (K := T_max δ ξ ω) (r_in := r_tidA)
      (body := fun tid => serialize41BodyProg δ ξ ω (decAbstractTable δ ξ ω tid))
      (x := encAbstractTable δ ξ ω tab) hwpos hT
      (show s.regs r_tidA = encAbstractTable δ ξ ω tab from hbuf.htid)
      (encAbstractTable_lt δ ξ ω tab hbuf.hq_le hlen) hbody with
    ⟨t', ht', hex'⟩
  exact ⟨s', t', hex', by omega, hout', hpos', harr, hreg⟩

end GraphMinor.Compute
