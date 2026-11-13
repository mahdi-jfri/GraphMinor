module

public import GraphMinor.Compute.Algorithm41Aux11

/-!
# Writing Models for GM XIII (4.1)

Step (4) of GM XIII (4.1), page 76, backtracks through the folio computation
and writes a model for each member. This file combines the arena-output steps
into programs writing model edge maps and branch subgraphs in their encoded order.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Write the branch subgraphs with the given vertex indices, in order. -/
def emit41ModelVertsProg (δ ξ ω idx : ℕ) : List ℕ → Cmd
  | [] => .skip
  | u :: us => .seq (emit41ModelVertexProg δ ξ ω idx u) (emit41ModelVertsProg δ ξ ω idx us)

/-- The branch-subgraph writer emits precisely the requested list of model sets. -/
theorem emit41ModelVertsProg_exec {w δ ξ ω kv ke cap : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)}
    (idx : Fin es.length) (us : List (Fin es[idx.1].H.digraph.numVerts))
    (hw : 2 < 2 ^ w) (hn_w : G.numVerts < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hkv_w : kv < 2 ^ w) (hke_w : ke < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (pref : List ℕ) (hcap : pref.length + us.length * (G.numVerts + G.numEdges) ≤ cap)
    (hcap_w : cap < 2 ^ w)
    {s : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s) (har : ArenaStateInv G kv ke s)
    (hr0 : s.regs 0 = G.numVerts) (hr1 : s.regs 1 = G.numEdges)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hpos : s.regs 9 = pref.length) :
    ∃ s' t,
      Exec w (emit41ModelVertsProg δ ξ ω idx.1 (us.map Fin.val)) s s' t ∧
      t ≤ 1 + (42 * kv + 42 * ke + 18 * (G.numVerts + G.numEdges) + 46) * us.length ∧
      s'.arrs outArr =
        (pref ++ us.flatMap (fun u => bitSetList (es[idx.1].vertVerts u) ++
          bitSetList (es[idx.1].vertEdges u))) ++
          List.replicate (cap - (pref.length + us.length * (G.numVerts + G.numEdges))) 0 ∧
      s'.regs 9 = pref.length + us.length * (G.numVerts + G.numEdges) ∧
      (∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) := by
  induction us generalizing pref s with
  | nil =>
    exact ⟨s, 1, .skip s, by simp, by simpa using hout, by simpa using hpos,
      fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  | cons u us ih =>
    have hcap₁ : pref.length + G.numVerts + G.numEdges ≤ cap := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hcap
      omega
    rcases emit41ModelVertexProg_exec hbuf har idx u hw hn_w hm_w hkv_w hke_w hS_w
        pref hcap₁ hcap_w hr0 hr1 hout hpos with
      ⟨s₁, t₁, hex₁, ht₁, hout₁, hpos₁, harr₁, hreg₁⟩
    let block := bitSetList (es[idx.1].vertVerts u) ++ bitSetList (es[idx.1].vertEdges u)
    have hblock : block.length = G.numVerts + G.numEdges := by simp [block]
    rcases ih (pref ++ block)
        (by simp only [List.length_append, hblock];
            simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using hcap)
        (hbuf.output_frame harr₁ hreg₁) (har.output_frame harr₁ hreg₁)
        (by rw [hreg₁ 0 (by decide) (by decide) (by decide)]; exact hr0)
        (by rw [hreg₁ 1 (by decide) (by decide) (by decide)]; exact hr1)
        (by simpa [block, Nat.add_assoc] using hout₁)
        (by simpa [hblock, Nat.add_assoc] using hpos₁) with
      ⟨s₂, t₂, hex₂, ht₂, hout₂, hpos₂, harr₂, hreg₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_cons, Nat.mul_succ]
      omega
    · simpa [List.flatMap_cons, block, hblock, Nat.add_mul, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, List.append_assoc] using hout₂
    · simpa [hblock, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpos₂
    · intro a ha hb hc
      exact (harr₂ a ha hb hc).trans (harr₁ a ha hb hc)
    · intro r hr h7 h9
      exact (hreg₂ r hr h7 h9).trans (hreg₁ r hr h7 h9)


/-- Write the model edges with the given indices, in order. -/
def emit41ModelEdgesProg (δ ξ ω idx : ℕ) : List ℕ → Cmd
  | [] => .skip
  | d :: ds => .seq
      (emit41WordProg (.read a_acc_em (.const (idx * V_max δ ξ ω + d))))
      (emit41ModelEdgesProg δ ξ ω idx ds)

/-- The edge-map writer emits the indices of the edges used by the model. -/
theorem emit41ModelEdgesProg_exec {w δ ξ ω cap : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)}
    (idx : Fin es.length) (ds : List (Fin es[idx.1].H.digraph.numEdges))
    (hw : 1 < 2 ^ w) (hm_w : G.numEdges < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (pref : List ℕ) (hcap : pref.length + ds.length ≤ cap) (hcap_w : cap < 2 ^ w)
    {s : State} (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hpos : s.regs 9 = pref.length) :
    ∃ s' t,
      Exec w (emit41ModelEdgesProg δ ξ ω idx.1 (ds.map Fin.val)) s s' t ∧
      t ≤ 1 + 8 * ds.length ∧
      s'.arrs outArr = (pref ++ ds.map (fun d => (es[idx.1].edgeMap d).1)) ++
        List.replicate (cap - (pref.length + ds.length)) 0 ∧
      s'.regs 9 = pref.length + ds.length ∧
      (∀ a : ℕ, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ 9 → s'.regs r = s.regs r) := by
  induction ds generalizing pref s with
  | nil =>
    exact ⟨s, 1, .skip s, by simp, by simpa using hout, by simpa using hpos,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | cons d ds ih =>
    let slot := idx.1 * V_max δ ξ ω + d.1
    have hdet := hbuf.hdet es[idx.1] (List.getElem_mem idx.2)
    have hslot := entrySlot_lt_S_tab hbuf idx
      (Nat.lt_trans d.2 (numEdges_lt_V_max (ξ := ξ) (ω := ω) hdet))
    have hslot_w : slot < 2 ^ w := Nat.lt_trans hslot hS_w
    have hlen : slot < (s.arrs a_acc_em).length := by
      change slot < (s.arrs bufA.a_em).length
      rw [hbuf.hem_len]
      exact hslot
    have hget : (s.arrs a_acc_em)[slot] = (es[idx.1].edgeMap d).1 := by
      have hget := (hbuf.hentries idx).2 d
      dsimp only [bufA] at hget
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some] at hget
      exact hget
    have hval_w : (es[idx.1].edgeMap d).1 < 2 ^ w :=
      Nat.lt_trans (es[idx.1].edgeMap d).2 hm_w
    have heval : (Expr.read a_acc_em (.const slot)).eval w s =
        some (es[idx.1].edgeMap d).1 := by
      simp [Expr.eval, checkWord, hslot_w, hlen, hget, hval_w]
    rcases emit41WordProg_exec (.read a_acc_em (.const slot)) pref hw
        (by simp only [List.length_cons] at hcap; omega) hcap_w heval hout hpos with
      ⟨s₁, t₁, hex₁, ht₁, hout₁, hpos₁, harr₁, hreg₁⟩
    rcases ih (pref ++ [(es[idx.1].edgeMap d).1])
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcap)
        (hbuf.output_frame (fun a _ _ ha => harr₁ a ha) (fun r _ _ hr => hreg₁ r hr))
        (by simpa using hout₁) (by simpa using hpos₁) with
      ⟨s₂, t₂, hex₂, ht₂, hout₂, hpos₂, harr₂, hreg₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Expr.cost] at ht₁
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hout₂
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpos₂
    · intro a ha
      exact (harr₂ a ha).trans (harr₁ a ha)
    · intro r hr
      exact (hreg₂ r hr).trans (hreg₁ r hr)


/-- Length of one serialized model, including its edge map and all branch bit lists. -/
theorem length_encRawCertEntry {q : ℕ} {G : ComputeDigraph} (e : RawCertEntry G q) :
    (encRawCertEntry e).length = e.H.digraph.numEdges +
      e.H.digraph.numVerts * (G.numVerts + G.numEdges) := by
  simp [encRawCertEntry, List.length_flatMap, List.sum_replicate]

/-- Write one model with the given numbers of vertices and edges.
These sizes are constants in each branch of the finite table dispatch. -/
def emit41ModelProg (δ ξ ω idx n m : ℕ) : Cmd :=
  .seq (emit41ModelEdgesProg δ ξ ω idx ((List.finRange m).map Fin.val))
    (emit41ModelVertsProg δ ξ ω idx ((List.finRange n).map Fin.val))

/-- GM XIII (4.1), step (4), page 76: write a model from its stored edge map
and the arena pointers recording its branch subgraphs. -/
theorem emit41ModelProg_exec {w δ ξ ω kv ke cap : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)}
    (idx : Fin es.length)
    (hw : 2 < 2 ^ w) (hn_w : G.numVerts < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hkv_w : kv < 2 ^ w) (hke_w : ke < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (pref : List ℕ) (hcap : pref.length + (encRawCertEntry es[idx.1]).length ≤ cap)
    (hcap_w : cap < 2 ^ w)
    {s : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s) (har : ArenaStateInv G kv ke s)
    (hr0 : s.regs 0 = G.numVerts) (hr1 : s.regs 1 = G.numEdges)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hpos : s.regs 9 = pref.length) :
    ∃ s' t,
      Exec w (emit41ModelProg δ ξ ω idx.1
        es[idx.1].H.digraph.numVerts es[idx.1].H.digraph.numEdges) s s' t ∧
      t ≤ 2 + 8 * es[idx.1].H.digraph.numEdges +
        (42 * kv + 42 * ke + 18 * (G.numVerts + G.numEdges) + 46) * es[idx.1].H.digraph.numVerts ∧
      s'.arrs outArr = (pref ++ encRawCertEntry es[idx.1]) ++
        List.replicate (cap - (pref.length + (encRawCertEntry es[idx.1]).length)) 0 ∧
      s'.regs 9 = pref.length + (encRawCertEntry es[idx.1]).length ∧
      (∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) := by
  rw [length_encRawCertEntry] at hcap
  rcases emit41ModelEdgesProg_exec idx (List.finRange es[idx.1].H.digraph.numEdges)
      (by omega) hm_w hS_w pref (by simpa using (show pref.length + es[idx.1].H.digraph.numEdges ≤ cap by omega))
      hcap_w hbuf hout hpos with
    ⟨s₁, t₁, hex₁, ht₁, hout₁, hpos₁, harr₁, hreg₁⟩
  let edges := (List.finRange es[idx.1].H.digraph.numEdges).map (fun d => (es[idx.1].edgeMap d).1)
  have hlen : edges.length = es[idx.1].H.digraph.numEdges := by simp [edges]
  rcases emit41ModelVertsProg_exec idx (List.finRange es[idx.1].H.digraph.numVerts)
      hw hn_w hm_w hkv_w hke_w hS_w (pref ++ edges)
      (by simpa [hlen, Nat.add_assoc] using hcap) hcap_w
      (hbuf.output_frame (fun a _ _ ha => harr₁ a ha) (fun r _ _ hr => hreg₁ r hr))
      (har.output_frame (fun a _ _ ha => harr₁ a ha) (fun r _ _ hr => hreg₁ r hr))
      (by rw [hreg₁ 0 (by decide)]; exact hr0)
      (by rw [hreg₁ 1 (by decide)]; exact hr1)
      (by simpa [hlen] using hout₁) (by simpa [hlen] using hpos₁) with
    ⟨s₂, t₂, hex₂, ht₂, hout₂, hpos₂, harr₂, hreg₂⟩
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_finRange] at ht₁ ht₂
    omega
  · simpa [encRawCertEntry, edges, length_encRawCertEntry, List.append_assoc, Nat.add_assoc] using hout₂
  · simpa [length_encRawCertEntry, hlen, Nat.add_assoc] using hpos₂
  · intro a ha hb hc
    exact (harr₂ a ha hb hc).trans (harr₁ a hc)
  · intro r hr h7 h9
    exact (hreg₂ r hr h7 h9).trans (hreg₁ r h9)


/-- Serialize models described by triples `(table index, vertex count, edge count)`.
All triples are constants in a branch of the final finite table dispatch. -/
def emit41ModelsProg (δ ξ ω : ℕ) : List (ℕ × ℕ × ℕ) → Cmd
  | [] => .skip
  | (idx, n, m) :: shapes => .seq (emit41ModelProg δ ξ ω idx n m) (emit41ModelsProg δ ξ ω shapes)

/-- The total time for one model is linear in the arena sizes and the input graph size,
with a coefficient depending only on the fixed folio parameters. -/
def C_emit41Model (δ ξ ω kv ke n m : ℕ) : ℕ :=
  2 + 8 * V_max δ ξ ω + (42 * kv + 42 * ke + 18 * (n + m) + 46) * V_max δ ξ ω

/-- Write the selected models, including their edge maps and every branch subgraph. -/
theorem emit41ModelsProg_exec {w δ ξ ω kv ke cap : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)}
    (indices : List (Fin es.length))
    (hw : 2 < 2 ^ w) (hn_w : G.numVerts < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hkv_w : kv < 2 ^ w) (hke_w : ke < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (pref : List ℕ)
    (hcap : pref.length + (encRawCertModels (indices.map (fun i => es[i.1]))).length ≤ cap)
    (hcap_w : cap < 2 ^ w) {s : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s) (har : ArenaStateInv G kv ke s)
    (hr0 : s.regs 0 = G.numVerts) (hr1 : s.regs 1 = G.numEdges)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hpos : s.regs 9 = pref.length) :
    ∃ s' t,
      Exec w (emit41ModelsProg δ ξ ω (indices.map (fun i =>
        (i.1, es[i.1].H.digraph.numVerts, es[i.1].H.digraph.numEdges)))) s s' t ∧
      t ≤ 1 + C_emit41Model δ ξ ω kv ke G.numVerts G.numEdges * indices.length ∧
      s'.arrs outArr = (pref ++ encRawCertModels (indices.map (fun i => es[i.1]))) ++
        List.replicate (cap - (pref.length + (encRawCertModels (indices.map (fun i => es[i.1]))).length)) 0 ∧
      s'.regs 9 = pref.length + (encRawCertModels (indices.map (fun i => es[i.1]))).length ∧
      (∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) := by
  induction indices generalizing pref s with
  | nil =>
    exact ⟨s, 1, .skip s, by simp, by simpa [encRawCertModels] using hout,
      by simpa [encRawCertModels] using hpos, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  | cons idx indices ih =>
    simp only [List.map_cons, encRawCertModels, List.flatMap_cons, List.length_append] at hcap
    rcases emit41ModelProg_exec idx hw hn_w hm_w hkv_w hke_w hS_w pref
        (by omega) hcap_w hbuf har hr0 hr1 hout hpos with
      ⟨s₁, t₁, hex₁, ht₁, hout₁, hpos₁, harr₁, hreg₁⟩
    have hdet := hbuf.hdet es[idx.1] (List.getElem_mem idx.2)
    have hv := numVerts_lt_V_max hbuf.hq_le hdet
    have he := numEdges_lt_V_max (ξ := ξ) (ω := ω) hdet
    have htime₁ : t₁ ≤ C_emit41Model δ ξ ω kv ke G.numVerts G.numEdges := by
      have hv_mul := Nat.mul_le_mul_left
        (42 * kv + 42 * ke + 18 * (G.numVerts + G.numEdges) + 46) (Nat.le_of_lt hv)
      have he_mul := Nat.mul_le_mul_left 8 (Nat.le_of_lt he)
      unfold C_emit41Model
      omega
    rcases ih (pref ++ encRawCertEntry es[idx.1])
        (by simpa [encRawCertModels, Nat.add_assoc] using hcap)
        (hbuf.output_frame harr₁ hreg₁) (har.output_frame harr₁ hreg₁)
        (by rw [hreg₁ 0 (by decide) (by decide) (by decide)]; exact hr0)
        (by rw [hreg₁ 1 (by decide) (by decide) (by decide)]; exact hr1)
        (by simpa using hout₁) (by simpa using hpos₁) with
      ⟨s₂, t₂, hex₂, ht₂, hout₂, hpos₂, harr₂, hreg₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_cons, Nat.mul_succ]
      omega
    · simpa [encRawCertModels, List.append_assoc, Nat.add_assoc] using hout₂
    · simpa [encRawCertModels, Nat.add_assoc] using hpos₂
    · intro a ha hb hc
      exact (harr₂ a ha hb hc).trans (harr₁ a ha hb hc)
    · intro r hr h7 h9
      exact (hreg₂ r hr h7 h9).trans (hreg₁ r hr h7 h9)

end GraphMinor.Compute
