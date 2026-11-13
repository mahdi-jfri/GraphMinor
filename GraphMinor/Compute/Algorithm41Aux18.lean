module

public import GraphMinor.Compute.Algorithm41Aux17

/-!
# Size Bounds for the Written Folio and Models in GM XIII (4.1)

For fixed folio parameters there are only a bounded number of members, and
each has a bounded number of vertices and edges. Thus the serialized folio
and all its models occupy a constant times the input graph size.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Bound on the size of a length-prefixed folio member code. -/
def L_code41 (δ ξ ω : ℕ) : ℕ := 3 + Q_max ξ ω + 2 * δ

/-- Bound on the full stream size per input word. -/
def L_stream41 (δ ξ ω : ℕ) : ℕ :=
  1 + C_max δ ξ ω * (L_code41 δ ξ ω + V_max δ ξ ω)

private theorem prefix41_length_le {q δ ξ ω : ℕ} (Hs : List (ComputeRootedDigraph q))
    (hq : q ≤ Q_max ξ ω) (hdet : ∀ H ∈ Hs, H.HasDetailLe δ) :
    (enc41FolioPrefix Hs).length ≤ 1 + Hs.length * L_code41 δ ξ ω := by
  have hsum : ((Hs.map encRootedDigraph).flatMap (fun c => c.length :: c)).length ≤
      Hs.length * L_code41 δ ξ ω := by
    induction Hs with
    | nil => simp
    | cons H Hs ih =>
      have hH := length_encRootedDigraph_le_of_hasDetailLe (hdet H (List.mem_cons_self ..))
      have hrec := ih (fun H hH => hdet H (List.mem_cons_of_mem _ hH))
      simp only [List.map_cons, List.flatMap_cons, List.length_append, List.length_cons,
        List.length_cons, Nat.succ_mul]
      unfold L_code41
      unfold L_code41 at hrec
      omega
  simpa only [enc41FolioPrefix, List.length_cons, Nat.add_comm] using Nat.add_le_add_left hsum 1

private theorem model41_entry_length_le {q δ ξ ω : ℕ} {G : ComputeDigraph}
    (e : RawCertEntry G q) (hq : q ≤ Q_max ξ ω) (hdet : e.H.HasDetailLe δ) :
    (encRawCertEntry e).length ≤ V_max δ ξ ω * (G.numVerts + G.numEdges + 1) := by
  have hv := Nat.le_of_lt (numVerts_lt_V_max hq hdet)
  have he := Nat.le_of_lt (numEdges_lt_V_max (ξ := ξ) (ω := ω) hdet)
  have hv_mul := Nat.mul_le_mul_right (G.numVerts + G.numEdges) hv
  rw [length_encRawCertEntry, Nat.mul_succ]
  omega

private theorem models41_length_le {q δ ξ ω : ℕ} {G : ComputeDigraph}
    (es : List (RawCertEntry G q)) (hq : q ≤ Q_max ξ ω)
    (hdet : ∀ e ∈ es, e.H.HasDetailLe δ) :
    (encRawCertModels es).length ≤ es.length *
      (V_max δ ξ ω * (G.numVerts + G.numEdges + 1)) := by
  induction es with
  | nil => simp [encRawCertModels]
  | cons e es ih =>
    have he := model41_entry_length_le e hq (hdet e (List.mem_cons_self ..))
    have hrec := ih (fun e he => hdet e (List.mem_cons_of_mem _ he))
    simpa only [encRawCertModels, List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
      using Nat.add_le_add he hrec

/-- A certified folio table has a serialized stream of linear size. -/
theorem stream41_length_le {δ ξ ω : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    (T : CertFolioTable G VA EA (finsetRootFn Z) δ) (hZ : Z.card ≤ Q_max ξ ω) :
    (encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList).length ≤
      L_stream41 δ ξ ω * (G.numVerts + G.numEdges + 1) := by
  have hdet : ∀ e ∈ T.toRawList, e.H.HasDetailLe δ := by
    intro e he
    obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
    exact e'.hdet
  have hdetH : ∀ H ∈ T.toRawList.map (·.H), H.HasDetailLe δ := by
    intro H hH
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hH
    exact hdet e he
  have hpre := prefix41_length_le (T.toRawList.map (·.H)) hZ hdetH
  rw [enc41FolioPrefix_table, List.length_map] at hpre
  have hmod := models41_length_le T.toRawList hZ hdet
  have hcount : T.toRawList.length ≤ C_max δ ξ ω := by
    have hlen := T.length_entries_le
    have hC := length_allDetailLeCodes_lt_C_max δ ξ ω hZ
    simpa only [CertFolioTable.toRawList, List.length_map] using (Nat.le_trans hlen (Nat.le_of_lt hC))
  have hpre_mul := Nat.mul_le_mul_right (L_code41 δ ξ ω) hcount
  have hmod_mul := Nat.mul_le_mul_right (V_max δ ξ ω * (G.numVerts + G.numEdges + 1)) hcount
  have hpre_scale : 1 + C_max δ ξ ω * L_code41 δ ξ ω ≤
      (1 + C_max δ ξ ω * L_code41 δ ξ ω) * (G.numVerts + G.numEdges + 1) := by
    calc
      _ = (1 + C_max δ ξ ω * L_code41 δ ξ ω) * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  rw [List.length_append]
  have hbound : (encFolioSetRep T.toFolioSetRep).length + (encRawCertModels T.toRawList).length ≤
      (1 + C_max δ ξ ω * L_code41 δ ξ ω) * (G.numVerts + G.numEdges + 1) +
        C_max δ ξ ω * (V_max δ ξ ω * (G.numVerts + G.numEdges + 1)) := by omega
  calc
    _ ≤ _ := hbound
    _ = L_stream41 δ ξ ω * (G.numVerts + G.numEdges + 1) := by
      simp only [L_stream41, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
      omega

/-- The size-expression syntax also has fixed size per abstract member. -/
theorem model41WordsExpr_cost {q : ℕ} (Hs : List (ComputeRootedDigraph q)) :
    (model41WordsExpr Hs).cost = 1 + 8 * Hs.length := by
  induction Hs with
  | nil => rfl
  | cons H Hs ih => simp only [model41WordsExpr, Expr.cost, ih, List.length_cons, Nat.mul_succ]; omega

end GraphMinor.Compute
