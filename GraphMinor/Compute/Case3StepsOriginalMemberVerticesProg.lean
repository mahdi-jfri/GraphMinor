module

public import GraphMinor.Compute.Case3StepsMemberVertexOrder
public import GraphMinor.Compute.TwoPathsRotate

/-!
# Writing the member vertex list in original labels

The member's increasing list uses compact compass labels. Reading each entry
through the compass inverse list gives its original label. The resulting
list is the vertex section of the member record in XIII (9.9), step 6.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Map the counted member list through the original compass inverse list. -/
def case3OriginalMemberVerticesProg : Cmd :=
  TwoPaths.mapProg 97 (.reg 62) 47 32 (.read 31 (.reg 97))

/-- Mapping the member list is linear in its vertex count and preserves
all input arrays and every register except the scan counter. -/
theorem case3OriginalMemberVerticesProg_exec {w k n : ℕ} (S : Finset (Fin k))
    (e : Fin k → Fin n) (hw : 1 < 2 ^ w) (hk : k < 2 ^ w)
    {s : State}
    (hmember : s.arrs 31 = (case3BoundaryVertices S).map Fin.val ++ List.replicate (k - S.card) 0)
    (hcount : s.regs 62 = S.card) (hlen : k ≤ (s.arrs 32).length)
    (hlabels : ∀ i : Fin k, (s.arrs 32).getD i.1 0 = (e i).1)
    (hwords : ∀ x ∈ s.arrs 32, x < 2 ^ w) :
    ∃ s' t, Exec w case3OriginalMemberVerticesProg s s' t ∧
      t ≤ 13 * S.card + 6 ∧
      s'.arrs 47 = (List.finRange S.card).map (fun i => (e (S.orderEmbOfFin rfl i)).1) ∧
      (∀ a, a ≠ 47 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 97 → s'.regs r = s.regs r) := by
  have hc : S.card ≤ k := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  let labels := (case3BoundaryVertices S).map Fin.val ++ List.replicate (k - S.card) 0
  let g (i : ℕ) := labels.getD i 0
  have hlookup (i : ℕ) (hi : i < S.card) : g i = (S.orderEmbOfFin rfl ⟨i, hi⟩).1 :=
    case3PaddedVertices_getD_orderEmb S ⟨i, hi⟩
  have hmemlen : labels.length = k := by
    simp only [labels, List.length_append, List.length_map, case3BoundaryVertices_length,
      List.length_replicate]
    omega
  obtain ⟨s', t, hex, ht, hkeep, hout⟩ := TwoPaths.mapProg_exec 97 (.reg 62) 47 32
    (.read 31 (.reg 97)) (by decide) S.card g (s.arrs 32) s hw (lt_of_le_of_lt hc hk)
    (by intro st hst; simp only [Expr.eval, checkWord, hst.1 62 (by decide), hcount,
        lt_of_le_of_lt hc hk, ↓reduceIte])
    (by
      intro st i hst hri hi
      have hiw : i < 2 ^ w := lt_of_lt_of_le hi hc |>.trans hk
      have his : i < (st.arrs 31).length := by
        rw [hst.2 31 (by decide), hmember, hmemlen]
        exact lt_of_lt_of_le hi hc
      have hread : (st.arrs 31)[i] = g i := by
        rw [← List.getD_eq_getElem _ 0 his, hst.2 31 (by decide), hmember]
      have hgw : g i < 2 ^ w := by rw [hlookup i hi]; exact (S.orderEmbOfFin rfl ⟨i, hi⟩).2.trans hk
      simp only [Expr.eval, checkWord, hri, hiw, his, hread, hgw, ↓reduceIte, ↓reduceDIte])
    (by intro i hi; exact lt_of_lt_of_le (by rw [hlookup i hi]; exact (S.orderEmbOfFin rfl ⟨i, hi⟩).2) hlen)
    hwords rfl
  have ht' : t ≤ 13 * S.card + 6 := by
    norm_num only [Expr.cost] at ht
    omega
  refine ⟨s', t, hex, ht', ?_, fun a ha => hkeep.2 a (by simpa using ha),
    fun r hr => hkeep.1 r (by simpa using hr)⟩
  rw [hout]
  apply List.ext_getElem (by simp only [List.length_map, List.length_range, List.length_finRange])
  intro i hi hi'
  have hic : i < S.card := by simpa only [List.length_map, List.length_range] using hi
  simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
  rw [hlookup i hic, hlabels]
  rfl

end GraphMinor.Compute
