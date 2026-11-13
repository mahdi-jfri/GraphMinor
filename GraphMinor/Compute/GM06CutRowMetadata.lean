module

public import GraphMinor.Compute.GM06CutPrepareRow
public import GraphMinor.Compute.GM06CutSelectRowProgram

/-!
# The computed local fields used by row emission

The split-row implementation of Section 9 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) passes seven local words from position preparation to the two
induced-row scans. This association list is just their register encoding. The lemmas show that the
actual preparation state has these values, that they fit in words, and that the row scan can
use them while preserving all input metadata.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The seven local fields consumed by the induced-row scan. -/
def gm06CutRowMetadata (position : Option GM06CutPosition) (row : List ℕ) : List (ℕ × ℕ) :=
  [(668, gm06CutPositionKind position), (669, gm06CutPositionIncoming position),
    (670, gm06CutPositionOutgoing position), (671, (gm06CutPositionCuffs position).1),
    (672, (gm06CutPositionCuffs position).2),
    (676, row.idxOf (gm06CutPositionBounds position).1),
    (677, row.idxOf (gm06CutPositionBounds position).2)]

/-- The completed preparation state contains exactly the seven local fields. -/
theorem gm06CutPrepared_metadata (marks : GM06CutTables) (v : ℕ) (row : List ℕ) (s sf : State)
    (hk : Keeps [650, 675, 676, 677] [614]
      (gm06CutDecodedState (gm06CutLoadedState s marks v) (gm06CutPositionAt marks v)) sf)
    (h676 : sf.regs 676 = row.idxOf (gm06CutPositionBounds (gm06CutPositionAt marks v)).1)
    (h677 : sf.regs 677 = row.idxOf (gm06CutPositionBounds (gm06CutPositionAt marks v)).2) :
    ∀ pair ∈ gm06CutRowMetadata (gm06CutPositionAt marks v) row, sf.regs pair.1 = pair.2 := by
  have hends := gm06CutPositionOfMarks_ends (marks.incoming[v]?.getD 0)
    (marks.outgoing[v]?.getD 0) (marks.cuffPositive[v]?.getD 0) (marks.cuffNegative[v]?.getD 0)
  rw [← gm06CutPositionAt_eq_ofMarks] at hends
  intro pair hp
  simp only [gm06CutRowMetadata, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [gm06CutDecodedState] using hk.1 668 (by decide)
  · have hr := hk.1 669 (by decide)
    simpa [gm06CutDecodedState, gm06CutLoadedState, hends.1] using hr
  · have hr := hk.1 670 (by decide)
    simpa [gm06CutDecodedState, gm06CutLoadedState, hends.2] using hr
  · simpa [gm06CutDecodedState] using hk.1 671 (by decide)
  · simpa [gm06CutDecodedState] using hk.1 672 (by decide)
  · exact h676
  · exact h677

/-- Every metadata register key is outside the row scan's write set. -/
theorem gm06CutRowMetadata_key (position : Option GM06CutPosition) (row : List ℕ)
    (pair : ℕ × ℕ) (hp : pair ∈ gm06CutRowMetadata position row) :
    pair.1 ∈ [668, 669, 670, 671, 672, 676, 677] := by
  have hk : pair.1 ∈ (gm06CutRowMetadata position row).map Prod.fst :=
    List.mem_map.mpr ⟨pair, hp, rfl⟩
  simpa only [gm06CutRowMetadata, List.map_cons, List.map_nil] using hk

/-- Metadata values are words once the tables and row length are words. -/
theorem gm06CutRowMetadata_words {w : ℕ} (marks : GM06CutTables) (v : ℕ) (row : List ℕ)
    (hw : 2 < 2 ^ w) (hl : row.length < 2 ^ w)
    (hwords : ∀ x ∈ marks.incoming ++ marks.outgoing ++ marks.cuffPositive ++ marks.cuffNegative, x < 2 ^ w) :
    ∀ pair ∈ gm06CutRowMetadata (gm06CutPositionAt marks v) row, pair.2 < 2 ^ w := by
  have hfields := gm06CutPositionAt_word_bounds marks v hw hwords
  intro pair hp
  simp only [gm06CutRowMetadata, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hfields _ (by simp)
  · exact hfields _ (by simp)
  · exact hfields _ (by simp)
  · exact hfields _ (by simp)
  · exact hfields _ (by simp)
  · exact List.idxOf_le_length.trans_lt hl
  · exact List.idxOf_le_length.trans_lt hl

/-- Invoke the row scan with its seven computed fields as a finite
register encoding. This form is used for both copies of a vertex. -/
theorem gm06CutSelectRowProg_exec_metadata {w m : ℕ}
    (position : Option GM06CutPosition) (row : List ℕ) (left : Bool) (s : State)
    (hw : 4 < 2 ^ w) (hm : 4 * m < 2 ^ w) (hl : row.length + 2 < 2 ^ w)
    (hnd : row.Nodup) (hkeys : ∀ d ∈ row, d < 2 * m)
    (h611 : s.arrs 611 = row) (h614 : s.arrs 614 = gm06RowPositions (2 * m) row)
    (h656 : s.regs 656 = (!left).toNat)
    (hmeta : ∀ pair ∈ gm06CutRowMetadata position row, s.regs pair.1 = pair.2)
    (hword : ∀ pair ∈ gm06CutRowMetadata position row, pair.2 < 2 ^ w) :
    ∃ sf t, Exec w gm06CutSelectRowProg s sf t ∧ t ≤ 2000 * (row.length + 1) ∧
      Keeps [650, 651, 652, 653] [615, 616] s sf ∧ sf.arrs 616 = gm06CutSelectedRow position row left := by
  apply gm06CutSelectRowProg_exec position row left s hw hm hl hnd hkeys h611 h614 h656
    (hmeta (668, gm06CutPositionKind position) (by simp [gm06CutRowMetadata])) (hmeta (669, gm06CutPositionIncoming position) (by simp [gm06CutRowMetadata]))
    (hmeta (670, gm06CutPositionOutgoing position) (by simp [gm06CutRowMetadata])) (hmeta (671, (gm06CutPositionCuffs position).1) (by simp [gm06CutRowMetadata]))
    (hmeta (672, (gm06CutPositionCuffs position).2) (by simp [gm06CutRowMetadata])) (hmeta (676, row.idxOf (gm06CutPositionBounds position).1) (by simp [gm06CutRowMetadata]))
    (hmeta (677, row.idxOf (gm06CutPositionBounds position).2) (by simp [gm06CutRowMetadata]))
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [h656]
    cases left <;> simp only [Bool.not_false, Bool.not_true, Bool.toNat_true, Bool.toNat_false] <;> omega
  · have hmap : r ∈ (gm06CutRowMetadata position row).map Prod.fst := by
      simpa only [gm06CutRowMetadata, List.map_cons, List.map_nil] using hr
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hmap
    rw [hmeta pair hp]
    exact hword pair hp

end GraphMinor.Compute
