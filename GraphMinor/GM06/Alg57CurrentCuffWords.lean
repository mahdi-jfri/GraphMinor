module

public import GraphMinor.GM06.Alg57CurrentRows
public import GraphMinor.GM06.Alg57CurrentCutEnds
import GraphMinor.GM06.Alg57PersistentRowRotation
import GraphMinor.Compute.GM06CutAdjacencyMath

/-!
# Cuff words in individual current rows

For the local side proof of VI (5.7), page 133, a signed cuff word
occurs only at its prescribed source or target. Distinct current
rows cannot share a word. Thus at a decoded cuff vertex the only
cuff words in the row are its two marked ends, and an interior
linkage row has no cuff word.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- A current word can belong to only one original vertex row. -/
theorem vertex_eq_of_common_row_word {a b : Fin x.vertexCount} {r : ℕ}
    (ha : r ∈ x.rotations.getD a.val []) (hb : r ∈ x.rotations.getD b.val []) : a = b := by
  have hal := rep.live_of_mem_row ha
  have hbl := rep.live_of_mem_row hb
  obtain ⟨d, hd, hl⟩ := exists_persistentDart_of_mem_row (rep.rows a hal) ha
  obtain ⟨e, he, hm⟩ := exists_persistentDart_of_mem_row (rep.rows b hbl) hb
  have hde := persistentDartLabel_injective rep.label (hl.trans hm.symm)
  apply rep.vertex_inj hal hbl
  apply injective_cylinderToSphere
  exact hd.symm.trans ((congrArg (dartVertex rep.par) hde).trans he)

/-- The two orientations of an inner cuff word occur at exactly
its two prescribed source slots. -/
theorem inner_word_mem_iff (hG : IsCylinderSection5Drawing k G)
    (a : Fin x.vertexCount) (i : Fin k) (b : Bool) :
    2 * (rep.tagged.length + i.val) + b.toNat ∈ x.rotations.getD a.val [] ↔
      a = if b then rep.source (finSuccCycle i) else rep.source i := by
  cases b with
  | false =>
    simp only [Bool.toNat_false, Nat.add_zero, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun h => rep.vertex_eq_of_common_row_word h (rep.inner_markers hG i).1,
      fun h => h.symm ▸ (rep.inner_markers hG i).1⟩
  | true =>
    simp only [Bool.toNat_true, ↓reduceIte]
    exact ⟨fun h => rep.vertex_eq_of_common_row_word h (rep.inner_markers hG i).2,
      fun h => h.symm ▸ (rep.inner_markers hG i).2⟩

/-- The two orientations of an outer cuff word occur at exactly
its two prescribed target slots. -/
theorem outer_word_mem_iff (hG : IsCylinderSection5Drawing k G)
    (a : Fin x.vertexCount) (i : Fin k) (b : Bool) :
    2 * (rep.tagged.length + k + i.val) + b.toNat ∈ x.rotations.getD a.val [] ↔
      a = if b then rep.target (finSuccCycle i) else rep.target i := by
  cases b with
  | false =>
    simp only [Bool.toNat_false, Nat.add_zero, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun h => rep.vertex_eq_of_common_row_word h (rep.outer_markers hG i).1,
      fun h => h.symm ▸ (rep.outer_markers hG i).1⟩
  | true =>
    simp only [Bool.toNat_true, ↓reduceIte]
    exact ⟨fun h => rep.vertex_eq_of_common_row_word h (rep.outer_markers hG i).2,
      fun h => h.symm ▸ (rep.outer_markers hG i).2⟩

/-- Every cuff word in a current row has one of the four signed
cuff forms, at its exact prescribed endpoint slot. -/
theorem cuff_word_cases (hG : IsCylinderSection5Drawing k G)
    (a : Fin x.vertexCount) {r : ℕ} (hr : r ∈ x.rotations.getD a.val [])
    (hlarge : 2 * rep.tagged.length ≤ r) :
    (∃ i : Fin k, ∃ b : Bool,
      r = 2 * (rep.tagged.length + i.val) + b.toNat ∧
        a = if b then rep.source (finSuccCycle i) else rep.source i) ∨
    ∃ i : Fin k, ∃ b : Bool,
      r = 2 * (rep.tagged.length + k + i.val) + b.toNat ∧
        a = if b then rep.target (finSuccCycle i) else rep.target i := by
  have hb := rep.row_word_lt hG hr
  have hpar : ∃ b : Bool, r = 2 * (r / 2) + b.toNat := by
    rcases gm06DartMate_end_cases r with ⟨he, _⟩ | ⟨he, _⟩
    · exact ⟨false, by simpa only [Bool.toNat_false, Nat.add_zero] using he⟩
    · exact ⟨true, by simpa only [Bool.toNat_true] using he⟩
  obtain ⟨b, hpar⟩ := hpar
  by_cases hi : r / 2 < rep.tagged.length + k
  · let i : Fin k := ⟨r / 2 - rep.tagged.length, by omega⟩
    have he : r = 2 * (rep.tagged.length + i.val) + b.toNat := by dsimp only [i]; omega
    exact Or.inl ⟨i, b, he, (rep.inner_word_mem_iff hG a i b).mp (he ▸ hr)⟩
  · let i : Fin k := ⟨r / 2 - (rep.tagged.length + k), by omega⟩
    have he : r = 2 * (rep.tagged.length + k + i.val) + b.toNat := by dsimp only [i]; omega
    exact Or.inr ⟨i, b, he, (rep.outer_word_mem_iff hG a i b).mp (he ▸ hr)⟩

/-- At a decoded linkage row, cuff words are exactly among the
marked cuff ends. In particular none occurs at an interior row. -/
theorem cuff_word_at_position (hG : IsCylinderSection5Drawing k G)
    (a : Fin x.vertexCount) {r : ℕ} (hr : r ∈ x.rotations.getD a.val [])
    (hlarge : 2 * rep.tagged.length ≤ r) (p : GM06CutPosition)
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) a.val = some p) :
    match p with
    | .interior _ _ => False
    | .start _ cp cn | .terminal _ cp cn => r = cp ∨ r = cn := by
  rcases rep.cuff_word_cases hG a hr hlarge with ⟨i, b, he, ha⟩ | ⟨i, b, he, ha⟩
  · cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at ha
      obtain ⟨q, hq⟩ := rep.cut_source_position hG.1 i
      rw [ha] at hp
      cases Option.some.inj (hp.symm.trans hq)
      exact Or.inl (by simpa only [Bool.toNat_false, Nat.add_zero] using he)
    | true =>
      simp only [↓reduceIte] at ha
      obtain ⟨q, hq⟩ := rep.cut_source_position hG.1 (finSuccCycle i)
      rw [ha] at hp
      cases Option.some.inj (hp.symm.trans hq)
      exact Or.inr (by simpa only [Bool.toNat_true, previousCuffIndex_succ] using he)
  · cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at ha
      obtain ⟨q, hq⟩ := rep.cut_target_position hG.1 i
      rw [ha] at hp
      cases Option.some.inj (hp.symm.trans hq)
      exact Or.inl (by simpa only [Bool.toNat_false, Nat.add_zero] using he)
    | true =>
      simp only [↓reduceIte] at ha
      obtain ⟨q, hq⟩ := rep.cut_target_position hG.1 (finSuccCycle i)
      rw [ha] at hp
      cases Option.some.inj (hp.symm.trans hq)
      exact Or.inr (by simpa only [Bool.toNat_true, previousCuffIndex_succ] using he)

end GM06CurrentDrawingRep
end GraphMinor.GM06
