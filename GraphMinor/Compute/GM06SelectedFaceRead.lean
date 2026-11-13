module

public import GraphMinor.Compute.GM06FaceRowReader

/-!
# Loading the face row named by its positive owner

Section 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) selects a
face through its reverse inner cuff end. A positive owner is its row index
plus one. This program subtracts one, skips that many actual encoded
rows and reads the selected row. Its proof derives the skipped source
prefix from the face encoding and bounds the scan by that encoding's
length. It preserves the owner and origin data for incidence marking.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Load the face whose positive owner is in register 668. -/
def gm06SelectedFaceReadProg : Cmd :=
  .seq (.assign 665 (.op .sub (.reg 668) (.const 1)))
    (.seq (.assign 661 (.const 1)) (.seq gm06SkipFaceRowsLoop gm06ReadFaceRowProg))

/-- Exact indexed face-row loading from the computed code in 607. -/
theorem gm06SelectedFaceReadProg_exec {w i : ℕ} (rows : List (List ℕ)) (s : State)
    (hw : 1 < 2 ^ w) (hi : i < rows.length)
    (h607 : s.arrs 607 = gm06EncodeRows rows)
    (hcode : (s.arrs 607).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 607, x < 2 ^ w)
    (h668 : s.regs 668 = i + 1) :
    ∃ sf t, Exec w gm06SelectedFaceReadProg s sf t ∧ t ≤ 20 + 40 * (s.arrs 607).length ∧
      Keeps [660, 661, 662, 664, 665] [600] s sf ∧ sf.arrs 600 = rows[i] := by
  let before := rows.take i
  let row := rows[i]
  let after := gm06EncodeRowsPayload (rows.drop (i + 1))
  have hbeforeLen : before.length = i := by simp only [before, List.length_take]; omega
  have hsource : s.arrs 607 = [rows.length] ++ gm06EncodeRowsPayload before ++ gm06EncodeNatList row ++ after := by
    rw [h607, gm06EncodeRows, gm06EncodeRowsPayload_split rows i hi]
    rfl
  have hbeforeCode : (gm06EncodeRowsPayload before).length = before.length + before.flatten.length := by
    have h := gm06FaceCode_length before
    simp only [gm06EncodeRows, List.length_cons] at h
    omega
  have htotal : (s.arrs 607).length = 2 + before.length + before.flatten.length + row.length + after.length := by
    rw [hsource]
    simp only [List.length_append, List.length_singleton, gm06EncodeNatList, List.length_cons, List.length_nil, hbeforeCode]
    omega
  have hcountFit : i + 1 < 2 ^ w := by omega
  let s₀ := s.setReg 665 i
  let s₁ := s₀.setReg 661 1
  have he₀ : Exec w (.assign 665 (.op .sub (.reg 668) (.const 1))) s s₀ 4 :=
    .assign (by
      have he := GraphMinor.Compute.Crossing.eval_sub (GraphMinor.Compute.Crossing.eval_reg h668 hcountFit)
        (GraphMinor.Compute.Crossing.eval_const hw)
      simpa using he)
  have he₁ : Exec w (.assign 661 (.const 1)) s₀ s₁ 2 := .assign (GraphMinor.Compute.Crossing.eval_const hw)
  have hk₀₁ : Keeps [660, 661, 662, 664, 665] [600] s s₁ :=
    ((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hp₂, _⟩ := gm06SkipFaceRowsLoop_exec before [rows.length]
    (gm06EncodeNatList row ++ after) s₁ hw (by omega)
    (by simpa only [s₁, s₀, State.setReg_arrs, List.append_assoc] using hsource)
    hcode hwords (by simp [s₁]) (by simpa only [hbeforeLen] using (show s₁.regs 665 = i by simp [s₁, s₀]))
  have hk₀₂ : Keeps [660, 661, 662, 664, 665] [600] s s₂ :=
    hk₀₁.trans hk₂ (fun _ h => h) (fun _ h => h)
  let pre := [rows.length] ++ gm06EncodeRowsPayload before
  have hreadSource : s₂.arrs 607 = pre ++ gm06EncodeNatList row ++ after := by
    rw [hk₀₂.2 607 (by decide)]
    exact hsource
  obtain ⟨sf, tf, hef, htf, hkf, hdf, _⟩ := gm06ReadFaceRowProg_exec pre row after s₂ hw hreadSource
    (by rw [hk₀₂.2 607 (by decide)]; exact hcode)
    (by rw [hk₀₂.2 607 (by decide)]; exact hwords)
    (by simpa only [pre, List.length_append, List.length_singleton] using hp₂)
  refine ⟨sf, 4 + (2 + (t₂ + tf)), .seq he₀ (.seq he₁ (.seq he₂ hef)), ?_,
    hk₀₂.trans hkf (by simp) (fun _ h => h), hdf⟩
  omega

/-- Read the computed owner of target dart 667 and return its row in 600.
Zero owner returns an empty row. The owner remains in register 668. -/
def gm06SelectFaceRowProg : Cmd :=
  .seq (.assign 668 (.read 605 (.reg 667)))
    (.ite (.reg 668) gm06SelectedFaceReadProg (.alloc 600 (.const 0)))

/-- The optional result distinguishes an absent dart from an empty row. -/
def gm06SelectFaceRowResult (s : State) : Option (List ℕ) :=
  if s.regs 668 = 0 then none else some (s.arrs 600)

/-- Exact selected-face row from the computed owner and face arrays.
The positive owner case is proved from actual owner-table writes. -/
theorem gm06SelectFaceRowProg_exec {w q d : ℕ} (rows : List (List ℕ)) (s : State)
    (hw : 1 < 2 ^ w) (hq : q < 2 ^ w) (hd : d < q) (hnd : rows.flatten.Nodup)
    (h605 : s.arrs 605 = gm06FaceOwners q rows) (h607 : s.arrs 607 = gm06EncodeRows rows)
    (hcode : (s.arrs 607).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 607, x < 2 ^ w)
    (h667 : s.regs 667 = d) :
    ∃ sf t, Exec w gm06SelectFaceRowProg s sf t ∧ t ≤ 24 + 40 * (s.arrs 607).length ∧
      Keeps [660, 661, 662, 664, 665, 668] [600] s sf ∧
      gm06SelectFaceRowResult sf = gm06SelectFaceRow rows d ∧
      sf.arrs 600 = (gm06SelectFaceRow rows d).getD [] := by
  let owner := gm06SelectedFaceOwner q rows d
  have hidx : d < (s.arrs 605).length := by simp only [h605, gm06FaceOwners_length]; exact hd
  have hget : (s.arrs 605)[d]'hidx = owner := by
    simp only [owner, gm06SelectedFaceOwner, h605, List.getElem?_eq_getElem (by simpa only [h605] using hidx), Option.getD_some]
  have hownerFit : owner < 2 ^ w := by
    by_cases hz : owner = 0
    · rw [hz]; exact Nat.two_pow_pos w
    · have hi : gm06SelectedFaceIndex q rows d = some (owner - 1) := by simp only [gm06SelectedFaceIndex, owner, hz, ↓reduceIte]
      obtain ⟨hrow, _, _⟩ := gm06SelectedFaceIndex_some rows hd hnd hi
      have hl := gm06FaceCode_length rows
      have hlen : (s.arrs 607).length = (gm06EncodeRows rows).length := congrArg List.length h607
      omega
  let s₀ := s.setReg 668 owner
  have he₀ : Exec w (.assign 668 (.read 605 (.reg 667))) s s₀ 3 :=
    .assign (by
      have he := GraphMinor.Compute.Crossing.eval_read (a := 605)
        (GraphMinor.Compute.Crossing.eval_reg h667 (hd.trans hq)) hidx (by simpa only [hget] using hownerFit)
      simpa only [hget] using he)
  have hk₀ : Keeps [660, 661, 662, 664, 665, 668] [600] s s₀ := (Keeps.refl _ _ s).setReg (by simp) _
  by_cases hz : owner = 0
  · let sf := s₀.setArr 600 []
    have hez : Exec w (.alloc 600 (.const 0)) s₀ sf 1 := .alloc (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
    have hs : gm06SelectFaceRow rows d = none :=
      (gm06SelectFaceRow_none_iff rows d).mpr ((gm06SelectedFaceOwner_zero_iff rows hd).mp hz)
    refine ⟨sf, 3 + (1 + 1), .seq he₀ (.ite_false (by simpa [s₀, hz] using
      (GraphMinor.Compute.Crossing.eval_reg (r := 668) (w := w) (s := s₀) rfl hownerFit)) hez),
      by omega, hk₀.setArr (by simp) _, ?_, ?_⟩
    · simp [gm06SelectFaceRowResult, sf, s₀, hz, hs]
    · simp [sf, hs]
  · have hi : gm06SelectedFaceIndex q rows d = some (owner - 1) := by
      simp only [gm06SelectedFaceIndex, owner, hz, ↓reduceIte]
    obtain ⟨hir, _, hselected⟩ := gm06SelectedFaceIndex_some rows hd hnd hi
    obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06SelectedFaceReadProg_exec rows s₀ hw hir h607 hcode hwords
      (by simp [s₀]; omega)
    have htf' : tf ≤ 20 + 40 * (s.arrs 607).length := by simpa only [s₀, State.setReg_arrs] using htf
    refine ⟨sf, 3 + (1 + tf), .seq he₀ (.ite_true (GraphMinor.Compute.Crossing.eval_reg (by simp [s₀]) hownerFit) hz hef),
      by omega,
      hk₀.trans hkf (by simp) (fun _ h => h), ?_, ?_⟩
    · simp only [gm06SelectFaceRowResult, hkf.1 668 (by decide), s₀, State.setReg_regs_self, hz, ↓reduceIte, hdf, hselected]
    · simp only [hdf, hselected, Option.getD_some]

end GraphMinor.Compute
