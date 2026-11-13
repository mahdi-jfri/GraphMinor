module

public import GraphMinor.Compute.Join13Defs

/-!
# Copying the folio prefix for (7.2)

The core writes the folio before its raw certificates. The wrapper scans the
self-delimiting codes and copies just that prefix into the caller's folio array.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Locate and copy the folio prefix of a core output stream. -/
def copyFolioPrefix72Prog (a_src a_out r : ℕ) : Cmd :=
  .seq (.assign r (.read a_src (.const 0)))
  (.seq (.assign (r + 1) (.const 1))
  (.seq (.assign (r + 2) (.const 0))
  (.seq (forUp (r + 2) (.reg r) (scanFolioPrefixBody a_src (r + 1) (r + 3)))
        (readSliceProg a_src (.const 0) a_out (.reg (r + 1)) (r + 4)))))

/-- Copying the folio prefix takes time linear in the prefix length and number
of representative codes. -/
theorem copyFolioPrefix72Prog_exec {w q δ : ℕ} (F : FolioSetRep q δ) (rest : List ℕ)
    (a_src a_out r : ℕ) (hne : a_src ≠ a_out) (s : State)
    (hw : 1 < 2 ^ w) (hcount : F.codes.length < 2 ^ w)
    (hlen : (encFolioSetRep F ++ rest).length < 2 ^ w)
    (hwords : ∀ x ∈ encFolioSetRep F, x < 2 ^ w)
    (hsrc : s.arrs a_src = encFolioSetRep F ++ rest) :
    ∃ s' t, Exec w (copyFolioPrefix72Prog a_src a_out r) s s' t ∧
      t ≤ 30 * ((encFolioSetRep F).length + F.codes.length + 1) ∧
      s'.arrs a_out = encFolioSetRep F := by
  have h0 : 0 < 2 ^ w := by omega
  have hpos : 0 < (s.arrs a_src).length := by rw [hsrc]; simp [encFolioSetRep]
  have hget : (s.arrs a_src)[0]'hpos = F.codes.length := by simp [hsrc, encFolioSetRep]
  let s₁ := s.setReg r F.codes.length
  have hex₁ : Exec w (.assign r (.read a_src (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hpos, hget, hcount])
  let s₂ := s₁.setReg (r + 1) 1
  have hex₂ : Exec w (.assign (r + 1) (.const 1)) s₁ s₂ 2 := .assign (by simp [Expr.eval, checkWord, hw])
  let s₃ := s₂.setReg (r + 2) 0
  have hex₃ : Exec w (.assign (r + 2) (.const 0)) s₂ s₃ 2 := .assign (by simp [Expr.eval, checkWord, h0])
  have hprefix : (encFolioSetRep F).length < 2 ^ w := by
    simp only [List.length_append] at hlen
    omega
  obtain ⟨s₄, t₄, hex₄, ht₄, hrpos₄, ha₄, _⟩ :=
    scanFolioPrefixLoop_exec (s := s₃) a_src (r + 2) r (r + 1) (r + 3)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      hw F.codes [F.codes.length] rest 0 (by simpa using hcount)
      (by exact hprefix)
      (by change s.arrs a_src = _; exact hsrc)
      (by simp [s₃]) (by simp [s₃, s₂, s₁]) (by simp [s₃, s₂])
  have hrpos : s₄.regs (r + 1) = (encFolioSetRep F).length := hrpos₄
  obtain ⟨s₅, t₅, hex₅, ht₅, hout, _, _⟩ :=
    readSliceProg_exec (s := s₄) (off := 0) (n := (encFolioSetRep F).length)
      a_src a_out (.const 0) (r + 1) (r + 4) hne (by omega)
      [] (encFolioSetRep F) rest rfl rfl hwords hw (by simpa using hprefix)
      (by simp [Expr.eval, checkWord])
      (by rw [ha₄]; exact hsrc) hrpos
  refine ⟨s₅, 3 + (2 + (2 + (t₄ + t₅))), .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), ?_, hout⟩
  simp only [Expr.cost] at ht₅
  omega

/-- Only the caller's folio array is written. -/
theorem copyFolioPrefix72Prog_writtenArrs (a_src a_out r : ℕ) :
    (copyFolioPrefix72Prog a_src a_out r).writtenArrs = {a_out} := by
  simp [copyFolioPrefix72Prog, scanFolioPrefixBody, readSliceProg, readSliceBody, forUp, Cmd.writtenArrs]

/-- All writes to registers are in the wrapper's scratch range. -/
theorem copyFolioPrefix72Prog_writtenRegs_ge (a_src a_out r j : ℕ)
    (hj : j ∈ (copyFolioPrefix72Prog a_src a_out r).writtenRegs) : r ≤ j := by
  simp [copyFolioPrefix72Prog, scanFolioPrefixBody, readSliceProg, readSliceBody, forUp, Cmd.writtenRegs] at hj
  omega

end GraphMinor.Compute
