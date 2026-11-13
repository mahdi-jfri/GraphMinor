module

public import GraphMinor.Compute.GM02RecursiveRestoreBoundary
public import GraphMinor.Compute.GM02RecursiveAfterRight
public import GraphMinor.Compute.GM02RecursiveFrameWrites
public import GraphMinor.Compute.GM02TerminatedWords

/-!
# Returning a right-child answer to its saved parent

Pop the parent arrays and continuation words, restore its catalogue and
inverse boundary names, then combine the saved left answer with the
returned right answer. The resulting state resumes the parent scan at
the next code, with the exact disjunction accumulator and older stack.
-/

public section
namespace GraphMinor.Compute
open Classical

private theorem bit_words {w n : ℕ} (S : Finset (Fin n)) (hw : 1 < 2 ^ w) :
    ∀ v ∈ bitSetList S, v < 2 ^ w := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  exact (getElem_bitSetList_le_one S i hi).trans_lt hw

/-- An ordinary right answer restores its parent and resumes the next scheme code. -/
theorem gm02RecursiveReturnProg_right_exec {w cap : ℕ} (q : ℕ)
    (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n)) (pref : List ℕ)
    (phase code aggregate leftAnswer rightAnswer : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w)
    (hframe : pref.length + 9 + x.enc.length + 2 * x.n < 2 ^ w)
    (hph : phase ≤ 1) (ha : aggregate ≤ 1) (hl : leftAnswer ≤ 1) (hr : rightAnswer ≤ 1)
    (hnext : code + 1 < 2 ^ w)
    (hcatw : gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q)
      (gm02CompressedBoundaryInput x L R) < 2 ^ w)
    (hheader : ∀ v ∈ gm02SavedFrameHeader x.enc (bitSetList L) (bitSetList R)
      (phase + 2) code aggregate leftAnswer
      (gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R)), v < 2 ^ w)
    (hstack : s.arrs (gm02RecursiveStackArr q) = pref ++
      gm02SavedFrameWords x.enc (bitSetList L) (bitSetList R) (phase + 2) code aggregate leftAnswer
        (gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R))
        pref.length ++ List.replicate cap 0)
    (hpos : s.regs (gm02RecursiveControlBase q + 10) = pref.length + 9 + x.enc.length + 2 * x.n)
    (hflag : s.regs outReg = rightAnswer) :
    let b := gm02RecursiveControlBase q
    ∃ s' t, Exec w (gm02RecursiveReturnProg q) s s' t ∧
      t ≤ 34 * (x.enc.length + 2 * x.n) + 63 * x.n + 28 * x.A.index + 390 ∧
      s'.arrs (gm02RecursiveParentArr q) = x.enc ∧ s'.arrs 1 = bitSetList L ∧ s'.arrs 2 = bitSetList R ∧
      s'.regs (b + 3) = phase ∧ s'.regs (b + 4) = code + 1 ∧
      s'.regs (b + 5) = 1 - (1 - aggregate) * (1 - leftAnswer * rightAnswer) ∧ s'.regs (b + 18) = 2 ∧
      s'.regs (b + 10) = pref.length ∧
      IsPrefixBuffer (gm02RecursiveStackArr q) pref (9 + x.enc.length + 2 * x.n + cap) s' ∧
      s'.regs 330 = gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R) ∧
      s'.arrs (gm02RecursiveParentArr q + 4) = List.ofFn
        (fun i : Fin (gm02CompressedBoundaryInput x L R).n =>
          (compactEmb (gm02BoundaryDeletedSet x L R) i).val) ∧
      s'.regs (b + 6) = leftAnswer ∧
      (∀ offset : ℕ, 18 < offset → s'.regs (b + offset) = s.regs (b + offset)) := by
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  let stack := gm02RecursiveStackArr q
  let scratch := gm02RecursiveZeroArr q
  have hpg := gm02RecursiveParentArr_ge q
  have hbg := gm02RecursiveControlBase_ge q
  have hgeom : stack ≠ p ∧ stack ≠ 1 ∧ stack ≠ 2 ∧ scratch ≠ stack ∧
      p ≠ 1 ∧ p ≠ 2 ∧ (1 : Arr) ≠ 2 ∧ p ≠ scratch ∧ (1 : Arr) ≠ scratch ∧ (2 : Arr) ≠ scratch := by
    dsimp only [p, stack, scratch, gm02RecursiveStackArr, gm02RecursiveZeroArr, Arr] at *
    omega
  obtain ⟨s₁, t₁, he₁, ht₁, hP₁, hL₁, hR₁, hm₁, hc₁, ha₁, hl₁, hcat₁, hpos₁, hstack₁, hr₁⟩ :=
    gm02RestoreFrameProg_exec stack scratch p 1 2 b
      hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2.1
      hgeom.2.2.2.2.2.1 hgeom.2.2.2.2.2.2.1 hgeom.2.2.2.2.2.2.2.1
      hgeom.2.2.2.2.2.2.2.2.1 hgeom.2.2.2.2.2.2.2.2.2
      x.enc (bitSetList L) (bitSetList R) pref (phase + 2) code aggregate leftAnswer
      (gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R)) s
      (by omega) (by simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hframe)
      (x.enc_all_lt hn hlen) (bit_words L (by omega)) (bit_words R (by omega)) hheader hstack
      (by simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hpos)
  have hflag₁ : s₁.regs outReg = rightAnswer :=
    (hr₁ _ (by dsimp only [b, outReg, Reg] at *; omega)).trans hflag
  obtain ⟨s₂, t₂, he₂, ht₂, hcat₂, hout₂, _, horig₂, harr₂, hreg₂⟩ :=
    gm02RecursiveRestoreBoundaryProg_exec q x L R _ s₁ hP₁ hL₁ hR₁ hcat₁ hn hlen hcatw
  have hhigh₂ (offset : ℕ) : s₂.regs (b + offset) = s₁.regs (b + offset) := hreg₂ offset
  obtain ⟨s₃, he₃, hphase₃, hcode₃, hagg₃, hstate₃, harr₃, hreg₃⟩ :=
    gm02RecursiveAfterRightProg_exec q s₂ phase code aggregate leftAnswer rightAnswer
      ((hhigh₂ 3).trans hm₁) ((hhigh₂ 4).trans hc₁) ((hhigh₂ 5).trans ha₁) ((hhigh₂ 6).trans hl₁)
      (hout₂.trans hflag₁) hph ha hl hr hw hnext
  have hg : (.op .eq (.reg (b + 10)) (.const 0) : Expr).eval w s = some 0 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, b, hpos,
      checkWord_of_lt hframe, checkWord_of_lt (by omega : 0 < 2 ^ w)]
  have hi : (.op .eq (.reg outReg) (.const 2) : Expr).eval w s₁ = some 0 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, hflag₁, show rightAnswer ≠ 2 by omega,
      checkWord_of_lt (hr.trans_lt (by omega : 1 < 2 ^ w)),
      checkWord_of_lt (by omega : 2 < 2 ^ w), checkWord_of_lt (by omega : 0 < 2 ^ w)]
  have hm : (.op .lt (.reg (b + 3)) (.const 2) : Expr).eval w s₂ = some 0 := by
    have hm₂ : s₂.regs (b + 3) = phase + 2 := (hhigh₂ 3).trans hm₁
    simp [Expr.eval, BinOp.eval, BinOp.raw, hm₂, checkWord_of_lt (by omega : phase + 2 < 2 ^ w),
      checkWord_of_lt (by omega : 2 < 2 ^ w), checkWord_of_lt (by omega : 0 < 2 ^ w)]
  have he : Exec w (gm02RecursiveReturnProg q) s s₃ (3 + (t₁ + (3 + (t₂ + (3 + 22))))) :=
    Exec.ite_false hg (Exec.seq he₁ (Exec.ite_false hi (Exec.seq he₂ (Exec.ite_false hm he₃))))
  have hp₂ : s₂.arrs p = x.enc := (harr₂ p (Or.inl le_rfl)).trans hP₁
  have hL₂ : s₂.arrs 1 = bitSetList L := (harr₂ 1 (Or.inl (by dsimp only [p, Arr] at *; omega))).trans hL₁
  have hR₂ : s₂.arrs 2 = bitSetList R := (harr₂ 2 (Or.inl (by dsimp only [p, Arr] at *; omega))).trans hR₁
  refine ⟨s₃, _, he, ?_, (congrFun harr₃ p).trans hp₂, (congrFun harr₃ 1).trans hL₂,
    (congrFun harr₃ 2).trans hR₂, hphase₃, hcode₃, hagg₃, hstate₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [length_bitSetList] at ht₁
    omega
  · exact (hreg₃ (b + 10) (by simp; dsimp only [b, Reg] at *; omega)).trans ((hhigh₂ 10).trans hpos₁)
  · have hs₂ := hstack₁.of_arr_eq (harr₂ stack (Or.inr
      (by dsimp only [stack, gm02RecursiveStackArr, Arr]; omega)))
    simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hs₂.of_arr_eq (congrFun harr₃ stack)
  · exact (hreg₃ 330 (by simp; dsimp only [b, Reg] at *; omega)).trans hcat₂
  · exact (congrFun harr₃ _).trans horig₂
  · exact (hreg₃ (b + 6) (by simp; dsimp only [b, Reg] at *; omega)).trans
      ((hhigh₂ 6).trans hl₁)
  · intro offset hoff
    exact (hreg₃ _ (by simp; dsimp only [b, Reg] at *; omega)).trans
      ((hhigh₂ offset).trans (he₁.regs_eq_of_not_mem_writtenRegs
        (gm02RecursiveRestoreFrame_high_not_written q offset hoff)))

end GraphMinor.Compute
