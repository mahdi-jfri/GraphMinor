module

public import GraphMinor.Compute.GM02RecursiveAfterLeftExecution
public import GraphMinor.Compute.GM02RecursiveRestoreBoundary
public import GraphMinor.Compute.GM02RecursiveFrameWrites
public import GraphMinor.Compute.GM02TerminatedWords

/-!
# Returning a left-child answer and starting its right sibling

Restore the saved parent and its boundary names, retain the child's
feasibility bit, and run the matching right-child continuation. The
parent frame is replaced by a right-return frame containing that exact
left answer. The older stack and root metadata remain unchanged.
-/

public section
namespace GraphMinor.Compute
open Classical

private theorem bit_words {w n : ℕ} (S : Finset (Fin n)) (hw : 1 < 2 ^ w) :
    ∀ v ∈ bitSetList S, v < 2 ^ w := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  exact (getElem_bitSetList_le_one S i hi).trans_lt hw

/-- An ordinary left answer starts the exact right child with the updated saved continuation. -/
theorem gm02RecursiveReturnProg_left_exec {w cap : ℕ} (q : ℕ)
    (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n))
    (C : (gm02CompressedBoundaryInput x L R).schemes) (pref : List ℕ)
    (phase aggregate oldLeftAnswer leftAnswer : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w)
    (hframe : pref.length + 9 + x.enc.length + 2 * x.n < 2 ^ w)
    (hph : phase ≤ 1) (ha : aggregate ≤ 1) (hl : leftAnswer ≤ 1)
    (hB : (gm02CompressedBoundaryInput x L R).n ≤ gm02RecursiveBoundaryBound q)
    (hNW : gm02RecursiveBoundaryBound q + 1 < 2 ^ w) (hCW : gm02RecursiveCodeBound q + 1 < 2 ^ w)
    (hcodes : 2 ^ gm02RecursiveCodeBound q ≤ 2 ^ w)
    (hchild : 8 + 2 * (edgeListOf x.G).length + 2 * C.right.index < 2 ^ w)
    (hclen : (gm02RecursiveChosenInput true x L R C).enc.length < 2 ^ w)
    (hcn : (gm02RecursiveChosenInput true x L R C).n < 2 ^ w)
    (hheader : ∀ v ∈ gm02SavedFrameHeader x.enc (bitSetList L) (bitSetList R)
      phase (gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C) aggregate oldLeftAnswer
      (gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R)), v < 2 ^ w)
    (hstack : s.arrs (gm02RecursiveStackArr q) = pref ++
      gm02SavedFrameWords x.enc (bitSetList L) (bitSetList R) phase
        (gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C) aggregate oldLeftAnswer
        (gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R))
        pref.length ++ List.replicate cap 0)
    (hpos : s.regs (gm02RecursiveControlBase q + 10) = pref.length + 9 + x.enc.length + 2 * x.n)
    (hflag : s.regs outReg = leftAnswer) :
    let b := gm02RecursiveControlBase q
    let child := gm02RecursiveChosenInput true x L R C
    ∃ s' t, Exec w (gm02RecursiveReturnProg q) s s' t ∧
      t ≤ 51 * (x.enc.length + 2 * x.n) + 63 * x.n + 56 * x.A.index +
        73 * gm02RecursiveBoundaryBound q + x.n * (143 + 28 * gm02RecursiveBoundaryBound q) +
        166 * (edgeListOf x.G).length + 8 * (gm02RecursiveCodeBound q + 1) +
        4 * (gm02RecursiveBoundaryBound q + 1) + 16 * child.enc.length + 750 ∧
      IsPrefixBuffer (gm02RecursiveStackArr q)
        (pref ++ gm02SavedFrameWords x.enc (bitSetList L) (bitSetList R) (phase + 2)
          (gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C) aggregate leftAnswer
          (gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R))
          pref.length) cap s' ∧
      s'.arrs (gm02RecursiveParentArr q) = child.enc ∧ s'.arrs 1 = bitSetList L ∧ s'.arrs 2 = bitSetList R ∧
      s'.regs (b + 10) = pref.length + 9 + x.enc.length + 2 * x.n ∧
      s'.regs (b + 3) = 1 - phase ∧ s'.regs (b + 18) = 1 ∧
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
  obtain ⟨s₁, t₁, he₁, ht₁, hP₁, hL₁, hR₁, hm₁, hc₁, ha₁, _, hcat₁, hpos₁, hstack₁, hr₁⟩ :=
    gm02RestoreFrameProg_exec stack scratch p 1 2 b
      hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2.1
      hgeom.2.2.2.2.2.1 hgeom.2.2.2.2.2.2.1 hgeom.2.2.2.2.2.2.2.1
      hgeom.2.2.2.2.2.2.2.2.1 hgeom.2.2.2.2.2.2.2.2.2
      x.enc (bitSetList L) (bitSetList R) pref phase
      (gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C) aggregate oldLeftAnswer
      (gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R)) s
      (by omega) (by simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hframe)
      (x.enc_all_lt hn hlen) (bit_words L (by omega)) (bit_words R (by omega)) hheader hstack
      (by simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hpos)
  have hflag₁ : s₁.regs outReg = leftAnswer :=
    (hr₁ _ (by dsimp only [b, outReg, Reg] at *; omega)).trans hflag
  have hcatw := (gm02BoundarySchemeSetCode_lt (gm02RecursiveBoundaryBound q)
    (gm02CompressedBoundaryInput x L R)).trans_le hcodes
  obtain ⟨s₂, t₂, he₂, ht₂, hcat₂, hout₂, _, horig₂, harr₂, hreg₂⟩ :=
    gm02RecursiveRestoreBoundaryProg_exec q x L R _ s₁ hP₁ hL₁ hR₁ hcat₁ hn hlen hcatw
  have hhigh₂ (offset : ℕ) : s₂.regs (b + offset) = s₁.regs (b + offset) := hreg₂ offset
  have hp₂ : s₂.arrs p = x.enc := (harr₂ p (Or.inl le_rfl)).trans hP₁
  have hL₂ : s₂.arrs 1 = bitSetList L := (harr₂ 1 (Or.inl (by dsimp only [p, Arr] at *; omega))).trans hL₁
  have hR₂ : s₂.arrs 2 = bitSetList R := (harr₂ 2 (Or.inl (by dsimp only [p, Arr] at *; omega))).trans hR₁
  have hstack₂ := hstack₁.of_arr_eq (harr₂ stack (Or.inr
    (by dsimp only [stack, gm02RecursiveStackArr, Arr]; omega)))
  obtain ⟨s₃, t₃, he₃, ht₃, hstack₃, hchild₃, hL₃, hR₃, hpos₃, hphase₃, hstate₃, hhigh₃⟩ :=
    gm02RecursiveAfterLeftProg_exec q x L R C pref phase aggregate leftAnswer s₂
      hp₂ hlen hL₂ hR₂ hB hn hNW hCW horig₂ hcat₂ hcodes hchild hclen hcn
      ((hhigh₂ 3).trans hm₁) hph ((hhigh₂ 4).trans hc₁) ((hhigh₂ 5).trans ha₁)
      (hout₂.trans hflag₁) ha hl hw hframe
      (by simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hstack₂)
      ((hhigh₂ 10).trans hpos₁)
  have hg : (.op .eq (.reg (b + 10)) (.const 0) : Expr).eval w s = some 0 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, b, hpos,
      checkWord_of_lt hframe, checkWord_of_lt (by omega : 0 < 2 ^ w)]
  have hi : (.op .eq (.reg outReg) (.const 2) : Expr).eval w s₁ = some 0 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, hflag₁, show leftAnswer ≠ 2 by omega,
      checkWord_of_lt (hl.trans_lt (by omega : 1 < 2 ^ w)),
      checkWord_of_lt (by omega : 2 < 2 ^ w), checkWord_of_lt (by omega : 0 < 2 ^ w)]
  have hm : (.op .lt (.reg (b + 3)) (.const 2) : Expr).eval w s₂ = some 1 := by
    have hm₂ : s₂.regs (b + 3) = phase := (hhigh₂ 3).trans hm₁
    simp [Expr.eval, BinOp.eval, BinOp.raw, hm₂, show phase < 2 by omega,
      checkWord_of_lt (hph.trans_lt (by omega : 1 < 2 ^ w)),
      checkWord_of_lt (by omega : 2 < 2 ^ w), checkWord_of_lt (by omega : 1 < 2 ^ w)]
  have he : Exec w (gm02RecursiveReturnProg q) s s₃ (3 + (t₁ + (3 + (t₂ + (3 + t₃))))) :=
    Exec.ite_false hg (Exec.seq he₁ (Exec.ite_false hi (Exec.seq he₂ (Exec.ite_true (v := 1) hm (by decide) he₃))))
  refine ⟨s₃, _, he, ?_, hstack₃, hchild₃, hL₃, hR₃, hpos₃, hphase₃, hstate₃, ?_⟩
  · simp only [length_bitSetList] at ht₁
    omega
  · intro offset hoff
    exact (hhigh₃ offset hoff).trans ((hhigh₂ offset).trans
      (he₁.regs_eq_of_not_mem_writtenRegs (gm02RecursiveRestoreFrame_high_not_written q offset hoff)))

end GraphMinor.Compute
