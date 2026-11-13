module

public import GraphMinor.Compute.GM02RecursiveCallExecution
public import GraphMinor.Compute.GM02RecursiveReturnProgram

/-!
# Dispatching the right child after the left answer

Store the left feasibility bit and dispatch the current scheme's right
call. Its code is still the selected catalogue code, so fixed-range
dispatch reaches the proved exact child construction and frame push.
The new saved frame contains precisely that returned left answer.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- Record the returned left bit and start the same scheme's exact right-child call. -/
theorem gm02RecursiveAfterLeftProg_exec {w cap : ℕ} (q : ℕ)
    (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n))
    (C : (gm02CompressedBoundaryInput x L R).schemes) (pref : List ℕ)
    (phase aggregate leftAnswer : ℕ) (s : State)
    (hparent : s.arrs (gm02RecursiveParentArr q) = x.enc) (hlen : x.enc.length < 2 ^ w)
    (hL : s.arrs 1 = bitSetList L) (hR : s.arrs 2 = bitSetList R)
    (hB : (gm02CompressedBoundaryInput x L R).n ≤ gm02RecursiveBoundaryBound q)
    (hn : x.n < 2 ^ w) (hNW : gm02RecursiveBoundaryBound q + 1 < 2 ^ w)
    (hCW : gm02RecursiveCodeBound q + 1 < 2 ^ w)
    (horig : s.arrs (gm02RecursiveParentArr q + 4) = List.ofFn
      (fun i : Fin (gm02CompressedBoundaryInput x L R).n =>
        (compactEmb (gm02BoundaryDeletedSet x L R) i).val))
    (hcat : s.regs 330 = gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q)
      (gm02CompressedBoundaryInput x L R))
    (hcodes : 2 ^ gm02RecursiveCodeBound q ≤ 2 ^ w)
    (hchild : 8 + 2 * (edgeListOf x.G).length +
      2 * C.right.index < 2 ^ w)
    (hclen : (gm02RecursiveChosenInput true x L R C).enc.length < 2 ^ w)
    (hcn : (gm02RecursiveChosenInput true x L R C).n < 2 ^ w)
    (hphase : s.regs (gm02RecursiveControlBase q + 3) = phase) (hph : phase ≤ 1)
    (hcode : s.regs (gm02RecursiveControlBase q + 4) =
      gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C)
    (hagg : s.regs (gm02RecursiveControlBase q + 5) = aggregate)
    (hleft : s.regs outReg = leftAnswer)
    (ha : aggregate ≤ 1) (hl : leftAnswer ≤ 1) (hw : 3 < 2 ^ w)
    (hframe : pref.length + 9 + x.enc.length + 2 * x.n < 2 ^ w)
    (hstack : IsPrefixBuffer (gm02RecursiveStackArr q) pref
      (9 + x.enc.length + 2 * x.n + cap) s)
    (hpos : s.regs (gm02RecursiveControlBase q + 10) = pref.length) :
    let child := gm02RecursiveChosenInput true x L R C
    let code := gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C
    let catalogue := gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R)
    let tag := phase + 2
    let b := gm02RecursiveControlBase q
    ∃ s' t, Exec w (gm02RecursiveAfterLeftProg q) s s' t ∧
      t ≤ 378 + 28 * x.A.index + 73 * gm02RecursiveBoundaryBound q +
        x.n * (143 + 28 * gm02RecursiveBoundaryBound q) + 166 * (edgeListOf x.G).length +
        8 * (gm02RecursiveCodeBound q + 1) + 4 * (gm02RecursiveBoundaryBound q + 1) +
        17 * (x.enc.length + 2 * x.n) + 16 * child.enc.length ∧
      IsPrefixBuffer (gm02RecursiveStackArr q)
        (pref ++ gm02SavedFrameWords x.enc (bitSetList L) (bitSetList R)
          tag code aggregate leftAnswer catalogue pref.length) cap s' ∧
      s'.arrs (gm02RecursiveParentArr q) = child.enc ∧ s'.arrs 1 = bitSetList L ∧ s'.arrs 2 = bitSetList R ∧
      s'.regs (b + 10) = pref.length + 9 + x.enc.length + 2 * x.n ∧
      s'.regs (b + 3) = 1 - phase ∧ s'.regs (b + 18) = 1 ∧
      (∀ offset : ℕ, 18 < offset → s'.regs (b + offset) = s.regs (b + offset)) := by
  let b := gm02RecursiveControlBase q
  have hbg := gm02RecursiveControlBase_ge q
  let s₁ := s.setReg (b + 6) leftAnswer
  have he₁ : Exec w (.assign (b + 6) (.reg outReg)) s s₁ 2 :=
    Exec.assign (by simp [Expr.eval, hleft, checkWord_of_lt (hl.trans_lt (by omega : 1 < 2 ^ w))])
  have hs₁ (offset : ℕ) (ho : offset ≠ 6) : s₁.regs (b + offset) = s.regs (b + offset) :=
    State.setReg_regs_ne _ _ (by dsimp only [Reg] at *; omega)
  obtain ⟨s₂, t₂, he₂, ht₂, hstack₂, hchild₂, hL₂, hR₂, hpos₂, hphase₂, hstate₂, hhigh₂⟩ :=
    gm02RecursiveCallProg_exec true q x L R C pref phase aggregate leftAnswer s₁
      hparent hlen hL hR hB hn hNW hCW horig
      ((State.setReg_regs_ne _ _ (by dsimp only [b, Reg] at *; omega)).trans hcat)
      hcodes hchild hclen hcn ((hs₁ 3 (by decide)).trans hphase) hph
      ((hs₁ 4 (by decide)).trans hcode) ((hs₁ 5 (by decide)).trans hagg)
      (by simp [s₁, b]) ha hl hw hframe hstack ((hs₁ 10 (by decide)).trans hpos)
  have hcode₁ : s₁.regs (b + 4) = gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C :=
    (hs₁ 4 (by decide)).trans hcode
  have hposK : 0 < gm02RecursiveCodeBound q := gm02BoundarySchemeCodeBound_pos _
  have hcodeK : s₁.regs (b + 4) < gm02RecursiveCodeBound q := by
    rw [hcode₁]
    exact gm02BoundarySchemeCode_lt_bound _ hB C
  have hcall : Exec w (gm02RecursiveCallProg true q (s₁.regs (b + 4))) s₁ s₂ t₂ := by
    simpa only [hcode₁] using he₂
  obtain ⟨t₃, he₃, ht₃⟩ := branchValProg_exec (b + 4) (gm02RecursiveCallProg true q)
    (gm02RecursiveCodeBound q - 1) (by omega) (by omega) hcall
  refine ⟨s₂, 2 + t₃, Exec.seq he₁ he₃, by omega, hstack₂, hchild₂, hL₂, hR₂, hpos₂,
    hphase₂, hstate₂, ?_⟩
  intro offset hoff
  exact (hhigh₂ offset hoff).trans (hs₁ offset (by omega))

end GraphMinor.Compute
