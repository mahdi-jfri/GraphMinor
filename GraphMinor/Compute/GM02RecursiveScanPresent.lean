module

public import GraphMinor.Compute.GM02RecursiveCallExecution
public import GraphMinor.Compute.GM02RecursiveScanProgram

/-!
# Starting the left call for a present catalogue code

The scan index selects a fixed branch, whose catalogue bit is one for
the given crossing scheme. Dispatch and that bit test therefore reach
the exact left-child call, with only bounded fixed-range overhead.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- A present scheme code starts its exact left recursive call through the full scan command. -/
theorem gm02RecursiveScanProg_present_exec {w cap : ℕ} (q : ℕ)
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
      2 * C.left.index < 2 ^ w)
    (hclen : (gm02RecursiveChosenInput false x L R C).enc.length < 2 ^ w)
    (hcn : (gm02RecursiveChosenInput false x L R C).n < 2 ^ w)
    (hphase : s.regs (gm02RecursiveControlBase q + 3) = phase) (hph : phase ≤ 1)
    (hcode : s.regs (gm02RecursiveControlBase q + 4) =
      gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C)
    (hagg : s.regs (gm02RecursiveControlBase q + 5) = aggregate)
    (hleft : s.regs (gm02RecursiveControlBase q + 6) = leftAnswer)
    (ha : aggregate ≤ 1) (hl : leftAnswer ≤ 1) (hw : 3 < 2 ^ w)
    (hframe : pref.length + 9 + x.enc.length + 2 * x.n < 2 ^ w)
    (hstack : IsPrefixBuffer (gm02RecursiveStackArr q) pref
      (9 + x.enc.length + 2 * x.n + cap) s)
    (hpos : s.regs (gm02RecursiveControlBase q + 10) = pref.length) :
    let child := gm02RecursiveChosenInput false x L R C
    let code := gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C
    let catalogue := gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R)
    let tag := phase
    let b := gm02RecursiveControlBase q
    ∃ s' t, Exec w (gm02RecursiveScanProg q) s s' t ∧
      t ≤ 384 + 28 * x.A.index + 73 * gm02RecursiveBoundaryBound q +
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
  let K := gm02RecursiveCodeBound q
  let B := gm02CompressedBoundaryInput x L R
  let code := gm02BoundarySchemeCode B C
  have hcodeK : code < K := gm02BoundarySchemeCode_lt_bound _ hB C
  have hKpos : 0 < K := gm02BoundarySchemeCodeBound_pos _
  have hKw : K < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hstack₁, hchild₁, hL₁, hR₁, hpos₁, hphase₁, hstate₁, hhigh₁⟩ :=
    gm02RecursiveCallProg_exec false q x L R C pref phase aggregate leftAnswer s
      hparent hlen hL hR hB hn hNW hCW horig hcat hcodes hchild hclen hcn hphase hph
      hcode hagg hleft ha hl hw hframe hstack hpos
  have hbit : (gm02CatalogueBitExpr code).eval w s = some 1 :=
    (gm02CatalogueBitExpr_valid B ⟨code, hcodeK⟩ s hcat hcodes (by omega)).mpr ⟨C, rfl⟩
  have hc : Exec w (gm02RecursiveScanCodeProg q code) s s₁ (5 + t₁) :=
    Exec.ite_true (v := 1) hbit (by decide) he₁
  have hcode' : s.regs (b + 4) = code := hcode
  have hc' : Exec w (gm02RecursiveScanCodeProg q (s.regs (b + 4))) s s₁ (5 + t₁) := by
    simpa only [hcode'] using hc
  obtain ⟨t₂, he₂, ht₂⟩ := branchValProg_exec (b + 4) (gm02RecursiveScanCodeProg q) (K - 1)
    (by rw [hcode']; omega) (by omega) hc'
  have hg : (.op .lt (.reg (b + 4)) (.const K) : Expr).eval w s = some 1 := by
    have hcw : code < 2 ^ w := hcodeK.trans hKw
    simp [Expr.eval, BinOp.eval, BinOp.raw, hcode', checkWord_of_lt hcw,
      checkWord_of_lt hKw, hcodeK, checkWord_of_lt (by omega : 1 < 2 ^ w)]
  refine ⟨s₁, 3 + t₂, Exec.ite_true (v := 1) hg (by decide) he₂, by omega,
    hstack₁, hchild₁, hL₁, hR₁, hpos₁, hphase₁, hstate₁, hhigh₁⟩

end GraphMinor.Compute
