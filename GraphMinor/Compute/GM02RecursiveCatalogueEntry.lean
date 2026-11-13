module

public import GraphMinor.Compute.GM02RecursiveScanInit
public import GraphMinor.Compute.GM02RecursiveSides

/-!
# Entering the scheme scan after separator success

The side arrays returned by separator search determine the compressed
boundary. Its size is bounded by seven times the fixed width. Execute
the catalogue program on these arrays, then initialize the scan words.
This connects the actual catalogue computation to the recursive control
state without changing the retained parent or saved stack.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- Catalogue generation followed by scan initialization keeps the exact parent data. -/
theorem gm02RecursiveCatalogueEntry_exec {w : ℕ} (q : ℕ) (allVertices : Bool)
    (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n)) (s : State)
    (hsrc : s.arrs (gm02RecursiveParentArr q) = x.enc)
    (hleft : s.arrs outArr = gm02VertexBits L) (hright : s.arrs 2 = gm02VertexBits R)
    (hvalid : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) (hindex : x.A.index ≤ 3 * q)
    (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w)
    (hwords : (7 * q) * (7 * q) + 7 * q + 2 < 2 ^ w)
    (hdepth : 3 + 3 * (7 * q) < 2 ^ w)
    (hcodes : 2 ^ gm02BoundarySchemeCodeBound (7 * q) ≤ 2 ^ w) :
    let p := gm02RecursiveParentArr q
    let b := gm02RecursiveControlBase q
    let B := gm02CompressedBoundaryInput x L R
    ∃ s' t, Exec w (.seq (gm02BoundaryCatalogueFromParentProg (gm02RecursiveBoundaryBound q) p)
        (gm02RecursiveScanInitProg q)) s s' t ∧
      t ≤ 150 * x.n + 200 * x.A.index + 358 +
        (4 + 3 * (7 * q)) * (4 * ((7 * q) * (7 * q) + 7 * q + 1) + 10) ∧
      s'.regs 330 = gm02BoundarySchemeSetCode (7 * q) B ∧
      s'.arrs (p + 4) = List.ofFn (fun i : Fin B.n =>
        (compactEmb (gm02BoundaryDeletedSet x L R) i).val) ∧
      s'.regs (b + 4) = 0 ∧ s'.regs (b + 5) = 0 ∧ s'.regs (b + 6) = 0 ∧
      s'.regs (b + 18) = 2 ∧
      (∀ j, j ≤ p ∨ p + 12 < j → s'.arrs j = s.arrs j) ∧
      (∀ offset : ℕ, offset ≠ 4 → offset ≠ 5 → offset ≠ 6 → offset ≠ 18 →
        s'.regs (b + offset) = s.regs (b + offset)) := by
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  have hpg := gm02RecursiveParentArr_ge q
  have hbg := gm02RecursiveControlBase_ge q
  have hbound := gm02RecursiveSides_boundary_bound allVertices x q L R hindex hvalid
  obtain ⟨s₁, t₁, he₁, ht₁, hcat, _, horig, ha₁, hr₁⟩ :=
    gm02BoundaryCatalogueFromParentProg_exec x L R p
      (by dsimp only [p, Arr] at *; omega) s hsrc
      (hleft.trans (gm02VertexBits_eq_bitSetList L))
      (hright.trans (gm02VertexBits_eq_bitSetList R)) hn hlen hbound hwords hdepth hcodes
  obtain ⟨s₂, he₂, hcode, hagg, hleftAns, hstate, ha₂, hr₂⟩ :=
    gm02RecursiveScanInitProg_exec (w := w) q s₁ (by omega)
  refine ⟨s₂, t₁ + 8, Exec.seq he₁ he₂, by omega, ?_, ?_, hcode, hagg, hleftAns, hstate, ?_, ?_⟩
  · exact (hr₂ 330 (by simp; dsimp only [Reg] at *; omega)).trans hcat
  · exact (congrFun ha₂ _).trans horig
  · intro j hj
    exact (congrFun ha₂ j).trans (ha₁ j hj)
  · intro offset h4 h5 h6 h18
    have hneq : b + offset ∉ [gm02RecursiveControlBase q + 4, gm02RecursiveControlBase q + 5,
        gm02RecursiveControlBase q + 6, gm02RecursiveControlBase q + 18] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
      dsimp only [b, Reg] at *
      omega
    exact (hr₂ _ hneq).trans (hr₁ _ (by dsimp only [b, Reg] at *; omega))

end GraphMinor.Compute
