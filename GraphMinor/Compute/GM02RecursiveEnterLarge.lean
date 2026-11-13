module

public import GraphMinor.Compute.GM02RecursiveSeparatorSelect
public import GraphMinor.Compute.GM02RecursiveCatalogueEntry

/-!
# Executing non-base entry into A1 or A2

For a graph larger than the exhaustive bound, run the selected balanced
separator query. A rejection gives the proved width report. A successful
query gives actual side bits, from which the program computes the full
crossing-scheme catalogue and enters its scan. Parent input, saved stack,
and the other recursive control words are preserved in both cases.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- Non-base entry returns a valid width report or initializes the complete scheme scan. -/
theorem gm02RecursiveEnterProg_large_exec {w : ℕ} (q : ℕ) (allVertices : Bool)
    (x : GM02SimpleTerminatedInput) (s : State)
    (hsrc : s.arrs (gm02RecursiveParentArr q) = x.enc)
    (hphase : s.regs (gm02RecursiveControlBase q + 3) = if allVertices then 0 else 1)
    (hlarge : 4 * q < x.n) (hindex : x.A.index ≤ 3 * q)
    (hw : 4 < 2 ^ w) (hlen : x.enc.length < 2 ^ w)
    (hsep : 2 + 2 * (edgeListOf x.G).length + x.n < 2 ^ w)
    (hn : 3 * x.n < 2 ^ w) (hb : x.n + 1 < 2 ^ w) (hp : (x.n + 1) ^ q < 2 ^ w)
    (hwords : (7 * q) * (7 * q) + 7 * q + 2 < 2 ^ w)
    (hdepth : 3 + 3 * (7 * q) < 2 ^ w)
    (hcodes : 2 ^ gm02BoundarySchemeCodeBound (7 * q) ≤ 2 ^ w) :
    let p := gm02RecursiveParentArr q
    let b := gm02RecursiveControlBase q
    ∃ s' t, Exec w (gm02RecursiveEnterProg q) s s' t ∧
      t ≤ (10000 * (q + 1) ^ 2 + 155) * (x.n + 1) ^ (q + 3) +
        150 * x.n + 200 * x.A.index + 370 +
        (4 + 3 * (7 * q)) * (4 * ((7 * q) * (7 * q) + 7 * q + 1) + 10) ∧
      ((s'.regs (b + 18) = 3 ∧ s'.regs outReg = 2 ∧ q ≤ x.width) ∨
        (s'.regs (b + 18) = 2 ∧ s'.regs (b + 4) = 0 ∧
          s'.regs (b + 5) = 0 ∧ s'.regs (b + 6) = 0 ∧
          ∃ L R : Finset (Fin x.n),
            s'.arrs outArr = gm02VertexBits L ∧ s'.arrs 2 = gm02VertexBits R ∧
            (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
              (gm02VertexBits L) (gm02VertexBits R) ∧
            s'.regs 330 = gm02BoundarySchemeSetCode (7 * q) (gm02CompressedBoundaryInput x L R) ∧
            s'.arrs (p + 4) = List.ofFn (fun i : Fin (gm02CompressedBoundaryInput x L R).n =>
              (compactEmb (gm02BoundaryDeletedSet x L R) i).val))) ∧
      s'.arrs p = x.enc ∧ s'.arrs (gm02RecursiveStackArr q) = s.arrs (gm02RecursiveStackArr q) ∧
      (∀ offset : ℕ, offset ≠ 4 → offset ≠ 5 → offset ≠ 6 → offset ≠ 18 →
        s'.regs (b + offset) = s.regs (b + offset)) := by
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  have hbg := gm02RecursiveControlBase_ge q
  have hpg := gm02RecursiveParentArr_ge q
  have hn' : x.n < 2 ^ w := by omega
  have hg : (.op .le (.read p (.const 0)) (.const (4 * q)) : Expr).eval w s = some 0 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, hsrc, p, GM02SimpleTerminatedInput.enc,
      encGraph, checkWord_of_lt (by omega : 0 < 2 ^ w), checkWord_of_lt hn',
      checkWord_of_lt (by omega : 4 * q < 2 ^ w), Nat.not_le.mpr hlarge]
  obtain ⟨s₁, t₁, he₁, ht₁, hout, ha₁, hr₁⟩ :=
    gm02RecursiveSeparatorSelectProg_exec q allVertices x s hsrc hphase hw hlen hsep hn hb hp
  have hsrc₁ : s₁.arrs p = x.enc := (ha₁ 0 (by decide) (by decide)).trans hsrc
  have hstack₁ : s₁.arrs (gm02RecursiveStackArr q) = s.arrs (gm02RecursiveStackArr q) :=
    ha₁ 40 (by decide) (by decide)
  rcases hout with ⟨hflag, hwidth⟩ | ⟨hflag, L, R, hL, hR, hvalid⟩
  · let s₂ := s₁.setReg (b + 18) 3
    have he₂ : Exec w (.assign (b + 18) (.const 3)) s₁ s₂ 2 :=
      Exec.assign (checkWord_of_lt (by omega))
    have hi : (.op .eq (.reg outReg) (.const 2) : Expr).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, hflag,
        checkWord_of_lt (by omega : 2 < 2 ^ w), checkWord_of_lt (by omega : 1 < 2 ^ w)]
    have he : Exec w (gm02RecursiveEnterProg q) s s₂ (4 + (t₁ + (3 + 2))) :=
      Exec.ite_false hg (Exec.seq he₁ (Exec.ite_true (v := 1) hi (by decide) he₂))
    refine ⟨s₂, _, he, by omega, Or.inl ⟨by simp [s₂, b], ?_, hwidth⟩, hsrc₁, hstack₁, ?_⟩
    · exact (State.setReg_regs_ne _ _ (by dsimp only [b, Reg, outReg] at *; omega)).trans hflag
    · intro offset _ _ _ h18
      exact (State.setReg_regs_ne _ _ (by dsimp only [Reg] at *; omega)).trans (hr₁ offset)
  · have hv : (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
        (gm02VertexBits L) (gm02VertexBits R) := by simpa only [hL, hR] using hvalid
    obtain ⟨s₂, t₂, he₂, ht₂, hcat, horig, hcode, hagg, hleft, hstate, ha₂, hr₂⟩ :=
      gm02RecursiveCatalogueEntry_exec q allVertices x L R s₁ hsrc₁ hL hR hv hindex
        hn' hlen hwords hdepth hcodes
    have hi : (.op .eq (.reg outReg) (.const 2) : Expr).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, hflag,
        checkWord_of_lt (by omega : 2 < 2 ^ w), checkWord_of_lt (by omega : 1 < 2 ^ w)]
    have he : Exec w (gm02RecursiveEnterProg q) s s₂ (4 + (t₁ + (3 + t₂))) :=
      Exec.ite_false hg (Exec.seq he₁ (Exec.ite_false hi he₂))
    refine ⟨s₂, _, he, by omega, Or.inr ⟨hstate, hcode, hagg, hleft, L, R, ?_, ?_, hv, hcat, horig⟩,
      ?_, ?_, ?_⟩
    · exact (ha₂ outArr (Or.inl (by dsimp only [p, outArr, Arr] at *; omega))).trans hL
    · exact (ha₂ 2 (Or.inl (by dsimp only [p, Arr] at *; omega))).trans hR
    · exact (ha₂ p (Or.inl le_rfl)).trans hsrc₁
    · exact (ha₂ _ (Or.inr (by dsimp only [gm02RecursiveStackArr, p, Arr]; omega))).trans hstack₁
    · intro offset h4 h5 h6 h18
      exact (hr₂ offset h4 h5 h6 h18).trans (hr₁ offset)

end GraphMinor.Compute
