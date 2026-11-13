module

public import GraphMinor.Compute.GM02RecursivePrefixBase
public import GraphMinor.Compute.GM02RecursiveEnterLarge
public import GraphMinor.Compute.GM02RecursiveInstanceWords
public import GraphMinor.Compute.GM02RecursiveLocalTime

/-!
# Entering either phase inside the recursive loop

Use exhaustion on a small current input and the phase-selected separator
otherwise. One actual loop step therefore reaches a correct return state
or the exact initialized scheme scan. The same width-dependent overhead
polynomial covers both branches under any supplied vertex bound.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- One entry prefix reaches a correct answer or the complete initialized catalogue scan. -/
theorem gm02RecursivePrefix_enter {w : ℕ} (q root n : ℕ) (phase : Bool)
    (x : GM02SimpleTerminatedInput) (s : State) (hx : x.n ≤ n) (hnroot : n ≤ root)
    (hsrc : s.arrs (gm02RecursiveParentArr q) = x.enc)
    (hphase : s.regs (gm02RecursiveControlBase q + 3) = if phase then 1 else 0)
    (hindex : if phase then x.A.index ≤ 3 * q else 2 * x.A.index ≤ 5 * q)
    (hstate : s.regs (gm02RecursiveControlBase q + 18) = 1)
    (hw : wordSize (gm02RecursiveWordConstant q) root ≤ w) :
    let p := gm02RecursiveParentArr q
    let b := gm02RecursiveControlBase q
    ∃ s' t, GM02LoopPrefix w (.reg (b + 18)) (gm02RecursiveMachineStepProg q) s s' t ∧
      t ≤ gm02RecursiveTimeCoefficient q * (n + 1) ^ (q + 3) ∧
      ((s'.regs (b + 18) = 3 ∧ x.recursiveCorrect q s') ∨
        (s'.regs (b + 18) = 2 ∧ s'.regs (b + 4) = 0 ∧ s'.regs (b + 5) = 0 ∧ s'.regs (b + 6) = 0 ∧
          ∃ L R : Finset (Fin x.n), s'.arrs outArr = gm02VertexBits L ∧ s'.arrs 2 = gm02VertexBits R ∧
            (gm02RecursiveSeparatorInput (!phase) x).validSides (q : ℤ) (gm02VertexBits L) (gm02VertexBits R) ∧
            s'.regs 330 = gm02BoundarySchemeSetCode (7 * q) (gm02CompressedBoundaryInput x L R) ∧
            s'.arrs (p + 4) = List.ofFn (fun i : Fin (gm02CompressedBoundaryInput x L R).n =>
              (compactEmb (gm02BoundaryDeletedSet x L R) i).val))) ∧
      s'.arrs p = x.enc ∧ s'.arrs (gm02RecursiveStackArr q) = s.arrs (gm02RecursiveStackArr q) ∧
      (∀ offset : ℕ, offset ≠ 4 → offset ≠ 5 → offset ≠ 6 → offset ≠ 18 → offset ≠ 22 →
        s'.regs (b + offset) = s.regs (b + offset)) := by
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  have hP1 : 1 ≤ (n + 1) ^ (q + 3) := Nat.one_le_pow _ _ (by omega)
  by_cases hsmall : x.n ≤ 4 * q
  · obtain ⟨s₁, t₁, he₁, ht₁, hout, hstate₁, ha₁, hr₁⟩ :=
      gm02RecursivePrefix_base q root x s hsrc hsmall hstate hw
    refine ⟨s₁, t₁, he₁, ?_, Or.inl ⟨hstate₁, hout⟩,
      (congrFun ha₁ p).trans hsrc, congrFun ha₁ _, ?_⟩
    · exact ht₁.trans ((gm02RecursiveTimeCoefficient_base q).1.trans
        (Nat.le_mul_of_pos_right _ hP1))
    · intro offset _ _ _ h18 h22
      exact hr₁ offset h18 h22
  · have hlarge : 4 * q < x.n := by omega
    have hidx : x.A.index ≤ 3 * q := by cases phase <;> simp only [Bool.false_eq_true, ↓reduceIte] at hindex <;> omega
    obtain ⟨h4, _, hwords, hdepth, _, _, hcodes, _⟩ := gm02Recursive_fixed_wordBounds q root w hw
    obtain ⟨hn, hlen, hsep, hn3, hb, hp, _⟩ :=
      gm02Recursive_instance_wordBounds q root w x (hx.trans hnroot) hw
    have hphase' : s.regs (b + 3) = if !phase then 0 else 1 := by
      cases phase <;> simpa only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using hphase
    obtain ⟨s₁, t₁, he₁, ht₁, hout, hsrc₁, hstack₁, hr₁⟩ :=
      gm02RecursiveEnterProg_large_exec q (!phase) x s hsrc hphase' hlarge hidx
        h4 hlen hsep hn3 hb hp hwords hdepth hcodes
    have hg : (.op .eq (.reg (b + 18)) (.const 1) : Expr).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, b, hstate, checkWord_of_lt (by omega : 1 < 2 ^ w)]
    have he : Exec w (gm02RecursiveMachineStepProg q) s s₁ (3 + t₁) :=
      Exec.ite_true (v := 1) hg (by decide) he₁
    have hguard : (.reg (b + 18) : Expr).eval w s = some 1 := by
      simp [Expr.eval, b, hstate, checkWord_of_lt (by omega : 1 < 2 ^ w)]
    refine ⟨s₁, 1 + (3 + t₁), GM02LoopPrefix.single hguard (by decide) he, ?_, ?_, hsrc₁, hstack₁, ?_⟩
    · have hpow := Nat.mul_le_mul_left (10000 * (q + 1) ^ 2 + 155)
        (Nat.pow_le_pow_left (Nat.add_le_add_right hx 1) (q + 3))
      have hlinear : 150 * x.n ≤ 150 * n := Nat.mul_le_mul_left _ hx
      have hcost : 1 + (3 + t₁) ≤ gm02RecursiveLocalTime q n := by
        dsimp only [gm02RecursiveLocalTime, gm02RecursiveCatalogueTime, gm02RecursiveBoundaryBound]
        omega
      exact hcost.trans (gm02RecursiveLocalTime_le q n)
    · rcases hout with ⟨hrun, hflag, hwidth⟩ | hscan
      · exact Or.inl ⟨hrun, Or.inr (Or.inr ⟨hflag, hwidth⟩)⟩
      · exact Or.inr hscan
    · intro offset h4 h5 h6 h18 _
      exact hr₁ offset h4 h5 h6 h18

end GraphMinor.Compute
