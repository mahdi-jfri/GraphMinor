module

public import GraphMinor.Compute.GM06CutOriginRows
public import GraphMinor.Compute.GM06CutActiveBits

/-!
# Initialized construction of copied origins and active-end bits

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) connects the
copied edge ends after forming the induced rotations. This program
allocates the complete copied dart space and scans those rows from
the start. It computes both the exact origin table and the exact
dense membership bits. Its source may be the zero-padded rotation
buffer already returned by the cut-rotation program.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Allocate origins 626 and active bits 627, then scan copied
rotations 625. Register 647 holds their complete dart-space size. -/
def gm06CutOriginProg : Cmd :=
  .seq (.alloc 626 (.reg 647))
    (.seq (.alloc 627 (.reg 647))
      (.seq (.assign 666 (.const 0))
        (.seq (.assign 661 (.const 1))
          (.seq (.assign 665 (.read 625 (.const 0))) gm06CutOriginRowsLoop))))

/-- Exact copied origins and active-end bits, initialized from no
supplied output tables. The complete scan has a linear time bound. -/
theorem gm06CutOriginProg_exec {w m : ℕ} (rows : List (List ℕ)) (tail : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hm : 4 * m < 2 ^ w)
    (hkeys : ∀ d ∈ rows.flatten, d < 4 * m)
    (ha : s.arrs 625 = gm06EncodeRows rows ++ tail)
    (hcode : (s.arrs 625).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (h647 : s.regs 647 = 4 * m) :
    ∃ sf t, Exec w gm06CutOriginProg s sf t ∧
      t ≤ 10 + 8 * m + 27 * rows.length + 38 * rows.flatten.length ∧
      Keeps gm06CutOriginRowsRegs [611, 626, 627] s sf ∧
      sf.arrs 626 = gm06CutOrigins m rows ∧ sf.arrs 627 = gm06IncidenceBits (4 * m) rows.flatten := by
  have hcount : rows.length < 2 ^ w := hwords _ (by rw [ha]; simp [gm06EncodeRows])
  let s₀ := s.setArr 626 (List.replicate (4 * m) 0)
  let s₁ := s₀.setArr 627 (List.replicate (4 * m) 0)
  let s₂ := s₁.setReg 666 0
  let s₃ := s₂.setReg 661 1
  let s₄ := s₃.setReg 665 rows.length
  have he₀ : Exec w (.alloc 626 (.reg 647)) s s₀ (1 + 4 * m) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg h647 hm)
  have he₁ : Exec w (.alloc 627 (.reg 647)) s₀ s₁ (1 + 4 * m) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₀] using h647) hm)
  have he₂ : Exec w (.assign 666 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₃ : Exec w (.assign 661 (.const 1)) s₂ s₃ 2 := .assign (GraphMinor.Compute.Crossing.eval_const hw)
  have hsrc : s₃.arrs 625 = gm06EncodeRows rows ++ tail := by simp [s₃, s₂, s₁, s₀, ha]
  have he₄ : Exec w (.assign 665 (.read 625 (.const 0))) s₃ s₄ 3 :=
    .assign (by
      have hi : 0 < (s₃.arrs 625).length := by simp [hsrc, gm06EncodeRows]
      have hget : (s₃.arrs 625)[0]'hi = rows.length := by simp [hsrc, gm06EncodeRows]
      have he := GraphMinor.Compute.Crossing.eval_read (a := 625)
        (GraphMinor.Compute.Crossing.eval_const (c := 0) (Nat.two_pow_pos w)) hi
        (by rw [hget]; exact hcount)
      simpa only [hget] using he)
  have hk₀₄ : Keeps gm06CutOriginRowsRegs [611, 626, 627] s s₄ :=
    (((((Keeps.refl _ _ s).setArr (by simp) _).setArr (by simp) _).setReg
      (by simp [gm06CutOriginRowsRegs]) _).setReg (by simp [gm06CutOriginRowsRegs]) _).setReg
        (by simp [gm06CutOriginRowsRegs]) _
  obtain ⟨sf, tf, hef, htf, hkf, hof, haf, _, _, _⟩ := gm06CutOriginRowsLoop_exec
    (base := 0) rows [rows.length] tail (List.replicate (4 * m) 0) (List.replicate (4 * m) 0) s₄
    hw hm (by simpa using hcount) hcount
    (by simpa only [s₄, State.setReg_arrs, gm06EncodeRows, List.singleton_append] using hsrc)
    (by rw [hk₀₄.2 625 (by decide)]; exact hcode)
    (by rw [hk₀₄.2 625 (by decide)]; exact hwords)
    hkeys (by simp) (by simp) (by simp [s₄, s₃, s₂, s₁, s₀]) (by simp [s₄, s₃, s₂, s₁])
    (by simp [s₄, s₃]) (by simp [s₄]) (by simp [s₄, s₃, s₂])
  refine ⟨sf, (1 + 4 * m) + ((1 + 4 * m) + (2 + (2 + (3 + tf)))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ hef)))), by omega,
    hk₀₄.trans hkf (fun _ h => h) (fun _ h => h), ?_, ?_⟩
  · simpa only [gm06CutOriginPairsFrom_zero, gm06CutOrigins] using hof
  · simpa only [gm06CutActiveScatter_eq] using haf

end GraphMinor.Compute
