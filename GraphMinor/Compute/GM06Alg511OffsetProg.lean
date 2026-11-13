module

public import GraphMinor.Compute.GM06Alg511OffsetBody
import GraphMinor.Compute.TwoPathsRotate
import Mathlib.Tactic

/-!
# Computing all reflected vertex corrections

For VI (5.11), page 134, enumerate the supplied vertex labels and
scan both ordered cuff rows at each label. Store the resulting
whole-turn correction bits in one array. The invariant records the
computed prefix and preserves both supplied cuff rows.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Plain finite table of reference correction bits for vertex labels. -/
def gm06Alg511OffsetWords (x : GM06Alg511Input) : List ℕ :=
  (List.range x.vertexCount).map (gm06Alg511CuffOffset x)

/-- The correction table has exactly one word per supplied vertex. -/
theorem gm06Alg511OffsetWords_length (x : GM06Alg511Input) :
    (gm06Alg511OffsetWords x).length = x.vertexCount := by
  simp [gm06Alg511OffsetWords]

/-- Reading a valid vertex position gives its supplied-cuff correction. -/
theorem gm06Alg511OffsetWords_getD (x : GM06Alg511Input) (v : ℕ) (hv : v < x.vertexCount) :
    (gm06Alg511OffsetWords x).getD v 0 = gm06Alg511CuffOffset x v := by
  simp [gm06Alg511OffsetWords, hv]

/-- Construct correction array 1200, using vertex counter 77. -/
def gm06Alg511OffsetProg : Cmd :=
  .seq (.alloc 1200 (.reg 41)) (.seq (.assign 77 (.const 0))
    (forUp 77 (.reg 41) gm06Alg511OffsetBody))

/-- The reflected-reference correction table is computed from the
supplied cuff rows in quadratic time, with all other arrays preserved. -/
theorem gm06Alg511OffsetProg_exec {w : ℕ} (x : GM06Alg511Input) (s : State)
    (hw : 2 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hi : x.innerCuff.length < 2 ^ w) (ho : x.outerCuff.length < 2 ^ w)
    (hiwords : ∀ a ∈ x.innerCuff, a < 2 ^ w) (howords : ∀ a ∈ x.outerCuff, a < 2 ^ w)
    (hind : x.innerCuff.Nodup) (hond : x.outerCuff.Nodup)
    (hinner : s.arrs 1004 = x.innerCuff) (houter : s.arrs 1006 = x.outerCuff)
    (hN : s.regs 41 = x.vertexCount) :
    ∃ s' t, Exec w gm06Alg511OffsetProg s s' t ∧
      t ≤ 6 + x.vertexCount * (41 + 13 * x.innerCuff.length + 13 * x.outerCuff.length) ∧
      Keeps [77, 20, 64, 65] [1200] s s' ∧ s'.arrs 1200 = gm06Alg511OffsetWords x := by
  let s₁ := s.setArr 1200 (List.replicate x.vertexCount 0)
  let s₂ := s₁.setReg 77 0
  have he₁ : Exec w (.alloc 1200 (.reg 41)) s s₁ (1 + x.vertexCount) :=
    .alloc (Crossing.eval_reg hN hn)
  have he₂ : Exec w (.assign 77 (.const 0)) s₁ s₂ 2 :=
    .assign (Crossing.eval_const (Nat.two_pow_pos w))
  let I : ℕ → State → Prop := fun i st =>
    Keeps [77, 20, 64, 65] [1200] s st ∧ st.regs 77 = i ∧
      st.arrs 1200 = (List.range i).map (gm06Alg511CuffOffset x) ++
        List.replicate (x.vertexCount - i) 0
  have hI₀ : I 0 s₂ :=
    ⟨((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _,
      by simp [s₂], by simp [s₂, s₁]⟩
  obtain ⟨s', t, he, ht, hI'⟩ := Crossing.forUp_exec' I x.vertexCount
    (33 + 13 * x.innerCuff.length + 13 * x.outerCuff.length) (by omega) hn
    (fun i _ st h => ⟨h.2.1, Crossing.eval_reg ((h.1.1 41 (by decide)).trans hN) hn⟩)
    (fun i hilt st h => by
      have hcap : (st.arrs 1200).length = x.vertexCount := by
        rw [h.2.2]
        simp
        omega
      obtain ⟨st', tb, heb, htb, hkeep, hout⟩ := gm06Alg511OffsetBody_exec x i st hw hn hilt
        hi ho hiwords howords hind hond
        ((h.1.2 1004 (by decide)).trans hinner) ((h.1.2 1006 (by decide)).trans houter) hcap h.2.1
      refine ⟨st', tb, heb, htb, ?_, (hkeep.1 77 (by decide)).trans h.2.1⟩
      refine ⟨(h.1.trans hkeep (by simp) (by simp)).setReg (by simp) _, by simp, ?_⟩
      simp only [State.setReg_arrs, hout, h.2.2]
      exact set_range_map (gm06Alg511CuffOffset x) hilt)
    s₂ hI₀
  refine ⟨s', 1 + x.vertexCount + (2 + t), .seq he₁ (.seq he₂ he), ?_, hI'.1, ?_⟩
  · simp only [Expr.cost] at ht
    nlinarith [ht]
  · simpa only [Nat.sub_self, List.replicate_zero, List.append_nil, gm06Alg511OffsetWords] using hI'.2.2

end GraphMinor.Compute
