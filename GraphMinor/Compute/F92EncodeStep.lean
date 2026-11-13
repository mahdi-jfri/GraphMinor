module

public import GraphMinor.Compute.F92SegmentArrays
public import GraphMinor.Compute.Algorithm92FClaim

/-!
# Appending one length-prefixed segment

Read a segment's length, prepend that length to its vertex array in a temporary array,
then append the record to the output body. The number of segments is fixed, so repeated
linear copying of the body still has linear total time in the graph size.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Append one segment record to the encoded body. Register `r_base` holds the body length. -/
def f92EncodeOneProg (k i a_base r_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 1) (.len (aSeg92 a_base k i)))
    (.seq (prependWordProg (.reg (r_base + 1)) (aSeg92 a_base k i) (aTmp1 a_base)
        (r_base + 1) (r_base + 2))
      (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
        (appendArrProg (aFbody a_base) (aTmp1 a_base) (aTmp2 a_base)
          r_base (r_base + 1) (r_base + 2))))

/-- One record is appended exactly, and the body length register is updated. -/
theorem f92EncodeOneProg_exec {w n k : ℕ} (Q : Fin k → List (Fin n)) (i : Fin k)
    (acc : List ℕ) (a_base r_base : ℕ)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (haccw : ∀ v ∈ acc, v < 2 ^ w)
    (hlenw : acc.length + ((Q i).length + 1) < 2 ^ w)
    {s : State} (hacc : s.arrs (aFbody a_base) = acc)
    (hQ : s.arrs (aSeg92 a_base k i.val) = (Q i).map Fin.val)
    (hracc : s.regs r_base = acc.length) :
    ∃ s' t, Exec w (f92EncodeOneProg k i.val a_base r_base) s s' t ∧
      t ≤ 34 * acc.length + 36 * (Q i).length + 78 ∧
      s'.arrs (aFbody a_base) = acc ++ ((Q i).length :: (Q i).map Fin.val) ∧
      s'.regs r_base = (acc ++ ((Q i).length :: (Q i).map Fin.val)).length ∧
      (∀ a : ℕ, a ≠ aFbody a_base → a ≠ aTmp1 a_base → a ≠ aTmp2 a_base →
        s'.arrs a = s.arrs a) ∧
      (∀ q < r_base, s'.regs q = s.regs q) := by
  have hQlenw : (Q i).length < 2 ^ w := by omega
  have hQplusw : (Q i).length + 1 < 2 ^ w := by omega
  have hQwords : ∀ v ∈ (Q i).map Fin.val, v < 2 ^ w := by
    intro v hv
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv
    exact u.isLt.trans hn
  let s₁ := s.setReg (r_base + 1) (Q i).length
  have hex₁ : Exec w (.assign (r_base + 1) (.len (aSeg92 a_base k i.val))) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hQ, hQlenw])
  obtain ⟨s₂, t₂, hex₂, ht₂, hitem₂, harr₂, hreg₂⟩ :=
    prependWordProg_exec (tag := (Q i).length) (.reg (r_base + 1)) (aSeg92 a_base k i.val) (aTmp1 a_base)
      (r_base + 1) (r_base + 2) (by dsimp [aSeg92]; f92_omega) (by omega)
      ((Q i).map Fin.val) hQwords hw (by simpa [Nat.add_comm] using hQplusw)
      (s := s₁) (by intro v; simp [Expr.eval, checkWord, s₁, hQlenw]) hQ (by simp [s₁])
  have hrlen₂ : s₂.regs (r_base + 1) = (Q i).length := by
    rw [hreg₂ (r_base + 1) (Or.inl (by omega))]
    simp [s₁]
  let s₃ := s₂.setReg (r_base + 1) ((Q i).length + 1)
  have hex₃ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₂ s₃ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen₂, hw, hQlenw, hQplusw])
  have hacc₃ : s₃.arrs (aFbody a_base) = acc := by
    rw [State.setReg_arrs, harr₂ _ (by f92_omega)]
    exact hacc
  have hracc₃ : s₃.regs r_base = acc.length := by
    simp only [s₃, State.setReg_regs_ne _ _ (show (r_base : ℕ) ≠ r_base + 1 by omega)]
    rw [hreg₂ r_base (Or.inl (by omega))]
    simpa [s₁] using hracc
  obtain ⟨s₄, t₄, hex₄, ht₄, hout₄, hracc₄, harr₄, hreg₄⟩ :=
    appendArrProg_exec (aFbody a_base) (aTmp1 a_base) (aTmp2 a_base)
      r_base (r_base + 1) (r_base + 2) (by f92_omega) (by f92_omega) (by f92_omega)
      (by omega) (by omega) (by omega) acc ((Q i).length :: (Q i).map Fin.val)
      haccw (by intro v hv; rcases List.mem_cons.mp hv with rfl | hv; exact hQlenw; exact hQwords v hv)
      hw (by simpa using hlenw) hacc₃ hitem₂ hracc₃ (by simp [s₃])
  dsimp only [Expr.cost] at ht₂
  simp only [List.length_map, List.length_cons] at ht₂ ht₄ hracc₄
  refine ⟨s₄, 2 + (t₂ + (4 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hout₄, by simpa using hracc₄, ?_, ?_⟩
  · intro a haB ha1 ha2
    rw [harr₄ a haB ha2, State.setReg_arrs, harr₂ a ha1]
    rfl
  · intro q hq
    rw [hreg₄ q (Or.inl (by omega)) (by omega)]
    dsimp [s₃]
    rw [State.setReg_regs_ne _ _ (by omega : (q : ℕ) ≠ r_base + 1),
      hreg₂ q (Or.inl (by omega))]
    simp [s₁, State.setReg, show q ≠ r_base + 1 by omega]

end GraphMinor.Compute.Alg92
